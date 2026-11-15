/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Doob's inequalities (package B, task B2)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces, proved by
task B2. See `docs/stage2-design.md`, Section 2.1 (design decision B-3), and
`docs/stage2-interfaces.md`.

Mathlib v4.35.0 has Doob's maximal inequality in discrete time (`MeasureTheory.maximal_ineq`)
but not Doob's `L^p` inequality.

* `lintegral_iSup_sq_le_of_submartingale`, `lintegral_iSup_sq_le_of_martingale`: Doob's `L²`
  inequality in discrete time, `𝔼 max_{k ≤ n} f_k² ≤ 4 𝔼 f_n²` (from `maximal_ineq` and the
  layer-cake formula).
* `IsCL2Mart.lintegral_iSup_sq_le`: Doob's `L²` inequality in continuous time for a continuous
  `L²` martingale up to null sets (dyadic grids and path continuity).
* `IsCL2Mart.measure_exists_ge_le`: Doob's maximal inequality for a nonnegative continuous
  martingale.

All four are proved (task B2). Auxiliary results: `lintegral_sq_le_of_weak` (the layer-cake
step), the dyadic grid `gridPt`, its filtration `gridFiltration`, `IsCL2Mart.martingale_grid`
(the versions `𝔼[M_t | 𝓕_t]` on a grid form a Mathlib martingale) and `tendsto_gridPt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Core of the layer-cake proof of Doob's `L²` inequality: if `S, g ≥ 0`, `g` is integrable,
`𝔼 S² < ∞` and `ε μ(S ≥ ε) ≤ 𝔼[g; S ≥ ε]` for every `ε ≥ 0`, then `𝔼 S² ≤ 4 𝔼 g²`.
(`𝔼 S² = 2 ∫_0^∞ t μ(S ≥ t) dt ≤ 2 𝔼[g S] ≤ (𝔼 S² + 4 𝔼 g²) / 2`.) -/
lemma lintegral_sq_le_of_weak [IsFiniteMeasure μ] {S g : Ω → ℝ} (hS : 0 ≤ S)
    (hSm : AEMeasurable S μ) (hg : 0 ≤ g) (hgi : Integrable g μ)
    (hfin : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ ≠ ∞)
    (hweak : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤ S ω} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ S ω}, g ω ∂μ)) :
    ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ := by
  set A := ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ with hA
  set ν := μ.withDensity (fun ω => ENNReal.ofReal (g ω))
  have hgm : AEMeasurable (fun ω => ENNReal.ofReal (g ω)) μ := hgi.aemeasurable.ennreal_ofReal
  have h1 := lintegral_rpow_eq_lintegral_meas_le_mul μ (Eventually.of_forall hS) hSm two_pos
  norm_num [Real.rpow_two] at h1
  have h2 : ∀ t ∈ Set.Ioi (0 : ℝ), μ {ω | t ≤ S ω} * ENNReal.ofReal t ≤ ν {ω | t ≤ S ω} := by
    intro t ht
    have := hweak t.toNNReal
    rw [Real.coe_toNNReal _ (le_of_lt ht)] at this
    rw [withDensity_apply', ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
      (Eventually.of_forall hg), mul_comm]
    exact this
  have h3 : ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ S ω} =
      ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (S ω) ∂μ := by
    rw [← lintegral_eq_lintegral_meas_le ν (ae_of_all _ hS)
      (hSm.mono_ac (withDensity_absolutelyContinuous _ _))]
    exact lintegral_withDensity_eq_lintegral_mul₀' hgm
      (hSm.ennreal_ofReal.mono_ac (withDensity_absolutelyContinuous _ _))
  have h4 : A + A ≤ A + 4 * ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ := by
    calc A + A = 2 * A := (two_mul A).symm
      _ ≤ 2 * (2 * ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ S ω}) := by
          rw [hA, h1]
          gcongr 2 * (2 * ?_)
          exact setLIntegral_mono' measurableSet_Ioi h2
      _ = ∫⁻ ω, ENNReal.ofReal (4 * g ω * S ω) ∂μ := by
          rw [h3, ← mul_assoc, ← lintegral_const_mul' _ _ (by norm_num)]
          congr 1; ext ω
          rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (hg ω)), ENNReal.ofReal_mul (by norm_num)]
          norm_num [mul_assoc]
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (S ω ^ 2) + 4 * ENNReal.ofReal (g ω ^ 2)) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [sq_nonneg (S ω - 2 * g ω)]
      _ = A + 4 * ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ := by
          rw [lintegral_add_left' (hSm.pow_const 2).ennreal_ofReal,
            lintegral_const_mul' _ _ (by norm_num)]
  exact ENNReal.le_of_add_le_add_left hfin h4

/-- **Doob's `L²` inequality, discrete time, nonnegative submartingale:**
`𝔼[max_{k ≤ n} f_k²] ≤ 4 𝔼[f_n²]` (both sides in `[0, ∞]`). -/
theorem lintegral_iSup_sq_le_of_submartingale [IsFiniteMeasure μ] {𝓕 : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hf : Submartingale f 𝓕 μ) (hnn : 0 ≤ f) (n : ℕ) :
    ∫⁻ ω, ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (f k ω ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂μ := by
  set S : Ω → ℝ := fun ω =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω with hS
  have hle : ∀ ω, ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (f k ω ^ 2) ≤
      ENNReal.ofReal (S ω ^ 2) := fun ω =>
    iSup₂_le fun k hk => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (hnn k ω) (Finset.le_sup' (fun k => f k ω) hk) 2)
  refine (lintegral_mono hle).trans ?_
  by_cases hB : ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂μ = ∞
  · rw [hB, ENNReal.mul_top (by norm_num)]; exact le_top
  have hSnn : 0 ≤ S := fun ω =>
    (hnn 0 ω).trans (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 n.succ_pos))
  have hSm : AEMeasurable S μ :=
    (Finset.measurable_range_sup'' fun k _ =>
      ((hf.stronglyMeasurable k).mono (𝓕.le k)).measurable).aemeasurable
  have hmemn : MemLp (f n) 2 μ :=
    (memLp_two_iff_integrable_sq (hf.integrable n).1).2
      ⟨(hf.integrable n).1.pow 2,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)).2
          (lt_top_iff_ne_top.2 hB)⟩
  have hmem : ∀ k ≤ n, MemLp (f k) 2 μ := fun k hk => by
    refine (hmemn.condExp (m := 𝓕 k) (by norm_num)).of_le (hf.integrable k).1 ?_
    filter_upwards [hf.ae_le_condExp hk] with ω hω
    rw [Real.norm_of_nonneg (hnn k ω)]
    exact hω.trans (Real.le_norm_self _)
  have hfin : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ ≠ ∞ := by
    have hpt : ∀ ω, ENNReal.ofReal (S ω ^ 2) ≤
        ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (f k ω ^ 2) := fun ω => by
      obtain ⟨j, hj, hjS⟩ :=
        Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one (fun k => f k ω)
      rw [hS]; dsimp only; rw [hjS]
      exact Finset.single_le_sum (f := fun k => ENNReal.ofReal (f k ω ^ 2))
        (fun _ _ => zero_le) hj
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [lintegral_finsetSum' _ fun k _ => ((hf.integrable k).aemeasurable.pow_const 2).ennreal_ofReal]
    exact ENNReal.sum_ne_top.2 fun k hk =>
      (hmem k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).integrable_sq.lintegral_lt_top.ne
  exact lintegral_sq_le_of_weak hSnn hSm (hnn n) (hf.integrable n) hfin
    fun ε => maximal_ineq hf hnn n

/-- **Doob's `L²` inequality, discrete time, martingale:**
`𝔼[max_{k ≤ n} f_k²] ≤ 4 𝔼[f_n²]` (both sides in `[0, ∞]`). -/
theorem lintegral_iSup_sq_le_of_martingale [IsFiniteMeasure μ] {𝓕 : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hf : Martingale f 𝓕 μ) (n : ℕ) :
    ∫⁻ ω, ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (f k ω ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂μ := by
  set p : ℕ → Ω → ℝ := fun k ω => max (f k ω) 0 with hp_def
  set q : ℕ → Ω → ℝ := fun k ω => max (-f k ω) 0 with hq_def
  have hp : Submartingale p 𝓕 μ := hf.submartingale.pos
  have hq : Submartingale q 𝓕 μ := hf.neg.submartingale.pos
  have hsq : ∀ k ω, f k ω ^ 2 = p k ω ^ 2 + q k ω ^ 2 := by
    intro k ω
    rcases le_total 0 (f k ω) with h | h
    · simp [hp_def, hq_def, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    · simp [hp_def, hq_def, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
  have hm : ∀ (g : ℕ → Ω → ℝ), Submartingale g 𝓕 μ →
      AEMeasurable (fun ω => ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (g k ω ^ 2)) μ :=
    fun g hg => AEMeasurable.biSup _ (Finset.range (n + 1)).countable_toSet
      fun k _ => ((hg.integrable k).aemeasurable.pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (f k ω ^ 2) ∂μ
      ≤ ∫⁻ ω, ((⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (p k ω ^ 2)) +
          ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (q k ω ^ 2)) ∂μ := by
        refine lintegral_mono fun ω => iSup₂_le fun k hk => ?_
        rw [hsq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        exact add_le_add (le_iSup₂ (f := fun k _ => ENNReal.ofReal (p k ω ^ 2)) k hk)
          (le_iSup₂ (f := fun k _ => ENNReal.ofReal (q k ω ^ 2)) k hk)
    _ = ∫⁻ ω, ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (p k ω ^ 2) ∂μ +
          ∫⁻ ω, ⨆ k ∈ Finset.range (n + 1), ENNReal.ofReal (q k ω ^ 2) ∂μ :=
        lintegral_add_left' (hm p hp) _
    _ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (p n ω ^ 2) ∂μ + 4 * ∫⁻ ω, ENNReal.ofReal (q n ω ^ 2) ∂μ :=
        add_le_add (lintegral_iSup_sq_le_of_submartingale hp (fun k ω => le_max_right _ _) n)
          (lintegral_iSup_sq_le_of_submartingale hq (fun k ω => le_max_right _ _) n)
    _ = 4 * ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂μ := by
        rw [← mul_add, ← lintegral_add_left' ((hp.integrable n).aemeasurable.pow_const 2).ennreal_ofReal]
        congr 1; refine lintegral_congr fun ω => ?_
        rw [hsq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- The dyadic grid of `[0, τ]`: `gridPt τ j k = (min k 2^j) 2^{-j} τ`. -/
def gridPt (τ : ℝ≥0) (j k : ℕ) : ℝ≥0 := ((min k (2 ^ j) : ℕ) : ℝ≥0) / 2 ^ j * τ

lemma gridPt_le (τ : ℝ≥0) (j k : ℕ) : gridPt τ j k ≤ τ := by
  unfold gridPt
  calc ((min k (2 ^ j) : ℕ) : ℝ≥0) / 2 ^ j * τ ≤ 1 * τ := by
        gcongr
        rw [div_le_one (by positivity)]
        exact_mod_cast min_le_right _ _
    _ = τ := one_mul τ

lemma gridPt_mono (τ : ℝ≥0) (j : ℕ) : Monotone (gridPt τ j) := fun a b h => by
  unfold gridPt
  gcongr

lemma gridPt_double (τ : ℝ≥0) (j k : ℕ) : gridPt τ (j + 1) (2 * k) = gridPt τ j k := by
  unfold gridPt
  rw [show min (2 * k) (2 ^ (j + 1)) = 2 * min k (2 ^ j) by
    rw [pow_succ, mul_comm (2 ^ j) 2, Nat.mul_min_mul_left]]
  push_cast
  rw [pow_succ]
  field_simp

lemma gridPt_top (τ : ℝ≥0) (j : ℕ) : gridPt τ j (2 ^ j) = τ := by
  simp [gridPt]

/-- The filtration `k ↦ 𝓕 (gridPt τ j k)` indexed by `ℕ`. -/
def gridFiltration (𝓕 : Filtration ℝ≥0 mΩ) (τ : ℝ≥0) (j : ℕ) : Filtration ℕ mΩ where
  seq k := 𝓕 (gridPt τ j k)
  mono' _ _ h := 𝓕.mono (gridPt_mono τ j h)
  le' _ := 𝓕.le _

/-- On the dyadic grid of `[0, τ]` with `τ ≤ T`, the versions `𝔼[M_t | 𝓕_t]` of a continuous
`L²` martingale form a (Mathlib) discrete-time martingale. -/
lemma IsCL2Mart.martingale_grid [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) {τ : ℝ≥0} (hτ : (τ : ℝ) ≤ T) (j : ℕ) :
    Martingale (fun k => μ[M (gridPt τ j k) | 𝓕 (gridPt τ j k)]) (gridFiltration 𝓕 τ j) μ := by
  refine ⟨fun k => stronglyMeasurable_condExp, fun a b hab => ?_⟩
  have hab' := gridPt_mono τ j hab
  have hT : ∀ k, ((gridPt τ j k : ℝ≥0) : ℝ) ≤ T :=
    fun k => (NNReal.coe_le_coe.2 (gridPt_le τ j k)).trans hτ
  calc μ[μ[M (gridPt τ j b) | 𝓕 (gridPt τ j b)] | 𝓕 (gridPt τ j a)]
      =ᵐ[μ] μ[M (gridPt τ j b) | 𝓕 (gridPt τ j a)] :=
        condExp_condExp_of_le (𝓕.mono hab') (𝓕.le _)
    _ =ᵐ[μ] M (gridPt τ j a) := hM.condExp _ _ hab' (hT b)
    _ =ᵐ[μ] μ[M (gridPt τ j a) | 𝓕 (gridPt τ j a)] := (hM.condExp _ _ le_rfl (hT a)).symm

/-- Every `t ∈ [0, T]` is the limit of the grid points `gridPt T j ⌊2^j t / T⌋₊`, which are
indexed by `k ≤ 2^j`. -/
lemma tendsto_gridPt {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Set.Icc 0 T) :
    (∀ j : ℕ, ⌊2 ^ j * t / T⌋₊ ≤ 2 ^ j) ∧
      Tendsto (fun j : ℕ => ((gridPt T.toNNReal j ⌊2 ^ j * t / T⌋₊ : ℝ≥0) : ℝ)) atTop (𝓝 t) := by
  have hk : ∀ j : ℕ, ⌊2 ^ j * t / T⌋₊ ≤ 2 ^ j := fun j => by
    apply Nat.floor_le_of_le
    rcases hT.eq_or_lt with h | h
    · subst h; simp
    · rw [div_le_iff₀ h]; push_cast; nlinarith [ht.2, pow_pos (two_pos : (0 : ℝ) < 2) j]
  have hval : ∀ j : ℕ, ((gridPt T.toNNReal j ⌊2 ^ j * t / T⌋₊ : ℝ≥0) : ℝ) =
      (⌊2 ^ j * t / T⌋₊ : ℝ) / 2 ^ j * T := by
    intro j; simp only [gridPt, min_eq_left (hk j)]; push_cast; rw [Real.coe_toNNReal _ hT]
  refine ⟨hk, ?_⟩
  simp_rw [hval]
  have hup : ∀ j : ℕ, (⌊2 ^ j * t / T⌋₊ : ℝ) / 2 ^ j * T ≤ t := by
    intro j
    rcases hT.eq_or_lt with h | h
    · subst h; simpa using ht.1
    · have := Nat.floor_le (show 0 ≤ 2 ^ j * t / T by have := ht.1; positivity)
      calc (⌊2 ^ j * t / T⌋₊ : ℝ) / 2 ^ j * T ≤ (2 ^ j * t / T) / 2 ^ j * T := by gcongr
        _ = t := by field_simp
  have hlow : ∀ j : ℕ, t - T / 2 ^ j ≤ (⌊2 ^ j * t / T⌋₊ : ℝ) / 2 ^ j * T := by
    intro j
    rcases hT.eq_or_lt with h | h
    · subst h; have : t = 0 := le_antisymm ht.2 ht.1; simp [this]
    · have h3 := (div_lt_iff₀ h).1 (Nat.lt_floor_add_one (2 ^ j * t / T))
      have h2 : (0 : ℝ) < 2 ^ j := by positivity
      rw [show t - T / 2 ^ j = (2 ^ j * t - T) / 2 ^ j by field_simp,
        show (⌊2 ^ j * t / T⌋₊ : ℝ) / 2 ^ j * T = (⌊2 ^ j * t / T⌋₊ * T) / 2 ^ j by ring]
      gcongr
      linarith
  have hlim : Tendsto (fun j : ℕ => t - T / 2 ^ j) atTop (𝓝 t) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul T
    rw [mul_zero] at this
    have := tendsto_const_nhds (x := t).sub this
    simpa [div_eq_mul_inv] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

/-- **Doob's `L²` inequality, continuous time:** for a continuous `L²` martingale `M` on
`[0, T]` (up to null sets), `sup_{t ∈ [0, T]} M_t²` is almost everywhere measurable and
`𝔼[sup_{t ∈ [0, T]} M_t²] ≤ 4 𝔼[M_T²]`. (For `T < 0` the supremum is over the empty set and
equals `0`.) -/
theorem IsCL2Mart.lintegral_iSup_sq_le [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) :
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2)) μ ∧
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (M T ω ^ 2) ∂μ := by
  rcases lt_or_ge T 0 with hT | hT
  · have h0 : ∀ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) = 0 := fun ω => by
      simp [Set.Icc_eq_empty (not_le.2 hT)]
    simp only [h0]
    exact ⟨aemeasurable_const, by simp⟩
  set τ := T.toNNReal with hτ
  have hτT : (τ : ℝ) = T := Real.coe_toNNReal _ hT
  set F : ℕ → Ω → ℝ≥0∞ := fun j ω =>
    ⨆ k ∈ Finset.range (2 ^ j + 1), ENNReal.ofReal (M (gridPt τ j k) ω ^ 2) with hF
  have hgridT : ∀ j k, ((gridPt τ j k : ℝ≥0) : ℝ) ≤ T :=
    fun j k => hτT ▸ NNReal.coe_le_coe.2 (gridPt_le τ j k)
  have hmeas : ∀ j, AEMeasurable (F j) μ := fun j =>
    AEMeasurable.biSup _ (Finset.range _).countable_toSet fun k _ =>
      ((hM.memLp _ (hgridT j k)).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hmono : Monotone F := by
    refine monotone_nat_of_le_succ fun j ω => iSup₂_le fun k hk => ?_
    rw [← gridPt_double τ j k]
    refine le_iSup₂ (f := fun k _ => ENNReal.ofReal (M (gridPt τ (j + 1) k) ω ^ 2)) (2 * k) ?_
    simp only [Finset.mem_range] at hk ⊢
    rw [pow_succ]
    omega
  have hsup : ∀ᵐ ω ∂μ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) = ⨆ j, F j ω := by
    filter_upwards [hM.cont] with ω hω
    apply le_antisymm
    · refine iSup₂_le fun t ht => ?_
      obtain ⟨hk, hlim⟩ := tendsto_gridPt hT ht
      have hc : Tendsto (fun j => ENNReal.ofReal (M (gridPt τ j ⌊2 ^ j * t / T⌋₊) ω ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (M t ω ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (((continuous_pow 2).tendsto _).comp
          ((hω t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim,
            Eventually.of_forall fun j => ⟨NNReal.coe_nonneg _, hgridT _ _⟩⟩)))
      refine le_of_tendsto' hc fun j => le_iSup_of_le j ?_
      exact le_iSup₂ (f := fun k _ => ENNReal.ofReal (M (gridPt τ j k) ω ^ 2)) _
        (Finset.mem_range.2 (Nat.lt_succ_of_le (hk j)))
    · exact iSup_le fun j => iSup₂_le fun k _ =>
        le_iSup₂ (f := fun t _ => ENNReal.ofReal (M t ω ^ 2)) _ ⟨NNReal.coe_nonneg _, hgridT j k⟩
  have hae : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2)) μ :=
    (AEMeasurable.iSup hmeas).congr (hsup.mono fun ω h => h.symm)
  refine ⟨hae, ?_⟩
  rw [lintegral_congr_ae hsup, lintegral_iSup' hmeas (ae_of_all _ fun ω a b h => hmono h ω)]
  refine iSup_le fun j => ?_
  set Y : ℕ → Ω → ℝ := fun k => μ[M (gridPt τ j k) | 𝓕 (gridPt τ j k)] with hY_def
  have hY : ∀ k, Y k =ᵐ[μ] M (gridPt τ j k) := fun k => hM.condExp _ _ le_rfl (hgridT j k)
  have hYall : ∀ᵐ ω ∂μ, ∀ k, Y k ω = M (gridPt τ j k) ω := ae_all_iff.2 hY
  calc ∫⁻ ω, F j ω ∂μ
      = ∫⁻ ω, ⨆ k ∈ Finset.range (2 ^ j + 1), ENNReal.ofReal (Y k ω ^ 2) ∂μ :=
        lintegral_congr_ae (hYall.mono fun ω h => by simp only [hF, h])
    _ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (Y (2 ^ j) ω ^ 2) ∂μ :=
        lintegral_iSup_sq_le_of_martingale (hM.martingale_grid hτT.le j) (2 ^ j)
    _ = 4 * ∫⁻ ω, ENNReal.ofReal (M T ω ^ 2) ∂μ := by
        congr 1
        refine lintegral_congr_ae ((hY (2 ^ j)).mono fun ω h => ?_)
        simp only [h, gridPt_top, hτT]

/-- **Doob's maximal inequality, continuous time:** for a continuous `L²` martingale `M` on
`[0, T]` which is almost surely nonnegative on `[0, T]`, and `K > 0`,
`ℙ(∃ t ∈ [0, T], M_t ≥ K) ≤ 𝔼[M_T] / K`. -/
theorem IsCL2Mart.measure_exists_ge_le [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) (hpos : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, 0 ≤ M t ω) {K : ℝ}
    (hK : 0 < K) :
    μ {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ M t ω} ≤ ENNReal.ofReal ((∫ ω, M T ω ∂μ) / K) := by
  rcases lt_or_ge T 0 with hT | hT
  · have h0 : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ M t ω} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun ω ⟨t, ht, _⟩ => absurd (ht.1.trans ht.2) (not_le.2 hT)
    rw [h0, measure_empty]
    exact zero_le
  set τ := T.toNNReal with hτ
  have hτT : (τ : ℝ) = T := Real.coe_toNNReal _ hT
  have hgridT : ∀ j k, ((gridPt τ j k : ℝ≥0) : ℝ) ≤ T :=
    fun j k => hτT ▸ NNReal.coe_le_coe.2 (gridPt_le τ j k)
  set E := ∫ ω, M T ω ∂μ with hE
  have hint : Integrable (M T) μ := by
    have := hM.memLp τ hτT.le
    rw [hτT] at this
    exact this.integrable one_le_two
  set P : ℕ → ℕ → Ω → ℝ := fun j k ω => max (μ[M (gridPt τ j k) | 𝓕 (gridPt τ j k)] ω) 0
    with hP_def
  have hP : ∀ j, Submartingale (P j) (gridFiltration 𝓕 τ j) μ :=
    fun j => (hM.martingale_grid hτT.le j).submartingale.pos
  have hPnn : ∀ j, 0 ≤ P j := fun j k ω => le_max_right _ _
  have hPT : ∀ j, P j (2 ^ j) =ᵐ[μ] M T := fun j => by
    filter_upwards [hM.condExp τ τ le_rfl hτT.le, hpos] with ω h1 h2
    show max (μ[M (gridPt τ j (2 ^ j)) | 𝓕 (gridPt τ j (2 ^ j))] ω) 0 = M T ω
    rw [gridPt_top, h1, hτT]
    exact max_eq_left (h2 T ⟨hT, le_rfl⟩)
  have key : ∀ c, 0 < c → c < K →
      μ {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ M t ω} ≤ ENNReal.ofReal (E / c) := by
    intro c hc hcK
    set S : ℕ → Set Ω := fun j => {ω | ((c.toNNReal : ℝ≥0) : ℝ) ≤
      (Finset.range (2 ^ j + 1)).sup' Finset.nonempty_range_add_one fun k => P j k ω} with hS
    have hSle : ∀ j, μ (S j) ≤ ENNReal.ofReal (E / c) := by
      intro j
      have h1 := maximal_ineq (hP j) (hPnn j) (ε := c.toNNReal) (2 ^ j)
      have h2 : ∫ ω in S j, P j (2 ^ j) ω ∂μ ≤ E :=
        (setIntegral_le_integral ((hP j).integrable _) (ae_of_all _ fun ω => hPnn j _ ω)).trans
          (le_of_eq (integral_congr_ae (hPT j)))
      have h3 : (c.toNNReal : ℝ≥0∞) * μ (S j) ≤ ENNReal.ofReal E :=
        h1.trans (ENNReal.ofReal_le_ofReal h2)
      rw [ENNReal.ofReal_div_of_pos hc, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc))
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact h3
    have hSmono : Monotone S := by
      refine monotone_nat_of_le_succ fun j ω hω => ?_
      simp only [hS, Set.mem_ofPred_eq] at hω ⊢
      refine hω.trans (Finset.sup'_le _ _ fun k hk => ?_)
      have : P j k ω = P (j + 1) (2 * k) ω := by simp only [hP_def, gridPt_double]
      rw [this]
      refine Finset.le_sup' (fun k => P (j + 1) k ω) ?_
      simp only [Finset.mem_range] at hk ⊢
      rw [pow_succ]
      omega
    have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ M t ω} ≤ᵐ[μ] ⋃ j, S j := by
      have hY : ∀ᵐ ω ∂μ, ∀ j k,
          μ[M (gridPt τ j k) | 𝓕 (gridPt τ j k)] ω = M (gridPt τ j k) ω :=
        ae_all_iff.2 fun j => ae_all_iff.2 fun k => hM.condExp _ _ le_rfl (hgridT j k)
      filter_upwards [hM.cont, hY] with ω hω hYω hA
      obtain ⟨t, ht, hKt⟩ := hA
      obtain ⟨hk, hlim⟩ := tendsto_gridPt hT ht
      have hc' : Tendsto (fun j => M (gridPt τ j ⌊2 ^ j * t / T⌋₊) ω) atTop (𝓝 (M t ω)) :=
        (hω t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim,
          Eventually.of_forall fun j => ⟨NNReal.coe_nonneg _, hgridT _ _⟩⟩)
      obtain ⟨j, hj⟩ := (hc'.eventually (lt_mem_nhds (hcK.trans_le hKt))).exists
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      show ((c.toNNReal : ℝ≥0) : ℝ) ≤ _
      rw [Real.coe_toNNReal _ hc.le]
      refine le_trans ?_ (Finset.le_sup' (fun k => P j k ω)
        (Finset.mem_range.2 (Nat.lt_succ_of_le (hk j))))
      show c ≤ max _ 0
      rw [hYω]
      exact hj.le.trans (le_max_left _ _)
    calc μ {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ M t ω} ≤ μ (⋃ j, S j) := measure_mono_ae hsub
      _ = ⨆ j, μ (S j) := hSmono.measure_iUnion
      _ ≤ ENNReal.ofReal (E / c) := iSup_le hSle
  have hlim : Tendsto (fun c => ENNReal.ofReal (E / c)) (𝓝[<] K) (𝓝 (ENNReal.ofReal (E / K))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds.div tendsto_id hK.ne').mono_left nhdsWithin_le_nhds)
  exact ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsLT hK) fun c hc => key c hc.1 hc.2)

end QSSEPtoKPZ
