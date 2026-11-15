/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.ProductPathwise
public import QSSEPtoKPZ.ItoIntegral.FourthMoment
public import QSSEPtoKPZ.ItoIntegral.Stopping

/-!
# Product rule: the quadratic covariation of two Itô integrals (package C, task C6)

Auxiliary material for `ItoIntegral/Product.lean`. Let `M = I(b)`, `N = I(d)` with
`∑ᵢ bᵢ², ∑ᵢ dᵢ² ≤ K`.

* `itoProd_ae_abs_tsum_mul_le`: almost surely, `|∑ᵢ bᵢ(s) dᵢ(s)| ≤ K` for almost every
  `s ∈ (0, T]` (the series `∑ᵢ bᵢ²`, `∑ᵢ dᵢ²` converge outside a `ds ⊗ dℙ`-null set, since the
  energies are finite), and `s ↦ ∑ᵢ bᵢ(s) dᵢ(s)` is integrable on `[0, T]`.
* `itoProd_tendsto_covariation`: `∑_{k < m} ΔM_k ΔN_k → ∫_0^t ∑ᵢ bᵢ dᵢ ds` in `L²`. Proof: the
  terms `D_k = ΔM_k ΔN_k - ∫_{t_k}^{t_{k+1}} ∑ᵢ bᵢ dᵢ` are martingale differences (cross bracket
  of `I(b 𝟙_{s > t_k})` and `I(d 𝟙_{s > t_k})`), hence orthogonal in `L²`, and
  `𝔼 D_k² ≤ 𝔼 ΔM_k⁴ + 𝔼 ΔN_k⁴ + 2 K² (t/m)² ≤ 14 K² (t/m)²` by the fourth moment bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

omit [Countable ι] in
/-- For a square-summable real pair, `|∑ᵢ xᵢ yᵢ| ≤ K` when `∑ᵢ xᵢ², ∑ᵢ yᵢ² ≤ K`
(`2 |xᵢ yᵢ| ≤ xᵢ² + yᵢ²`). -/
private lemma abs_tsum_mul_le {x y : ι → ℝ} (hx : Summable fun i => x i ^ 2)
    (hy : Summable fun i => y i ^ 2) {K : ℝ} (hxK : ∑' i, x i ^ 2 ≤ K)
    (hyK : ∑' i, y i ^ 2 ≤ K) : |∑' i, x i * y i| ≤ K := by
  have hle : ∀ i, |x i * y i| ≤ (x i ^ 2 + y i ^ 2) / 2 := fun i => by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x i| - |y i|), sq_abs (x i), sq_abs (y i)]
  have hs : Summable fun i => (x i ^ 2 + y i ^ 2) / 2 := (hx.add hy).div_const 2
  have ha : Summable fun i => |x i * y i| := hs.of_nonneg_of_le (fun i => abs_nonneg _) hle
  calc |∑' i, x i * y i| ≤ ∑' i, |x i * y i| := by
        have := norm_tsum_le_tsum_norm (f := fun i => x i * y i)
          (by simpa only [Real.norm_eq_abs] using ha)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' i, (x i ^ 2 + y i ^ 2) / 2 := ha.tsum_le_tsum hle hs
    _ = (∑' i, x i ^ 2 + ∑' i, y i ^ 2) / 2 := by rw [tsum_div_const, hx.tsum_add hy]
    _ ≤ K := by linarith

/-- Finite energy: almost surely, `∑ᵢ hᵢ(s)²` converges for almost every `s ∈ (0, T]`. -/
private lemma ae_summable_sq {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) (T : ℝ) :
    ∀ᵐ ω ∂μ, ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 T)), Summable fun i => h i s ω ^ 2 := by
  have hm := itoEnergy_measurable_pathEnergy hh.meas T
  have hfin : ∫⁻ ω, pathEnergy h T ω ∂μ ≠ ⊤ := (hh.energy_lt_top T).ne
  filter_upwards [ae_lt_top hm hfin] with ω hω
  rw [itoEnergy_pathEnergy_eq_pos] at hω
  have hΨ : Measurable fun s => ∑' i, ‖(if 0 < s then h i s ω else 0)‖ₑ ^ 2 :=
    (itoEnergy_measurable_tsum hh.meas).comp measurable_prodMk_right
  filter_upwards [ae_lt_top hΨ hω.ne, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  simp only [hsI.1, ↓reduceIte, itoEnergy_enorm_sq] at hs
  have := ENNReal.summable_toReal hs.ne
  simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this

/-- **The cross density is bounded and integrable.** If `b`, `d` are Itô-integrable with
`∑ᵢ bᵢ(s, ω)² ≤ K` and `∑ᵢ dᵢ(s, ω)² ≤ K` for all `s > 0` and `ω` (Lean's `tsum`), then almost
surely `|∑ᵢ bᵢ(s) dᵢ(s)| ≤ K` for almost every `s ∈ (0, T]`, and `s ↦ ∑ᵢ bᵢ(s) dᵢ(s)` is
integrable on `[0, T]` (`T ≥ 0`: nothing is assumed at negative times). -/
theorem itoProd_ae_abs_tsum_mul_le {b d : ι → ℝ → Ω → ℝ} (hb : IsItoIntegrable 𝓖 μ b)
    (hd : IsItoIntegrable 𝓖 μ d) {K : ℝ} (hbK : ∀ ω (s : ℝ), 0 < s → ∑' i, b i s ω ^ 2 ≤ K)
    (hdK : ∀ ω (s : ℝ), 0 < s → ∑' i, d i s ω ^ 2 ≤ K) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂μ, (∀ᵐ s ∂(volume.restrict (Set.Ioc 0 T)), |∑' i, b i s ω * d i s ω| ≤ K) ∧
      IntervalIntegrable (fun s => ∑' i, b i s ω * d i s ω) volume 0 T := by
  filter_upwards [ae_summable_sq hb T, ae_summable_sq hd T] with ω hωb hωd
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 T)), |∑' i, b i s ω * d i s ω| ≤ K := by
    filter_upwards [hωb, hωd, ae_restrict_mem measurableSet_Ioc] with s h1 h2 hs
    exact abs_tsum_mul_le h1 h2 (hbK ω s hs.1) (hdK ω s hs.1)
  refine ⟨hbound, ?_⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hmeas : Measurable fun s =>
      ∑' i, (if 0 < s then b i s ω else 0) * (if 0 < s then d i s ω else 0) :=
    Measurable.tsum fun i => ((hb.meas i).comp measurable_prodMk_right).mul
      ((hd.meas i).comp measurable_prodMk_right)
  have hae : AEStronglyMeasurable (fun s => ∑' i, b i s ω * d i s ω)
      (volume.restrict (Set.Ioc 0 T)) := by
    refine hmeas.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [hs.1]
  exact Integrable.of_bound hae K (hbound.mono fun s hs => by simpa [Real.norm_eq_abs] using hs)

/-- The tail `h 𝟙_{s > u}` of a family. -/
private def tail (u : ℝ≥0) (h : ι → ℝ → Ω → ℝ) : ι → ℝ → Ω → ℝ :=
  fun i s ω => if (u : ℝ) < s then h i s ω else 0

omit [Countable ι] in
private lemma tail_eq (u : ℝ≥0) (h : ι → ℝ → Ω → ℝ) :
    tail u h = fun i s ω => if (u : ℝ) < s then (fun _ : Ω => (1 : ℝ)) ω * h i s ω else 0 := by
  funext i s ω
  simp [tail]

private lemma isItoIntegrable_tail {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    (u : ℝ≥0) : IsItoIntegrable 𝓖 μ (tail u h) := by
  rw [tail_eq]
  exact hh.mul_indicator_gt measurable_const ⟨1, fun _ => by simp⟩

/-- `I_t(h 𝟙_{s > u}) = I_t(h) - I_{t ∧ u}(h)`. -/
private lemma stochInt_tail (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (u : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (tail u h) t ω =
      stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h ((min t u : ℝ≥0) : ℝ) ω := by
  rw [tail_eq]
  filter_upwards [stochInt_mul_indicator_gt hB hh (u := u) (ξ := fun _ => 1) measurable_const
    ⟨1, fun _ => by simp⟩] with ω hω t
  rw [hω t, one_mul]

omit [Countable ι] in
/-- `∫_0^v ∑ᵢ (b 𝟙_{s > u})ᵢ (d 𝟙_{s > u})ᵢ = ∫_u^v ∑ᵢ bᵢ dᵢ` (no integrability needed). -/
private lemma integral_tail_mul {u v : ℝ≥0} (huv : u ≤ v) (b d : ι → ℝ → Ω → ℝ) (ω : Ω) :
    ∫ r in (0 : ℝ)..v, ∑' i, tail u b i r ω * tail u d i r ω =
      ∫ r in (u : ℝ)..v, ∑' i, b i r ω * d i r ω := by
  have h1 : (fun r => ∑' i, tail u b i r ω * tail u d i r ω) =
      (Set.Ioi (u : ℝ)).indicator (fun r => ∑' i, b i r ω * d i r ω) := by
    funext r
    by_cases hr : (u : ℝ) < r
    · simp [tail, hr]
    · simp [tail, hr]
  rw [h1, intervalIntegral.integral_of_le (NNReal.coe_nonneg v),
    intervalIntegral.integral_of_le (by exact_mod_cast huv), setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioc (0 : ℝ) v ∩ Set.Ioi (u : ℝ) = Set.Ioc (u : ℝ) v := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩
      exact ⟨⟨lt_of_le_of_lt (NNReal.coe_nonneg u) h3, h2⟩, h3⟩
  rw [hset]

/-- **The bound for `m` cells.** `𝔼[(∑_{k < m} ΔI_k(b) ΔI_k(d) - ∫_0^t ∑ᵢ bᵢ dᵢ)²] ≤
m · 14 K² (t/m)²`. -/
private lemma covariation_bound (hB : IsBrownianFamily 𝓖 B μ) {b d : ι → ℝ → Ω → ℝ}
    (hb : IsItoIntegrable 𝓖 μ b) (hd : IsItoIntegrable 𝓖 μ d) {K : ℝ}
    (hbK : ∀ ω (s : ℝ), 0 < s → ∑' i, b i s ω ^ 2 ≤ K)
    (hdK : ∀ ω (s : ℝ), 0 < s → ∑' i, d i s ω ^ 2 ≤ K) (t : ℝ≥0) {m : ℕ} (hm : 0 < m) :
    ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range m,
        (stochInt 𝓖 μ B b (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B b (itoProdGrid t m k) ω) *
          (stochInt 𝓖 μ B d (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B d (itoProdGrid t m k) ω) -
        ∫ s in (0 : ℝ)..t, ∑' i, b i s ω * d i s ω) ^ 2) ∂μ ≤
      ENNReal.ofReal (m * (14 * K ^ 2 * ((t : ℝ) / m) ^ 2)) := by
  set u : ℕ → ℝ≥0 := fun k => itoProdGrid t m k with hu
  set δ : ℝ := (t : ℝ) / m with hδdef
  have hδ : ∀ k, ((u (k + 1) : ℝ≥0) : ℝ) - u k = δ := by
    intro k
    simp only [hu, itoProdGrid_succ, NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast, hδdef]
    ring
  have hmono : ∀ k, u k ≤ u (k + 1) := fun k => itoProdGrid_mono t m (Nat.le_succ k)
  set c : ℝ := 14 * K ^ 2 * δ ^ 2 with hc
  set D : ℕ → Ω → ℝ := fun k ω =>
    stochInt 𝓖 μ B (tail (u k) b) (u (k + 1)) ω * stochInt 𝓖 μ B (tail (u k) d) (u (k + 1)) ω -
      ∫ r in (0 : ℝ)..(u (k + 1)), ∑' i, tail (u k) b i r ω * tail (u k) d i r ω with hD
  set D' : ℕ → Ω → ℝ := fun k => μ[D k | 𝓖 (u (k + 1))] with hD'
  have hDD' : ∀ k, D' k =ᵐ[μ] D k := fun k =>
    condExp_stochInt_mul hB (isItoIntegrable_tail hb _) (isItoIntegrable_tail hd _) le_rfl
  have hD'sm : ∀ k, StronglyMeasurable[𝓖 (u (k + 1))] (D' k) := fun k => stronglyMeasurable_condExp
  have hD0 : ∀ k, μ[D' k | 𝓖 (u k)] =ᵐ[μ] 0 := by
    intro k
    refine (condExp_congr_ae (hDD' k)).trans ?_
    refine (condExp_stochInt_mul hB (isItoIntegrable_tail hb (u k))
      (isItoIntegrable_tail hd (u k)) (hmono k)).trans ?_
    filter_upwards [stochInt_tail hB hb (u k), stochInt_tail hB hd (u k)] with ω h2 h3
    simp only [h2, h3, min_self, sub_self, zero_mul, Pi.zero_apply]
    rw [integral_tail_mul le_rfl, intervalIntegral.integral_same, sub_zero]
  have hgood := itoProd_ae_abs_tsum_mul_le (μ := μ) hb hd hbK hdK t (NNReal.coe_nonneg t)
  -- second moment of each term
  have hDsq : ∀ k < m, MemLp (D' k) 2 μ ∧ ∫ ω, D' k ω ^ 2 ∂μ ≤ c := by
    intro k hk
    have hk1 : u (k + 1) ≤ t := itoProdGrid_le t (by omega)
    set x : Ω → ℝ := fun ω => stochInt 𝓖 μ B b (u (k + 1)) ω - stochInt 𝓖 μ B b (u k) ω with hx
    set y : Ω → ℝ := fun ω => stochInt 𝓖 μ B d (u (k + 1)) ω - stochInt 𝓖 μ B d (u k) ω with hy
    have hxm : Measurable x := ((stochInt_adapted hB b _).mono (𝓖.le _) le_rfl).sub
      ((stochInt_adapted hB b _).mono (𝓖.le _) le_rfl)
    have hym : Measurable y := ((stochInt_adapted hB d _).mono (𝓖.le _) le_rfl).sub
      ((stochInt_adapted hB d _).mono (𝓖.le _) le_rfl)
    have hpt : ∀ᵐ ω ∂μ, D' k ω ^ 2 ≤ x ω ^ 4 + y ω ^ 4 + 2 * (K * δ) ^ 2 := by
      filter_upwards [hDD' k, stochInt_tail hB hb (u k), stochInt_tail hB hd (u k), hgood]
        with ω h1 h2 h3 h4
      have hDx : D' k ω = x ω * y ω - ∫ r in (u k : ℝ)..(u (k + 1)), ∑' i, b i r ω * d i r ω := by
        rw [h1]
        simp only [hD, hx, hy, h2, h3, min_eq_right (hmono k), integral_tail_mul (hmono k)]
      set a := ∫ r in (u k : ℝ)..(u (k + 1)), ∑' i, b i r ω * d i r ω with ha
      have hab : |a| ≤ K * δ := by
        have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (u k : ℝ)) (b := (u (k + 1) : ℝ))
          (f := fun r => ∑' i, b i r ω * d i r ω) (g := fun _ => K)
          (by exact_mod_cast hmono k) ?_ intervalIntegrable_const
        · rw [intervalIntegral.integral_const, smul_eq_mul, hδ k, Real.norm_eq_abs] at hle
          rw [ha]
          linarith
        · have := (ae_restrict_iff' measurableSet_Ioc).1 h4.1
          filter_upwards [this] with r hr hrI
          rw [Real.norm_eq_abs]
          refine hr ⟨lt_of_le_of_lt (NNReal.coe_nonneg _) hrI.1, hrI.2.trans ?_⟩
          exact_mod_cast hk1
      have ha2 : a ^ 2 ≤ (K * δ) ^ 2 := by
        rw [← sq_abs a]
        exact pow_le_pow_left₀ (abs_nonneg a) hab 2
      rw [hDx]
      nlinarith [sq_nonneg (x ω * y ω + a), sq_nonneg (x ω ^ 2 - y ω ^ 2)]
    have h4b := lintegral_stochInt_sub_pow_four_le hB hb (hmono k)
      (fun ω s hs _ => hbK ω s (lt_of_le_of_lt (NNReal.coe_nonneg _) hs))
    have h4d := lintegral_stochInt_sub_pow_four_le hB hd (hmono k)
      (fun ω s hs _ => hdK ω s (lt_of_le_of_lt (NNReal.coe_nonneg _) hs))
    rw [hδ] at h4b h4d
    have hlint : ∫⁻ ω, ENNReal.ofReal (D' k ω ^ 2) ∂μ ≤ ENNReal.ofReal c := by
      calc ∫⁻ ω, ENNReal.ofReal (D' k ω ^ 2) ∂μ
          ≤ ∫⁻ ω, (ENNReal.ofReal (x ω ^ 4) + ENNReal.ofReal (y ω ^ 4) +
              ENNReal.ofReal (2 * (K * δ) ^ 2)) ∂μ := by
            refine lintegral_mono_ae (hpt.mono fun ω hω => ?_)
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            exact ENNReal.ofReal_le_ofReal hω
        _ = ∫⁻ ω, ENNReal.ofReal (x ω ^ 4) ∂μ + ∫⁻ ω, ENNReal.ofReal (y ω ^ 4) ∂μ +
              ENNReal.ofReal (2 * (K * δ) ^ 2) := by
            rw [lintegral_add_right _ measurable_const, lintegral_add_left
              (hxm.pow_const 4).ennreal_ofReal, lintegral_const, measure_univ, mul_one]
        _ ≤ ENNReal.ofReal (6 * K ^ 2 * δ ^ 2) + ENNReal.ofReal (6 * K ^ 2 * δ ^ 2) +
              ENNReal.ofReal (2 * (K * δ) ^ 2) := by
            gcongr
        _ = ENNReal.ofReal c := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity), hc]
            congr 1
            ring
    have hae : AEStronglyMeasurable (D' k) μ :=
      ((hD'sm k).mono (𝓖.le _)).aestronglyMeasurable
    have hmem : MemLp (D' k) 2 μ := by
      rw [memLp_two_iff_integrable_sq hae]
      refine ⟨hae.pow 2, (hasFiniteIntegral_iff_ofReal
        (ae_of_all _ fun ω => sq_nonneg _)).2 (hlint.trans_lt ENNReal.ofReal_lt_top)⟩
    refine ⟨hmem, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _) (hae.pow 2)]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
  -- orthogonality of the terms
  have hind : ∀ n ≤ m, MemLp (fun ω => ∑ k ∈ Finset.range n, D' k ω) 2 μ ∧
      ∫ ω, (∑ k ∈ Finset.range n, D' k ω) ^ 2 ∂μ ≤ n * c := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty]
      exact ⟨memLp_const 0, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨hS2, hSi⟩ := ih (by omega)
      obtain ⟨hD2, hDi⟩ := hDsq n (by omega)
      set S : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, D' k ω with hS
      have hSm : StronglyMeasurable[𝓖 (u n)] S := by
        have := Finset.stronglyMeasurable_sum (m := 𝓖 (u n)) (Finset.range n) (f := D')
          fun k hk => (hD'sm k).mono (𝓖.mono (itoProdGrid_mono t m (by
            simp only [Finset.mem_range] at hk; omega)))
        convert this using 1
        funext ω
        simp [hS]
      have hint : Integrable (S * D' n) μ := hS2.integrable_mul hD2
      have hSD : ∫ ω, S ω * D' n ω ∂μ = 0 := by
        calc ∫ ω, S ω * D' n ω ∂μ = ∫ ω, (μ[S * D' n | 𝓖 (u n)]) ω ∂μ :=
              (integral_condExp (𝓖.le _)).symm
          _ = ∫ ω, (S * μ[D' n | 𝓖 (u n)]) ω ∂μ :=
              integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hSm hint
                (hD2.integrable one_le_two))
          _ = 0 := by
              rw [integral_congr_ae ((hD0 n).mono fun ω h => by
                show S ω * μ[D' n | 𝓖 (u n)] ω = (0 : Ω → ℝ) ω
                rw [h]; simp)]
              simp
      have heq : (fun ω => (∑ k ∈ Finset.range (n + 1), D' k ω) ^ 2) =
          fun ω => S ω ^ 2 + 2 * (S ω * D' n ω) + D' n ω ^ 2 := by
        funext ω
        simp only [Finset.sum_range_succ, hS]
        ring
      refine ⟨?_, ?_⟩
      · have := hS2.add hD2
        convert this using 1
        funext ω
        simp [Finset.sum_range_succ, hS]
      · have i1 : Integrable (fun ω => S ω ^ 2) μ := hS2.integrable_sq
        have i2 : Integrable (fun ω => 2 * (S ω * D' n ω)) μ := hint.const_mul 2
        have i3 : Integrable (fun ω => D' n ω ^ 2) μ := hD2.integrable_sq
        have i12 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω * D' n ω)) μ := i1.add i2
        rw [heq, integral_add i12 i3, integral_add i1 i2, integral_const_mul, hSD]
        push_cast
        linarith
  -- identification of the sum
  have hfin : ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range m,
        (stochInt 𝓖 μ B b (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B b (itoProdGrid t m k) ω) *
          (stochInt 𝓖 μ B d (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B d (itoProdGrid t m k) ω) -
        ∫ s in (0 : ℝ)..t, ∑' i, b i s ω * d i s ω) = ∑ k ∈ Finset.range m, D' k ω := by
    filter_upwards [ae_all_iff.2 fun k => stochInt_tail hB hb (u k),
      ae_all_iff.2 fun k => stochInt_tail hB hd (u k), ae_all_iff.2 hDD', hgood]
      with ω h1 h2 h3 h4
    have hsplit : ∑ k ∈ Finset.range m, ∫ r in (u k : ℝ)..(u (k + 1)), ∑' i, b i r ω * d i r ω =
        ∫ r in (0 : ℝ)..t, ∑' i, b i r ω * d i r ω := by
      have := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => (u k : ℝ))
        (n := m) (f := fun r => ∑' i, b i r ω * d i r ω) (μ := volume) fun k hk => by
          refine h4.2.mono_set ?_
          rw [Set.uIcc_of_le (by exact_mod_cast hmono k), Set.uIcc_of_le (NNReal.coe_nonneg t)]
          exact Set.Icc_subset_Icc (NNReal.coe_nonneg _)
            (by exact_mod_cast itoProdGrid_le t (by omega : k + 1 ≤ m))
      simpa [hu, itoProdGrid_zero, itoProdGrid_self t hm.ne'] using this
    rw [← hsplit, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h3 k]
    simp only [hD, h1 k (u (k + 1)), h2 k (u (k + 1)), min_eq_right (hmono k),
      integral_tail_mul (hmono k)]
    rfl
  obtain ⟨hS2, hSi⟩ := hind m le_rfl
  rw [lintegral_congr_ae (hfin.mono fun ω h => by rw [h]),
    ← ofReal_integral_eq_lintegral_ofReal hS2.integrable_sq (ae_of_all _ fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hSi

/-- **Quadratic covariation of two Itô integrals.** If `b`, `d` are Itô-integrable with
`∑ᵢ bᵢ², ∑ᵢ dᵢ² ≤ K` at all times `s > 0`, then
`𝔼[(∑_{k < m} ΔI_k(b) ΔI_k(d) - ∫_0^t ∑ᵢ bᵢ dᵢ ds)²] → 0`, where
`ΔI_k(b) = I_{t_{k+1}}(b) - I_{t_k}(b)`, `t_k = k t / m`. -/
theorem itoProd_tendsto_covariation (hB : IsBrownianFamily 𝓖 B μ) {b d : ι → ℝ → Ω → ℝ}
    (hb : IsItoIntegrable 𝓖 μ b) (hd : IsItoIntegrable 𝓖 μ d) {K : ℝ}
    (hbK : ∀ ω (s : ℝ), 0 < s → ∑' i, b i s ω ^ 2 ≤ K)
    (hdK : ∀ ω (s : ℝ), 0 < s → ∑' i, d i s ω ^ 2 ≤ K) (t : ℝ≥0) :
    Tendsto (fun m : ℕ => ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range m,
        (stochInt 𝓖 μ B b (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B b (itoProdGrid t m k) ω) *
          (stochInt 𝓖 μ B d (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B d (itoProdGrid t m k) ω) -
        ∫ s in (0 : ℝ)..t, ∑' i, b i s ω * d i s ω) ^ 2) ∂μ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (14 * K ^ 2 * (t : ℝ) ^ 2 / m)) atTop
      (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat
      (14 * K ^ 2 * (t : ℝ) ^ 2))
    rwa [ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  refine (covariation_bound hB hb hd hbK hdK t hm).trans_eq ?_
  congr 1
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

end QSSEPtoKPZ
