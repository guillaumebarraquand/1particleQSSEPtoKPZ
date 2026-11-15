/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.AtomicTV
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.Tightness.FiniteMeasureEmbed

/-!
# The measures `𝒵_n` of a finite system: identities, versions, closeness (task M2)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task M2.
`docs/stage5-design.md`, Sections 1.2 (f), 3.5.

* `rescaledMeasure_eq_box`: `𝒵_n(t) = ϱ_n(t) 𝖹^L_n(t)` for every `L` (as (3.8), which is the case
  `L = ∞`, Stage 2's `rescaledMeasure_eq`).
* `exists_rescaledPath_version_box`: for a wave function on a finite box, `(𝒵_n(t))_{t ∈ [0,T]}`
  has an almost everywhere measurable version with values in `C([0,T], ℳ₊)` (a finite sum of
  atoms with continuous weights and positions; measurability by
  `measurable_pathFiniteMeasure_iff_tightEmb`).
* `abs_integral_rescaledMeasure_box_sub_le`: the closeness bound of the proof of Theorem 1.2,
  `|𝒵^L_n(t)(f) - 𝒵_n(t)(f)| ≤ ‖f‖_∞ ϱ_n(t) ∑ₓ |𝔷^L_n(t,x) - 𝔷_n(t,x)|`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-! ### The identity `𝒵_n = ϱ_n 𝖹^L_n` -/

/-- The weight of the atom at `y_n(t,y)` in `𝒵_n(t)`: `n^{-1/2} Z_n(t,y_n(t,y)) = ϱ_n(t) 𝔷_n(t,y)`
(the pointwise identity behind (3.8)). -/
private lemma boxVer_weight {n : ℝ} (hn : 1 ≤ n) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ)
    (y : ℤ) :
    n ^ (-1 / 2 : ℝ) * rescaledField n (density ψ ω) t y = varrhoN n t * zN n ψ ω t y := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  set a := n ^ (1 / 4 : ℝ) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hn0 _
  have hpow : ∀ k : ℕ, n ^ ((k : ℝ) / 4) = a ^ k := fun k => by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have h2 : n ^ (1 / 2 : ℝ) = a ^ 2 := by rw [← hpow 2]; norm_num
  have h3 : n ^ (3 / 4 : ℝ) = a ^ 3 := by rw [← hpow 3]; norm_num
  have hm : n ^ (-1 / 2 : ℝ) = (a ^ 2)⁻¹ := by
    rw [← h2, ← Real.rpow_neg hn0.le]; norm_num
  have hq : thetaN n = a⁻¹ := by
    rw [thetaN, ha_def, ← Real.rpow_neg hn0.le]; norm_num
  unfold rescaledField zN varrhoN rescaledPosition
  rw [h2, h3, hm, hq]
  have hx : a ^ 2 * t / 2 + a * ((y - a ^ 3 * t) / a ^ 2) - t / 24 =
      (n * lambdaN n / 2 - a ^ 2 / 2 - 1 / 24) * t + (a⁻¹ * y - n * lambdaN n / 2 * t) := by
    field_simp
    ring
  rw [hx, Real.exp_add]
  field_simp

/-- **(3.8) on `Λ_L`**: `rescaledMeasure L n P t = ϱ_n(t) · 𝖹^L_n(t)`, `P = density ψ ω`, for every
`L ∈ ℕ ∪ {∞}`, every realization and every real `t`. -/
theorem rescaledMeasure_eq_box {n : ℝ} (hn : 1 ≤ n) (L : ℕ∞) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω)
    (t : ℝ) :
    rescaledMeasure L n (density ψ ω) t =
      ENNReal.ofReal (varrhoN n t) • tiltedMeasureBox L n ψ ω t := by
  have hv : 0 ≤ varrhoN n t := (Real.exp_pos _).le
  ext s hs
  rw [Measure.smul_apply, rescaledMeasure, tiltedMeasureBox, Measure.sum_apply _ hs,
    Measure.sum_apply _ hs, smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hv, boxVer_weight hn]

/-! ### Finite boxes -/

/-- `Λ_L = {-L, …, L}` for finite `L`. -/
private lemma boxVer_box_eq (L : ℕ) :
    box (L : ℕ∞) = ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ) := by
  ext x
  simp only [box, Finset.coe_Icc, Set.mem_Icc]
  change ((x.natAbs : ℕ) : ℕ∞) ≤ (L : ℕ∞) ↔ _
  rw [ENat.natCast_le_natCast]
  omega

/-- `Λ_L` is finite for finite `L`. -/
private lemma boxVer_finite (L : ℕ) : (box (L : ℕ∞)).Finite := by
  rw [boxVer_box_eq]; exact Finset.finite_toSet _

/-- For finite `L`, `𝒵_n(t)` (a finite sum of finite atoms) is a finite measure. -/
private lemma boxVer_isFinite (L : ℕ) (n : ℝ) (P : ℝ → ℤ → ℝ) (t : ℝ) :
    IsFiniteMeasure (rescaledMeasure (L : ℕ∞) n P t) := by
  have := (boxVer_finite L).fintype
  refine ⟨?_⟩
  rw [rescaledMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun y _ => ?_
  simp

/-- `𝒵_n(t)` as an element of `ℳ₊(ℝ) = FiniteMeasure ℝ`, for finite `L`. -/
private def boxVerFM (L : ℕ) (n : ℝ) (P : ℝ → ℤ → ℝ) (t : ℝ) : FiniteMeasure ℝ :=
  ⟨rescaledMeasure (L : ℕ∞) n P t, boxVer_isFinite L n P t⟩

/-- `∫ f d𝒵_n(t) = ∑_{y ∈ Λ_L} (n^{-1/2} Z_n(t,y))⁺ f(y_n(t,y))` for finite `L`. -/
private lemma boxVer_integral (L : ℕ) (n : ℝ) (P : ℝ → ℤ → ℝ) (t : ℝ) (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(boxVerFM L n P t : Measure ℝ) =
      ∑' y : box (L : ℕ∞), max (n ^ (-1 / 2 : ℝ) * rescaledField n P t y) 0 *
        f (rescaledPosition n t y) := by
  have := boxVer_isFinite L n P t
  change ∫ x, f x ∂(rescaledMeasure (L : ℕ∞) n P t) = _
  have hi : Integrable f (rescaledMeasure (L : ℕ∞) n P t) := f.integrable _
  rw [rescaledMeasure] at hi ⊢
  rw [integral_sum_measure hi]
  refine tsum_congr fun y => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal', smul_eq_mul]

/-- On a realization with `t ↦ ψ_t` continuous on `[0, ∞)` and `n ≥ 0`, the path
`t ↦ 𝒵_n(t)` is continuous from `[0,T]` to `ℳ₊(ℝ)` (finite sum of atoms with continuous weights
and positions). -/
private lemma boxVer_continuous (L : ℕ) {n : ℝ} (hn : 0 ≤ n) (T : ℝ) {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    {ω : Ω} (hc : Continuous fun s : ℝ≥0 => ψ s ω) :
    Continuous fun t : Set.Icc (0 : ℝ) T => boxVerFM L n (density ψ ω) t := by
  have := (boxVer_finite L).fintype
  refine FiniteMeasure.continuous_iff_forall_continuous_integral.2 fun f => ?_
  simp_rw [boxVer_integral, tsum_fintype]
  refine continuous_finsetSum _ fun y _ => ?_
  have hs : Continuous fun t : Set.Icc (0 : ℝ) T =>
      (⟨n * t / 2, by have := t.2.1; positivity⟩ : ℝ≥0) :=
    Continuous.subtype_mk (by fun_prop) _
  have hψ : Continuous fun t : Set.Icc (0 : ℝ) T => ψ (n * t / 2) ω y :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 y).continuous.comp (hc.comp hs)
  have hpos : Continuous fun t : Set.Icc (0 : ℝ) T => rescaledPosition n t y := by
    unfold rescaledPosition; fun_prop
  have hden : Continuous fun t : Set.Icc (0 : ℝ) T => density ψ ω (n * t / 2) y :=
    (continuous_norm.comp hψ).pow 2
  unfold rescaledField
  exact ((continuous_const.mul ((continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul
    hden)).max continuous_const).mul (f.continuous.comp hpos)

open Classical in
/-- The path `t ↦ 𝒵_n(t)` on `[0,T]` as an element of `C([0,T], ℳ₊(ℝ))`, when `n ≥ 0` and
`t ↦ ψ_t(ω)` is continuous (the constant path `0` otherwise). -/
private def boxVerPath (L : ℕ) (n T : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) :
    C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  if h : 0 ≤ n ∧ Continuous fun s : ℝ≥0 => ψ s ω then
    ⟨fun t => boxVerFM L n (density ψ ω) t, boxVer_continuous L h.1 T h.2⟩
  else 0

private lemma boxVerPath_apply (L : ℕ) {n : ℝ} (hn : 0 ≤ n) (T : ℝ) {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    {ω : Ω} (hc : Continuous fun s : ℝ≥0 => ψ s ω) (t : Set.Icc (0 : ℝ) T) :
    boxVerPath L n T ψ ω t = boxVerFM L n (density ψ ω) t := by
  simp [boxVerPath, hn, hc]

/-- **Version of `𝒵_n` for a finite box.** For a wave function `ψ` on `Λ_L` (`L` finite), `n ≥ 1`
and `T`, there is an almost everywhere measurable `𝒵 : Ω → C([0,T], ℳ₊)` with, almost surely,
`𝒵(ω)(t) = 𝒵_n(t)` (`rescaledMeasure L n (density ψ ω) t`) for all `t ∈ [0,T]`. -/
theorem exists_rescaledPath_version_box [IsProbabilityMeasure μ] {L : ℕ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), AEMeasurable Zv μ ∧
      ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T,
        (Zv ω t : Measure ℝ) = rescaledMeasure L n (density ψ ω) t := by
  classical
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  -- the good set `S`: measurable, of full measure, made of continuous paths
  set G : Set Ω := {ω | Continuous fun s : ℝ≥0 => ψ s ω} with hG
  set S : Set Ω := (toMeasurable μ Gᶜ)ᶜ with hS_def
  have hGc : μ Gᶜ = 0 := by
    have := hψ.continuous
    rw [ae_iff] at this
    exact this
  have hSc : μ Sᶜ = 0 := by rw [hS_def, compl_compl, measure_toMeasurable, hGc]
  have hSG : ∀ ω ∈ S, Continuous fun s : ℝ≥0 => ψ s ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable μ _ h)
  have hSm : MeasurableSet S := (measurableSet_toMeasurable μ _).compl
  refine ⟨fun ω => if ω ∈ S then boxVerPath L n T ψ ω else 0, Measurable.aemeasurable ?_, ?_⟩
  · refine measurable_pathFiniteMeasure_iff_tightEmb.2 fun t j => ?_
    have := (boxVer_finite L).fintype
    have e : (fun ω => ∫ x, bumpTest j x ∂((if ω ∈ S then boxVerPath L n T ψ ω else 0) t :
          Measure ℝ)) =
        fun ω => if ω ∈ S then ∑ y : box (L : ℕ∞),
          max (n ^ (-1 / 2 : ℝ) * rescaledField n (density ψ ω) t y) 0 *
            bumpTest j (rescaledPosition n t y) else 0 := by
      funext ω
      by_cases hω : ω ∈ S
      · simp only [hω, ite_true]
        rw [boxVerPath_apply L hn0 T (hSG ω hω), boxVer_integral, tsum_fintype]
      · simp [hω]
    rw [e]
    refine Measurable.ite hSm (Finset.measurable_sum _ fun y _ => ?_) measurable_const
    have ht : 0 ≤ n * (t : ℝ) / 2 := by have := t.2.1; positivity
    have h := (hψ.adapted ⟨n * t / 2, ht⟩ y).mono (𝓕.le _) le_rfl
    change Measurable fun ω => ψ (n * t / 2) ω y at h
    unfold rescaledField density
    exact ((measurable_const.mul (measurable_const.mul
      ((continuous_norm.pow 2).measurable.comp h))).max measurable_const).mul measurable_const
  · have : ∀ᵐ ω ∂μ, ω ∈ S := by
      rw [ae_iff]; exact hSc
    filter_upwards [this] with ω hω t
    simp only [hω, ite_true]
    rw [boxVerPath_apply L hn0 T (hSG ω hω)]
    rfl

/-! ### Closeness of `𝒵^L_n` and `𝒵_n` -/

/-- **Closeness of `𝒵^L_n(t)` and `𝒵_n(t)`.** For `n ≥ 1`, a realization `ω` and a time `t` such
that `x ↦ 𝔷_n(t,x)` is summable and `ψ^L_{nt/2}` vanishes outside `Λ_L`, and a bounded continuous
`f`: `|∫ f d𝒵^L_n(t) - ∫ f d𝒵_n(t)| ≤ ‖f‖_∞ ϱ_n(t) ∑ₓ |𝔷^L_n(t,x) - 𝔷_n(t,x)|`. -/
theorem abs_integral_rescaledMeasure_box_sub_le {n : ℝ} (hn : 1 ≤ n) (L : ℕ)
    (ψL ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (hs : Summable (zN n ψ ω t))
    (hsupp : ∀ x, x ∉ box L → ψL (n * t / 2) ω x = 0) (f : ℝ →ᵇ ℝ) :
    |(∫ x, f x ∂(rescaledMeasure L n (density ψL ω) t))
        - ∫ x, f x ∂(rescaledMeasure ⊤ n (density ψ ω) t)| ≤
      ‖f‖ * (varrhoN n t * ∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|) := by
  have hv : 0 ≤ varrhoN n t := (Real.exp_pos _).le
  have hz0 : ∀ x, x ∉ box (L : ℕ∞) → zN n ψL ω t x = 0 := fun x hx => by
    unfold zN density
    rw [hsupp x hx]
    simp
  have hzL : (box (L : ℕ∞)).indicator (zN n ψL ω t) = zN n ψL ω t := by
    funext x
    by_cases hx : x ∈ box (L : ℕ∞)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hz0 x hx]
  have hz : (box ⊤).indicator (zN n ψ ω t) = zN n ψ ω t := by
    rw [Set.eq_univ_of_forall fun x => (by simp [box] : x ∈ box ⊤), Set.indicator_univ]
  have hsL : Summable (zN n ψL ω t) :=
    summable_of_ne_finset_zero (s := Finset.Icc (-(L : ℤ)) L) fun x hx => hz0 x (by
      rw [boxVer_box_eq]; exact hx)
  rw [rescaledMeasure_eq_box hn, rescaledMeasure_eq_box hn, tiltedMeasureBox_eq_sum,
    tiltedMeasureBox_eq_sum, hzL, hz, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hv, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul, abs_of_nonneg hv]
  calc varrhoN n t * |(∫ x, f x ∂(Measure.sum fun x : ℤ =>
          ENNReal.ofReal (zN n ψL ω t x) • Measure.dirac (rescaledPosition n t x)))
        - ∫ x, f x ∂(Measure.sum fun x : ℤ =>
          ENNReal.ofReal (zN n ψ ω t x) • Measure.dirac (rescaledPosition n t x))|
      ≤ varrhoN n t * (‖f‖ * ∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|) :=
        mul_le_mul_of_nonneg_left (abs_integral_sum_dirac_sub_le _ _ _ hsL hs f) hv
    _ = ‖f‖ * (varrhoN n t * ∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|) := by ring

end QSSEPtoKPZ
