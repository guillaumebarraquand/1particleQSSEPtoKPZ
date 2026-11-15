/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Prop72NoiseStep1
public import QSSEPtoKPZ.WhiteNoise.Prop72NoiseAux
public import QSSEPtoKPZ.WhiteNoise.Product

/-!
# Proposition 7.2, Step 2: the integrands defining the white noise (task J1)

The white noise of Step 2 is `ξ_t(A) = ((𝟙_{Z>0}/Z) 𝟙_A) · M(t) + ∫_0^t ∫_A 𝟙_{Z=0} ξ'(ds dy)`.
Its distribution function is built from the intervals `I_x = (0, x]` (`x ≥ 0`) and `(x, 0]`
(`x < 0`, with a sign), through the signed indicator `e_x = 𝟙_{(0,x]} - 𝟙_{(x,0]}`
(`prop72NoiseE`), for which `e_b - e_a = 𝟙_{(a,b]}` when `a ≤ b`.

* `prop72NoiseZp Z r x ω = Z(r⁺, x, ω)`: the field `Z` with its values at negative times replaced,
  so that it is jointly measurable (`Z` itself is only predictable on `ℝ₊`);
* `prop72NoiseH Z x = 𝟙_{Z>0} e_x / Z`: the integrand of the martingale-measure part;
* `prop72NoiseK Z T x = e_x` except on `{0 < r ≤ T, Z > 0}`, where it is `0`: the integrand of
  the part driven by the auxiliary noise `ξ'` (which alone drives `ξ` after time `T`).

We also restate Step 1 (`prop72Noise_hasCovariation`) for the intensity `q = Zp²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The signed indicator `e_x = 𝟙_{(0,x]} - 𝟙_{(x,0]}`. -/
def prop72NoiseE (x y : ℝ) : ℝ :=
  (if 0 < y ∧ y ≤ x then 1 else 0) - (if x < y ∧ y ≤ 0 then 1 else 0)

/-- `Z(r⁺, x, ω)`. -/
def prop72NoiseZp (Z : ℝ → ℝ → Ω → ℝ) (r x : ℝ) (ω : Ω) : ℝ := Z (r.toNNReal : ℝ) x ω

/-- The integrand `𝟙_{Z>0} e_x / Z` of the martingale-measure part of `ξ_t(I_x)`. -/
def prop72NoiseH (Z : ℝ → ℝ → Ω → ℝ) (x r y : ℝ) (ω : Ω) : ℝ :=
  if 0 < prop72NoiseZp Z r y ω then prop72NoiseE x y / prop72NoiseZp Z r y ω else 0

/-- The integrand `(1 - 𝟙_{0 < r ≤ T, Z > 0}) e_x` of the part of `ξ_t(I_x)` driven by `ξ'`. -/
def prop72NoiseK {Ω'' : Type*} (Z : ℝ → ℝ → Ω → ℝ) (T x r y : ℝ) (ω : Ω × Ω'') : ℝ :=
  if 0 < r ∧ r ≤ T ∧ 0 < prop72NoiseZp Z r y ω.1 then 0 else prop72NoiseE x y

theorem prop72NoiseZp_of_nonneg (Z : ℝ → ℝ → Ω → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : ℝ) (ω : Ω) :
    prop72NoiseZp Z r x ω = Z r x ω := by
  simp [prop72NoiseZp, Real.coe_toNNReal r hr]

theorem prop72NoiseE_measurable (x : ℝ) : Measurable (prop72NoiseE x) := by
  unfold prop72NoiseE
  exact (Measurable.ite (measurableSet_Ioc (a := 0) (b := x)) measurable_const
    measurable_const).sub (Measurable.ite (measurableSet_Ioc (a := x) (b := 0))
      measurable_const measurable_const)

/-- `e_b - e_a = 𝟙_{(a,b]}` for `a ≤ b`. -/
theorem prop72NoiseE_sub {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    prop72NoiseE b y - prop72NoiseE a y = if a < y ∧ y ≤ b then 1 else 0 := by
  unfold prop72NoiseE
  by_cases hy : 0 < y
  · have h1 : ¬ (b < y ∧ y ≤ 0) := fun h => by linarith [h.2]
    have h2 : ¬ (a < y ∧ y ≤ 0) := fun h => by linarith [h.2]
    simp only [h1, h2, ite_false, sub_zero]
    by_cases hb : y ≤ b
    · by_cases ha : y ≤ a
      · simp [hy, hb, ha, not_lt.2 ha]
      · simp [hy, hb, ha, lt_of_not_ge ha]
    · have ha : ¬ y ≤ a := fun h => hb (h.trans hab)
      simp [hb, ha]
  · have hy' : y ≤ 0 := le_of_not_gt hy
    have h1 : ¬ (0 < y ∧ y ≤ b) := fun h => hy h.1
    have h2 : ¬ (0 < y ∧ y ≤ a) := fun h => hy h.1
    simp only [h1, h2, ite_false, zero_sub, hy', and_true]
    by_cases hb : b < y
    · have ha : a < y := lt_of_le_of_lt hab hb
      simp [hb, ha, not_le.2 hb]
    · by_cases ha : a < y
      · simp [hb, ha, le_of_not_gt hb]
      · simp [hb, ha]

/-- `|e_x| ≤ 1`. -/
theorem prop72NoiseE_abs_le (x y : ℝ) : |prop72NoiseE x y| ≤ 1 := by
  unfold prop72NoiseE
  split_ifs with h1 h2 h2 <;> norm_num

/-- `e_x² ≤ 𝟙_{[-|x|, |x|]}`. -/
theorem prop72NoiseE_sq_le (x y : ℝ) :
    prop72NoiseE x y ^ 2 ≤ (Set.Icc (-|x|) |x|).indicator 1 y := by
  by_cases hy : y ∈ Set.Icc (-|x|) |x|
  · rw [Set.indicator_of_mem hy, Pi.one_apply]
    have := prop72NoiseE_abs_le x y
    nlinarith [abs_nonneg (prop72NoiseE x y), sq_abs (prop72NoiseE x y)]
  · rw [Set.indicator_of_notMem hy]
    have h0 : prop72NoiseE x y = 0 := by
      unfold prop72NoiseE
      have h1 : ¬ (0 < y ∧ y ≤ x) := fun h => hy ⟨by linarith [abs_nonneg x], h.2.trans (le_abs_self x)⟩
      have h2 : ¬ (x < y ∧ y ≤ 0) := fun h => hy ⟨by linarith [neg_abs_le x], by linarith [abs_nonneg x]⟩
      simp [h1, h2]
    rw [h0]; norm_num

/-- `∫ e_x² ≤ 2|x| < ∞`, in `[0, ∞]`. -/
theorem prop72NoiseE_lintegral_lt_top (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (prop72NoiseE x y ^ 2) < ⊤ := by
  calc ∫⁻ y, ENNReal.ofReal (prop72NoiseE x y ^ 2)
      ≤ ∫⁻ y, (Set.Icc (-|x|) |x|).indicator 1 y := lintegral_mono fun y => by
        have h := prop72NoiseE_sq_le x y
        by_cases hy : y ∈ Set.Icc (-|x|) |x|
        · rw [Set.indicator_of_mem hy] at h ⊢
          simpa using ENNReal.ofReal_le_ofReal h
        · rw [Set.indicator_of_notMem hy] at h ⊢
          simp [ENNReal.ofReal_eq_zero.2 h]
    _ = volume (Set.Icc (-|x|) |x|) := lintegral_indicator_one measurableSet_Icc
    _ < ⊤ := measure_Icc_lt_top

/-- `∫_0^T ∫ e_x²` is finite, uniformly in `ω` (iterated lower integrals). -/
theorem prop72NoiseE_lintegral3_lt_top {μ : Measure Ω} [IsFiniteMeasure μ] (T x : ℝ) :
    ∫⁻ _ω, (∫⁻ _r in Set.Icc (0 : ℝ) T, ∫⁻ y, ENNReal.ofReal (prop72NoiseE x y ^ 2)) ∂μ < ⊤ := by
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (prop72NoiseE_lintegral_lt_top x)
    measure_Icc_lt_top) (measure_lt_top μ _)

variable {𝒢 : Filtration ℝ≥0 mΩ} {Z : ℝ → ℝ → Ω → ℝ}

/-- `Zp` is predictable when `Z` is. -/
theorem prop72NoiseZp_pred
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2) :
    MMPred 𝒢 (prop72NoiseZp Z) := by
  unfold MMPred
  have e : (fun p : (ℝ≥0 × Ω) × ℝ => prop72NoiseZp Z p.1.1 p.2 p.1.2) =
      fun p => Z p.1.1 p.2 p.1.2 := by
    funext p; simp [prop72NoiseZp]
  rw [e]; exact hZp

/-- `Zp` is jointly measurable on `Ω × ℝ × ℝ`. -/
theorem prop72NoiseZp_measurable
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2) :
    Measurable fun p : Ω × ℝ × ℝ => prop72NoiseZp Z p.2.1 p.2.2 p.1 := by
  have := (prop72NoiseZp_pred hZp).lift
  convert this using 2 with p
  simp [prop72NoiseZp]

/-- The integrand `𝟙_{Z>0} e_x / Z` is predictable. -/
theorem prop72NoiseH_pred
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (x : ℝ) : MMPred 𝒢 (prop72NoiseH Z x) := by
  have hz := prop72NoiseZp_pred hZp
  have he : MMPred 𝒢 fun _ y _ => prop72NoiseE x y := mmPred_of_measurable (prop72NoiseE_measurable x)
  unfold MMPred at hz he ⊢
  unfold prop72NoiseH
  exact Measurable.ite (measurableSet_lt measurable_const hz) (he.div hz) measurable_const

/-- `(𝟙_{Z>0} e_x / Z)² Z² ≤ e_x²`. -/
theorem prop72NoiseH_sq_mul_le (x r y : ℝ) (ω : Ω) :
    prop72NoiseH Z x r y ω ^ 2 * prop72NoiseZp Z r y ω ^ 2 ≤ prop72NoiseE x y ^ 2 := by
  unfold prop72NoiseH
  split_ifs with h
  · rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 h.ne')]
  · simp [sq_nonneg]

/-- The energy `𝔼 ∫_0^T ∫ (𝟙_{Z>0} e_x / Z)² Z²` is finite. -/
theorem prop72NoiseH_energy {μ : Measure Ω} [IsFiniteMeasure μ] (T x : ℝ) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ y,
      ENNReal.ofReal (prop72NoiseH Z x r y ω ^ 2 * prop72NoiseZp Z r y ω ^ 2)) ∂μ < ⊤ :=
  lt_of_le_of_lt (mm_lintegral3_mono fun r y ω =>
    ENNReal.ofReal_le_ofReal (prop72NoiseH_sq_mul_le x r y ω))
    (prop72NoiseE_lintegral3_lt_top T x)

/-- The intensity `q = Zp²` has finite mass `𝔼 ∫_0^T ∫ q < ∞` ((7.1)). -/
theorem prop72Noise_hq1 {μ : Measure Ω} {T : ℝ}
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂μ < ⊤) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (prop72NoiseZp Z r x ω ^ 2)) ∂μ
      < ⊤ := by
  refine lt_of_le_of_lt (le_of_eq ?_) hZ2
  refine lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only [prop72NoiseZp_of_nonneg Z hr.1]

/-- **(7.9)** for the intensity `Zp²`: `⟨M^φ, M^ψ⟩_t = ∫_0^t ∫ Zp² φ ψ`. -/
theorem prop72Noise_hMZ {Pr : Measure Ω} [IsProbabilityMeasure Pr] {T : ℝ} (hT : 0 < T)
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {φ ψ : ℝ → ℝ} {C C' : ℝ} (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C)
    (hψ : IsC13 T (fun _ => ψ) (fun _ _ => 0) C') :
    HasCovariation T 𝒢 (limMart Y (fun _ => φ) (fun _ _ => 0))
      (limMart Y (fun _ => ψ) (fun _ _ => 0))
      (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, prop72NoiseZp Z r x ω ^ 2 * φ x * ψ x) Pr := by
  refine (prop72Noise_hasCovariation hT hZp hZ2 hmart hφ hψ).mmCongrCov hT.le
    (ae_of_all _ fun ω t ht => ?_)
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le ht.1] at hr
  simp only [prop72NoiseZp_of_nonneg Z hr.1]

end QSSEPtoKPZ
