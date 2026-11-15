/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.L2Bound
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Mollifiers `ρ_ε`: approximate identity, Young's inequality (task G3)

Generic facts on `ρ_ε(x) = ρ(x/ε)/ε` for a mollifier `ρ` (Section 6 of the article), used by
`LimitPoints/Density.lean` and `LimitPoints/Mollify.lean`:

* `mollif_rhoEps_nonneg`, `mollif_rhoEps_eq_zero`, `mollif_rhoEps_le`, `mollif_integral_rhoEps`:
  `ρ_ε ≥ 0`, `ρ_ε(z) = 0` for `|z| ≥ ε`, `ρ_ε ≤ ‖ρ‖_∞ / ε`, `∫ ρ_ε = 1`;
* `mollif_ae_tendsto`: **Lebesgue's differentiation theorem for mollifiers**: for `w` locally
  integrable, `(ρ_ε ⋆ w)(x) → w(x)` as `ε → 0⁺` for almost every `x` (from Mathlib's version for
  balls, `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`);
* `mollif_lintegral_sq_le`: **Young's inequality** `‖ρ_ε ⋆ w‖₂² ≤ ‖w‖₂²` (pointwise
  Cauchy–Schwarz `(ρ_ε ⋆ w)² ≤ ρ_ε ⋆ w²`, then Tonelli).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {ρ : ℝ → ℝ}

/-! ### Elementary facts on `ρ_ε` -/

/-- `ρ_ε` is continuous. -/
theorem mollif_rhoEps_continuous (hρ : IsMollifier ρ) (ε : ℝ) : Continuous (rhoEps ρ ε) :=
  show Continuous fun x => ρ (x / ε) / ε from
    (hρ.continuous.comp (continuous_id.div_const ε)).div_const ε

/-- `ρ_ε ≥ 0` for `ε ≥ 0`. -/
theorem mollif_rhoEps_nonneg (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ rhoEps ρ ε x :=
  div_nonneg (hρ.nonneg _) hε

/-- `ρ_ε(z) = 0` for `|z| ≥ ε > 0`. -/
theorem mollif_rhoEps_eq_zero (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {z : ℝ}
    (hz : ε ≤ |z|) : rhoEps ρ ε z = 0 := by
  rw [rhoEps, hρ.zero_of_one_le, zero_div]
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε, one_mul]
  exact hz

/-- `‖ρ‖_∞ = sup_x |ρ(x)|`. -/
def mollifSup (ρ : ℝ → ℝ) : ℝ := ⨆ x, |ρ x|

/-- `|ρ| ≤ ‖ρ‖_∞` (`ρ` is continuous with compact support, hence bounded). -/
theorem mollif_abs_le_sup (hρ : IsMollifier ρ) (x : ℝ) : |ρ x| ≤ mollifSup ρ := by
  obtain ⟨M, hM⟩ := hρ.continuous.bounded_above_of_compact_support hρ.hasCompactSupport
  exact le_ciSup (f := fun x => |ρ x|) ⟨M, by rintro _ ⟨y, rfl⟩; simpa using hM y⟩ x

/-- `‖ρ‖_∞ ≥ 0`. -/
theorem mollifSup_nonneg (hρ : IsMollifier ρ) : 0 ≤ mollifSup ρ :=
  (abs_nonneg _).trans (mollif_abs_le_sup hρ 0)

/-- `ρ_ε ≤ ‖ρ‖_∞ / ε`. -/
theorem mollif_rhoEps_le (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    rhoEps ρ ε x ≤ mollifSup ρ / ε := by
  rw [rhoEps]
  exact div_le_div_of_nonneg_right ((le_abs_self _).trans (mollif_abs_le_sup hρ _)) hε.le

/-- `|ρ_ε| ≤ ‖ρ‖_∞ / ε`. -/
theorem mollif_abs_rhoEps_le (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |rhoEps ρ ε x| ≤ mollifSup ρ / ε := by
  rw [abs_of_nonneg (mollif_rhoEps_nonneg hρ hε.le x)]
  exact mollif_rhoEps_le hρ hε x

/-- `ρ_ε` has compact support. -/
theorem mollif_rhoEps_hasCompactSupport (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (rhoEps ρ ε) :=
  HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun x hx => by
    refine mollif_rhoEps_eq_zero hρ hε ?_
    by_contra h
    exact hx (abs_le.1 (not_le.1 h).le)

/-- `ρ_ε` is integrable. -/
theorem mollif_rhoEps_integrable (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (rhoEps ρ ε) :=
  (mollif_rhoEps_continuous hρ ε).integrable_of_hasCompactSupport
    (mollif_rhoEps_hasCompactSupport hρ hε)

/-- `∫ ρ_ε = 1` for `ε > 0`. -/
theorem mollif_integral_rhoEps (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, rhoEps ρ ε x = 1 := by
  show ∫ x, ρ (x / ε) / ε = 1
  rw [integral_div, Measure.integral_comp_div ρ ε, hρ.integral_eq_one, abs_of_pos hε,
    smul_eq_mul, mul_one, div_self hε.ne']

/-- `∫ ρ_ε(x - y) dy = 1` and `∫ ρ_ε(y - x) dy = 1`. -/
theorem mollif_integral_rhoEps_sub (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∫ y, rhoEps ρ ε (x - y) = 1 ∧ ∫ y, rhoEps ρ ε (y - x) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [integral_sub_left_eq_self (rhoEps ρ ε) volume x]
    exact mollif_integral_rhoEps hρ hε
  · rw [integral_sub_right_eq_self (rhoEps ρ ε) x]
    exact mollif_integral_rhoEps hρ hε

/-- `∫⁻ ρ_ε(y - x) dy = 1`. -/
theorem mollif_lintegral_rhoEps_sub (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (rhoEps ρ ε (y - x)) = 1 := by
  rw [lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (rhoEps ρ ε y)) x,
    ← ofReal_integral_eq_lintegral_ofReal (mollif_rhoEps_integrable hρ hε)
      (ae_of_all _ (mollif_rhoEps_nonneg hρ hε.le)), mollif_integral_rhoEps hρ hε,
    ENNReal.ofReal_one]

/-! ### Lebesgue's differentiation theorem for mollifiers -/

/-- **Lebesgue's differentiation theorem for the mollifiers `ρ_ε`**: for a locally integrable `w`,
`∫ ρ_ε(x - y) w(y) dy → w(x)` as `ε → 0⁺`, for almost every `x`. -/
theorem mollif_ae_tendsto (hρ : IsMollifier ρ) {w : ℝ → ℝ} (hw : LocallyIntegrable w volume) :
    ∀ᵐ x, Tendsto (fun ε => ∫ y, rhoEps ρ ε (x - y) * w y) (𝓝[>] 0) (𝓝 (w x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hw 1] with x hx
  have hav := hx (fun _ => x) id tendsto_id
    (eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
      simp [Metric.mem_closedBall, hε.le])
  refine tendsto_integral_smul_of_tendsto_average_norm_sub (2 * mollifSup ρ)
    (a := fun ε => Metric.closedBall x ε) (g := fun ε y => rhoEps ρ ε (x - y)) hav
    (Eventually.of_forall fun ε => hw.integrableOn_isCompact (isCompact_closedBall x ε)) ?_ ?_ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (mollif_integral_rhoEps_sub hρ hε x).1.symm
  · filter_upwards [eventually_mem_nhdsWithin] with ε (hε : 0 < ε)
    intro y hy
    by_contra h
    refine hy (mollif_rhoEps_eq_zero hρ hε ?_)
    rw [Metric.mem_closedBall, Real.dist_eq, not_le, abs_sub_comm] at h
    exact h.le
  · filter_upwards [eventually_mem_nhdsWithin] with ε (hε : 0 < ε)
    intro y
    rw [Real.volume_real_closedBall hε.le, mul_div_mul_left _ _ two_ne_zero]
    exact mollif_abs_rhoEps_le hρ hε _

/-! ### Young's inequality in `L²` -/

/-- Pointwise Cauchy–Schwarz: for `a ≥ 0` with `∫ a = 1`, `(∫ a w)² ≤ ∫ a w²`. -/
private lemma mollif_sq_integral_le {a w : ℝ → ℝ} (ha0 : ∀ x, 0 ≤ a x) (ha : Integrable a)
    (ha1 : ∫ x, a x = 1) (haw : Integrable fun x => a x * w x)
    (haw2 : Integrable fun x => a x * w x ^ 2) :
    (∫ x, a x * w x) ^ 2 ≤ ∫ x, a x * w x ^ 2 := by
  set c := ∫ x, a x * w x
  have e : (fun x => a x * (w x - c) ^ 2) =
      fun x => a x * w x ^ 2 - 2 * c * (a x * w x) + c ^ 2 * a x := by
    ext x; ring
  have h0 : 0 ≤ ∫ x, a x * (w x - c) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (ha0 x) (sq_nonneg _)
  have h1 : ∫ x, (a x * w x ^ 2 - 2 * c * (a x * w x) + c ^ 2 * a x) =
      (∫ x, a x * w x ^ 2) - 2 * c * c + c ^ 2 := by
    rw [integral_add ?_ (ha.const_mul _), integral_sub haw2 (haw.const_mul _), integral_const_mul,
      integral_const_mul, ha1, mul_one]
    exact haw2.sub (haw.const_mul _)
  rw [e, h1] at h0
  nlinarith

/-- `x ↦ ρ_ε(y - x) w(x)` is integrable when `w² ` is integrable and `w` is measurable. -/
theorem mollif_integrable_mul (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℝ}
    (hw : AEStronglyMeasurable w volume) (hw2 : Integrable fun x => w x ^ 2) (y : ℝ) :
    Integrable fun x => rhoEps ρ ε (y - x) * w x := by
  have hr2 : Integrable fun x => rhoEps ρ ε (y - x) ^ 2 := by
    have hcs : HasCompactSupport fun x => rhoEps ρ ε x ^ 2 := by
      have := (mollif_rhoEps_hasCompactSupport hρ hε).mul_left (f' := rhoEps ρ ε) (f := rhoEps ρ ε)
      simp only [sq]
      exact this
    have : Integrable fun x => rhoEps ρ ε x ^ 2 :=
      ((mollif_rhoEps_continuous hρ ε).pow 2).integrable_of_hasCompactSupport hcs
    exact this.comp_sub_left y
  refine ((hr2.add hw2).div_const 2).mono'
    (((mollif_rhoEps_continuous hρ ε).comp (continuous_const.sub continuous_id))
      |>.aestronglyMeasurable.mul hw) (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  set A := |rhoEps ρ ε (y - x)|
  set B := |w x|
  have hA : rhoEps ρ ε (y - x) ^ 2 = A ^ 2 := (sq_abs _).symm
  have hB : w x ^ 2 = B ^ 2 := (sq_abs _).symm
  rw [hA, hB]
  nlinarith [sq_nonneg (A - B)]

/-- `x ↦ ρ_ε(y - x) w(x)²` is integrable when `w²` is integrable. -/
theorem mollif_integrable_mul_sq (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℝ}
    (hw2 : Integrable fun x => w x ^ 2) (y : ℝ) :
    Integrable fun x => rhoEps ρ ε (y - x) * w x ^ 2 :=
  hw2.bdd_mul (c := mollifSup ρ / ε)
    ((mollif_rhoEps_continuous hρ ε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact mollif_abs_rhoEps_le hρ hε _)

/-- **Young's inequality** for the mollifier: `∫ (∫ ρ_ε(y - x) w(x) dx)² dy ≤ ∫ w²`, in `[0, ∞]`. -/
theorem mollif_lintegral_sq_le (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {w : ℝ → ℝ}
    (hw : Measurable w) (hw2 : Integrable fun x => w x ^ 2) :
    ∫⁻ y, ENNReal.ofReal ((∫ x, rhoEps ρ ε (y - x) * w x) ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (w x ^ 2) := by
  have hr := mollif_rhoEps_continuous hρ ε
  calc ∫⁻ y, ENNReal.ofReal ((∫ x, rhoEps ρ ε (y - x) * w x) ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal (∫ x, rhoEps ρ ε (y - x) * w x ^ 2) := by
        refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        exact mollif_sq_integral_le (a := fun x => rhoEps ρ ε (y - x))
          (fun x => mollif_rhoEps_nonneg hρ hε.le _)
          ((mollif_rhoEps_integrable hρ hε).comp_sub_left y)
          ((integral_sub_left_eq_self (rhoEps ρ ε) volume y).trans (mollif_integral_rhoEps hρ hε))
          (mollif_integrable_mul hρ hε hw.aestronglyMeasurable hw2 y)
          (mollif_integrable_mul_sq hρ hε hw2 y)
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (rhoEps ρ ε (y - x)) * ENNReal.ofReal (w x ^ 2) := by
        refine lintegral_congr fun y => ?_
        rw [ofReal_integral_eq_lintegral_ofReal (mollif_integrable_mul_sq hρ hε hw2 y)
          (ae_of_all _ fun x => mul_nonneg (mollif_rhoEps_nonneg hρ hε.le _) (sq_nonneg _))]
        exact lintegral_congr fun x => ENNReal.ofReal_mul (mollif_rhoEps_nonneg hρ hε.le _)
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (rhoEps ρ ε (y - x)) * ENNReal.ofReal (w x ^ 2) := by
        refine lintegral_lintegral_swap ?_
        refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable.mul
          (ENNReal.measurable_ofReal.comp ((hw.comp measurable_snd).pow_const 2)).aemeasurable
        exact (hr.comp (continuous_fst.sub continuous_snd)).measurable
    _ = ∫⁻ x, ENNReal.ofReal (w x ^ 2) := by
        refine lintegral_congr fun x => ?_
        have hm : Measurable fun y => ENNReal.ofReal (rhoEps ρ ε (y - x)) :=
          ENNReal.measurable_ofReal.comp (hr.measurable.comp (measurable_id.sub_const x))
        rw [lintegral_mul_const _ hm,
          mollif_lintegral_rhoEps_sub hρ hε x, one_mul]

end QSSEPtoKPZ
