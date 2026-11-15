/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Density
public import QSSEPtoKPZ.Replacement.L2Bound

/-!
# Smoothed norms of measures (task G3)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G3.
See `docs/stage4-design.md`, Section 3.2, and `docs/stage4-interfaces.md`.

`smoothedNormSq ν φ ρ ε = ‖(φν) ⋆ ρ_ε‖₂²` (Stage 2, (6.1)).
* continuity in `(μ, ε)` on `ℳ₊ × (0, ∞)` (third term of (7.6), and (7.4) with `ε_n → ε`);
* for a measure with an `L²` density `u`: `‖(φμ) ⋆ ρ_ε‖₂² ≤ ‖φu‖₂²` and `→ ‖φu‖₂²` as `ε → 0`
  (fourth term of (7.6)).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

/-! ### Auxiliary results -/

section MollifAux

variable {ρ : ℝ → ℝ}

/-- The bounded continuous function `((x, y), e) ↦ φ(x) φ(y) κ_{max(e, ε₀/2)}(x - y)`. -/
private def mollifKernel (hρ : IsMollifier ρ) {φ : ℝ → ℝ} (hφ : Continuous φ) {c : ℝ}
    (hc : ∀ x, |φ x| ≤ c) {ε₀ : ℝ} (hε₀ : 0 < ε₀) : (ℝ × ℝ) × ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q => φ q.1.1 * φ q.1.2 * kappaEps ρ (max q.2 (ε₀ / 2)) (q.1.1 - q.1.2))
    (by
      have hκ := hρ.kappa_even_nonneg_smooth.2.2.continuous
      have hm : Continuous fun q : (ℝ × ℝ) × ℝ => max q.2 (ε₀ / 2) :=
        continuous_snd.max continuous_const
      have hm0 : ∀ q : (ℝ × ℝ) × ℝ, max q.2 (ε₀ / 2) ≠ 0 := fun q =>
        (lt_of_lt_of_le (by linarith) (le_max_right _ _)).ne'
      show Continuous fun q : (ℝ × ℝ) × ℝ => φ q.1.1 * φ q.1.2 *
        (kappa ρ ((q.1.1 - q.1.2) / max q.2 (ε₀ / 2)) / max q.2 (ε₀ / 2))
      refine ((hφ.comp (continuous_fst.comp continuous_fst)).mul
        (hφ.comp (continuous_snd.comp continuous_fst))).mul ?_
      exact (hκ.comp (((continuous_fst.comp continuous_fst).sub
        (continuous_snd.comp continuous_fst)).div hm hm0)).div hm hm0)
    (c * c * (kappa ρ 0 / (ε₀ / 2)))
    (fun q => by
      have hm : 0 < max q.2 (ε₀ / 2) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hκ : |kappaEps ρ (max q.2 (ε₀ / 2)) (q.1.1 - q.1.2)| ≤ kappa ρ 0 / (ε₀ / 2) := by
        rw [kappaEps, abs_of_nonneg (div_nonneg (hρ.kappa_nonneg _) hm.le)]
        calc kappa ρ ((q.1.1 - q.1.2) / max q.2 (ε₀ / 2)) / max q.2 (ε₀ / 2)
            ≤ kappa ρ 0 / max q.2 (ε₀ / 2) :=
              div_le_div_of_nonneg_right (hρ.kappa_le _) hm.le
          _ ≤ kappa ρ 0 / (ε₀ / 2) :=
              div_le_div_of_nonneg_left (hρ.kappa_nonneg 0) (by linarith) (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
      gcongr
      exacts [hc _, hc _])

/-- A measurable version `w = φ ũ` of `φ u`, with `ũ ≥ 0` measurable and `ũ = u` a.e.: the inner
integrals of `smoothedNormSq` against `u dx` are `∫ ρ_ε(y - x) w(x) dx`, `w²` is integrable and
`∫ w² = ∫ φ² u²`. -/
private lemma mollif_withDensity_setup {u : ℝ → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hu : MemLp u 2 volume)
    {φ : ℝ → ℝ} (hφ : Measurable φ) (hb : ∃ C, ∀ x, |φ x| ≤ C) :
    ∃ w : ℝ → ℝ, Measurable w ∧ Integrable (fun x => w x ^ 2) ∧
      (∀ ε y, ∫ x, φ x * rhoEps ρ ε (y - x) ∂(volume.withDensity fun x => ENNReal.ofReal (u x))
        = ∫ x, rhoEps ρ ε (y - x) * w x) ∧
      ∫ x, φ x ^ 2 * u x ^ 2 = ∫ x, w x ^ 2 := by
  obtain ⟨c, hc⟩ := hb
  set ũ : ℝ → ℝ := fun x => max (hu.aestronglyMeasurable.mk u x) 0 with hũ
  have hũm : Measurable ũ := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  have hũ0 : ∀ x, 0 ≤ ũ x := fun x => le_max_right _ _
  have hũu : u =ᵐ[volume] ũ := hu.aestronglyMeasurable.ae_eq_mk.mono fun x hx => by
    simp only [hũ, ← hx, max_eq_left (hu0 x)]
  have hν : (volume.withDensity fun x => ENNReal.ofReal (u x)) =
      volume.withDensity fun x => ENNReal.ofReal (ũ x) :=
    withDensity_congr_ae (hũu.mono fun x hx => by
      show ENNReal.ofReal (u x) = ENNReal.ofReal (ũ x); rw [hx])
  have hu2 : Integrable fun x => u x ^ 2 := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
  refine ⟨fun x => φ x * ũ x, hφ.mul hũm, ?_, fun ε y => ?_, ?_⟩
  · refine (hu2.const_mul (c ^ 2)).mono' ((hφ.mul hũm).pow_const 2).aestronglyMeasurable
      (hũu.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, ← hx]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq' (abs_le.1 (hc x)).1 (abs_le.1 (hc x)).2))
      (sq_nonneg _) |>.trans_eq' rfl
  · have hm : Measurable fun x => ENNReal.ofReal (ũ x) := ENNReal.measurable_ofReal.comp hũm
    rw [hν, integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [ENNReal.toReal_ofReal (hũ0 x), smul_eq_mul]
    ring
  · refine integral_congr_ae (hũu.mono fun x hx => ?_)
    simp only
    rw [hx]
    ring

/-- `y ↦ (∫ ρ_ε(y - x) w(x) dx)²` is strongly measurable. -/
private lemma mollif_conv_sq_measurable (hρ : IsMollifier ρ) (ε : ℝ) {w : ℝ → ℝ}
    (hw : Measurable w) :
    StronglyMeasurable fun y => (∫ x, rhoEps ρ ε (y - x) * w x) ^ 2 := by
  have hg : StronglyMeasurable (fun q : ℝ × ℝ => rhoEps ρ ε (q.1 - q.2) * w q.2) :=
    (((mollif_rhoEps_continuous hρ ε).comp (continuous_fst.sub continuous_snd)).measurable.mul
      (hw.comp measurable_snd)).stronglyMeasurable
  exact (hg.integral_prod_right' (ν := volume)).pow 2

/-- `smoothedNormSq` in `[0, ∞]`. -/
private lemma mollif_smoothed_eq_toReal (hρ : IsMollifier ρ) (ε : ℝ) {w : ℝ → ℝ}
    (hw : Measurable w) :
    ∫ y, (∫ x, rhoEps ρ ε (y - x) * w x) ^ 2 =
      (∫⁻ y, ENNReal.ofReal ((∫ x, rhoEps ρ ε (y - x) * w x) ^ 2)).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
    (mollif_conv_sq_measurable hρ ε hw).aestronglyMeasurable

/-- Rewriting `smoothedNormSq` with the inner integrals given by `hconv`. -/
private lemma mollif_smoothedNormSq_eq {ν : Measure ℝ} {φ w : ℝ → ℝ} {ε : ℝ}
    (hconv : ∀ ε y, ∫ x, φ x * rhoEps ρ ε (y - x) ∂ν = ∫ x, rhoEps ρ ε (y - x) * w x) :
    smoothedNormSq ν φ ρ ε = ∫ y, (∫ x, rhoEps ρ ε (y - x) * w x) ^ 2 := by
  unfold smoothedNormSq
  exact integral_congr_ae (ae_of_all _ fun y => by simp only; rw [hconv])

end MollifAux

/-! ### Main results -/

/-- `(μ, ε) ↦ ‖(φμ) ⋆ ρ_ε‖₂²` is continuous on `ℳ₊ × (0, ∞)` for `φ` bounded continuous
(by (6.1), the integral of a bounded continuous function against `μ ⊗ μ`). -/
theorem continuousOn_smoothedNormSq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hb : ∃ C, ∀ x, |φ x| ≤ C) :
    ContinuousOn (fun p : FiniteMeasure ℝ × ℝ => smoothedNormSq (p.1 : Measure ℝ) φ ρ p.2)
      (Set.univ ×ˢ Set.Ioi 0) := by
  rintro ⟨μ₀, ε₀⟩ ⟨-, hε₀ : 0 < ε₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨c, hc⟩ := hb
  set H := mollifKernel hρ hφ hc hε₀
  have hG : Continuous fun p : FiniteMeasure ℝ × ℝ => ∫ q, H q ∂(((p.1.prod p.1).prod
      (diracProba p.2).toFiniteMeasure : FiniteMeasure ((ℝ × ℝ) × ℝ)) : Measure _) :=
    (densFM_continuous_integral H).comp (densFM_continuous_prod.comp
      ((densFM_continuous_prod.comp (continuous_fst.prodMk continuous_fst)).prodMk
        (densFM_continuous_dirac.comp continuous_snd)))
  refine hG.continuousAt.congr ?_
  have h0 : ((μ₀, ε₀) : FiniteMeasure ℝ × ℝ) ∈ Prod.snd ⁻¹' Set.Ioi (ε₀ / 2) := by
    simp only [Set.mem_preimage, Set.mem_Ioi]
    linarith
  filter_upwards [(isOpen_Ioi.preimage continuous_snd).mem_nhds h0] with p hp
  have hp' : ε₀ / 2 < p.2 := hp
  have hp0 : 0 < p.2 := by linarith
  rw [(smoothedNormSq_eq hρ (p.1 : Measure ℝ) hφ ⟨c, hc⟩ hp0).2.2]
  simp only [FiniteMeasure.toMeasure_prod,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [integral_prod _ (BoundedContinuousFunction.integrable _ _)]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  show ∫ e, H (q, e) ∂(Measure.dirac p.2) = _
  rw [integral_dirac]
  show φ q.1 * φ q.2 * kappaEps ρ (max p.2 (ε₀ / 2)) (q.1 - q.2) = _
  rw [max_eq_left hp'.le]

/-- Young's inequality: for a measure `u(x) dx` with `u ≥ 0` in `L²`, and `φ` bounded measurable,
`‖(φ u) ⋆ ρ_ε‖₂² ≤ ∫ φ² u²`. -/
theorem smoothedNormSq_withDensity_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {u : ℝ → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) (hu : MemLp u 2 volume) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hb : ∃ C, ∀ x, |φ x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    smoothedNormSq (volume.withDensity fun x => ENNReal.ofReal (u x)) φ ρ ε ≤
      ∫ x, φ x ^ 2 * u x ^ 2 := by
  obtain ⟨w, hwm, hw2, hconv, hint⟩ := mollif_withDensity_setup hu0 hu hφ hb
  have hY := mollif_lintegral_sq_le hρ hε hwm hw2
  have hfin : ∫⁻ x, ENNReal.ofReal (w x ^ 2) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hw2 (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  rw [mollif_smoothedNormSq_eq hconv]
  rw [hint, mollif_smoothed_eq_toReal hρ ε hwm, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun _ => sq_nonneg _) (hwm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono hfin.ne hY

/-- Approximate identity in `L²`: `‖(φ u) ⋆ ρ_ε‖₂² → ∫ φ² u²` as `ε → 0⁺`. -/
theorem tendsto_smoothedNormSq_withDensity {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {u : ℝ → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) (hu : MemLp u 2 volume) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hb : ∃ C, ∀ x, |φ x| ≤ C) :
    Tendsto (fun ε => smoothedNormSq (volume.withDensity fun x => ENNReal.ofReal (u x)) φ ρ ε)
      (𝓝[>] 0) (𝓝 (∫ x, φ x ^ 2 * u x ^ 2)) := by
  obtain ⟨w, hwm, hw2, hconv, hint⟩ := mollif_withDensity_setup hu0 hu hφ hb
  set A : ℝ → ℝ≥0∞ := fun ε => ∫⁻ y, ENNReal.ofReal ((∫ x, rhoEps ρ ε (y - x) * w x) ^ 2)
    with hA
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (w x ^ 2) with hB
  have hfin : B < ∞ := by
    rw [hB, ← ofReal_integral_eq_lintegral_ofReal hw2 (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hwl : LocallyIntegrable w volume :=
    ((memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).2 hw2).locallyIntegrable
      (by norm_num)
  have hlimA : Tendsto A (𝓝[>] 0) (𝓝 B) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · by_contra hcon
      rw [not_eventually] at hcon
      obtain ⟨ns, hns, hnb⟩ := exists_seq_forall_of_frequently hcon
      have hle : B ≤ liminf (fun n => A (ns n)) atTop := by
        calc B = ∫⁻ y, liminf (fun n => ENNReal.ofReal
              ((∫ x, rhoEps ρ (ns n) (y - x) * w x) ^ 2)) atTop := by
              refine lintegral_congr_ae ?_
              filter_upwards [mollif_ae_tendsto hρ hwl] with y hy
              have := ((ENNReal.continuous_ofReal.comp (continuous_pow 2)).tendsto _).comp
                (hy.comp hns)
              exact this.liminf_eq.symm
          _ ≤ liminf (fun n => A (ns n)) atTop :=
              lintegral_liminf_le' fun n => (ENNReal.measurable_ofReal.comp
                (mollif_conv_sq_measurable hρ (ns n) hwm).measurable).aemeasurable
      exact lt_irrefl _ (hb.trans_le (hle.trans
        (liminf_le_of_frequently_le' (Frequently.of_forall fun n => not_lt.1 (hnb n)))))
    · filter_upwards [eventually_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (mollif_lintegral_sq_le hρ hε hwm hw2).trans_lt hb
  have hreal := (ENNReal.tendsto_toReal hfin.ne).comp hlimA
  rw [hint, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
    (hwm.pow_const 2).aestronglyMeasurable]
  refine hreal.congr fun ε => ?_
  rw [Function.comp_apply, mollif_smoothedNormSq_eq hconv, mollif_smoothed_eq_toReal hρ ε hwm]

end QSSEPtoKPZ
