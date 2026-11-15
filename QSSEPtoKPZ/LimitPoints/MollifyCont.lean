/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.MollifyAux
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Weak continuity of products of finite measures and of mollified measures (task G3)

* `densFM_continuous_prod`: `(μ, ν) ↦ μ ⊗ ν` is continuous for the topology of weak convergence
  of finite measures (from Mathlib's `ProbabilityMeasure.continuous_prod`, by normalizing:
  `μ ⊗ ν = μ(1) ν(1) · (μ/μ(1)) ⊗ (ν/ν(1))`);
* `densFM_continuous_dirac`: `x ↦ δ_x` is continuous;
* `densFM_continuous_integral`: `ν ↦ ∫ H dν` is continuous for `H` bounded continuous;
* `densFM_continuous_conv`: `(μ, x) ↦ (μ ⋆ ρ_ε)(x) = ∫ ρ_ε(x - y) μ(dy)` is jointly continuous on
  `ℳ₊ × ℝ` (it is `∫ H d(μ ⊗ δ_x)` with `H(y, x) = ρ_ε(x - y)`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

/-- `ν ↦ ∫ H dν` is continuous on finite measures, for `H` bounded continuous. -/
theorem densFM_continuous_integral {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (H : α →ᵇ ℝ) :
    Continuous fun ν : FiniteMeasure α => ∫ x, H x ∂(ν : Measure α) :=
  continuous_iff_continuousAt.2 fun _ =>
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id H

/-- `∫ H d(μ ⊗ ν) = μ(1) ν(1) ∫ H d(μ̂ ⊗ ν̂)` with `μ̂, ν̂` the normalized measures. -/
private lemma densFM_integral_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Nonempty α] [Nonempty β] (H : α × β → ℝ) (μ : FiniteMeasure α) (ν : FiniteMeasure β) :
    ∫ x, H x ∂((μ.prod ν : FiniteMeasure (α × β)) : Measure (α × β)) =
      (μ.mass : ℝ) * ν.mass *
        ∫ x, H x ∂((μ.normalize.prod ν.normalize : ProbabilityMeasure (α × β)) : Measure _) := by
  have hμ : (μ : Measure α) = μ.mass • (μ.normalize : Measure α) := by
    conv_lhs => rw [μ.self_eq_mass_smul_normalize]
    rw [FiniteMeasure.toMeasure_smul, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  have hν : (ν : Measure β) = ν.mass • (ν.normalize : Measure β) := by
    conv_lhs => rw [ν.self_eq_mass_smul_normalize]
    rw [FiniteMeasure.toMeasure_smul, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [FiniteMeasure.toMeasure_prod, ProbabilityMeasure.toMeasure_prod, hμ, hν,
    Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul,
    mul_assoc]

/-- **Weak continuity of products**: `(μ, ν) ↦ μ ⊗ ν` is continuous on `ℳ₊(α) × ℳ₊(β)`. -/
theorem densFM_continuous_prod {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [SecondCountableTopology α] [TopologicalSpace.PseudoMetrizableSpace α]
    [OpensMeasurableSpace α] [Nonempty α] [TopologicalSpace β] [MeasurableSpace β]
    [SecondCountableTopology β] [TopologicalSpace.PseudoMetrizableSpace β]
    [OpensMeasurableSpace β] [Nonempty β] :
    Continuous fun p : FiniteMeasure α × FiniteMeasure β => p.1.prod p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [ContinuousAt, FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro H
  simp_rw [densFM_integral_prod_eq (fun x => H x)]
  have hm1 : Tendsto (fun p : FiniteMeasure α × FiniteMeasure β => (p.1.mass : ℝ)) (𝓝 p₀)
      (𝓝 (p₀.1.mass : ℝ)) :=
    (NNReal.continuous_coe.comp (FiniteMeasure.continuous_mass.comp continuous_fst)).tendsto _
  have hm2 : Tendsto (fun p : FiniteMeasure α × FiniteMeasure β => (p.2.mass : ℝ)) (𝓝 p₀)
      (𝓝 (p₀.2.mass : ℝ)) :=
    (NNReal.continuous_coe.comp (FiniteMeasure.continuous_mass.comp continuous_snd)).tendsto _
  by_cases h : p₀.1 ≠ 0 ∧ p₀.2 ≠ 0
  · refine (hm1.mul hm2).mul ?_
    have h1 := FiniteMeasure.tendsto_normalize_of_tendsto
      (continuous_fst.tendsto p₀ : Tendsto (fun p : FiniteMeasure α × FiniteMeasure β => p.1) _ _)
      h.1
    have h2 := FiniteMeasure.tendsto_normalize_of_tendsto
      (continuous_snd.tendsto p₀ : Tendsto (fun p : FiniteMeasure α × FiniteMeasure β => p.2) _ _)
      h.2
    have h3 := (ProbabilityMeasure.continuous_prod.tendsto
      (p₀.1.normalize, p₀.2.normalize)).comp (h1.prodMk_nhds h2)
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h3 H
  · have h0 : (p₀.1.mass : ℝ) * p₀.2.mass = 0 := by
      rcases not_and_or.1 h with h' | h'
      · rw [not_not.1 h', (FiniteMeasure.mass_zero_iff _).2 rfl]; simp
      · rw [not_not.1 h', (FiniteMeasure.mass_zero_iff _).2 rfl]; simp
    rw [h0, zero_mul]
    have hb : Tendsto (fun p : FiniteMeasure α × FiniteMeasure β =>
        (p.1.mass : ℝ) * p.2.mass * ‖H‖) (𝓝 p₀) (𝓝 0) := by
      have := (hm1.mul hm2).mul_const ‖H‖
      rwa [h0, zero_mul] at this
    refine squeeze_zero_norm (fun p => ?_) hb
    rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    gcongr
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun x => H.norm_coe_le_norm x)).trans ?_
    simp

/-- `x ↦ δ_x` is continuous into `ℳ₊`. -/
theorem densFM_continuous_dirac {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] :
    Continuous fun x : α => (diracProba x).toFiniteMeasure :=
  ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_diracProba

/-- `ρ_ε(x - ·)` as a bounded continuous function of `(y, x)`. -/
private def densConvKernel (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) : ℝ × ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun q => rhoEps ρ ε (q.2 - q.1))
    ((mollif_rhoEps_continuous hρ ε).comp (continuous_snd.sub continuous_fst)) (mollifSup ρ / ε)
    fun q => by rw [Real.norm_eq_abs]; exact mollif_abs_rhoEps_le hρ hε _

/-- **Joint continuity of mollified measures**: `(μ, x) ↦ ∫ ρ_ε(x - y) μ(dy)` is continuous on
`ℳ₊ × ℝ`, for `ε > 0`. -/
theorem densFM_continuous_conv {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun p : FiniteMeasure ℝ × ℝ => ∫ y, rhoEps ρ ε (p.2 - y) ∂(p.1 : Measure ℝ) := by
  have hc := (densFM_continuous_integral (densConvKernel ρ hρ ε hε)).comp
    (densFM_continuous_prod.comp (continuous_fst.prodMk (densFM_continuous_dirac.comp
      continuous_snd)))
  refine hc.congr fun p => ?_
  simp only [Function.comp_apply, FiniteMeasure.toMeasure_prod,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [integral_prod _ (BoundedContinuousFunction.integrable _ _)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show ∫ x, densConvKernel ρ hρ ε hε (y, x) ∂(Measure.dirac p.2) = _
  rw [integral_dirac]
  rfl

end QSSEPtoKPZ
