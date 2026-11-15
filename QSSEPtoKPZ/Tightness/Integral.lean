/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs

/-!
# The notation `𝖹_n(t;φ) = ∫ φ d𝖹_n(t)` (Section 5)

Statement: Stage 3, task T0' (`docs/stage3-design.md`, Section 3.1); proof: task Q1.

The article writes `μ(φ) = ∫ φ dμ` for a measure `μ` and uses `𝖹_n(t;φ)` both for the integral of
`φ` against the measure `𝖹_n(t)` of (3.5) (`tiltedMeasure`) and for the series
`∑ₓ 𝔷_n(t,x) φ(y_n(t,x))` (`pairZ`). The statement below says that the two agree for bounded
measurable `φ`, as soon as the total mass `∑ₓ 𝔷_n(t,x)` is finite.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Notation of Section 5**, `𝖹_n(t;φ) = ∫ φ d𝖹_n(t)`: for a realization `ω` and a time `t`
at which `∑ₓ 𝔷_n(t,x)` converges, and for `φ` measurable and bounded, the measure `𝖹_n(t)` of
(3.5) is finite, `φ` is `𝖹_n(t)`-integrable, and
`∫ φ d𝖹_n(t) = ∑ₓ 𝔷_n(t,x) φ(y_n(t,x)) = 𝖹_n(t;φ)`. -/
theorem integral_tiltedMeasure {n t : ℝ} {ω : Ω} (hs : Summable (zN n ψ ω t))
    {φ : ℝ → ℝ} (hφm : Measurable φ) {c : ℝ} (hφ : ∀ y, |φ y| ≤ c) :
    IsFiniteMeasure (tiltedMeasure n ψ ω t) ∧
    Integrable φ (tiltedMeasure n ψ ω t) ∧
    ∫ y, φ y ∂(tiltedMeasure n ψ ω t) = pairZ n ψ ω t φ := by
  have hz : ∀ x, 0 ≤ zN n ψ ω t x := fun x =>
    mul_nonneg (Real.exp_pos _).le (by unfold density; positivity)
  have hfin : IsFiniteMeasure (tiltedMeasure n ψ ω t) := by
    constructor
    rw [tiltedMeasure, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hz hs]
    exact ENNReal.ofReal_lt_top
  have hint : Integrable φ (tiltedMeasure n ψ ω t) :=
    Integrable.of_bound hφm.aestronglyMeasurable c
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hφ y)
  refine ⟨hfin, hint, ?_⟩
  rw [tiltedMeasure] at hint ⊢
  rw [integral_sum_measure hint, pairZ]
  congr 1
  funext x
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hz x), smul_eq_mul]

end QSSEPtoKPZ
