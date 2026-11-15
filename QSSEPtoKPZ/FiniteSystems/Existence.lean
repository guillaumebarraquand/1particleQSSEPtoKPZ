/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.BrownianFamily
public import QSSEPtoKPZ.FiniteSystems.Statements
public import QSSEPtoKPZ.Uniqueness.Theorem12

/-!
# Existence of the wave function (companion E1) and nonnegativity of the SHE (companion P)
(task E1b)

STATEMENT FILE (task T0‴ of Stage 5, `docs/stage5-statements.md`); the proof of
`exists_isWaveFunction_lib` is task E1b, in this file (`docs/stage5-design.md`, Section 1.2 (h)):
`exists_isBrownianFamily`, `IsBrownianFamily.nullAug` and `prop_2_1_existence`.

`exists_isWaveFunction_lib` and `IsMildSolution.nonneg_lib` are the companion statements **E1**
(`exists_isWaveFunction`) and **P** (`IsMildSolution.nonneg`) of `Companions.lean`, word for word
(checked with `pp.all` and by the kernel). P is proved here from Stage 4's
`IsMildSolution.nonneg_of_isWaveFunction` and E1 with `L = ∞` (a probability space in `Type`,
hence the universe instance `.{0}`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **E1** (existence of the wave function; Proposition 2.1 when `L = ∞`, Section 1.3 when
`L < ∞`), library copy of `exists_isWaveFunction`. For every `L ∈ ℕ ∪ {∞}`, there are a
probability space, a filtration, a family of independent Brownian motions `B` indexed by
`ℤ × {0, 1}`, and a process `ψ` which is the wave function of the one-particle QSSEP on `Λ_L`
driven by `B`. -/
theorem exists_isWaveFunction_lib (L : ℕ∞) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)),
      IsProbabilityMeasure μ ∧ IsBrownianFamily 𝓕 B μ ∧ IsWaveFunction L 𝓕 B ψ μ := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, hμ, hB⟩ := exists_isBrownianFamily
  obtain ⟨ψ, hψ⟩ := prop_2_1_existence hB L
  exact ⟨Ω, mΩ, μ, nullAug μ 𝓕, B, ψ, hμ, hB.nullAug, hψ⟩

/-- **P** (nonnegativity of the solution of the stochastic heat equation; Section 1.4 of the
article), library copy of `IsMildSolution.nonneg`. Almost surely, `Z(t,x) ≥ 0` for all `t > 0`
and `x ∈ ℝ`. Proved from the limit (Stage 4, `IsMildSolution.nonneg_of_isWaveFunction`) and E1
for `L = ∞`. -/
theorem IsMildSolution.nonneg_lib {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → 0 ≤ Z t x ω :=
  IsMildSolution.nonneg_of_isWaveFunction.{0} (exists_isWaveFunction_lib ⊤) hS hZ

end QSSEPtoKPZ
