/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.Defs
public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import QSSEPtoKPZ.Uniqueness.Volterra
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.Uniqueness.Prop73Main

/-!
# Proposition 7.3: uniqueness for the weak mild equation

STATEMENT FILE (task T0″ of Stage 4, `docs/stage4-statements.md`); the proof is task K1, in
this file (`docs/stage4-design.md`, Section 1.2 (g), decision D5″: test functions
`ρ_δ(z - ·)` instead of an orthonormal basis, then `volterra_ae_eq_zero`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

set_option linter.unusedVariables false in
/-- **Proposition 7.3**, with (7.13). Let `ξ` be a white noise (distribution function `S`) for a
filtration `𝓖`, and let `Z¹, Z² ∈ ℋ_T` both satisfy the weak mild equation (7.13) for almost
every `t ∈ (0,T]` and every `f ∈ C_c^∞(ℝ)` (`IsWeakMild`). Then `Z¹ = Z²` almost everywhere on
`Ω × [0,T] × ℝ`. -/
theorem prop_7_3 {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}
    (hS : IsWhiteNoise 𝓖 S ν) {T : ℝ} (hT : 0 < T) {Z₁ Z₂ : ℝ → ℝ → Ω → ℝ}
    (h₁ : IsWeakMild T 𝓖 S Z₁ ν) (h₂ : IsWeakMild T 𝓖 S Z₂ ν) :
    ∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
      Z₁ p.2.1 p.2.2 p.1 = Z₂ p.2.1 p.2.2 p.1 := by
  exact prop73_main hS h₁.measurable h₂.measurable h₁.sq_integrable h₂.sq_integrable h₁.weak
    h₂.weak

end QSSEPtoKPZ
