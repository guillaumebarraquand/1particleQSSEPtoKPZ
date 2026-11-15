/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

/-!
# Definitions for the weak mild equation (Sections 7.2 and 7.3 of the article)

STATEMENT FILE (task T0″ of Stage 4): these definitions are part of the statements of Section 7
submitted to the author (`docs/stage4-statements.md`). They are complete (no `sorry`).

* `heatConv r f y = (g_r ⋆ f)(y)`, with `g` the heat kernel of (1.13).
* `IsWeakMild T 𝓖 S Z ν`: `Z ∈ ℋ_T` (here: jointly measurable and square integrable on
  `Ω × [0,T] × ℝ`, decision D8″) and `Z` satisfies the weak mild equation (7.13) for almost every
  `t ∈ (0,T]` and every `f ∈ C_c^∞(ℝ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `(g_r ⋆ f)(y) = ∫ g_r(y - x) f(x) dx`, where `g_r` is the heat kernel (`heatKernel`). In
(7.8) and (7.13) it appears with `r = t - s`. -/
def heatConv (r : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x, heatKernel r (y - x) * f x

/-- `IsWeakMild T 𝓖 S Z ν`: the random field `Z(t,x)` belongs to `ℋ_T` and solves the weak form
(7.13) of the mild equation, driven by the white noise with distribution function `S`:

* `Z` is jointly measurable on `Ω × ℝ × ℝ` (predictability is not required, decision D8″);
* `𝔼 ∫_0^T ∫_ℝ Z(t,x)² dx dt < ∞`;
* for almost every `t ∈ (0,T]`, for every `f ∈ C_c^∞(ℝ)`, almost surely,
  `∫ Z(t,x) f(x) dx = ∫ g_t(x) f(x) dx + ∫_0^t ∫_ℝ (g_{t-s} ⋆ f)(y) Z(s,y) ξ(ds dy)`,
  the stochastic integral being the frozen `IsWalshIntegral` (which asserts that it exists).

The negligible set of times does not depend on `f`. -/
structure IsWeakMild (T : ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (Z : ℝ → ℝ → Ω → ℝ)
    (ν : Measure Ω) : Prop where
  /-- `(ω, t, x) ↦ Z(t,x)(ω)` is measurable. -/
  measurable : Measurable (uncurryField Z)
  /-- `𝔼 ∫_0^T ∫_ℝ Z(t,x)² dx dt < ∞`. -/
  sq_integrable : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂ν < ⊤
  /-- The weak mild equation (7.13), for almost every `t ∈ (0,T]` and all `f ∈ C_c^∞(ℝ)`. -/
  weak : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ f : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω else 0)
      (fun ω => (∫ x, Z t x ω * f x) - ∫ x, heatKernel t x * f x)

end QSSEPtoKPZ
