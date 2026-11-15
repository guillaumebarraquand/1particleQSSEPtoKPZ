/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.StochFubini

/-!
# The solution of the stochastic heat equation in Section 7.3: (7.15) and (7.13)

STATEMENT FILE (task T0″ of Stage 4, `docs/stage4-statements.md`). The two statements are about
the field `Z` **given** in the statement of Theorem 1.2 (a solution of (1.13), the frozen
`IsMildSolution`); the existence theorem of Chen–Dalang used by the article for (7.14) is not
used (decision D4″). Their proofs are tasks K2 (`heatMild_integral_sq`, file
`SecondMoment.lean`) and K3 (`heatMild_isWeakMild`, file `StochFubini.lean`), whose statements
are the same; here they are only quoted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- **Equation (7.15)**, in series form (decision D9″). For a solution `Z` of (1.13) and `t > 0`,
`Z(t,x)` is square integrable and
`𝔼[Z(t,x)²] = ∑_{k ≥ 1} K^{⋆k}(t,x)`, `K^{⋆k}(t,x) = 2^{-k} t^{k/2-1} Γ(k/2)⁻¹ g_{t/2}(x)`
(the series converges; `K^{⋆k}` is the `k`-th space-time convolution power of
`K(t,x) = g_t(x)²`, and the sum of the series is the right side of (7.15)). -/
theorem IsMildSolution.integral_sq (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) {t x : ℝ} (ht : 0 < t) :
    MemLp (Z t x) 2 ν ∧ HasSum (fun k : ℕ => (2 : ℝ) ^ (-((k : ℝ) + 1)) *
        t ^ (((k : ℝ) + 1) / 2 - 1) / Real.Gamma (((k : ℝ) + 1) / 2) * heatKernel (t / 2) x)
      (∫ ω, Z t x ω ^ 2 ∂ν) :=
  heatMild_integral_sq hS hZ ht

/-- **After (7.15)**: "`Z⋆ ∈ ℋ_T`" and "`Z⋆` satisfies (7.13) for all `t ∈ (0,T]`" (stochastic
Fubini), for the given solution `Z` of (1.13): there is a jointly measurable version `Z'` of `Z`
(almost surely `Z' = Z` on `(0, ∞) × ℝ`) such that `IsWeakMild T 𝓖 S Z' ν` (`Z' ∈ ℋ_T` and
(7.13) for almost every `t`), and (7.13) holds for **every** `t ∈ (0,T]` and `f ∈ C_c^∞(ℝ)`. -/
theorem IsMildSolution.isWeakMild (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) {T : ℝ} (hT : 0 < T) :
    ∃ Z' : ℝ → ℝ → Ω → ℝ, (∀ᵐ ω ∂ν, ∀ t x, 0 < t → Z' t x ω = Z t x ω) ∧
      IsWeakMild T 𝓖 S Z' ν ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        IsWalshIntegral 𝓖 S ν
          (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z' s y ω else 0)
          (fun ω => (∫ x, Z' t x ω * f x) - ∫ x, heatKernel t x * f x) :=
  heatMild_isWeakMild hS hZ hT

end QSSEPtoKPZ
