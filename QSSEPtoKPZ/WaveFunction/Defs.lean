/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Definitions of Section 2: the discrete Laplacian and the generator `𝒬`

* `lap f x = f(x+1) + f(x-1) - 2 f(x)`: the Laplacian `Δ = Δ_∞` on `ℤ` (Section 2.2, `L = ∞`).
* `inclGen f`: the generator `𝒬` of the two-particle symmetric inclusion process, (2.6).
-/

@[expose] public section

noncomputable section

namespace QSSEPtoKPZ

/-- The discrete Laplacian on `ℤ`: `Δ f(x) = f(x+1) + f(x-1) - 2 f(x)` (`Δ_L` of Section 2.2 for
`L = ∞`). -/
def lap (f : ℤ → ℝ) (x : ℤ) : ℝ := f (x + 1) + f (x - 1) - 2 * f x

/-- The generator `𝒬` of (2.6), acting on `f : ℤ² → ℝ`:
`𝒬 f(x₁,x₂) = (Δ₁ + Δ₂) f(x₁,x₂) + 𝟙_{|x₁ - x₂| = 1} [f(x₁,x₁) + f(x₂,x₂) - 2 f(x₁,x₂)]`, where
`Δᵢ` is the Laplacian in the variable `xᵢ`. -/
def inclGen (f : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ :=
  lap (fun y => f y x₂) x₁ + lap (fun y => f x₁ y) x₂ +
    if |x₁ - x₂| = 1 then f x₁ x₁ + f x₂ x₂ - 2 * f x₁ x₂ else 0

end QSSEPtoKPZ
