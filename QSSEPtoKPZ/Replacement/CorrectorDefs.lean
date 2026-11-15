/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.Replacement.Poisson

/-!
# Definitions of Section 6: smoothing, the corrector `𝖥_n` and `𝖡_n`

* `rhoEps ρ ε`: `ρ_ε(x) = ρ(x/ε)/ε`; `kappaEps ρ ε`: `κ_ε(x) = κ(x/ε)/ε` (beginning of
  Section 6; `κ = ρ ⋆ ρ` is `kappa ρ` of `Replacement/Mollifier.lean`).
* `smoothedNormSq ν φ ρ ε`: `‖(φν) ⋆ ρ_ε‖₂²` for a measure `ν` on `ℝ`, where
  `(φν) ⋆ ρ_ε (y) = ∫ ρ_ε(y - x) φ(x) ν(dx)` (convolution as in the Notation paragraph of
  Section 1).
* `FN`: the corrector `𝖥_n(t)`, (6.9); `BN`: `𝖡_n(t;φ)`, (6.10).
-/

@[expose] public section

open MeasureTheory
open scoped lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*}

/-- `ρ_ε(x) = ρ(x/ε)/ε` (Section 6). -/
def rhoEps (ρ : ℝ → ℝ) (ε x : ℝ) : ℝ := ρ (x / ε) / ε

/-- `κ_ε(x) = κ(x/ε)/ε` with `κ = ρ ⋆ ρ` (Section 6); the article notes that `κ_ε = ρ_ε ⋆ ρ_ε`
(statement `kappaEps_eq_conv`). -/
def kappaEps (ρ : ℝ → ℝ) (ε x : ℝ) : ℝ := kappa ρ (x / ε) / ε

/-- `‖(φν) ⋆ ρ_ε‖₂² = ∫_ℝ (∫_ℝ φ(x) ρ_ε(y - x) ν(dx))² dy`, for a measure `ν` on `ℝ`. -/
def smoothedNormSq (ν : Measure ℝ) (φ : ℝ → ℝ) (ρ : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ y, (∫ x, φ x * rhoEps ρ ε (y - x) ∂ν) ^ 2

/-- The corrector (6.9):
`𝖥_n(t) = 2/(c_n n^{1/2}) ∑_{x₁,x₂ ∈ ℤ} 𝔷_n(t,x₁) 𝔷_n(t,x₂) g_m(x₂ - x₁) φ_t(y_n(t,x₁)) φ_t(y_n(t,x₂))`. -/
def FN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ρ : ℝ → ℝ) (m : ℕ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) :
    ℝ :=
  2 / (cN n * n ^ (1 / 2 : ℝ)) * pairZ2 n ψ ω t
    (fun x₁ x₂ => gM ρ m (x₂ - x₁) * φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂))

/-- (6.10): `𝖡_n(t;φ) = n^{1/2} ∑_{x₁,x₂ ∈ ℤ} 𝔷_n(t,x₁) 𝔷_n(t,x₂) k_m(x₂ - x₁) φ(y_n(t,x₁)) φ(y_n(t,x₂))`. -/
def BN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ρ : ℝ → ℝ) (m : ℕ) (t : ℝ) (φ : ℝ → ℝ) (ω : Ω) : ℝ :=
  n ^ (1 / 2 : ℝ) * pairZ2 n ψ ω t
    (fun x₁ x₂ => kM ρ m (x₂ - x₁) * φ (rescaledPosition n t x₁) * φ (rescaledPosition n t x₂))

end QSSEPtoKPZ
