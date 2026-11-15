/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.TiltedField.Constants
public import QSSEPtoKPZ.Martingales.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Definitions of Section 3: the tilted field

For a real number `n ≥ 1` (the constants `θ_n, c_n, λ_n, a_n` of (3.1) are in
`TiltedField/Constants.lean`), and a realization `ω` of the wave function `ψ`:

* `zN`: the tilted field `𝔷_n(t,x)`, (3.3); the position `y_n(t,x)` of (3.4) is
  `rescaledPosition n t x` of `Definitions.lean`;
* `tiltedMeasure`: the measure `𝒵_n(t)`, (3.5), and `pairZ`: `𝒵_n(t;φ)`;
* `WN`: the total mass `𝒲_n(t)`, (3.6);
* `varrhoN`: `ϱ_n(t)`, (3.8);
* `EN`: `ℰ_n(t;φ)`, (3.12);
* `IsC13`: `φ ∈ C_b^{1,3}([0,T] × ℝ)` with `‖φ‖_{1,3} ≤ C` (Section 3.2);
* `AN`: the operator `𝒜_n`, (3.13);
* `MN`: the process `M_n^φ`, (3.14), and `QN`: the right-hand side of (3.15);
* `filtN`: the filtration `𝓕ⁿ_t = 𝓕_{nt/2}`;
* `tiltedInclGen`: the operator `𝒬^θ`, (3.19);
* `pairZ2`: `𝒵_n^{⊗2}(t;f)`, and `bracketDensN2`: the density of the bracket of the martingale
  `N_n^f` of (3.22), computed from (3.22) and (3.11).

Processes are written `X t ω` (as `ψ` in `Definitions.lean`) or, for quantities that the
article writes as functions of `t` and of a test function, `X ω t φ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The tilted and rescaled field (3.3): `𝔷_n(t,x) = exp(θ_n x - n λ_n t / 2) P(n t / 2, x)`,
where `P = density ψ ω`. -/
def zN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) : ℝ :=
  Real.exp (thetaN n * x - n * lambdaN n / 2 * t) * density ψ ω (n * t / 2) x

/-- The random measure (3.5): `𝒵_n(t) = ∑_{x ∈ ℤ} 𝔷_n(t,x) δ_{y_n(t,x)}`, with
`y_n(t,x) = rescaledPosition n t x = n^{-1/2} (x - n^{3/4} t)` (3.4). -/
def tiltedMeasure (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) : Measure ℝ :=
  Measure.sum fun x : ℤ => ENNReal.ofReal (zN n ψ ω t x) • Measure.dirac (rescaledPosition n t x)

/-- `𝒵_n(t;φ) = ∑_{x ∈ ℤ} 𝔷_n(t,x) φ(y_n(t,x))` (after (3.5)). -/
def pairZ (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∑' x : ℤ, zN n ψ ω t x * φ (rescaledPosition n t x)

/-- The total mass (3.6): `𝒲_n(t) = 𝒵_n(t;1) = ∑_{x ∈ ℤ} 𝔷_n(t,x)`. -/
def WN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (ω : Ω) : ℝ :=
  pairZ n ψ ω t fun _ => 1

/-- `ϱ_n(t) = exp((n λ_n / 2 - n^{1/2} / 2 - 1/24) t)`, (3.8). -/
def varrhoN (n t : ℝ) : ℝ :=
  Real.exp ((n * lambdaN n / 2 - n ^ (1 / 2 : ℝ) / 2 - 1 / 24) * t)

/-- (3.12): `ℰ_n(t;φ) = n^{1/2} ∑_{x ∈ ℤ} 𝔷_n(t,x) 𝔷_n(t,x+1) φ(y_n(t,x)) φ(y_n(t,x+1))`.
The article writes `ℰ_n(t)` for `ℰ_n(t;1)`, which is `EN n ψ ω t (fun _ => 1)` here. -/
def EN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  n ^ (1 / 2 : ℝ) * ∑' x : ℤ, zN n ψ ω t x * zN n ψ ω t (x + 1) *
    φ (rescaledPosition n t x) * φ (rescaledPosition n t (x + 1))

/-- `φ ∈ C_b^{1,3}([0,T] × ℝ)`, with time derivative `φt`, and `‖φ‖_{1,3} ≤ C` (Section 3.2):
for `t ∈ [0, T]`, `φ t` is of class `C³` on `ℝ`; `φt t x` is the derivative of `t ↦ φ t x` on
`[0, T]` (one-sided at `0` and `T`); `φt` and the space derivatives `∂ₓᵏ φ` for `k ≤ 3`
(including `φ` itself, `k = 0`) are continuous on `[0, T] × ℝ`; and
`‖φ‖_∞ + ‖∂ₜφ‖_∞ + ‖∂ₓφ‖_∞ + ‖∂ₓ²φ‖_∞ + ‖∂ₓ³φ‖_∞ ≤ C`, the suprema being over `[0, T] × ℝ`.
The values of `φ` and `φt` for `t ∉ [0, T]` play no role. -/
structure IsC13 (T : ℝ) (φ φt : ℝ → ℝ → ℝ) (C : ℝ) : Prop where
  contDiff : ∀ t ∈ Set.Icc 0 T, ContDiff ℝ 3 (φ t)
  hasDerivWithinAt : ∀ x, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (φ · x) (φt t x) (Set.Icc 0 T) t
  continuousOn : ContinuousOn (Function.uncurry φt) (Set.Icc 0 T ×ˢ Set.univ) ∧
    ∀ k ≤ 3, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (φ p.1) p.2) (Set.Icc 0 T ×ˢ Set.univ)
  bound : ∃ c : Fin 5 → ℝ, ∑ i, c i ≤ C ∧ ∀ t ∈ Set.Icc 0 T, ∀ x,
    |φ t x| ≤ c 0 ∧ |φt t x| ≤ c 1 ∧ |iteratedDeriv 1 (φ t) x| ≤ c 2 ∧
    |iteratedDeriv 2 (φ t) x| ≤ c 3 ∧ |iteratedDeriv 3 (φ t) x| ≤ c 4

/-- The operator (3.13):
`𝒜_n φ(y) = (n/2) [e^{θ_n} φ(y + n^{-1/2}) + e^{-θ_n} φ(y - n^{-1/2}) - 2 c_n φ(y)] - n^{1/4} φ'(y)`. -/
def AN (n : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  n / 2 * (Real.exp (thetaN n) * φ (y + n ^ (-1 / 2 : ℝ)) +
    Real.exp (-thetaN n) * φ (y - n ^ (-1 / 2 : ℝ)) - 2 * cN n * φ y) -
    n ^ (1 / 4 : ℝ) * deriv φ y

/-- The process (3.14):
`M_n^φ(t) = 𝒵_n(t;φ_t) - φ_0(0) - ∫_0^t 𝒵_n(s; ∂ₛφ_s + 𝒜_n φ_s) ds`. -/
def MN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  pairZ n ψ ω t (φ t) - φ 0 0 -
    ∫ s in (0 : ℝ)..t, pairZ n ψ ω s (fun y => φt s y + AN n (φ s) y)

/-- The integrand of (3.15):
`∑_{x ∈ ℤ} 𝔷_n(s,x) 𝔷_n(s,x+1) [e^{θ_n/2} φ_s(y_n(s,x+1)) - e^{-θ_n/2} φ_s(y_n(s,x))]²`. -/
def QNdens (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (φ : ℝ → ℝ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  ∑' x : ℤ, zN n ψ ω s x * zN n ψ ω s (x + 1) *
    (Real.exp (thetaN n / 2) * φ s (rescaledPosition n s (x + 1)) -
      Real.exp (-thetaN n / 2) * φ s (rescaledPosition n s x)) ^ 2

/-- The right-hand side of (3.15): `n ∫_0^t QNdens(s) ds`. -/
def QN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (φ : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  n * ∫ s in (0 : ℝ)..t, QNdens n ψ φ s ω

/-- The time-changed filtration `𝓕ⁿ_t = 𝓕_{nt/2}` of Section 3.1. -/
def filtN (n : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ :=
  timeChange (n / 2).toNNReal 𝓕

/-- The operator `𝒬^θ` of (3.19), acting on `f : ℤ² → ℝ`:
`𝒬^θ f(x₁,x₂) = ∑_{σ = ±1} e^{σθ} [f(x₁+σ,x₂) + f(x₁,x₂+σ) - 2 f(x₁,x₂)]
  + 𝟙_{x₂ = x₁+1} [e^θ (f(x₂,x₂) - f(x₁,x₂)) + e^{-θ} (f(x₁,x₁) - f(x₁,x₂))]
  + 𝟙_{x₂ = x₁-1} [e^{-θ} (f(x₂,x₂) - f(x₁,x₂)) + e^θ (f(x₁,x₁) - f(x₁,x₂))]`. -/
def tiltedInclGen (θ : ℝ) (f : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ :=
  Real.exp θ * (f (x₁ + 1) x₂ + f x₁ (x₂ + 1) - 2 * f x₁ x₂) +
  Real.exp (-θ) * (f (x₁ - 1) x₂ + f x₁ (x₂ - 1) - 2 * f x₁ x₂) +
  (if x₂ = x₁ + 1 then
    Real.exp θ * (f x₂ x₂ - f x₁ x₂) + Real.exp (-θ) * (f x₁ x₁ - f x₁ x₂) else 0) +
  (if x₂ = x₁ - 1 then
    Real.exp (-θ) * (f x₂ x₂ - f x₁ x₂) + Real.exp θ * (f x₁ x₁ - f x₁ x₂) else 0)

/-- `𝒵_n^{⊗2}(t;f) = ∑_{x₁,x₂ ∈ ℤ} 𝔷_n(t,x₁) 𝔷_n(t,x₂) f(x₁,x₂)` (Section 3.3). -/
def pairZ2 (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (f : ℤ → ℤ → ℝ) : ℝ :=
  ∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * f x₁ x₂

/-- The density of the bracket of the martingale `N_n^f` of (3.22), obtained from (3.22) and
(3.11):
`4 n ∑_{x ∈ ℤ} 𝔷_n(s,x) 𝔷_n(s,x+1) [∑_{x' ∈ ℤ} 𝔷_n(s,x') (e^{θ_n/2} f_s(x+1,x') - e^{-θ_n/2} f_s(x,x'))]²`. -/
def bracketDensN2 (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (f : ℝ → ℤ → ℤ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  4 * n * ∑' x : ℤ, zN n ψ ω s x * zN n ψ ω s (x + 1) *
    (∑' x' : ℤ, zN n ψ ω s x' *
      (Real.exp (thetaN n / 2) * f s (x + 1) x' - Real.exp (-thetaN n / 2) * f s x x')) ^ 2

end QSSEPtoKPZ
