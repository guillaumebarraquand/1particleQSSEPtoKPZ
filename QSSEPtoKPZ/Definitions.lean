/-
Formal statement of the main theorem of
  G. Barraquand, "Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation" (2026).
Lean 4 / Mathlib formalization written by Claude (Anthropic) at the request of the author,
November 2026. See README.md.
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Filtration

/-!
# The objects appearing in the main theorem of the article

This file contains the definitions needed to state Theorem 1.2 of

  G. Barraquand, *Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation* (2026).

Equation numbers refer to that article. The statement itself is in
`QSSEPtoKPZ/MainTheorem.lean`, and `QSSEPtoKPZ/Checks.lean` contains proved lemmas which test
the definitions below.

## Conventions

* Stochastic processes are functions of a real time variable, `X : ℝ → Ω → E`, but only their
  values at times `t ≥ 0` matter: all the conditions imposed below quantify over `t : ℝ≥0`.
  Filtrations are indexed by `ℝ≥0`.
* Mathlib does not contain stochastic integration yet. The two stochastic integrals that we need
  are therefore defined here, in an elementary way:
  * `itoSum`: Itô integrals of *continuous* adapted processes against Brownian motions are
    limits in probability of left-point Riemann sums;
  * `IsWalshIntegral`: the Itô-Walsh integral against a space-time white noise is the closure
    in `L²` of the integral of elementary predictable fields.

## Contents

* `IsBrownianFamily`: a family of independent standard Brownian motions with respect to a
  filtration.
* `IsWaveFunction`: the wave function `ψ` of the one-particle QSSEP on `Λ_L`, solution of the
  stochastic differential equation (1.7) (or (2.1) when `L = ∞`).
* `rescaledMeasure`: the measure `𝒵ₙ(t)` of (1.15).
* `IsWhiteNoise`, `IsWalshIntegral`: space-time white noise and its stochastic integral.
* `IsMildSolution`: the solution of the stochastic heat equation with initial condition `δ₀`,
  in the mild form (1.13).
* `sheMeasure`: the measure `𝒵(t)` of Theorem 1.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Brownian motions -/

/-- `IsBrownianFamily 𝓕 B μ` means that `(B i)` is a family of independent standard real
Brownian motions with respect to the filtration `𝓕`, under the probability measure `μ`:
the processes `B i` are adapted, continuous, start from `0`, and for all `s ≤ t` the increments
`B i t - B i s`, `i : ι`, are independent centered Gaussian random variables with variance
`t - s`, which are (jointly) independent of `𝓕 s`. -/
structure IsBrownianFamily {ι : Type*} (𝓕 : Filtration ℝ≥0 mΩ) (B : ι → ℝ → Ω → ℝ)
    (μ : Measure Ω) : Prop where
  /-- `B i` is adapted to `𝓕`. -/
  adapted : ∀ (i : ι) (t : ℝ≥0), Measurable[𝓕 t] (B i t)
  /-- Almost surely, `t ↦ B i t` is continuous on `[0, ∞)`. -/
  continuous : ∀ i : ι, ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => B i t ω
  /-- `B i` starts from `0`. -/
  zero : ∀ i : ι, ∀ᵐ ω ∂μ, B i 0 ω = 0
  /-- The increment `B i t - B i s` has the distribution `N(0, t - s)`. -/
  gaussian : ∀ (i : ι) (s t : ℝ≥0), s ≤ t →
    HasLaw (fun ω => B i t ω - B i s ω) (gaussianReal 0 (t - s)) μ
  /-- The increments between the times `s` and `t` of the processes `B i` are independent. -/
  indep : ∀ s t : ℝ≥0, s ≤ t → iIndepFun (fun (i : ι) (ω : Ω) => B i t ω - B i s ω) μ
  /-- The increments between the times `s` and `t` are independent of the past `𝓕 s`. -/
  indep_past : ∀ s t : ℝ≥0, s ≤ t →
    Indep (⨆ i : ι, MeasurableSpace.comap (fun ω => B i t ω - B i s ω) inferInstance) (𝓕 s) μ

/-- The standard complex Brownian motions `W⁽ˣ⁾ = (B₁⁽ˣ⁾ + i B₂⁽ˣ⁾) / √2` attached to the bonds
`(x, x + 1)` of `ℤ` (Section 1.3 of the article), built from a family `B` of real Brownian
motions indexed by `ℤ × {0, 1}`. -/
def complexBM (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ) (t : ℝ) (ω : Ω) : ℂ :=
  ((B (x, 0) t ω : ℂ) + Complex.I * (B (x, 1) t ω : ℂ)) / (Real.sqrt 2 : ℂ)

/-- The left-point Riemann sum `∑_{k < m} f(t_k) (W(t_{k+1}) - W(t_k))`, with `t_k = k t / m`,
which approximates the Itô integral `∫₀ᵗ f_s dW_s`.

If `W` is a (complex) Brownian motion with respect to a filtration and `f` is a continuous
adapted process, these sums converge in probability to the Itô integral as `m → ∞`
(see e.g. Revuz-Yor, *Continuous martingales and Brownian motion*, Proposition IV.2.13, or
Protter, *Stochastic integration and differential equations*, Theorem II.21). Hence, for a
continuous adapted process `f`, a random variable is the Itô integral `∫₀ᵗ f_s dW_s` if and only
if it is the limit in probability of `itoSum f W t m` as `m → ∞`. -/
def itoSum (f W : ℝ → Ω → ℂ) (t : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  ∑ k ∈ Finset.range m,
    f ((k : ℝ) * t / m) ω * (W (((k : ℝ) + 1) * t / m) ω - W ((k : ℝ) * t / m) ω)

/-! ### The one-particle QSSEP -/

/-- The lattice `Λ_L = {-L, ..., L}`, for `L ∈ ℕ ∪ {∞}`, with `Λ_∞ = ℤ`. -/
def box (L : ℕ∞) : Set ℤ := {x | (x.natAbs : ℕ∞) ≤ L}

/-- The number `D(x,x)` of neighbours of `x` in `Λ_L` (it equals `2 - 𝟙_{|x| = L}` for
`x ∈ Λ_L` when `L ≥ 1`). -/
def degree (L : ℕ∞) (x : ℤ) : ℕ :=
  (box L).indicator 1 (x + 1) + (box L).indicator 1 (x - 1)

/-- `IsWaveFunction L 𝓕 B ψ μ` means that `ψ` is the wave function of the one-particle QSSEP on
`Λ_L`, started from a particle at the origin and driven by the complex Brownian motions
`W⁽ˣ⁾ = complexBM B x`: it is the continuous adapted `ℓ²(ℤ)`-valued process, vanishing outside
`Λ_L`, such that for all `x ∈ Λ_L` and `t ≥ 0`,

  `ψ_t(x) = 𝟙_{x=0} + i ∫₀ᵗ ψ_s(x+1) dW_s⁽ˣ⁾ + i ∫₀ᵗ ψ_s(x-1) dW̄_s⁽ˣ⁻¹⁾ - ½ D(x,x) ∫₀ᵗ ψ_s(x) ds`.

This is equation (1.7) of the article in integral form (equation (2.1) when `L = ∞`), where the
terms involving sites outside `Λ_L` disappear because `ψ` vanishes there. Such a process is
unique up to indistinguishability: when `L < ∞`, it is `ψ_t = U_t e₀`, where `U` is the unitary
process of Definition 1.1, and when `L = ∞` it is the process of Proposition 2.1.

The Itô integrals are expressed as limits in probability of the Riemann sums `itoSum`, which is
legitimate since `ψ` is continuous and adapted. -/
structure IsWaveFunction (L : ℕ∞) (𝓕 : Filtration ℝ≥0 mΩ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ)
    (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop where
  /-- `ψ` is adapted to `𝓕`. -/
  adapted : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓕 t] fun ω => ψ t ω x
  /-- Almost surely, `t ↦ ψ_t` is continuous from `[0, ∞)` to `ℓ²(ℤ)`. -/
  continuous : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => ψ t ω
  /-- `ψ` vanishes outside `Λ_L`. -/
  support : ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0
  /-- The stochastic differential equation (1.7), in integral form. -/
  sde : ∀ (t : ℝ≥0) (x : ℤ), x ∈ box L →
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        Complex.I * itoSum (fun s ω => ψ s ω (x + 1)) (complexBM B x) t m ω +
        Complex.I * itoSum (fun s ω => ψ s ω (x - 1))
          (fun s ω => conj (complexBM B (x - 1) s ω)) t m ω)
      atTop
      (fun ω => ψ t ω x - (if x = 0 then 1 else 0) +
        (degree L x : ℂ) / 2 * ∫ s in (0 : ℝ)..t, ψ s ω x)

/-- The random probability distribution `P(t,x) = |ψ_t(x)|²` of (1.8), for a given realization
`ω` of the noise. -/
def density (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) : ℝ := ‖ψ t ω x‖ ^ 2

/-! ### The rescaled field -/

/-- The position, in the window of observation, of the lattice site `y` at the macroscopic time
`t`: the unique `x ∈ ℝ` such that `n^{3/4} t + n^{1/2} x = y`. As `y` ranges over `Λ_L`, this
describes the set `𝕃ₙ(t)` of Section 1.4. -/
def rescaledPosition (n t : ℝ) (y : ℤ) : ℝ := (y - n ^ (3 / 4 : ℝ) * t) / n ^ (1 / 2 : ℝ)

/-- The rescaled field (1.14),

  `Zₙ(t,x) = n^{1/2} exp(n^{1/2} t / 2 + n^{1/4} x - t / 24) P(n t / 2, n^{3/4} t + n^{1/2} x)`,

evaluated at the point `x = rescaledPosition n t y` of `𝕃ₙ(t)`. -/
def rescaledField (n : ℝ) (P : ℝ → ℤ → ℝ) (t : ℝ) (y : ℤ) : ℝ :=
  n ^ (1 / 2 : ℝ) *
    Real.exp (n ^ (1 / 2 : ℝ) * t / 2 + n ^ (1 / 4 : ℝ) * rescaledPosition n t y - t / 24) *
    P (n * t / 2) y

/-- The measure (1.15), `𝒵ₙ(t) = n^{-1/2} ∑_{x ∈ 𝕃ₙ(t)} Zₙ(t,x) δ_x`, associated to a function
`P : ℝ → ℤ → ℝ` (which will be `density ψ ω`). -/
def rescaledMeasure (L : ℕ∞) (n : ℝ) (P : ℝ → ℤ → ℝ) (t : ℝ) : Measure ℝ :=
  Measure.sum fun y : box L =>
    ENNReal.ofReal (n ^ (-1 / 2 : ℝ) * rescaledField n P t y) •
      Measure.dirac (rescaledPosition n t y)

/-! ### Space-time white noise and the stochastic heat equation -/

/-- The increment of the function `S(·, ·, ω)` on the rectangle `(s, t] × (a, b]`. In the sequel,
`S` is the distribution function of a space-time white noise `ξ` (a Brownian sheet), and
`rectMass S s t a b = ξ((s, t] × (a, b])` is the mass that `ξ` gives to this rectangle. -/
def rectMass (S : ℝ → ℝ → Ω → ℝ) (s t a b : ℝ) (ω : Ω) : ℝ :=
  S t b ω - S t a ω - S s b ω + S s a ω

/-- `IsWhiteNoise 𝓖 S ν` means that `S` is the distribution function of a space-time white noise
`ξ` on `ℝ₊ × ℝ` with respect to the filtration `𝓖` (in the sense of Walsh, as recalled in
Section 7.2 of the article): `ξ((s, t] × (a, b]) = rectMass S s t a b`. In other words, `S` is
a Brownian sheet, up to its values on the axes, which play no role.

Concretely: `S` is adapted, and for all `s ≤ t`, the masses of the rectangles `(s, t] × (a, b]`
are centered Gaussian random variables with variance `(t - s)(b - a)`, which are independent
for disjoint intervals `(a, b]`, and independent of `𝓖 s`. -/
structure IsWhiteNoise (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    Prop where
  /-- `S` is adapted to `𝓖`. -/
  adapted : ∀ (t : ℝ≥0) (x : ℝ), Measurable[𝓖 t] (S t x)
  /-- The mass of the rectangle `(s, t] × (a, b]` has the distribution `N(0, (t - s)(b - a))`. -/
  gaussian : ∀ (s t : ℝ≥0) (a b : ℝ), s ≤ t → a ≤ b →
    HasLaw (rectMass S s t a b) (gaussianReal 0 ((t - s) * (b - a).toNNReal)) ν
  /-- The masses of the rectangles `(s, t] × (a i, a (i+1)]`, for `a 0 ≤ a 1 ≤ ... ≤ a k`, are
  independent. -/
  indep : ∀ s t : ℝ≥0, s ≤ t → ∀ (k : ℕ) (a : Fin (k + 1) → ℝ), Monotone a →
    iIndepFun (fun i : Fin k => rectMass S s t (a i.castSucc) (a i.succ)) ν
  /-- The masses of the rectangles `(s, t] × (a, b]` are independent of the past `𝓖 s`. -/
  indep_past : ∀ s t : ℝ≥0, s ≤ t →
    Indep (⨆ (a : ℝ) (b : ℝ), MeasurableSpace.comap (rectMass S s t a b) inferInstance)
      (𝓖 s) ν

/-- A random field `h(s, y, ω)`, viewed as a function on `Ω × (ℝ × ℝ)`. This is used to state
that `h` belongs to `L²(Ω × ℝ × ℝ, ν ⊗ ds ⊗ dy)`. -/
def uncurryField (h : ℝ → ℝ → Ω → ℝ) (p : Ω × ℝ × ℝ) : ℝ := h p.2.1 p.2.2 p.1

/-- The Itô-Walsh stochastic integral with respect to the white noise `ξ` with distribution
function `S`: `IsWalshIntegral 𝓖 S ν h X` means that the random field `h(s,y)` is integrable
against `ξ` and that

  `X = ∫_{ℝ₊ × ℝ} h(s,y) ξ(ds dy)`   almost surely.

As in Walsh's construction, this is the smallest relation which
* contains the elementary predictable fields `h = c 𝟙_{(s,t] × (a,b]}`, where `c` is a bounded
  `𝓖 s`-measurable random variable, for which `X = c ξ((s,t] × (a,b])`;
* is stable under addition;
* is closed under limits in `L²`: if `hₖ → h` in `L²(Ω × ℝ₊ × ℝ)` and `∫ hₖ dξ → X` in `L²(Ω)`
  then `X = ∫ h dξ`.

When `IsWhiteNoise 𝓖 S ν` holds, Itô's isometry shows that `X` is determined almost surely by
`h`, and the fields `h` which are integrable in this sense are those which coincide almost
everywhere with a predictable field in `L²(Ω × ℝ₊ × ℝ)`.

In the third rule, the limits `h` and `X` are explicitly required to be (almost everywhere)
measurable and square integrable, so that the meaning of the definition does not depend on
the conventions of Mathlib for the integrals of non-measurable functions. -/
inductive IsWalshIntegral (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    (ℝ → ℝ → Ω → ℝ) → (Ω → ℝ) → Prop
  /-- Elementary predictable fields. -/
  | block (s t : ℝ≥0) (a b : ℝ) (c : Ω → ℝ) (hst : s ≤ t) (hab : a ≤ b)
      (hc : Measurable[𝓖 s] c) (hbdd : ∃ C : ℝ, ∀ ω, |c ω| ≤ C) :
      IsWalshIntegral 𝓖 S ν
        (fun r y ω => if (s : ℝ) < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then c ω else 0)
        (fun ω => c ω * rectMass S s t a b ω)
  /-- Additivity. -/
  | add (h h' : ℝ → ℝ → Ω → ℝ) (X X' : Ω → ℝ) :
      IsWalshIntegral 𝓖 S ν h X → IsWalshIntegral 𝓖 S ν h' X' →
      IsWalshIntegral 𝓖 S ν (fun r y ω => h r y ω + h' r y ω) (fun ω => X ω + X' ω)
  /-- Closure under limits in `L²`. -/
  | limit (h : ℝ → ℝ → Ω → ℝ) (X : Ω → ℝ) (hs : ℕ → ℝ → ℝ → Ω → ℝ) (Xs : ℕ → Ω → ℝ) :
      (∀ k, IsWalshIntegral 𝓖 S ν (hs k) (Xs k)) →
      MemLp (uncurryField h) 2 (ν.prod volume) → MemLp X 2 ν →
      Tendsto (fun k => eLpNorm (uncurryField (hs k) - uncurryField h) 2 (ν.prod volume))
        atTop (𝓝 0) →
      Tendsto (fun k => eLpNorm (Xs k - X) 2 ν) atTop (𝓝 0) →
      IsWalshIntegral 𝓖 S ν h X

/-- The heat kernel `g_t(x) = exp(-x² / 2t) / √(2πt)` of (1.13). -/
def heatKernel (t x : ℝ) : ℝ := Real.exp (-x ^ 2 / (2 * t)) / Real.sqrt (2 * Real.pi * t)

/-- `IsMildSolution 𝓖 S Z ν` means that the random field `Z(t,x)`, `t > 0`, `x ∈ ℝ`, is the
solution of the stochastic heat equation `∂_t Z = ½ ∂_xx Z + Z ξ` (1.12) with initial condition
`δ₀`, driven by the white noise `ξ` with distribution function `S`: it is continuous on
`(0, ∞) × ℝ`, and for all `t > 0` and `x ∈ ℝ`, almost surely,

  `Z(t,x) = g_t(x) + ∫₀ᵗ ∫_ℝ g_{t-s}(x-y) Z(s,y) ξ(ds dy)`,

which is equation (1.13). The fact that the stochastic integral is well-defined is part of the
definition. Such a random field exists (Bertini-Cancrini, Amir-Corwin-Quastel, Chen-Dalang, see
Section 7.3 of the article), and it is unique up to indistinguishability: if `Z¹` and `Z²` are
two of them, Itô's isometry shows that `F(t,x) = 𝔼[(Z¹(t,x) - Z²(t,x))²]`, which is finite, is
a fixed point of the convolution with the kernel `g_t(x)²` on `(0, ∞) × ℝ`, hence `F = 0`. -/
structure IsMildSolution (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (Z : ℝ → ℝ → Ω → ℝ)
    (ν : Measure Ω) : Prop where
  /-- Almost surely, `(t,x) ↦ Z(t,x)` is continuous on `(0, ∞) × ℝ`. -/
  continuous : ∀ᵐ ω ∂ν, ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ)
  /-- The mild form (1.13) of the stochastic heat equation. -/
  mild : ∀ t x : ℝ, 0 < t →
    IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatKernel (t - s) (x - y) * Z s y ω else 0)
      (fun ω => Z t x ω - heatKernel t x)

/-- The measure `𝒵(t)` of Theorem 1.2, associated to a function `Z : ℝ → ℝ → ℝ` (which will be
a realization of the solution of the stochastic heat equation): `𝒵(0) = δ₀` and
`𝒵(t)(dx) = max(Z(t,x), 0) dx` for `t ≠ 0`.

The positive part comes from `ENNReal.ofReal`, which sends negative numbers to `0`. For the
solution of the stochastic heat equation, `Z ≥ 0` (statement `IsMildSolution.nonneg` in
`Companions.lean`), so that `𝒵(t)(dx) = Z(t,x) dx` for `t > 0`, as in the article (see
`integral_sheMeasure` in `Checks.lean` and `IsMildSolution.integral_sheMeasure` in
`Corollaries.lean`). -/
def sheMeasure (Z : ℝ → ℝ → ℝ) (t : ℝ) : Measure ℝ :=
  if t = 0 then Measure.dirac 0 else volume.withDensity fun x => ENNReal.ofReal (Z t x)

end QSSEPtoKPZ
