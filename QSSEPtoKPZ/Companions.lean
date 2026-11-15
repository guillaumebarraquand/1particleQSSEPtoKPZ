/-
Formal statement of the main theorem of
  G. Barraquand, "Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation" (2026).
Lean 4 / Mathlib formalization written by Claude (Anthropic) at the request of the author,
November 2026. See README.md.
-/
module

public import QSSEPtoKPZ.Definitions

/-!
# Companion statements: the hypotheses of the main theorem can be met

`main_theorem` is about *every* realization of the one-particle QSSEP and *every* realization of
the solution of the stochastic heat equation. If one of the definitions it relies on could not
be satisfied, the theorem would be true for an empty reason. The statements below say that the
objects exist, and that they are unique, so that the definitions mean what they are meant to
mean. They are the statements E1, U1, E2, W, U3 of the plan of the formalization, and the
statement P (nonnegativity of the solution of the stochastic heat equation), added on
12 November 2026.

**Only the statements are given here; the `sorry` below are intentional.** All of them are
proved in the library (copies named `*_lib`), and `Solution.lean` states them again word for word
and proves them from there.

* E1 `exists_isWaveFunction`: for every `L`, the wave function exists on some filtered
  probability space carrying a Brownian family.
* U1 `isWaveFunction_unique`: two wave functions driven by the same Brownian family are
  indistinguishable.
* E2 `exists_isWhiteNoise`: a space-time white noise exists on some filtered probability space.
* W `IsWalshIntegral.ae_eq`, `IsWalshIntegral.isometry`: the stochastic integral of a field is
  determined almost surely by the field (up to null sets), the field and the integral are square
  integrable, and Itô's isometry holds.
* U3 `isMildSolution_unique`: two solutions of the stochastic heat equation (1.13) driven by the
  same white noise are indistinguishable on `(0, ∞) × ℝ`.
* P `IsMildSolution.nonneg`: the solution of the stochastic heat equation is nonnegative. It is
  needed to read the measure `sheMeasure Z t`, which is defined with `max (Z t x) 0`, as
  `Z(t,x) dx` (see `integral_sheMeasure` in `Checks.lean`).

The existence of a solution of the stochastic heat equation in the sense of `IsMildSolution`
(statement E3 of the plan of the formalization: a field which is continuous on `(0, ∞) × ℝ`
and satisfies (1.13)) is **not stated here and is left unproved**, by decision of the author
(11 November 2026). It is
known in the literature (Bertini-Cancrini, Amir-Corwin-Quastel, Chen-Dalang; see Section 7.3 of
the article), and it is not used in the proof of the main theorem.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

namespace QSSEPtoKPZ

/-! ### The one-particle QSSEP -/

/-- **E1** (existence of the wave function; Proposition 2.1 when `L = ∞`, Section 1.3 when
`L < ∞`). For every `L ∈ ℕ ∪ {∞}`, there are a probability space, a filtration, a family of
independent Brownian motions `B` indexed by `ℤ × {0, 1}`, and a process `ψ` which is the wave
function of the one-particle QSSEP on `Λ_L` driven by `B`. -/
theorem exists_isWaveFunction (L : ℕ∞) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)),
      IsProbabilityMeasure μ ∧ IsBrownianFamily 𝓕 B μ ∧ IsWaveFunction L 𝓕 B ψ μ := by
  sorry

/-- **U1** (pathwise uniqueness of the wave function; Proposition 2.1 when `L = ∞`, linear
stochastic differential equations in finite dimension when `L < ∞`). Two wave functions on `Λ_L`
driven by the same Brownian family, with respect to the same filtration, are indistinguishable:
almost surely, `ψ_t = ψ'_t` for all `t ≥ 0`. -/
theorem isWaveFunction_unique {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {L : ℕ∞}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℤ × Fin 2 → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ)
    (hψ' : IsWaveFunction L 𝓕 B ψ' μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ t ω = ψ' t ω := by
  sorry

/-! ### Space-time white noise and the stochastic heat equation -/

/-- **E2** (existence of space-time white noise; used implicitly throughout Section 7). There
are a probability space, a filtration and a random field `S` which is the distribution function
of a space-time white noise with respect to this filtration. -/
theorem exists_isWhiteNoise :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ν : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ)
      (S : ℝ → ℝ → Ω → ℝ),
      IsProbabilityMeasure ν ∧ IsWhiteNoise 𝓖 S ν := by
  sorry

/-- **W**, first part (the Itô-Walsh integral is well defined; Section 7.2). If `X = ∫ h dξ`
and `X' = ∫ h' dξ`, and the fields `h` and `h'` agree almost everywhere on
`Ω × ℝ₊ × ℝ`, then `X = X'` almost surely. In particular the integral of a field is determined
up to a null set. -/
theorem IsWalshIntegral.ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {h h' : ℝ → ℝ → Ω → ℝ} {X X' : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) (hX' : IsWalshIntegral 𝓖 S ν h' X')
    (hh : uncurryField h =ᵐ[ν.prod volume] uncurryField h') :
    X =ᵐ[ν] X' := by
  sorry

/-- **W**, second part (Itô's isometry for the Itô-Walsh integral; Section 7.2). If
`X = ∫ h dξ`, then `h` is square integrable on `Ω × ℝ₊ × ℝ`, `X` is square integrable, and

  `𝔼[X²] = 𝔼 ∫∫ h(s,y)² ds dy`.

Both integrability statements are part of the conclusion, so that the identity cannot hold
because of Lean's convention that the integral of a non-integrable function is `0`. -/
theorem IsWalshIntegral.isometry {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    MemLp (uncurryField h) 2 (ν.prod volume) ∧ MemLp X 2 ν ∧
      ∫ ω, X ω ^ 2 ∂ν = ∫ p, uncurryField h p ^ 2 ∂(ν.prod volume) := by
  sorry

/-- **U3** (uniqueness for the stochastic heat equation; Section 7.3, and point 4 of "Choices
made in the formalization" in `README.md`). Two solutions of (1.13) driven by the same white
noise are indistinguishable on `(0, ∞) × ℝ`: almost surely, `Z(t,x) = Z'(t,x)` for all `t > 0`
and `x ∈ ℝ`. -/
theorem isMildSolution_unique {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z Z' : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) (hZ' : IsMildSolution 𝓖 S Z' ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → Z t x ω = Z' t x ω := by
  sorry

/-- **P** (nonnegativity of the solution of the stochastic heat equation; Section 1.4 of the
article, which quotes Mueller and Moreno for the strict positivity). Almost surely,
`Z(t,x) ≥ 0` for all `t > 0` and `x ∈ ℝ`.

Nonnegativity is neither a hypothesis of `IsMildSolution` nor part of the conclusion of
`main_theorem`. It is what makes the measure `sheMeasure Z t`, which is defined with the positive
part `max (Z t x) 0` (because `ENNReal.ofReal` sends negative numbers to `0`), equal to the
measure `Z(t,x) dx` of the article: see `integral_sheMeasure` and
`integral_sheMeasure_of_nonneg` in `Checks.lean`, and `IsMildSolution.integral_sheMeasure` in
`Corollaries.lean`.

It is not an input of the proof of `main_theorem`. It is deduced from the limit: the field `Z`
has the law of the density of a limit of the nonnegative measures `𝒵ₙ`
(`IsMildSolution.nonneg_of_isWaveFunction`), and a wave function on `ℤ` exists (E1). This does
not use the existence statement E3. -/
theorem IsMildSolution.nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → 0 ≤ Z t x ω := by
  sorry

end QSSEPtoKPZ
