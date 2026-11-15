/-
Formal statement of the main theorem of
  G. Barraquand, "Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation" (2026).
Lean 4 / Mathlib formalization written by Claude (Anthropic) at the request of the author,
November 2026. See README.md.
-/
module

public import QSSEPtoKPZ.Assembly.MainTheorem
public import QSSEPtoKPZ.FiniteSystems.Existence
public import QSSEPtoKPZ.FiniteSystems.Uniqueness
public import QSSEPtoKPZ.WhiteNoise.Existence
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.Uniqueness.SecondMoment

/-!
# Solution file

The counterpart of `Challenge.lean` for the Lean `comparator` tool (configuration in
`comparator.json`). It imports the definitions of `QSSEPtoKPZ/Definitions.lean` (through the
library) and states the eight theorems of `QSSEPtoKPZ/MainTheorem.lean` and
`QSSEPtoKPZ/Companions.lean` verbatim (decision D7‴ of `docs/stage5-design.md`). Each is
proved by its library copy (`main_theorem_lib`, `exists_isWaveFunction_lib`, …), whose
statement was checked to be identical (`pp.all`, kernel both ways). It does not import
`MainTheorem.lean` or `Companions.lean`, which keep their `sorry` on purpose: they are the
statement files from which `Challenge.lean` is generated. `lake comparator` checks that each
theorem here has exactly the statement of `Challenge.lean` and uses only the standard axioms.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

namespace QSSEPtoKPZ

/-- **Theorem 1.2** (convergence of the one-particle QSSEP to the stochastic heat equation).

Proved from the library copy `main_theorem_lib` (`QSSEPtoKPZ/Assembly/MainTheorem.lean`), whose
statement is identical. -/
theorem main_theorem
    -- The scaling parameter `n → ∞` and the sizes `L ∈ ℤ_{≥1} ∪ {∞}` of the systems,
    -- with `L / n^{3/4} → ∞`.
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ∞) (hL₁ : ∀ k, 1 ≤ L k)
    (hL : Tendsto (fun k => (L k : ℝ≥0∞) / ENNReal.ofReal (n k ^ (3 / 4 : ℝ))) atTop (𝓝 ⊤))
    -- For each `k`, the one-particle QSSEP on `Λ_{L k}`: a filtered probability space,
    -- independent Brownian motions `B k`, and the wave function `ψ k`.
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction (L k) (𝓕 k) (B k) (ψ k) (μ k))
    -- The solution `Z` of the stochastic heat equation with initial condition `δ₀`, driven by
    -- a space-time white noise `ξ` (encoded by its distribution function `S`).
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ')
    (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν)
    -- The time horizon.
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝒵n : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
      (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      -- `𝒵n k` is the process `(𝒵ₙ(t))_{t ∈ [0,T]}` of (1.15), with `n = n k`,
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵n k ω t : Measure ℝ) = rescaledMeasure (L k) (n k) (density (ψ k) ω) t) ∧
      -- `𝒵` is the process `𝒵(0) = δ₀`, `𝒵(t)(dx) = max(Z(t,x), 0) dx` (`= Z(t,x) dx`, since
      -- `Z ≥ 0` by `IsMildSolution.nonneg`),
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      -- and `𝒵n k` converges in distribution to `𝒵` in `C([0,T], ℳ₊(ℝ))`.
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν := by
  apply main_theorem_lib <;> assumption

end QSSEPtoKPZ


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
  apply exists_isWaveFunction_lib

/-- **U1** (pathwise uniqueness of the wave function; Proposition 2.1 when `L = ∞`, linear
stochastic differential equations in finite dimension when `L < ∞`). Two wave functions on `Λ_L`
driven by the same Brownian family, with respect to the same filtration, are indistinguishable:
almost surely, `ψ_t = ψ'_t` for all `t ≥ 0`. -/
theorem isWaveFunction_unique {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {L : ℕ∞}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℤ × Fin 2 → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ)
    (hψ' : IsWaveFunction L 𝓕 B ψ' μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ t ω = ψ' t ω := by
  apply isWaveFunction_unique_lib <;> assumption

/-! ### Space-time white noise and the stochastic heat equation -/

/-- **E2** (existence of space-time white noise; used implicitly throughout Section 7). There
are a probability space, a filtration and a random field `S` which is the distribution function
of a space-time white noise with respect to this filtration. -/
theorem exists_isWhiteNoise :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ν : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ)
      (S : ℝ → ℝ → Ω → ℝ),
      IsProbabilityMeasure ν ∧ IsWhiteNoise 𝓖 S ν := by
  apply exists_isWhiteNoise_lib

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
  apply IsWalshIntegral.ae_eq_lib <;> assumption

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
  apply IsWalshIntegral.isometry_lib <;> assumption

/-- **U3** (uniqueness for the stochastic heat equation; Section 7.3, and point 4 of "Choices
made in the formalization" in `README.md`). Two solutions of (1.13) driven by the same white
noise are indistinguishable on `(0, ∞) × ℝ`: almost surely, `Z(t,x) = Z'(t,x)` for all `t > 0`
and `x ∈ ℝ`. -/
theorem isMildSolution_unique {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z Z' : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) (hZ' : IsMildSolution 𝓖 S Z' ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → Z t x ω = Z' t x ω := by
  apply isMildSolution_unique_lib <;> assumption

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
  apply IsMildSolution.nonneg_lib <;> assumption

end QSSEPtoKPZ
