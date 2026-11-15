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
# Statement of the main theorem

This file contains the formal statement of Theorem 1.2 of

  G. Barraquand, *Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation* (2026).

**Only the statement is given here; the `sorry` below is intentional.** The theorem is proved
in the library (`main_theorem_lib`, in `QSSEPtoKPZ/Assembly/MainTheorem.lean`), and
`Solution.lean` states it again word for word and proves it from there; `lake comparator` checks
that the two statements agree. All the definitions on which the statement depends are in
`QSSEPtoKPZ/Definitions.lean`; they do not use `sorry`, and neither they nor the proof use any
axiom other than the standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`).

## The statement, in words

Let `n_k → ∞` be a sequence of real numbers with `n_k ≥ 1`, and let `L_k ∈ ℤ_{≥1} ∪ {∞}` be such
that `L_k / n_k^{3/4} → ∞`. For each `k`, consider the one-particle QSSEP on `Λ_{L_k}`: on some
filtered probability space carrying independent complex Brownian motions `W⁽ˣ⁾`, let `ψ` be the
wave function, solution of (1.7), let `P(t,x) = |ψ_t(x)|²`, and let `𝒵ₙ(t)` be the measure
defined by (1.14) and (1.15) with `n = n_k`.

On another filtered probability space, let `ξ` be a space-time white noise and let `Z` be the
solution of the stochastic heat equation with initial condition `δ₀`, in the mild form (1.13).
Let `𝒵(0) = δ₀` and `𝒵(t)(dx) = Z(t,x) dx` for `t > 0`. (In Lean, `sheMeasure` uses the positive
part `max(Z(t,x), 0)`; the two agree because `Z ≥ 0`, which is the companion statement
`IsMildSolution.nonneg` and is not a hypothesis of the theorem.)

Then, for all `T > 0`, the processes `(𝒵ₙ(t))_{t ∈ [0,T]}` and `(𝒵(t))_{t ∈ [0,T]}` have
versions with values in `C([0,T], ℳ₊(ℝ))`, and the former converge in distribution to the latter
in this space.

## Remarks on the formalization

* `ℳ₊(ℝ)` is Mathlib's `FiniteMeasure ℝ`, equipped with the topology of weak convergence
  (convergence of the integrals of bounded continuous functions). The space
  `C([0,T], ℳ₊(ℝ))` is `C(Set.Icc 0 T, FiniteMeasure ℝ)` with the compact-open topology, which is
  the topology of uniform convergence since `[0,T]` is compact, and with its Borel σ-algebra.
* Convergence in distribution is Mathlib's `MeasureTheory.TendstoInDistribution`: the random
  variables are almost everywhere measurable and their laws converge weakly.
* The measures `𝒵ₙ(t)` and `𝒵(t)` are defined pathwise, as elements of `Measure ℝ`. The statement
  asserts the existence of random variables with values in `C([0,T], ℳ₊(ℝ))` which coincide
  almost surely with these processes, for all `t ∈ [0,T]` simultaneously. Two such random
  variables are almost surely equal, so that their law is uniquely determined.
* The theorem is stated for an arbitrary realization of the QSSEP and of the solution of the
  stochastic heat equation, on arbitrary probability spaces. The usual conditions on the
  filtrations are not needed to state the result (and the general case follows from the case
  where they hold, by augmenting the filtration).
* In the article the scaling parameter `n ≥ 1` is a real number. The convergence as `n → ∞` is
  equivalent to the convergence along every sequence `n_k → ∞`, which is what is stated here.
* The Cole-Hopf solution `h = log Z` of the KPZ equation, which is mentioned in the statement of
  Theorem 1.2, is defined by this formula and does not need to appear in the formal statement.

See `README.md` for a discussion of the choices made in the definitions.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

namespace QSSEPtoKPZ

/-- **Theorem 1.2** (convergence of the one-particle QSSEP to the stochastic heat equation).

Stated here without proof; it is proved in `Solution.lean`, from the library copy
`main_theorem_lib`. -/
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
  sorry

end QSSEPtoKPZ
