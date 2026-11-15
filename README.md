# A formal proof of the convergence of the one-particle QSSEP to the KPZ equation

Lean 4 / Mathlib formalization of the statement **and the proof** of the main theorem (Theorem 1.2) of

> G. Barraquand, *Convergence of the one-particle quantum symmetric simple exclusion process to the KPZ equation* (2026).

The Lean code was written by Claude (Anthropic) in November 2026, at the request of the author, who approved the statements stage by stage (see `docs/`).

## Status

| | |
|---|---|
| Theorem 1.2 | `QSSEPtoKPZ.main_theorem`: **proved** |
| Companion statements (non-vacuity and well-posedness) | E1 existence of the wave function, U1 its uniqueness, E2 existence of a white noise, W Itô isometry and uniqueness of the Walsh integral, U3 uniqueness of the solution of the stochastic heat equation, P its positivity: **all proved** |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Checked by | `lake comparator` (Lean's kernel), and with `--paranoid` also Lean's paranoid kernel, lean4lean, nanoda, con-leche and con-ron |
| Versions | Lean 4.35.0, Mathlib v4.35.0 (commit `56a0058`), pinned in `lake-manifest.json` |
| Size | about 62,600 lines of Lean |

Not formalized: the existence of a continuous solution of the stochastic heat equation started from $\delta_0$, a result from the literature. It is not needed for the theorem as stated, which quantifies over all solutions.

## Layout

| File | Content |
|---|---|
| `Challenge.lean` | **the statement only**: the 17 definitions and the 8 theorems (Theorem 1.2 and the 7 companions) with `sorry`, importing Mathlib only. This is the file to read to know what is proved. |
| `Solution.lean` | the same 8 theorems, proved from the library |
| `comparator.json` | configuration of `lake comparator` (Challenge vs Solution, permitted axioms) |
| `QSSEPtoKPZ/Definitions.lean`, `MainTheorem.lean`, `Companions.lean` | the statement inside the library (`Challenge.lean` is generated from them by `scripts/make_challenge.py`); their theorems keep `sorry`, their proofs are in `Solution.lean` |
| `QSSEPtoKPZ/` (other folders) | the proof, organized by sections of the article: `WaveFunction/` (Section 2), `TiltedField/` (3), `SecondMoments/` (4), `Tightness/` (5), `Replacement/` (6), `LimitPoints/`, `WhiteNoise/`, `Uniqueness/` (7), `FiniteSystems/` (8 and Section 2.1), `Assembly/` (end of the proof); generic tools in `Martingales/` and `ItoIntegral/` |
| `docs/` | for each stage: the statements approved by the author (`stageN-statements`), the design, the interfaces, an independent audit, and a report; `parse-audit` (a check of all approved statements for misread notation); the comparator logs |
| `DEVIATIONS.md` | where the formal proof departs from the printed proofs of the article |

## How to check it

With Lean installed through `elan`:

```
lake exe cache get        # downloads the compiled Mathlib
lake build                # builds the library, Challenge and Solution
lake comparator           # judges Solution against Challenge
```

Expected results:

* `lake build` ends with `Build completed successfully`. Its only warnings are 16 times `declaration uses 'sorry'`, all in `QSSEPtoKPZ/MainTheorem.lean`, `QSSEPtoKPZ/Companions.lean` and `Challenge.lean`: these are the statement files, which keep `sorry` on purpose (`lake build 2>&1 | grep '^warning' | grep -v 'declaration uses'` prints nothing).
* `lake comparator` ends with `Your solution is okay!`: every theorem of `Solution.lean` has exactly the statement of `Challenge.lean`, uses only the three standard axioms, and is accepted by the kernel. `lake comparator --paranoid` also runs the five other checkers bundled with Lean.
* Directly: `printf 'import Solution\n#print axioms QSSEPtoKPZ.main_theorem\n' | lake env lean --stdin` prints `[propext, Classical.choice, Quot.sound]`.

## The statement

```lean
theorem main_theorem
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ∞) (hL₁ : ∀ k, 1 ≤ L k)
    (hL : Tendsto (fun k => (L k : ℝ≥0∞) / ENNReal.ofReal (n k ^ (3 / 4 : ℝ))) atTop (𝓝 ⊤))
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction (L k) (𝓕 k) (B k) (ψ k) (μ k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ')
    (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝒵n : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
      (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵n k ω t : Measure ℝ) = rescaledMeasure (L k) (n k) (density (ψ k) ω) t) ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν
```

In words: for every sequence of real numbers `n k ≥ 1` going to infinity and all sizes `L k ∈ ℤ_{≥1} ∪ {∞}` with `L k / (n k)^{3/4} → ∞`; for every realization of the one-particle QSSEP on `Λ_{L k}` (a filtered probability space, independent Brownian motions, and the wave function `ψ k` solving (1.7)); for every realization of the solution `Z` of the stochastic heat equation with initial condition `δ₀` (a filtered probability space, a white noise, and a continuous random field solving (1.13)); and for every `T > 0`: the processes `(𝒵ₙ(t))_{t ∈ [0,T]}` and `(𝒵(t))_{t ∈ [0,T]}` have versions with values in `C([0,T], ℳ₊(ℝ))`, and the former converge in distribution to the latter.

## Dictionary

| Article | Lean | Remarks |
|---|---|---|
| filtered probability space `(Ω, ℱ, (ℱ_t), ℙ)` | `Ω`, `μ : Measure Ω`, `𝓕 : Filtration ℝ≥0 mΩ` | the usual conditions are not assumed |
| independent real `(ℱ_t)`-Brownian motions `B₁⁽ˣ⁾, B₂⁽ˣ⁾` | `IsBrownianFamily 𝓕 B μ`, with `B : ℤ × Fin 2 → ℝ → Ω → ℝ` | adapted, a.s. continuous, `B_0 = 0`, increments `N(0, t-s)`, independent of each other and of `ℱ_s` |
| `W⁽ˣ⁾ = (B₁⁽ˣ⁾ + i B₂⁽ˣ⁾)/√2` | `complexBM B x` | |
| `Λ_L`, `L ∈ ℤ_{≥1} ∪ {∞}` | `box L`, `L : ℕ∞` | `Λ_∞ = ℤ` |
| `D(x,x)` | `degree L x` | |
| wave function `ψ_t`, eq. (1.7) | `IsWaveFunction L 𝓕 B ψ μ` | integral form of the SDE; `ψ` vanishes outside `Λ_L` |
| `P(t,x)`, eq. (1.8) | `density ψ ω t x` | |
| `Zₙ(t,x)`, `𝒵ₙ(t)`, eqs. (1.14)–(1.15) | `rescaledField`, `rescaledMeasure L n P t` | |
| space-time white noise `ξ` | `IsWhiteNoise 𝓖 S ν` | `S` is the distribution function of `ξ` |
| Itô–Walsh integral `∫ h dξ` | `IsWalshIntegral 𝓖 S ν h X` | `X = ∫ h dξ`; defined as the smallest relation containing elementary predictable fields, stable under sums and `L²` limits |
| `g_t(x)` | `heatKernel t x` | |
| solution of the SHE from `δ₀`, eq. (1.13) | `IsMildSolution 𝓖 S Z ν` | continuous on `(0,∞) × ℝ` |
| `𝒵(t)` | `sheMeasure Z t` | `δ₀` if `t = 0`, `max(Z(t,x), 0) dx` otherwise; equal to `Z(t,x) dx` since `Z ≥ 0` (companion P) |
| `C([0,T], ℳ₊)`, convergence in distribution | `C(Set.Icc (0:ℝ) T, FiniteMeasure ℝ)`, `TendstoInDistribution` | Mathlib; Borel σ-algebra; a different probability space for each `k` is allowed |

## Choices made in the formal statement

1. **Stochastic integrals.** In `IsWaveFunction` the Itô integrals are limits in probability of left-point Riemann sums; `IsWalshIntegral` is Walsh's construction stated as a characterization (its well-posedness, the companion W, is proved).
2. **White noise** is encoded by its distribution function (a Brownian sheet).
3. **Wave function.** For all `L`, `ψ` is defined by the stochastic differential equation (1.7), not as `U_t e₀`.
4. **Solution of the stochastic heat equation.** A random field continuous on `(0,∞) × ℝ` satisfying (1.13) for all `(t,x)`; adaptedness and positivity are not assumed (uniqueness U3 and positivity P are proved).
5. **"For every realization".** The theorem quantifies over all probability spaces carrying the QSSEP and all carrying a solution of the SHE; it is not vacuous since such objects exist (E1, E2).
6. **Versions.** The conclusion asserts that `𝒵ₙ` and `𝒵` have versions with continuous trajectories in `ℳ₊(ℝ)`.
7. **Filtrations** are arbitrary (no usual conditions); continuity, `B_0 = 0` and the support condition are required almost surely.
8. **The parameter `n`** is an arbitrary sequence of reals `≥ 1` going to infinity.

## Contents of the proof

The proof follows the article section by section; `DEVIATIONS.md` lists the places where it departs from the printed proofs (mostly where a cited theorem is not available in Mathlib and a direct argument was shorter). Generic results proved along the way and not in Mathlib include: continuous-time martingales (Doob's inequalities, optional sampling, null augmentation), the Itô integral against a countable Brownian family with the product rule, Aldous' tightness criterion for continuous paths, metrizability of `ℳ₊(ℝ)` through a countable family of test functions, Skorokhod's representation along a subsequence, Lévy's characterization of Brownian motion, integrals against orthogonal martingale measures, the existence of a space-time white noise, and Picard iteration for the wave equation in `ℓ²(ℤ)`.

## License

Copyright 2026 Guillaume Barraquand. Released under the Apache License 2.0 (see `LICENSE`).
