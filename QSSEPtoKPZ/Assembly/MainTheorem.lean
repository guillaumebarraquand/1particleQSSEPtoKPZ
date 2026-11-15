/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Assembly.Slutsky
public import QSSEPtoKPZ.Assembly.BoxVersion
public import QSSEPtoKPZ.FiniteSystems.Statements
public import QSSEPtoKPZ.Uniqueness.Theorem12
public import QSSEPtoKPZ.Assembly.MainProof

/-!
# Theorem 1.2 (task M3)

STATEMENT FILE (task T0‴ of Stage 5, `docs/stage5-statements.md`); the proof is task M3, in
`Assembly/MainProof.lean` (`thmMain_proof`), quoted here (`docs/stage5-design.md`, Section 1.2
(f), decisions D2‴, D6‴, note on M3). For each `k`:
`ψ^∞_k` is the given `ψ_k` if `L_k = ∞`, and the wave function on `ℤ` constructed on `Ω_k` from
the given `B_k` (`prop_2_1_existence`) otherwise; `main_theorem_top` (for the filtrations
`nullAug (μ k) (𝓕 k)`) gives versions `Y_k` of `ϱ_{n_k} 𝖹_{n_k}` converging in distribution;
the versions `X_k` of `𝒵_{n_k}` are `exists_rescaledPath_version_box` for finite `L_k` and
`Y_k` for `L_k = ∞`; `abs_integral_rescaledMeasure_box_sub_le`, `prop81_bound`,
`prop81Rhs_tendsto_enat` and `varrhoN_bounds` give the closeness hypothesis of
`tendstoInDistribution_of_close`.

`main_theorem_lib` is the frozen `main_theorem` of `MainTheorem.lean`, word for word (checked
with `pp.all` and by the kernel, `docs/stage5-statements.md`). It is not imported by
`MainTheorem.lean`; `Solution.lean` states `main_theorem` and proves it by quoting
`main_theorem_lib` (decision D7‴, task F‴).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **Theorem 1.2** (convergence of the one-particle QSSEP to the stochastic heat equation),
library copy of the frozen `main_theorem`. Let `n_k → ∞`, `n_k ≥ 1`, and `L_k ∈ ℤ_{≥1} ∪ {∞}`
with `L_k / n_k^{3/4} → ∞`; for each `k` a realization of the one-particle QSSEP on `Λ_{L_k}`
(wave function `ψ k` driven by a Brownian family `B k` indexed by `ℤ × {0,1}`); on another
probability space a white noise `S` and a solution `Z` of (1.13); and `T > 0`. Then the processes
`(𝒵_{n_k}(t))_{t ∈ [0,T]}` of (1.15) and `(𝒵(t))_{t ∈ [0,T]}` (`𝒵(0) = δ₀`,
`𝒵(t)(dx) = max(Z(t,x), 0) dx`) have versions with values in `C([0,T], ℳ₊)`, and the former
converge in distribution to the latter. -/
theorem main_theorem_lib
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
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν :=
  thmMain_proof n hn₁ hn L hL₁ hL μ 𝓕 B hB ψ hψ ν 𝓖 S hS Z hZ T hT

end QSSEPtoKPZ
