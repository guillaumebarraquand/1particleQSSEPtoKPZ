/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71
public import QSSEPtoKPZ.WhiteNoise.Prop72
public import QSSEPtoKPZ.Uniqueness.SheVersion
public import QSSEPtoKPZ.Uniqueness.MildSolution
public import QSSEPtoKPZ.Uniqueness.WeakMildBridge
public import QSSEPtoKPZ.Tightness.Prop51
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import QSSEPtoKPZ.Uniqueness.Theorem12Proof

/-!
# Theorem 1.2 for `L_n = ∞`, and nonnegativity of the solution of the SHE

STATEMENT FILE (task T0″ of Stage 4, `docs/stage4-statements.md`); the proofs are task Q5
(13 November 2026), in `Uniqueness/Theorem12Proof.lean` (`thm12_main_top`, `thm12_nonneg`;
`docs/stage4-design.md`, Section 1.2 (h) and note on Q5). From `prop_7_1` and
`prop_7_2` (with `𝒵(0) = δ₀`, the first conjunct of `prop_7_1`), the interface
`isWeakMild_prod_of_eq_7_8` (task Q5a) gives `IsWeakMild` for the lifted density on `Ω × Ω'`,
the hypothesis of `exists_sheVersion_map_eq`.

`main_theorem_top` is the frozen `main_theorem` of `MainTheorem.lean` with `L k = ∞` for every
`k`; the hypotheses on `L` (`1 ≤ L k`, `L k / n_k^{3/4} → ∞`), which then hold, are dropped
(decision D11″). Its conclusion is that of `main_theorem` with `L k = ⊤` (checked with `pp.all`,
`docs/stage4-statements.md`). The frozen `main_theorem` (all `L k`) also needs Section 8:
it is `main_theorem_lib` (`Assembly/MainTheorem.lean`, Stage 5).

`IsMildSolution.nonneg_of_isWaveFunction` is the conditional form of the companion statement P
(`IsMildSolution.nonneg`): P follows from it and the companion E1 for `L = ∞`
(`IsMildSolution.nonneg_lib`, `FiniteSystems/Existence.lean`, Stage 5).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- **Theorem 1.2 when `L_n = ∞` for all `n`** (end of Section 7). This is `main_theorem` with
`L k = ⊤` for every `k`. Let `n_k → ∞`, `n_k ≥ 1`; for each `k` a realization of the
one-particle QSSEP on `ℤ` (wave function `ψ k`); on another probability space a white noise `S`
and a solution `Z` of (1.13); and `T > 0`. Then the processes `(𝒵_{n_k}(t))_{t ∈ [0,T]}` of
(1.15) and `(𝒵(t))_{t ∈ [0,T]}` (`𝒵(0) = δ₀`, `𝒵(t)(dx) = max(Z(t,x), 0) dx`) have versions with
values in `C([0,T], ℳ₊)`, and the former converge in distribution to the latter. -/
theorem main_theorem_top
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ')
    (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝒵n : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
      (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵n k ω t : Measure ℝ) = rescaledMeasure ⊤ (n k) (density (ψ k) ω) t) ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν :=
  thm12_main_top n hn₁ hn μ 𝓕 B hB ψ hψ ν 𝓖 S hS Z hZ T hT

/-- **Nonnegativity of the solution of the SHE, conditionally on the existence of the QSSEP on
`ℤ`** (companion P, conditional form). If some probability space carries a Brownian family and a
wave function on `ℤ` (the conclusion of the companion E1 for `L = ∞`), then every solution `Z`
of (1.13) is almost surely nonnegative on `(0, ∞) × ℝ`. -/
theorem IsMildSolution.nonneg_of_isWaveFunction
    (hE : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀) (μ₀ : Measure Ω₀)
      (𝓕₀ : Filtration ℝ≥0 m₀) (B₀ : ℤ × Fin 2 → ℝ → Ω₀ → ℝ) (ψ₀ : ℝ → Ω₀ → ℓ²(ℤ, ℂ)),
      IsProbabilityMeasure μ₀ ∧ IsBrownianFamily 𝓕₀ B₀ μ₀ ∧ IsWaveFunction ⊤ 𝓕₀ B₀ ψ₀ μ₀)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → 0 ≤ Z t x ω :=
  thm12_nonneg hE hS hZ

end QSSEPtoKPZ
