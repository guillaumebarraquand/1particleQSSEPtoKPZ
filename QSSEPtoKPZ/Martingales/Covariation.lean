/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Defs
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Cross brackets (Stage 2, package B)

`HasCovariation T 𝓕 M N A μ` means `⟨M, N⟩ = A` on `[0, T]`, in the sense of
`docs/stage2-design.md`, Section 1.2 (b): `M` and `N` are continuous square-integrable
martingales on `[0, T]` (up to null sets, `IsCL2Mart`), `A` is integrable, almost surely
continuous with `A_0 = 0`, and `M N - A` is a martingale on `[0, T]` (up to null sets).

It is used in Proposition 2.2 (equation (2.5) for `x ≠ y`, where `A = 0`). It is kept in a
separate file because `Martingales/Defs.lean` was merged before this definition was written.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `⟨M, N⟩_t = A_t` on `[0, T]`: `M` and `N` are continuous square-integrable martingales on
`[0, T]` (up to null sets, as in `IsCL2Mart`), `A` is integrable, almost surely continuous and
of bounded variation on `[0, T]` with `A_0 = 0`, and `𝔼[M_t N_t - A_t | 𝓕_s] = M_s N_s - A_s`
almost surely for `0 ≤ s ≤ t ≤ T`. The bounded variation makes `A` unique (a continuous
martingale of bounded variation is constant); without it, `A` would only be determined up to a
continuous martingale. -/
structure HasCovariation (T : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (M N A : ℝ → Ω → ℝ)
    (μ : Measure Ω) : Prop where
  left : IsCL2Mart T 𝓕 M μ
  right : IsCL2Mart T 𝓕 N μ
  integrable_cov : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (A t) μ
  zero : ∀ᵐ ω ∂μ, A 0 ω = 0
  cont_cov : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 T)
  bv : ∀ᵐ ω ∂μ, BoundedVariationOn (fun t => A t ω) (Set.Icc 0 T)
  condExp_mul : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T →
    μ[fun ω => M t ω * N t ω - A t ω | 𝓕 s] =ᵐ[μ] fun ω => M s ω * N s ω - A s ω

end QSSEPtoKPZ
