/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Tightness.FiniteMeasureEmbed

/-!
# An explicit metric on `C([0,T], ℳ₊)` (task M1)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task M1.
`docs/stage5-design.md`, Sections 1.2 (f), 3.5, decision D6‴.

`pathMetricDist γ γ' = sup_{t ∈ [0,T]} ∑_j min(2^{-j}, |γ(t)(f_j) - γ'(t)(f_j)|)`, with the bump
functions `f_j = bumpTest j` of Stage 3 (`‖f_j‖_∞ ≤ 1`). It is the pull-back of the uniform
metric on `C([0,T], ℝ^ℕ)` (with the countable-product metric) by the embedding
`γ ↦ (t ↦ (γ(t)(f_j))_j)` (`isEmbedding_tightEmb`, `ContinuousMap.isEmbedding_postcomp`), so it
induces the topology of `C([0,T], ℳ₊)`; this, and the local `PseudoMetricSpace` structure, are
internal to task M1 (`Slutsky.lean`).

* `pathMetricDist_le_of_close`: if `|γ(t)(f) - γ'(t)(f)| ≤ ε ‖f‖_∞` for all `t` and all bounded
  continuous `f`, then `pathMetricDist γ γ' ≤ ∑_j min(2^{-j}, ε)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

/-- The metric on paths `C([0,T], ℳ₊)`:
`sup_{t ∈ [0,T]} ∑_j min(2^{-j}, |∫ f_j dγ(t) - ∫ f_j dγ'(t)|)` (design: `pathDist`). -/
def pathMetricDist {T : ℝ} (γ γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, ∑' j : ℕ, min ((1 / 2 : ℝ) ^ j)
    |(∫ x, bumpTest j x ∂(γ t : Measure ℝ)) - ∫ x, bumpTest j x ∂(γ' t : Measure ℝ)|

/-- `‖f_j‖_∞ ≤ 1` for the bump functions `f_j = bumpTest j`. -/
theorem pathMetric_norm_bumpTest_le_one (j : ℕ) : ‖bumpTest j‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).2 fun x => by
    simpa [Real.norm_eq_abs] using abs_bumpTestRaw_le j x

/-- If `a_j ≥ 0`, the series `∑_j min(2^{-j}, a_j)` converges (domination by `∑_j 2^{-j}`). -/
theorem pathMetric_summable_min (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    Summable fun j : ℕ => min ((1 / 2 : ℝ) ^ j) (a j) :=
  Summable.of_nonneg_of_le (fun j => le_min (by positivity) (ha j)) (fun j => min_le_left _ _)
    summable_geometric_two

/-- **Closeness at one time.** If `|μ(f) - ν(f)| ≤ ε ‖f‖_∞` for every bounded continuous `f`,
then `∑_j min(2^{-j}, |μ(f_j) - ν(f_j)|) ≤ ∑_j min(2^{-j}, ε)` (because `‖f_j‖_∞ ≤ 1`). -/
theorem pathMetric_tsum_le_of_close {ε : ℝ} (hε : 0 ≤ ε) {μ ν : FiniteMeasure ℝ}
    (h : ∀ f : ℝ →ᵇ ℝ, |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)| ≤ ε * ‖f‖) :
    (∑' j : ℕ, min ((1 / 2 : ℝ) ^ j)
      |(∫ x, bumpTest j x ∂(μ : Measure ℝ)) - ∫ x, bumpTest j x ∂(ν : Measure ℝ)|) ≤
      ∑' j : ℕ, min ((1 / 2 : ℝ) ^ j) ε := by
  refine Summable.tsum_le_tsum (fun j => min_le_min_left _ ?_)
    (pathMetric_summable_min _ fun _ => abs_nonneg _) (pathMetric_summable_min _ fun _ => hε)
  exact (h (bumpTest j)).trans
    (by simpa using mul_le_mul_of_nonneg_left (pathMetric_norm_bumpTest_le_one j) hε)

/-- Uniform weak closeness bounds the path metric. -/
theorem pathMetricDist_le_of_close {T ε : ℝ} (hε : 0 ≤ ε)
    {γ γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (h : ∀ (t : Set.Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
      |(∫ x, f x ∂(γ t : Measure ℝ)) - ∫ x, f x ∂(γ' t : Measure ℝ)| ≤ ε * ‖f‖) :
    pathMetricDist γ γ' ≤ ∑' j : ℕ, min ((1 / 2 : ℝ) ^ j) ε :=
  Real.iSup_le (fun t => pathMetric_tsum_le_of_close hε (h t))
    (tsum_nonneg fun _ => le_min (by positivity) hε)

end QSSEPtoKPZ
