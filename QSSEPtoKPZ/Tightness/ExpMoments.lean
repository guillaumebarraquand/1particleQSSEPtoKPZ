/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.Tightness.ExpMomentsAux

/-!
# Lemma 5.2: exponential moments and compact containment

Statement: Stage 3, task T0' (`docs/stage3-design.md`, Section 3.2); proof: task Q1, as in the
article (the auxiliary results are in `Tightness/ExpMomentsAux.lean`).

Notation of the article: `e_b(y) = e^{b y}`, `cosh = (e_1 + e_{-1}) / 2`, and
`𝖹_n(t;φ) = ∑ₓ 𝔷_n(t,x) φ(y_n(t,x))` (`pairZ`). The test functions `e_b` and `cosh` are
unbounded; the first conjunct of `lemma_5_2` (almost sure convergence of the series
`∑ₓ 𝔷_n(t,x) e^{b y_n(t,x)}` for all `t ≥ 0` and `b ∈ [-1,1]`) makes the series `𝖹_n(t;e_b)`
and `𝖹_n(t;cosh)` genuine ones (otherwise Lean gives them the value `0`). The supremum in
(5.1) is taken in `[0, ∞]`, and the probability of the event is the outer probability (the
event is not claimed to be measurable; a bound on the outer probability is stronger).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Lemma 5.2**, with equation (5.1). For `n ≥ 1`:
* almost surely, for all `t ≥ 0` and `b ∈ [-1,1]`, the series `∑ₓ 𝔷_n(t,x) e^{b y_n(t,x)}`
  converges;
* for `b ∈ [-1,1]` and `t ≥ 0`, `𝖹_n(t;e_b)` is integrable and `𝔼[𝖹_n(t;e_b)] ≤ e^{2t}`;
* (5.1): for `T > 0` and `K > 0`,
  `ℙ(sup_{t ∈ [0,T]} 𝖹_n(t;cosh) ≥ K) ≤ 2 e^{2T} / K`
  (supremum in `[0, ∞]`, outer probability). -/
theorem lemma_5_2 (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n : ℝ} (hn : 1 ≤ n) :
    (∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      Summable fun x => zN n ψ ω t x * Real.exp (b * rescaledPosition n t x)) ∧
    (∀ b ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => pairZ n ψ ω t fun y => Real.exp (b * y)) μ ∧
      ∫ ω, pairZ n ψ ω t (fun y => Real.exp (b * y)) ∂μ ≤ Real.exp (2 * t)) ∧
    ∀ T K : ℝ, 0 < T → 0 < K →
      μ {ω | ENNReal.ofReal K ≤ ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (pairZ n ψ ω t Real.cosh)} ≤
        ENNReal.ofReal (2 * Real.exp (2 * T) / K) :=
  ⟨expMom_ae_summable hB hψ hn, fun _ hb _ ht => expMom_integral_le hB hψ hn hb ht,
    fun _ _ hT hK => expMom_compact_containment hB hψ hn hT hK⟩

end QSSEPtoKPZ
