/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Defs
public import QSSEPtoKPZ.FiniteSystems.Picard
public import QSSEPtoKPZ.FiniteSystems.Lemma82
public import QSSEPtoKPZ.FiniteSystems.Prop81

/-!
# Proposition 2.1 (existence), Lemma 8.2, Proposition 8.1

STATEMENT FILE (task T0‴ of Stage 5, `docs/stage5-statements.md`, `docs/stage5-design.md`,
Sections 2.2, 2.3). Each statement is proved by quoting a twin with the same statement in the
file of the task that proves it: `picard_isWaveFunction` (task L2b, `FiniteSystems/Picard.lean`),
`lemma82_bound` (task L6, `FiniteSystems/Lemma82.lean`), `prop81_tendsto` (task L8,
`FiniteSystems/Prop81.lean`). This file was not modified by those tasks; the statements below
depend on no `sorry`.

Conventions of Stages 2–4: arbitrary probability spaces, filtrations without the usual
conditions, probabilities of events not claimed measurable are outer probabilities, every series
and integral that appears is asserted genuine.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- **Proposition 2.1, existence** (strong form, every `L ∈ ℕ ∪ {∞}`; for `L < ∞` the existence
half of "linear SDE in finite dimension", Section 1.3). On any filtered probability space
carrying a family `B` of independent Brownian motions indexed by `ℤ × {0,1}` (`IsBrownianFamily`),
there is a wave function on `Λ_L` driven by `B` (`IsWaveFunction`, equation (1.7)), adapted to
the filtration augmented by the null sets (`nullAug`; the article works under the usual
conditions, where the two filtrations coincide). The uniqueness half is the companion U1
(`isWaveFunction_unique_lib`). -/
theorem prop_2_1_existence (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞) :
    ∃ ψ : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveFunction L (nullAug μ 𝓕) B ψ μ :=
  picard_isWaveFunction hB L

/-- **Lemma 8.2**, equation (8.1). Let `ψ` be a wave function on `ℤ` and `ψ^L` a wave function on
`Λ_L` (`L ≥ 1` an integer), driven by the same Brownian family for the same filtration (the
coupling of Section 8), `P = |ψ|²`, `P^L = |ψ^L|²` (`density`), and `S > 0`. Then the series
`𝖯(|X_s| ≥ L) = ∑_{|x| ≥ L} p_s(x)` converge (`s ≥ 0`), `s ↦ 𝖯(|X_s| ≥ L)` is integrable on
`[0,S]`, the supremum below is a random variable (up to null sets), and
`𝔼[sup_{s ∈ [0,S]} (∑_{x ∈ Λ_L} |P(s,x) - P^L(s,x)|)²] ≤ 4(8+S) ∫_0^S 𝖯(|X_s| ≥ L) ds`,
`X` the continuous-time simple random walk started from `0` (law `p_s = rwKernel s`). -/
theorem lemma_8_2 [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {L : ℕ} (hL : 1 ≤ L) (hψL : IsWaveFunction L 𝓕 B ψL μ) {S : ℝ} (hS : 0 < S) :
    (∀ s : ℝ, 0 ≤ s → Summable fun x : ℤ => if (L : ℤ) ≤ |x| then rwKernel s x else 0) ∧
    IntervalIntegrable (fun s => rwTail s L) volume 0 S ∧
    AEMeasurable (fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x|) ^ 2)) μ ∧
    ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x|) ^ 2)) ∂μ ≤
      ENNReal.ofReal (4 * (8 + S) * ∫ s in (0 : ℝ)..S, rwTail s L) :=
  lemma82_bound hB hψ hL hψL hS

/-- **Proposition 8.1**. Let `n_k ≥ 1` with `n_k → ∞`, and integers `L_k ≥ 1` with
`L_k / n_k^{3/4} → ∞`. For each `k`, on a filtered probability space with a Brownian family
`B_k`, let `ψ_k` be a wave function on `ℤ` and `ψ^L_k` a wave function on `Λ_{L_k}`, both driven
by `B_k` for the same filtration (the coupling of Section 8). Then for all `T > 0` and `ε > 0`,
`ℙ*(sup_{t ∈ [0,T]} ‖𝖹^{L_k}_{n_k}(t) - 𝖹_{n_k}(t)‖_TV > ε) → 0`: the supremum of the total
variation distance (Mathlib's `etvDist`, infinite if a measure is infinite) tends to `0` in
(outer) probability. -/
theorem prop_8_1 (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ) (hL₁ : ∀ k, 1 ≤ L k)
    (hL : Tendsto (fun k => (L k : ℝ) / n k ^ (3 / 4 : ℝ)) atTop atTop)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (ψL : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ))
    (hψL : ∀ k, IsWaveFunction (L k) (𝓕 k) (B k) (ψL k) (μ k))
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k => μ k {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
        etvDist (tiltedMeasureBox (L k) (n k) (ψL k) ω t) (tiltedMeasure (n k) (ψ k) ω t)})
      atTop (𝓝 0) :=
  prop81_tendsto n hn₁ hn L hL₁ hL μ 𝓕 B hB ψ hψ ψL hψL T hT ε hε

end QSSEPtoKPZ
