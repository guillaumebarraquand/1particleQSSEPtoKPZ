/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.WaveFunction.Kernel

/-!
# Definitions of Section 8: the measure `𝖹_n^L` and the tail of the random walk

DEFINITION FILE (task T0‴ of Stage 5, `docs/stage5-statements.md`, `docs/stage5-design.md`,
Section 2.1). Complete definitions, no `sorry`.

* `tiltedMeasureBox L n ψ ω t`: the measure `𝖹_n^L(t) = ∑_{x ∈ Λ_L} 𝔷_n(t,x) δ_{y_n(t,x)}` of
  Section 8 (before Proposition 8.1), with `𝔷_n(t,x) = exp(θ_n x - n λ_n t / 2) P(n t / 2, x)`
  computed from `ψ` (`zN`, Stage 2). For `L = ∞` it is the measure `𝖹_n(t)` of (3.5)
  (`tiltedMeasure`), up to the reindexing `box ⊤ ≃ ℤ`.
* `rwTail s L = 𝖯(|X_s| ≥ L) = ∑_{|x| ≥ L} p_s(x)`, with `p_s = rwKernel s` the law of the
  continuous-time simple random walk `X` at time `s` (Stage 2), as in Lemma 8.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The measure `𝖹_n^L(t) = ∑_{x ∈ Λ_L} 𝔷_n(t,x) δ_{y_n(t,x)}` of Section 8, where
`𝔷_n(t,x) = exp(θ_n x - n λ_n t / 2) P(n t / 2, x)` is computed from `ψ` (`zN`) and
`y_n(t,x) = n^{-1/2}(x - n^{3/4} t)` (`rescaledPosition`). With `ψ = ψ^L` (a wave function on
`Λ_L`) it is the article's `𝖹_n^L(t)`; with `L = ∞` it is `𝖹_n(t)` of (3.5). -/
def tiltedMeasureBox (L : ℕ∞) (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) : Measure ℝ :=
  Measure.sum fun x : box L =>
    ENNReal.ofReal (zN n ψ ω t x) • Measure.dirac (rescaledPosition n t x)

/-- `𝖯(|X_s| ≥ L) = ∑_{|x| ≥ L} p_s(x)`, for the continuous-time simple random walk `X` started
from `0` which jumps at rate `1` to each neighbour (`p_s = rwKernel s`), as in Lemma 8.2. -/
def rwTail (s : ℝ) (L : ℕ) : ℝ := ∑' x : ℤ, if (L : ℤ) ≤ |x| then rwKernel s x else 0

end QSSEPtoKPZ
