/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Defs
public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.Martingales.Defs
public import QSSEPtoKPZ.WaveFunction.ExpWeightsIto

/-!
# Lemma 2.3 (1): linear functionals of `P`

Statement: Stage 2, task T0; proof: task D5. Take a unit-norm version `ψ'` of `ψ`
(`IsWaveFunction.exists_isUnitWave`), equal to `ψ` at all times almost surely; for `ψ'` this is
`IsUnitWave.lemma_2_3_linear_unit` (file `ExpWeightsIto.lean`: boxes `|x| ≤ K` and `K → ∞`, the
tails being controlled by (2.2)). The statement for `ψ` follows on the almost sure event
`{ψ'_t = ψ_t for all t ≥ 0}` (`HasBracket.congr`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Lemma 2.3 (1), equation (2.7)**, `L = ∞`. Let `T > 0`, `a ≥ 0`, and let `α_t(x)` be `C¹` in
`t ∈ [0,T]` (derivative `α'`, continuous in `t`, one-sided at `0` and `T`) with
`|α_t(x)| + |∂ₜα_t(x)| ≤ C e^{a|x|}`. Then almost surely, for `t ∈ [0,T]`, the series
`∑ₓ α_t(x) P(t,x)`, `∑ₓ (∂ₜα_t + Δα_t)(x) P(t,x)` and `∑ₓ (α_t(x+1) - α_t(x))² P(t,x) P(t,x+1)`
converge absolutely, the drift and the bracket density below are integrable on `[0,T]`, and
`M_t = ∑ₓ α_t(x) P(t,x) - α_0(0) - ∫_0^t ∑ₓ (∂ₛα_s + Δα_s)(x) P(s,x) ds`
(the last term of (2.7), `∫_0^t ∑ₓ (α_s(x+1) - α_s(x)) dJ_s(x)`) is a continuous square-integrable
martingale on `[0,T]` with bracket `⟨M⟩_t = ∫_0^t ∑ₓ 2 (α_s(x+1) - α_s(x))² P(s,x) P(s,x+1) ds`
(the bracket of the stochastic integral, by (2.5)). -/
theorem lemma_2_3_linear (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {T a C : ℝ} (hT : 0 < T) (ha : 0 ≤ a) {α α' : ℝ → ℤ → ℝ}
    (hα : ∀ x, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (α · x) (α' t x) (Set.Icc 0 T) t)
    (hα' : ∀ x, ContinuousOn (α' · x) (Set.Icc 0 T))
    (hbd : ∀ x, ∀ t ∈ Set.Icc 0 T, |α t x| + |α' t x| ≤ C * Real.exp (a * |(x : ℝ)|)) :
    (∀ᵐ ω ∂μ, (∀ t ∈ Set.Icc 0 T,
        Summable (fun x => |α t x| * density ψ ω t x) ∧
        Summable (fun x => |α' t x + lap (α t) x| * density ψ ω t x) ∧
        Summable (fun x => (α t (x + 1) - α t x) ^ 2 * density ψ ω t x * density ψ ω t (x + 1))) ∧
      IntervalIntegrable (fun s => ∑' x, (α' s x + lap (α s) x) * density ψ ω s x) volume 0 T ∧
      IntervalIntegrable (fun s => ∑' x,
        2 * (α s (x + 1) - α s x) ^ 2 * density ψ ω s x * density ψ ω s (x + 1)) volume 0 T) ∧
    HasBracket T 𝓕
      (fun t ω => ∑' x, α t x * density ψ ω t x - α 0 0 -
        ∫ s in (0 : ℝ)..t, ∑' x, (α' s x + lap (α s) x) * density ψ ω s x)
      (fun t ω => ∫ s in (0 : ℝ)..t, ∑' x,
        2 * (α s (x + 1) - α s x) ^ 2 * density ψ ω s x * density ψ ω s (x + 1)) μ := by
  obtain ⟨ψ', hu⟩ := hψ.exists_isUnitWave hB
  obtain ⟨h1, h2⟩ := hu.lemma_2_3_linear_unit hB hT ha hα hα' hbd
  -- on the event `{ψ'_t = ψ_t for all t ≥ 0}`, the densities agree at all times `s ≥ 0`
  have hden : ∀ᵐ ω ∂μ, ∀ s : ℝ, 0 ≤ s → density ψ ω s = density ψ' ω s := by
    filter_upwards [hu.ae_eq] with ω hω s hs
    funext x
    show ‖ψ s ω x‖ ^ 2 = ‖ψ' s ω x‖ ^ 2
    rw [show ψ' s ω = ψ s ω from hω ⟨s, hs⟩]
  have hint : ∀ ω, (∀ s : ℝ, 0 ≤ s → density ψ ω s = density ψ' ω s) →
      ∀ (F : ℝ → (ℤ → ℝ) → ℝ) (t : ℝ), 0 ≤ t →
        ∫ s in (0 : ℝ)..t, F s (density ψ ω s) = ∫ s in (0 : ℝ)..t, F s (density ψ' ω s) :=
    fun ω hω F t ht => intervalIntegral.integral_congr fun s hs => by
      rw [Set.uIcc_of_le ht] at hs
      simp only [hω s hs.1]
  have hII : ∀ ω, (∀ s : ℝ, 0 ≤ s → density ψ ω s = density ψ' ω s) →
      ∀ F : ℝ → (ℤ → ℝ) → ℝ, IntervalIntegrable (fun s => F s (density ψ' ω s)) volume 0 T →
        IntervalIntegrable (fun s => F s (density ψ ω s)) volume 0 T :=
    fun ω hω F hF => hF.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2
      (ae_of_all _ fun s hs => by
        rw [Set.uIoc_of_le hT.le] at hs
        simp only [hω s hs.1.le]))
  refine ⟨?_, ?_⟩
  · filter_upwards [h1, hden] with ω hω hd
    refine ⟨fun t ht => ?_, hII ω hd (fun s P => ∑' x, (α' s x + lap (α s) x) * P x) hω.2.1,
      hII ω hd (fun s P => ∑' x, 2 * (α s (x + 1) - α s x) ^ 2 * P x * P (x + 1)) hω.2.2⟩
    rw [hd t ht.1]
    exact hω.1 t ht
  · refine h2.congr hT.le ?_ ?_
    · filter_upwards [hden] with ω hd t ht
      rw [hd t ht.1, hint ω hd (fun s P => ∑' x, (α' s x + lap (α s) x) * P x) t ht.1]
    · filter_upwards [hden] with ω hd t ht
      exact (hint ω hd (fun s P => ∑' x, 2 * (α s (x + 1) - α s x) ^ 2 * P x * P (x + 1))
        t ht.1).symm

end QSSEPtoKPZ
