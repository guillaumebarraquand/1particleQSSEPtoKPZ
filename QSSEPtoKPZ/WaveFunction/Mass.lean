/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.Martingales.Defs
public import QSSEPtoKPZ.WaveFunction.MassLimit

/-!
# Conservation of the mass

Statement: Stage 2, task T0; proof: task D2. The proof takes a good version `ψ̃` of `ψ`
(`IsWaveFunction.exists_isGoodWave`), for which `‖ψ̃_t‖ = 1` for all `t`, almost surely
(`IsGoodWave.ae_norm_eq_one`, file `MassLimit.lean`), and uses `∑ₓ |ψ̃_t(x)|² = ‖ψ̃_t‖²` and the
indistinguishability of `ψ̃` and `ψ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Conservation of the mass** (the consequence of (2.7) with `α ≡ 1` stated after
Lemma 2.3): almost surely, for all `t ≥ 0`, `∑_{x ∈ ℤ} P(t,x) = 1` (the series converges, with
sum `1`). -/
theorem hasSum_density (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, HasSum (density ψ ω t) 1 := by
  obtain ⟨ψ', hg⟩ := hψ.exists_isGoodWave
  filter_upwards [hg.ae_norm_eq_one hB, hg.ae_eq] with ω h1 h2 t
  have h := hasSum_density_norm_sq ψ' ω t
  rw [h1 t, one_pow] at h
  have e : density ψ' ω t = density ψ ω t := by
    funext x
    simp only [density, h2 t]
  rwa [e] at h

end QSSEPtoKPZ
