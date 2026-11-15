/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Assembly.MainTheorem
public import QSSEPtoKPZ.FiniteSystems.Existence
public import QSSEPtoKPZ.Checks

/-!
# The consequences of the main theorem, from the library (decision D10‴)

Proved copies of the two results of `Corollaries.lean` (`main_theorem_fixed_time`,
`IsMildSolution.integral_sheMeasure`), with the same statements and the same proofs, quoting the
library copies `main_theorem_lib` and `IsMildSolution.nonneg_lib` instead of the statement files
(`Corollaries.lean` imports `MainTheorem.lean` and `Companions.lean` and keeps their `sorry`).
Written by task I0‴ of Stage 5; they depend on no `sorry` (`main_theorem_lib` and
`exists_isWaveFunction_lib` are proved, by tasks M3 and E1b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

namespace QSSEPtoKPZ

/-- For any fixed `t ≥ 0` and any bounded continuous function `φ`, the integral of `φ` against
`𝒵ₙ(t)` converges in distribution to the integral of `φ` against `𝒵(t)` (library copy of
`main_theorem_fixed_time`). -/
theorem main_theorem_fixed_time_lib
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
    (t : ℝ) (ht : 0 ≤ t) (φ : BoundedContinuousFunction ℝ ℝ) :
    TendstoInDistribution
      (fun k ω => ∫ x, φ x ∂(rescaledMeasure (L k) (n k) (density (ψ k) ω) t)) atTop
      (fun ω => ∫ x, φ x ∂(sheMeasure (fun s x => Z s x ω) t)) μ ν := by
  have hT : (0 : ℝ) < max t 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨𝒵n, 𝒵, h₁, h₂, h₃⟩ :=
    main_theorem_lib n hn₁ hn L hL₁ hL μ 𝓕 B hB ψ hψ ν 𝓖 S hS Z hZ (max t 1) hT
  have ht' : t ∈ Set.Icc (0 : ℝ) (max t 1) := ⟨ht, le_max_left _ _⟩
  refine (tendstoInDistribution_integral h₃ ⟨t, ht'⟩ φ).congr (fun k => ?_) ?_
  · filter_upwards [h₁ k] with ω hω
    rw [hω ⟨t, ht'⟩]
  · filter_upwards [h₂] with ω hω
    rw [hω ⟨t, ht'⟩]

/-- The measure `𝒵(t)` of the statement is `Z(t,x) dx`: almost surely, for all `t > 0` and every
function `φ`, `∫ φ d𝒵(t) = ∫ Z(t,x) φ(x) dx` (library copy of
`IsMildSolution.integral_sheMeasure`, using `IsMildSolution.nonneg_lib`). -/
theorem IsMildSolution.integral_sheMeasure_lib {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ν : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∀ᵐ ω ∂ν, ∀ t : ℝ, 0 < t → ∀ φ : ℝ → ℝ,
      ∫ x, φ x ∂(sheMeasure (fun s x => Z s x ω) t) = ∫ x, Z t x ω * φ x := by
  filter_upwards [hZ.nonneg_lib hS, hZ.continuous] with ω hpos hcont t ht φ
  have hc : Continuous fun x => Z t x ω :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨ht, trivial⟩
  exact integral_sheMeasure_of_nonneg ht.ne' hc.measurable (fun x => hpos t x ht) φ

end QSSEPtoKPZ
