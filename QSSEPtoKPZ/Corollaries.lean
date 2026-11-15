/-
Formal statement of the main theorem of
  G. Barraquand, "Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation" (2026).
Lean 4 / Mathlib formalization written by Claude (Anthropic) at the request of the author,
November 2026. See README.md.
-/
module

public import QSSEPtoKPZ.Checks
public import QSSEPtoKPZ.Companions
public import QSSEPtoKPZ.MainTheorem

/-!
# A consequence of the main theorem

The statement which follows Theorem 1.2 in the article: for any fixed time `t` and any bounded
continuous function `φ`,

  `n^{-1/2} ∑_{x ∈ 𝕃ₙ(t)} Zₙ(t,x) φ(x)  ⟹  ∫ Z(t,x) φ(x) dx`.

It is deduced here from the statement `main_theorem` of `MainTheorem.lean` (hence, as compiled
here, it depends on the intentional `sorry` of that statement file, and on nothing else). It shows
how the formal statement of the main theorem can be used. The same results, with the same
statements and proofs but quoting the proved library copies, are in `Assembly/Corollaries.lean`
and depend on no `sorry`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

namespace QSSEPtoKPZ

/-- For any fixed `t ≥ 0` and any bounded continuous function `φ`, the integral of `φ` against
`𝒵ₙ(t)` converges in distribution to the integral of `φ` against `𝒵(t)`. -/
theorem main_theorem_fixed_time
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
    main_theorem n hn₁ hn L hL₁ hL μ 𝓕 B hB ψ hψ ν 𝓖 S hS Z hZ (max t 1) hT
  have ht' : t ∈ Set.Icc (0 : ℝ) (max t 1) := ⟨ht, le_max_left _ _⟩
  refine (tendstoInDistribution_integral h₃ ⟨t, ht'⟩ φ).congr (fun k => ?_) ?_
  · filter_upwards [h₁ k] with ω hω
    rw [hω ⟨t, ht'⟩]
  · filter_upwards [h₂] with ω hω
    rw [hω ⟨t, ht'⟩]

/-- The measure `𝒵(t)` of the statement is `Z(t,x) dx`, as in the article: almost surely, for all
`t > 0` and every function `φ`, `∫ φ d𝒵(t) = ∫ Z(t,x) φ(x) dx`.

`sheMeasure` is defined with the positive part of `Z` (see `integral_sheMeasure`). This result
removes the positive part, using the nonnegativity of the solution `IsMildSolution.nonneg`;
as compiled here it therefore depends on the intentional `sorry` of that statement (the copy in
`Assembly/Corollaries.lean` does not). -/
theorem IsMildSolution.integral_sheMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ν : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∀ᵐ ω ∂ν, ∀ t : ℝ, 0 < t → ∀ φ : ℝ → ℝ,
      ∫ x, φ x ∂(sheMeasure (fun s x => Z s x ω) t) = ∫ x, Z t x ω * φ x := by
  filter_upwards [hZ.nonneg hS, hZ.continuous] with ω hpos hcont t ht φ
  have hc : Continuous fun x => Z t x ω :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨ht, trivial⟩
  exact integral_sheMeasure_of_nonneg ht.ne' hc.measurable (fun x => hpos t x ht) φ

end QSSEPtoKPZ
