/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.Uniqueness.SecondMomentIter

/-!
# Second moments of mild solutions, (7.15), and uniqueness U3 (task K2)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task K2.
See `docs/stage4-design.md`, Section 1.2 (h), and `docs/stage4-interfaces.md`.

For a solution `Z` of (1.13) (the frozen `IsMildSolution`): `F(t,x) = 𝔼[Z(t,x)²]` is finite
(W) and satisfies `F = K + K ⋆ F` with `K(t,x) = g_t(x)²` (Itô isometry, `𝔼 Z(t,x) = g_t(x)`);
since `K^{⋆k} ≤ ε_k K`, `F = ∑_{k ≥ 1} K^{⋆k}`, which is (7.15) in series form (decision D9″).
The same computation for the difference of two solutions gives **U3**
(`isMildSolution_unique_lib`, library copy of `isMildSolution_unique` of `Companions.lean`,
statement identical, checked with `pp.all`). `heatMild_integral_sq` is the statement
`IsMildSolution.integral_sq` of `Uniqueness/MildSolution.lean` (same statement).

Proofs (task K2): the jointly measurable version and `𝔼 ∫ h dξ = 0` in
`SecondMomentVersion.lean`; the convolution `⊛` on `(0,t) × ℝ` and its associativity in
`SecondMomentConv.lean`; the renewal equation, its iteration, the series and the core of U3 in
`SecondMomentIter.lean`. U3 then follows by continuity from equality at rational points.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- **U3** (library copy of `isMildSolution_unique` of `Companions.lean`; uniqueness for the
stochastic heat equation; Section 7.3). Two solutions of (1.13) driven by the same white noise
are indistinguishable on `(0, ∞) × ℝ`: almost surely, `Z(t,x) = Z'(t,x)` for all `t > 0` and
`x ∈ ℝ`. -/
theorem isMildSolution_unique_lib {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z Z' : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) (hZ' : IsMildSolution 𝓖 S Z' ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → Z t x ω = Z' t x ω := by
  obtain ⟨V, hVae, hVm, hVc, hV⟩ := secondMom_exists_version hS hZ
  obtain ⟨V', hV'ae, hV'm, hV'c, hV'⟩ := secondMom_exists_version hS hZ'
  have hrat : ∀ᵐ ω ∂ν, ∀ q : ℚ × ℚ, 0 < (q.1 : ℝ) → V q.1 q.2 ω = V' q.1 q.2 ω := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < (q.1 : ℝ)
    · filter_upwards [secondMom_ae_eq_of_measurable hS hV hV' hVm hV'm hq q.2] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [hVae, hV'ae, hrat] with ω h1 h2 h3 t x ht
  have := secondMom_eqOn_of_rat (hVc ω) (hV'c ω) (fun q hq => h3 q hq)
    (show (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ from ⟨ht, trivial⟩)
  rw [← h1 t x ht, ← h2 t x ht]
  exact this

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- **A jointly measurable, everywhere continuous version** of a mild solution: it agrees with
`Z` on `(0, ∞) × ℝ` almost surely, is continuous on `(0, ∞) × ℝ` for every `ω`, and is again a
mild solution. -/
theorem heatMild_exists_version (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) :
    ∃ Z' : ℝ → ℝ → Ω → ℝ, (∀ᵐ ω ∂ν, ∀ t x, 0 < t → Z' t x ω = Z t x ω) ∧
      Measurable (uncurryField Z') ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℝ => Z' p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ)) ∧
      IsMildSolution 𝓖 S Z' ν :=
  secondMom_exists_version hS hZ

/-- (7.15), as a series (same statement as `IsMildSolution.integral_sq`):
`𝔼[Z(t,x)²] = ∑_{k ≥ 1} K^{⋆k}(t,x)`, `K^{⋆k}(t,x) = 2^{-k} t^{k/2-1} Γ(k/2)⁻¹ g_{t/2}(x)`. -/
theorem heatMild_integral_sq (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) {t x : ℝ} (ht : 0 < t) :
    MemLp (Z t x) 2 ν ∧ HasSum (fun k : ℕ => (2 : ℝ) ^ (-((k : ℝ) + 1)) *
        t ^ (((k : ℝ) + 1) / 2 - 1) / Real.Gamma (((k : ℝ) + 1) / 2) * heatKernel (t / 2) x)
      (∫ ω, Z t x ω ^ 2 ∂ν) := by
  refine ⟨secondMom_memLp hS hZ ht x, ?_⟩
  obtain ⟨V, hVae, hVm, -, hV⟩ := secondMom_exists_version hS hZ
  have e : ∫ ω, Z t x ω ^ 2 ∂ν = ∫ ω, V t x ω ^ 2 ∂ν :=
    integral_congr_ae (hVae.mono fun ω h => by simp only [h t x ht])
  rw [e]
  exact secondMom_hasSum_of_measurable hS hV hVm ht

/-- The bound `𝔼[Z(t,x)²] ≤ C g_t(x)²` on `(0,T] × ℝ`. -/
theorem heatMild_integral_sq_le (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) (T : ℝ) :
    ∃ C, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, ∫ ω, Z t x ω ^ 2 ∂ν ≤ C * heatKernel t x ^ 2 := by
  obtain ⟨ε, hεs, -, hε⟩ := heatSqIter_le T
  refine ⟨∑' k, ε k, fun t ht x => ?_⟩
  have h : HasSum (fun k : ℕ => heatSqIter k t x) (∫ ω, Z t x ω ^ 2 ∂ν) :=
    (heatMild_integral_sq hS hZ ht.1).2
  exact hasSum_le (fun k => hε k t ht x) h (hεs.hasSum.mul_right _)

end QSSEPtoKPZ
