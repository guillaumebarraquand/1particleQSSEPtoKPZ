/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71Density
public import QSSEPtoKPZ.LimitPoints.Prop71Bracket

/-!
# Proposition 7.1: properties of the limit points

STATEMENT FILE (task T0″ of Stage 4, `docs/stage4-statements.md`). `prop_7_1` is proved (task
Q4, 13 November 2026) in this file, from `limPt_dirac_density` (task Q2) and
`IsLimCoupling.hasBracket` (task Q4), through `skorokhod_subseq` and `limBr_hasBracket_map_iff`
(`hasBracket_map_iff` with the bracket modified off a null set); `eq_7_4` is quoted from
`limPt_eq_7_4` (task Q2, same statement).

A **limit point** (decision D6″): let `n_k → ∞`, and for each `k` a realization of the
one-particle QSSEP on `ℤ` and a version `Zv k` of `(𝖹_{n_k}(t))_{t ∈ [0,T]}` (Stage 3,
`prop_5_1_version`); let `Y` be any random variable with values in `C([0,T], ℳ₊)` such that
`Zv k → Y` in distribution. The statements concern the law of `Y` only, so that they hold for
every such `Y`, on any probability space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Proposition 7.1**, with (7.1), (7.2), (7.3). Let `ρ` be a mollifier (Section 6), `T > 0`,
`n_k → ∞` (`n_k ≥ 1`), and for each `k` a realization of the one-particle QSSEP on `ℤ` with a
version `Zv k` of `(𝖹_{n_k}(t))_{t ∈ [0,T]}`; let `Y : Ω → C([0,T], ℳ₊)` be measurable with
`Zv k → Y` in distribution, and write `𝒵 = Y`. Then:
1. almost surely `𝒵(0) = δ₀`;
2. the field `Z(t,x) = liminf_k (𝒵(t) ⋆ ρ_{1/k})(x)` (`0` if infinite; `limField`) is
   predictable for the natural filtration `𝒢⁰` of `𝒵` (times the Borel σ-algebra in `x`),
   nonnegative, satisfies (7.1) `𝔼 ∫_0^T ∫ Z(t,x)² dx dt < ∞`, and almost surely
   `𝒵(t)(dx) = Z(t,x) dx` for almost every `t ∈ [0,T]`;
3. for every `φ ∈ C_b^{1,3}([0,T] × ℝ)`, the process `M^φ` of (7.2) is a continuous
   square-integrable martingale for `𝒢⁰` augmented by the null sets, with
   `⟨M^φ⟩_t = ∫_0^t ∫ Z(s,x)² φ_s(x)² dx ds` (7.3) (`HasBracket`, which also asserts that the
   bracket is integrable, continuous, nondecreasing and `0` at `0`). -/
theorem prop_7_1 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T : ℝ} (hT : 0 < T)
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ωk : ℕ → Type*} {mΩk : ∀ k, MeasurableSpace (Ωk k)}
    (μ : ∀ k, Measure (Ωk k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩk k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ωk k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ωk k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (Zv : ∀ k, Ωk k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (hZv : ∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
      (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t)
    {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    (hconv : TendstoInDistribution Zv atTop Y μ Pr) :
    (∀ᵐ ω ∂Pr, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0) ∧
    (Measurable[((pathFiltration (mΩ := mΩ) Y).predictable).prod (borel ℝ)]
        (fun p : (ℝ≥0 × Ω) × ℝ => limField ρ Y p.1.1 p.2 p.1.2) ∧
      (∀ t x ω, 0 ≤ limField ρ Y t x ω) ∧
      ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limField ρ Y t x ω ^ 2)) ∂Pr < ⊤ ∧
      ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (pathAt (Y ω) t : Measure ℝ) =
          volume.withDensity fun x => ENNReal.ofReal (limField ρ Y t x ω)) ∧
    ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T (nullAug Pr (pathFiltration Y)) (limMart Y φ φt)
        (limBracket (limField ρ Y) φ) Pr := by
  have h12 := limPt_dirac_density hρ hT n hn₁ hn μ 𝓕 B hB ψ hψ Zv hZv hY hconv
  refine ⟨h12.1, h12.2, ?_⟩
  intro φ φt C hφ
  -- Skorokhod's representation along a subsequence
  obtain ⟨σ, hσ, Ω', _, Pr', hPr', X', Y', hX', hY', hXmap, hYmap, hconv'⟩ :=
    skorokhod_subseq hconv.tendsto
  have hYmap' : Pr'.map Y' = Pr.map Y := hYmap
  have hc : IsLimCoupling Pr' T (fun j => n (σ j)) X' Y' :=
    { isProbabilityMeasure := hPr'
      pos := hT
      one_le := fun j => hn₁ (σ j)
      tendsto_atTop := hn.comp hσ.tendsto_atTop
      measurable := hX'
      measurable_lim := hY'
      law := fun j => by
        rw [hXmap j]
        exact ⟨Ωk (σ j), mΩk (σ j), μ (σ j), 𝓕 (σ j), B (σ j), ψ (σ j), Zv (σ j), inferInstance,
          hB (σ j), hψ (σ j), hconv.forall_aemeasurable (σ j), hZv (σ j), rfl⟩
      tendsto := hconv' }
  -- Proposition 7.1 (2) for `Y'`, which has the law of `Y`
  have hconvY' : TendstoInDistribution Zv atTop Y' μ Pr' :=
    { forall_aemeasurable := hconv.forall_aemeasurable
      aemeasurable_limit := hY'.aemeasurable
      tendsto := by
        have e : (⟨Pr'.map Y', inferInstance⟩ : ProbabilityMeasure _) =
            ⟨Pr.map Y, inferInstance⟩ := Subtype.ext hYmap'
        rw [e]
        exact hconv.tendsto }
  have h12' := limPt_dirac_density hρ hT n hn₁ hn μ 𝓕 B hB ψ hψ Zv hZv hY' hconvY'
  have hbr := hc.hasBracket hρ h12'.2.2.2.1 h12'.2.2.2.2 hφ
  have hcan := (limBr_hasBracket_map_iff hT.le hY' hρ hφ
    (limBr_ae_good hY' hρ h12'.2.2.2.1)).1 hbr
  rw [hYmap'] at hcan
  exact (limBr_hasBracket_map_iff hT.le hY hρ hφ (limBr_ae_good hY hρ h12.2.2.2.1)).2 hcan

/-- **Equation (7.4)**: there is a constant `C`, depending only on `ρ`, such that for every limit
point `𝒵 = Y` as in `prop_7_1` (any `T > 0`, any `n_k → ∞`, any realizations and versions) and
every `ε > 0`, `𝔼 ∫_0^T ‖𝒵(t) ⋆ ρ_ε‖₂² dt ≤ C 2^{16T}` (computed in `[0, ∞]`; the integrand is
asserted to be jointly measurable in `(ω, t)`, so that the integrals are genuine). The
probability space `Ω` of `𝒵` is bound after `∃ C`, so `C` does not depend on it (only the
universe levels are fixed outside). -/
theorem eq_7_4 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ {T : ℝ}, 0 < T → ∀ (n : ℕ → ℝ), (∀ k, 1 ≤ n k) → Tendsto n atTop atTop →
    ∀ {Ωk : ℕ → Type*} {mΩk : ∀ k, MeasurableSpace (Ωk k)}
      (μ : ∀ k, Measure (Ωk k)) [∀ k, IsProbabilityMeasure (μ k)]
      (𝓕 : ∀ k, Filtration ℝ≥0 (mΩk k))
      (B : ∀ k, ℤ × Fin 2 → ℝ → Ωk k → ℝ), (∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k)) →
    ∀ (ψ : ∀ k, ℝ → Ωk k → ℓ²(ℤ, ℂ)), (∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k)) →
    ∀ (Zv : ∀ k, Ωk k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t) →
    ∀ {Ω : Type*} {_ : MeasurableSpace Ω} {Pr : Measure Ω} [IsProbabilityMeasure Pr]
      {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}, Measurable Y → TendstoInDistribution Zv atTop Y μ Pr → ∀ {ε : ℝ}, 0 < ε →
      Measurable (fun p : Ω × ℝ => ENNReal.ofReal
        (smoothedNormSq (pathAt (Y p.1) p.2 : Measure ℝ) (fun _ => 1) ρ ε)) ∧
      ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (smoothedNormSq (pathAt (Y ω) t : Measure ℝ) (fun _ => 1) ρ ε)) ∂Pr ≤
        ENNReal.ofReal (C * 2 ^ (16 * T)) :=
  limPt_eq_7_4 hρ

end QSSEPtoKPZ
