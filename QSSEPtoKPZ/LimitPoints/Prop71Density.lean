/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PrelimitLaw
public import QSSEPtoKPZ.LimitPoints.Mollify
public import QSSEPtoKPZ.LimitPoints.Skorokhod
public import QSSEPtoKPZ.LimitPoints.Prop71Fatou
public import QSSEPtoKPZ.LimitPoints.Prop71Duality

/-!
# Proposition 7.1 (1), (2) and (7.4) (task Q2)

INTERFACE FILE (task I0″ of Stage 4), proved by task Q2 (13 November 2026).
See `docs/stage4-design.md`, Section 1.2 (e), and `docs/stage4-interfaces.md`.

`limPt_eq_7_4` is the statement `eq_7_4` of `LimitPoints/Prop71.lean` (same statement), and
`limPt_dirac_density` gives the first two parts of `prop_7_1` (same hypotheses). Both are
statements about the law of `Y` (the limit of the laws `P_k` of the versions), proved with
Fatou's lemma under convergence in law (`limPt_lintegral_le_of_tendsto`, through Skorokhod's
representation `skorokhod_subseq`):
* (1): applied to the indicator of the open set `{γ : γ(0) ≠ δ₀}`, whose `P_k`-integral is `0`
  (`IsPathPrelimLaw.ae_dirac`);
* (7.4): applied to `γ ↦ ∫_0^T ‖γ(t) ⋆ ρ_{ε_k}‖₂² dt` with `ε_k = ⌊ε n_k^{1/2}⌋ n_k^{-1/2} → ε`
  (`pathPrelim_eq_6_2` for large `k`, continuity of `(μ, ε) ↦ ‖μ ⋆ ρ_ε‖₂²`);
* (2): Fatou twice with (7.4) for `ε = 1/(k+1)` gives
  `𝔼 ∫_0^T liminf_k ‖𝒵(t) ⋆ ρ_{1/(k+1)}‖₂² dt ≤ C 2^{16T}`, hence (7.1) by
  `lintegral_limDensity_sq_le`; where the liminf is finite, `limPt_bound_of_liminf` gives the
  duality bound and `withDensity_limDensity_of_bound` the density; predictability is
  `measurable_limField_predictable`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

universe u v

/-- (7.4), with the universes of the realizations and of the space of `𝒵` named (proof of
`limPt_eq_7_4`). With `P_k` the law of `Zv k` and `ε_k = ⌊ε n_k^{1/2}⌋ n_k^{-1/2} → ε`,
`∫ ∫_0^T ‖γ(t) ⋆ ρ_{ε_k}‖₂² dt dP_k(γ) ≤ C 2^{16T}` by (6.2) (`pathPrelim_eq_6_2`) for large `k`,
and Fatou's lemma under convergence in law (`limPt_lintegral_le_of_tendsto`) passes to the
limit. -/
private theorem prop71Dens_eq_7_4_aux {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ {T : ℝ}, 0 < T → ∀ (n : ℕ → ℝ), (∀ k, 1 ≤ n k) → Tendsto n atTop atTop →
    ∀ {Ωk : ℕ → Type u} {mΩk : ∀ k, MeasurableSpace (Ωk k)}
      (μ : ∀ k, Measure (Ωk k)) [∀ k, IsProbabilityMeasure (μ k)]
      (𝓕 : ∀ k, Filtration ℝ≥0 (mΩk k))
      (B : ∀ k, ℤ × Fin 2 → ℝ → Ωk k → ℝ), (∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k)) →
    ∀ (ψ : ∀ k, ℝ → Ωk k → ℓ²(ℤ, ℂ)), (∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k)) →
    ∀ (Zv : ∀ k, Ωk k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t) →
    ∀ {Ω : Type v} {_ : MeasurableSpace Ω} {Pr : Measure Ω} [IsProbabilityMeasure Pr]
      {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}, Measurable Y →
      TendstoInDistribution Zv atTop Y μ Pr → ∀ {ε : ℝ}, 0 < ε →
      Measurable (fun p : Ω × ℝ => ENNReal.ofReal
        (smoothedNormSq (pathAt (Y p.1) p.2 : Measure ℝ) (fun _ => 1) ρ ε)) ∧
      ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (smoothedNormSq (pathAt (Y ω) t : Measure ℝ) (fun _ => 1) ρ ε)) ∂Pr ≤
        ENNReal.ofReal (C * 2 ^ (16 * T)) := by
  obtain ⟨C, hC⟩ := pathPrelim_eq_6_2.{u} hρ
  refine ⟨C, ?_⟩
  intro T hT n hn₁ hn Ωk mΩk μ _ 𝓕 B hB ψ hψ Zv hZv Ω _ Pr _ Y hY hconv ε hε
  have hmeas1 := limPt_measurable_smoothedNormSq hρ (T := T) hε
  have hmeas2 : Measurable fun p : Ω × ℝ => (Y p.1, p.2) := hY.prodMap measurable_id
  refine ⟨(hmeas1.comp hmeas2 :), ?_⟩
  -- the laws `P_k` of the versions, and the limit law
  set P : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
    fun k => ⟨(μ k).map (Zv k), inferInstance⟩ with hPdef
  have hPP : ∀ k, IsPathPrelimLaw.{u} T (n k) (P k : Measure _) := fun k =>
    ⟨Ωk k, mΩk k, μ k, 𝓕 k, B k, ψ k, Zv k, inferInstance, hB k, hψ k,
      hconv.forall_aemeasurable k, hZv k, rfl⟩
  -- `ε_k' = max(⌊ε n_k^{1/2}⌋ n_k^{-1/2}, ε/2) → ε`
  obtain ⟨hεs, hm1⟩ := limPt_tendsto_epsN hn hε
  set εs : ℕ → ℝ := fun k => (⌊ε * n k ^ (1 / 2 : ℝ)⌋₊ : ℝ) * n k ^ (-1 / 2 : ℝ) with hεsdef
  set εs' : ℕ → ℝ := fun k => max (εs k) (ε / 2) with hεs'def
  have hε2 : 0 < ε / 2 := half_pos hε
  have hεs' : Tendsto εs' atTop (𝓝 ε) := by
    have h := hεs.max (tendsto_const_nhds (x := ε / 2))
    rwa [max_eq_left (by linarith : ε / 2 ≤ ε)] at h
  set F : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ≥0∞ := fun e γ =>
    ∫⁻ t in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (smoothedNormSq (pathAt γ t : Measure ℝ) (fun _ => 1) ρ e) with hFdef
  have hFm : ∀ e, 0 < e → Measurable (F e) := fun e he =>
    (limPt_measurable_smoothedNormSq hρ he).lintegral_prod_right'
  have key := limPt_lintegral_le_of_tendsto hconv.tendsto (G := fun k => F (εs' k)) (G₀ := F ε)
    (fun k => hFm _ (lt_max_of_lt_right hε2)) (hFm ε hε) ?lsc
    (c := ENNReal.ofReal (C * 2 ^ (16 * T))) ?bound
  case lsc =>
    intro φ hφ γs γ hγ
    have hmt : ∀ e, 0 < e → ∀ γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable fun t =>
        ENNReal.ofReal (smoothedNormSq (pathAt γ' t : Measure ℝ) (fun _ => 1) ρ e) :=
      fun e he γ' =>
        ((limPt_measurable_smoothedNormSq hρ (T := T) he).comp measurable_prodMk_left :)
    calc F ε γ ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, liminf (fun k => ENNReal.ofReal
          (smoothedNormSq (pathAt (γs k) t : Measure ℝ) (fun _ => 1) ρ (εs' (φ k)))) atTop := by
          refine lintegral_mono fun t => ?_
          have h := (ENNReal.continuous_ofReal.tendsto _).comp
            (limPt_tendsto_smoothedNormSq hρ hε hγ (hεs'.comp hφ) t)
          exact h.liminf_eq.ge
      _ ≤ liminf (fun k => F (εs' (φ k)) (γs k)) atTop :=
          lintegral_liminf_le fun k => hmt _ (lt_max_of_lt_right hε2) _
  case bound =>
    filter_upwards [hm1, hεs.eventually (lt_mem_nhds (half_lt_self hε))] with k hk hk2
    have heq : εs' k = (⌊ε * n k ^ (1 / 2 : ℝ)⌋₊ : ℝ) * n k ^ (-1 / 2 : ℝ) :=
      max_eq_left hk2.le
    simp only [heq, hFdef]
    exact ((hC (hPP k) (hn₁ k) hT _ hk).2 :)
  calc ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (smoothedNormSq (pathAt (Y ω) t : Measure ℝ) (fun _ => 1) ρ ε)) ∂Pr
      = ∫⁻ γ, F ε γ ∂(Pr.map Y) := (lintegral_map (hFm ε hε) hY).symm
    _ ≤ _ := key

/-- Proposition 7.1 (1) and (2), with the universes named (proof of `limPt_dirac_density`). -/
private theorem prop71Dens_dirac_density_aux {Ω : Type v} {mΩ : MeasurableSpace Ω}
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T : ℝ} (hT : 0 < T)
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ωk : ℕ → Type u} {mΩk : ∀ k, MeasurableSpace (Ωk k)}
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
          volume.withDensity fun x => ENNReal.ofReal (limField ρ Y t x ω)) := by
  refine ⟨?_, measurable_limField_predictable hρ hY, fun t x ω => limDensity_nonneg ρ _ x, ?_⟩
  · -- (1): portmanteau for the closed set `A = {γ : γ(0) = δ₀}`, through Fatou's lemma for
    -- the indicator of the open set `Aᶜ`
    set μ₀ : FiniteMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩ with hμ₀
    set A : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) := (fun γ => pathAt γ 0) ⁻¹' {μ₀} with hA
    have hAc : IsClosed A := isClosed_singleton.preimage
      (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))
    have hAm : MeasurableSet A := hAc.measurableSet
    have hmemA : ∀ γ, γ ∈ A ↔ (pathAt γ 0 : Measure ℝ) = Measure.dirac 0 := fun γ => by
      simp only [hA, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => by rw [h]; rfl, fun h => FiniteMeasure.toMeasure_injective (by rw [h]; rfl)⟩
    set P : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
      fun k => ⟨(μ k).map (Zv k), inferInstance⟩ with hPdef
    have hPP : ∀ k, IsPathPrelimLaw.{u} T (n k) (P k : Measure _) := fun k =>
      ⟨Ωk k, mΩk k, μ k, 𝓕 k, B k, ψ k, Zv k, inferInstance, hB k, hψ k,
        hconv.forall_aemeasurable k, hZv k, rfl⟩
    have key := limPt_lintegral_le_of_tendsto hconv.tendsto (G := fun _ => Aᶜ.indicator 1)
      (G₀ := Aᶜ.indicator 1) (fun _ => measurable_one.indicator hAm.compl)
      (measurable_one.indicator hAm.compl) ?lsc (c := 0) ?bound
    case lsc =>
      intro φ _ γs γ hγ
      by_cases hγA : γ ∈ Aᶜ
      · rw [Set.indicator_of_mem hγA]
        refine le_liminf_of_le (by isBoundedDefault) ?_
        filter_upwards [hγ.eventually (hAc.isOpen_compl.mem_nhds hγA)] with k hk
        rw [Set.indicator_of_mem hk]
        exact le_rfl
      · rw [Set.indicator_of_notMem hγA]
        exact zero_le
    case bound =>
      refine Eventually.of_forall fun k => ?_
      rw [lintegral_indicator_one hAm.compl]
      refine le_of_eq ?_
      have h := (hPP k).ae_dirac (hn₁ k) hT.le
      exact ae_iff.1 (h.mono fun γ hγ => (hmemA γ).2 hγ)
    rw [lintegral_indicator_one hAm.compl, nonpos_iff_eq_zero] at key
    have hae : ∀ᵐ γ ∂(Pr.map Y), γ ∈ A := ae_iff.2 key
    exact (ae_of_ae_map hY.aemeasurable hae).mono fun ω hω => (hmemA _).1 hω
  · -- (2): Fatou's lemma twice, with (7.4) for `ε = 1/(k+1)`
    obtain ⟨C, hC⟩ := prop71Dens_eq_7_4_aux.{u, v} hρ
    have h74 := fun k : ℕ => hC hT n hn₁ hn μ 𝓕 B hB ψ hψ Zv hZv hY hconv
      (ε := 1 / ((k : ℝ) + 1)) (by positivity)
    set f : ℕ → Ω × ℝ → ℝ≥0∞ := fun k p => ENNReal.ofReal
      (smoothedNormSq (pathAt (Y p.1) p.2 : Measure ℝ) (fun _ => 1) ρ (1 / ((k : ℝ) + 1)))
      with hfdef
    have hfm : ∀ k, Measurable (f k) := fun k => (h74 k).1
    set H : Ω × ℝ → ℝ≥0∞ := fun p => liminf (fun k => f k p) atTop with hHdef
    have hHm : Measurable H := Measurable.liminf hfm
    have hHint : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, H (ω, t)) ∂Pr ≤
        ENNReal.ofReal (C * 2 ^ (16 * T)) := by
      calc ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, H (ω, t)) ∂Pr
          ≤ ∫⁻ ω, liminf (fun k => ∫⁻ t in Set.Icc (0 : ℝ) T, f k (ω, t)) atTop ∂Pr :=
            lintegral_mono fun ω =>
              lintegral_liminf_le fun k => ((hfm k).comp measurable_prodMk_left :)
        _ ≤ liminf (fun k => ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, f k (ω, t)) ∂Pr) atTop :=
            lintegral_liminf_le fun k => (hfm k).lintegral_prod_right'
        _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall fun k => (h74 k).2)
    have hfin : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, H (ω, t)) ∂Pr ≠ ⊤ :=
      (hHint.trans_lt ENNReal.ofReal_lt_top).ne
    refine ⟨?_, ?_⟩
    · -- (7.1)
      refine lt_of_le_of_lt ?_ (hHint.trans_lt ENNReal.ofReal_lt_top)
      exact lintegral_mono fun ω => lintegral_mono fun t =>
        lintegral_limDensity_sq_le hρ (pathAt (Y ω) t)
    · -- the density
      filter_upwards [ae_lt_top hHm.lintegral_prod_right' hfin] with ω hω
      filter_upwards [ae_lt_top (hHm.comp measurable_prodMk_left :) hω.ne] with t ht
      obtain ⟨C', hC'⟩ := limPt_bound_of_liminf hρ (μ := pathAt (Y ω) t) ht
      exact (withDensity_limDensity_of_bound hρ hC').2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- (7.4) (same statement as `eq_7_4`). -/
theorem limPt_eq_7_4 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
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
  prop71Dens_eq_7_4_aux hρ

/-- **Proposition 7.1 (1) and (2)** (the first two conjuncts of `prop_7_1`, same hypotheses). -/
theorem limPt_dirac_density {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T : ℝ} (hT : 0 < T)
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
          volume.withDensity fun x => ENNReal.ofReal (limField ρ Y t x ω)) :=
  prop71Dens_dirac_density_aux hρ hT n hn₁ hn μ 𝓕 B hB ψ hψ Zv hZv hY hconv

end QSSEPtoKPZ
