/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.MMBracket

/-!
# Limits of martingale-measure integrals (task G8a, auxiliary)

The `limit` rule of `IsMMIntegral`: integrands `h_k → h` for the energy
`𝔼 ∫_0^T ∫ (h_k - h)² q`, processes `X_k → X` in `L²(ℙ; sup_{r ∈ [0,T]})` (a lower integral),
with `X` continuous and almost everywhere strongly measurable at each time. Since each value
`X_k(t) - X(t)` is almost everywhere strongly measurable and dominated by the supremum,
`X_k(t) → X(t)` in `L²(ℙ)` for each `t ∈ [0, T]` (`mm_tendsto_sq_of_sup`); the martingale
property (`mm_isCL2Mart_limit`) and the covariation (`mm_hasCovariation_limit`) pass to the
limit in `L¹(ℙ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {T : ℝ}
  {q : ℝ → ℝ → Ω → ℝ}

/-- Convergence in `L²(ℙ; sup_{[0,T]})` gives convergence in `L²(ℙ)` at each time. -/
theorem mm_tendsto_sq_of_sup {Xs : ℕ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ}
    (hsup : Tendsto (fun k => ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ) atTop (𝓝 0)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    Tendsto (fun k => ∫⁻ ω, ‖Xs k t ω - X t ω‖ₑ ^ 2 ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsup (fun _ => zero_le)
    fun k => lintegral_mono fun ω => by
      rw [StochIntAux.enorm_sq_eq]
      exact le_iSup₂ (f := fun r _ => ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) t ht

/-- The limit is in `L²` at each time. -/
private lemma mm_memLp_limit {Xs : ℕ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ} {t : ℝ}
    (hXs : ∀ k, MemLp (Xs k t) 2 μ) (hm : AEStronglyMeasurable (X t) μ)
    (hL2 : Tendsto (fun k => ∫⁻ ω, ‖Xs k t ω - X t ω‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    MemLp (X t) 2 μ := by
  obtain ⟨k, hk⟩ := (hL2.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hd : MemLp (fun ω => Xs k t ω - X t ω) 2 μ :=
    StochIntAux.memLp_two_of_lintegral ((hXs k).aestronglyMeasurable.sub hm)
      (ne_top_of_lt (hk.trans ENNReal.one_lt_top))
  have := (hXs k).sub hd
  refine this.ae_eq (ae_of_all _ fun ω => ?_)
  simp

/-- **Martingale property of the limit.** -/
theorem mm_isCL2Mart_limit [IsFiniteMeasure μ] {Xs : ℕ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ}
    (hXs : ∀ k, IsCL2Mart T 𝒢 (Xs k) μ) (hc : ∀ ω, ContinuousOn (fun r => X r ω) (Set.Icc 0 T))
    (hm : ∀ r ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (X r) μ)
    (hsup : Tendsto (fun k => ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ) atTop (𝓝 0)) :
    IsCL2Mart T 𝒢 X μ := by
  have hmem : ∀ t : ℝ≥0, (t : ℝ) ≤ T → MemLp (X t) 2 μ := fun t ht =>
    mm_memLp_limit (fun k => (hXs k).memLp t ht) (hm t ⟨t.2, ht⟩)
      (mm_tendsto_sq_of_sup hsup ⟨t.2, ht⟩)
  have hL1 : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      Tendsto (fun k => ∫⁻ ω, ‖Xs k t ω - X t ω‖ₑ ∂μ) atTop (𝓝 0) := fun t ht =>
    StochIntAux.tendsto_lintegral_enorm_of_sq
      (fun k => ((hXs k).memLp t ht).aestronglyMeasurable.aemeasurable.sub
        (hm t ⟨t.2, ht⟩).aemeasurable)
      (mm_tendsto_sq_of_sup hsup ⟨t.2, ht⟩)
  refine ⟨ae_of_all _ hc, hmem, fun s t hst ht => ?_⟩
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  exact StochIntAux.condExp_ae_eq_of_tendsto s
    (fun k => ((hXs k).memLp t ht).integrable one_le_two) ((hmem t ht).integrable one_le_two)
    (hm s ⟨s.2, hs⟩) (fun k => (hXs k).condExp s t hst ht) (hL1 t ht) (hL1 s hs)

/-- The limit vanishes at time `0` if the approximations do (`T ≥ 0`). -/
theorem mm_ae_zero_limit (hT : 0 ≤ T) {Xs : ℕ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ}
    (h0 : ∀ k, Xs k 0 =ᵐ[μ] 0) (hm : AEStronglyMeasurable (X 0) μ)
    (hsup : Tendsto (fun k => ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ) atTop (𝓝 0)) :
    X 0 =ᵐ[μ] 0 := by
  have hL2 := mm_tendsto_sq_of_sup hsup ⟨le_rfl, hT⟩
  have hc : ∀ k, ∫⁻ ω, ‖Xs k 0 ω - X 0 ω‖ₑ ^ 2 ∂μ = ∫⁻ ω, ‖X 0 ω‖ₑ ^ 2 ∂μ := fun k =>
    lintegral_congr_ae ((h0 k).mono fun ω hω => by simp [hω])
  simp only [hc] at hL2
  have h := tendsto_nhds_unique tendsto_const_nhds hL2
  rw [lintegral_eq_zero_iff' (hm.aemeasurable.enorm.pow_const 2)] at h
  filter_upwards [h] with ω hω
  simpa using hω

/-- **Covariation of the limit**: if `⟨X_k, Y⟩ = ∫_0^· ∫ q h_k g` for every `k`, `h_k → h` for
the energy, and `X_k → X` in `L²(ℙ; sup_{[0,T]})`, then `⟨X, Y⟩ = ∫_0^· ∫ q h g`. -/
theorem mm_hasCovariation_limit [IsFiniteMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω) {Y : ℝ → Ω → ℝ} {g : ℝ → ℝ → Ω → ℝ} (hg : MMPred 𝒢 g)
    (hEg : mmEnergy μ T q g ≠ ∞) {hs : ℕ → ℝ → ℝ → Ω → ℝ} {Xs : ℕ → ℝ → Ω → ℝ}
    {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ}
    (hk : ∀ k, HasCovariation T 𝒢 (Xs k) Y (mmBr q (hs k) g) μ) (hhs : ∀ k, MMPred 𝒢 (hs k))
    (hEs : ∀ k, mmEnergy μ T q (hs k) ≠ ∞) (hh : MMPred 𝒢 h) (hEh : mmEnergy μ T q h ≠ ∞)
    (hlim : Tendsto (fun k => mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω)) atTop (𝓝 0))
    (hc : ∀ ω, ContinuousOn (fun r => X r ω) (Set.Icc 0 T))
    (hm : ∀ r ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (X r) μ)
    (hsup : Tendsto (fun k => ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ) atTop (𝓝 0)) :
    HasCovariation T 𝒢 X Y (mmBr q h g) μ := by
  have hX := mm_isCL2Mart_limit (fun k => (hk k).left) hc hm hsup
  have hY := (hk 0).right
  have hgood := mmBr_ae_good hT hq hq0 hh hg hEh hEg
  refine ⟨hX, hY, fun t ht => integrable_mmBr hq hq0 hh hg hEh hEg ⟨t.2, ht⟩,
    ae_of_all _ fun ω => by simp [mmBr], hgood.mono fun ω h => h.1, hgood.mono fun ω h => h.2,
    fun s t hst ht => ?_⟩
  have hsT : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  -- `L¹` convergence of `X_k Y - ∫ q h_k g` at the times `u ∈ [0, T]`
  have hconv : ∀ u : ℝ≥0, (u : ℝ) ≤ T → Tendsto (fun k => ∫⁻ ω,
      ‖(Xs k u ω * Y u ω - mmBr q (hs k) g u ω) - (X u ω * Y u ω - mmBr q h g u ω)‖ₑ ∂μ)
      atTop (𝓝 0) := by
    intro u hu
    have hu' : (u : ℝ) ∈ Set.Icc 0 T := ⟨u.2, hu⟩
    have h1 : Tendsto (fun k => ∫⁻ ω, ‖Xs k u ω * Y u ω - X u ω * Y u ω‖ₑ ∂μ) atTop (𝓝 0) :=
      StochIntAux.tendsto_lintegral_mul_sub
        (fun k => ((hk k).left.memLp u hu).aestronglyMeasurable.aemeasurable)
        (fun _ => (hY.memLp u hu).aestronglyMeasurable.aemeasurable)
        (hX.memLp u hu).aestronglyMeasurable.aemeasurable
        (hY.memLp u hu).aestronglyMeasurable.aemeasurable
        (StochIntAux.lintegral_sq_ne_top (hX.memLp u hu))
        (StochIntAux.lintegral_sq_ne_top (hY.memLp u hu))
        (mm_tendsto_sq_of_sup hsup hu') (by simp)
    have h2 := tendsto_mmBr_sub hq hq0 hhs hh hg hEs hEh hEg hlim hu'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using h1.add h2) (fun _ => zero_le) fun k => ?_
    calc ∫⁻ ω, ‖(Xs k u ω * Y u ω - mmBr q (hs k) g u ω) -
          (X u ω * Y u ω - mmBr q h g u ω)‖ₑ ∂μ
        ≤ ∫⁻ ω, (‖Xs k u ω * Y u ω - X u ω * Y u ω‖ₑ +
            ‖mmBr q (hs k) g u ω - mmBr q h g u ω‖ₑ) ∂μ := by
          refine lintegral_mono fun ω => le_trans (le_of_eq ?_) enorm_sub_le
          congr 1; ring
      _ = _ := lintegral_add_left' ((((hk k).left.memLp u hu).aestronglyMeasurable.mul
          (hY.memLp u hu).aestronglyMeasurable).sub ((hX.memLp u hu).aestronglyMeasurable.mul
          (hY.memLp u hu).aestronglyMeasurable)).aemeasurable.enorm _
  have hint : ∀ u : ℝ≥0, (u : ℝ) ≤ T → Integrable (fun ω => X u ω * Y u ω - mmBr q h g u ω) μ :=
    fun u hu => ((hX.memLp u hu).integrable_mul (hY.memLp u hu)).sub
      (integrable_mmBr hq hq0 hh hg hEh hEg ⟨u.2, hu⟩)
  exact StochIntAux.condExp_ae_eq_of_tendsto s
    (fun k => (((hk k).left.memLp t ht).integrable_mul (hY.memLp t ht)).sub
      ((hk k).integrable_cov t ht)) (hint t ht) (hint s hsT).aestronglyMeasurable
    (fun k => (hk k).condExp_mul s t hst ht) (hconv t ht) (hconv s hsT)

/-- The limit integrand has finite energy. -/
theorem mmEnergy_ne_top_of_tendsto [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {hs : ℕ → ℝ → ℝ → Ω → ℝ} {h : ℝ → ℝ → Ω → ℝ} (hhs : ∀ k, MMPred 𝒢 (hs k))
    (hh : MMPred 𝒢 h) (hEs : ∀ k, mmEnergy μ T q (hs k) ≠ ∞)
    (hlim : Tendsto (fun k => mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω)) atTop
      (𝓝 0)) : mmEnergy μ T q h ≠ ∞ := by
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have := mmEnergy_lincomb_le (μ := μ) (T := T) hq hq0 (hhs k) ((hhs k).sub hh) 1 (-1)
  have e : (fun r x ω => 1 * hs k r x ω + -1 * (hs k r x ω - h r x ω)) = h := by
    funext r x ω; ring
  rw [e] at this
  refine ne_top_of_le_ne_top ?_ this
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hEs k),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_lt (hk.trans ENNReal.one_lt_top))⟩

end QSSEPtoKPZ
