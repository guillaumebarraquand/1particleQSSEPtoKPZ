/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Assembly.PathMetric
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Slutsky's lemma for paths of measures, with varying probability spaces (task M1)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proof is task M1.
`docs/stage5-design.md`, Sections 1.2 (f), 3.5, decision D6‴ (replaces Billingsley's
Theorem 3.1 and the bounded Lipschitz distance of the article's proof of Theorem 1.2).

`tendstoInDistribution_of_close`: if `Y_k → Z` in distribution in `C([0,T], ℳ₊)`, `X_k` is
almost everywhere measurable, and for every `ε > 0` the outer probability that
`|X_k(t)(f) - Y_k(t)(f)| ≤ ε ‖f‖_∞` fails for some `t` and some bounded continuous `f` tends to
`0`, then `X_k → Z` in distribution. (Proof: `pathMetricDist` and the proof of Mathlib's
`tendstoInDistribution_of_tendstoInMeasure_sub` with bounded Lipschitz test functions,
`tendsto_iff_forall_lipschitz_integral_tendsto`, one probability space per `k`.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

/-! ### Slutsky's lemma in a pseudo-metric space, with outer probabilities -/

/-- A bounded continuous function of an almost everywhere measurable random variable is
integrable. -/
private theorem slutsky_integrable_comp {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → E} (hX : AEMeasurable X P) (F : E →ᵇ ℝ) :
    Integrable (fun ω => F (X ω)) P :=
  Integrable.of_bound (F.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable ‖F‖
    (ae_of_all _ fun _ => F.norm_coe_le_norm _)

/-- **One-step bound.** For `F` bounded and `L`-Lipschitz and `δ ≥ 0`,
`|E[F(X)] - E[F(Y)]| ≤ L δ + 2 ‖F‖_∞ P^*(d(X,Y) > δ)`, with the outer probability `P^*` (the set
`{d(X,Y) > δ}` need not be measurable; it is replaced by a measurable hull of the same measure). -/
private theorem slutsky_abs_integral_sub_le {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → E} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (F : E →ᵇ ℝ) {L : ℝ≥0} (hL : LipschitzWith L F) {δ : ℝ} (hδ : 0 ≤ δ) :
    |(∫ ω, F (X ω) ∂P) - ∫ ω, F (Y ω) ∂P| ≤
      L * δ + 2 * ‖F‖ * (P {ω | δ < dist (X ω) (Y ω)}).toReal := by
  set S := toMeasurable P {ω | δ < dist (X ω) (Y ω)}
  have hS : MeasurableSet S := measurableSet_toMeasurable _ _
  have hPS : P S = P {ω | δ < dist (X ω) (Y ω)} := measure_toMeasurable _
  have hg : Integrable (fun ω => (L : ℝ) * δ + S.indicator (fun _ => 2 * ‖F‖) ω) P :=
    (integrable_const _).add ((integrable_const _).indicator hS)
  rw [← integral_sub (slutsky_integrable_comp hX F) (slutsky_integrable_comp hY F),
    ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ fun ω => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, ← Real.dist_eq]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 := F.dist_le_two_norm (X ω) (Y ω)
      have : 0 ≤ (L : ℝ) * δ := by positivity
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hd : dist (X ω) (Y ω) ≤ δ := by
        by_contra h
        exact hω (subset_toMeasurable _ _ (not_le.1 h))
      exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  · rw [integral_add (integrable_const _) ((integrable_const _).indicator hS),
      integral_const, integral_indicator_const _ hS]
    simp [measureReal_def, hPS]
    ring

/-- **Slutsky's lemma, one probability space per `k`, outer probabilities.** Let `m` be a
pseudo-metric on `E` inducing its topology. If `Y_k → Z` in distribution, each `X_k` is almost
everywhere measurable, and `P_k^*(d(X_k, Y_k) > δ) → 0` for every `δ > 0`, then `X_k → Z` in
distribution. Proof: integrals of bounded Lipschitz functions
(`tendsto_iff_forall_lipschitz_integral_tendsto`) and `slutsky_abs_integral_sub_le`. -/
private theorem slutsky_of_pseudoMetric {E : Type*} [τ : TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (m : PseudoMetricSpace E)
    (hm : τ = m.toUniformSpace.toTopologicalSpace)
    {ι : ℕ → Type*} {mι : ∀ k, MeasurableSpace (ι k)}
    {P : ∀ k, Measure (ι k)} [∀ k, IsProbabilityMeasure (P k)]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X Y : ∀ k, ι k → E} {Z : Ω' → E}
    (hX : ∀ k, AEMeasurable (X k) (P k)) (hY : TendstoInDistribution Y atTop Z P ν)
    (hXY : ∀ δ > 0, Tendsto (fun k => P k {ω | δ < m.dist (X k ω) (Y k ω)}) atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z P ν := by
  subst hm
  let _ := m
  refine ⟨hX, hY.aemeasurable_limit, ?_⟩
  have hYt := tendsto_iff_forall_lipschitz_integral_tendsto.1 hY.tendsto
  refine tendsto_iff_forall_lipschitz_integral_tendsto.2 ?_
  rintro F ⟨M, hM⟩ ⟨L, hL⟩
  let G : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨F, hL.continuous⟩ M hM
  have hYF := hYt F ⟨M, hM⟩ ⟨L, hL⟩
  simp only [ProbabilityMeasure.coe_mk] at hYF ⊢
  have hmapX : ∀ k, ∫ x, F x ∂((P k).map (X k)) = ∫ ω, G (X k ω) ∂(P k) := fun k =>
    integral_map (hX k) G.continuous.aestronglyMeasurable
  have hmapY : ∀ k, ∫ x, F x ∂((P k).map (Y k)) = ∫ ω, G (Y k ω) ∂(P k) := fun k =>
    integral_map (hY.forall_aemeasurable k) G.continuous.aestronglyMeasurable
  simp_rw [hmapX]
  simp_rw [hmapY] at hYF
  rw [Metric.tendsto_atTop] at hYF ⊢
  intro η hη
  set δ : ℝ := η / (3 * (L + 1))
  have hδ : 0 < δ := by positivity
  have hLδ : (L : ℝ) * δ < η / 3 := by
    have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
    rw [show (L : ℝ) * δ = η / 3 * (L / (L + 1)) by simp only [δ]; field_simp]
    exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
  have hp := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hXY δ hδ)
  rw [ENNReal.toReal_zero, Metric.tendsto_atTop] at hp
  obtain ⟨N₁, hN₁⟩ := hp (η / 3 / (2 * ‖G‖ + 1)) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hYF (η / 3) (by positivity)
  refine ⟨max N₁ N₂, fun k hk => ?_⟩
  have h1 := slutsky_abs_integral_sub_le (hX k) (hY.forall_aemeasurable k) G hL hδ.le
  have h2 : dist (P k {ω | δ < dist (X k ω) (Y k ω)}).toReal 0 < η / 3 / (2 * ‖G‖ + 1) :=
    hN₁ k (le_of_max_le_left hk)
  have h3 := hN₂ k (le_of_max_le_right hk)
  set p := (P k {ω | δ < dist (X k ω) (Y k ω)}).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hp0, lt_div_iff₀ (by positivity)] at h2
  have h4 : 2 * ‖G‖ * p ≤ p * (2 * ‖G‖ + 1) := by nlinarith
  rw [Real.dist_eq] at h3 ⊢
  have h5 := abs_sub_le (∫ ω, G (X k ω) ∂(P k)) (∫ ω, G (Y k ω) ∂(P k))
    (∫ x, F x ∂(ν.map Z))
  linarith

/-! ### The path metric as a pseudo-metric space structure -/

/-- The embedding `γ ↦ (t ↦ (γ(t)(f_j))_j)` of `C([0,T], ℳ₊)` into `C([0,T], ℝ^ℕ)`. -/
private def pathMetricEmb (T : ℝ) :
    C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → C(Set.Icc (0 : ℝ) T, ℕ → ℝ) :=
  fun γ => (⟨tightEmb, continuous_tightEmb⟩ : C(FiniteMeasure ℝ, ℕ → ℝ)).comp γ

/-- The pseudo-metric on `C([0,T], ℳ₊)` pulled back by `pathMetricEmb` from the uniform metric
on `C([0,T], ℝ^ℕ)`, with the countable-product metric `PiCountable.pseudoMetricSpace` on `ℝ^ℕ`
(whose uniform structure is the product one). -/
@[instance_reducible]
private def pathMetricPMS (T : ℝ) : PseudoMetricSpace C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  letI : PseudoMetricSpace (ℕ → ℝ) := PiCountable.pseudoMetricSpace
  PseudoMetricSpace.induced (pathMetricEmb T) inferInstance

/-- The pseudo-metric `pathMetricPMS` induces the topology of `C([0,T], ℳ₊)`
(`isEmbedding_tightEmb`, `ContinuousMap.isEmbedding_postcomp`). -/
private theorem pathMetricPMS_topology (T : ℝ) :
    (inferInstance : TopologicalSpace C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) =
      (pathMetricPMS T).toUniformSpace.toTopologicalSpace :=
  (ContinuousMap.isEmbedding_postcomp _ isEmbedding_tightEmb).eq_induced

/-- `d(γ, γ') ≤ C` iff `∑_j min(2^{-j}, |γ(t)(f_j) - γ'(t)(f_j)|) ≤ C` for all `t`
(for `C ≥ 0`); thus `d = pathMetricDist`. -/
private theorem pathMetricPMS_dist_le_iff (T : ℝ) (γ γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    {C : ℝ} (hC : 0 ≤ C) :
    (pathMetricPMS T).dist γ γ' ≤ C ↔ ∀ t, (∑' j : ℕ, min ((1 / 2 : ℝ) ^ j)
      |(∫ x, bumpTest j x ∂(γ t : Measure ℝ)) - ∫ x, bumpTest j x ∂(γ' t : Measure ℝ)|) ≤ C := by
  let _ : PseudoMetricSpace (ℕ → ℝ) := PiCountable.pseudoMetricSpace
  change dist (pathMetricEmb T γ) (pathMetricEmb T γ') ≤ C ↔ _
  rw [ContinuousMap.dist_le hC]
  refine forall_congr' fun t => ?_
  change (∑' j : ℕ, min (2⁻¹ ^ Encodable.encode j)
    (dist (tightEmb (γ t) j) (tightEmb (γ' t) j))) ≤ C ↔ _
  simp [Encodable.encode_nat, Real.dist_eq, tightEmb, one_div]

/-- `∑_j min(2^{-j}, ε) → 0` as `ε → 0⁺` (dominated convergence for series). -/
private theorem pathMetric_tendsto_tsum_min :
    Tendsto (fun ε : ℝ => ∑' j : ℕ, min ((1 / 2 : ℝ) ^ j) ε) (𝓝[>] 0) (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun ε (j : ℕ) => min ((1 / 2 : ℝ) ^ j) ε) (g := fun j => min ((1 / 2 : ℝ) ^ j) 0)
    (bound := fun j => (1 / 2 : ℝ) ^ j) summable_geometric_two
    (fun j => ((continuous_const.min continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds) ?_
  · simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) j
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) hε.le)]
    exact min_le_left _ _

/-- **Slutsky for paths of measures, with varying probability spaces.** -/
theorem tendstoInDistribution_of_close {T : ℝ} {ι : ℕ → Type*} {mι : ∀ k, MeasurableSpace (ι k)}
    {P : ∀ k, Measure (ι k)} [∀ k, IsProbabilityMeasure (P k)]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X Y : ∀ k, ι k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Z : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hX : ∀ k, AEMeasurable (X k) (P k)) (hY : TendstoInDistribution Y atTop Z P ν)
    (hXY : ∀ ε > 0, Tendsto (fun k => P k {ω | ¬ ∀ (t : Set.Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
        |(∫ x, f x ∂(X k ω t : Measure ℝ)) - ∫ x, f x ∂(Y k ω t : Measure ℝ)| ≤ ε * ‖f‖})
      atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z P ν := by
  refine slutsky_of_pseudoMetric (pathMetricPMS T) (pathMetricPMS_topology T) hX hY
    fun δ hδ => ?_
  obtain ⟨ε, hεδ, hε⟩ := ((pathMetric_tendsto_tsum_min.eventually (gt_mem_nhds hδ)).and
    self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hXY ε hε)
    (fun _ => zero_le) fun k => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hgood
  refine (not_le.2 hω) (le_trans ?_ hεδ.le)
  exact (pathMetricPMS_dist_le_iff T _ _ (tsum_nonneg fun _ => le_min (by positivity) hε0)).2
    fun t => pathMetric_tsum_le_of_close hε0 (hgood t)

end QSSEPtoKPZ
