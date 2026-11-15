/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71BracketPre

/-!
# Proposition 7.1 (3): the stopped identity in the limit (task Q4)

Along the Skorokhod coupling (`IsLimCoupling`), with a further subsequence along which (7.6)
holds almost surely (`limBr_exists_subseq`), and at a level `L` where the hitting times of the
limit level process `V = max(Q, (M^φ)²)` at and above `L` almost surely agree, the stopped
prelimit identity (`limBr_prelim_integral`) passes to the limit by dominated convergence (the
stopped quantities are bounded by `L`): `limBr_stopped_limit`,
`𝔼[Θ(𝒵) ((M^φ(t∧σ^L)² - Q(t∧σ^L)) - (M^φ(s∧σ^L)² - Q(s∧σ^L)))] = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Interval

noncomputable section

namespace QSSEPtoKPZ

universe u

variable {T : ℝ}

/-- **A subsequence along which convergence in probability of paths, uniformly on `S`, becomes
almost sure** (Borel–Cantelli, with outer measures). -/
theorem limBr_exists_subseq {Ω : Type*} {mΩ : MeasurableSpace Ω} {Pr : Measure Ω}
    {f : ℕ → ℝ → Ω → ℝ} {g : ℝ → Ω → ℝ} {S : Set ℝ}
    (h : ∀ η : ℝ, 0 < η →
      Tendsto (fun j => Pr {ω | ∃ t ∈ S, η < |f j t ω - g t ω|}) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, Tendsto ψ atTop atTop ∧
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun k t => f (ψ k) t ω) (fun t => g t ω) atTop S := by
  have hN : ∀ k : ℕ, ∃ N, ∀ j ≥ N, Pr {ω | ∃ t ∈ S, (1 / 2 : ℝ) ^ k < |f j t ω - g t ω|} ≤
      (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    eventually_atTop.1 ((h _ (by positivity)).eventually
      (ge_mem_nhds (ENNReal.pow_pos (by norm_num) k)))
  choose N hN using hN
  refine ⟨fun k => max (N k) k, tendsto_atTop_mono (fun k => le_max_right _ _) tendsto_id, ?_⟩
  have hsum : ∑' k, Pr {ω | ∃ t ∈ S, (1 / 2 : ℝ) ^ k < |f (max (N k) k) t ω - g t ω|} ≠ ⊤ :=
    ne_top_of_le_ne_top (tsum_geometric_lt_top.2 (by norm_num)).ne
      (ENNReal.tsum_le_tsum fun k => hN k _ (le_max_left _ _))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [hω, eventually_ge_atTop K] with k hk hKk t ht
  simp only [not_exists, not_and, not_lt] at hk
  rw [Real.dist_eq, abs_sub_comm]
  calc |f (max (N k) k) t ω - g t ω| ≤ (1 / 2) ^ k := hk t ht
    _ ≤ (1 / 2) ^ K := pow_le_pow_of_le_one (by norm_num) (by norm_num) hKk
    _ < ε := hK

/-- Uniform convergence of `max(q_k, m_k²)` from that of `q_k` and `m_k`, the limit `m` being
continuous on a compact set. -/
theorem limBr_tendstoUniformlyOn_max_sq {q m : ℕ → ℝ → ℝ} {q0 m0 : ℝ → ℝ} {S : Set ℝ}
    (hS : IsCompact S) (hq : TendstoUniformlyOn q q0 atTop S)
    (hm : TendstoUniformlyOn m m0 atTop S) (hm0 : ContinuousOn m0 S) :
    TendstoUniformlyOn (fun k t => max (q k t) (m k t ^ 2)) (fun t => max (q0 t) (m0 t ^ 2))
      atTop S := by
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn hm0
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  rw [Metric.tendstoUniformlyOn_iff] at hq hm ⊢
  intro ε hε
  have hδ : 0 < min 1 (ε / (2 * R' + 2)) := lt_min one_pos (by positivity)
  filter_upwards [hq ε hε, hm _ hδ] with k h1 h2 t ht
  have a1 := h1 t ht
  have a2 := h2 t ht
  rw [Real.dist_eq] at a1 a2 ⊢
  refine (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt a1 ?_)
  have hR0 : |m0 t| ≤ R' := by
    have := hR t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have e : m0 t ^ 2 - m k t ^ 2 = (m0 t - m k t) * (m0 t + m k t) := by ring
  have a3 : |m0 t - m k t| ≤ 1 := a2.le.trans (min_le_left _ _)
  have hsum : |m0 t + m k t| ≤ 2 * R' + 1 := by
    calc |m0 t + m k t| = |2 * m0 t - (m0 t - m k t)| := by ring_nf
      _ ≤ |2 * m0 t| + |m0 t - m k t| := abs_sub _ _
      _ ≤ 2 * R' + 1 := by
          rw [abs_mul, abs_two]
          linarith
  rw [e, abs_mul]
  calc |m0 t - m k t| * |m0 t + m k t| ≤ min 1 (ε / (2 * R' + 2)) * (2 * R' + 1) :=
        mul_le_mul a2.le hsum (abs_nonneg _) hδ.le
    _ ≤ ε / (2 * R' + 2) * (2 * R' + 1) := by
        gcongr
        exact min_le_right _ _
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- Convergence of the stopped increments, from uniform convergence of the processes and
convergence of the stopping times. -/
theorem limBrInc_tendsto {Mk Ak : ℕ → ℝ → ℝ} {M A : ℝ → ℝ} {σk : ℕ → ℝ} {σ s t : ℝ}
    (hM : TendstoUniformlyOn Mk M atTop (Icc 0 T)) (hA : TendstoUniformlyOn Ak A atTop (Icc 0 T))
    (hMc : ContinuousOn M (Icc 0 T)) (hAc : ContinuousOn A (Icc 0 T))
    (hσ : Tendsto σk atTop (𝓝 σ)) (hσk : ∀ k, σk k ∈ Icc 0 T) (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) :
    Tendsto (fun k => limBrInc (Mk k) (Ak k) s t (σk k)) atTop (𝓝 (limBrInc M A s t σ)) := by
  have hσI : σ ∈ Icc 0 T := isClosed_Icc.mem_of_tendsto hσ (Eventually.of_forall hσk)
  have hr : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun k => min r (σk k)) atTop (𝓝[Icc 0 T] (min r σ)) :=
    fun r hr => tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.min hσ,
      Eventually.of_forall fun k => ⟨le_min hr.1 (hσk k).1, (min_le_left _ _).trans hr.2⟩⟩
  have hmem : ∀ r ∈ Icc (0 : ℝ) T, min r σ ∈ Icc (0 : ℝ) T := fun r hr =>
    ⟨le_min hr.1 hσI.1, (min_le_left _ _).trans hr.2⟩
  have hMt := hM.tendsto_comp (hMc _ (hmem t ht)) (hr t ht)
  have hAt := hA.tendsto_comp (hAc _ (hmem t ht)) (hr t ht)
  have hMs := hM.tendsto_comp (hMc _ (hmem s hs)) (hr s hs)
  have hAs := hA.tendsto_comp (hAc _ (hmem s hs)) (hr s hs)
  exact ((hMt.pow 2).sub hAt).sub ((hMs.pow 2).sub hAs)

/-- `M_n^φ(0) = 0` when `γ(0) = δ₀`. -/
theorem limBr_MNpath_zero {n : ℝ} {φ φt : ℝ → ℝ → ℝ} {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (h : (pathAt γ 0 : Measure ℝ) = Measure.dirac 0) : MNpath n φ φt 0 γ = 0 := by
  simp [MNpath, pairFM, h]

/-- **The stopped prelimit quantities are bounded by the level**: if `M_n^φ(0) = 0` then, for
`r ≤ T` and `σ = hitTime V_n L T`, `M_n^φ(r∧σ)² ≤ L` and `0 ≤ Q_n(r∧σ) ≤ L`. -/
private lemma limBr_pre_bound {n C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    (hT : 0 ≤ T) {L : ℝ} (hL : 0 ≤ L) {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (h0 : MNpath n φ φt 0 γ = 0) {r : ℝ≥0} (hr : (r : ℝ) ≤ T) :
    MNpath n φ φt (min (r : ℝ) (hitTime (limBrPreV n φ φt) L ⟨T, hT⟩ γ)) γ ^ 2 ≤ L ∧
      0 ≤ QNpath n φ (min (r : ℝ) (hitTime (limBrPreV n φ φt) L ⟨T, hT⟩ γ)) γ ∧
      QNpath n φ (min (r : ℝ) (hitTime (limBrPreV n φ φt) L ⟨T, hT⟩ γ)) γ ≤ L := by
  set τ := hitTime (limBrPreV n φ φt) L ⟨T, hT⟩ γ
  have hQ0 : QNpath n φ 0 γ = 0 := by simp [QNpath]
  have hV0 : limBrPreV n φ φt ((0 : ℝ≥0) : ℝ) γ ≤ L := by
    simp only [limBrPreV, NNReal.coe_zero, pathFunClamp_of_mem (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Icc 0 T),
      hQ0, h0]
    simpa using hL
  have hV := le_of_le_hitTime (limBr_continuous_preV hT hn hφ γ) hV0
    (min_le_right r τ : min r τ ≤ τ)
  have hmem : ((min r τ : ℝ≥0) : ℝ) ∈ Icc 0 T :=
    ⟨NNReal.coe_nonneg _, (NNReal.coe_le_coe.2 (min_le_left _ _)).trans hr⟩
  rw [limBrPreV, pathFunClamp_of_mem hmem, max_le_iff, NNReal.coe_min] at hV
  refine ⟨hV.2, ?_, hV.1⟩
  rw [← hQ0]
  have hmem' : min (r : ℝ) (τ : ℝ) ∈ Icc 0 T := by rwa [NNReal.coe_min] at hmem
  exact (continuousOn_monotoneOn_QNpath hn hφ γ).2 ⟨le_rfl, hT⟩ hmem' hmem'.1

/-- **The stopped identity in the limit** (proof of Proposition 7.1 (3), localization D3″). -/
theorem limBr_stopped_limit {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs}
    {n : ℕ → ℝ} {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    (hT : 0 ≤ T) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {C : ℝ} {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop)
    (hQ : ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun k t => QNpath (n (ψ k)) φ t (X (ψ k) ω))
      (fun t => limBracket (limField ρ Xl) φ t ω) atTop (Icc 0 T))
    (hG : ∀ᵐ ω ∂Pr, Xl ω ∈ limBrGood ρ T) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : Pr {ω | hitTime (fun u ω => limBrLimV ρ φ φt u (Xl ω)) L ⟨T, hT⟩ ω ≠
      hitTimeStrict (fun u ω => limBrLimV ρ φ φt u (Xl ω)) L ⟨T, hT⟩ ω} = 0)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ) ≤ T)
    {Θ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ} (hΘc : Continuous Θ)
    (hΘ : Measurable[pathFiltrationCan T s] Θ) {B : ℝ} (hB : ∀ γ, |Θ γ| ≤ B) :
    AEStronglyMeasurable (fun ω => Θ (Xl ω) *
      limBrInc (fun r => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt r
        (Xl ω)) (fun r => limBrMod ρ φ r (Xl ω)) s t
        (hitTime (fun u ω => limBrLimV ρ φ φt u (Xl ω)) L ⟨T, hT⟩ ω)) Pr ∧
    ∫ ω, Θ (Xl ω) *
      limBrInc (fun r => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt r
        (Xl ω)) (fun r => limBrMod ρ φ r (Xl ω)) s t
        (hitTime (fun u ω => limBrLimV ρ φ φt u (Xl ω)) L ⟨T, hT⟩ ω) ∂Pr = 0 := by
  have hPr := hc.isProbabilityMeasure
  have hTp := hc.pos
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  set T' : ℝ≥0 := ⟨T, hT⟩ with hT'
  -- the prelimit integrands, along the subsequence
  set F : ℕ → Ωs → ℝ := fun k ω => Θ (X (ψ k) ω) *
    limBrInc (fun r => MNpath (n (ψ k)) φ φt r (X (ψ k) ω))
      (fun r => QNpath (n (ψ k)) φ r (X (ψ k) ω)) s t
      (hitTime (limBrPreV (n (ψ k)) φ φt) L T' (X (ψ k) ω)) with hF
  have hpre := fun k => limBr_prelim_integral (hc.law (ψ k)) (hc.one_le (ψ k)) hTp hφ L hst ht
    hΘ hB
  have hFm : ∀ k, AEStronglyMeasurable (F k) Pr := fun k =>
    (hpre k).1.aestronglyMeasurable.comp_aemeasurable (hc.measurable (ψ k)).aemeasurable
  have hF0 : ∀ k, ∫ ω, F k ω ∂Pr = 0 := fun k =>
    (integral_map (hc.measurable (ψ k)).aemeasurable (hpre k).1.aestronglyMeasurable).symm.trans
      (hpre k).2
  -- the bound `|F_k| ≤ 4 B L`
  have hbound : ∀ k, ∀ᵐ ω ∂Pr, ‖F k ω‖ ≤ B * (4 * L) := by
    intro k
    filter_upwards [ae_of_ae_map (hc.measurable (ψ k)).aemeasurable
      ((hc.law (ψ k)).ae_dirac (hc.one_le (ψ k)) hT)] with ω hω
    have h0 := limBr_MNpath_zero (n := n (ψ k)) (φ := φ) (φt := φt) hω
    obtain ⟨a1, a2, a3⟩ := limBr_pre_bound (hc.one_le (ψ k)) hφ hT hL0 h0 ht
    obtain ⟨b1, b2, b3⟩ := limBr_pre_bound (hc.one_le (ψ k)) hφ hT hL0 h0 hs
    have hinc : |limBrInc (fun r => MNpath (n (ψ k)) φ φt r (X (ψ k) ω))
        (fun r => QNpath (n (ψ k)) φ r (X (ψ k) ω)) s t
        (hitTime (limBrPreV (n (ψ k)) φ φt) L T' (X (ψ k) ω))| ≤ 4 * L := by
      simp only [limBrInc]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (MNpath (n (ψ k)) φ φt (min (t : ℝ)
        (hitTime (limBrPreV (n (ψ k)) φ φt) L T' (X (ψ k) ω))) (X (ψ k) ω)),
        sq_nonneg (MNpath (n (ψ k)) φ φt (min (s : ℝ)
        (hitTime (limBrPreV (n (ψ k)) φ φt) L T' (X (ψ k) ω))) (X (ψ k) ω))]
    rw [hF, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB _) hinc (abs_nonneg _) ((abs_nonneg _).trans (hB (X (ψ k) ω)))
  -- almost sure convergence
  have hconv : ∀ᵐ ω ∂Pr, Tendsto (fun k => F k ω) atTop (𝓝 (Θ (Xl ω) *
      limBrInc (fun r => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt r
        (Xl ω)) (fun r => limBrMod ρ φ r (Xl ω)) s t
        (hitTime (fun u ω => limBrLimV ρ φ φt u (Xl ω)) L ⟨T, hT⟩ ω))) := by
    filter_upwards [hc.tendsto, hQ, hG, ae_iff.2 hL] with ω hX hq hg hhit
    have hXψ : Tendsto (fun k => X (ψ k) ω) atTop (𝓝 (Xl ω)) := hX.comp hψ
    have hMu := tendstoUniformlyOn_MNpath hφ (fun k => hc.one_le (ψ k))
      (hc.tendsto_atTop.comp hψ) hXψ
    have hAu : TendstoUniformlyOn (fun k r => QNpath (n (ψ k)) φ r (X (ψ k) ω))
        (fun r => limBrMod ρ φ r (Xl ω)) atTop (Icc 0 T) :=
      hq.congr_right fun r _ => (indicator_of_mem hg
        (limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ r)).symm
    have hMc := limMart_continuousOn hφ (Xl ω)
    have hAc := (limBrMod_props hφ hρ (Xl ω)).1
    have hVu : TendstoUniformlyOn (fun k r => limBrPreV (n (ψ k)) φ φt r (X (ψ k) ω))
        (fun r => limBrLimV ρ φ φt r (Xl ω)) atTop (Icc 0 T) :=
      ((limBr_tendstoUniformlyOn_max_sq isCompact_Icc hAu hMu hMc).congr
        (Eventually.of_forall fun k r hr => by
          simp only [limBrPreV, pathFunClamp_of_mem hr])).congr_right
        fun r hr => by simp only [limBrLimV, pathFunClamp_of_mem hr]
    have hVc : ContinuousOn (fun r => limBrLimV ρ φ φt r (Xl ω)) (Icc 0 T) :=
      (hAc.sup (hMc.pow 2)).congr fun r hr => by rw [limBrLimV, pathFunClamp_of_mem hr]; rfl
    have hσ := tendsto_hitTime (X := fun k u ω => limBrPreV (n (ψ k)) φ φt u (X (ψ k) ω))
      (Xl := fun u ω => limBrLimV ρ φ φt u (Xl ω)) (K := L) (T := T') hVc hVu hhit
    have hσr := (NNReal.continuous_coe.tendsto _).comp hσ
    have hinc := limBrInc_tendsto (s := s) (t := t) hMu hAu hMc hAc hσr
      (fun k => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (hitTime_le _ _ _ _)⟩)
      ⟨s.2, hs⟩ ⟨t.2, ht⟩
    exact ((hΘc.tendsto _).comp hXψ).mul hinc
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => B * (4 * L)) hFm
    (integrable_const _) hbound hconv
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hFm hconv, ?_⟩
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun k => (hF0 k).symm)

end QSSEPtoKPZ
