/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.ConvQ
public import QSSEPtoKPZ.LimitPoints.HitLevel
public import QSSEPtoKPZ.LimitPoints.Prop71BracketLim

/-!
# Proposition 7.1 (3): the bracket of `M^φ`, by localization (task Q4)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task Q4
(13 November 2026). See `docs/stage4-design.md`, Section 1.2 (d), decision D3″, and
`docs/stage4-interfaces.md`. Auxiliary files: `Prop71BracketAux.lean` (the bracket functional
on the path space, transfer), `Prop71BracketPre.lean` (the stopped prelimit identity),
`Prop71BracketLim.lean` (its limit at a good level `L`).

Localization at `σ^L = inf{t : max(⟨M_n^φ⟩_t, M_n^φ(t)²) ≥ L} ∧ T` instead of BDG
(`tendsto_hitTime`, `countable_hitTime_ne`, `HasBracket.stopped`); the stopped quantities are
bounded by `L`; along a further subsequence (7.6) holds almost surely; then
`(M^φ)² - Q` is a local martingale, and a true martingale since `𝔼[Q(T)] < ∞` by (7.1) and
`𝔼 sup_t M^φ(t)² ≤ 4 𝔼 M^φ(T)²` (Doob, `IsCL2Mart.lintegral_iSup_sq_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- (7.3) is integrable: `𝔼 Q(t) ≤ c² 𝔼 ∫_0^T ∫ Z² < ∞` by (7.1), for `t ∈ [0,T]`. -/
theorem limBr_integrable_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {Pr : Measure Ω} {T : ℝ}
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y) {ρ : ℝ → ℝ}
    (hρ : IsMollifier ρ) {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal (limField ρ Y t x ω ^ 2)) ∂Pr < ⊤) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    Integrable (fun ω => limBracket (limField ρ Y) φ t ω) Pr := by
  obtain ⟨c, hc⟩ := limBr_ofReal_le (ρ := ρ) hφ
  refine ⟨((limBr_measurable_bracket hφ hρ ht).comp hY).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => limBr_bracket_nonneg (Y ω) ht.1)).2 ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (limBracket (limField ρ Y) φ t ω) ∂Pr
      ≤ ∫⁻ ω, ENNReal.ofReal c * (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ x,
          ENNReal.ofReal (limDensity ρ (pathAt (Y ω) s) x ^ 2)) ∂Pr :=
        lintegral_mono fun ω => hc (Y ω) t ht
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZ2

/-- **The identity `𝔼[Θ(𝒵) ((M^φ(t)² - Q(t)) - (M^φ(s)² - Q(s)))] = 0`** for `Θ` bounded,
continuous, measurable for the canonical filtration at time `s` (proof of Proposition 7.1 (3)):
let `L → ∞` along good levels in `limBr_stopped_limit`, with dominated convergence
(`𝔼 sup_t M^φ(t)² ≤ 4 𝔼 M^φ(T)²` by Doob, `𝔼 Q(T) < ∞` by (7.1)). -/
theorem limBr_integral_eq_zero {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} {T : ℝ}
    {n : ℕ → ℝ} {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal (limField ρ Xl t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Xl ω) t : Measure ℝ) =
        volume.withDensity fun x => ENNReal.ofReal (limField ρ Xl t x ω))
    {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : (t : ℝ) ≤ T) {Θ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ} (hΘc : Continuous Θ)
    (hΘ : Measurable[pathFiltrationCan T s] Θ) {B : ℝ} (hB : ∀ γ, |Θ γ| ≤ B) :
    ∫ ω, Θ (Xl ω) * ((limMart Xl φ φt t ω ^ 2 - limBracket (limField ρ Xl) φ t ω) -
      (limMart Xl φ φt s ω ^ 2 - limBracket (limField ρ Xl) φ s ω)) ∂Pr = 0 := by
  have hPr := hc.isProbabilityMeasure
  have hT : 0 ≤ T := hc.pos.le
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  set T' : ℝ≥0 := ⟨T, hT⟩ with hT'
  have hG := limBr_ae_good hc.measurable_lim hρ hZ2
  -- a subsequence along which (7.6) holds almost surely
  obtain ⟨ψ, hψ, hQ⟩ := limBr_exists_subseq
    (f := fun j t ω => QNpath (n j) φ t (X j ω))
    (g := fun t ω => limBracket (limField ρ Xl) φ t ω)
    fun η hη => hc.tendsto_QN hρ hZ2 hdens hφ hη
  -- the level process of the limit, and its countably many bad levels
  set V : ℝ → Ωs → ℝ := fun u ω => limBrLimV ρ φ φt u (Xl ω) with hV
  have hVm : ∀ u, Measurable (V u) := fun u =>
    ((limBr_measurable_mod hφ hρ (pathFunClamp_mem hT u)).max
      ((limMart_measurable hφ (pathFunClamp_mem hT u)).pow_const 2)).comp hc.measurable_lim
  have hVc : ∀ ω, ContinuousOn (fun u => V u ω) (Set.Icc 0 T) := fun ω =>
    ((limBrMod_props hφ hρ (Xl ω)).1.sup ((limMart_continuousOn hφ (Xl ω)).pow 2)).congr
      fun r hr => by rw [hV]; simp only; rw [limBrLimV, pathFunClamp_of_mem hr]; rfl
  have hcount := countable_hitTime_ne (μ := Pr) (T := T') hVm hVc
  have hLex : ∀ i : ℕ, ∃ L ∈ {K : ℝ | Pr {ω | hitTime V K T' ω ≠ hitTimeStrict V K T' ω} ≠ 0}ᶜ,
      L ∈ Set.Ioo (i : ℝ) (i + 1) := fun i => by
    have h0 := hcount.measure_zero (volume : Measure ℝ)
    obtain ⟨L, hL1, hL2⟩ := nonempty_of_measure_ne_zero
      (μ := (volume : Measure ℝ)) (s := Set.Ioo (i : ℝ) (i + 1) \
        {K : ℝ | Pr {ω | hitTime V K T' ω ≠ hitTimeStrict V K T' ω} ≠ 0})
      (by rw [measure_sdiff_null h0, Real.volume_Ioo]; simp)
    exact ⟨L, hL2, hL1⟩
  choose Ls hLs hLsI using hLex
  have hL0 : ∀ i, 0 ≤ Ls i := fun i => (Nat.cast_nonneg i).trans (hLsI i).1.le
  have hstep := fun i => limBr_stopped_limit hc hT hρ hφ hψ hQ hG (hL0 i)
    (not_not.1 (hLs i)) hst ht hΘc hΘ hB
  -- Doob's inequality and (7.1): the dominating function
  have hM := hc.isCL2Mart hφ
  have hD := hM.lintegral_iSup_sq_le
  have hMT := hM.memLp ⟨T, hT⟩ le_rfl
  have hD2 : ∫⁻ ω, ⨆ r ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (limMart Xl φ φt r ω ^ 2) ∂Pr ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp)
      ((memLp_two_iff_integrable_sq hMT.aestronglyMeasurable).1 hMT).lintegral_lt_top.ne) hD.2
  set S : Ωs → ℝ := fun ω =>
    (⨆ r ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (limMart Xl φ φt r ω ^ 2)).toReal with hS
  have hSi : Integrable S Pr := integrable_toReal_of_lintegral_ne_top hD.1 hD2
  have hAT := limBr_integrable_comp hc.measurable_lim hρ hφ hZ2 (t := T) ⟨hT, le_rfl⟩
  have hbi : Integrable (fun ω => B * (2 * S ω + 2 * limBracket (limField ρ Xl) φ T ω)) Pr :=
    ((hSi.const_mul 2).add (hAT.const_mul 2)).const_mul B
  set Gf : ℕ → Ωs → ℝ := fun i ω => Θ (Xl ω) *
    limBrInc (fun r => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt r
      (Xl ω)) (fun r => limBrMod ρ φ r (Xl ω)) s t (hitTime V (Ls i) T' ω) with hGf
  have hbound : ∀ i, ∀ᵐ ω ∂Pr, ‖Gf i ω‖ ≤
      B * (2 * S ω + 2 * limBracket (limField ρ Xl) φ T ω) := by
    intro i
    filter_upwards [hG, ae_lt_top' hD.1 hD2] with ω hg hfin
    have hA := limBrMod_props hφ hρ (Xl ω)
    have hAT' : limBrMod ρ φ T (Xl ω) = limBracket (limField ρ Xl) φ T ω :=
      Set.indicator_of_mem hg _
    have key : ∀ r : ℝ≥0, (r : ℝ) ≤ T →
        limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt
          (min (r : ℝ) (hitTime V (Ls i) T' ω)) (Xl ω) ^ 2 ≤ S ω ∧
        0 ≤ limBrMod ρ φ (min (r : ℝ) (hitTime V (Ls i) T' ω)) (Xl ω) ∧
        limBrMod ρ φ (min (r : ℝ) (hitTime V (Ls i) T' ω)) (Xl ω) ≤
          limBracket (limField ρ Xl) φ T ω := by
      intro r hr
      have hmem : min (r : ℝ) (hitTime V (Ls i) T' ω) ∈ Set.Icc 0 T :=
        ⟨le_min r.2 (NNReal.coe_nonneg _), (min_le_left _ _).trans hr⟩
      refine ⟨?_, hA.2.2.2 _ hmem.1, hAT' ▸ hA.2.1 hmem ⟨hT, le_rfl⟩ hmem.2⟩
      rw [hS, ← ENNReal.ofReal_le_iff_le_toReal hfin.ne]
      exact le_iSup₂ (f := fun r _ => ENNReal.ofReal (limMart Xl φ φt r ω ^ 2)) _ hmem
    obtain ⟨a1, a2, a3⟩ := key t ht
    obtain ⟨b1, b2, b3⟩ := key s hs
    have hinc : |limBrInc (fun r => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
        γ') φ φt r (Xl ω)) (fun r => limBrMod ρ φ r (Xl ω)) s t (hitTime V (Ls i) T' ω)| ≤
        2 * S ω + 2 * limBracket (limField ρ Xl) φ T ω := by
      simp only [limBrInc]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (limMart (fun γ' : C(Set.Icc (0 : ℝ) T,
        FiniteMeasure ℝ) => γ') φ φt (min (t : ℝ) (hitTime V (Ls i) T' ω)) (Xl ω)),
        sq_nonneg (limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt
          (min (s : ℝ) (hitTime V (Ls i) T' ω)) (Xl ω))]
    rw [hGf, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB _) hinc (abs_nonneg _) ((abs_nonneg _).trans (hB (Xl ω)))
  -- as `L → ∞`, the hitting time is eventually `T`
  have hconv : ∀ᵐ ω ∂Pr, Tendsto (fun i => Gf i ω) atTop (𝓝 (Θ (Xl ω) *
      ((limMart Xl φ φt t ω ^ 2 - limBracket (limField ρ Xl) φ t ω) -
        (limMart Xl φ φt s ω ^ 2 - limBracket (limField ρ Xl) φ s ω)))) := by
    filter_upwards [hG] with ω hg
    obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (hVc ω)
    have hLs : Tendsto Ls atTop atTop :=
      tendsto_atTop_mono (fun i => (hLsI i).1.le) tendsto_natCast_atTop_atTop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hLs.eventually_gt_atTop R] with i hi
    have hhit : hitTime V (Ls i) T' ω = T' := hitTime_eq_of_forall_lt fun u hu => by
      have hu' : (u : ℝ) ∈ Set.Icc 0 T := ⟨u.2, (NNReal.coe_lt_coe.2 hu).le⟩
      have := hR u hu'
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans_lt (this.trans_lt hi)
    rw [hGf]
    simp only [hhit, limBrInc]
    have e1 : min (t : ℝ) (T' : ℝ) = t := min_eq_left ht
    have e2 : min (s : ℝ) (T' : ℝ) = s := min_eq_left hs
    rw [e1, e2]
    simp only [limBrMod, Set.indicator_of_mem hg]
    rfl
  have hlim := tendsto_integral_of_dominated_convergence _ (fun i => (hstep i).1) hbi hbound hconv
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun i => (hstep i).2.symm)

/-- **Proposition 7.1 (3)** on the coupling: `⟨M^φ⟩_t = ∫_0^t ∫ Z(s,x)² φ_s(x)² dx ds`. -/
theorem IsLimCoupling.hasBracket {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} {T : ℝ}
    {n : ℕ → ℝ} {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal (limField ρ Xl t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Xl ω) t : Measure ℝ) =
        volume.withDensity fun x => ENNReal.ofReal (limField ρ Xl t x ω))
    {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    HasBracket T (nullAug Pr (pathFiltration Xl)) (limMart Xl φ φt)
      (limBracket (limField ρ Xl) φ) Pr := by
  have hPr := hc.isProbabilityMeasure
  have hT : 0 ≤ T := hc.pos.le
  have hG := limBr_ae_good hc.measurable_lim hρ hZ2
  refine (limBr_hasBracket_map_iff hT hc.measurable_lim hρ hφ hG).2 ?_
  set P := Pr.map Xl with hP
  set m := limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt with hm
  set a := limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ
    with ha
  have hGm : ∀ᵐ γ ∂P, γ ∈ limBrGood ρ T :=
    (ae_map_iff hc.measurable_lim.aemeasurable (limBr_measurableSet_good hρ)).2 hG
  have hM : IsCL2Mart T (nullAug P (pathFiltrationCan T)) m P :=
    (isCL2Mart_map_iff hc.measurable_lim (fun t ht => limMart_measurable hφ ht)
      (limMart_continuousOn hφ)).1 (hc.isCL2Mart hφ)
  have hai : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (a t) P := fun t ht =>
    (integrable_map_measure (limBr_measurable_bracket hφ hρ ht).aestronglyMeasurable
      hc.measurable_lim.aemeasurable).2 (limBr_integrable_comp hc.measurable_lim hρ hφ hZ2 ht)
  refine { toIsCL2Mart := hM
           integrable_bracket := fun t ht => hai t ⟨t.2, ht⟩
           zero := ae_of_all _ fun γ => by simp [ha, limBracket]
           mono := by
             filter_upwards [hGm] with γ hγ using (limBr_continuousOn_monotoneOn hφ hρ hγ).2
           cont_bracket := by
             filter_upwards [hGm] with γ hγ using (limBr_continuousOn_monotoneOn hφ hρ hγ).1
           condExp_sq := fun s t hst ht => ?_ }
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hsI : (s : ℝ) ∈ Set.Icc 0 T := ⟨s.2, hs⟩
  have htI : (t : ℝ) ∈ Set.Icc 0 T := ⟨t.2, ht⟩
  set D : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ :=
    fun γ => (m t γ ^ 2 - a t γ) - (m s γ ^ 2 - a s γ) with hD
  have hYt : Integrable (fun γ => m t γ ^ 2 - a t γ) P :=
    (hM.memLp t ht).integrable_sq.sub (hai t htI)
  have hYs : Integrable (fun γ => m s γ ^ 2 - a s γ) P :=
    (hM.memLp s hs).integrable_sq.sub (hai s hsI)
  have hDi : Integrable D P := hYt.sub hYs
  have hD0 : P[D | nullAug P (pathFiltrationCan T) s] =ᵐ[P] 0 := by
    refine pathCan_condExp_eq_zero hDi fun k u f g hu => ?_
    set Θ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ :=
      fun γ => ∏ i, g i (pairFM (pathAt γ (u i)) (f i)) with hΘ
    have hpc : ∀ i, Continuous fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
        pairFM (pathAt γ (u i)) (f i) := fun i =>
      (continuous_pairFM (f i).continuous ⟨‖f i‖, fun x => by
        simpa [Real.norm_eq_abs] using (f i).norm_coe_le_norm x⟩).comp
        (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))
    have hΘc : Continuous Θ := continuous_finsetProd _ fun i _ => (g i).continuous.comp (hpc i)
    have hΘB : ∀ γ, |Θ γ| ≤ ∏ i, ‖g i‖ := fun γ => by
      rw [hΘ, ← Real.norm_eq_abs, norm_prod]
      gcongr with i
      exact (g i).norm_coe_le_norm _
    have hΘmc : Measurable[pathFiltrationCan T s] Θ :=
      Finset.measurable_prod _ fun i _ => (g i).continuous.measurable.comp
        (measurable_pairFM_pathFiltrationCan (hu i) (f i))
    have hDm : Measurable D :=
      (((limMart_measurable hφ htI).pow_const 2).sub (limBr_measurable_bracket hφ hρ htI)).sub
        (((limMart_measurable hφ hsI).pow_const 2).sub (limBr_measurable_bracket hφ hρ hsI))
    have hmeas : Measurable fun γ => Θ γ * D γ := hΘc.measurable.mul hDm
    show ∫ γ, Θ γ * D γ ∂P = 0
    rw [hP, integral_map hc.measurable_lim.aemeasurable hmeas.aestronglyMeasurable]
    exact limBr_integral_eq_zero hc hρ hZ2 hdens hφ hst ht hΘc hΘmc hΘB
  have hmsm : StronglyMeasurable[nullAug P (pathFiltrationCan T) s]
      (fun γ => m s γ ^ 2 - a s γ) :=
    ((((limMart_stronglyMeasurable_can hφ hs).measurable.pow_const 2).sub
      (limBr_measurable_can hφ hρ hs)).stronglyMeasurable).mono (le_nullAug _ _ s)
  have e : (fun γ => m t γ ^ 2 - a t γ) = fun γ => D γ + (m s γ ^ 2 - a s γ) := by
    funext γ
    simp [hD]
  rw [e]
  refine (condExp_add hDi hYs _).trans ?_
  rw [condExp_of_stronglyMeasurable ((nullAug P (pathFiltrationCan T)).le s) hmsm hYs]
  filter_upwards [hD0] with γ hγ
  simp [hγ]

end QSSEPtoKPZ
