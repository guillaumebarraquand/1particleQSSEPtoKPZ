/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PrelimitLaw
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.LimitPoints.Prop71MartL2

/-!
# Proposition 7.1 (3): (7.5) and the martingale property of `M^φ` (task Q3)

INTERFACE FILE (task I0″ of Stage 4): the definition is complete; the statements below are
interfaces, proved by task Q3. See `docs/stage4-design.md`, Section 1.2 (b)–(d), and
`docs/stage4-interfaces.md`.

`IsLimCoupling Pr T n X Xl`: the Skorokhod coupling of Section 7.1 — on one probability space,
random paths `X j` whose laws are prelimit laws at scales `n j → ∞`, converging almost surely in
`C([0,T], ℳ₊)` to `Xl`. In the proof of Proposition 7.1 it is obtained from `skorokhod_subseq`.
* (7.5), pathwise: `sup_{t ≤ T} |M_n^φ(t) - M^φ(t)| → 0` along converging paths
  (`tendstoUniformlyOn_MNpath`; uses `prop_3_1_generator`).
* `M^φ` is a continuous square-integrable martingale for the natural filtration of `Xl` with the
  null sets (`IsLimCoupling.isCL2Mart`; the article's `Θ` argument, `pathCan_condExp_eq_zero`,
  uniform integrability from `𝔼[M_n^φ(t)²] = 𝔼[⟨M_n^φ⟩_t]`, Proposition 3.1 (2) and (4.8)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp Interval

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- The Skorokhod coupling of Section 7.1. -/
structure IsLimCoupling {Ωs : Type*} [MeasurableSpace Ωs] (Pr : Measure Ωs) (T : ℝ)
    (n : ℕ → ℝ) (X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure Pr
  pos : 0 < T
  one_le : ∀ j, 1 ≤ n j
  tendsto_atTop : Tendsto n atTop atTop
  measurable : ∀ j, Measurable (X j)
  measurable_lim : Measurable Xl
  law : ∀ j, IsPathPrelimLaw.{u} T (n j) (Pr.map (X j))
  tendsto : ∀ᵐ ω ∂Pr, Tendsto (fun j => X j ω) atTop (𝓝 (Xl ω))

/-- **(7.5), pathwise**: if `γ_j → γ` in `C([0,T], ℳ₊)` and `n_j → ∞`, then
`M_{n_j}^φ(γ_j) → M^φ(γ)` uniformly on `[0,T]`. -/
theorem tendstoUniformlyOn_MNpath {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {n : ℕ → ℝ} (hn₁ : ∀ j, 1 ≤ n j) (hn : Tendsto n atTop atTop)
    {γ : ℕ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} {γl : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hγ : Tendsto γ atTop (𝓝 γl)) :
    TendstoUniformlyOn (fun j t => MNpath (n j) φ φt t (γ j))
      (fun t => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt t γl) atTop
      (Set.Icc 0 T) := by
  by_cases hT : 0 ≤ T
  swap
  · intro u _
    exact Eventually.of_forall fun j t ht => absurd (ht.1.trans ht.2) hT
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  have hφ0 := hφ.pathFun_continuousOn_comp (f := fun y => y) continuous_id
  set Cp := max C 0 with hCp
  -- the three continuous functionals of the path
  have hA := continuousOn_pairFM_pathAt hφ0 ⟨c, hc⟩
  have hL := continuousOn_pairFM_pathAt hφ.limMart_continuousOn_drift hφ.limMart_bound_drift
  have hW := continuousOn_pairFM_pathAt (T := T) (φ := fun _ _ => (1 : ℝ)) continuousOn_const
    ⟨1, fun _ _ _ => by simp⟩
  obtain ⟨Wm, hWm⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hW.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨trivial, ht⟩ : MapsTo (fun t : ℝ => (γl, t)) (Icc 0 T) (univ ×ˢ Icc 0 T)))
  have hWm' : ∀ s ∈ Icc 0 T, |pairFM (pathAt γl s) (fun _ => (1 : ℝ))| ≤ Wm := fun s hs => by
    simpa using hWm s hs
  have e1 := limMart_unif_of_continuousOn
    (F := fun γ t => pairFM (pathAt γ t) (φ t)) hA hγ (by positivity : 0 < ε / 3)
  have e2 := limMart_unif_of_continuousOn
    (F := fun γ s => pairFM (pathAt γ s) (fun y => φt s y + iteratedDeriv 2 (φ s) y / 2)) hL hγ
    (by positivity : 0 < ε / (3 * (T + 1)))
  have e3 := limMart_unif_of_continuousOn
    (F := fun γ s => pairFM (pathAt γ s) (fun _ => (1 : ℝ))) hW hγ one_pos
  have hn4 : Tendsto (fun j => n j ^ (-1 / 4 : ℝ) * (Cp * (Wm + 1) * T)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)).comp hn).mul_const
      (Cp * (Wm + 1) * T)
    rw [zero_mul] at h
    refine h.congr fun j => ?_
    simp only [Function.comp_apply]
    norm_num
  have e4 := hn4.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))
  filter_upwards [e1, e2, e3, e4] with j h1 h2 h3 h4 t ht
  have hnj := hn₁ j
  -- the drifts at time `s`
  set Dj : ℝ → ℝ := fun s => pairFM (pathAt (γ j) s) (fun y => φt s y + AN (n j) (φ s) y)
  set Lj : ℝ → ℝ := fun s => pairFM (pathAt (γ j) s)
    (fun y => φt s y + iteratedDeriv 2 (φ s) y / 2)
  set Ll : ℝ → ℝ := fun s => pairFM (pathAt γl s)
    (fun y => φt s y + iteratedDeriv 2 (φ s) y / 2)
  have hcont : ∀ g : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), ∀ {F : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) →
      (∃ K, ∀ s ∈ Icc 0 T, ∀ y, |F s y| ≤ K) →
      IntervalIntegrable (fun s => pairFM (pathAt g s) (F s)) volume 0 t := fun g F hF hb =>
    (((continuousOn_pairFM_pathAt hF hb).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨trivial, hs⟩ : MapsTo (fun s : ℝ => (g, s)) (Icc 0 T)
        (univ ×ˢ Icc 0 T))).mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
      ).intervalIntegrable
  have hDj := hcont (γ j) (hφ.pathFun_continuousOn_drift (n j)) (hφ.pathFun_bound_drift (n j))
  have hLl := hcont γl hφ.limMart_continuousOn_drift hφ.limMart_bound_drift
  have hpt : ∀ s ∈ Ι (0 : ℝ) t, ‖Dj s - Ll s‖ ≤
      n j ^ (-1 / 4 : ℝ) * Cp * (Wm + 1) + ε / (3 * (T + 1)) := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
    obtain ⟨K1, hK1⟩ := hφ.pathFun_bound_drift (n j)
    obtain ⟨K2, hK2⟩ := hφ.limMart_bound_drift
    have hc1 : Continuous fun y => φt s y + AN (n j) (φ s) y :=
      (hφ.pathFun_continuousOn_drift (n j)).comp_continuous
        (continuous_const.prodMk continuous_id) fun y => ⟨hsT, trivial⟩
    have hc2 : Continuous fun y => φt s y + iteratedDeriv 2 (φ s) y / 2 :=
      hφ.limMart_continuousOn_drift.comp_continuous
        (continuous_const.prodMk continuous_id) fun y => ⟨hsT, trivial⟩
    have hDL := limMart_abs_pairFM_sub_le (pathAt (γ j) s) hc1.measurable hc2.measurable
      (hK1 s hsT) (hK2 s hsT) (c := n j ^ (-1 / 4 : ℝ) * Cp) fun y => by
        have := hφ.limMart_abs_AN_sub_le hnj hsT y
        have hle : n j ^ (-1 / 4 : ℝ) * C ≤ n j ^ (-1 / 4 : ℝ) * Cp :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        calc |φt s y + AN (n j) (φ s) y - (φt s y + iteratedDeriv 2 (φ s) y / 2)|
            = |AN (n j) (φ s) y - iteratedDeriv 2 (φ s) y / 2| := by ring_nf
          _ ≤ _ := this.trans hle
    have hWj : pairFM (pathAt (γ j) s) (fun _ => (1 : ℝ)) ≤ Wm + 1 := by
      have a := h3 s hsT
      have b := hWm' s hsT
      rw [abs_lt] at a
      linarith [le_abs_self (pairFM (pathAt γl s) fun _ => (1 : ℝ))]
    have hLjl := h2 s hsT
    have hnn : 0 ≤ n j ^ (-1 / 4 : ℝ) * Cp := by positivity
    rw [Real.norm_eq_abs]
    calc |Dj s - Ll s| ≤ |Dj s - Lj s| + |Lj s - Ll s| := abs_sub_le _ _ _
      _ ≤ n j ^ (-1 / 4 : ℝ) * Cp * pairFM (pathAt (γ j) s) (fun _ => (1 : ℝ)) +
          ε / (3 * (T + 1)) := add_le_add hDL hLjl.le
      _ ≤ n j ^ (-1 / 4 : ℝ) * Cp * (Wm + 1) + ε / (3 * (T + 1)) := by gcongr
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub hDj hLl, sub_zero, abs_of_nonneg ht.1] at hint
  have hA1 := h1 t ht
  rw [Real.dist_eq]
  have e : limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt t γl -
      MNpath (n j) φ φt t (γ j) =
      (pairFM (pathAt γl t) (φ t) - pairFM (pathAt (γ j) t) (φ t)) +
        ((∫ s in (0 : ℝ)..t, Dj s) - ∫ s in (0 : ℝ)..t, Ll s) := by
    simp only [limMart, MNpath, Dj, Ll]
    ring
  rw [e, Real.norm_eq_abs] at *
  have hT1 : t * (ε / (3 * (T + 1))) ≤ ε / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [ht.2]
  have hT2 : n j ^ (-1 / 4 : ℝ) * Cp * (Wm + 1) * t ≤ n j ^ (-1 / 4 : ℝ) * (Cp * (Wm + 1) * T) := by
    have hWm0 : 0 ≤ Wm + 1 := by
      have := hWm' 0 ⟨le_rfl, hT⟩
      linarith [abs_nonneg (pairFM (pathAt γl 0) fun _ => (1 : ℝ))]
    have : 0 ≤ n j ^ (-1 / 4 : ℝ) * Cp * (Wm + 1) := by positivity
    nlinarith [ht.2]
  calc |pairFM (pathAt γl t) (φ t) - pairFM (pathAt (γ j) t) (φ t) +
        ((∫ s in (0 : ℝ)..t, Dj s) - ∫ s in (0 : ℝ)..t, Ll s)|
      ≤ |pairFM (pathAt γl t) (φ t) - pairFM (pathAt (γ j) t) (φ t)| +
        |(∫ s in (0 : ℝ)..t, Dj s) - ∫ s in (0 : ℝ)..t, Ll s| := abs_add_le _ _
    _ < ε / 3 + (n j ^ (-1 / 4 : ℝ) * Cp * (Wm + 1) + ε / (3 * (T + 1))) * t := by
        refine add_lt_add_of_lt_of_le ?_ hint
        rw [abs_sub_comm]
        exact hA1
    _ ≤ ε := by nlinarith

/-- For a martingale `M` and a bounded `𝓕_s`-measurable `Θ`, `𝔼[Θ (M_t - M_s)] = 0` (the identity
(7.7) of the article for `M_n^φ`). -/
private lemma limMart_integral_mul_sub_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {M : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M P) {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ) ≤ T)
    {Θ : Ω → ℝ} (hΘ : StronglyMeasurable[𝓕 s] Θ) {B : ℝ} (hB : ∀ ω, |Θ ω| ≤ B) :
    ∫ ω, Θ ω * (M t ω - M s ω) ∂P = 0 := by
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hMt : Integrable (M t) P := (hM.memLp t ht).integrable one_le_two
  have hMs : Integrable (M s) P := (hM.memLp s hs).integrable one_le_two
  have hdiff : Integrable (fun ω => M t ω - M s ω) P := hMt.sub hMs
  have hprod : Integrable (Θ * fun ω => M t ω - M s ω) P :=
    hdiff.bdd_mul (hΘ.mono (𝓕.le s)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)
  have h1 : P[fun ω => M t ω - M s ω | 𝓕 s] =ᵐ[P] 0 := by
    refine (condExp_sub hMt hMs _).trans ?_
    filter_upwards [hM.condExp s t hst ht, hM.condExp s s le_rfl hs] with ω h1 h2
    simp [h1, h2]
  have h2 := condExp_mul_of_stronglyMeasurable_left hΘ hprod hdiff
  calc ∫ ω, Θ ω * (M t ω - M s ω) ∂P = ∫ ω, (Θ * fun ω => M t ω - M s ω) ω ∂P := rfl
    _ = ∫ ω, (P[Θ * fun ω => M t ω - M s ω | 𝓕 s]) ω ∂P :=
        (integral_condExp (𝓕.le s)).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h2, h1] with ω h2 h1
        rw [h2, Pi.mul_apply, h1]
        simp
    _ = 0 := by simp

/-- **`M^φ` is a martingale** for the natural filtration of the limit (with the null sets). -/
theorem IsLimCoupling.isCL2Mart {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} {T : ℝ}
    {n : ℕ → ℝ} {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    IsCL2Mart T (nullAug Pr (pathFiltration Xl)) (limMart Xl φ φt) Pr := by
  have hPr := hc.isProbabilityMeasure
  have hT := hc.pos
  set m := limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt with hm
  have key : IsCL2Mart T (nullAug (Pr.map Xl) (pathFiltrationCan T)) m (Pr.map Xl) := by
    have hPl : IsProbabilityMeasure (Pr.map Xl) :=
      inferInstance
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ j, ∀ t ∈ Icc 0 T,
        ∫⁻ ω, ENNReal.ofReal (MNpath (n j) φ φt t (X j ω) ^ 2) ∂Pr ≤ ENNReal.ofReal K := by
      refine ⟨4 * C ^ 2 * 2 ^ (1 + 16 * T), fun j t ht => ?_⟩
      have hmeas := measurable_MNpath (hc.one_le j) hφ ht
      refine le_of_eq_of_le (lintegral_map (f := fun γ => ENNReal.ofReal (MNpath (n j) φ φt t γ ^ 2))
        (ENNReal.measurable_ofReal.comp (hmeas.pow_const 2)) (hc.measurable j)).symm ?_
      exact (hc.law j).limMart_lintegral_sq_le (hc.one_le j) hT hφ ht
    have hmeasj : ∀ j, ∀ t ∈ Icc 0 T, Measurable fun ω => MNpath (n j) φ φt t (X j ω) :=
      fun j t ht => (measurable_MNpath (hc.one_le j) hφ ht).comp (hc.measurable j)
    have hconv : ∀ᵐ ω ∂Pr, ∀ t ∈ Icc 0 T,
        Tendsto (fun j => MNpath (n j) φ φt t (X j ω)) atTop (𝓝 (m t (Xl ω))) := by
      filter_upwards [hc.tendsto] with ω hω t ht
      exact (tendstoUniformlyOn_MNpath hφ hc.one_le hc.tendsto_atTop hω).tendsto_at ht
    -- `M^φ(t) ∈ L²`
    have hmem : ∀ t ∈ Icc 0 T, MemLp (m t) 2 (Pr.map Xl) := by
      intro t ht
      have h := (limMart_tendsto_integral_of_sq_le (fun j => hmeasj j t ht) ENNReal.ofReal_ne_top
        (fun j => hK j t ht) (by filter_upwards [hconv] with ω hω using hω t ht)).1
      exact (memLp_map_measure_iff (limMart_measurable hφ ht).aestronglyMeasurable
        hc.measurable_lim.aemeasurable).2 h
    refine ⟨ae_of_all _ (limMart_continuousOn hφ), fun t ht => hmem t ⟨t.2, ht⟩,
      fun s t hst ht => ?_⟩
    have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
    have hsI : (s : ℝ) ∈ Icc 0 T := ⟨s.2, hs⟩
    have htI : (t : ℝ) ∈ Icc 0 T := ⟨t.2, ht⟩
    set D : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ := fun γ => m t γ - m s γ with hD
    have hmt := (hmem t htI).integrable one_le_two
    have hms := (hmem s hsI).integrable one_le_two
    have hDi : Integrable D (Pr.map Xl) := hmt.sub hms
    have hD0 : (Pr.map Xl)[D | nullAug (Pr.map Xl) (pathFiltrationCan T) s] =ᵐ[Pr.map Xl] 0 := by
      refine pathCan_condExp_eq_zero hDi fun k u f g hu => ?_
      set Θ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ :=
        fun γ => ∏ i, g i (pairFM (pathAt γ (u i)) (f i)) with hΘ
      have hpc : ∀ i, Continuous fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
          pairFM (pathAt γ (u i)) (f i) := fun i =>
        (continuous_pairFM (f i).continuous ⟨‖f i‖, fun x => by
          simpa [Real.norm_eq_abs] using (f i).norm_coe_le_norm x⟩).comp
          (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))
      have hΘc : Continuous Θ := continuous_finsetProd _ fun i _ => (g i).continuous.comp (hpc i)
      set B : ℝ := ∏ i, ‖g i‖ with hB
      have hΘB : ∀ γ, |Θ γ| ≤ B := fun γ => by
        rw [hΘ, hB, ← Real.norm_eq_abs, norm_prod]
        gcongr with i
        exact (g i).norm_coe_le_norm _
      have hΘmc : Measurable[pathFiltrationCan T s] Θ :=
        Finset.measurable_prod _ fun i _ => (g i).continuous.measurable.comp
          (measurable_pairFM_pathFiltrationCan (hu i) (f i))
      -- pass to the limit in `𝔼[Θ_n (M_n^φ(t) - M_n^φ(s))] = 0`
      set F : ℕ → Ωs → ℝ := fun j ω =>
        Θ (X j ω) * (MNpath (n j) φ φt t (X j ω) - MNpath (n j) φ φt s (X j ω)) with hF
      have hFm : ∀ j, Measurable (F j) := fun j =>
        (hΘc.measurable.comp (hc.measurable j)).mul ((hmeasj j t htI).sub (hmeasj j s hsI))
      have hFK : ∀ j, ∫⁻ ω, ENNReal.ofReal (F j ω ^ 2) ∂Pr ≤
          ENNReal.ofReal (2 * B ^ 2) * (ENNReal.ofReal K + ENNReal.ofReal K) := by
        intro j
        calc ∫⁻ ω, ENNReal.ofReal (F j ω ^ 2) ∂Pr
            ≤ ∫⁻ ω, ENNReal.ofReal (2 * B ^ 2) *
              (ENNReal.ofReal (MNpath (n j) φ φt t (X j ω) ^ 2) +
                ENNReal.ofReal (MNpath (n j) φ φt s (X j ω) ^ 2)) ∂Pr := by
              refine lintegral_mono fun ω => ?_
              rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
                ← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              have h1 : Θ (X j ω) ^ 2 ≤ B ^ 2 := by
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) (hΘB _) 2
              set a := MNpath (n j) φ φt t (X j ω)
              set b := MNpath (n j) φ φt s (X j ω)
              have h2 : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a + b)]
              calc F j ω ^ 2 = Θ (X j ω) ^ 2 * (a - b) ^ 2 := by simp only [hF]; ring
                _ ≤ B ^ 2 * (2 * (a ^ 2 + b ^ 2)) :=
                    mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
                _ = 2 * B ^ 2 * (a ^ 2 + b ^ 2) := by ring
          _ = ENNReal.ofReal (2 * B ^ 2) *
              (∫⁻ ω, ENNReal.ofReal (MNpath (n j) φ φt t (X j ω) ^ 2) ∂Pr +
                ∫⁻ ω, ENNReal.ofReal (MNpath (n j) φ φt s (X j ω) ^ 2) ∂Pr) := by
              have hmt' : Measurable fun ω => ENNReal.ofReal (MNpath (n j) φ φt t (X j ω) ^ 2) :=
                ENNReal.measurable_ofReal.comp ((hmeasj j t htI).pow_const 2)
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmt']
          _ ≤ _ := by gcongr <;> [exact hK j t htI; exact hK j s hsI]
      have hFlim : ∀ᵐ ω ∂Pr, Tendsto (fun j => F j ω) atTop (𝓝 (Θ (Xl ω) * D (Xl ω))) := by
        filter_upwards [hconv, hc.tendsto] with ω hω hX
        exact ((hΘc.tendsto _).comp hX).mul ((hω t htI).sub (hω s hsI))
      have hF0 : ∀ j, ∫ ω, F j ω ∂Pr = 0 := by
        intro j
        have := (hc.law j).isProbabilityMeasure
        have hB' := ((hc.law j).hasBracket (hc.one_le j) hT hφ).toIsCL2Mart
        have h0 := limMart_integral_mul_sub_eq_zero hB' hst ht
          ((hΘmc.mono (le_nullAug _ _ s) le_rfl).stronglyMeasurable) hΘB
        have hmeas : Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
            Θ γ * (MNpath (n j) φ φt t γ - MNpath (n j) φ φt s γ) :=
          hΘc.measurable.mul ((measurable_MNpath (hc.one_le j) hφ htI).sub
            (measurable_MNpath (hc.one_le j) hφ hsI))
        rw [← h0]
        exact (integral_map (hc.measurable j).aemeasurable hmeas.aestronglyMeasurable).symm
      have hlim := (limMart_tendsto_integral_of_sq_le hFm (by finiteness) hFK hFlim).2
      simp only [hF0, tendsto_const_nhds_iff] at hlim
      have hmeas : Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => Θ γ * D γ :=
        hΘc.measurable.mul ((limMart_measurable hφ htI).sub (limMart_measurable hφ hsI))
      have e : ∫ γ, Θ γ * D γ ∂(Pr.map Xl) = ∫ ω, Θ (Xl ω) * D (Xl ω) ∂Pr :=
        integral_map hc.measurable_lim.aemeasurable hmeas.aestronglyMeasurable
      show ∫ γ, Θ γ * D γ ∂(Pr.map Xl) = 0
      rw [e]
      exact hlim.symm
    have hmsm : StronglyMeasurable[nullAug (Pr.map Xl) (pathFiltrationCan T) s] (m s) :=
      (limMart_stronglyMeasurable_can hφ hs).mono (le_nullAug _ _ s)
    have e : m t = fun γ => D γ + m s γ := by
      funext γ
      simp [hD]
    rw [e]
    refine (condExp_add hDi hms _).trans ?_
    rw [condExp_of_stronglyMeasurable ((nullAug (Pr.map Xl) (pathFiltrationCan T)).le s) hmsm hms]
    filter_upwards [hD0] with γ hγ
    simp [hγ]
  exact (isCL2Mart_map_iff hc.measurable_lim (fun t ht => limMart_measurable hφ ht)
    (limMart_continuousOn hφ)).2 key

end QSSEPtoKPZ
