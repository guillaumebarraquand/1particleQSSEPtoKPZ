/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71MartAux

/-!
# `L²` bounds and uniform integrability for Proposition 7.1 (3) (task Q3)

* `IsPathPrelimLaw.limMart_lintegral_sq_le`: under a prelimit law,
  `𝔼[M_n^φ(t)²] = 𝔼[⟨M_n^φ⟩_t] ≤ 4C² 2^{1+16T}` (Proposition 3.1 (2) and (4.8); the article:
  "`𝔼[M_n^φ(t)²] = 𝔼[Q_n(t)]` is bounded uniformly in `n`").
* `limMart_tendsto_integral_of_sq_le`: a sequence bounded in `L²` and converging almost surely
  converges in `L¹` (Vitali), and its limit is in `L²` (Fatou).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- `ℰ_n(t;1) ≥ 0` on the path space. -/
theorem limMart_ENpath_one_nonneg (n : ℝ) {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (s : ℝ) (hn : 0 ≤ n) : 0 ≤ ENpath n γ s fun _ => 1 := by
  unfold ENpath
  refine mul_nonneg (Real.rpow_nonneg hn _) (tsum_nonneg fun x => ?_)
  simp only [mul_one]
  exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- **Uniform `L²` bound** (Section 7.1): under a prelimit law,
`𝔼[M_n^φ(t)²] = 𝔼[⟨M_n^φ⟩_t] ≤ 4C² 2^{1+16T}` for `t ∈ [0,T]`. -/
theorem IsPathPrelimLaw.limMart_lintegral_sq_le {T n : ℝ}
    {P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hP : IsPathPrelimLaw.{u} T n P)
    (hn : 1 ≤ n) (hT : 0 < T) {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ∫⁻ γ, ENNReal.ofReal (MNpath n φ φt t γ ^ 2) ∂P ≤
      ENNReal.ofReal (4 * C ^ 2 * 2 ^ (1 + 16 * T)) := by
  have := hP.isProbabilityMeasure
  have hB := hP.hasBracket hn hT hφ
  set tN : ℝ≥0 := ⟨t, ht.1⟩ with htN
  have hM2 : MemLp (MNpath n φ φt t) 2 P := hB.memLp tN ht.2
  have hMi : Integrable (fun γ => MNpath n φ φt t γ ^ 2) P := hM2.integrable_sq
  have hQi : Integrable (QNpath n φ t) P := hB.integrable_bracket tN ht.2
  have hcond : P[fun γ => MNpath n φ φt t γ ^ 2 - QNpath n φ t γ |
      nullAug P (pathFiltrationCan T) 0] =ᵐ[P]
      fun γ => MNpath n φ φt 0 γ ^ 2 - QNpath n φ 0 γ := by
    have h := hB.condExp_sq 0 tN zero_le ht.2
    rw [NNReal.coe_zero] at h
    exact h
  have hM0 : ∀ᵐ γ ∂P, MNpath n φ φt 0 γ = 0 := by
    filter_upwards [hP.ae_dirac hn hT.le] with γ hγ
    simp only [MNpath, pairFM, hγ, integral_dirac, intervalIntegral.integral_same,
      sub_self]
  have hQ0 : ∀ γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), QNpath n φ 0 γ = 0 := fun γ => by simp [QNpath]
  have hint : ∫ γ, (MNpath n φ φt t γ ^ 2 - QNpath n φ t γ) ∂P = 0 := by
    rw [← integral_condExp ((nullAug P (pathFiltrationCan T)).le 0), integral_congr_ae hcond]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hM0] with γ hγ
    simp [hγ, hQ0]
  rw [integral_sub hMi hQi, sub_eq_zero] at hint
  have hQnn : ∀ γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), 0 ≤ QNpath n φ t γ := fun γ => by
    have := (continuousOn_monotoneOn_QNpath hn hφ γ).2 ⟨le_rfl, hT.le⟩ ⟨ht.1, ht.2⟩ ht.1
    simpa [hQ0] using this
  obtain ⟨-, -, hE1m, hE1⟩ := hP.prop_4_3_path hn hT.le
  have haN := constants_bounds hn
  have hbound : ∀ᵐ γ ∂P, ENNReal.ofReal (QNpath n φ t γ) ≤ ENNReal.ofReal (4 * C ^ 2) *
      ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) := by
    filter_upwards [hP.prop_3_1_path hn hT hφ] with γ hγ
    obtain ⟨-, hi1, hQ, -⟩ := hγ
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hQ 0 t le_rfl ht.1 ht.2
    rw [hQ0, sub_zero] at h1
    have hnn : ∀ s, 0 ≤ ENpath n γ s fun _ => 1 :=
      fun s => limMart_ENpath_one_nonneg n γ s (by linarith)
    have hle : ∫ s in (0 : ℝ)..t, ENpath n γ s (fun _ => 1) ≤
        ∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1 :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (ae_of_all _ fun s => hnn s) hi1
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..t, ENpath n γ s (fun _ => 1) :=
      intervalIntegral.integral_nonneg ht.1 fun s _ => hnn s
    have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
    calc QNpath n φ t γ ≤ 2 * C ^ 2 * (aN n * ∫ s in (0 : ℝ)..t, ENpath n γ s fun _ => 1) := h1
      _ ≤ 2 * C ^ 2 * (2 * ∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) := by
          gcongr
          all_goals linarith [haN.2.2.2.1, haN.2.2.2.2.1, haN.2.2.2.2.2]
      _ = 4 * C ^ 2 * ∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1 := by ring
  calc ∫⁻ γ, ENNReal.ofReal (MNpath n φ φt t γ ^ 2) ∂P
      = ENNReal.ofReal (∫ γ, MNpath n φ φt t γ ^ 2 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hMi (ae_of_all _ fun _ => sq_nonneg _)).symm
    _ = ∫⁻ γ, ENNReal.ofReal (QNpath n φ t γ) ∂P := by
        rw [hint]
        exact ofReal_integral_eq_lintegral_ofReal hQi (ae_of_all _ hQnn)
    _ ≤ ∫⁻ γ, ENNReal.ofReal (4 * C ^ 2) *
          ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) ∂P :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal (4 * C ^ 2) *
          ∫⁻ γ, ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) ∂P :=
        lintegral_const_mul _ hE1m
    _ ≤ ENNReal.ofReal (4 * C ^ 2) * ENNReal.ofReal (2 ^ (1 + 16 * T)) := by gcongr
    _ = ENNReal.ofReal (4 * C ^ 2 * 2 ^ (1 + 16 * T)) :=
        (ENNReal.ofReal_mul (by positivity)).symm

/-- Pointwise bound behind uniform integrability: `|f| 1_{|f| ≥ c} ≤ f²/c`. -/
private lemma limMart_enorm_indicator_le {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ) :
    ‖({x : ℝ | c ≤ ‖x‖₊}.indicator id a : ℝ)‖ₑ ≤ ENNReal.ofReal (a ^ 2) / c := by
  by_cases h : c ≤ ‖a‖₊
  · rw [indicator_of_mem (show a ∈ {x : ℝ | c ≤ ‖x‖₊} from h), id]
    have hsq : ENNReal.ofReal (a ^ 2) = ‖a‖ₑ * ‖a‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _), ← sq, sq_abs]
    rw [hsq, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hc)) (Or.inl ENNReal.coe_ne_top)]
    gcongr
    exact_mod_cast h
  · rw [indicator_of_notMem (show a ∉ {x : ℝ | c ≤ ‖x‖₊} from h), enorm_zero]
    exact zero_le

/-- **Vitali's convergence theorem, `L²`-bounded form**: if `f_j → g` almost surely and
`𝔼[f_j²] ≤ K < ∞`, then `g ∈ L²` and `𝔼[f_j] → 𝔼[g]`. -/
theorem limMart_tendsto_integral_of_sq_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ j, Measurable (f j)) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hfK : ∀ j, ∫⁻ ω, ENNReal.ofReal (f j ω ^ 2) ∂μ ≤ K)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun j => f j ω) atTop (𝓝 (g ω))) :
    MemLp g 2 μ ∧ Tendsto (fun j => ∫ ω, f j ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hf j).aestronglyMeasurable) hfg
  have hmem : ∀ j, MemLp (f j) 2 μ := fun j =>
    (memLp_two_iff_integrable_sq (hf j).aestronglyMeasurable).2
      ⟨((hf j).pow_const 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2
          ((hfK j).trans_lt hK.lt_top)⟩
  have hgK : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ ≤ K := by
    calc ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ
        = ∫⁻ ω, liminf (fun j => ENNReal.ofReal (f j ω ^ 2)) atTop ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfg] with ω hω
          exact (((ENNReal.continuous_ofReal.comp (continuous_pow 2)).tendsto _).comp
            hω).liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ ω, ENNReal.ofReal (f j ω ^ 2) ∂μ) atTop :=
          lintegral_liminf_le' fun j =>
            (ENNReal.measurable_ofReal.comp ((hf j).pow_const 2)).aemeasurable
      _ ≤ K := liminf_le_of_frequently_le' (Frequently.of_forall hfK)
  have hgmem : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg).2 ⟨hg.pow 2,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2 (hgK.trans_lt hK.lt_top)⟩
  refine ⟨hgmem, ?_⟩
  -- uniform integrability
  have hui : UnifIntegrable f 1 μ := by
    refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun j => (hf j).aestronglyMeasurable)
      fun ε hε => ?_
    have hlim : Tendsto (fun k : ℕ => K * ((k : ℝ≥0∞))⁻¹) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hK)
      rwa [mul_zero] at this
    obtain ⟨k, hk, hk1⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
      (eventually_ge_atTop 1)).exists
    have hc0 : ((k : ℝ≥0)) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    refine ⟨(k : ℝ≥0), fun j => ?_⟩
    have hind : {x | ((k : ℝ≥0)) ≤ ‖f j x‖₊}.indicator (f j) =
        fun x => {y : ℝ | ((k : ℝ≥0)) ≤ ‖y‖₊}.indicator id (f j x) := by
      funext x
      by_cases h : ((k : ℝ≥0)) ≤ ‖f j x‖₊
      · rw [indicator_of_mem (show x ∈ {x | ((k : ℝ≥0)) ≤ ‖f j x‖₊} from h),
          indicator_of_mem (show f j x ∈ {y : ℝ | ((k : ℝ≥0)) ≤ ‖y‖₊} from h), id]
      · rw [indicator_of_notMem (show x ∉ {x | ((k : ℝ≥0)) ≤ ‖f j x‖₊} from h),
          indicator_of_notMem (show f j x ∉ {y : ℝ | ((k : ℝ≥0)) ≤ ‖y‖₊} from h)]
    have hmeas : AEStronglyMeasurable
        (fun x => {y : ℝ | ((k : ℝ≥0)) ≤ ‖y‖₊}.indicator id (f j x)) μ :=
      ((measurable_id.indicator (measurableSet_le measurable_const measurable_nnnorm)).comp
        (hf j)).aestronglyMeasurable
    rw [hind, eLpNorm_one_eq_lintegral_enorm hmeas]
    calc ∫⁻ x, ‖{y : ℝ | ((k : ℝ≥0)) ≤ ‖y‖₊}.indicator id (f j x)‖ₑ ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal (f j x ^ 2) * ((k : ℝ≥0∞))⁻¹ ∂μ := by
          refine lintegral_mono fun x => ?_
          have := limMart_enorm_indicator_le hc0 (f j x)
          rwa [div_eq_mul_inv, ENNReal.coe_natCast] at this
      _ = (∫⁻ x, ENNReal.ofReal (f j x ^ 2) ∂μ) * ((k : ℝ≥0∞))⁻¹ :=
          lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast (show k ≠ 0 by omega)))
      _ ≤ K * ((k : ℝ≥0∞))⁻¹ := by gcongr; exact hfK j
      _ ≤ ε := hk.le
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun j => (hf j).aestronglyMeasurable) (hgmem.mono_exponent (by norm_num)) hui hfg
  exact tendsto_integral_of_L1' g (Eventually.of_forall fun j => (hmem j).integrable one_le_two)
    hL1

end QSSEPtoKPZ
