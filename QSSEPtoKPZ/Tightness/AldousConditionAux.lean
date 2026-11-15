/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Martingales
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.SecondMoments.TotalMass
public import QSSEPtoKPZ.Martingales.Stopping

/-!
# Auxiliary results for equation (5.2) (task Q2)

* `aldousCond_isC13_const`: a time-independent `φ ∈ C_b³(ℝ)` with `‖φ‖_{1,3} ≤ C` on the
  horizon `1` has `‖φ‖_{1,3} ≤ C` on every horizon `T`;
* `aldousCond_C_nonneg`, `aldousCond_abs_AN_le`: `C ≥ 0` and `‖𝒜_n φ‖_∞ ≤ 2 C` (from
  Proposition 3.1 (1));
* `aldousCond_abs_pairZ_le`: `|𝖹_n(t;f)| ≤ K 𝒲_n(t)` for `|f| ≤ K`;
* `aldousCond_measure_lt_abs_le`: Chebyshev's inequality `ℙ(|X| > r) ≤ 𝔼[X²] / r²`;
* `aldousCond_sq_increment`: for `⟨M⟩ = A`, a stopping time `τ ≤ T` and `s ≥ 0`,
  `𝔼[(M_{τ+s} - M_τ)²] = 𝔼[A_{τ+s} - A_τ]` (optional sampling for `M` and for `M² - A`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Test functions -/

/-- A time-independent `φ ∈ C_b³(ℝ)` with `‖φ‖_{1,3} ≤ C` (on the horizon `1`) satisfies
`‖φ‖_{1,3} ≤ C` on every horizon `T`. -/
theorem aldousCond_isC13_const {C : ℝ} {φ : ℝ → ℝ} (hφ : IsC13 1 (fun _ => φ) (fun _ _ => 0) C)
    (T : ℝ) : IsC13 T (fun _ => φ) (fun _ _ => 0) C := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hcd : ContDiff ℝ 3 φ := hφ.contDiff 0 h0
  obtain ⟨c, hcs, hc⟩ := hφ.bound
  refine ⟨fun _ _ => hcd, fun x t _ => hasDerivWithinAt_const _ _ _,
    ⟨continuousOn_const, fun k hk => ?_⟩, ⟨c, hcs, fun t _ x => hc 0 h0 x⟩⟩
  exact ((hcd.continuous_iteratedDeriv k (by exact_mod_cast hk)).comp
    continuous_snd).continuousOn

/-- The constant `C` of `‖φ‖_{1,3} ≤ C` is nonnegative. -/
theorem aldousCond_C_nonneg {C : ℝ} {φ : ℝ → ℝ} (hφ : IsC13 1 (fun _ => φ) (fun _ _ => 0) C) :
    0 ≤ C := by
  obtain ⟨c, hcs, hc⟩ := hφ.bound
  have hb := hc 0 ⟨le_rfl, zero_le_one⟩ 0
  simp only [Fin.sum_univ_five] at hcs
  linarith [(abs_nonneg _).trans hb.1, (abs_nonneg _).trans hb.2.1,
    (abs_nonneg _).trans hb.2.2.1, (abs_nonneg _).trans hb.2.2.2.1,
    (abs_nonneg _).trans hb.2.2.2.2]

/-- `‖𝒜_n φ‖_∞ ≤ 2 ‖φ‖_{1,3}` (proof of Proposition 5.1), from Proposition 3.1 (1):
`|𝒜_n φ| ≤ |𝒜_n φ - φ''/2| + |φ''|/2 ≤ n^{-1/4} C + C/2`. -/
theorem aldousCond_abs_AN_le {n C : ℝ} (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hφ : IsC13 1 (fun _ => φ) (fun _ _ => 0) C) (y : ℝ) : |AN n φ y| ≤ 2 * C := by
  have h1 := prop_3_1_generator hn hφ y
  have hC := aldousCond_C_nonneg hφ
  obtain ⟨c, hcs, hc⟩ := hφ.bound
  have hb := hc 0 ⟨le_rfl, zero_le_one⟩ y
  simp only [Fin.sum_univ_five] at hcs
  have hq : n ^ (-1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hqC : n ^ (-1 / 4 : ℝ) * C ≤ C := by nlinarith
  have h2 : |iteratedDeriv 2 φ y / 2| ≤ C / 2 := by
    rw [abs_div, abs_two]
    have := hb.2.2.2.1
    linarith [(abs_nonneg _).trans hb.1, (abs_nonneg _).trans hb.2.1,
      (abs_nonneg _).trans hb.2.2.1, (abs_nonneg _).trans hb.2.2.2.2]
  have h3 := abs_sub_abs_le_abs_sub (AN n φ y) (iteratedDeriv 2 φ y / 2)
  linarith

/-- `|𝖹_n(t;f)| ≤ K 𝒲_n(t)` if `∑ₓ 𝔷_n(t,x)` converges and `|f| ≤ K`. -/
theorem aldousCond_abs_pairZ_le {n t K : ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hs : Summable (zN n ψ ω t)) {f : ℝ → ℝ} (hf : ∀ y, |f y| ≤ K) :
    |pairZ n ψ ω t f| ≤ K * WN n ψ t ω := by
  rw [totalMass_WN_eq, ← tsum_mul_left, ← Real.norm_eq_abs]
  have hz0 := totalMass_zN_nonneg n ψ ω t
  refine tsum_of_norm_bounded (hs.mul_left K).hasSum fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hz0 x), mul_comm K]
  exact mul_le_mul_of_nonneg_left (hf _) (hz0 x)

/-! ### Chebyshev's inequality -/

/-- **Chebyshev's inequality**: `ℙ(|X| > r) ≤ 𝔼[X²] / r²` for `r > 0`. -/
theorem aldousCond_measure_lt_abs_le {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) {r : ℝ} (hr : 0 < r) :
    μ {ω | r < |X ω|} ≤ ENNReal.ofReal ((∫ ω, X ω ^ 2 ∂μ) / r ^ 2) := by
  have hsub : {ω | r < |X ω|} ⊆ {ω | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (X ω ^ 2)} := by
    intro ω hω
    have hω' : r < |X ω| := hω
    show ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (X ω ^ 2)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← sq_abs (X ω)]
    nlinarith
  have hr2 : 0 < r ^ 2 := by positivity
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
    (hX.aemeasurable.pow_const 2).ennreal_ofReal (ENNReal.ofReal_pos.2 hr2).ne'
    ENNReal.ofReal_ne_top).trans ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hX2 (ae_of_all _ fun ω => sq_nonneg _),
    ← ENNReal.ofReal_div_of_pos hr2]

/-! ### Second moment of a martingale increment after a stopping time -/

/-- **Increment of a martingale after a stopping time.** If `⟨M⟩ = A` on `[0, T + s]`
(`T, s ≥ 0`) and `τ ≤ T` is a stopping time of the augmented filtration, then
`M_{τ+s} - M_τ` is a.e. strongly measurable, `(M_{τ+s} - M_τ)²` and `A_{τ+s} - A_τ` are
integrable, and `𝔼[(M_{τ+s} - M_τ)²] = 𝔼[A_{τ+s} - A_τ]`. Proof: optional sampling
`𝔼[M_{τ+s} | 𝓕_τ] = M_τ` and `𝔼[M_{τ+s}² - A_{τ+s} | 𝓕_τ] = M_τ² - A_τ`. -/
theorem aldousCond_sq_increment [IsFiniteMeasure μ] {T s : ℝ} {M A : ℝ → Ω → ℝ}
    (h : HasBracket (T + s) 𝓕 M A μ) (hT : 0 ≤ T) (hs : 0 ≤ s) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    AEStronglyMeasurable (fun ω => M (τ ω + s) ω - M (τ ω) ω) μ ∧
    Integrable (fun ω => (M (τ ω + s) ω - M (τ ω) ω) ^ 2) μ ∧
    Integrable (fun ω => A (τ ω + s) ω - A (τ ω) ω) μ ∧
    ∫ ω, (M (τ ω + s) ω - M (τ ω) ω) ^ 2 ∂μ = ∫ ω, (A (τ ω + s) ω - A (τ ω) ω) ∂μ := by
  have hM := h.toIsCL2Mart
  have hTs : 0 ≤ T + s := by linarith
  have hss : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  have hτT' : ∀ ω, (τ ω : ℝ) ≤ T + s := fun ω => by linarith [hτT ω]
  have hmemτ : ∀ ω, (τ ω : ℝ) ∈ Set.Icc (0 : ℝ) (T + s) := fun ω => ⟨(τ ω).2, hτT' ω⟩
  have hmemτs : ∀ ω, (τ ω : ℝ) + s ∈ Set.Icc (0 : ℝ) (T + s) := fun ω =>
    ⟨by linarith [NNReal.coe_nonneg (τ ω)], by linarith [hτT ω]⟩
  -- the stopping time `τ + s`
  have hρ := isStoppingTime_comp_of_monotone hτ (F := fun x => x + s.toNNReal)
    (fun a b h => add_le_add_left h _) (fun x => le_self_add)
  have hρT : ∀ ω, ((τ ω + s.toNNReal : ℝ≥0) : ℝ) ≤ T + s := fun ω => by
    rw [NNReal.coe_add, hss]; linarith [hτT ω]
  -- adaptedness
  have hMm : ∀ t : ℝ≥0, (t : ℝ) ≤ T + s → AEStronglyMeasurable[𝓕 t] (M t) μ := fun t ht =>
    aestronglyMeasurable_of_condExp_eq_self (h.condExp t t le_rfl ht)
  have hAm : ∀ t : ℝ≥0, (t : ℝ) ≤ T + s → AEStronglyMeasurable[𝓕 t] (A t) μ :=
    totalMass_bracket_adapted h
  -- measurability of the four stopped values
  have ha : AEStronglyMeasurable (fun ω => M (τ ω + s) ω) μ :=
    totalMass_aesm_stopped_add hs h.cont hMm hτ hτT
  have hα : AEStronglyMeasurable (fun ω => A (τ ω + s) ω) μ :=
    totalMass_aesm_stopped_add hs h.cont_bracket hAm hτ hτT
  have hbτ : AEStronglyMeasurable[hτ.measurableSpace] (fun ω => M (τ ω) ω) μ :=
    aestronglyMeasurable_stoppedAt h.cont hMm hτ hτT'
  have hb : AEStronglyMeasurable (fun ω => M (τ ω) ω) μ := hbτ.mono hτ.measurableSpace_le
  have hβ : AEStronglyMeasurable (fun ω => A (τ ω) ω) μ :=
    (aestronglyMeasurable_stoppedAt h.cont_bracket hAm hτ hτT').mono hτ.measurableSpace_le
  -- domination
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) (T + s), ENNReal.ofReal (M t ω ^ 2)
    with hSdef
  have hS : ∫⁻ ω, S ω ∂μ ≠ ∞ := totalMass_lintegral_iSup_sq_ne_top hM hTs
  have hSle : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) (T + s), ENNReal.ofReal (M t ω ^ 2) ≤ S ω :=
    fun ω t ht => le_iSup₂ (f := fun t _ => ENNReal.ofReal (M t ω ^ 2)) t ht
  have ha2 : Integrable (fun ω => M (τ ω + s) ω ^ 2) μ :=
    integrable_of_enorm_le_lintegral (ha.pow 2) hS (ae_of_all _ fun ω => by
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]; exact hSle ω _ (hmemτs ω))
  have hb2 : Integrable (fun ω => M (τ ω) ω ^ 2) μ :=
    integrable_of_enorm_le_lintegral (hb.pow 2) hS (ae_of_all _ fun ω => by
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]; exact hSle ω _ (hmemτ ω))
  have haL : MemLp (fun ω => M (τ ω + s) ω) 2 μ := (memLp_two_iff_integrable_sq ha).2 ha2
  have hbL : MemLp (fun ω => M (τ ω) ω) 2 μ := (memLp_two_iff_integrable_sq hb).2 hb2
  have ha1 : Integrable (fun ω => M (τ ω + s) ω) μ := haL.integrable one_le_two
  have hab : Integrable (fun ω => M (τ ω + s) ω * M (τ ω) ω) μ := by
    have e : (fun ω => M (τ ω + s) ω * M (τ ω) ω) = fun ω =>
        ((M (τ ω + s) ω + M (τ ω) ω) ^ 2 - M (τ ω + s) ω ^ 2 - M (τ ω) ω ^ 2) / 2 := by
      funext ω; ring
    have hsum : Integrable (fun ω => (M (τ ω + s) ω + M (τ ω) ω) ^ 2) μ :=
      (memLp_two_iff_integrable_sq (ha.add hb)).1 (haL.add hbL)
    rw [e]
    exact ((hsum.sub ha2).sub hb2).div_const 2
  have hAT : Integrable (A (T + s)) μ := h.integrable_bracket ⟨T + s, hTs⟩ le_rfl
  have hAb := totalMass_bracket_bounds h hTs
  have hα1 : Integrable (fun ω => A (τ ω + s) ω) μ := by
    refine hAT.mono' hα ?_
    filter_upwards [hAb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hω _ (hmemτs ω)).1]
    exact (hω _ (hmemτs ω)).2
  have hβ1 : Integrable (fun ω => A (τ ω) ω) μ := by
    refine hAT.mono' hβ ?_
    filter_upwards [hAb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hω _ (hmemτ ω)).1]
    exact (hω _ (hmemτ ω)).2
  -- optional sampling for `M`
  have h1 := hM.condExp_stopped (σ := τ) (τ := fun ω => τ ω + s.toNNReal) hτ hρ
    (fun ω => le_self_add) hρT
  simp only [NNReal.coe_add, hss] at h1
  -- optional sampling for `M² - A`
  have hmaps : Set.MapsTo (fun t : ℝ => t + s) (Set.Icc 0 T) (Set.Icc 0 (T + s)) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIcc : Set.Icc (0 : ℝ) T ⊆ Set.Icc 0 (T + s) :=
    Set.Icc_subset_Icc_right (by linarith)
  have hcoe : ∀ t : ℝ≥0, ((t + s.toNNReal : ℝ≥0) : ℝ) = t + s := fun t => by
    rw [NNReal.coe_add, hss]
  have h2 := condExp_stopped_of_forall (𝓕 := 𝓕) (T := T)
    (V := fun t ω => M (t + s) ω ^ 2 - A (t + s) ω) (Y := fun t ω => M t ω ^ 2 - A t ω)
    (by
      filter_upwards [h.cont, h.cont_bracket] with ω h1 h2
      have c1 : ContinuousOn (fun t => M (t + s) ω) (Set.Icc 0 T) :=
        h1.comp (continuousOn_id.add continuousOn_const) hmaps
      have c2 : ContinuousOn (fun t => A (t + s) ω) (Set.Icc 0 T) :=
        h2.comp (continuousOn_id.add continuousOn_const) hmaps
      exact (c1.pow 2).sub c2)
    (by
      filter_upwards [h.cont, h.cont_bracket] with ω h1 h2
      exact ((h1.mono hIcc).pow 2).sub (h2.mono hIcc))
    (fun t ht => by
      have hts : ((t + s.toNNReal : ℝ≥0) : ℝ) ≤ T + s := by rw [hcoe]; linarith
      have := ((h.memLp _ hts).aestronglyMeasurable.pow 2).sub
        (h.integrable_bracket _ hts).aestronglyMeasurable
      rw [hcoe] at this
      exact this)
    (by
      refine ne_top_of_le_ne_top (?_ : ∫⁻ ω, 2 * S ω + ENNReal.ofReal (2 * A (T + s) ω) ∂μ ≠ ∞)
        (lintegral_mono_ae ?_)
      · rw [lintegral_add_right' _ (hAT.const_mul 2).aemeasurable.ennreal_ofReal,
          lintegral_const_mul' _ _ (by simp)]
        exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hS,
          (hAT.const_mul 2).lintegral_lt_top.ne⟩
      · filter_upwards [hAb] with ω hω
        refine iSup₂_le fun t ht => ?_
        have ht1 : t + s ∈ Set.Icc (0 : ℝ) (T + s) := hmaps ht
        have ht2 : t ∈ Set.Icc (0 : ℝ) (T + s) := hIcc ht
        obtain ⟨p1, p2⟩ := hω _ ht1
        obtain ⟨q1, q2⟩ := hω _ ht2
        have e1 : |M (t + s) ω ^ 2 - A (t + s) ω| ≤ M (t + s) ω ^ 2 + A (T + s) ω := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (M (t + s) ω)]
        have e2 : |M t ω ^ 2 - A t ω| ≤ M t ω ^ 2 + A (T + s) ω := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (M t ω)]
        calc ENNReal.ofReal (|M (t + s) ω ^ 2 - A (t + s) ω| + |M t ω ^ 2 - A t ω|)
            ≤ ENNReal.ofReal (M (t + s) ω ^ 2 + M t ω ^ 2 + 2 * A (T + s) ω) :=
              ENNReal.ofReal_le_ofReal (by linarith)
          _ = ENNReal.ofReal (M (t + s) ω ^ 2) + ENNReal.ofReal (M t ω ^ 2) +
                ENNReal.ofReal (2 * A (T + s) ω) := by
              rw [ENNReal.ofReal_add (by positivity) (by linarith),
                ENNReal.ofReal_add (by positivity) (by positivity)]
          _ ≤ S ω + S ω + ENNReal.ofReal (2 * A (T + s) ω) := by
              gcongr
              · exact hSle ω _ ht1
              · exact hSle ω _ ht2
          _ = 2 * S ω + ENNReal.ofReal (2 * A (T + s) ω) := by rw [two_mul (S ω)])
    (fun t ht => by
      have hts : ((t + s.toNNReal : ℝ≥0) : ℝ) ≤ T + s := by rw [hcoe]; linarith
      have := h.condExp_sq t (t + s.toNNReal) le_self_add hts
      rw [hcoe] at this
      exact this)
    hτ hτT
  -- the integrals
  have hm := hτ.measurableSpace_le
  have I2 : ∫ ω, (M (τ ω + s) ω ^ 2 - A (τ ω + s) ω) ∂μ =
      ∫ ω, (M (τ ω) ω ^ 2 - A (τ ω) ω) ∂μ := by
    rw [← integral_condExp (μ := μ) (f := fun ω => M (τ ω + s) ω ^ 2 - A (τ ω + s) ω) hm]
    exact integral_congr_ae h2
  have I1 : ∫ ω, M (τ ω + s) ω * M (τ ω) ω ∂μ = ∫ ω, M (τ ω) ω * M (τ ω) ω ∂μ := by
    have hpull := condExp_mul_of_aestronglyMeasurable_right (m := hτ.measurableSpace) (μ := μ)
      (f := fun ω => M (τ ω + s) ω) hbτ hab ha1
    rw [← integral_condExp (μ := μ) (f := fun ω => M (τ ω + s) ω * M (τ ω) ω) hm]
    refine integral_congr_ae (hpull.trans ?_)
    filter_upwards [h1] with ω hω
    simp only [Pi.mul_apply, hω]
  have i1 : Integrable (fun ω => M (τ ω + s) ω ^ 2 - A (τ ω + s) ω) μ := ha2.sub hα1
  have i2 : Integrable (fun ω => M (τ ω) ω ^ 2 - A (τ ω) ω) μ := hb2.sub hβ1
  have i3 : Integrable (fun ω => M (τ ω) ω * M (τ ω) ω) μ := by
    simpa only [sq] using hb2
  have i4 : Integrable (fun ω => M (τ ω + s) ω * M (τ ω) ω - M (τ ω) ω * M (τ ω) ω) μ :=
    hab.sub i3
  have i5 : Integrable (fun ω => A (τ ω + s) ω - A (τ ω) ω) μ := hα1.sub hβ1
  have E1 : ∫ ω, ((M (τ ω + s) ω ^ 2 - A (τ ω + s) ω) - (M (τ ω) ω ^ 2 - A (τ ω) ω)) ∂μ = 0 := by
    rw [integral_sub i1 i2, I2, sub_self]
  have E2 : ∫ ω, (M (τ ω + s) ω * M (τ ω) ω - M (τ ω) ω * M (τ ω) ω) ∂μ = 0 := by
    rw [integral_sub hab i3, I1, sub_self]
  have e : (fun ω => (M (τ ω + s) ω - M (τ ω) ω) ^ 2) = fun ω =>
      (((M (τ ω + s) ω ^ 2 - A (τ ω + s) ω) - (M (τ ω) ω ^ 2 - A (τ ω) ω)) -
        2 * (M (τ ω + s) ω * M (τ ω) ω - M (τ ω) ω * M (τ ω) ω)) +
        (A (τ ω + s) ω - A (τ ω) ω) := by
    funext ω; ring
  refine ⟨ha.sub hb, ?_, i5, ?_⟩
  · rw [e]; exact ((i1.sub i2).sub (i4.const_mul 2)).add i5
  · have j1 := integral_add ((i1.sub i2).sub (i4.const_mul 2)) i5
    have j2 := integral_sub (i1.sub i2) (i4.const_mul 2)
    simp only [Pi.sub_apply] at j1 j2
    rw [e, j1, j2, integral_const_mul, E1, E2]
    ring

end QSSEPtoKPZ
