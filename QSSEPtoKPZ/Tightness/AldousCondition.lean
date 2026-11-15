/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.Tightness.AldousConditionAux

/-!
# Equation (5.2): Aldous' condition for `𝖹_n(·;φ)`

Statement: Stage 3, task T0' (`docs/stage3-design.md`, Section 3.3, decision D4'); proof:
task Q2.

The article proves (5.2), `lim_{δ→0} sup_n sup_{τ, s ≤ δ} ℙ(|𝖹_n(τ+s;φ) - 𝖹_n(τ;φ)| > η) = 0`,
through the bound `2 C δ / η + 4 C √δ / η²` of the end of the proof of Proposition 5.1. The
statement below keeps this quantitative form, because the tightness proof uses it:
`ℙ(|𝖹_n(τ+s;φ) - 𝖹_n(τ;φ)| > η) ≤ c (C s / η + C² √s / η²)` for `s ≤ 1/16`, with `c` depending
only on `T` and `C ≥ ‖φ‖_{1,3}`.

* `φ` is a time-independent function of `C_b³(ℝ)` with `‖φ‖_{1,3} ≤ C`, written
  `IsC13 1 (fun _ => φ) (fun _ _ => 0) C` (the article takes `φ ∈ C_c^∞(ℝ)`; its proof only
  uses `‖φ‖_{1,3}`).
* The stopping times are those of `𝓕ⁿ` augmented by the null sets (`nullAug`, decision D4 of
  Stage 2, as in Proposition 4.3), bounded by `T`.
* The constant `c` is quantified before the probability space (decision D8 of Stage 2).
* The conjunct "almost surely `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`" makes the series
  `𝖹_n(t;φ)` genuine ones (`φ` is bounded); otherwise Lean gives them the value `0`.
* The probability of the event is the outer probability (the event is not claimed measurable).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **Equation (5.2)** (Aldous' condition), in the quantitative form of the end of the proof of
Proposition 5.1. For every `T` there is a constant `c` such that, for every probability space,
Brownian family and wave function, every `n ≥ 1`, every `φ ∈ C_b³(ℝ)` with `‖φ‖_{1,3} ≤ C`, every
stopping time `τ ≤ T` of `𝓕ⁿ` augmented by the null sets, every `s ∈ [0, 1/16]` and `η > 0`:
almost surely `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`, and
`ℙ(|𝖹_n(τ+s;φ) - 𝖹_n(τ;φ)| > η) ≤ c (C s / η + C² √s / η²)` (outer probability). -/
theorem aldous_condition (T : ℝ) :
    ∃ c : ℝ, ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
      IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ →
      ∀ {n C : ℝ} {φ : ℝ → ℝ}, 1 ≤ n → IsC13 1 (fun _ => φ) (fun _ _ => 0) C →
      ∀ {τ : Ω → ℝ≥0}, IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)) →
      (∀ ω, (τ ω : ℝ) ≤ T) → ∀ {s η : ℝ}, 0 ≤ s → s ≤ 1 / 16 → 0 < η →
      (∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      μ {ω | η < |pairZ n ψ ω ((τ ω : ℝ) + s) φ - pairZ n ψ ω (τ ω) φ|} ≤
        ENNReal.ofReal (c * (C * s / η + C ^ 2 * Real.sqrt s / η ^ 2)) := by
  refine ⟨32 * (1 + 2 ^ (3 + 16 * (max T 0 + 1))), ?_⟩
  intro Ω mΩ 𝓕 μ _ B ψ hB hψ n C φ hn hφ τ hτ hτT s η hs hs' hη
  set T' : ℝ := max T 0 with hT'def
  set H : ℝ := T' + 1 with hHdef
  set K : ℝ := 2 ^ (3 + 16 * H) with hKdef
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hH0 : 0 < H := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hτT' : ∀ ω, (τ ω : ℝ) ≤ T' := fun ω => (hτT ω).trans (le_max_left _ _)
  have hτ0 : ∀ ω, (0 : ℝ) ≤ τ ω := fun ω => NNReal.coe_nonneg _
  have hsH : T' + s ≤ H := by linarith
  have hC : 0 ≤ C := aldousCond_C_nonneg hφ
  -- Proposition 3.1 on `[0, H]`, (4.8) on `[0, H]`, (4.9) at `τ`
  obtain ⟨hP1, hMB, hQW, -⟩ := prop_3_1 hB hψ hn hH0 (aldousCond_isC13_const hφ H)
  obtain ⟨-, hSm, hSint, -, -⟩ := prop_4_3_bounds hB hψ hn hH0.le
  obtain ⟨-, hIint, hIce⟩ := prop_4_3_increment hB hψ hn hτ
    ⟨T'.toNNReal, fun ω => by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hT'0]; exact hτT' ω⟩
    hs hs'
  obtain ⟨-, hWB, -⟩ := hasBracket_WN hB hψ hn hH0
  refine ⟨hP1.mono fun ω h => h.1, ?_⟩
  -- the supremum `S₂ = sup_{u ∈ [0,H]} 𝒲_n(u)²`
  set S2 : Ω → ℝ≥0∞ := fun ω => ⨆ u ∈ Set.Icc (0 : ℝ) H, ENNReal.ofReal (WN n ψ u ω ^ 2)
    with hS2def
  have hS2le : ∀ ω, ∀ u ∈ Set.Icc (0 : ℝ) H, ENNReal.ofReal (WN n ψ u ω ^ 2) ≤ S2 ω :=
    fun ω u hu => le_iSup₂ (f := fun u _ => ENNReal.ofReal (WN n ψ u ω ^ 2)) u hu
  have hS2fin : ∫⁻ ω, S2 ω ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSint
  have hS2lt : ∀ᵐ ω ∂μ, S2 ω < ∞ := ae_lt_top' hSm hS2fin
  -- the martingale increment
  set ΔM : Ω → ℝ := fun ω => MN n ψ (fun _ => φ) (fun _ _ => 0) (τ ω + s) ω -
    MN n ψ (fun _ => φ) (fun _ _ => 0) (τ ω) ω with hΔM
  set r : ℝ := η / 2 with hr
  have hr0 : 0 < r := by positivity
  -- Step 1: `|𝖹_n(τ+s;φ) - 𝖹_n(τ;φ)| ≤ |ΔM| + 2 C s sup_{[0,H]} 𝒲_n`
  have hincl : {ω | η < |pairZ n ψ ω ((τ ω : ℝ) + s) φ - pairZ n ψ ω (τ ω) φ|} ≤ᵐ[μ]
      ({ω | ENNReal.ofReal r ≤ ENNReal.ofReal (2 * C * s) * (1 + S2 ω)} ∪
        {ω | r < |ΔM ω|} : Set Ω) := by
    filter_upwards [hP1, hS2lt] with ω hω hfin hE
    obtain ⟨hsum, hII, -, -, -⟩ := hω
    have hE' : η < |pairZ n ψ ω ((τ ω : ℝ) + s) φ - pairZ n ψ ω (τ ω) φ| := hE
    set g : ℝ → ℝ := fun u => pairZ n ψ ω u
      (fun y => (fun (_ _ : ℝ) => (0 : ℝ)) u y + AN n ((fun _ => φ) u) y) with hg
    have hsub : ∀ a : ℝ, 0 ≤ a → a ≤ H → IntervalIntegrable g MeasureTheory.volume 0 a :=
      fun a h0 h1 => hII.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.2 (Or.inl ⟨h0, h1⟩)))
    have hid : pairZ n ψ ω ((τ ω : ℝ) + s) φ - pairZ n ψ ω (τ ω) φ =
        ΔM ω + ∫ u in (τ ω : ℝ)..(τ ω + s), g u := by
      rw [← intervalIntegral.integral_interval_sub_left (hsub _ (by linarith [hτ0 ω])
        (by linarith [hτT' ω])) (hsub _ (hτ0 ω) (by linarith [hτT' ω]))]
      simp only [hΔM, MN, hg]
      ring
    set m : ℝ := (S2 ω).toReal with hm
    have hWm : ∀ u ∈ Set.Icc (0 : ℝ) H, WN n ψ u ω ≤ 1 + m := fun u hu => by
      have h1 : WN n ψ u ω ^ 2 ≤ m :=
        (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 (hS2le ω u hu)
      nlinarith [sq_nonneg (WN n ψ u ω - 1)]
    have hD : |∫ u in (τ ω : ℝ)..(τ ω + s), g u| ≤ 2 * C * (1 + m) * s := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (τ ω : ℝ))
        (b := τ ω + s) (f := g) (C := 2 * C * (1 + m)) (fun u hu => by
          rw [Set.uIoc_of_le (by linarith)] at hu
          have hu' : u ∈ Set.Icc (0 : ℝ) H :=
            ⟨by linarith [hu.1, hτ0 ω], by linarith [hu.2, hτT' ω]⟩
          rw [Real.norm_eq_abs]
          refine (aldousCond_abs_pairZ_le (hsum u hu'.1) (K := 2 * C) fun y => ?_).trans ?_
          · simpa only [zero_add] using aldousCond_abs_AN_le hn hφ y
          · exact mul_le_mul_of_nonneg_left (hWm u hu') (by positivity))
      rwa [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hs] at this
    by_cases hM : r < |ΔM ω|
    · exact Or.inr hM
    · left
      show ENNReal.ofReal r ≤ ENNReal.ofReal (2 * C * s) * (1 + S2 ω)
      rw [hid] at hE'
      have h1 := abs_add_le (ΔM ω) (∫ u in (τ ω : ℝ)..(τ ω + s), g u)
      have hS2 : S2 ω = ENNReal.ofReal m := (ENNReal.ofReal_toReal hfin.ne).symm
      have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
      rw [hS2, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hm0,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      push Not at hM
      nlinarith
  -- Step 2: the drift term, by Markov's inequality and (4.8)
  have hA1 : μ {ω | ENNReal.ofReal r ≤ ENNReal.ofReal (2 * C * s) * (1 + S2 ω)} ≤
      ENNReal.ofReal (2 * C * s * (1 + K) / r) := by
    refine (meas_ge_le_lintegral_div ((aemeasurable_const.add hSm).const_mul _)
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp only [Pi.add_apply]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      ENNReal.ofReal_div_of_pos hr0,
      ENNReal.ofReal_mul (p := 2 * C * s) (q := 1 + K) (by positivity),
      ENNReal.ofReal_add zero_le_one hK0, ENNReal.ofReal_one]
    gcongr
  -- Step 3: the martingale term, by optional sampling, Prop. 3.1 (2), (4.9) and Chebyshev
  obtain ⟨hΔMm, hΔM2, hΔQ, hΔeq⟩ := aldousCond_sq_increment (hMB.mono_horizon hsH) hT'0 hs hτ
    hτT'
  have hWτm : AEStronglyMeasurable (fun ω => WN n ψ (τ ω) ω) μ :=
    (aestronglyMeasurable_stoppedAt hWB.cont (fun t ht =>
      aestronglyMeasurable_of_condExp_eq_self (hWB.condExp t t le_rfl ht)) hτ
      (fun ω => by linarith [hτT' ω])).mono hτ.measurableSpace_le
  have hWτle : ∀ ω, ENNReal.ofReal (WN n ψ (τ ω) ω ^ 2) ≤ S2 ω :=
    fun ω => hS2le ω _ ⟨hτ0 ω, by linarith [hτT' ω]⟩
  have hWτ2 : Integrable (fun ω => WN n ψ (τ ω) ω ^ 2) μ :=
    integrable_of_enorm_le_lintegral (hWτm.pow 2) hS2fin (ae_of_all _ fun ω => by
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]; exact hWτle ω)
  have hWτK : ∫ ω, WN n ψ (τ ω) ω ^ 2 ∂μ ≤ K := by
    have h1 : ENNReal.ofReal (∫ ω, WN n ψ (τ ω) ω ^ 2 ∂μ) ≤ ENNReal.ofReal K := by
      rw [ofReal_integral_eq_lintegral_ofReal hWτ2 (ae_of_all _ fun ω => sq_nonneg _)]
      exact (lintegral_mono hWτle).trans hSint
    exact (ENNReal.ofReal_le_ofReal_iff hK0).1 h1
  have hint : ∫ ω, ΔM ω ^ 2 ∂μ ≤ 8 * C ^ 2 * Real.sqrt s * K := by
    have e1 : ∫ ω, ΔM ω ^ 2 ∂μ = ∫ ω, (QN n ψ (fun _ => φ) (τ ω + s) ω -
        QN n ψ (fun _ => φ) (τ ω) ω) ∂μ := hΔeq
    rw [e1]
    calc ∫ ω, (QN n ψ (fun _ => φ) (τ ω + s) ω - QN n ψ (fun _ => φ) (τ ω) ω) ∂μ
        ≤ ∫ ω, 2 * C ^ 2 * (aN n * ∫ r in (τ ω : ℝ)..(τ ω + s), EN n ψ ω r fun _ => 1) ∂μ := by
          refine integral_mono_ae hΔQ (hIint.const_mul _) ?_
          filter_upwards [hQW] with ω hω
          exact hω _ _ (hτ0 ω) (by linarith) (by linarith [hτT' ω])
      _ = 2 * C ^ 2 * ∫ ω, (aN n * ∫ r in (τ ω : ℝ)..(τ ω + s), EN n ψ ω r fun _ => 1) ∂μ :=
          integral_const_mul _ _
      _ ≤ 2 * C ^ 2 * ∫ ω, 4 * Real.sqrt s * WN n ψ (τ ω) ω ^ 2 ∂μ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← integral_condExp hτ.measurableSpace_le]
          exact integral_mono_ae integrable_condExp (hWτ2.const_mul _) hIce
      _ = 2 * C ^ 2 * (4 * Real.sqrt s * ∫ ω, WN n ψ (τ ω) ω ^ 2 ∂μ) := by
          rw [integral_const_mul]
      _ ≤ 2 * C ^ 2 * (4 * Real.sqrt s * K) := by gcongr
      _ = 8 * C ^ 2 * Real.sqrt s * K := by ring
  have hA2 : μ {ω | r < |ΔM ω|} ≤ ENNReal.ofReal (8 * C ^ 2 * Real.sqrt s * K / r ^ 2) :=
    (aldousCond_measure_lt_abs_le hΔMm hΔM2 hr0).trans
      (ENNReal.ofReal_le_ofReal (by gcongr))
  -- Step 4: conclusion
  refine (measure_mono_ae hincl).trans ((measure_union_le _ _).trans
    ((add_le_add hA1 hA2).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have ha : 0 ≤ C * s / η := by positivity
  have hb : 0 ≤ C ^ 2 * Real.sqrt s / η ^ 2 := by positivity
  have e1 : 2 * C * s * (1 + K) / r = 4 * (1 + K) * (C * s / η) := by
    rw [hr]; field_simp; ring
  have e2 : 8 * C ^ 2 * Real.sqrt s * K / r ^ 2 = 32 * K * (C ^ 2 * Real.sqrt s / η ^ 2) := by
    rw [hr]; field_simp; ring
  rw [e1, e2]
  nlinarith


end QSSEPtoKPZ
