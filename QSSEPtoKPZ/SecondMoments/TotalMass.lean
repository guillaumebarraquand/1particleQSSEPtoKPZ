/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.SecondMoments.FeynmanKac
public import QSSEPtoKPZ.SecondMoments.TotalMassAux

/-!
# Proposition 4.3: the total mass `𝒲_n`

Statements: Stage 2, task T0; proofs: task F1 (auxiliary results in `TotalMassAux.lean`).
The function `u_n` is `uN` of Stage 1 (`SecondMoments/FeynmanKac.lean`).

Stopping times are `ℝ≥0`-valued, bounded, and are stopping times of the filtration `𝓕ⁿ`
augmented by the null sets (`nullAug`, decision D4 of `docs/stage2-design.md`); `hτ.measurableSpace`
is the σ-algebra `𝓕ⁿ_τ` of the events prior to `τ` (for that filtration).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Proposition 4.3 (1)**, equation (4.7), for deterministic times: for `n ≥ 1` and `s, t ≥ 0`,
almost surely `∑ₓ 𝔷_n(r,x)` converges for all `r ≥ 0`; the family
`𝔷_n(t,x₁) 𝔷_n(t,x₂) u_n(s,x₂-x₁)` is almost surely summable over `(x₁,x₂) ∈ ℤ²`; `𝒲_n(t+s)²` is
integrable; and
`𝔼[𝒲_n(t+s)² | 𝓕ⁿ_t] = ∑_{x₁,x₂ ∈ ℤ} 𝔷_n(t,x₁) 𝔷_n(t,x₂) u_n(s,x₂-x₁)` almost surely. -/
theorem prop_4_3_condSecondMoment (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) (t s : ℝ≥0) :
    (∀ᵐ ω ∂μ, (∀ r : ℝ, 0 ≤ r → Summable (zN n ψ ω r)) ∧
      Summable (fun p : ℤ × ℤ => zN n ψ ω t p.1 * zN n ψ ω t p.2 * uN n s (p.2 - p.1))) ∧
    Integrable (fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2) μ ∧
    μ[fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2 | filtN n 𝓕 t] =ᵐ[μ]
      fun ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * uN n s (x₂ - x₁) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) + s := by positivity
  obtain ⟨hsum, hM⟩ := totalMass_isCL2Mart_rev hB hψ hn ht0
  have hu : ∀ r, |uN n s r| ≤ (2 : ℝ) ^ (1 + 16 * (s : ℝ)) := fun r => by
    obtain ⟨h1, h2⟩ := uN_bounds hn (NNReal.coe_nonneg s) r
    rw [abs_of_nonneg (by linarith)]; exact h2
  have hts : ((t + s : ℝ≥0) : ℝ) ≤ (t : ℝ) + s + 1 := by push_cast; linarith
  -- the martingale at time `t + s` is `𝒲_n(t+s)² - u_n(t+s, 0)`, since `u_n(0, ·) = 1`
  have hend : (fun ω => pairZ2 n ψ ω ((t + s : ℝ≥0) : ℝ)
      (fun x₁ x₂ => uN n ((t : ℝ) + s - ((t + s : ℝ≥0) : ℝ)) (x₂ - x₁)) - uN n ((t : ℝ) + s) 0) =
      fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2 - uN n ((t : ℝ) + s) 0 := by
    funext ω
    rw [NNReal.coe_add, sub_self, uN_zero, totalMass_WN_eq]
    simp only [pairZ2, lp.infty_coeFn_one, Pi.one_apply, totalMass_tsum_const, one_mul]
  have hXi : Integrable (fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2 - uN n ((t : ℝ) + s) 0) μ := by
    rw [← hend]; exact (hM.memLp (t + s) hts).integrable one_le_two
  have hWi : Integrable (fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2) μ := by
    refine (hXi.add (integrable_const (uN n ((t : ℝ) + s) 0))).congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  refine ⟨?_, hWi, ?_⟩
  · filter_upwards [hsum] with ω hω
    exact ⟨hω, totalMass_summable_prod (hω t t.2) (totalMass_zN_nonneg n ψ ω t) hu⟩
  · have hce := hM.condExp t (t + s) le_self_add hts
    have hm := (filtN n 𝓕).le t
    have hce' : μ[fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2 - uN n ((t : ℝ) + s) 0 | filtN n 𝓕 t]
        =ᵐ[μ] fun ω => pairZ2 n ψ ω t (fun x₁ x₂ => uN n s (x₂ - x₁)) - uN n ((t : ℝ) + s) 0 := by
      rw [← hend]; simpa only [add_sub_cancel_left] using hce
    have e1 : (fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2) =
        (fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2 - uN n ((t : ℝ) + s) 0) +
          fun _ => uN n ((t : ℝ) + s) 0 := by
      funext ω; simp
    rw [e1]
    refine (condExp_add hXi (integrable_const _) _).trans ?_
    rw [condExp_const hm]
    filter_upwards [hce'] with ω hω
    simp only [Pi.add_apply, hω, pairZ2]
    ring

/-- **Proposition 4.3 (1)**, equation (4.7), at a bounded stopping time `τ` (last sentence of
item (1)): for `n ≥ 1` and `s ≥ 0`, the same statement as `prop_4_3_condSecondMoment` with `t`
replaced by `τ` and `𝓕ⁿ_t` by `𝓕ⁿ_τ`. -/
theorem prop_4_3_condSecondMoment_stopping (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T) {s : ℝ} (hs : 0 ≤ s) :
    (∀ᵐ ω ∂μ, (∀ r : ℝ, 0 ≤ r → Summable (zN n ψ ω r)) ∧
      Summable (fun p : ℤ × ℤ => zN n ψ ω (τ ω) p.1 * zN n ψ ω (τ ω) p.2 * uN n s (p.2 - p.1))) ∧
    Integrable (fun ω => WN n ψ (τ ω + s) ω ^ 2) μ ∧
    μ[fun ω => WN n ψ (τ ω + s) ω ^ 2 | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ,
        zN n ψ ω (τ ω) x₁ * zN n ψ ω (τ ω) x₂ * uN n s (x₂ - x₁) := by
  obtain ⟨T0, hT0⟩ := hτb
  have hτT : ∀ ω, (τ ω : ℝ) ≤ T0 := fun ω => NNReal.coe_le_coe.2 (hT0 ω)
  have hT00 : (0 : ℝ) ≤ T0 := T0.2
  have hss : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  have hdet : ∀ t : ℝ≥0, Integrable (fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2) μ ∧
      μ[fun ω => WN n ψ ((t : ℝ) + s) ω ^ 2 | filtN n 𝓕 t] =ᵐ[μ]
        fun ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * uN n s (x₂ - x₁) :=
    fun t => by
      have h := prop_4_3_condSecondMoment hB hψ hn t s.toNNReal
      rw [hss] at h
      exact h.2
  have hWB := hasBracket_WN hB hψ hn (T := (T0 : ℝ) + s + 1) (by positivity)
  have hWc := hWB.2.1.cont
  have hsum : ∀ᵐ ω ∂μ, ∀ r : ℝ, 0 ≤ r → Summable (zN n ψ ω r) := hWB.1.mono fun ω h => h.1
  have hu0 : ∀ r, 0 ≤ uN n s r := fun r => zero_le_one.trans (uN_bounds hn hs r).1
  have huC : ∀ r, uN n s r ≤ (2 : ℝ) ^ (1 + 16 * s) := fun r => (uN_bounds hn hs r).2
  have hu : ∀ r, |uN n s r| ≤ (2 : ℝ) ^ (1 + 16 * s) := fun r => by
    rw [abs_of_nonneg (hu0 r)]; exact huC r
  have hC0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 + 16 * s) := by positivity
  have hYc := totalMass_continuousOn_pairZ2 hB hψ hn (T := (T0 : ℝ) + 1) (by positivity)
    (g := ⇑(uN n s)) (uN_neg n s) hu
  have hSfin := totalMass_lintegral_iSup_sq_ne_top hWB.2.1.toIsCL2Mart
    (by positivity : (0 : ℝ) ≤ (T0 : ℝ) + s + 1)
  have hmain := condExp_stopped_of_forall (𝓕 := filtN n 𝓕)
    (V := fun t ω => WN n ψ (t + s) ω ^ 2)
    (Y := fun t ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * uN n s (x₂ - x₁))
    (T := T0) ?_ ?_ (fun t _ => (hdet t).1.aestronglyMeasurable) ?_ (fun t _ => (hdet t).2) hτ hτT
  rotate_left
  · filter_upwards [hWc] with ω hω
    exact (hω.comp (continuous_id'.add continuous_const).continuousOn
      (fun t ht => by
        simp only [Pi.add_apply]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)).pow 2
  · filter_upwards [hYc] with ω hω
    exact hω.mono (Set.Icc_subset_Icc_right (by linarith))
  · refine ne_top_of_le_ne_top (b := ∫⁻ ω, (1 + ENNReal.ofReal ((2 : ℝ) ^ (1 + 16 * s))) *
      ⨆ t ∈ Set.Icc (0 : ℝ) ((T0 : ℝ) + s + 1), ENNReal.ofReal (WN n ψ t ω ^ 2) ∂μ) ?_ ?_
    · rw [lintegral_const_mul' _ _ (by finiteness)]
      exact ENNReal.mul_ne_top (by finiteness) hSfin
    · refine lintegral_mono_ae ?_
      filter_upwards [hsum] with ω hω
      refine iSup₂_le fun t ht => ?_
      have hb := totalMass_tsum_bounds (hω t ht.1) (totalMass_zN_nonneg n ψ ω t) hu0 huC
      rw [← totalMass_WN_eq] at hb
      have h1 : ENNReal.ofReal (WN n ψ (t + s) ω ^ 2) ≤
          ⨆ r ∈ Set.Icc (0 : ℝ) ((T0 : ℝ) + s + 1), ENNReal.ofReal (WN n ψ r ω ^ 2) :=
        le_iSup₂ (f := fun r _ => ENNReal.ofReal (WN n ψ r ω ^ 2)) (t + s)
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : ENNReal.ofReal (WN n ψ t ω ^ 2) ≤
          ⨆ r ∈ Set.Icc (0 : ℝ) ((T0 : ℝ) + s + 1), ENNReal.ofReal (WN n ψ r ω ^ 2) :=
        le_iSup₂ (f := fun r _ => ENNReal.ofReal (WN n ψ r ω ^ 2)) t
          ⟨ht.1, by linarith [ht.2]⟩
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hb.1, ENNReal.ofReal_add (sq_nonneg _) hb.1,
        add_mul, one_mul]
      refine add_le_add h1 ((ENNReal.ofReal_le_ofReal hb.2).trans ?_)
      rw [ENNReal.ofReal_mul hC0]
      gcongr
  refine ⟨?_, ?_, hmain⟩
  · filter_upwards [hsum] with ω hω
    exact ⟨hω, totalMass_summable_prod (hω _ (τ ω).2) (totalMass_zN_nonneg n ψ ω _) hu⟩
  · have hm : AEStronglyMeasurable (fun ω => WN n ψ (τ ω + s) ω) μ :=
      totalMass_aesm_stopped_add (T := T0) hs
        (hWc.mono fun ω h => h.mono (Set.Icc_subset_Icc_right (by linarith)))
        (fun t ht => aestronglyMeasurable_of_condExp_eq_self
          (hWB.2.1.condExp t t le_rfl (by linarith))) hτ hτT
    refine integrable_of_enorm_le_lintegral (hm.pow 2) hSfin (ae_of_all _ fun ω => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_iSup₂ (f := fun r _ => ENNReal.ofReal (WN n ψ r ω ^ 2)) _
      ⟨by positivity, by linarith [hτT ω]⟩

/-- **Proposition 4.3 (2)**, equation (4.8): for `n ≥ 1` and `t ≥ 0`,
`𝔼[sup_{s ∈ [0,t]} 𝒲_n(s)²] ≤ 2^{3+16t}` (the supremum, in `[0, ∞]`, being almost everywhere
measurable), and, `s ↦ ℰ_n(s)` being almost surely integrable on `[0,t]` and `∫_0^t ℰ_n(s) ds`
integrable, `𝔼[∫_0^t ℰ_n(s) ds] ≤ 2^{1+16t}`. -/
theorem prop_4_3_bounds (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) :
    (∀ᵐ ω ∂μ, (∀ r : ℝ, 0 ≤ r → Summable (zN n ψ ω r)) ∧
      IntervalIntegrable (fun s => EN n ψ ω s fun _ => 1) volume 0 t) ∧
    AEMeasurable (fun ω => ⨆ s ∈ Set.Icc 0 t, ENNReal.ofReal (WN n ψ s ω ^ 2)) μ ∧
    ∫⁻ ω, ⨆ s ∈ Set.Icc 0 t, ENNReal.ofReal (WN n ψ s ω ^ 2) ∂μ ≤
      ENNReal.ofReal (2 ^ (3 + 16 * t)) ∧
    Integrable (fun ω => ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) μ ∧
    ∫ ω, (∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) ∂μ ≤ 2 ^ (1 + 16 * t) := by
  have hWB := hasBracket_WN hB hψ hn (T := t + 1) (by linarith)
  have hW := hWB.2.1.mono_horizon (show t ≤ t + 1 by linarith)
  have hm0 := (filtN n 𝓕).le 0
  have ht' : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  have hu0 : ∀ r, 0 ≤ uN n t r := fun r => zero_le_one.trans (uN_bounds hn ht r).1
  have huC : ∀ r, uN n t r ≤ (2 : ℝ) ^ (1 + 16 * t) := fun r => (uN_bounds hn ht r).2
  -- `𝔼[𝒲_n(t)²] = 𝔼[𝔼[𝒲_n(t)² | 𝓕ⁿ_0]] ≤ 2^{1+16t}` by (4.7) at time `0` and (4.6)
  have hdet := prop_4_3_condSecondMoment hB hψ hn 0 t.toNNReal
  rw [NNReal.coe_zero, zero_add, ht'] at hdet
  obtain ⟨hsum0, hWi, hce⟩ := hdet
  have hY0 : ∀ᵐ ω ∂μ, (∑' x₁ : ℤ, ∑' x₂ : ℤ,
      zN n ψ ω 0 x₁ * zN n ψ ω 0 x₂ * uN n t (x₂ - x₁)) ≤ (2 : ℝ) ^ (1 + 16 * t) := by
    filter_upwards [hsum0, hWB.2.2] with ω hω h1
    have hb := totalMass_tsum_bounds (hω.1 0 le_rfl) (totalMass_zN_nonneg n ψ ω 0) hu0 huC
    rw [← totalMass_WN_eq, h1] at hb
    simpa using hb.2
  have hEW : ∫ ω, WN n ψ t ω ^ 2 ∂μ ≤ (2 : ℝ) ^ (1 + 16 * t) := by
    rw [← integral_condExp (μ := μ) (f := fun ω => WN n ψ t ω ^ 2) hm0]
    calc ∫ ω, (μ[fun ω => WN n ψ t ω ^ 2 | filtN n 𝓕 0]) ω ∂μ
        = ∫ ω, (∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω 0 x₁ * zN n ψ ω 0 x₂ * uN n t (x₂ - x₁)) ∂μ :=
          integral_congr_ae hce
      _ ≤ ∫ _, (2 : ℝ) ^ (1 + 16 * t) ∂μ :=
          integral_mono_ae (integrable_condExp.congr hce) (integrable_const _) hY0
      _ = (2 : ℝ) ^ (1 + 16 * t) := by simp
  refine ⟨?_, hW.toIsCL2Mart.lintegral_iSup_sq_le.1, ?_, ?_⟩
  · filter_upwards [hWB.1] with ω h
    refine ⟨h.1, h.2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_)⟩
    rw [Set.mem_uIcc]; left; constructor <;> linarith
  · refine hW.toIsCL2Mart.lintegral_iSup_sq_le.2.trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hWi (ae_of_all _ fun ω => sq_nonneg _)]
    have e : (2 : ℝ) ^ (3 + 16 * t) = 4 * (2 : ℝ) ^ (1 + 16 * t) := by
      rw [show (3 : ℝ) + 16 * t = 2 + (1 + 16 * t) by ring, Real.rpow_add (by norm_num)]
      norm_num
    rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
  -- the bracket: `𝔼[⟨𝒲_n⟩_t] = 𝔼[𝒲_n(t)²] - 1`
  have hAi : Integrable (fun ω => aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) μ := by
    have := hW.integrable_bracket t.toNNReal ht'.le
    rwa [ht'] at this
  have hsq := hW.condExp_sq 0 t.toNNReal zero_le ht'.le
  rw [ht', NNReal.coe_zero] at hsq
  have hint : ∫ ω, (WN n ψ t ω ^ 2 - aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) ∂μ = 1 := by
    rw [← integral_condExp (μ := μ) hm0, integral_congr_ae hsq]
    have h1 : (fun ω => WN n ψ 0 ω ^ 2 - aN n * ∫ s in (0 : ℝ)..0, EN n ψ ω s fun _ => 1)
        =ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [hWB.2.2] with ω h
      simp [h]
    rw [integral_congr_ae h1]
    simp
  rw [integral_sub hWi hAi, integral_const_mul] at hint
  have ha := (constants_bounds hn).2.2.1
  have hI0 : 0 ≤ ∫ ω, (∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) ∂μ := by
    refine integral_nonneg fun ω => intervalIntegral.integral_nonneg ht fun r _ => ?_
    unfold EN
    exact mul_nonneg (by positivity) (tsum_nonneg fun x => by
      simp only [mul_one]
      exact mul_nonneg (totalMass_zN_nonneg n ψ ω r x) (totalMass_zN_nonneg n ψ ω r (x + 1)))
  have hapos : 0 < aN n := by linarith
  refine ⟨?_, by nlinarith⟩
  have e : (fun ω => ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) =
      fun ω => (aN n)⁻¹ * (aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) := by
    funext ω; field_simp
  rw [e]
  exact hAi.const_mul _

/-- **Proposition 4.3 (3)**, equation (4.9): for `n ≥ 1`, a bounded stopping time `τ` and
`s ∈ [0, 1/16]`, almost surely `r ↦ ℰ_n(r)` is integrable on `[τ, τ+s]`, the increment
`⟨𝒲_n⟩_{τ+s} - ⟨𝒲_n⟩_τ = a_n ∫_τ^{τ+s} ℰ_n(r) dr` (by (3.16)) is integrable, and
`𝔼[⟨𝒲_n⟩_{τ+s} - ⟨𝒲_n⟩_τ | 𝓕ⁿ_τ] ≤ 4 √s 𝒲_n(τ)²` almost surely. -/
theorem prop_4_3_increment (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n : ℝ} (hn : 1 ≤ n) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 16) :
    (∀ᵐ ω ∂μ, (∀ r : ℝ, 0 ≤ r → Summable (zN n ψ ω r)) ∧
      IntervalIntegrable (fun r => EN n ψ ω r fun _ => 1) volume (τ ω) (τ ω + s)) ∧
    Integrable (fun ω => aN n * ∫ r in (τ ω : ℝ)..(τ ω + s), EN n ψ ω r fun _ => 1) μ ∧
    μ[fun ω => aN n * ∫ r in (τ ω : ℝ)..(τ ω + s), EN n ψ ω r fun _ => 1 |
        hτ.measurableSpace] ≤ᵐ[μ]
      fun ω => 4 * Real.sqrt s * WN n ψ (τ ω) ω ^ 2 := by
  obtain ⟨T0, hT0⟩ := hτb
  have hτT : ∀ ω, (τ ω : ℝ) ≤ T0 := fun ω => NNReal.coe_le_coe.2 (hT0 ω)
  have hT00 : (0 : ℝ) ≤ T0 := T0.2
  have hss : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  have hT' : (0 : ℝ) ≤ (T0 : ℝ) + s + 1 := by positivity
  have hWB := hasBracket_WN hB hψ hn (T := (T0 : ℝ) + s + 1) (by positivity)
  set A : ℝ → Ω → ℝ := fun t ω => aN n * ∫ r in (0 : ℝ)..t, EN n ψ ω r fun _ => 1 with hA
  have hH : HasBracket ((T0 : ℝ) + s + 1) (filtN n 𝓕) (WN n ψ) A μ := hWB.2.1
  have hsum : ∀ᵐ ω ∂μ, ∀ r : ℝ, 0 ≤ r → Summable (zN n ψ ω r) := hWB.1.mono fun ω h => h.1
  have hu0 : ∀ r, 0 ≤ uN n s r := fun r => zero_le_one.trans (uN_bounds hn hs r).1
  have huC : ∀ r, uN n s r ≤ (2 : ℝ) ^ (1 + 16 * s) := fun r => (uN_bounds hn hs r).2
  have hu : ∀ r, |uN n s r| ≤ (2 : ℝ) ^ (1 + 16 * s) := fun r => by
    rw [abs_of_nonneg (hu0 r)]; exact huC r
  have hC0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 + 16 * s) := by positivity
  have hAint : ∀ r : ℝ, 0 ≤ r → r ≤ (T0 : ℝ) + s + 1 → Integrable (A r) μ := fun r h0 h1 => by
    have := hH.integrable_bracket r.toNNReal (by rwa [Real.coe_toNNReal _ h0])
    rwa [Real.coe_toNNReal _ h0] at this
  have hAad : ∀ t : ℝ≥0, (t : ℝ) ≤ (T0 : ℝ) + s → AEStronglyMeasurable[filtN n 𝓕 t] (A t) μ :=
    fun t ht => totalMass_bracket_adapted hH t (by linarith)
  have hAb := totalMass_bracket_bounds hH hT'
  have hAc := hH.cont_bracket
  -- deterministic times: `𝔼[A_{t+s} - A_t | 𝓕ⁿ_t] = 𝒵_n^{⊗2}(t; u_n(s,·)) - 𝒲_n(t)²`
  have hinc : ∀ t : ℝ≥0, (t : ℝ) ≤ T0 → μ[fun ω => A (t + s) ω - A t ω | filtN n 𝓕 t] =ᵐ[μ]
      fun ω => (∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * uN n s (x₂ - x₁)) -
        WN n ψ t ω ^ 2 := by
    intro t ht
    have h1 := prop_4_3_condSecondMoment hB hψ hn t s.toNNReal
    rw [hss] at h1
    obtain ⟨-, hWi, hce⟩ := h1
    have hts : ((t + s.toNNReal : ℝ≥0) : ℝ) ≤ (T0 : ℝ) + s + 1 := by
      rw [NNReal.coe_add, hss]; linarith
    have hsq := hH.condExp_sq t (t + s.toNNReal) le_self_add hts
    rw [NNReal.coe_add, hss] at hsq
    have hAi1 : Integrable (A (t + s)) μ := hAint _ (by positivity) (by linarith)
    have hAi0 : Integrable (A t) μ := hAint _ t.2 (by linarith)
    have hm := (filtN n 𝓕).le t
    have hAm : μ[A t | filtN n 𝓕 t] =ᵐ[μ] A t :=
      condExp_of_aestronglyMeasurable' hm (hAad t (by linarith)) hAi0
    have e : (fun ω => A (t + s) ω - A t ω) = (fun ω => WN n ψ (t + s) ω ^ 2) -
        (fun ω => WN n ψ (t + s) ω ^ 2 - A (t + s) ω) - A t := by
      funext ω; simp only [Pi.sub_apply]; ring
    rw [e]
    have hXi : Integrable (fun ω => WN n ψ (t + s) ω ^ 2 - A (t + s) ω) μ := hWi.sub hAi1
    refine (condExp_sub (hWi.sub hXi) hAi0 _).trans ?_
    refine ((condExp_sub hWi hXi _).sub hAm).trans ?_
    filter_upwards [hce, hsq] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2]
    ring
  have hYc := totalMass_continuousOn_pairZ2 hB hψ hn (T := (T0 : ℝ) + 1) (by positivity)
    (g := ⇑(uN n s)) (uN_neg n s) hu
  have hSfin := totalMass_lintegral_iSup_sq_ne_top hH.toIsCL2Mart hT'
  have hmain := condExp_stopped_of_forall (𝓕 := filtN n 𝓕)
    (V := fun t ω => A (t + s) ω - A t ω)
    (Y := fun t ω => (∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * uN n s (x₂ - x₁)) -
      WN n ψ t ω ^ 2)
    (T := T0) ?_ ?_ ?_ ?_ hinc hτ hτT
  rotate_left
  · filter_upwards [hAc] with ω hω
    exact (hω.comp (continuous_id'.add continuous_const).continuousOn
      (fun t ht => by
        simp only [Pi.add_apply]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)).sub
      (hω.mono (Set.Icc_subset_Icc_right (by linarith)))
  · filter_upwards [hYc, hH.cont] with ω h1 h2
    exact (h1.mono (Set.Icc_subset_Icc_right (by linarith))).sub
      ((h2.mono (Set.Icc_subset_Icc_right (by linarith))).pow 2)
  · exact fun t ht => (hAint _ (by positivity) (by linarith)).aestronglyMeasurable.sub
      (hAint _ (NNReal.coe_nonneg t) (by linarith)).aestronglyMeasurable
  · refine ne_top_of_le_ne_top (b := ∫⁻ ω, ENNReal.ofReal (A ((T0 : ℝ) + s + 1) ω) +
      ENNReal.ofReal ((2 : ℝ) ^ (1 + 16 * s) + 1) *
        ⨆ t ∈ Set.Icc (0 : ℝ) ((T0 : ℝ) + s + 1), ENNReal.ofReal (WN n ψ t ω ^ 2) ∂μ) ?_ ?_
    · rw [lintegral_add_left' (hAint _ hT' le_rfl).aemeasurable.ennreal_ofReal,
        lintegral_const_mul' _ _ (by finiteness)]
      exact ENNReal.add_ne_top.2 ⟨(hAint _ hT' le_rfl).lintegral_lt_top.ne,
        ENNReal.mul_ne_top (by finiteness) hSfin⟩
    · refine lintegral_mono_ae ?_
      filter_upwards [hsum, hAb] with ω hω hb
      refine iSup₂_le fun t ht => ?_
      have hz := totalMass_tsum_bounds (hω t ht.1) (totalMass_zN_nonneg n ψ ω t) hu0 huC
      rw [← totalMass_WN_eq] at hz
      have hb1 := hb (t + s) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hb0 := hb t ⟨ht.1, by linarith [ht.2]⟩
      have h2 : ENNReal.ofReal (WN n ψ t ω ^ 2) ≤
          ⨆ r ∈ Set.Icc (0 : ℝ) ((T0 : ℝ) + s + 1), ENNReal.ofReal (WN n ψ r ω ^ 2) :=
        le_iSup₂ (f := fun r _ => ENNReal.ofReal (WN n ψ r ω ^ 2)) t
          ⟨ht.1, by linarith [ht.2]⟩
      have hW2 := sq_nonneg (WN n ψ t ω)
      have e1 : |A (t + s) ω - A t ω| ≤ A ((T0 : ℝ) + s + 1) ω := by
        rw [abs_le]; constructor <;> linarith
      have e2 : |(∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * uN n s (x₂ - x₁)) -
          WN n ψ t ω ^ 2| ≤ ((2 : ℝ) ^ (1 + 16 * s) + 1) * WN n ψ t ω ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith
      refine (ENNReal.ofReal_le_ofReal (add_le_add e1 e2)).trans ?_
      rw [ENNReal.ofReal_add (hb (T0 + s + 1) ⟨hT', le_rfl⟩).1 (mul_nonneg (by linarith) hW2),
        ENNReal.ofReal_mul (p := (2 : ℝ) ^ (1 + 16 * s) + 1) (by linarith)]
      gcongr
  -- from `A_{τ+s} - A_τ` to the integral over `[τ, τ+s]`
  have hmemτ : ∀ ω, (τ ω : ℝ) ∈ Set.uIcc 0 ((T0 : ℝ) + s + 1) := fun ω =>
    Set.mem_uIcc.2 (Or.inl ⟨(τ ω).2, by linarith [hτT ω]⟩)
  have hmemτs : ∀ ω, (τ ω : ℝ) + s ∈ Set.uIcc 0 ((T0 : ℝ) + s + 1) := fun ω =>
    Set.mem_uIcc.2 (Or.inl ⟨by positivity, by linarith [hτT ω]⟩)
  have heq : ∀ᵐ ω ∂μ, aN n * (∫ r in (τ ω : ℝ)..(τ ω + s), EN n ψ ω r fun _ => 1) =
      A (τ ω + s) ω - A (τ ω) ω := by
    filter_upwards [hWB.1] with ω h
    have h1 := h.2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (hmemτs ω))
    have h2 := h.2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (hmemτ ω))
    simp only [hA]
    rw [← intervalIntegral.integral_interval_sub_left h1 h2]
    ring
  have hAc0 : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 ((T0 : ℝ) + s)) :=
    hAc.mono fun ω h => h.mono (Set.Icc_subset_Icc_right (by linarith))
  have hm1 := totalMass_aesm_stopped_add (T := T0) hs hAc0 hAad hτ hτT
  have hm0 := (aestronglyMeasurable_stoppedAt
    (hAc.mono fun ω h => h.mono (Set.Icc_subset_Icc_right (by linarith)))
    (fun t ht => hAad t (by linarith)) hτ hτT).mono hτ.measurableSpace_le
  have hDi : Integrable (fun ω => A (τ ω + s) ω - A (τ ω) ω) μ := by
    refine Integrable.mono' (hAint _ hT' le_rfl) (hm1.sub hm0) ?_
    filter_upwards [hAb] with ω hb
    have hb1 := hb (τ ω + s) ⟨by positivity, by linarith [hτT ω]⟩
    have hb0 := hb (τ ω) ⟨(τ ω).2, by linarith [hτT ω]⟩
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  refine ⟨?_, hDi.congr (heq.mono fun ω h => h.symm), ?_⟩
  · filter_upwards [hWB.1] with ω h
    exact ⟨h.1, h.2.mono_set (Set.uIcc_subset_uIcc (hmemτ ω) (hmemτs ω))⟩
  · filter_upwards [condExp_congr_ae (m := hτ.measurableSpace) heq, hmain, hsum] with ω h1 h2 h3
    rw [h1, h2]
    have hz := totalMass_tsum_bounds (h3 _ (NNReal.coe_nonneg (τ ω)))
      (totalMass_zN_nonneg n ψ ω _) hu0
      (fun r => uN_le_one_add_sqrt hn hs hs' r)
    rw [← totalMass_WN_eq] at hz
    linarith [hz.2]

end QSSEPtoKPZ
