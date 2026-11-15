/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.MomentAux

/-!
# The truncated moment estimate (task D4)

See `docs/stage2-design.md`, Section 1.2 (g). Let `ψ'` be a unit-norm version of the wave
function, `b ≥ 0`, `R ∈ ℕ`, `w_R = w_{b,R}` the truncated weight `e^{b min(|x|,R)}`,
`V_R(t) = ∑ₓ w_R(x) P(t,x)` and `c = 2 (e^b - 1)`, so that `Δw_R ≤ c w_R`.

* `W(t) = e^{-ct} V_R(t) = ∑ₓ e^{-ct} w_R(x) P(t,x)` is an Itô process (bounded weights,
  `IsUnitWave.isItoProcessUpTo_weight`) whose drift `e^{-ct} ∑ₓ (Δw_R - c w_R)(x) P(t,x)` is
  `≤ 0`; hence `e^{-ct} V_R(t) ≤ 1 + I_t` for all `t ≤ N`, almost surely, where `I` is the
  martingale part (`IsUnitWave.momentV_le_stochInt`).
* Taking expectations, `𝔼 V_R(t) ≤ e^{ct}` (`IsUnitWave.lintegral_momentV_le`).
* The bracket density of `I` is `∑_y (e^{-cs}(w_R(y+1) - w_R(y)))² 2 P(y) P(y+1)
  ≤ 2 ((e^b - 1) e^b)² V_{2b,R}(s)`, whose expectation is `≤ 2 ((e^b - 1) e^b)² e^{c₂ s}`,
  `c₂ = 2 (e^{2b} - 1)`.
* Doob's inequality then gives the bound uniform in `R`
  (`IsUnitWave.lintegral_iSup_momentV_le`):
  `𝔼 sup_{t ≤ T} V_R(t) ≤ e^{cT} (2 + 4 · 2 ((e^b - 1) e^b)² e^{c₂ T} T)`.

(The design document writes `c = 2 (cosh a - 1)`; with the truncated weights `Δw_R(0) =
2 (e^b - 1) w_R(0)` when `R ≥ 1`, so the constant `2 (e^b - 1)` is used instead. Only the
existence of a constant matters.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The rate `c = 2 (e^b - 1)` (`Δw_{b,R} ≤ c w_{b,R}`). -/
def momentRate (b : ℝ) : ℝ := 2 * (Real.exp b - 1)

lemma momentRate_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ momentRate b := by
  unfold momentRate; linarith [Real.one_le_exp hb]

/-- The time-dependent weight `e^{-ct} w_{b,R}(x)`. -/
def momentTW (b : ℝ) (R : ℕ) (t : ℝ) (x : ℤ) : ℝ :=
  Real.exp (-(momentRate b * t)) * momentWeight b R x

/-- The time derivative of `momentTW`. -/
def momentTW' (b : ℝ) (R : ℕ) (t : ℝ) (x : ℤ) : ℝ :=
  -momentRate b * Real.exp (-(momentRate b * t)) * momentWeight b R x

/-- The constant of the bound `𝔼 sup_{t ≤ T} V_{b,R}(t) ≤ momentConst b T`. -/
def momentConst (b T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (momentRate b * T)) * (2 + 4 * (ENNReal.ofReal
    (2 * ((Real.exp b - 1) * Real.exp b) ^ 2 * Real.exp (momentRate (2 * b) * T)) *
      ENNReal.ofReal T))

lemma momentConst_ne_top (b T : ℝ) : momentConst b T ≠ ∞ := by
  unfold momentConst
  finiteness

namespace IsUnitWave

/-- `∑ₓ e^{-ct} w(x) P(t,x)` is an Itô process up to every `N`, with drift
`∑ₓ (∂ₜ + Δ)(e^{-ct} w)(x) P(t,x)` and diffusion `weightCurrent ψ' (momentTW b R)`. -/
theorem isItoProcessUpTo_momentTW [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (N : ℝ≥0) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => ∑' x, momentTW b R t x * density ψ' ω t x)
      (fun s ω => ∑' x, (momentTW' b R s x + lap (momentTW b R s) x) * density ψ' ω s x)
      (weightCurrent ψ' (momentTW b R)) := by
  have hc := momentRate_nonneg hb
  refine hu.isItoProcessUpTo_weight hB (C := (1 + momentRate b) * Real.exp (b * R))
    (fun x t _ => ?_) (fun x => ?_) (fun x t ht => ?_)
  · have h := (((hasDerivAt_id' t).const_mul (momentRate b)).neg.exp).mul_const
      (momentWeight b R x)
    refine HasDerivAt.hasDerivWithinAt ?_
    convert h using 1
    · funext y; simp [momentTW]
    · simp only [momentTW', Pi.neg_apply]; ring
  · exact (Continuous.continuousOn (by unfold momentTW'; fun_prop))
  · have he : Real.exp (-(momentRate b * t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    have hep := Real.exp_pos (-(momentRate b * t))
    have hw := abs_momentWeight_le hb R x
    have hwp := momentWeight_pos b R x
    have hE := Real.exp_pos (b * R)
    rw [abs_of_pos hwp] at hw
    have hprod : Real.exp (-(momentRate b * t)) * momentWeight b R x ≤ Real.exp (b * R) := by
      calc _ ≤ 1 * momentWeight b R x := mul_le_mul_of_nonneg_right he hwp.le
        _ ≤ _ := by rw [one_mul]; exact hw
    constructor
    · rw [momentTW, abs_mul, abs_of_pos hep, abs_of_pos hwp]
      nlinarith
    · rw [momentTW', abs_mul, abs_mul, abs_neg, abs_of_nonneg hc, abs_of_pos hep,
        abs_of_pos hwp, mul_assoc]
      have := mul_le_mul_of_nonneg_left hprod hc
      nlinarith

/-- **Supermartingale bound.** Almost surely, for all `t ∈ [0, N]`,
`e^{-ct} V_{b,R}(t) ≤ 1 + I_t`, where `I` is the martingale part of `e^{-ct} V_{b,R}`. -/
theorem momentV_le_stochInt [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (N : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → t ≤ N →
      Real.exp (-(momentRate b * t)) * momentV ψ' b R t ω ≤
        1 + stochInt (nullAug μ 𝓕) μ B (fun i s ω =>
          if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0) t ω := by
  have hX := hu.isItoProcessUpTo_momentTW hB hb R N
  have hc := momentRate_nonneg hb
  filter_upwards [hX.eq] with ω hω t ht0 htN
  have e := hω ⟨t, ht0⟩
  have hm : min (⟨t, ht0⟩ : ℝ≥0) N = ⟨t, ht0⟩ := min_eq_left htN
  erw [hm] at e
  -- the value at time `t` and at time `0`
  have hXt : ∑' x, momentTW b R t x * density ψ' ω t x =
      Real.exp (-(momentRate b * t)) * momentV ψ' b R t ω := by
    rw [momentV, ← tsum_mul_left]
    congr 1; funext x; simp only [momentTW]; ring
  have hX0 : ∑' x, momentTW b R 0 x * density ψ' ω 0 x = 1 := by
    have : ∀ x, momentTW b R 0 x * density ψ' ω 0 x = if x = 0 then 1 else 0 := fun x => by
      rw [density, hu.init_apply ω x]
      split_ifs with h
      · subst h; simp [momentTW, momentWeight]
      · simp
    simp only [this, tsum_ite_eq]
  -- the drift is nonpositive
  have hdr : ∀ s, (∑' x, (momentTW' b R s x + lap (momentTW b R s) x) *
      density ψ' ω s x) ≤ 0 := fun s => by
    refine tsum_nonpos fun x => ?_
    have hl : lap (momentTW b R s) x =
        Real.exp (-(momentRate b * s)) * lap (momentWeight b R) x := by
      simp only [lap, momentTW]; ring
    have h1 : momentTW' b R s x + lap (momentTW b R s) x =
        Real.exp (-(momentRate b * s)) *
          (lap (momentWeight b R) x - momentRate b * momentWeight b R x) := by
      rw [hl, momentTW']; ring
    rw [h1]
    have := lap_momentWeight_le hb R x
    have : lap (momentWeight b R) x - momentRate b * momentWeight b R x ≤ 0 := by
      unfold momentRate; linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this) (density_nonneg ψ' ω s x)
  have hint : (∫ s in (0 : ℝ)..t, ∑' x, (momentTW' b R s x + lap (momentTW b R s) x) *
      density ψ' ω s x) ≤ 0 := by
    have := intervalIntegral.integral_nonneg (μ := volume) ht0 fun s _ => neg_nonneg.2 (hdr s)
    rw [intervalIntegral.integral_neg] at this
    linarith
  rw [← hXt]
  have e' : ∑' x, momentTW b R t x * density ψ' ω t x = 1 +
      (∫ s in (0 : ℝ)..t, ∑' x, (momentTW' b R s x + lap (momentTW b R s) x) *
        density ψ' ω s x) + stochInt (nullAug μ 𝓕) μ B (fun i s ω =>
          if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0) t ω := by
    rw [← hX0]; exact e
  rw [e']
  linarith

/-- The martingale part `I` is Itô-integrable, and `𝔼 I_t = 0`. -/
lemma integral_stochInt_momentTW [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (N : ℝ≥0) (t : ℝ≥0) :
    Integrable (stochInt (nullAug μ 𝓕) μ B (fun i s ω =>
      if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0) t) μ ∧
    ∫ ω, stochInt (nullAug μ 𝓕) μ B (fun i s ω =>
      if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0) t ω ∂μ = 0 := by
  have hX := hu.isItoProcessUpTo_momentTW hB hb R N
  have hbr := hasBracket_stochInt hB.nullAug hX.integrable t
  refine ⟨(hbr.memLp t le_rfl).integrable one_le_two, ?_⟩
  have hce := hbr.condExp 0 t (zero_le) le_rfl
  have h := integral_congr_ae hce
  rw [integral_condExp ((nullAug μ 𝓕).le 0)] at h
  rw [h]
  simp [stochInt_of_nonpos]

/-- **First moment.** `𝔼 V_{b,R}(t) ≤ e^{ct}` for `t ≥ 0`. -/
theorem lintegral_momentV_le [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (momentV ψ' b R t ω) ∂μ ≤
      ENNReal.ofReal (Real.exp (momentRate b * t)) := by
  set N : ℝ≥0 := ⟨t, ht⟩ with hN
  set I := stochInt (nullAug μ 𝓕) μ B (fun i s ω =>
      if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0) (N : ℝ) with hI
  obtain ⟨hIi, hI0⟩ := hu.integral_stochInt_momentTW hB hb R N N
  have hle := hu.momentV_le_stochInt hB hb R N
  have hpos : ∀ᵐ ω ∂μ, 0 ≤ 1 + I ω := by
    filter_upwards [hle] with ω hω
    exact le_trans (mul_nonneg (Real.exp_pos _).le (momentV_nonneg _ _ _ _ _))
      (hω t ht le_rfl)
  have hbd : ∀ᵐ ω ∂μ, ENNReal.ofReal (momentV ψ' b R t ω) ≤
      ENNReal.ofReal (Real.exp (momentRate b * t)) * ENNReal.ofReal (1 + I ω) := by
    filter_upwards [hle] with ω hω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hω t ht le_rfl
    have e : Real.exp (momentRate b * t) * Real.exp (-(momentRate b * t)) = 1 := by
      rw [← Real.exp_add]; simp
    calc momentV ψ' b R t ω = Real.exp (momentRate b * t) *
          (Real.exp (-(momentRate b * t)) * momentV ψ' b R t ω) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  calc ∫⁻ ω, ENNReal.ofReal (momentV ψ' b R t ω) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (momentRate b * t)) * ENNReal.ofReal (1 + I ω) ∂μ :=
        lintegral_mono_ae hbd
    _ = ENNReal.ofReal (Real.exp (momentRate b * t)) * ENNReal.ofReal (∫ ω, (1 + I ω) ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal (f := fun ω => 1 + I ω)
            ((integrable_const 1).add hIi) hpos]
    _ = ENNReal.ofReal (Real.exp (momentRate b * t)) := by
        rw [integral_add (integrable_const 1) hIi]
        simp only [hI0]
        simp

/-- Joint measurability of `(ω, s) ↦ P(max s 0, x)`. -/
lemma weight_measurable_density_max (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) :
    Measurable fun p : Ω × ℝ => density ψ' p.1 (max p.2 0) x := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (s : ℝ) (ω : Ω) => density ψ' ω (max s 0) x)
    (fun ω => (hu.weight_continuousOn_density ω x).comp_continuous
      (continuous_id.max continuous_const) fun s => le_max_right s 0)
    (fun s => (hu.weight_measurable_density ⟨max s 0, le_max_right s 0⟩ x).mono
      ((nullAug μ 𝓕).le _) le_rfl)
  exact h.comp measurable_swap

/-- **Energy of the martingale part.** For `T ≤ N`,
`𝔼 ∫_0^T ∑ᵢ (weightCurrent)ᵢ² ds ≤ 2 ((e^b - 1) e^b)² e^{c₂ T} T`, `c₂ = 2 (e^{2b} - 1)`:
the bracket density is at most `2 ((e^b - 1) e^b)² V_{2b,R}(s)` and `𝔼 V_{2b,R}(s) ≤ e^{c₂ s}`. -/
theorem energy_momentTW_le [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (N : ℝ≥0) {T : ℝ}
    (hTN : T ≤ N) :
    energy μ (fun i s ω => if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0)
      T ≤ ENNReal.ofReal (2 * ((Real.exp b - 1) * Real.exp b) ^ 2 *
        Real.exp (momentRate (2 * b) * T)) * ENNReal.ofReal T := by
  set D := (Real.exp b - 1) * Real.exp b with hD
  have hb2 : 0 ≤ 2 * b := by linarith
  set F : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    ENNReal.ofReal (2 * D ^ 2 * momentV ψ' (2 * b) R (max s 0) ω) with hF
  have hc := momentRate_nonneg hb
  have hpt : ∀ ω s, s ∈ Set.Ioc (0 : ℝ) T → ∑' i, ‖(if s ≤ (N : ℝ) then
      weightCurrent ψ' (momentTW b R) i s ω else 0)‖ₑ ^ 2 ≤ F ω s := by
    intro ω s hs
    have hsN : s ≤ (N : ℝ) := hs.2.trans hTN
    have hs0 : 0 ≤ s := hs.1.le
    have he1 : Real.exp (-(momentRate b * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    simp only [hsN, ite_true]
    have hwb : ∀ y, |momentTW b R s y| ≤ Real.exp (b * R) := fun y => by
      rw [momentTW, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc _ ≤ 1 * Real.exp (b * R) :=
            mul_le_mul he1 (abs_momentWeight_le hb R y) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    rw [tsum_enorm_weightCurrent_sq ψ' _ s ω (summable_weightCurrent_fiber ψ' hwb ω)]
    simp only [hF, max_eq_left hs0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [momentV, ← tsum_mul_left]
    refine (summable_weightCurrent_fiber ψ' hwb ω).tsum_le_tsum (fun y => ?_)
      ((summable_momentV hb2 ψ' R s ω).mul_left _)
    have hsq := sq_momentWeight_sub_le hb R y
    have he : Real.exp (-(momentRate b * s)) ^ 2 ≤ 1 :=
      pow_le_one₀ (Real.exp_pos _).le he1
    have hP0 := density_nonneg ψ' ω s y
    have hP1 := density_nonneg ψ' ω s (y + 1)
    have hq := hu.density_le_one ω hs0 (y + 1)
    have h2 : momentWeight b R y ^ 2 = momentWeight (2 * b) R y := by
      rw [momentWeight_pow]; norm_num
    have e1 : (momentTW b R s (y + 1) - momentTW b R s y) ^ 2 =
        Real.exp (-(momentRate b * s)) ^ 2 *
          (momentWeight b R (y + 1) - momentWeight b R y) ^ 2 := by
      simp only [momentTW]; ring
    rw [e1, ← h2]
    have hΔ : 0 ≤ (momentWeight b R (y + 1) - momentWeight b R y) ^ 2 := sq_nonneg _
    calc Real.exp (-(momentRate b * s)) ^ 2 *
          (momentWeight b R (y + 1) - momentWeight b R y) ^ 2 *
          (2 * density ψ' ω s y * density ψ' ω s (y + 1))
        ≤ (D ^ 2 * momentWeight b R y ^ 2) * (2 * density ψ' ω s y * density ψ' ω s (y + 1)) :=
          mul_le_mul_of_nonneg_right (le_trans (mul_le_of_le_one_left hΔ he) hsq)
            (by positivity)
      _ ≤ (D ^ 2 * momentWeight b R y ^ 2) * (2 * density ψ' ω s y) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = 2 * D ^ 2 * (momentWeight b R y ^ 2 * density ψ' ω s y) := by ring
  have hFm : Measurable (Function.uncurry F) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (StochIntAux.measurable_tsum_real
      fun x => measurable_const.mul (hu.weight_measurable_density_max x)))
  have hc2 := momentRate_nonneg hb2
  calc energy μ (fun i s ω => if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω
        else 0) T
      ≤ ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, F ω s) ∂μ :=
        lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioc (hpt ω)
    _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ ω, F ω s ∂μ :=
        lintegral_lintegral_swap hFm.aemeasurable
    _ ≤ ∫⁻ s in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (2 * D ^ 2 *
          Real.exp (momentRate (2 * b) * T)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        have hs0 : 0 ≤ s := hs.1.le
        simp only [hF, max_eq_left hs0]
        simp_rw [ENNReal.ofReal_mul (show 0 ≤ 2 * D ^ 2 by positivity)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hm := hu.lintegral_momentV_le hB hb2 R hs0
        refine (mul_le_mul' le_rfl hm).trans ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hc2)) (by positivity))
    _ = _ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]

/-- **The bound uniform in `R`** (the core of (2.2)): for `b ≥ 0`, `T ≥ 0` and every `R`,
`𝔼 sup_{t ∈ [0,T]} V_{b,R}(t) ≤ momentConst b T`. (`e^{-ct} V_{b,R} ≤ 1 + I`, Doob's inequality
for `I`, and the energy bound.) -/
theorem lintegral_iSup_momentV_le [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (R : ℕ) :
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (momentV ψ' b R t ω) ∂μ ≤
      momentConst b T := by
  set N : ℝ≥0 := ⟨T, hT⟩ with hN
  set I := stochInt (nullAug μ 𝓕) μ B (fun i s ω =>
    if s ≤ (N : ℝ) then weightCurrent ψ' (momentTW b R) i s ω else 0) with hI
  have hX := hu.isItoProcessUpTo_momentTW hB hb R N
  have hc := momentRate_nonneg hb
  have hle := hu.momentV_le_stochInt hB hb R N
  have hpt : ∀ᵐ ω ∂μ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (momentV ψ' b R t ω) ≤
      ENNReal.ofReal (Real.exp (momentRate b * T)) * (2 + ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (I t ω ^ 2)) := by
    filter_upwards [hle] with ω hω
    refine iSup₂_le fun t ht => ?_
    have h1 := hω t ht.1 ht.2
    have hV : momentV ψ' b R t ω ≤ Real.exp (momentRate b * T) * (2 + I t ω ^ 2) := by
      have eexp : Real.exp (momentRate b * t) * Real.exp (-(momentRate b * t)) = 1 := by
        rw [← Real.exp_add]; simp
      have hmono : Real.exp (momentRate b * t) ≤ Real.exp (momentRate b * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hc)
      calc momentV ψ' b R t ω = Real.exp (momentRate b * t) *
            (Real.exp (-(momentRate b * t)) * momentV ψ' b R t ω) := by
            rw [← mul_assoc, eexp, one_mul]
        _ ≤ Real.exp (momentRate b * t) * (1 + I t ω) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ Real.exp (momentRate b * t) * (2 + I t ω ^ 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (I t ω - 1), sq_nonneg (I t ω)])
              (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_right hmono (by positivity)
    calc ENNReal.ofReal (momentV ψ' b R t ω)
        ≤ ENNReal.ofReal (Real.exp (momentRate b * T) * (2 + I t ω ^ 2)) :=
          ENNReal.ofReal_le_ofReal hV
      _ = ENNReal.ofReal (Real.exp (momentRate b * T)) * (2 + ENNReal.ofReal (I t ω ^ 2)) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
            ENNReal.ofReal_add (by norm_num) (sq_nonneg _)]
          simp
      _ ≤ _ := by
          gcongr
          exact le_iSup₂ (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) T) =>
            ENNReal.ofReal (I t ω ^ 2)) t ht
  have hDoob := lintegral_iSup_stochInt_sq_le hB.nullAug hX.integrable T
  have hen := hu.energy_momentTW_le hB hb R N le_rfl
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (momentRate b * T)) * (2 + ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (I t ω ^ 2)) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp (momentRate b * T)) * (2 + ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (I t ω ^ 2) ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left measurable_const]
        simp
    _ ≤ momentConst b T := by
        unfold momentConst
        gcongr
        exact hDoob.trans (mul_le_mul' le_rfl hen)

end IsUnitWave

end QSSEPtoKPZ
