/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Volterra inequality with kernel `(t-s)^{-1/2}` (task G10a)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G10a.
See `docs/stage4-design.md`, Section 3.4, and `docs/stage4-interfaces.md`.

End of the proof of Proposition 7.3: if `F ≥ 0` is integrable on `[0,T]` and
`F(t) ≤ c ∫_0^t F(s) (t-s)^{-1/2} ds` for almost every `t`, then `F = 0` almost everywhere
(multiply by `e^{-at}`, integrate, Fubini, `∫_0^∞ e^{-ar} r^{-1/2} dr = √(π/a)`, choose `a`
large). Stated in `[0, ∞]` so that no integrability of the right side is needed.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- `∫_0^∞ r^{-1/2} e^{-ar} dr = a^{-1/2} Γ(1/2)` (`a > 0`), as a lower integral. -/
private lemma volterra_lintegral_kernel {a : ℝ} (ha : 0 < a) :
    ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (Real.exp (-a * r)) =
      ENNReal.ofReal ((1 / a) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := a) (by norm_num) ha
  have hpos : 0 < (1 / a) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    positivity
  have hint : IntegrableOn (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * t)))
      (Set.Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact hpos.ne')
  rw [← h, ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
      (Real.exp_pos _).le))]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hr) _),
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, neg_mul]

/-- Volterra's lemma for a measurable `F` vanishing outside `[0,T]`: with `w(t) = e^{-at}`,
`I = ∫_0^T F w` satisfies `I ≤ c √(π/a) I`, hence `I = 0` for `a` large. -/
private lemma volterra_aux {T c : ℝ} {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (hsupp : ∀ s, s ∉ Set.Icc 0 T → F s = 0)
    (hFi : ∫⁻ t in Set.Icc 0 T, F t < ⊤)
    (hle : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      F t ≤ ENNReal.ofReal c * ∫⁻ s in Set.Ioo 0 t, F s * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ)))) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), F t = 0 := by
  set c' := max c 0 with hc'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  set a := (2 * c' * Real.sqrt Real.pi + 1) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-a * t)) with hw
  set k : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-(1 / 2 : ℝ))) with hk
  have hwm : Measurable w := by rw [hw]; fun_prop
  have hkm : Measurable k := by rw [hk]; fun_prop
  set K := ∫⁻ r in Set.Ioi 0, k r * w r with hK
  have hKval : K = ENNReal.ofReal ((1 / a) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2)) :=
    volterra_lintegral_kernel ha0
  set I := ∫⁻ t in Set.Icc 0 T, F t * w t with hI
  have hItop : I ≠ ⊤ := by
    refine ne_top_of_le_ne_top hFi.ne (setLIntegral_mono' measurableSet_Icc fun t ht => ?_)
    calc F t * w t ≤ F t * 1 := by
          gcongr
          exact ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by nlinarith [ht.1]))
      _ = F t := mul_one _
  set S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  set J : ℝ × ℝ → ℝ≥0∞ := fun p => F p.2 * k (p.1 - p.2) * w p.1 with hJ
  have hJm : Measurable J :=
    ((hF.comp measurable_snd).mul (hkm.comp (measurable_fst.sub measurable_snd))).mul
      (hwm.comp measurable_fst)
  have hJSm : Measurable (S.indicator J) := hJm.indicator hSm
  have step1 : I ≤ ENNReal.ofReal c * ∫⁻ t, ∫⁻ s, S.indicator J (t, s) := by
    calc I ≤ ∫⁻ t in Set.Icc 0 T, (ENNReal.ofReal c * ∫⁻ s in Set.Ioo 0 t, F s * k (t - s)) * w t :=
          lintegral_mono_ae (hle.mono fun t ht => mul_le_mul_left ht _)
      _ = ENNReal.ofReal c * ∫⁻ t in Set.Icc 0 T, ∫⁻ s in Set.Ioo 0 t, F s * k (t - s) * w t := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun t => ?_
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_assoc]
      _ ≤ ENNReal.ofReal c * ∫⁻ t, ∫⁻ s in Set.Ioo 0 t, F s * k (t - s) * w t := by
          gcongr; exact Measure.restrict_le_self
      _ = _ := by
          congr 1
          refine lintegral_congr fun t => ?_
          rw [← lintegral_indicator measurableSet_Ioo]
          refine lintegral_congr fun s => ?_
          by_cases hs : s ∈ Set.Ioo 0 t
          · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show (t, s) ∈ S from hs)]
          · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show (t, s) ∉ S from hs)]
  have step2 : ∀ s, ∫⁻ t, S.indicator J (t, s) ≤ F s * w s * K := by
    intro s
    rcases le_or_gt s 0 with hs | hs
    · have h0 : ∀ t, S.indicator J (t, s) = 0 := fun t =>
        Set.indicator_of_notMem (fun h => by linarith [h.1]) _
      simp [h0]
    · rw [← lintegral_add_right_eq_self _ s]
      have h1 : ∀ r, S.indicator J (r + s, s) =
          F s * w s * (Set.Ioi 0).indicator (fun r => k r * w r) r := by
        intro r
        by_cases hr : 0 < r
        · rw [Set.indicator_of_mem (show (r + s, s) ∈ S from ⟨hs, by linarith⟩),
            Set.indicator_of_mem (show r ∈ Set.Ioi 0 from hr)]
          simp only [hJ, hw, add_sub_cancel_right]
          rw [show -a * (r + s) = -a * r + -a * s by ring, Real.exp_add,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
        · rw [Set.indicator_of_notMem (show (r + s, s) ∉ S from fun h => hr (by linarith [h.2])),
            Set.indicator_of_notMem (show r ∉ Set.Ioi 0 from hr), mul_zero]
      simp_rw [h1]
      rw [lintegral_const_mul (F s * w s) (f := (Set.Ioi 0).indicator (fun r => k r * w r))
          ((hkm.mul hwm).indicator measurableSet_Ioi),
        lintegral_indicator measurableSet_Ioi]
  have step3 : ∫⁻ s, F s * w s * K = K * I := by
    rw [lintegral_mul_const K (f := fun s => F s * w s) (hF.mul hwm), mul_comm, hI, setLIntegral_eq_of_support_subset]
    intro s hs
    by_contra h
    exact hs (show F s * w s = 0 by rw [hsupp s h, zero_mul])
  have hmain : I ≤ ENNReal.ofReal c * K * I := by
    calc I ≤ ENNReal.ofReal c * ∫⁻ t, ∫⁻ s, S.indicator J (t, s) := step1
      _ = ENNReal.ofReal c * ∫⁻ s, ∫⁻ t, S.indicator J (t, s) := by
          rw [lintegral_lintegral_swap (f := fun t s => S.indicator J (t, s)) hJSm.aemeasurable]
      _ ≤ ENNReal.ofReal c * ∫⁻ s, F s * w s * K := by gcongr with s; exact step2 s
      _ = ENNReal.ofReal c * K * I := by rw [step3, mul_assoc]
  -- the constant `c √(π/a)` is at most `1/2`
  have hq : ENNReal.ofReal c * K ≤ ENNReal.ofReal (1 / 2) := by
    have hcc : ENNReal.ofReal c = ENNReal.ofReal c' := by
      rcases le_total c 0 with h | h
      · rw [ENNReal.ofReal_of_nonpos h, hc', max_eq_right h, ENNReal.ofReal_zero]
      · rw [hc', max_eq_left h]
    rw [hcc, hKval, ← ENNReal.ofReal_mul hc'0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsa : (1 / a) ^ (1 / 2 : ℝ) = 1 / (2 * c' * Real.sqrt Real.pi + 1) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ ha0.le, Real.sqrt_one, ha,
        Real.sqrt_sq (by positivity)]
    rw [hsa, Real.Gamma_one_half_eq]
    have hpi := Real.sqrt_nonneg Real.pi
    rw [show c' * (1 / (2 * c' * Real.sqrt Real.pi + 1) * Real.sqrt Real.pi) =
      c' * Real.sqrt Real.pi / (2 * c' * Real.sqrt Real.pi + 1) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hc'0 hpi]
  have hI0 : I = 0 := by
    have h1 : I ≤ ENNReal.ofReal (1 / 2) * I := hmain.trans (by gcongr)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hItop) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h2
    have h3 : I.toReal = 0 := by linarith [ENNReal.toReal_nonneg (a := I)]
    rcases (ENNReal.toReal_eq_zero_iff I).1 h3 with h | h
    · exact h
    · exact absurd h hItop
  have hzero := (lintegral_eq_zero_iff (hF.mul hwm)).1 hI0
  filter_upwards [hzero] with t ht
  have hwt : w t ≠ 0 := by
    simp only [hw, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  exact (mul_eq_zero.1 ht).resolve_right hwt

/-- **Volterra's lemma** for the kernel `(t-s)^{-1/2}`. -/
theorem volterra_ae_eq_zero {T c : ℝ} {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F (volume.restrict (Set.Icc 0 T)))
    (hFi : ∫⁻ t in Set.Icc 0 T, F t < ⊤)
    (hle : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      F t ≤ ENNReal.ofReal c * ∫⁻ s in Set.Ioo 0 t, F s * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ)))) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), F t = 0 := by
  set F₁ := (Set.Icc 0 T).indicator (hF.mk F) with hF₁
  have hF₁m : Measurable F₁ := hF.measurable_mk.indicator measurableSet_Icc
  have hFF₁ : F =ᵐ[volume.restrict (Set.Icc 0 T)] F₁ := by
    filter_upwards [hF.ae_eq_mk, ae_restrict_mem measurableSet_Icc] with t h1 h2
    rw [hF₁, Set.indicator_of_mem h2]; exact h1
  have hinner : ∀ t, t ≤ T → ∫⁻ s in Set.Ioo 0 t, F s * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) =
      ∫⁻ s in Set.Ioo 0 t, F₁ s * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    refine lintegral_congr_ae ((ae_restrict_of_ae_restrict_of_subset
      (show Set.Ioo 0 t ⊆ Set.Icc 0 T from fun s hs => ⟨hs.1.le, hs.2.le.trans ht⟩) hFF₁).mono
        fun s hs => congrArg (· * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ)))) hs)
  have hle₁ : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), F₁ t ≤ ENNReal.ofReal c *
      ∫⁻ s in Set.Ioo 0 t, F₁ s * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [hle, hFF₁, ae_restrict_mem measurableSet_Icc] with t h1 h2 h3
    rw [← h2, ← hinner t h3.2]; exact h1
  have hFi₁ : ∫⁻ t in Set.Icc 0 T, F₁ t < ⊤ := by rwa [← lintegral_congr_ae hFF₁]
  have hsupp : ∀ s, s ∉ Set.Icc 0 T → F₁ s = 0 := fun s hs => Set.indicator_of_notMem hs _
  filter_upwards [volterra_aux hF₁m hsupp hFi₁ hle₁, hFF₁] with t h1 h2
  rw [h2, h1]

end QSSEPtoKPZ
