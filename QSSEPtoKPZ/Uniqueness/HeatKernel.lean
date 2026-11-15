/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.Defs
public import QSSEPtoKPZ.Checks
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The heat kernel: Gaussian identities and the iterated kernels `K^{⋆k}` (task G10a)

INTERFACE FILE (task I0″ of Stage 4): the definition is complete; the statements below are
interfaces, proved by task G10a. See `docs/stage4-design.md`, Sections 1.2 (h) and 3.4, and
`docs/stage4-interfaces.md`.

`g_r(x) = heatKernel r x`. Facts used in Section 7.3:
* `∫ g_r = 1`, `∫ g_r² = (4π r)^{-1/2}`, `g_a ⋆ g_b = g_{a+b}`;
* `|g_r ⋆ f| ≤ sup |f|`, `‖g_r ⋆ f‖₂ ≤ ‖f‖₂`;
* `K(t,x) = g_t(x)²` and its space-time convolution powers
  `K^{⋆(k+1)}(t,x) = 2^{-(k+1)} t^{(k+1)/2 - 1} Γ((k+1)/2)⁻¹ g_{t/2}(x)` (`heatSqIter k`, indexed
  from `0`), with `K^{⋆(k+2)} = K ⋆ K^{⋆(k+1)}` and `K^{⋆(k+1)} ≤ ε_k K` on `(0,T]`, `∑ ε_k < ∞`.
  Their sum is the second moment (7.15) (`IsMildSolution.integral_sq`).

Proofs (task G10a): completion of the square and `integral_gaussian` for `g_a ⋆ g_b`;
`g_r(x)² = (4πr)^{-1/2} g_{r/2}(x)`; Jensen's inequality `(g_r ⋆ f)² ≤ g_r ⋆ f²` and Fubini for
the `L²` bound; for `K ⋆ K^{⋆(k+1)}`, Tonelli, the semigroup in space and the Beta integral
`∫_0^t s^{α-1}(t-s)^{β-1} ds = t^{α+β-1} B(α,β)` (from Mathlib's Beta distribution) in time;
`K^{⋆(k+1)} = √π (√t/2)^k Γ((k+1)/2)⁻¹ K` and the ratio test for `∑ ε_k`. Extra public lemma:
`heatSqIter_nonneg`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- `K^{⋆(k+1)}(t,x) = 2^{-(k+1)} t^{(k+1)/2 - 1} Γ((k+1)/2)⁻¹ g_{t/2}(x)`; for `k = 0` this is
`g_t(x)²` (`t > 0`). -/
def heatSqIter (k : ℕ) (t x : ℝ) : ℝ :=
  (2 : ℝ) ^ (-((k : ℝ) + 1)) * t ^ (((k : ℝ) + 1) / 2 - 1) / Real.Gamma (((k : ℝ) + 1) / 2) *
    heatKernel (t / 2) x

/-- The heat kernel is nonnegative. -/
theorem heatKernel_nonneg (t x : ℝ) : 0 ≤ heatKernel t x :=
  div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- `g_r(x) = exp(-x²/(2r)) / √(2πr)` written with the Gaussian `exp(-b x²)`, `b = 1/(2r)`. -/
private lemma heatKernel_eq_gauss (r x : ℝ) :
    heatKernel r x = Real.exp (-(1 / (2 * r)) * x ^ 2) / Real.sqrt (2 * Real.pi * r) := by
  unfold heatKernel; congr 2; ring

/-- The heat kernel is jointly measurable in `(t, x)`. -/
private lemma measurable_heatKernel_uncurry :
    Measurable (fun p : ℝ × ℝ => heatKernel p.1 p.2) := by
  unfold heatKernel; fun_prop

/-- `g_r(x) ≤ (2πr)^{-1/2}`. -/
private lemma heatKernel_le (r x : ℝ) : heatKernel r x ≤ 1 / Real.sqrt (2 * Real.pi * r) := by
  unfold heatKernel
  rcases le_or_gt r 0 with h | h
  · rw [Real.sqrt_eq_zero'.2 (by nlinarith [Real.pi_pos]), div_zero, div_zero]
  · gcongr
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x]) (by linarith)

/-- `∫ g_r = 1` (`r > 0`), with integrability. -/
theorem heatKernel_integral {r : ℝ} (hr : 0 < r) :
    Integrable (heatKernel r) ∧ ∫ x, heatKernel r x = 1 := by
  have hb : 0 < 1 / (2 * r) := by positivity
  have hfun : heatKernel r =
      fun x => Real.exp (-(1 / (2 * r)) * x ^ 2) / Real.sqrt (2 * Real.pi * r) :=
    funext (heatKernel_eq_gauss r)
  rw [hfun]
  refine ⟨(integrable_exp_neg_mul_sq hb).div_const _, ?_⟩
  rw [integral_div, integral_gaussian]
  have : Real.pi / (1 / (2 * r)) = 2 * Real.pi * r := by field_simp
  rw [this, div_self (Real.sqrt_pos.2 (by positivity)).ne']

/-- `g_r(x)² = (4πr)^{-1/2} g_{r/2}(x)` (`r > 0`). -/
private lemma heatKernel_sq_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    heatKernel r x ^ 2 = heatKernel (r / 2) x / Real.sqrt (4 * Real.pi * r) := by
  unfold heatKernel
  rw [div_div, ← Real.sqrt_mul (by positivity), div_pow, Real.sq_sqrt (by positivity),
    show 2 * Real.pi * (r / 2) * (4 * Real.pi * r) = (2 * Real.pi * r) ^ 2 by ring,
    Real.sqrt_sq (by positivity), ← Real.exp_nat_mul]
  congr 2
  field_simp
  ring

/-- `∫ g_r² = (4π r)^{-1/2}` (`r > 0`), with integrability. -/
theorem heatKernel_sq_integral {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => heatKernel r x ^ 2) ∧
      ∫ x, heatKernel r x ^ 2 = 1 / Real.sqrt (4 * Real.pi * r) := by
  have hfun : (fun x => heatKernel r x ^ 2) =
      fun x => heatKernel (r / 2) x / Real.sqrt (4 * Real.pi * r) :=
    funext (heatKernel_sq_eq hr)
  obtain ⟨hi, h1⟩ := heatKernel_integral (half_pos hr)
  rw [hfun, integral_div, h1]
  exact ⟨hi.div_const _, rfl⟩

/-- The semigroup property `g_a ⋆ g_b = g_{a+b}`. -/
theorem heatKernel_conv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    ∫ y, heatKernel a (x - y) * heatKernel b y = heatKernel (a + b) x := by
  set β := (a + b) / (2 * a * b) with hβ
  set m := b * x / (a + b) with hm
  have hβpos : 0 < β := by positivity
  have hfun : (fun y => heatKernel a (x - y) * heatKernel b y) = fun y =>
      Real.exp (-x ^ 2 / (2 * (a + b))) / (Real.sqrt (2 * Real.pi * a) *
        Real.sqrt (2 * Real.pi * b)) * Real.exp (-β * (y - m) ^ 2) := by
    funext y
    unfold heatKernel
    rw [div_mul_div_comm, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    rw [hβ, hm]
    field_simp
    ring
  rw [hfun, integral_const_mul, integral_sub_right_eq_self (fun y => Real.exp (-β * y ^ 2)) m,
    integral_gaussian]
  unfold heatKernel
  rw [div_mul_eq_mul_div, mul_div_assoc]
  congr 1
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div' _ (by positivity), ← Real.sqrt_inv]
  congr 1
  rw [hβ]
  field_simp

set_option linter.unusedVariables false in
/-- `|g_r ⋆ f| ≤ C` when `|f| ≤ C` (`r > 0`, `f` measurable). -/
theorem abs_heatConv_le {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (y : ℝ) : |heatConv r f y| ≤ C := by
  obtain ⟨hi, h1⟩ := heatKernel_integral hr
  have hi' : Integrable (fun x => heatKernel r (y - x) * C) := (hi.comp_sub_left y).mul_const C
  calc |heatConv r f y| = ‖∫ x, heatKernel r (y - x) * f x‖ := rfl
    _ ≤ ∫ x, heatKernel r (y - x) * C := by
      refine norm_integral_le_of_norm_le hi' (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg _ _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC x) (heatKernel_nonneg _ _)
    _ = C := by
      rw [integral_mul_const, integral_sub_left_eq_self (heatKernel r) volume y, h1, one_mul]

/-- Jensen's inequality for the heat kernel: `(g_r ⋆ f)(y)² ≤ (g_r ⋆ f²)(y)`, with the
integrability of `g_r(y - ·) f` and `g_r(y - ·) f²` (`f ∈ L²`). -/
private lemma heatConv_sq_le {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ} (hf : MemLp f 2 volume) (y : ℝ) :
    Integrable (fun x => heatKernel r (y - x) * f x) ∧
      Integrable (fun x => heatKernel r (y - x) * f x ^ 2) ∧
      heatConv r f y ^ 2 ≤ ∫ x, heatKernel r (y - x) * f x ^ 2 := by
  obtain ⟨hi, h1⟩ := heatKernel_integral hr
  have hφ : Integrable (fun x => heatKernel r (y - x)) := hi.comp_sub_left y
  have hφm : AEStronglyMeasurable (fun x => heatKernel r (y - x)) volume := hφ.1
  have hφ1 : ∫ x, heatKernel r (y - x) = 1 := by
    rw [integral_sub_left_eq_self (heatKernel r) volume y, h1]
  have hf2 : Integrable (fun x => f x ^ 2) := hf.integrable_sq
  have hφf2 : Integrable (fun x => heatKernel r (y - x) * f x ^ 2) :=
    hf2.bdd_mul hφm (c := 1 / Real.sqrt (2 * Real.pi * r)) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (heatKernel_nonneg _ _)]; exact heatKernel_le _ _)
  have hφf : Integrable (fun x => heatKernel r (y - x) * f x) := by
    refine ((hφ.add hφf2).div_const 2).mono' (hφm.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg _ _), Real.norm_eq_abs]
    have h0 := heatKernel_nonneg r (y - x)
    have : |f x| ≤ (1 + f x ^ 2) / 2 := by
      nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x)]
    calc heatKernel r (y - x) * |f x| ≤ heatKernel r (y - x) * ((1 + f x ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by simp only [Pi.add_apply]; ring
  refine ⟨hφf, hφf2, ?_⟩
  set m := heatConv r f y with hm
  have hm' : m = ∫ x, heatKernel r (y - x) * f x := rfl
  have hint : Integrable (fun x => heatKernel r (y - x) * f x ^ 2 -
      2 * m * (heatKernel r (y - x) * f x) + m ^ 2 * heatKernel r (y - x)) :=
    (hφf2.sub (hφf.const_mul _)).add (hφ.const_mul _)
  have h0 : 0 ≤ ∫ x, (heatKernel r (y - x) * f x ^ 2 -
      2 * m * (heatKernel r (y - x) * f x) + m ^ 2 * heatKernel r (y - x)) := by
    refine integral_nonneg fun x => ?_
    have := heatKernel_nonneg r (y - x)
    have : heatKernel r (y - x) * f x ^ 2 - 2 * m * (heatKernel r (y - x) * f x) +
        m ^ 2 * heatKernel r (y - x) = heatKernel r (y - x) * (f x - m) ^ 2 := by ring
    rw [this]; positivity
  rw [integral_add (f := fun x => heatKernel r (y - x) * f x ^ 2 -
      2 * m * (heatKernel r (y - x) * f x)) (g := fun x => m ^ 2 * heatKernel r (y - x))
      (hφf2.sub (hφf.const_mul _)) (hφ.const_mul _),
    integral_sub (f := fun x => heatKernel r (y - x) * f x ^ 2)
      (g := fun x => 2 * m * (heatKernel r (y - x) * f x)) hφf2 (hφf.const_mul _),
    integral_const_mul, integral_const_mul, hφ1, ← hm'] at h0
  have e : m ^ 2 = m * m := sq m
  linarith

/-- `‖g_r ⋆ f‖₂ ≤ ‖f‖₂` (`r > 0`, `f ∈ L²`), with integrability. -/
theorem heatConv_sq_integral_le {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Integrable (fun y => heatConv r f y ^ 2) ∧
      ∫ y, heatConv r f y ^ 2 ≤ ∫ x, f x ^ 2 := by
  obtain ⟨hi, h1⟩ := heatKernel_integral hr
  have hgm : Measurable (fun p : ℝ × ℝ => heatKernel r (p.1 - p.2)) := by
    unfold heatKernel; fun_prop
  have hHm : AEStronglyMeasurable (fun p : ℝ × ℝ => heatKernel r (p.1 - p.2) * f p.2 ^ 2)
      (volume.prod volume) :=
    hgm.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_snd.pow 2)
  have hHi : Integrable (fun p : ℝ × ℝ => heatKernel r (p.1 - p.2) * f p.2 ^ 2)
      (volume.prod volume) := by
    refine (integrable_prod_iff' hHm).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact (hi.comp_sub_right x).mul_const (f x ^ 2)
    · refine hf.integrable_sq.congr (Eventually.of_forall fun x => ?_)
      have : ∀ y, ‖heatKernel r (y - x) * f x ^ 2‖ = heatKernel r (y - x) * f x ^ 2 := fun y =>
        Real.norm_of_nonneg (mul_nonneg (heatKernel_nonneg _ _) (sq_nonneg _))
      simp only [this]
      rw [integral_mul_const, integral_sub_right_eq_self (heatKernel r) x, h1, one_mul]
  have hG : Integrable (fun y => ∫ x, heatKernel r (y - x) * f x ^ 2) := hHi.integral_prod_left
  have hGeq : ∫ y, ∫ x, heatKernel r (y - x) * f x ^ 2 = ∫ x, f x ^ 2 := by
    rw [integral_integral_swap (f := fun y x => heatKernel r (y - x) * f x ^ 2) hHi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const, integral_sub_right_eq_self (heatKernel r) x, h1, one_mul]
  have hconvm : AEStronglyMeasurable (heatConv r f) volume :=
    (hgm.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  have hle : ∀ y, heatConv r f y ^ 2 ≤ ∫ x, heatKernel r (y - x) * f x ^ 2 :=
    fun y => (heatConv_sq_le hr hf y).2.2
  have hsq : Integrable (fun y => heatConv r f y ^ 2) :=
    hG.mono' (hconvm.pow 2) (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle y)
  exact ⟨hsq, (integral_mono hsq hG hle).trans hGeq.le⟩

/-- `K^{⋆1} = K`: `heatSqIter 0 t x = g_t(x)²` for `t > 0`. -/
theorem heatSqIter_zero {t : ℝ} (ht : 0 < t) (x : ℝ) : heatSqIter 0 t x = heatKernel t x ^ 2 := by
  rw [heatKernel_sq_eq ht, heatSqIter]
  simp only [Nat.cast_zero, zero_add]
  have h1 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have h2 : t ^ ((1 : ℝ) / 2 - 1) = 1 / Real.sqrt t := by
    rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg ht.le, Real.sqrt_eq_rpow,
      inv_eq_one_div]
  have h3 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h4 := Real.sqrt_pos.2 ht
  have h5 := Real.sqrt_pos.2 Real.pi_pos
  rw [h1, h2, Real.Gamma_one_half_eq, h3]
  field_simp

/-- `K^{⋆(k+1)}(t,x) ≥ 0` (it vanishes for `t ≤ 0`, since then `g_{t/2} = 0`). -/
theorem heatSqIter_nonneg (k : ℕ) (t x : ℝ) : 0 ≤ heatSqIter k t x := by
  rcases le_or_gt t 0 with ht | ht
  · have : heatKernel (t / 2) x = 0 := by
      unfold heatKernel
      rw [Real.sqrt_eq_zero'.2 (by nlinarith [Real.pi_pos]), div_zero]
    simp [heatSqIter, this]
  · have := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1) / 2 by positivity)
    exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)) this.le)
      (heatKernel_nonneg _ _)

/-- Linear change of variables `x = a u` in a lower integral on `ℝ` (`a > 0`). -/
private lemma heat_lintegral_scale (f : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, f x = ENNReal.ofReal a * ∫⁻ u, f (a * u) := by
  have h := lintegral_map_equiv (μ := volume) f (MeasurableEquiv.mulLeft₀ a ha.ne')
  rw [MeasurableEquiv.coe_mulLeft₀, Real.map_volume_mul_left ha.ne', lintegral_smul_measure] at h
  rw [← h, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul ha.le, abs_of_pos (inv_pos.2 ha),
    mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one, one_mul]

/-- The Beta integral on `(0,t)`:
`∫_0^t s^{α-1} (t-s)^{β-1} ds = t^{α+β-1} B(α,β)` (`α, β, t > 0`), as a lower integral. -/
private lemma heat_lintegral_beta {α β t : ℝ} (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    ∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal (s ^ (α - 1) * (t - s) ^ (β - 1)) =
      ENNReal.ofReal (t ^ (α + β - 1) * ProbabilityTheory.beta α β) := by
  have hpos := ProbabilityTheory.beta_pos hα hβ
  have hB : ∫⁻ u in Set.Ioo 0 1, ENNReal.ofReal (u ^ (α - 1) * (1 - u) ^ (β - 1)) =
      ENNReal.ofReal (ProbabilityTheory.beta α β) := by
    have h := ProbabilityTheory.lintegral_betaPDF_eq_one hα hβ
    rw [ProbabilityTheory.lintegral_betaPDF] at h
    simp_rw [mul_assoc, ENNReal.ofReal_mul (one_div_pos.2 hpos).le] at h
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    calc _ = ENNReal.ofReal (ProbabilityTheory.beta α β) *
          (ENNReal.ofReal (1 / ProbabilityTheory.beta α β) *
            ∫⁻ u in Set.Ioo 0 1, ENNReal.ofReal (u ^ (α - 1) * (1 - u) ^ (β - 1))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne',
            ENNReal.ofReal_one, one_mul]
      _ = _ := by rw [h, mul_one]
  rw [← lintegral_indicator measurableSet_Ioo, heat_lintegral_scale _ ht]
  have key : ∀ u, (Set.Ioo 0 t).indicator
      (fun s => ENNReal.ofReal (s ^ (α - 1) * (t - s) ^ (β - 1))) (t * u) =
      ENNReal.ofReal (t ^ (α + β - 2)) * (Set.Ioo 0 1).indicator
        (fun u => ENNReal.ofReal (u ^ (α - 1) * (1 - u) ^ (β - 1))) u := by
    intro u
    by_cases hu : u ∈ Set.Ioo 0 1
    · have hmem : t * u ∈ Set.Ioo 0 t := ⟨mul_pos ht hu.1, by nlinarith [hu.2]⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow ht.le hu.1.le, show t - t * u = t * (1 - u) by ring,
        Real.mul_rpow ht.le (by linarith [hu.2]), show α + β - 2 = (α - 1) + (β - 1) by ring,
        Real.rpow_add ht]
      ring
    · have hmem : t * u ∉ Set.Ioo 0 t := fun h => hu ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hu, mul_zero]
  simp_rw [key]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioo, hB,
    ← mul_assoc, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show α + β - 1 = 1 + (α + β - 2) by ring, Real.rpow_add ht, Real.rpow_one]

/-- The space integral in `K ⋆ K^{⋆(k+1)}`: for `0 < s < t`,
`∫ g_{t-s}(x-y)² K^{⋆(k+1)}(s,y) dy = D(s) g_{t/2}(x)` (Gaussian semigroup). -/
private lemma heat_lintegral_space (k : ℕ) {s t : ℝ} (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2 * heatSqIter k s y) =
      ENNReal.ofReal ((2 : ℝ) ^ (-((k : ℝ) + 1)) * s ^ (((k : ℝ) + 1) / 2 - 1) /
        Real.Gamma (((k : ℝ) + 1) / 2) / Real.sqrt (4 * Real.pi * (t - s)) *
          heatKernel (t / 2) x) := by
  have hts : 0 < t - s := by linarith
  set D := (2 : ℝ) ^ (-((k : ℝ) + 1)) * s ^ (((k : ℝ) + 1) / 2 - 1) /
    Real.Gamma (((k : ℝ) + 1) / 2) / Real.sqrt (4 * Real.pi * (t - s)) with hD
  have hDpos : 0 ≤ D := by
    have := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1) / 2 by positivity)
    rw [hD]; exact div_nonneg (div_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg hs.le _)) this.le) (Real.sqrt_nonneg _)
  have hpt : ∀ y, heatKernel (t - s) (x - y) ^ 2 * heatSqIter k s y =
      D * (heatKernel ((t - s) / 2) (x - y) * heatKernel (s / 2) y) := by
    intro y
    rw [heatKernel_sq_eq hts, heatSqIter, hD]
    ring
  have hint : Integrable (fun y => heatKernel ((t - s) / 2) (x - y) * heatKernel (s / 2) y) := by
    refine (heatKernel_integral (half_pos hs)).1.bdd_mul
      (c := 1 / Real.sqrt (2 * Real.pi * ((t - s) / 2))) ?_ (Eventually.of_forall fun y => ?_)
    · exact (by unfold heatKernel; fun_prop :
        Measurable fun y => heatKernel ((t - s) / 2) (x - y)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (heatKernel_nonneg _ _)]; exact heatKernel_le _ _
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul D)
    (Eventually.of_forall fun y => mul_nonneg hDpos
      (mul_nonneg (heatKernel_nonneg _ _) (heatKernel_nonneg _ _))),
    integral_const_mul, heatKernel_conv (half_pos hts) (half_pos hs),
    show (t - s) / 2 + s / 2 = t / 2 by ring]

/-- `K^{⋆(k+2)} = K ⋆ K^{⋆(k+1)}` (space-time convolution on `(0,t) × ℝ`), with integrability of
the integrand. -/
theorem heatSqIter_succ (k : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => heatKernel (t - p.1) (x - p.2) ^ 2 * heatSqIter k p.1 p.2)
        (Set.Ioo 0 t ×ˢ Set.univ) ∧
      heatSqIter (k + 1) t x =
        ∫ p in Set.Ioo 0 t ×ˢ Set.univ, heatKernel (t - p.1) (x - p.2) ^ 2 * heatSqIter k p.1 p.2 := by
  set Φ : ℝ × ℝ → ℝ := fun p => heatKernel (t - p.1) (x - p.2) ^ 2 * heatSqIter k p.1 p.2 with hΦ
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => mul_nonneg (sq_nonneg _) (heatSqIter_nonneg _ _ _)
  have hΦm : Measurable Φ := by
    rw [hΦ]; simp only [heatSqIter, heatKernel]; fun_prop
  have hαpos : 0 < ((k : ℝ) + 1) / 2 := by positivity
  have hΓ := Real.Gamma_pos_of_pos hαpos
  set E := (2 : ℝ) ^ (-((k : ℝ) + 1)) / Real.Gamma (((k : ℝ) + 1) / 2) /
    Real.sqrt (4 * Real.pi) * heatKernel (t / 2) x with hE
  have hEnn : 0 ≤ E := by
    rw [hE]; exact mul_nonneg (div_nonneg (div_nonneg (by positivity) hΓ.le)
      (Real.sqrt_nonneg _)) (heatKernel_nonneg _ _)
  have hlin : ∫⁻ p in Set.Ioo 0 t ×ˢ Set.univ, ENNReal.ofReal (Φ p) =
      ENNReal.ofReal (heatSqIter (k + 1) t x) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod _ hΦm.ennreal_ofReal.aemeasurable]
    have hcongr : Set.EqOn (fun s => ∫⁻ y, ENNReal.ofReal (Φ (s, y)))
        (fun s => ENNReal.ofReal E * ENNReal.ofReal
          (s ^ (((k : ℝ) + 1) / 2 - 1) * (t - s) ^ ((1 : ℝ) / 2 - 1))) (Set.Ioo 0 t) := by
      intro s hs
      have hts : 0 < t - s := by linarith [hs.2]
      simp only [hΦ]
      rw [heat_lintegral_space k hs.1 hs.2 x, ← ENNReal.ofReal_mul hEnn]
      congr 1
      have h1 : (t - s) ^ ((1 : ℝ) / 2 - 1) = (Real.sqrt (t - s))⁻¹ := by
        rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg hts.le, Real.sqrt_eq_rpow]
      have h2 : Real.sqrt (4 * Real.pi * (t - s)) = Real.sqrt (4 * Real.pi) * Real.sqrt (t - s) :=
        Real.sqrt_mul (by positivity) _
      have h3 := Real.sqrt_pos.2 hts
      have h4 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.2 (by positivity)
      rw [h1, h2, hE]
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioo hcongr,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      heat_lintegral_beta hαpos (by norm_num : (0 : ℝ) < 1 / 2) ht, ← ENNReal.ofReal_mul hEnn]
    congr 1
    have e1 : (((k + 1 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 / 2 := by push_cast; ring
    have e3 : (2 : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) + 1)) = 2 ^ (-((k : ℝ) + 1)) / 2 := by
      push_cast
      rw [show -((k : ℝ) + 1 + 1) = -((k : ℝ) + 1) + (-1) by ring, Real.rpow_add two_pos,
        Real.rpow_neg_one]
      ring
    have e4 : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hΓ' := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1) / 2 + 1 / 2 by positivity)
    have h5 := Real.sqrt_pos.2 Real.pi_pos
    rw [heatSqIter, e1, e3, hE, ProbabilityTheory.beta, Real.Gamma_one_half_eq, e4]
    field_simp
  have hint : IntegrableOn Φ (Set.Ioo 0 t ×ˢ Set.univ) :=
    ⟨hΦm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hΦnn)).2
      (hlin ▸ ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hΦnn) hΦm.aestronglyMeasurable, hlin,
    ENNReal.toReal_ofReal (heatSqIter_nonneg _ _ _)]

/-- `K^{⋆(k+1)}(t,x) = √π (√t/2)^k Γ((k+1)/2)⁻¹ g_t(x)²` (`t > 0`). -/
private lemma heatSqIter_eq_mul_sq (k : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSqIter k t x = Real.sqrt Real.pi * (Real.sqrt t / 2) ^ k /
      Real.Gamma (((k : ℝ) + 1) / 2) * heatKernel t x ^ 2 := by
  rw [heatKernel_sq_eq ht, heatSqIter]
  have h1 : t ^ (((k : ℝ) + 1) / 2 - 1) = Real.sqrt t ^ k / Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
    congr 1; ring
  have h2 : (2 : ℝ) ^ (-((k : ℝ) + 1)) = 1 / (2 ^ k * 2) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_add_one two_ne_zero, Real.rpow_natCast, one_div]
  have h3 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h4 := Real.sqrt_pos.2 ht
  have h5 := Real.sqrt_pos.2 Real.pi_pos
  have h6 := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1) / 2 by positivity)
  rw [h1, h2, h3, div_pow]
  field_simp

/-- `∑_m b^m / Γ(s₀ + m) < ∞` (`s₀ > 0`, `b ≥ 0`), by the ratio test. -/
private lemma heat_summable_pow_div_Gamma {s₀ b : ℝ} (hs : 0 < s₀) (hb : 0 ≤ b) :
    Summable (fun m : ℕ => b ^ m / Real.Gamma (s₀ + m)) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [eventually_ge_atTop ⌈2 * b⌉₊] with m hm
  have hm' : 2 * b ≤ m := Nat.ceil_le.1 hm
  have hΓ := Real.Gamma_pos_of_pos (show 0 < s₀ + m by positivity)
  have hsucc : Real.Gamma (s₀ + ((m + 1 : ℕ) : ℝ)) = (s₀ + m) * Real.Gamma (s₀ + m) := by
    push_cast; rw [← add_assoc, Real.Gamma_add_one (show (0 : ℝ) < s₀ + m by positivity).ne']
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hsucc, pow_succ]
  calc b ^ m * b / ((s₀ + m) * Real.Gamma (s₀ + m))
      = b / (s₀ + m) * (b ^ m / Real.Gamma (s₀ + m)) := by field_simp
    _ ≤ 1 / 2 * (b ^ m / Real.Gamma (s₀ + m)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [div_le_iff₀ (by positivity)]
      linarith

/-- `K^{⋆(k+1)} ≤ ε_k K` on `(0,T]`, with `∑ ε_k < ∞`. -/
theorem heatSqIter_le (T : ℝ) :
    ∃ ε : ℕ → ℝ, Summable ε ∧ (∀ k, 0 ≤ ε k) ∧
      ∀ k, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, heatSqIter k t x ≤ ε k * heatKernel t x ^ 2 := by
  set a := Real.sqrt (max T 0) / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨fun k => Real.sqrt Real.pi * a ^ k / Real.Gamma (((k : ℝ) + 1) / 2), ?_, ?_, ?_⟩
  · refine Summable.even_add_odd ?_ ?_
    · have h := (heat_summable_pow_div_Gamma (by norm_num : (0 : ℝ) < 1 / 2)
        (sq_nonneg a)).mul_left (Real.sqrt Real.pi)
      refine h.congr fun m => ?_
      rw [← pow_mul, show (((2 * m : ℕ) : ℝ) + 1) / 2 = 1 / 2 + (m : ℝ) by push_cast; ring]
      ring
    · have h := (heat_summable_pow_div_Gamma (by norm_num : (0 : ℝ) < 1)
        (sq_nonneg a)).mul_left (Real.sqrt Real.pi * a)
      refine h.congr fun m => ?_
      rw [← pow_mul, pow_succ,
        show (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = 1 + (m : ℝ) by push_cast; ring]
      ring
  · intro k
    have := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1) / 2 by positivity)
    positivity
  · intro k t ht x
    rw [heatSqIter_eq_mul_sq k ht.1 x]
    have := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1) / 2 by positivity)
    have hsa : Real.sqrt t / 2 ≤ a := by
      rw [ha]; gcongr; exact le_max_of_le_left ht.2
    dsimp only
    gcongr

end QSSEPtoKPZ
