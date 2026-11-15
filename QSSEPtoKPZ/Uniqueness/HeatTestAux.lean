/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Gaussian averages and the heat equation for `g_r ⋆ f` (task G10b, auxiliary)

For `h : ℝ → ℝ` bounded and continuous, the Gaussian average
`heatTestGauss h r y = ∫ g_1(z) h(y - √r z) dz` (`√r = 0` for `r ≤ 0`) satisfies:
* `heatTestGauss h r y = (g_r ⋆ h)(y)` for `r > 0` (change of variables `x = y - √r z`), and
  `= h(y)` for `r ≤ 0` (`∫ g_1 = 1`);
* it is jointly continuous in `(r, y) ∈ ℝ²` (dominated convergence, bound `sup|h| g_1`) and
  bounded by `sup |h|`;
* `∂_y heatTestGauss h r y = heatTestGauss h' r y` (differentiation under the integral sign).

For `f ∈ C_c^∞(ℝ)` and `r > 0`, `∂_r (g_r ⋆ f)(y) = ½ (g_r ⋆ f'')(y)`
(`heatTest_hasDerivAt_heatConv_time`): differentiate under the integral sign in the form
`∫ g_r(y - x) f(x) dx`, use `∂_r g_r = ½ ∂_w² g_r`, and identify
`∫ ∂_w² g_r(y - x) f(x) dx = ∂_y² (g_r ⋆ f)(y) = (g_r ⋆ f'')(y)` by computing the second space
derivative in both forms.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The Gaussian average `∫ g_1(z) h(y - √r z) dz`; equals `(g_r ⋆ h)(y)` for `r > 0` and `h(y)`
for `r ≤ 0`. -/
def heatTestGauss (h : ℝ → ℝ) (r y : ℝ) : ℝ :=
  ∫ z, heatKernel 1 z * h (y - Real.sqrt r * z)

/-- The standard Gaussian density is continuous. -/
private lemma continuous_heatKernel_one : Continuous (heatKernel 1) := by
  unfold heatKernel; fun_prop

/-- `heatTestGauss h r y = h y` for `r ≤ 0`. -/
theorem heatTestGauss_of_nonpos (h : ℝ → ℝ) {r : ℝ} (hr : r ≤ 0) (y : ℝ) :
    heatTestGauss h r y = h y := by
  simp only [heatTestGauss, Real.sqrt_eq_zero'.2 hr, zero_mul, sub_zero]
  rw [integral_mul_const, (heatKernel_integral one_pos).2, one_mul]

/-- `√r g_r(√r z) = g_1(z)` (`r > 0`). -/
private lemma heatKernel_scale {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Real.sqrt r * heatKernel r (Real.sqrt r * z) = heatKernel 1 z := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  unfold heatKernel
  rw [mul_pow, Real.sq_sqrt hr.le, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi) r,
    mul_one, mul_one]
  have : -(r * z ^ 2) / (2 * r) = -z ^ 2 / 2 := by field_simp
  rw [this]
  field_simp

/-- `heatTestGauss h r y = (g_r ⋆ h)(y)` for `r > 0`. -/
theorem heatTestGauss_eq_heatConv (h : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    heatTestGauss h r y = heatConv r h y := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  set G : ℝ → ℝ := fun x => heatKernel r x * h (y - x) with hG
  have h1 : heatConv r h y = ∫ x, G x := by
    rw [← integral_sub_left_eq_self G volume y]
    simp only [heatConv, hG, sub_sub_cancel]
  have h2 : heatTestGauss h r y = Real.sqrt r * ∫ z, G (Real.sqrt r * z) := by
    rw [← integral_const_mul]
    unfold heatTestGauss
    congr 1
    funext z
    simp only [hG, ← mul_assoc, heatKernel_scale hr]
  rw [h2, h1, Measure.integral_comp_mul_left G, smul_eq_mul, abs_of_pos (inv_pos.2 hs), ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul]

/-- `|heatTestGauss h r y| ≤ M` when `|h| ≤ M`. -/
theorem abs_heatTestGauss_le {h : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |h x| ≤ M) (r y : ℝ) :
    |heatTestGauss h r y| ≤ M := by
  have hint := heatKernel_integral (r := 1) one_pos
  rw [← Real.norm_eq_abs]
  calc ‖heatTestGauss h r y‖ ≤ ∫ z, heatKernel 1 z * M := by
        refine norm_integral_le_of_norm_le (hint.1.mul_const M) (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg 1 z)]
        exact mul_le_mul_of_nonneg_left (hM _) (heatKernel_nonneg 1 z)
    _ = M := by rw [integral_mul_const, hint.2, one_mul]

/-- `(r, y) ↦ heatTestGauss h r y` is continuous on `ℝ²` (`h` continuous and bounded). -/
theorem continuous_heatTestGauss {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ x, |h x| ≤ M) : Continuous fun p : ℝ × ℝ => heatTestGauss h p.1 p.2 := by
  unfold heatTestGauss
  refine continuous_of_dominated (bound := fun z => heatKernel 1 z * M) (fun p => ?_)
    (fun p => Eventually.of_forall fun z => ?_) ((heatKernel_integral one_pos).1.mul_const M)
    (Eventually.of_forall fun z => ?_)
  · exact (continuous_heatKernel_one.mul (hh.comp (by fun_prop))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg 1 z)]
    exact mul_le_mul_of_nonneg_left (hM _) (heatKernel_nonneg 1 z)
  · exact continuous_const.mul (hh.comp (by fun_prop))

/-- `∂_y heatTestGauss h r y = heatTestGauss h' r y` (`h' ` continuous and bounded). -/
theorem hasDerivAt_heatTestGauss {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hh' : Continuous h') {M M' : ℝ} (hM : ∀ x, |h x| ≤ M) (hM' : ∀ x, |h' x| ≤ M') (r y : ℝ) :
    HasDerivAt (heatTestGauss h r) (heatTestGauss h' r y) y := by
  have hh : Continuous h := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hint := (heatKernel_integral one_pos).1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y z => heatKernel 1 z * h (y - Real.sqrt r * z))
    (F' := fun y z => heatKernel 1 z * h' (y - Real.sqrt r * z)) (x₀ := y)
    (bound := fun z => heatKernel 1 z * M') Filter.univ_mem
    (Eventually.of_forall fun y' =>
      (continuous_heatKernel_one.mul (hh.comp (by fun_prop))).aestronglyMeasurable)
    ((hint.mul_const M).mono' (continuous_heatKernel_one.mul
      (hh.comp (by fun_prop))).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg 1 z)]
        exact mul_le_mul_of_nonneg_left (hM _) (heatKernel_nonneg 1 z)))
    (continuous_heatKernel_one.mul (hh'.comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun z y' _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg 1 z)]
      exact mul_le_mul_of_nonneg_left (hM' _) (heatKernel_nonneg 1 z))
    (hint.mul_const M')
    (Eventually.of_forall fun z y' _ => by
      have := ((hd (y' - Real.sqrt r * z)).comp y' ((hasDerivAt_id y').sub_const
        (Real.sqrt r * z))).const_mul (heatKernel 1 z)
      simpa using this)
  exact key.2

/-- The iterated derivatives of `f ∈ C_c^∞(ℝ)`: continuous, compactly supported, bounded, and
`(f^{(k)})' = f^{(k+1)}`. -/
theorem heatTest_iteratedDeriv_props {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (k : ℕ) :
    Continuous (iteratedDeriv k f) ∧ HasCompactSupport (iteratedDeriv k f) ∧
      (∀ x, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x) ∧
      ∃ M, ∀ x, |iteratedDeriv k f x| ≤ M := by
  have hc : Continuous (iteratedDeriv k f) := hf.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  have hs : HasCompactSupport (iteratedDeriv k f) := by
    clear hc
    induction k with
    | zero => simpa [iteratedDeriv_zero] using hfc
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  refine ⟨hc, hs, fun x => ?_, hc.bounded_above_of_compact_support hs⟩
  rw [iteratedDeriv_succ]
  exact ((hf.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)) x).hasDerivAt

/-- Differentiation under the integral sign against a continuous compactly supported `f`:
if `∂_p F(p, x) = F'(p, x)` for `p` near `p₀`, with `F'` jointly continuous, then
`∂_p ∫ F(p, x) f(x) dx = ∫ F'(p₀, x) f(x) dx`. -/
private lemma heatTest_hasDerivAt_integral_mul {F F' : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {p₀ ε : ℝ} (hε : 0 < ε)
    (hF : ∀ p, Continuous (F p))
    (hF' : ContinuousOn (Function.uncurry F') (Metric.closedBall p₀ ε ×ˢ Set.univ))
    (hd : ∀ p ∈ Metric.ball p₀ ε, ∀ x, HasDerivAt (F · x) (F' p x) p) :
    HasDerivAt (fun p => ∫ x, F p x * f x) (∫ x, F' p₀ x * f x) p₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ ε).prod hfc).exists_bound_of_continuousOn
    (hF'.mono (Set.prod_mono le_rfl (Set.subset_univ _)))
  have hF'0 : Continuous (F' p₀) := by
    have : ContinuousOn (Function.uncurry F' ∘ fun x => (p₀, x)) Set.univ :=
      hF'.comp (Continuous.continuousOn (by fun_prop))
        (fun x _ => ⟨Metric.mem_closedBall_self hε.le, Set.mem_univ _⟩)
    exact continuousOn_univ.1 this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun p x => F p x * f x) (F' := fun p x => F' p x * f x) (x₀ := p₀)
    (bound := fun x => C * |f x|) (Metric.ball_mem_nhds p₀ hε)
    (Eventually.of_forall fun p => ((hF p).mul hf).aestronglyMeasurable)
    (((hF p₀).mul hf).integrable_of_hasCompactSupport hfc.mul_left)
    (hF'0.mul hf).aestronglyMeasurable
    (Eventually.of_forall fun x p hp => ?_)
    ((hf.integrable_of_hasCompactSupport hfc).abs.const_mul C)
    (Eventually.of_forall fun x p hp => (hd p hp x).mul_const (f x))
  · exact key.2
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x ∈ tsupport f
    · have := hC (p, x) ⟨Metric.ball_subset_closedBall hp, hx⟩
      exact mul_le_mul_of_nonneg_right (by simpa using this) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp

/-- `∂_w g_r(w) = -(w/r) g_r(w)`. -/
private def heatTestKer1 (r w : ℝ) : ℝ := -(w / r) * heatKernel r w

/-- `∂_w² g_r(w) = (w²/r² - 1/r) g_r(w)`. -/
private def heatTestKer2 (r w : ℝ) : ℝ := (w ^ 2 / r ^ 2 - 1 / r) * heatKernel r w

private lemma hasDerivAt_heatKernel_space {r : ℝ} (hr : 0 < r) (w : ℝ) :
    HasDerivAt (heatKernel r) (heatTestKer1 r w) w := by
  show HasDerivAt (fun w => Real.exp (-w ^ 2 / (2 * r)) / Real.sqrt (2 * Real.pi * r)) _ w
  have h1 : HasDerivAt (fun w : ℝ => -w ^ 2 / (2 * r)) (-(2 * w) / (2 * r)) w := by
    simpa using ((hasDerivAt_pow 2 w).neg.div_const (2 * r))
  convert (h1.exp).div_const (Real.sqrt (2 * Real.pi * r)) using 1
  unfold heatTestKer1 heatKernel
  field_simp

private lemma hasDerivAt_heatTestKer1 {r : ℝ} (hr : 0 < r) (w : ℝ) :
    HasDerivAt (heatTestKer1 r) (heatTestKer2 r w) w := by
  have := (((hasDerivAt_id' w).div_const r).neg).mul (hasDerivAt_heatKernel_space hr w)
  convert this using 1
  · funext v; simp [heatTestKer1]
  unfold heatTestKer1 heatTestKer2
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- `∂_r g_r(w) = ½ ∂_w² g_r(w)` (`r > 0`). -/
private lemma hasDerivAt_heatKernel_time {r : ℝ} (hr : 0 < r) (w : ℝ) :
    HasDerivAt (fun r => heatKernel r w) (heatTestKer2 r w / 2) r := by
  have h1 : HasDerivAt (fun r : ℝ => -w ^ 2 / 2 * r⁻¹) (-w ^ 2 / 2 * (-(r ^ 2)⁻¹)) r :=
    (hasDerivAt_inv hr.ne').const_mul _
  have h2 : HasDerivAt (fun r : ℝ => Real.sqrt (2 * Real.pi * r))
      (2 * Real.pi * 1 / (2 * Real.sqrt (2 * Real.pi * r))) r :=
    ((hasDerivAt_id r).const_mul (2 * Real.pi)).sqrt
      (by simp only [id]; exact (mul_pos Real.two_pi_pos hr).ne')
  have hc : 0 < Real.sqrt (2 * Real.pi * r) := Real.sqrt_pos.2 (mul_pos Real.two_pi_pos hr)
  have key := (h1.exp).div h2 hc.ne'
  have hfun : (fun r => heatKernel r w) =
      fun r => Real.exp (-w ^ 2 / 2 * r⁻¹) / Real.sqrt (2 * Real.pi * r) := by
    funext r; unfold heatKernel; congr 2; ring
  rw [hfun]
  convert key using 1
  have hc2 : Real.sqrt (2 * Real.pi * r) ^ 2 = 2 * Real.pi * r := Real.sq_sqrt (mul_pos Real.two_pi_pos hr).le
  unfold heatTestKer2 heatKernel
  rw [show -w ^ 2 / (2 * r) = -w ^ 2 / 2 * r⁻¹ by ring]
  generalize Real.exp (-w ^ 2 / 2 * r⁻¹) = E
  generalize Real.sqrt (2 * Real.pi * r) = c at hc hc2 ⊢
  have hπ : Real.pi = c ^ 2 / (2 * r) := by field_simp; linarith
  rw [hπ]
  field_simp

/-- For `f ∈ C_c^∞(ℝ)` and `r > 0`: `∂_r (g_r ⋆ f)(y) = ½ (g_r ⋆ f'')(y)`. -/
theorem heatTest_hasDerivAt_heatConv_time {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    HasDerivAt (fun r => heatConv r f y) (heatConv r (iteratedDeriv 2 f) y / 2) r := by
  obtain ⟨hc0, hs0, -, -⟩ := heatTest_iteratedDeriv_props hf hfc 0
  rw [iteratedDeriv_zero] at hc0 hs0
  -- the time derivative under the integral sign
  have hA : HasDerivAt (fun r => heatConv r f y) (∫ x, heatTestKer2 r (y - x) / 2 * f x) r := by
    refine heatTest_hasDerivAt_integral_mul (F := fun r x => heatKernel r (y - x))
      (F' := fun r x => heatTestKer2 r (y - x) / 2) hc0 hs0 (half_pos hr)
      (fun p => by unfold heatKernel; fun_prop) ?_ ?_
    · intro p hp
      have hp0 : 0 < p.1 := by
        have := (Metric.mem_closedBall.1 hp.1); rw [Real.dist_eq] at this
        linarith [neg_abs_le (p.1 - r)]
      apply ContinuousAt.continuousWithinAt
      simp only [heatTestKer2, heatKernel]
      fun_prop (disch := first | exact hp0.ne' | (apply ne_of_gt; nlinarith [Real.pi_pos]) |
        (rw [Real.sqrt_ne_zero']; nlinarith [Real.pi_pos]) | (apply pow_ne_zero; exact hp0.ne'))
    · intro p hp x
      have hp0 : 0 < p := by
        have := (Metric.mem_ball.1 hp); rw [Real.dist_eq] at this
        linarith [neg_abs_le (p - r)]
      exact hasDerivAt_heatKernel_time hp0 (y - x)
  -- the second space derivative, in kernel form
  have hcont : ∀ (K : ℝ → ℝ), Continuous K →
      ContinuousOn (Function.uncurry fun (y : ℝ) (x : ℝ) => K (y - x)) (Metric.closedBall y 1 ×ˢ Set.univ) :=
    fun K hK => (hK.comp (by fun_prop)).continuousOn
  have hK1c : Continuous (heatTestKer1 r) := continuous_iff_continuousAt.2 fun w =>
    (hasDerivAt_heatTestKer1 hr w).continuousAt
  have hK2c : Continuous (heatTestKer2 r) := by
    unfold heatTestKer2 heatKernel
    fun_prop (disch := first | exact hr.ne' | (apply ne_of_gt; nlinarith [Real.pi_pos]) |
        (rw [Real.sqrt_ne_zero']; nlinarith [Real.pi_pos]) | (apply pow_ne_zero; exact hr.ne'))
  have hB1 : ∀ y, HasDerivAt (heatConv r f) (∫ x, heatTestKer1 r (y - x) * f x) y := fun y =>
    heatTest_hasDerivAt_integral_mul (F := fun y x => heatKernel r (y - x))
      (F' := fun y x => heatTestKer1 r (y - x)) hc0 hs0 one_pos
      (fun p => by unfold heatKernel; fun_prop) ((hK1c.comp (by fun_prop)).continuousOn)
      (fun p _ x => by
        exact (hasDerivAt_heatKernel_space hr (p - x)).comp_sub_const p x)
  have hB2 : HasDerivAt (fun y => ∫ x, heatTestKer1 r (y - x) * f x)
      (∫ x, heatTestKer2 r (y - x) * f x) y :=
    heatTest_hasDerivAt_integral_mul (F := fun y x => heatTestKer1 r (y - x))
      (F' := fun y x => heatTestKer2 r (y - x)) hc0 hs0 one_pos
      (fun p => hK1c.comp (by fun_prop)) ((hK2c.comp (by fun_prop)).continuousOn)
      (fun p _ x => by
        exact (hasDerivAt_heatTestKer1 hr (p - x)).comp_sub_const p x)
  -- the same derivatives, in convolution form
  have hC : ∀ k y, HasDerivAt (heatConv r (iteratedDeriv k f))
      (heatConv r (iteratedDeriv (k + 1) f) y) y := by
    intro k y
    obtain ⟨-, -, hd, M, hM⟩ := heatTest_iteratedDeriv_props hf hfc k
    obtain ⟨hc', -, -, M', hM'⟩ := heatTest_iteratedDeriv_props hf hfc (k + 1)
    have := hasDerivAt_heatTestGauss hd hc' hM hM' r y
    rwa [heatTestGauss_eq_heatConv _ hr,
      show heatTestGauss (iteratedDeriv k f) r = heatConv r (iteratedDeriv k f) from
        funext fun y => heatTestGauss_eq_heatConv _ hr y] at this
  have hE1 : (fun y => ∫ x, heatTestKer1 r (y - x) * f x) = heatConv r (iteratedDeriv 1 f) := by
    funext y
    have := hC 0 y
    rw [iteratedDeriv_zero] at this
    exact (hB1 y).unique this
  have hE2 : ∫ x, heatTestKer2 r (y - x) * f x = heatConv r (iteratedDeriv 2 f) y := by
    rw [hE1] at hB2
    exact hB2.unique (hC 1 y)
  convert hA using 1
  rw [← hE2, ← integral_div]
  congr 1; funext x; ring

end QSSEPtoKPZ
