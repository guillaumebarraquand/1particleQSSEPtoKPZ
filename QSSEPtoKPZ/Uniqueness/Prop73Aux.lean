/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.Defs
public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.LimitPoints.MollifyAux
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Proposition 7.3: the key inequality (task K1)

Auxiliary results for the proof of Proposition 7.3 (`Uniqueness/Prop73.lean`), following
decision D5″ of `docs/stage4-design.md` (Section 1.2 (g)). Let `D = Z¹ - Z²` and
`F(t) = 𝔼 ‖D(t, ·)‖₂²`. For a time `t` at which (7.13) holds for both solutions,
with the test functions `f = ρ_δ(z - ·)`:

* `prop73_isometry`: Itô's isometry, `𝔼[(D(t) ⋆ ρ_δ)(z)²] = 𝔼 ∫_0^t ∫ (g_{t-s} ⋆ f)(y)² D(s,y)² dy ds`;
* `prop73_young`: Young's inequality, `∫ (g_r ⋆ ρ_δ(z - ·))(y)² dz ≤ ‖g_r‖₂² = (4πr)^{-1/2}`;
* `prop73_mollified_le`: hence `𝔼 ‖D(t) ⋆ ρ_δ‖₂² ≤ (2√π)⁻¹ ∫_0^t F(s) (t-s)^{-1/2} ds`;
* `prop73_fatou`: letting `δ → 0` (Lebesgue's differentiation theorem and Fatou's lemma),
  `F(t) ≤ (2√π)⁻¹ ∫_0^t F(s) (t-s)^{-1/2} ds`.

Also `prop73_exists_mollifier` (a mollifier exists: a normalized smooth bump function).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- A mollifier exists (the normalized smooth bump function supported in `[-1, 1]`). -/
theorem prop73_exists_mollifier : ∃ ρ : ℝ → ℝ, IsMollifier ρ := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f.normed volume, ⟨f.contDiff_normed, fun x => f.normed_neg x, f.nonneg_normed,
    fun x hx => ?_, f.integral_normed⟩⟩
  have : x ∉ Function.support (f.normed volume) := by
    rw [f.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact hx.le
  exact Function.notMem_support.1 this

/-- The constant `(2√π)⁻¹` of the article. -/
def prop73Const : ℝ := 1 / (2 * Real.sqrt Real.pi)

theorem prop73Const_nonneg : 0 ≤ prop73Const := by unfold prop73Const; positivity

/-- `‖g_r‖₂² = (4πr)^{-1/2} = (2√π)⁻¹ r^{-1/2}`. -/
private lemma prop73_const_eq {r : ℝ} (hr : 0 < r) :
    1 / Real.sqrt (4 * Real.pi * r) = prop73Const * r ^ (-(1 / 2 : ℝ)) := by
  unfold prop73Const
  rw [Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have := Real.sqrt_pos.2 hr
  have := Real.sqrt_pos.2 Real.pi_pos
  field_simp

variable {ρ : ℝ → ℝ}

/-- The test function `ρ_δ(z - ·)` belongs to `C_c^∞(ℝ)`. -/
theorem prop73_test_smooth (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (z : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => rhoEps ρ δ (z - x)) ∧
      HasCompactSupport (fun x => rhoEps ρ δ (z - x)) := by
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ (⊤ : ℕ∞) (fun x => ρ ((z - x) / δ) / δ)
    exact (hρ.smooth.comp ((contDiff_const.sub contDiff_id).div_const δ)).div_const δ
  · exact (mollif_rhoEps_hasCompactSupport hρ hδ).comp_homeomorph (Homeomorph.subLeft z)

/-- **Young's inequality** for the heat kernel and the mollifier:
`∫ (g_r ⋆ ρ_δ(z - ·))(y)² dz ≤ ‖g_r‖₂² = (4πr)^{-1/2}`. -/
theorem prop73_young (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ∫⁻ z, ENNReal.ofReal (heatConv r (fun x => rhoEps ρ δ (z - x)) y ^ 2) ≤
      ENNReal.ofReal (prop73Const * r ^ (-(1 / 2 : ℝ))) := by
  have hw : Measurable (fun x => heatKernel r (y - x)) := by unfold heatKernel; fun_prop
  obtain ⟨hi, heq⟩ := heatKernel_sq_integral hr
  have hw2 : Integrable (fun x => heatKernel r (y - x) ^ 2) :=
    hi.comp_sub_left (f := fun x => heatKernel r x ^ 2) y
  calc ∫⁻ z, ENNReal.ofReal (heatConv r (fun x => rhoEps ρ δ (z - x)) y ^ 2)
      = ∫⁻ z, ENNReal.ofReal ((∫ x, rhoEps ρ δ (z - x) * heatKernel r (y - x)) ^ 2) := by
        refine lintegral_congr fun z => ?_
        unfold heatConv
        simp_rw [mul_comm (heatKernel r _)]
    _ ≤ ∫⁻ x, ENNReal.ofReal (heatKernel r (y - x) ^ 2) := mollif_lintegral_sq_le hρ hδ hw hw2
    _ = ENNReal.ofReal (∫ x, heatKernel r (y - x) ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hw2 (ae_of_all _ fun _ => sq_nonneg _)).symm
    _ = _ := by
        rw [integral_sub_left_eq_self (fun x => heatKernel r x ^ 2) volume y, heq,
          prop73_const_eq hr]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Itô's isometry** for the difference of two solutions of (7.13), at a time `t` and for one
test function `f`: `𝔼[(∫ (Z¹ - Z²)(t,x) f(x) dx)²] = 𝔼 ∫_0^t ∫ (g_{t-s} ⋆ f)(y)² D(s,y)² dy ds`. -/
theorem prop73_isometry {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}
    (hS : IsWhiteNoise 𝓖 S ν) {t : ℝ} {f : ℝ → ℝ} {Z₁ Z₂ : ℝ → ℝ → Ω → ℝ}
    (hW₁ : IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₁ s y ω else 0)
      (fun ω => (∫ x, Z₁ t x ω * f x) - ∫ x, heatKernel t x * f x))
    (hW₂ : IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₂ s y ω else 0)
      (fun ω => (∫ x, Z₂ t x ω * f x) - ∫ x, heatKernel t x * f x)) :
    ∫⁻ ω, ENNReal.ofReal (((∫ x, Z₁ t x ω * f x) - ∫ x, Z₂ t x ω * f x) ^ 2) ∂ν =
      ∫⁻ p : Ω × ℝ × ℝ, ENNReal.ofReal ((if 0 < p.2.1 ∧ p.2.1 < t then
        heatConv (t - p.2.1) f p.2.2 * (Z₁ p.2.1 p.2.2 p.1 - Z₂ p.2.1 p.2.2 p.1) else 0) ^ 2)
        ∂(ν.prod volume) := by
  have hW := hW₁.sub hW₂
  have e1 : (fun ω => ((∫ x, Z₁ t x ω * f x) - ∫ x, heatKernel t x * f x) -
      ((∫ x, Z₂ t x ω * f x) - ∫ x, heatKernel t x * f x)) =
      fun ω => (∫ x, Z₁ t x ω * f x) - ∫ x, Z₂ t x ω * f x := by
    funext ω; ring
  rw [e1] at hW
  obtain ⟨hh, hX, heq⟩ := IsWalshIntegral.isometry_lib hS hW
  have e2 : (fun p : Ω × ℝ × ℝ => uncurryField (fun s y ω =>
      (if 0 < s ∧ s < t then heatConv (t - s) f y * Z₁ s y ω else 0) -
      (if 0 < s ∧ s < t then heatConv (t - s) f y * Z₂ s y ω else 0)) p) =
      fun p => if 0 < p.2.1 ∧ p.2.1 < t then
        heatConv (t - p.2.1) f p.2.2 * (Z₁ p.2.1 p.2.2 p.1 - Z₂ p.2.1 p.2.2 p.1) else 0 := by
    funext p
    simp only [uncurryField]
    split_ifs <;> ring
  have hh' := hh
  rw [show uncurryField (fun s y ω =>
      (if 0 < s ∧ s < t then heatConv (t - s) f y * Z₁ s y ω else 0) -
      (if 0 < s ∧ s < t then heatConv (t - s) f y * Z₂ s y ω else 0)) = _ from e2] at hh' heq
  rw [← ofReal_integral_eq_lintegral_ofReal hX.integrable_sq (ae_of_all _ fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hh'.integrable_sq (ae_of_all _ fun _ => sq_nonneg _),
    heq]

/-- Measurability of `(ω, z) ↦ ∫ Z(t,x) ρ_δ(z - x) dx`. -/
theorem prop73_measurable_conv (hρ : IsMollifier ρ) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : Measurable (uncurryField Z)) (δ t : ℝ) :
    Measurable (fun q : Ω × ℝ => ∫ x, Z t x q.1 * rhoEps ρ δ (q.2 - x)) := by
  have hm : Measurable (fun r : (Ω × ℝ) × ℝ => Z t r.2 r.1.1 * rhoEps ρ δ (r.1.2 - r.2)) := by
    refine Measurable.mul ?_ ((mollif_rhoEps_continuous hρ δ).measurable.comp (by fun_prop))
    exact hZ.comp (f := fun r : (Ω × ℝ) × ℝ => (r.1.1, t, r.2)) (by fun_prop)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Measurability of `(z, s, y) ↦ (g_{t-s} ⋆ ρ_δ(z - ·))(y)`. -/
theorem prop73_measurable_heatConv (hρ : IsMollifier ρ) (δ t : ℝ) :
    Measurable (fun q : ℝ × ℝ × ℝ => heatConv (t - q.2.1) (fun x => rhoEps ρ δ (q.1 - x)) q.2.2) := by
  have hm : Measurable (fun r : (ℝ × ℝ × ℝ) × ℝ =>
      heatKernel (t - r.1.2.1) (r.1.2.2 - r.2) * rhoEps ρ δ (r.1.1 - r.2)) := by
    refine Measurable.mul ?_ ((mollif_rhoEps_continuous hρ δ).measurable.comp (by fun_prop))
    unfold heatKernel; fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Measurability of `(ω, s, y) ↦ D(s,y)²` in `[0,∞]`. -/
theorem prop73_measurable_sq {D : ℝ → ℝ → Ω → ℝ} (hD : Measurable (uncurryField D)) :
    Measurable (fun p : Ω × ℝ × ℝ => ENNReal.ofReal (D p.2.1 p.2.2 p.1 ^ 2)) :=
  (hD.pow_const 2).ennreal_ofReal

/-- Measurability of `(t, ω) ↦ ∫ D(t,x)² dx` in `[0,∞]`. -/
theorem prop73_measurable_inner {D : ℝ → ℝ → Ω → ℝ} (hD : Measurable (uncurryField D)) :
    Measurable (fun q : ℝ × Ω => ∫⁻ x, ENNReal.ofReal (D q.1 x q.2 ^ 2)) := by
  have hm : Measurable (fun r : (ℝ × Ω) × ℝ => ENNReal.ofReal (D r.1.1 r.2 r.1.2 ^ 2)) :=
    (prop73_measurable_sq hD).comp (f := fun r : (ℝ × Ω) × ℝ => (r.1.2, r.1.1, r.2))
      (by fun_prop)
  exact hm.lintegral_prod_right'

/-- Measurability of `t ↦ 𝔼 ∫ D(t,x)² dx` in `[0,∞]`. -/
theorem prop73_measurable_F {D : ℝ → ℝ → Ω → ℝ} (hD : Measurable (uncurryField D))
    (ν : Measure Ω) [SFinite ν] :
    Measurable (fun t => ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (D t x ω ^ 2)) ∂ν) :=
  (prop73_measurable_inner hD).lintegral_prod_right'

/-- Exchange of `𝔼` and `∫ dt`: `∫ 𝔼 ∫ D(t,x)² dx dt = 𝔼 ∫ ∫ D(t,x)² dx dt`. -/
theorem prop73_lintegral_swap {D : ℝ → ℝ → Ω → ℝ} (hD : Measurable (uncurryField D))
    (ν : Measure Ω) [SFinite ν] (μ : Measure ℝ) [SFinite μ] :
    ∫⁻ t, (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (D t x ω ^ 2)) ∂ν) ∂μ =
      ∫⁻ ω, (∫⁻ t, (∫⁻ x, ENNReal.ofReal (D t x ω ^ 2)) ∂μ) ∂ν :=
  lintegral_lintegral_swap (prop73_measurable_inner hD).aemeasurable

/-- The weight `𝟙_{0<s<t} (2√π)⁻¹ (t-s)^{-1/2}`. -/
def prop73Weight (t s : ℝ) : ℝ≥0∞ :=
  (Set.Ioo 0 t).indicator (fun s => ENNReal.ofReal (prop73Const * (t - s) ^ (-(1 / 2 : ℝ)))) s

theorem prop73_measurable_weight (t : ℝ) : Measurable (prop73Weight t) :=
  (Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioo

/-- `𝔼 ∫_0^t ∫ (2√π)⁻¹ (t-s)^{-1/2} D(s,y)² dy ds = (2√π)⁻¹ ∫_0^t F(s) (t-s)^{-1/2} ds`, with
`F(s) = 𝔼 ∫ D(s,x)² dx` (Tonelli). -/
theorem prop73_lintegral_weight {D : ℝ → ℝ → Ω → ℝ} (hD : Measurable (uncurryField D))
    (ν : Measure Ω) [SFinite ν] (t : ℝ) :
    ∫⁻ p : Ω × ℝ × ℝ, prop73Weight t p.2.1 * ENNReal.ofReal (D p.2.1 p.2.2 p.1 ^ 2)
        ∂(ν.prod volume) =
      ENNReal.ofReal prop73Const * ∫⁻ s in Set.Ioo 0 t,
        (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (D s x ω ^ 2)) ∂ν) * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) := by
  have hk := prop73_measurable_weight t
  have hd := prop73_measurable_sq hD
  have hm : Measurable (fun p : Ω × ℝ × ℝ =>
      prop73Weight t p.2.1 * ENNReal.ofReal (D p.2.1 p.2.2 p.1 ^ 2)) :=
    (hk.comp (by fun_prop : Measurable fun p : Ω × ℝ × ℝ => p.2.1)).mul hd
  rw [lintegral_prod _ hm.aemeasurable]
  have hy : ∀ ω s, Measurable (fun y => ENNReal.ofReal (D s y ω ^ 2)) := fun ω s =>
    hd.comp (f := fun y => (ω, s, y)) (by fun_prop)
  have h1 : ∀ ω, ∫⁻ q : ℝ × ℝ, prop73Weight t q.1 * ENNReal.ofReal (D q.1 q.2 ω ^ 2) =
      ∫⁻ s, prop73Weight t s * ∫⁻ y, ENNReal.ofReal (D s y ω ^ 2) := by
    intro ω
    have hm' : Measurable (fun q : ℝ × ℝ => prop73Weight t q.1 * ENNReal.ofReal (D q.1 q.2 ω ^ 2)) :=
      (hk.comp measurable_fst).mul (hd.comp (f := fun q : ℝ × ℝ => (ω, q.1, q.2)) (by fun_prop))
    rw [Measure.volume_eq_prod, lintegral_prod _ hm'.aemeasurable]
    exact lintegral_congr fun s => by dsimp only; exact lintegral_const_mul _ (hy ω s)
  have hJ : Measurable (fun q : Ω × ℝ => prop73Weight t q.2 * ∫⁻ y, ENNReal.ofReal (D q.2 y q.1 ^ 2)) :=
    (hk.comp measurable_snd).mul ((prop73_measurable_inner hD).comp (f := fun q : Ω × ℝ => (q.2, q.1))
      (by fun_prop))
  rw [lintegral_congr fun ω => h1 ω, lintegral_lintegral_swap hJ.aemeasurable]
  have h2 : ∀ s, ∫⁻ ω, (prop73Weight t s * ∫⁻ y, ENNReal.ofReal (D s y ω ^ 2)) ∂ν =
      (Set.Ioo 0 t).indicator (fun s => ENNReal.ofReal (prop73Const * (t - s) ^ (-(1 / 2 : ℝ))) *
        ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (D s x ω ^ 2)) ∂ν) s := by
    intro s
    have hs : Measurable (fun ω => ∫⁻ y, ENNReal.ofReal (D s y ω ^ 2)) :=
      (prop73_measurable_inner hD).comp (f := fun ω => (s, ω)) (by fun_prop)
    rw [lintegral_const_mul _ hs, Set.indicator_mul_left]
    rfl
  rw [lintegral_congr h2, lintegral_indicator measurableSet_Ioo, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine lintegral_congr fun s => ?_
  rw [ENNReal.ofReal_mul prop73Const_nonneg]
  ring

/-- Pointwise bound after integrating in `z` (Young's inequality `prop73_young`):
`∫ 𝟙_{0<s<t} (g_{t-s} ⋆ ρ_δ(z - ·))(y)² D² dz ≤ 𝟙_{0<s<t} (2√π)⁻¹ (t-s)^{-1/2} D²`. -/
theorem prop73_pointwise_bound (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (D : ℝ → ℝ → Ω → ℝ)
    (t : ℝ) (p : Ω × ℝ × ℝ) :
    ∫⁻ z, ENNReal.ofReal ((if 0 < p.2.1 ∧ p.2.1 < t then
        heatConv (t - p.2.1) (fun x => rhoEps ρ δ (z - x)) p.2.2 * D p.2.1 p.2.2 p.1 else 0) ^ 2)
      ≤ prop73Weight t p.2.1 * ENNReal.ofReal (D p.2.1 p.2.2 p.1 ^ 2) := by
  by_cases h : 0 < p.2.1 ∧ p.2.1 < t
  · simp only [h.1, h.2, and_self, ↓reduceIte]
    rw [prop73Weight, Set.indicator_of_mem (show p.2.1 ∈ Set.Ioo 0 t from h)]
    calc ∫⁻ z, ENNReal.ofReal ((heatConv (t - p.2.1) (fun x => rhoEps ρ δ (z - x)) p.2.2 *
          D p.2.1 p.2.2 p.1) ^ 2)
        = ∫⁻ z, ENNReal.ofReal (heatConv (t - p.2.1) (fun x => rhoEps ρ δ (z - x)) p.2.2 ^ 2) *
            ENNReal.ofReal (D p.2.1 p.2.2 p.1 ^ 2) :=
          lintegral_congr fun z => by rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
      _ = (∫⁻ z, ENNReal.ofReal (heatConv (t - p.2.1) (fun x => rhoEps ρ δ (z - x)) p.2.2 ^ 2)) *
            ENNReal.ofReal (D p.2.1 p.2.2 p.1 ^ 2) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact prop73_young hρ hδ (sub_pos.2 h.2) _
  · simp only [h, ↓reduceIte]
    simp

/-- **Key estimate** (D5″): if (7.13) holds at time `t` for `Z¹` and `Z²` and all test functions,
then for every `δ > 0`, `𝔼 ‖D(t) ⋆ ρ_δ‖₂² ≤ (2√π)⁻¹ ∫_0^t F(s) (t-s)^{-1/2} ds`, where
`D = Z¹ - Z²` and `F(s) = 𝔼 ‖D(s)‖₂²` (Itô's isometry, Young's inequality, Tonelli). -/
theorem prop73_mollified_le {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}
    (hS : IsWhiteNoise 𝓖 S ν) (hρ : IsMollifier ρ) {Z₁ Z₂ : ℝ → ℝ → Ω → ℝ}
    (hZ₁ : Measurable (uncurryField Z₁)) (hZ₂ : Measurable (uncurryField Z₂)) {t : ℝ}
    (hw₁ : ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      IsWalshIntegral 𝓖 S ν
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₁ s y ω else 0)
        (fun ω => (∫ x, Z₁ t x ω * f x) - ∫ x, heatKernel t x * f x))
    (hw₂ : ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      IsWalshIntegral 𝓖 S ν
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₂ s y ω else 0)
        (fun ω => (∫ x, Z₂ t x ω * f x) - ∫ x, heatKernel t x * f x))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (((∫ x, Z₁ t x ω * rhoEps ρ δ (z - x)) -
        ∫ x, Z₂ t x ω * rhoEps ρ δ (z - x)) ^ 2)) ∂ν ≤
      ENNReal.ofReal prop73Const * ∫⁻ s in Set.Ioo 0 t,
        (∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((Z₁ s x ω - Z₂ s x ω) ^ 2)) ∂ν) *
          ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hD : Measurable (uncurryField fun s y ω => Z₁ s y ω - Z₂ s y ω) := hZ₁.sub hZ₂
  rw [lintegral_lintegral_swap ((((prop73_measurable_conv hρ hZ₁ δ t).sub
    (prop73_measurable_conv hρ hZ₂ δ t)).pow_const 2).ennreal_ofReal.aemeasurable)]
  have hiso : ∀ z, ∫⁻ ω, ENNReal.ofReal (((∫ x, Z₁ t x ω * rhoEps ρ δ (z - x)) -
      ∫ x, Z₂ t x ω * rhoEps ρ δ (z - x)) ^ 2) ∂ν =
      ∫⁻ p : Ω × ℝ × ℝ, ENNReal.ofReal ((if 0 < p.2.1 ∧ p.2.1 < t then
        heatConv (t - p.2.1) (fun x => rhoEps ρ δ (z - x)) p.2.2 *
          (Z₁ p.2.1 p.2.2 p.1 - Z₂ p.2.1 p.2.2 p.1) else 0) ^ 2) ∂(ν.prod volume) := fun z => by
    obtain ⟨hf1, hf2⟩ := prop73_test_smooth hρ hδ z
    exact prop73_isometry hS (hw₁ _ hf1 hf2) (hw₂ _ hf1 hf2)
  have hΦ := prop73_measurable_heatConv hρ δ t
  have hG : Measurable (fun r : ℝ × (Ω × ℝ × ℝ) => ENNReal.ofReal ((if 0 < r.2.2.1 ∧ r.2.2.1 < t then
      heatConv (t - r.2.2.1) (fun x => rhoEps ρ δ (r.1 - x)) r.2.2.2 *
        (Z₁ r.2.2.1 r.2.2.2 r.2.1 - Z₂ r.2.2.1 r.2.2.2 r.2.1) else 0) ^ 2)) := by
    refine (Measurable.pow_const (Measurable.ite ?_ ((hΦ.comp (f := fun r : ℝ × (Ω × ℝ × ℝ) =>
      (r.1, r.2.2.1, r.2.2.2)) (by fun_prop)).mul (hD.comp measurable_snd)) measurable_const) 2)
      |>.ennreal_ofReal
    have h1 : Measurable fun r : ℝ × (Ω × ℝ × ℝ) => r.2.2.1 := by fun_prop
    exact (measurableSet_lt measurable_const h1).inter (measurableSet_lt h1 measurable_const)
  rw [lintegral_congr hiso, lintegral_lintegral_swap hG.aemeasurable]
  calc _ ≤ ∫⁻ p : Ω × ℝ × ℝ, prop73Weight t p.2.1 *
        ENNReal.ofReal ((Z₁ p.2.1 p.2.2 p.1 - Z₂ p.2.1 p.2.2 p.1) ^ 2) ∂(ν.prod volume) :=
        lintegral_mono fun p => prop73_pointwise_bound hρ hδ (fun s y ω => Z₁ s y ω - Z₂ s y ω) t p
    _ = _ := prop73_lintegral_weight hD ν t

/-- `Z(t, ·, ω) ∈ L²(ℝ)` when `∫ Z(t,x,ω)² dx < ∞`. -/
theorem prop73_memLp_of_lintegral {Z : ℝ → ℝ → Ω → ℝ} (hZ : Measurable (uncurryField Z)) {t : ℝ}
    {ω : Ω} (h : ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2) < ⊤) :
    Measurable (fun x => Z t x ω) ∧ MemLp (fun x => Z t x ω) 2 volume := by
  have hm : Measurable (fun x => Z t x ω) := hZ.comp (f := fun x => (ω, t, x)) (by fun_prop)
  refine ⟨hm, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2 h

/-- **Fatou step** (D5″): if `𝔼 ‖D(t) ⋆ ρ_δ‖₂² ≤ R` for every `δ > 0` and `Z¹(t), Z²(t) ∈ L²`
almost surely, then `𝔼 ‖D(t)‖₂² ≤ R` (Lebesgue's differentiation theorem for the mollifiers
`ρ_δ`, `δ = 1/(n+1) → 0`, and Fatou's lemma, in `x` and then in `ω`). -/
theorem prop73_fatou (hρ : IsMollifier ρ) {ν : Measure Ω} [SFinite ν] {Z₁ Z₂ : ℝ → ℝ → Ω → ℝ}
    (hZ₁ : Measurable (uncurryField Z₁)) (hZ₂ : Measurable (uncurryField Z₂)) {t : ℝ}
    (hfin₁ : ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (Z₁ t x ω ^ 2)) ∂ν < ⊤)
    (hfin₂ : ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (Z₂ t x ω ^ 2)) ∂ν < ⊤) {R : ℝ≥0∞}
    (hR : ∀ δ : ℝ, 0 < δ → ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (((∫ x, Z₁ t x ω * rhoEps ρ δ (z - x)) -
        ∫ x, Z₂ t x ω * rhoEps ρ δ (z - x)) ^ 2)) ∂ν ≤ R) :
    ∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2)) ∂ν ≤ R := by
  set δs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδs
  have hδpos : ∀ n, 0 < δs n := fun n => by positivity
  have hδlim : Tendsto δs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hδpos⟩
  have hX : ∀ n, Measurable (fun q : Ω × ℝ => ENNReal.ofReal (((∫ x, Z₁ t x q.1 *
      rhoEps ρ (δs n) (q.2 - x)) - ∫ x, Z₂ t x q.1 * rhoEps ρ (δs n) (q.2 - x)) ^ 2)) := fun n =>
    (((prop73_measurable_conv hρ hZ₁ (δs n) t).sub
      (prop73_measurable_conv hρ hZ₂ (δs n) t)).pow_const 2).ennreal_ofReal
  have hinner : ∀ {Z : ℝ → ℝ → Ω → ℝ}, Measurable (uncurryField Z) →
      Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) := fun hZ =>
    (prop73_measurable_inner hZ).comp (f := fun ω => (t, ω)) (by fun_prop)
  have hgood₁ := ae_lt_top' (hinner hZ₁).aemeasurable hfin₁.ne
  have hgood₂ := ae_lt_top' (hinner hZ₂).aemeasurable hfin₂.ne
  have hpt : ∀ᵐ ω ∂ν, ∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2) ≤
      liminf (fun n => ∫⁻ z, ENNReal.ofReal (((∫ x, Z₁ t x ω * rhoEps ρ (δs n) (z - x)) -
        ∫ x, Z₂ t x ω * rhoEps ρ (δs n) (z - x)) ^ 2)) atTop := by
    filter_upwards [hgood₁, hgood₂] with ω h1 h2
    obtain ⟨hm₁, hL₁⟩ := prop73_memLp_of_lintegral hZ₁ h1
    obtain ⟨hm₂, hL₂⟩ := prop73_memLp_of_lintegral hZ₂ h2
    have hw : MemLp (fun x => Z₁ t x ω - Z₂ t x ω) 2 volume := hL₁.sub hL₂
    have hconv : ∀ n z, (∫ x, Z₁ t x ω * rhoEps ρ (δs n) (z - x)) -
        ∫ x, Z₂ t x ω * rhoEps ρ (δs n) (z - x) =
        ∫ x, rhoEps ρ (δs n) (z - x) * (Z₁ t x ω - Z₂ t x ω) := by
      intro n z
      have i1 := mollif_integrable_mul hρ (hδpos n) hm₁.aestronglyMeasurable hL₁.integrable_sq z
      have i2 := mollif_integrable_mul hρ (hδpos n) hm₂.aestronglyMeasurable hL₂.integrable_sq z
      simp_rw [mul_comm (Z₁ t _ ω), mul_comm (Z₂ t _ ω), mul_sub]
      exact (integral_sub i1 i2).symm
    have hlim : ∀ᵐ z, Tendsto (fun n => ENNReal.ofReal (((∫ x, Z₁ t x ω *
        rhoEps ρ (δs n) (z - x)) - ∫ x, Z₂ t x ω * rhoEps ρ (δs n) (z - x)) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((Z₁ t z ω - Z₂ t z ω) ^ 2))) := by
      filter_upwards [mollif_ae_tendsto hρ (hw.locallyIntegrable (by norm_num))] with z hz
      simp_rw [hconv]
      exact (ENNReal.continuous_ofReal.tendsto _).comp ((hz.comp hδlim).pow 2)
    calc ∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2)
        = ∫⁻ z, liminf (fun n => ENNReal.ofReal (((∫ x, Z₁ t x ω * rhoEps ρ (δs n) (z - x)) -
            ∫ x, Z₂ t x ω * rhoEps ρ (δs n) (z - x)) ^ 2)) atTop :=
          lintegral_congr_ae (hlim.mono fun z hz => hz.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' fun n =>
          ((hX n).comp (f := fun z => (ω, z)) (by fun_prop)).aemeasurable
  calc _ ≤ ∫⁻ ω, liminf (fun n => ∫⁻ z, ENNReal.ofReal (((∫ x, Z₁ t x ω *
        rhoEps ρ (δs n) (z - x)) - ∫ x, Z₂ t x ω * rhoEps ρ (δs n) (z - x)) ^ 2)) atTop ∂ν :=
        lintegral_mono_ae hpt
    _ ≤ liminf (fun n => ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (((∫ x, Z₁ t x ω *
        rhoEps ρ (δs n) (z - x)) - ∫ x, Z₂ t x ω * rhoEps ρ (δs n) (z - x)) ^ 2)) ∂ν) atTop :=
        lintegral_liminf_le' fun n => (hX n).lintegral_prod_right'.aemeasurable
    _ ≤ R := liminf_le_of_frequently_le' (Frequently.of_forall fun n => hR _ (hδpos n))

end QSSEPtoKPZ
