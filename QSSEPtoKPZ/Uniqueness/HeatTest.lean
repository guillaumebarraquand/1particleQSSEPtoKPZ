/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import QSSEPtoKPZ.Uniqueness.HeatTestAux
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import QSSEPtoKPZ.TiltedField.Defs

/-!
# The test function of Step 4 of the proof of Proposition 7.2 (task G10b)

INTERFACE FILE (task I0″ of Stage 4): the definitions are complete; the statements below are
interfaces, proved by task G10b. See `docs/stage4-design.md`, Sections 1.3 and 3.4, and
`docs/stage4-interfaces.md`.

For `f ∈ C_c^∞(ℝ)` and `t > 0`: `φ_s = g_{t-s} ⋆ f` for `s < t` and `φ_s = f - (s-t)/2 f''` for
`s ≥ t`, with time derivative `-½ g_{t-s} ⋆ f''` for `s < t` and `-½ f''` for `s ≥ t`. It belongs
to `C_b^{1,3}([0,T] × ℝ)` (`IsC13`), solves `∂ₛφ + ½ ∂ₓ²φ = 0` on `[0,t] × ℝ`, `φ_t = f`, and
`φ_0(0) = ∫ g_t f`.

Proofs (task G10b), with `G_h(r, y) = ∫ g_1(z) h(y - √r z) dz` (`heatTestGauss`, file
`HeatTestAux.lean`), which is `g_r ⋆ h` for `r > 0` and `h` for `r ≤ 0`:
`φ_s = G_f(t - s, ·) - (s - t)⁺/2 f''` and `∂ₛφ_s = -½ G_{f''}(t - s, ·)` for **all** `s`, hence
`∂ₓᵏ φ_s = G_{f^{(k)}}(t - s, ·) - (s - t)⁺/2 f^{(k+2)}`; continuity and bounds follow from those
of `G`. The time derivative is computed for `s ≠ t` (from `∂_r (g_r ⋆ f) = ½ g_r ⋆ f''` for
`s < t`), and at `s = t` by continuity of `∂ₛφ` (`hasDerivAt_of_hasDerivAt_of_ne'`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The test function `φ_s(y)` of Step 4. -/
def heatTest (t : ℝ) (f : ℝ → ℝ) (s y : ℝ) : ℝ :=
  if s < t then heatConv (t - s) f y else f y - (s - t) / 2 * iteratedDeriv 2 f y

/-- Its time derivative `∂ₛφ_s(y)`. -/
def heatTestDeriv (t : ℝ) (f : ℝ → ℝ) (s y : ℝ) : ℝ :=
  if s < t then -(heatConv (t - s) (iteratedDeriv 2 f) y / 2) else -(iteratedDeriv 2 f y / 2)

variable {f : ℝ → ℝ} {t : ℝ}

/-- `φ_s(y) = G_f(t - s, y) - (s - t)⁺/2 f''(y)` for all `s`. -/
private lemma heatTest_eq_gauss (s y : ℝ) :
    heatTest t f s y = heatTestGauss f (t - s) y - max (s - t) 0 / 2 * iteratedDeriv 2 f y := by
  unfold heatTest
  split_ifs with h
  · rw [heatTestGauss_eq_heatConv _ (sub_pos.2 h), max_eq_right (by linarith)]; ring
  · rw [heatTestGauss_of_nonpos _ (by linarith), max_eq_left (by linarith)]

/-- `∂ₛφ_s(y) = -½ G_{f''}(t - s, y)` for all `s`. -/
private lemma heatTestDeriv_eq_gauss (s y : ℝ) :
    heatTestDeriv t f s y = -(heatTestGauss (iteratedDeriv 2 f) (t - s) y / 2) := by
  unfold heatTestDeriv
  split_ifs with h
  · rw [heatTestGauss_eq_heatConv _ (sub_pos.2 h)]
  · rw [heatTestGauss_of_nonpos _ (by linarith)]

/-- The space derivative of `G_{f^{(k)}}(t - s, ·) - (s - t)⁺/2 f^{(k+2)}`. -/
private lemma heatTest_hasDerivAt_space (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (s : ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun y => heatTestGauss (iteratedDeriv k f) (t - s) y -
        max (s - t) 0 / 2 * iteratedDeriv (k + 2) f y)
      (heatTestGauss (iteratedDeriv (k + 1) f) (t - s) y -
        max (s - t) 0 / 2 * iteratedDeriv (k + 1 + 2) f y) y := by
  obtain ⟨-, -, hd, M, hM⟩ := heatTest_iteratedDeriv_props hf hfc k
  obtain ⟨hc', -, -, M', hM'⟩ := heatTest_iteratedDeriv_props hf hfc (k + 1)
  obtain ⟨-, -, hd2, -⟩ := heatTest_iteratedDeriv_props hf hfc (k + 2)
  exact (hasDerivAt_heatTestGauss hd hc' hM hM' (t - s) y).sub ((hd2 y).const_mul _)

/-- `∂ₓᵏ φ_s = G_{f^{(k)}}(t - s, ·) - (s - t)⁺/2 f^{(k+2)}`. -/
private lemma iteratedDeriv_heatTest (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (s : ℝ) (k : ℕ) :
    iteratedDeriv k (heatTest t f s) = fun y => heatTestGauss (iteratedDeriv k f) (t - s) y -
      max (s - t) 0 / 2 * iteratedDeriv (k + 2) f y := by
  induction k with
  | zero => funext y; simp only [iteratedDeriv_zero]; exact heatTest_eq_gauss s y
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    exact (heatTest_hasDerivAt_space hf hfc s k y).deriv

/-- Joint continuity of `(s, y) ↦ G_{f^{(k)}}(t - s, y) - (s - t)⁺/2 f^{(k+2)}(y)`. -/
private lemma heatTest_continuous_gauss (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (k : ℕ) : Continuous fun p : ℝ × ℝ => heatTestGauss (iteratedDeriv k f) (t - p.1) p.2 -
      max (p.1 - t) 0 / 2 * iteratedDeriv (k + 2) f p.2 := by
  obtain ⟨hc, -, -, M, hM⟩ := heatTest_iteratedDeriv_props hf hfc k
  obtain ⟨hc2, -⟩ := heatTest_iteratedDeriv_props hf hfc (k + 2)
  have := (continuous_heatTestGauss hc hM).comp
    (show Continuous fun p : ℝ × ℝ => (t - p.1, p.2) by fun_prop)
  exact this.sub ((by fun_prop : Continuous fun p : ℝ × ℝ => max (p.1 - t) 0 / 2).mul
    (hc2.comp continuous_snd))

/-- Joint continuity of `(s, y) ↦ ∂ₛφ_s(y)`. -/
private lemma heatTest_continuous_deriv (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Continuous (Function.uncurry (heatTestDeriv t f)) := by
  obtain ⟨hc, -, -, M, hM⟩ := heatTest_iteratedDeriv_props hf hfc 2
  have : Function.uncurry (heatTestDeriv t f) =
      fun p : ℝ × ℝ => -(heatTestGauss (iteratedDeriv 2 f) (t - p.1) p.2 / 2) := by
    funext p; exact heatTestDeriv_eq_gauss p.1 p.2
  rw [this]
  exact (((continuous_heatTestGauss hc hM).comp
    (show Continuous fun p : ℝ × ℝ => (t - p.1, p.2) by fun_prop)).div_const 2).neg

/-- The time derivative: `∂ₛφ_s(y) = heatTestDeriv t f s y` for every `s ∈ ℝ`. -/
private lemma heatTest_hasDerivAt_time (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (s y : ℝ) : HasDerivAt (fun s => heatTest t f s y) (heatTestDeriv t f s y) s := by
  refine hasDerivAt_of_hasDerivAt_of_ne' (f := fun s => heatTest t f s y)
    (g := fun s => heatTestDeriv t f s y) (x := t) (fun s hs => ?_) ?_ ?_ s
  · rcases lt_or_gt_of_ne hs with h | h
    · have key := (heatTest_hasDerivAt_heatConv_time hf hfc (sub_pos.2 h) y).comp s
        ((hasDerivAt_id' s).const_sub t)
      have hev : (fun s => heatTest t f s y) =ᶠ[𝓝 s] fun s => heatConv (t - s) f y :=
        (eventually_lt_nhds h).mono fun s' hs' => by simp [heatTest, hs']
      convert key.congr_of_eventuallyEq hev using 1
      simp [heatTestDeriv, h]
    · have key := ((((hasDerivAt_id' s).sub_const t).div_const 2).mul_const
        (iteratedDeriv 2 f y)).const_sub (f y)
      have hev : (fun s => heatTest t f s y) =ᶠ[𝓝 s]
          fun s => f y - (s - t) / 2 * iteratedDeriv 2 f y :=
        (eventually_gt_nhds h).mono fun s' hs' => by simp [heatTest, not_lt.2 hs'.le]
      convert key.congr_of_eventuallyEq hev using 1
      simp only [heatTestDeriv, not_lt.2 h.le, ↓reduceIte]
      ring
  · have : (fun s => heatTest t f s y) = fun s => heatTestGauss f (t - s) y -
        max (s - t) 0 / 2 * iteratedDeriv 2 f y := funext fun s => heatTest_eq_gauss s y
    rw [this]
    have hc := heatTest_continuous_gauss (t := t) hf hfc 0
    simp only [iteratedDeriv_zero, zero_add] at hc
    exact (hc.comp (show Continuous fun s : ℝ => (s, y) by fun_prop)).continuousAt
  · exact ((heatTest_continuous_deriv hf hfc).comp
      (show Continuous fun s : ℝ => (s, y) by fun_prop)).continuousAt

/-- `|G - m d| ≤ M_G + A M_d` for `0 ≤ m ≤ A`, `|G| ≤ M_G`, `|d| ≤ M_d`. -/
private lemma heatTest_abs_sub_le {G m d MG Md A : ℝ} (hG : |G| ≤ MG) (hd : |d| ≤ Md)
    (hm0 : 0 ≤ m) (hmA : m ≤ A) : |G - m * d| ≤ MG + A * Md := by
  calc |G - m * d| ≤ |G| + |m * d| := abs_sub _ _
    _ = |G| + m * |d| := by rw [abs_mul, abs_of_nonneg hm0]
    _ ≤ MG + A * Md := add_le_add hG (mul_le_mul hmA hd (abs_nonneg _) (hm0.trans hmA))

/-- `φ ∈ C_b^{1,3}([0,T] × ℝ)` with time derivative `heatTestDeriv`. -/
theorem isC13_heatTest (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (ht : 0 < t)
    (T : ℝ) : ∃ C, IsC13 T (heatTest t f) (heatTestDeriv t f) C := by
  have hb : ∀ k, ∃ M, ∀ x, |iteratedDeriv k f x| ≤ M := fun k =>
    (heatTest_iteratedDeriv_props hf hfc k).2.2.2
  choose M hM using hb
  have hM0 : ∀ k, 0 ≤ M k := fun k => (abs_nonneg _).trans (hM k 0)
  set A := |T| + |t|
  have hm : ∀ s ∈ Set.Icc 0 T, 0 ≤ max (s - t) 0 / 2 ∧ max (s - t) 0 / 2 ≤ A := by
    intro s hs
    refine ⟨by positivity, ?_⟩
    have : max (s - t) 0 ≤ A := max_le (by linarith [hs.2, le_abs_self T, neg_abs_le t])
      (by positivity)
    linarith [le_max_right (s - t) 0]
  refine ⟨_, ⟨fun s _ => ?_, fun x s _ => (heatTest_hasDerivAt_time hf hfc s x).hasDerivWithinAt,
    ⟨(heatTest_continuous_deriv hf hfc).continuousOn, fun k _ => ?_⟩,
    ⟨![M 0 + A * M 2, M 2, M 1 + A * M 3, M 2 + A * M 4, M 3 + A * M 5], le_rfl,
      fun s hs x => ?_⟩⟩⟩
  · refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
    rw [iteratedDeriv_heatTest hf hfc]
    exact fun y => (heatTest_hasDerivAt_space hf hfc s m y).differentiableAt
  · have : (fun p : ℝ × ℝ => iteratedDeriv k (heatTest t f p.1) p.2) =
        fun p : ℝ × ℝ => heatTestGauss (iteratedDeriv k f) (t - p.1) p.2 -
          max (p.1 - t) 0 / 2 * iteratedDeriv (k + 2) f p.2 := by
      funext p; rw [iteratedDeriv_heatTest hf hfc]
    rw [this]
    exact (heatTest_continuous_gauss hf hfc k).continuousOn
  · obtain ⟨hm0, hmA⟩ := hm s hs
    have hG : ∀ k, |heatTestGauss (iteratedDeriv k f) (t - s) x| ≤ M k := fun k =>
      abs_heatTestGauss_le (hM k) _ _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, iteratedDeriv_heatTest hf hfc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [heatTest_eq_gauss]
      have := hG 0; rw [iteratedDeriv_zero] at this
      exact heatTest_abs_sub_le this (hM 2 x) hm0 hmA
    · rw [heatTestDeriv_eq_gauss, abs_neg, abs_div, abs_two]
      linarith [hG 2, hM0 2]
    · exact heatTest_abs_sub_le (hG 1) (hM 3 x) hm0 hmA
    · exact heatTest_abs_sub_le (hG 2) (hM 4 x) hm0 hmA
    · exact heatTest_abs_sub_le (hG 3) (hM 5 x) hm0 hmA

set_option linter.unusedVariables false in
/-- The backward heat equation `∂ₛφ + ½ ∂ₓ²φ = 0` on `[0,t] × ℝ`. -/
theorem heatTest_pde (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (ht : 0 < t)
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) (y : ℝ) :
    heatTestDeriv t f s y + iteratedDeriv 2 (heatTest t f s) y / 2 = 0 := by
  rw [heatTestDeriv_eq_gauss, iteratedDeriv_heatTest hf hfc, max_eq_right (by linarith [hs.2])]
  ring

/-- `φ_t = f`. -/
theorem heatTest_self (t : ℝ) (f : ℝ → ℝ) : heatTest t f t = f := by
  funext y
  simp [heatTest]

/-- `φ_0(0) = ∫ g_t(x) f(x) dx`. -/
theorem heatTest_zero_zero (ht : 0 < t) : heatTest t f 0 0 = ∫ x, heatKernel t x * f x := by
  simp only [heatTest, ht, ↓reduceIte, heatConv, sub_zero, zero_sub, heatKernel, even_two.neg_pow]

end QSSEPtoKPZ
