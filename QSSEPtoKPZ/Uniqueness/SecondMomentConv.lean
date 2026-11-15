/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.HeatKernel

/-!
# Space-time convolution of nonnegative functions on `(0,t) × ℝ` (task K2)

For `A, B : ℝ → ℝ → [0,∞]`,
`(A ⊛ B)(t,x) = ∫∫_{(0,t) × ℝ} A(t-s, x-y) B(s,y) ds dy` (`secondMomConv`), a lower integral.
We prove its associativity for measurable `A, B, C` (Tonelli and translation invariance of the
Lebesgue measure), and that the iterated kernels `K^{⋆(k+1)}` (`heatSqIter k`, of
`HeatKernel.lean`) satisfy `K ⊛ K^{⋆(k+1)} = K^{⋆(k+2)}` in this form (`secondMomConv_K_iter`).
This is the bookkeeping of the iteration `F = K + K ⋆ F` of Section 1.2 (h) of
`docs/stage4-design.md`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- Space-time convolution on `(0,t) × ℝ` of nonnegative extended functions:
`(A ⊛ B)(t,x) = ∫∫_{(0,t) × ℝ} A(t-s, x-y) B(s,y) ds dy`. -/
def secondMomConv (A B : ℝ → ℝ → ℝ≥0∞) (t x : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Set.Ioo 0 t ×ˢ Set.univ, A (t - p.1) (x - p.2) * B p.1 p.2

/-- The iterated kernel `K^{⋆(k+1)}(t,x)` (`heatSqIter k t x`) as an extended nonnegative
number. -/
def secondMomK (k : ℕ) (t x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (heatSqIter k t x)

/-- The heat kernel vanishes for `t ≤ 0` (by the conventions `√r = 0` for `r ≤ 0` and
`a / 0 = 0`). -/
theorem secondMom_heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) : heatKernel t x = 0 := by
  rw [heatKernel, Real.sqrt_eq_zero_of_nonpos (by nlinarith [Real.pi_pos]), div_zero]

/-- `K^{⋆1}(t,x) = g_t(x)²` for every `t` (both sides vanish for `t ≤ 0`). -/
theorem secondMom_heatSqIter_zero (t x : ℝ) : heatSqIter 0 t x = heatKernel t x ^ 2 := by
  rcases lt_or_ge 0 t with ht | ht
  · exact heatSqIter_zero ht x
  · rw [secondMom_heatKernel_of_nonpos ht, heatSqIter, secondMom_heatKernel_of_nonpos (by linarith)]
    simp

/-- The iterated kernels are jointly measurable. -/
theorem measurable_secondMomK (k : ℕ) : Measurable (Function.uncurry (secondMomK k)) := by
  have : Measurable fun p : ℝ × ℝ => heatSqIter k p.1 p.2 := by
    simp only [heatSqIter, heatKernel]; fun_prop
  exact this.ennreal_ofReal

/-- Composition of a jointly measurable `A` with measurable coordinates. -/
theorem secondMom_measurable_comp {α : Type*} {mα : MeasurableSpace α} {A : ℝ → ℝ → ℝ≥0∞}
    (hA : Measurable (Function.uncurry A)) {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => A (f a) (g a) :=
  hA.comp (f := fun a => (f a, g a)) (hf.prodMk hg)

/-- `(A ⊛ B)(t,x)` depends only on the values of `B` on `(0,t) × ℝ`: if `B = B'` there, then
`(A ⊛ B)(t,x) = (A ⊛ B')(t,x)`. -/
theorem secondMomConv_congr_right {A B B' : ℝ → ℝ → ℝ≥0∞} {t x : ℝ}
    (h : ∀ s y, 0 < s → s < t → B s y = B' s y) :
    secondMomConv A B t x = secondMomConv A B' t x :=
  setLIntegral_congr_fun (measurableSet_Ioo.prod MeasurableSet.univ) fun p hp => by
    simp only [h p.1 p.2 hp.1.1 hp.1.2]

/-- If `A = A'` on `(0, t) × ℝ`, then `(A ⊛ B)(t,x) = (A' ⊛ B)(t,x)`. -/
theorem secondMomConv_congr_left {A A' B : ℝ → ℝ → ℝ≥0∞} {t x : ℝ}
    (h : ∀ r z, 0 < r → r < t → A r z = A' r z) :
    secondMomConv A B t x = secondMomConv A' B t x :=
  setLIntegral_congr_fun (measurableSet_Ioo.prod MeasurableSet.univ) fun p hp => by
    simp only [h (t - p.1) (x - p.2) (by linarith [hp.1.2]) (by linarith [hp.1.1])]

/-- Additivity in the second argument (the first summand measurable). -/
theorem secondMomConv_add {A B B' : ℝ → ℝ → ℝ≥0∞} (hA : Measurable (Function.uncurry A))
    (hB : Measurable (Function.uncurry B)) (t x : ℝ) :
    secondMomConv A (fun s y => B s y + B' s y) t x =
      secondMomConv A B t x + secondMomConv A B' t x := by
  simp only [secondMomConv, mul_add]
  refine lintegral_add_left ?_ _
  exact (secondMom_measurable_comp hA (by fun_prop) (by fun_prop)).mul
    (secondMom_measurable_comp hB (by fun_prop) (by fun_prop))

/-- Finite additivity in the second argument (measurable summands). -/
theorem secondMomConv_finset_sum {A : ℝ → ℝ → ℝ≥0∞} {B : ℕ → ℝ → ℝ → ℝ≥0∞}
    (hA : Measurable (Function.uncurry A)) (hB : ∀ k, Measurable (Function.uncurry (B k)))
    (I : Finset ℕ) (t x : ℝ) :
    secondMomConv A (fun s y => ∑ k ∈ I, B k s y) t x = ∑ k ∈ I, secondMomConv A (B k) t x := by
  simp only [secondMomConv, Finset.mul_sum]
  refine lintegral_finsetSum _ fun k _ => ?_
  exact (secondMom_measurable_comp hA (by fun_prop) (by fun_prop)).mul
    (secondMom_measurable_comp (hB k) (by fun_prop) (by fun_prop))

/-- Monotonicity in the first argument, on `(0,t] × ℝ`. -/
theorem secondMomConv_mono_left {A A' B : ℝ → ℝ → ℝ≥0∞} {t x : ℝ}
    (h : ∀ r z, 0 < r → r ≤ t → A r z ≤ A' r z) :
    secondMomConv A B t x ≤ secondMomConv A' B t x :=
  setLIntegral_mono' (measurableSet_Ioo.prod MeasurableSet.univ) fun p hp =>
    mul_le_mul_left (h _ _ (by linarith [hp.1.2]) (by linarith [hp.1.1])) _

/-- `(c A) ⊛ B = c (A ⊛ B)`. -/
theorem secondMomConv_const_mul_left {c : ℝ≥0∞} (hc : c ≠ ⊤) (A B : ℝ → ℝ → ℝ≥0∞)
    (t x : ℝ) :
    secondMomConv (fun r z => c * A r z) B t x = c * secondMomConv A B t x := by
  simp only [secondMomConv, mul_assoc]
  exact lintegral_const_mul' _ _ hc

/-- The inner integral of the associativity, after the translation `p = p' + q`. -/
private lemma secondMomConv_inner {A B : ℝ → ℝ → ℝ≥0∞} (t x : ℝ) (q : ℝ × ℝ) :
    ∫⁻ p : ℝ × ℝ, (if q.1 < p.1 ∧ p.1 < t then A (t - p.1) (x - p.2) * B (p.1 - q.1) (p.2 - q.2)
      else 0) = secondMomConv A B (t - q.1) (x - q.2) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [← lintegral_add_right_eq_self _ q, secondMomConv,
    ← lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
  refine lintegral_congr fun p => ?_
  simp only [Prod.fst_add, Prod.snd_add, Set.indicator_apply, Set.mem_prod, Set.mem_Ioo,
    Set.mem_univ, and_true, add_sub_cancel_right]
  have e1 : (q.1 < p.1 + q.1 ∧ p.1 + q.1 < t) ↔ (0 < p.1 ∧ p.1 < t - q.1) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hp : 0 < p.1 ∧ p.1 < t - q.1
  · rw [ite_eq_left (e1.2 hp), ite_eq_left hp]
    congr 2 <;> ring
  · rw [ite_eq_right (fun h => hp (e1.1 h)), ite_eq_right hp]

/-- **Associativity** of the space-time convolution on `(0,t) × ℝ`, for measurable `A, B, C`:
`A ⊛ (B ⊛ C) = (A ⊛ B) ⊛ C` (Tonelli and translation invariance). -/
theorem secondMomConv_assoc {A B C : ℝ → ℝ → ℝ≥0∞} (hA : Measurable (Function.uncurry A))
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C)) (t x : ℝ) :
    secondMomConv A (secondMomConv B C) t x = secondMomConv (secondMomConv A B) C t x := by
  set Φ : ℝ × ℝ → ℝ × ℝ → ℝ≥0∞ := fun p q =>
    if 0 < q.1 ∧ q.1 < p.1 ∧ p.1 < t then
      A (t - p.1) (x - p.2) * B (p.1 - q.1) (p.2 - q.2) * C q.1 q.2 else 0 with hΦ
  have hs : MeasurableSet {a : (ℝ × ℝ) × (ℝ × ℝ) | 0 < a.2.1 ∧ a.2.1 < a.1.1 ∧ a.1.1 < t} := by
    measurability
  have hm : Measurable fun a : (ℝ × ℝ) × (ℝ × ℝ) =>
      A (t - a.1.1) (x - a.1.2) * B (a.1.1 - a.2.1) (a.1.2 - a.2.2) * C a.2.1 a.2.2 :=
    ((secondMom_measurable_comp hA (by fun_prop) (by fun_prop)).mul
      (secondMom_measurable_comp hB (by fun_prop) (by fun_prop))).mul
      (secondMom_measurable_comp hC (by fun_prop) (by fun_prop))
  have hΦm : Measurable (Function.uncurry Φ) := Measurable.ite hs hm measurable_const
  have hL : secondMomConv A (secondMomConv B C) t x = ∫⁻ p, ∫⁻ q, Φ p q := by
    rw [secondMomConv, ← lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
    refine lintegral_congr fun p => ?_
    simp only [Set.indicator_apply, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true]
    by_cases hp : 0 < p.1 ∧ p.1 < t
    · have hBC : Measurable fun q : ℝ × ℝ => B (p.1 - q.1) (p.2 - q.2) * C q.1 q.2 :=
        (secondMom_measurable_comp hB (by fun_prop) (by fun_prop)).mul
          (secondMom_measurable_comp hC (by fun_prop) (by fun_prop))
      rw [ite_eq_left hp, secondMomConv,
        ← lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ),
        ← lintegral_const_mul _ (hBC.indicator (measurableSet_Ioo.prod MeasurableSet.univ))]
      refine lintegral_congr fun q => ?_
      simp only [hΦ, Set.indicator_apply, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true]
      by_cases hq : 0 < q.1 ∧ q.1 < p.1
      · rw [ite_eq_left hq, ite_eq_left ⟨hq.1, hq.2, hp.2⟩, mul_assoc]
      · rw [ite_eq_right hq, ite_eq_right (fun h => hq ⟨h.1, h.2.1⟩), mul_zero]
    · rw [ite_eq_right hp]
      symm
      refine lintegral_eq_zero_iff' ?_ |>.2 (ae_of_all _ fun q => ?_)
      · exact (hΦm.comp (measurable_const.prodMk measurable_id)).aemeasurable
      · simp only [hΦ]
        rw [ite_eq_right]
        · rfl
        · exact fun h => hp ⟨h.1.trans h.2.1, h.2.2⟩
  rw [hL, lintegral_lintegral_swap hΦm.aemeasurable, secondMomConv,
    ← lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
  refine lintegral_congr fun q => ?_
  simp only [Set.indicator_apply, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true]
  by_cases hq : 0 < q.1
  · have e : ∀ p : ℝ × ℝ, Φ p q =
        (if q.1 < p.1 ∧ p.1 < t then A (t - p.1) (x - p.2) * B (p.1 - q.1) (p.2 - q.2)
          else 0) * C q.1 q.2 := by
      intro p
      simp only [hΦ]
      by_cases hp : q.1 < p.1 ∧ p.1 < t
      · rw [ite_eq_left ⟨hq, hp⟩, ite_eq_left hp]
      · rw [ite_eq_right (fun h => hp h.2), ite_eq_right hp, zero_mul]
    have hs' : MeasurableSet {p : ℝ × ℝ | q.1 < p.1 ∧ p.1 < t} := by
      measurability
    have hAB : Measurable fun p : ℝ × ℝ => A (t - p.1) (x - p.2) * B (p.1 - q.1) (p.2 - q.2) :=
      (secondMom_measurable_comp hA (by fun_prop) (by fun_prop)).mul
        (secondMom_measurable_comp hB (by fun_prop) (by fun_prop))
    simp_rw [e]
    rw [lintegral_mul_const _ (Measurable.ite hs' hAB measurable_const), secondMomConv_inner]
    by_cases hqt : q.1 < t
    · rw [ite_eq_left ⟨hq, hqt⟩]
    · rw [ite_eq_right (fun h => hqt h.2), secondMomConv,
        Set.Ioo_eq_empty (by linarith), Set.empty_prod, Measure.restrict_empty, lintegral_zero_measure,
        zero_mul]
  · rw [ite_eq_right (fun h => hq h.1)]
    refine lintegral_eq_zero_iff' ?_ |>.2 (ae_of_all _ fun p => ?_)
    · exact (hΦm.comp (measurable_id.prodMk measurable_const)).aemeasurable
    · simp only [hΦ]
      rw [ite_eq_right (fun h => hq h.1)]
      rfl

/-- `K ⊛ K^{⋆(k+1)} = K^{⋆(k+2)}` (`heatSqIter_succ`), as extended nonnegative numbers, for
every `t` (both sides vanish for `t ≤ 0`). -/
theorem secondMomConv_K_iter (k : ℕ) (t x : ℝ) :
    secondMomConv (secondMomK 0) (secondMomK k) t x = secondMomK (k + 1) t x := by
  rcases le_or_gt t 0 with ht | ht
  · rw [secondMomConv, Set.Ioo_eq_empty (by linarith), Set.empty_prod, Measure.restrict_empty,
      lintegral_zero_measure, secondMomK, heatSqIter, secondMom_heatKernel_of_nonpos (by linarith),
      mul_zero, ENNReal.ofReal_zero]
  obtain ⟨hint, heq⟩ := heatSqIter_succ k ht x
  rw [secondMomK, heq, ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun p => mul_nonneg (sq_nonneg _) (heatSqIter_nonneg _ _ _)), secondMomConv]
  refine lintegral_congr fun p => ?_
  rw [secondMomK, secondMomK, secondMom_heatSqIter_zero, ENNReal.ofReal_mul (sq_nonneg _)]

end QSSEPtoKPZ
