/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.TiltedField.Identities
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Calculus facts on `φ ∈ C_b^{1,3}([0,T] × ℝ)` for the proof of Lemma 6.4

Task G1. For `φ` with `IsC13 T φ φt C` (`‖φ‖_{1,3} ≤ C`) and `t ∈ [0,T]`:

* `IsC13.abs_le_C`: `|φ_t|, |∂ₜφ_t|, |∂ₓφ_t|, |∂ₓ²φ_t| ≤ C`;
* `IsC13.abs_sub_le`, `IsC13.abs_deriv_sub_le`: `φ_t` and `∂ₓφ_t` are `C`-Lipschitz;
* `IsC13.abs_taylor_le`: `|φ_t(b) - φ_t(a) - (b - a) ∂ₓφ_t(a)| ≤ C (b - a)²`;
* `IsC13.abs_dt_add_AN_le`: `|∂ₜφ_t + 𝒜_n φ_t| ≤ 3C` (from Proposition 3.1 (1));
* `IsC13.hasDerivWithinAt_line`: the chain rule
  `d/ds φ_s(a + b s) = ∂ₜφ_s(a + b s) + b ∂ₓφ_s(a + b s)` on `[0,T]`, which only uses the
  continuity of `∂ₜφ` on `[0,T] × ℝ` (no joint differentiability is assumed in `IsC13`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace QSSEPtoKPZ

variable {T C : ℝ} {φ φt : ℝ → ℝ → ℝ}

namespace IsC13

/-- The five bounds of `‖φ‖_{1,3} ≤ C`, each by `C` (the partial bounds are nonnegative). -/
lemma corr_abs_le_C (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    |φ t x| ≤ C ∧ |φt t x| ≤ C ∧ |deriv (φ t) x| ≤ C ∧ |deriv (deriv (φ t)) x| ≤ C ∧
      |iteratedDeriv 2 (φ t) x| ≤ C := by
  obtain ⟨c, hc, hb⟩ := hφ.bound
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    obtain ⟨b0, b1, b2, b3, b4⟩ := hb 0 h0 0
    fin_cases i
    · exact (abs_nonneg _).trans b0
    · exact (abs_nonneg _).trans b1
    · exact (abs_nonneg _).trans b2
    · exact (abs_nonneg _).trans b3
    · exact (abs_nonneg _).trans b4
  rw [Fin.sum_univ_five] at hc
  have := hc0 0; have := hc0 1; have := hc0 2; have := hc0 3; have := hc0 4
  obtain ⟨b0, b1, b2, b3, b4⟩ := hb t ht x
  have e2 : iteratedDeriv 2 (φ t) = deriv (deriv (φ t)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [iteratedDeriv_one] at b2
  refine ⟨by linarith, by linarith, by linarith, ?_, by linarith⟩
  rw [← e2]; linarith

/-- `0 ≤ C`. -/
lemma corr_C_nonneg (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) : 0 ≤ C :=
  (abs_nonneg _).trans (hφ.corr_abs_le_C hT ⟨le_rfl, hT⟩ 0).1

/-- `φ_t` is differentiable. -/
lemma corr_differentiable (hφ : IsC13 T φ φt C) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Differentiable ℝ (φ t) :=
  (hφ.contDiff t ht).differentiable (by norm_num)

/-- `∂ₓφ_t` is differentiable. -/
lemma corr_differentiable_deriv (hφ : IsC13 T φ φt C) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Differentiable ℝ (deriv (φ t)) := by
  have := (hφ.contDiff t ht).differentiable_iteratedDeriv 1 (by norm_num)
  rwa [iteratedDeriv_one] at this

/-- A function whose derivative is bounded by `M` is `M`-Lipschitz. -/
lemma corr_abs_sub_le_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : ∀ x, |deriv f x| ≤ M) (a b : ℝ) : |f b - f a| ≤ M * |b - a| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun x _ => hf x)
    (fun x _ => by simpa [Real.norm_eq_abs] using hM x) convex_univ (mem_univ a) (mem_univ b)
  simpa [Real.norm_eq_abs] using this

/-- `φ_t` is `C`-Lipschitz. -/
lemma corr_abs_sub_le (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (a b : ℝ) :
    |φ t b - φ t a| ≤ C * |b - a| :=
  corr_abs_sub_le_of_deriv (hφ.corr_differentiable ht) (fun x => (hφ.corr_abs_le_C hT ht x).2.2.1) a b

/-- `∂ₓφ_t` is `C`-Lipschitz. -/
lemma corr_abs_deriv_sub_le (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (a b : ℝ) : |deriv (φ t) b - deriv (φ t) a| ≤ C * |b - a| :=
  corr_abs_sub_le_of_deriv (hφ.corr_differentiable_deriv ht) (fun x => (hφ.corr_abs_le_C hT ht x).2.2.2.1) a b

/-- First order Taylor bound: `|φ_t(b) - φ_t(a) - (b - a) ∂ₓφ_t(a)| ≤ C (b - a)²`. -/
lemma corr_abs_taylor_le (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (a b : ℝ) :
    |φ t b - φ t a - (b - a) * deriv (φ t) a| ≤ C * (b - a) ^ 2 := by
  set d := deriv (φ t) a
  have hd : ∀ x, HasDerivAt (fun x => φ t x - x * d) (deriv (φ t) x - d) x := fun x => by
    have := ((hφ.corr_differentiable ht) x).hasDerivAt.fun_sub ((hasDerivAt_id x).mul_const d)
    simpa using this
  have hC := hφ.corr_C_nonneg hT
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (s := uIcc a b) (C := C * |b - a|)
    (fun x _ => (hd x).differentiableAt)
    (fun x hx => by
      rw [(hd x).deriv, Real.norm_eq_abs]
      calc |deriv (φ t) x - d| ≤ C * |x - a| := hφ.corr_abs_deriv_sub_le hT ht a x
        _ ≤ C * |b - a| := mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hx) hC)
    (convex_uIcc a b) (left_mem_uIcc) (right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  have e : φ t b - b * d - (φ t a - a * d) = φ t b - φ t a - (b - a) * d := by ring
  rw [e] at key
  calc _ ≤ C * |b - a| * |b - a| := key
    _ = C * (b - a) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `|∂ₜφ_t + 𝒜_n φ_t| ≤ 3C`, from Proposition 3.1 (1) (`prop_3_1_generator`). -/
lemma corr_abs_dt_add_AN_le (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) {n : ℝ}
    (hn : 1 ≤ n) (y : ℝ) : |φt t y + AN n (φ t) y| ≤ 3 * C := by
  obtain ⟨c, hc, hb⟩ := hφ.bound
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    obtain ⟨b0, b1, b2, b3, b4⟩ := hb 0 h0 0
    fin_cases i
    · exact (abs_nonneg _).trans b0
    · exact (abs_nonneg _).trans b1
    · exact (abs_nonneg _).trans b2
    · exact (abs_nonneg _).trans b3
    · exact (abs_nonneg _).trans b4
  have h1 : IsC13 1 (fun _ => φ t) (fun _ _ => 0) C := by
    refine ⟨fun _ _ => hφ.contDiff t ht, fun x s _ => hasDerivWithinAt_const _ _ _,
      ⟨continuousOn_const, fun k hk => ?_⟩, ⟨fun i => if i = 1 then 0 else c i, ?_, ?_⟩⟩
    · exact (((hφ.contDiff t ht).continuous_iteratedDeriv k
        (by exact_mod_cast hk)).comp continuous_snd).continuousOn
    · rw [Fin.sum_univ_five] at hc ⊢
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      linarith [hc0 1]
    · intro s _ x
      obtain ⟨b0, -, b2, b3, b4⟩ := hb t ht x
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, abs_zero, le_refl, true_and]
      exact ⟨b0, b2, b3, b4⟩
  have hgen := prop_3_1_generator hn h1 y
  obtain ⟨-, b1, -, -, b2⟩ := hφ.corr_abs_le_C hT ht y
  have hC := hφ.corr_C_nonneg hT
  have hn4 : n ^ (-1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have h4 : n ^ (-1 / 4 : ℝ) * C ≤ C := by nlinarith
  rw [abs_le] at hgen b1 b2 ⊢
  constructor <;> nlinarith

/-- The mean value theorem in time: for `s, t ∈ [0,T]`, `φ_s(y) - φ_t(y) = (s - t) ∂ₜφ_ξ(y)`
for some `ξ` between `s` and `t`. -/
lemma corr_exists_time_mvt (hφ : IsC13 T φ φt C) {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (y : ℝ) : ∃ ξ ∈ uIcc s t, φ s y - φ t y = (s - t) * φt ξ y := by
  have hcont : ContinuousOn (fun u => φ u y) (Icc 0 T) := fun u hu =>
    (hφ.hasDerivWithinAt y u hu).continuousWithinAt
  have hder : ∀ u ∈ Ioo 0 T, HasDerivAt (fun u => φ u y) (φt u y) u := fun u hu =>
    (hφ.hasDerivWithinAt y u (Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  rcases lt_trichotomy s t with hst | rfl | hst
  · obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope (fun u => φ u y) (fun u => φt u y) hst
      (hcont.mono (Icc_subset_Icc hs.1 ht.2))
      (fun u hu => hder u ⟨hs.1.trans_lt hu.1, hu.2.trans_le ht.2⟩)
    refine ⟨ξ, ?_, ?_⟩
    · rw [uIcc_of_le hst.le]; exact Ioo_subset_Icc_self hξ
    · rw [e]; field_simp [sub_ne_zero.2 hst.ne']; ring
  · exact ⟨s, left_mem_uIcc, by ring⟩
  · obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope (fun u => φ u y) (fun u => φt u y) hst
      (hcont.mono (Icc_subset_Icc ht.1 hs.2))
      (fun u hu => hder u ⟨ht.1.trans_lt hu.1, hu.2.trans_le hs.2⟩)
    refine ⟨ξ, ?_, ?_⟩
    · rw [uIcc_of_ge hst.le]; exact Ioo_subset_Icc_self hξ
    · rw [e]; field_simp [sub_ne_zero.2 hst.ne']

/-- The chain rule along a line: on `[0,T]`,
`d/ds φ_s(a + b s) = ∂ₜφ_s(a + b s) + b ∂ₓφ_s(a + b s)`. -/
lemma corr_hasDerivWithinAt_line (hφ : IsC13 T φ φt C) {t : ℝ} (ht : t ∈ Icc 0 T) (a b : ℝ) :
    HasDerivWithinAt (fun s => φ s (a + b * s))
      (φt t (a + b * t) + b * deriv (φ t) (a + b * t)) (Icc 0 T) t := by
  -- split `φ_s(y_s) = (φ_s(y_s) - φ_t(y_s)) + φ_t(y_s)`
  have hK : HasDerivWithinAt (fun s => φ t (a + b * s)) (b * deriv (φ t) (a + b * t))
      (Icc 0 T) t := by
    have hl : HasDerivAt (fun s => a + b * s) b t := by
      simpa using ((hasDerivAt_id t).const_mul b).const_add a
    have := ((hφ.corr_differentiable ht) (a + b * t)).hasDerivAt.comp t hl
    rw [mul_comm] at this
    exact this.hasDerivWithinAt
  have hH : HasDerivWithinAt (fun s => φ s (a + b * s) - φ t (a + b * s)) (φt t (a + b * t))
      (Icc 0 T) t := by
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    have hc : ContinuousWithinAt (Function.uncurry φt) (Icc 0 T ×ˢ univ) (t, a + b * t) :=
      hφ.continuousOn.1 _ ⟨ht, mem_univ _⟩
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hc ε hε
    have hb1 : 0 < 1 + |b| := by positivity
    filter_upwards [inter_mem_nhdsWithin (Icc 0 T)
      (Metric.ball_mem_nhds t (div_pos hδ hb1)), self_mem_nhdsWithin] with s hs hsI
    have hst : |s - t| < δ / (1 + |b|) := by
      have := hs.2; rwa [Metric.mem_ball, Real.dist_eq] at this
    obtain ⟨ξ, hξ, e⟩ := hφ.corr_exists_time_mvt hsI ht (a + b * s)
    have hξt : |ξ - t| ≤ |s - t| := by
      have := abs_sub_left_of_mem_uIcc (a := t) (b := s) (by rwa [uIcc_comm] at hξ)
      exact this
    have hξI : ξ ∈ Icc 0 T := (uIcc_subset_Icc hsI ht) hξ
    have hlt : |s - t| * (1 + |b|) < δ := (lt_div_iff₀ hb1).1 hst
    have hdist : dist (ξ, a + b * s) (t, a + b * t) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      constructor
      · nlinarith [abs_nonneg b, abs_nonneg (s - t)]
      · have : a + b * s - (a + b * t) = b * (s - t) := by ring
        rw [this, abs_mul]; nlinarith [abs_nonneg b, abs_nonneg (s - t)]
    have h2 := hδε (x := (ξ, a + b * s)) ⟨hξI, mem_univ _⟩ hdist
    rw [Real.dist_eq] at h2
    simp only [Function.uncurry_apply_pair] at h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_self, sub_zero, e, smul_eq_mul,
      ← mul_sub, abs_mul]
    rw [mul_comm ε]
    exact mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
  have := hH.fun_add hK
  simpa only [sub_add_cancel] using this

end IsC13

end QSSEPtoKPZ
