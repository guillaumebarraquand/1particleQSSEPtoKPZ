/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs

/-!
# Test functions `φ ∈ C_b^{1,3}`: continuity and bounds used on the path space (task Q1a)

For `φ ∈ C_b^{1,3}([0,T] × ℝ)` (`IsC13`), the functions `φ_s(y)` and
`∂ₛφ_s(y) + 𝒜_nφ_s(y)` (the integrand of (3.14)) are continuous and bounded on `[0,T] × ℝ`. We
also introduce the clamp `s ↦ max(0, min(T, s))`, a continuous map of `ℝ` onto `[0,T]` equal to
the identity on `[0,T]`, used to extend functions of `s ∈ [0,T]` to all `s` without changing the
integrals over `[0,t] ⊆ [0,T]`.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace QSSEPtoKPZ

/-- The clamp `s ↦ max(0, min(T, s))` onto `[0,T]`. -/
def pathFunClamp (T s : ℝ) : ℝ := max 0 (min T s)

/-- The clamp is the identity on `[0,T]`. -/
theorem pathFunClamp_of_mem {T s : ℝ} (hs : s ∈ Set.Icc 0 T) : pathFunClamp T s = s := by
  unfold pathFunClamp
  rw [min_eq_right hs.2, max_eq_right hs.1]

/-- The clamp takes values in `[0,T]` when `0 ≤ T`. -/
theorem pathFunClamp_mem {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : pathFunClamp T s ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

/-- The clamp is continuous. -/
theorem continuous_pathFunClamp (T : ℝ) : Continuous (pathFunClamp T) := by
  unfold pathFunClamp; fun_prop

variable {T C : ℝ} {φ φt : ℝ → ℝ → ℝ}

/-- `(s, y) ↦ φ_s(f(y))` is continuous on `[0,T] × ℝ` for `f` continuous. -/
theorem IsC13.pathFun_continuousOn_comp (hφ : IsC13 T φ φt C) {f : ℝ → ℝ} (hf : Continuous f) :
    ContinuousOn (fun p : ℝ × ℝ => φ p.1 (f p.2)) (Set.Icc 0 T ×ˢ Set.univ) := by
  have h0 := hφ.continuousOn.2 0 (by norm_num)
  simp only [iteratedDeriv_zero] at h0
  exact h0.comp (continuous_fst.prodMk (hf.comp continuous_snd)).continuousOn
    fun p hp => ⟨hp.1, trivial⟩

/-- `(s, y) ↦ ∂ₓφ_s(y)` is continuous on `[0,T] × ℝ`. -/
theorem IsC13.pathFun_continuousOn_deriv (hφ : IsC13 T φ φt C) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (φ p.1) p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  have h1 := hφ.continuousOn.2 1 (by norm_num)
  simpa only [iteratedDeriv_one] using h1

/-- `φ` is bounded on `[0,T] × ℝ`, by a nonnegative constant. -/
theorem IsC13.pathFun_bound (hφ : IsC13 T φ φt C) :
    ∃ c, 0 ≤ c ∧ ∀ s ∈ Set.Icc 0 T, ∀ y, |φ s y| ≤ c := by
  obtain ⟨c, -, hc⟩ := hφ.bound
  refine ⟨max (c 0) 0, le_max_right _ _, fun s hs y => (hc s hs y).1.trans (le_max_left _ _)⟩

/-- The integrand `∂ₛφ_s + 𝒜_nφ_s` of (3.14) is continuous on `[0,T] × ℝ`. -/
theorem IsC13.pathFun_continuousOn_drift (hφ : IsC13 T φ φt C) (n : ℝ) :
    ContinuousOn (Function.uncurry fun s y => φt s y + AN n (φ s) y)
      (Set.Icc 0 T ×ˢ Set.univ) := by
  have ha := hφ.pathFun_continuousOn_comp (f := fun y => y + n ^ (-1 / 2 : ℝ)) (by fun_prop)
  have hb := hφ.pathFun_continuousOn_comp (f := fun y => y - n ^ (-1 / 2 : ℝ)) (by fun_prop)
  have hc := hφ.pathFun_continuousOn_comp (f := fun y => y) continuous_id
  have hd := hφ.pathFun_continuousOn_deriv
  have he := hφ.continuousOn.1
  unfold AN
  exact he.add ((continuousOn_const.mul (((continuousOn_const.mul ha).add
    (continuousOn_const.mul hb)).sub (continuousOn_const.mul hc))).sub
    (continuousOn_const.mul hd))

/-- The integrand `∂ₛφ_s + 𝒜_nφ_s` of (3.14) is bounded on `[0,T] × ℝ`. -/
theorem IsC13.pathFun_bound_drift (hφ : IsC13 T φ φt C) (n : ℝ) :
    ∃ K, ∀ s ∈ Set.Icc 0 T, ∀ y, |φt s y + AN n (φ s) y| ≤ K := by
  obtain ⟨c, -, hc⟩ := hφ.bound
  refine ⟨c 1 + |n / 2| * (Real.exp (thetaN n) * c 0 + Real.exp (-thetaN n) * c 0 +
    |2 * cN n| * c 0) + |n ^ (1 / 4 : ℝ)| * c 2, fun s hs y => ?_⟩
  have h1 := (hc s hs y).2.1
  have h2 := (hc s hs y).2.2.1
  rw [iteratedDeriv_one] at h2
  have hp := (hc s hs (y + n ^ (-1 / 2 : ℝ))).1
  have hm := (hc s hs (y - n ^ (-1 / 2 : ℝ))).1
  have h0 := (hc s hs y).1
  have e1 := Real.exp_pos (thetaN n)
  have e2 := Real.exp_pos (-thetaN n)
  have hS : |Real.exp (thetaN n) * φ s (y + n ^ (-1 / 2 : ℝ)) +
      Real.exp (-thetaN n) * φ s (y - n ^ (-1 / 2 : ℝ)) - 2 * cN n * φ s y| ≤
      Real.exp (thetaN n) * c 0 + Real.exp (-thetaN n) * c 0 + |2 * cN n| * c 0 := by
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul, abs_of_pos e1]; exact mul_le_mul_of_nonneg_left hp e1.le
    · rw [abs_mul, abs_of_pos e2]; exact mul_le_mul_of_nonneg_left hm e2.le
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
  unfold AN
  calc |φt s y + (n / 2 * (Real.exp (thetaN n) * φ s (y + n ^ (-1 / 2 : ℝ)) +
        Real.exp (-thetaN n) * φ s (y - n ^ (-1 / 2 : ℝ)) - 2 * cN n * φ s y) -
        n ^ (1 / 4 : ℝ) * deriv (φ s) y)|
      ≤ |φt s y| + (|n / 2 * (Real.exp (thetaN n) * φ s (y + n ^ (-1 / 2 : ℝ)) +
        Real.exp (-thetaN n) * φ s (y - n ^ (-1 / 2 : ℝ)) - 2 * cN n * φ s y)| +
        |n ^ (1 / 4 : ℝ) * deriv (φ s) y|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ _ := by
      rw [abs_mul, abs_mul, add_assoc]
      exact add_le_add h1 (add_le_add (mul_le_mul_of_nonneg_left hS (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))

end QSSEPtoKPZ
