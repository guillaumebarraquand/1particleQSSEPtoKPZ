/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The constants of Section 3.1

For a real number `n ≥ 1`, equation (3.1) of the article:

  `θ_n = n^{-1/4}`,  `c_n = cosh θ_n`,  `λ_n = 2 (cosh θ_n - 1)`,  `a_n = n^{1/2} λ_n`,

and the bounds (3.2).
-/

@[expose] public section

noncomputable section

namespace QSSEPtoKPZ

/-- `θ_n = n^{-1/4}`, equation (3.1). -/
def thetaN (n : ℝ) : ℝ := n ^ (-1 / 4 : ℝ)

/-- `c_n = cosh θ_n`, equation (3.1). -/
def cN (n : ℝ) : ℝ := Real.cosh (thetaN n)

/-- `λ_n = 2 (cosh θ_n - 1)`, equation (3.1). -/
def lambdaN (n : ℝ) : ℝ := 2 * (Real.cosh (thetaN n) - 1)

/-- `a_n = n^{1/2} λ_n`, equation (3.1). -/
def aN (n : ℝ) : ℝ := n ^ (1 / 2 : ℝ) * lambdaN n

/-- Auxiliary: `sinh x ≤ x cosh x` for `x ≥ 0` (the derivative of `x cosh x - sinh x` is
`x sinh x ≥ 0`). -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y * Real.cosh y - Real.sinh y) (y * Real.sinh y) y := by
    intro y
    have := ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
    convert this using 1
    · rfl
    · simp only [id_eq]
      ring
  have hmono : Monotone (fun y : ℝ => y * Real.cosh y - Real.sinh y) := by
    refine monotone_of_hasDerivAt_nonneg hd fun y => ?_
    rcases le_total 0 y with hy | hy
    · exact mul_nonneg hy (Real.sinh_nonneg_iff.2 hy)
    · exact mul_nonneg_of_nonpos_of_nonpos hy (Real.sinh_nonpos_iff.2 hy)
  have := hmono hx
  simp at this
  linarith

/-- The elementary inequalities of Section 3.1: `θ² ≤ 2 (cosh θ - 1) ≤ θ² cosh θ` for `θ ≥ 0`.
(The second family of inequalities stated there, on `sinh θ - θ`, is not used in the pilot and is
not stated here.) -/
theorem sq_le_two_mul_cosh_sub_one {θ : ℝ} (hθ : 0 ≤ θ) :
    θ ^ 2 ≤ 2 * (Real.cosh θ - 1) ∧ 2 * (Real.cosh θ - 1) ≤ θ ^ 2 * Real.cosh θ := by
  set x := θ / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hθx : θ = 2 * x := by rw [hx]; ring
  have hcosh : Real.cosh θ = Real.cosh x ^ 2 + Real.sinh x ^ 2 := by
    rw [hθx, Real.cosh_two_mul]
  have hsq := Real.cosh_sq x
  have hs1 : x ≤ Real.sinh x := Real.self_le_sinh_iff.2 hx0
  have hs2 : Real.sinh x ≤ x * Real.cosh x := sinh_le_mul_cosh hx0
  have hs0 : 0 ≤ Real.sinh x := hx0.trans hs1
  rw [hcosh, hθx]
  constructor
  · nlinarith [mul_le_mul hs1 hs1 hx0 hs0]
  · have hxc : 0 ≤ x * Real.cosh x := mul_nonneg hx0 (zero_le_one.trans (Real.one_le_cosh x))
    nlinarith [mul_le_mul hs2 hs2 hs0 hxc, mul_nonneg (sq_nonneg x) (sq_nonneg (Real.sinh x))]

/-- **Equation (3.2).** For all `n ≥ 1`:
`n^{-1/2} ≤ λ_n ≤ c_n n^{-1/2}` and `1 ≤ a_n ≤ c_n ≤ cosh 1 < 2`. -/
theorem constants_bounds {n : ℝ} (hn : 1 ≤ n) :
    n ^ (-1 / 2 : ℝ) ≤ lambdaN n ∧ lambdaN n ≤ cN n * n ^ (-1 / 2 : ℝ) ∧
      1 ≤ aN n ∧ aN n ≤ cN n ∧ cN n ≤ Real.cosh 1 ∧ Real.cosh 1 < 2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hθ0 : 0 < thetaN n := Real.rpow_pos_of_pos hn0 _
  have hθ1 : thetaN n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hθsq : thetaN n ^ 2 = n ^ (-1 / 2 : ℝ) := by
    rw [thetaN, ← Real.rpow_mul_natCast hn0.le]
    norm_num
  have hhalf : n ^ (1 / 2 : ℝ) * n ^ (-1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hpos : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  obtain ⟨h1, h2⟩ := sq_le_two_mul_cosh_sub_one hθ0.le
  rw [hθsq] at h1 h2
  have hl1 : n ^ (-1 / 2 : ℝ) ≤ lambdaN n := h1
  have hl2 : lambdaN n ≤ cN n * n ^ (-1 / 2 : ℝ) := by
    rw [mul_comm]; exact h2
  have hc1 : cN n ≤ Real.cosh 1 := by
    rw [cN, Real.cosh_le_cosh, abs_of_pos hθ0, abs_one]
    exact hθ1
  have hcosh1 : Real.cosh 1 < 2 := by
    rw [Real.cosh_eq]
    have he := Real.exp_one_lt_three
    have he' : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    linarith
  refine ⟨hl1, hl2, ?_, ?_, hc1, hcosh1⟩
  · have := mul_le_mul_of_nonneg_left hl1 hpos.le
    rwa [hhalf] at this
  · calc aN n = n ^ (1 / 2 : ℝ) * lambdaN n := rfl
      _ ≤ n ^ (1 / 2 : ℝ) * (cN n * n ^ (-1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hl2 hpos.le
      _ = cN n * (n ^ (1 / 2 : ℝ) * n ^ (-1 / 2 : ℝ)) := by ring
      _ = cN n := by rw [hhalf, mul_one]

end QSSEPtoKPZ
