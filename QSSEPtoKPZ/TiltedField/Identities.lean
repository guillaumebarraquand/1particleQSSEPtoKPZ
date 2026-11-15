/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.WaveFunction.Defs
public import QSSEPtoKPZ.SecondMoments.Generator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Section 3: elementary inequalities and algebraic identities

Statements: Stage 2, task T0; proofs: task E1. No probability here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*}

/-- **The inequality on `sinh θ - θ` of Section 3.1** (stated before (3.2)): for `θ ≥ 0`,
`0 ≤ sinh θ - θ ≤ (θ³/6) cosh θ`. (The other inequality stated there,
`θ² ≤ 2(cosh θ - 1) ≤ θ² cosh θ`, is `sq_le_two_mul_cosh_sub_one` of Stage 1.) -/
theorem sinh_sub_self_bounds {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ Real.sinh θ - θ ∧ Real.sinh θ - θ ≤ θ ^ 3 / 6 * Real.cosh θ := by
  refine ⟨by linarith [Real.self_le_sinh_iff.2 hθ], ?_⟩
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x ^ 3 / 6 * Real.cosh x - Real.sinh x + x)
      (x ^ 2 / 2 * Real.cosh x + x ^ 3 / 6 * Real.sinh x - Real.cosh x + 1) x := by
    intro x
    have := ((((hasDerivAt_pow 3 x).div_const 6).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x)).add (hasDerivAt_id x)
    convert this using 1
    · funext y
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id]
    · norm_num
      left
      ring
  have hmono : MonotoneOn (fun x => x ^ 3 / 6 * Real.cosh x - Real.sinh x + x) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
      fun x hx => ?_
    rw [interior_Ici] at hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have h1 := (sq_le_two_mul_cosh_sub_one hx0).2
    have h2 : 0 ≤ x ^ 3 / 6 * Real.sinh x :=
      mul_nonneg (by positivity) (Real.sinh_nonneg_iff.2 hx0)
    linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hθ) hθ
  norm_num at this
  linarith

/-- Auxiliary: the Taylor expansion of `cosh` at order 4 with remainder, for `0 ≤ θ ≤ 1`:
`0 ≤ cosh θ - 1 - θ²/2 - θ⁴/24 ≤ θ⁶`. -/
private lemma cosh_taylor_bounds {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 ≤ Real.cosh θ - 1 - θ ^ 2 / 2 - θ ^ 4 / 24 ∧
      Real.cosh θ - 1 - θ ^ 2 / 2 - θ ^ 4 / 24 ≤ θ ^ 6 := by
  constructor
  · have := sum_le_hasSum (Finset.range 3) (fun i _ => by positivity) (Real.hasSum_cosh θ)
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  · have e1 := Real.exp_bound (x := θ) (by rw [abs_of_nonneg h0]; exact h1) (n := 6) (by norm_num)
    have e2 := Real.exp_bound (x := -θ) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 6)
      (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg h0] at e1 e2
    rw [abs_le] at e1 e2
    rw [Real.cosh_eq]
    have h6 : 0 ≤ θ ^ 6 := by positivity
    norm_num at e1 e2
    nlinarith [e1.1, e1.2, e2.1, e2.2]

/-- **Equation (3.8)**: the measure `rescaledMeasure ⊤ n P t` of Theorem 1.2 (equation (1.15),
`L = ∞`), with `P = density ψ ω`, is `ϱ_n(t)` times the measure `tiltedMeasure n ψ ω t` of (3.5).
Holds for every realization `ω` and every real `t`. -/
theorem rescaledMeasure_eq {n : ℝ} (hn : 1 ≤ n) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) :
    rescaledMeasure ⊤ n (density ψ ω) t =
      ENNReal.ofReal (varrhoN n t) • tiltedMeasure n ψ ω t := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  set a := n ^ (1 / 4 : ℝ) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hn0 _
  have hpow : ∀ k : ℕ, n ^ ((k : ℝ) / 4) = a ^ k := fun k => by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have h2 : n ^ (1 / 2 : ℝ) = a ^ 2 := by rw [← hpow 2]; norm_num
  have h3 : n ^ (3 / 4 : ℝ) = a ^ 3 := by rw [← hpow 3]; norm_num
  have hm : n ^ (-1 / 2 : ℝ) = (a ^ 2)⁻¹ := by
    rw [← h2, ← Real.rpow_neg hn0.le]; norm_num
  have hq : thetaN n = a⁻¹ := by
    rw [thetaN, ha_def, ← Real.rpow_neg hn0.le]; norm_num
  have key : ∀ y : ℤ, n ^ (-1 / 2 : ℝ) * rescaledField n (density ψ ω) t y =
      varrhoN n t * zN n ψ ω t y := by
    intro y
    unfold rescaledField zN varrhoN rescaledPosition
    rw [h2, h3, hm, hq]
    have hx : a ^ 2 * t / 2 + a * ((y - a ^ 3 * t) / a ^ 2) - t / 24 =
        (n * lambdaN n / 2 - a ^ 2 / 2 - 1 / 24) * t + (a⁻¹ * y - n * lambdaN n / 2 * t) := by
      field_simp
      ring
    rw [hx, Real.exp_add]
    field_simp
  have hbox : ∀ x : ℤ, x ∈ box ⊤ := fun x => by simp [box]
  have hv : 0 ≤ varrhoN n t := (Real.exp_pos _).le
  ext s hs
  rw [Measure.smul_apply, rescaledMeasure, tiltedMeasure, Measure.sum_apply _ hs,
    Measure.sum_apply _ hs, smul_eq_mul, ← ENNReal.tsum_mul_left,
    ← (Equiv.subtypeUnivEquiv hbox).tsum_eq]
  refine tsum_congr fun y => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Equiv.subtypeUnivEquiv_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hv, key]

/-- **Equation (3.9)**: for `n ≥ 1` and `t ≥ 0`, `1 ≤ ϱ_n(t) ≤ exp(t n^{-1/2})`. -/
theorem varrhoN_bounds {n t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) :
    1 ≤ varrhoN n t ∧ varrhoN n t ≤ Real.exp (t * n ^ (-1 / 2 : ℝ)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  set q := thetaN n with hq_def
  have hq0 : 0 < q := Real.rpow_pos_of_pos hn0 _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hpow : ∀ k : ℕ, q ^ k = n ^ (-(k : ℝ) / 4) := fun k => by
    rw [hq_def, thetaN, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have hq4 : n * q ^ 4 = 1 := by
    rw [hpow 4, show -((4 : ℕ) : ℝ) / 4 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  have hq6 : n ^ (-1 / 2 : ℝ) = n * q ^ 6 := by
    rw [hpow 6, show -1 / 2 = 1 + -((6 : ℕ) : ℝ) / 4 by norm_num, Real.rpow_add hn0,
      Real.rpow_one]
  have hq2 : n ^ (1 / 2 : ℝ) = n * q ^ 2 := by
    rw [hpow 2, show (1 / 2 : ℝ) = 1 + -((2 : ℕ) : ℝ) / 4 by norm_num, Real.rpow_add hn0,
      Real.rpow_one]
  obtain ⟨hD0, hD1⟩ := cosh_taylor_bounds hq0.le hq1
  set K := n * lambdaN n / 2 - n ^ (1 / 2 : ℝ) / 2 - 1 / 24 with hK
  have hKD : K = n * (Real.cosh q - 1 - q ^ 2 / 2 - q ^ 4 / 24) := by
    rw [hK, hq2, lambdaN]
    linear_combination hq4 / 24
  have hK0 : 0 ≤ K := by rw [hKD]; exact mul_nonneg hn0.le hD0
  have hK1 : K ≤ n ^ (-1 / 2 : ℝ) := by
    rw [hKD, hq6]; exact mul_le_mul_of_nonneg_left hD1 hn0.le
  refine ⟨Real.one_le_exp (mul_nonneg hK0 ht), Real.exp_le_exp.2 ?_⟩
  rw [mul_comm t]
  exact mul_le_mul_of_nonneg_right hK1 ht

/-- Auxiliary: Taylor's formula at order 2 with the Lagrange remainder, for `φ ∈ C³(ℝ)` with
`|φ⁽³⁾| ≤ M`: `|φ(y+h) - φ(y) - h φ'(y) - (h²/2) φ''(y)| ≤ M |h|³ / 6`. -/
private lemma taylor_two_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {M : ℝ}
    (hM : ∀ z, |iteratedDeriv 3 φ z| ≤ M) (y h : ℝ) :
    |φ (y + h) - φ y - h * deriv φ y - h ^ 2 / 2 * iteratedDeriv 2 φ y| ≤ M * |h| ^ 3 / 6 := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hne : y ≠ y + h := by intro e; apply hh; linarith
  obtain ⟨x', -, hx'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne
    (hφ.contDiffOn.of_le (by norm_num))
  have hu := uniqueDiffOn_uIcc hne
  have hmem : y ∈ Set.uIcc y (y + h) := Set.left_mem_uIcc
  rw [taylor_within_apply] at hx'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hx'
  rw [iteratedDerivWithin_eq_iteratedDeriv hu (hφ.contDiffAt.of_le (by norm_num)) hmem,
    iteratedDerivWithin_eq_iteratedDeriv hu (hφ.contDiffAt.of_le (by norm_num)) hmem,
    iteratedDerivWithin_eq_iteratedDeriv hu (hφ.contDiffAt.of_le (by norm_num)) hmem] at hx'
  simp only [iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, add_sub_cancel_left] at hx'
  norm_num [Nat.factorial] at hx'
  have e : φ (y + h) - φ y - h * deriv φ y - h ^ 2 / 2 * iteratedDeriv 2 φ y =
      iteratedDeriv 3 φ x' * h ^ 3 / 6 := by rw [← hx']; ring
  rw [e, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  gcongr
  exact hM x'

/-- **Proposition 3.1 (1)**: for `n ≥ 1` and `φ ∈ C_b³(ℝ)` with `‖φ‖_{1,3} ≤ C` (`φ` seen as a
function of `(t,x)` which does not depend on `t`, with `∂ₜφ = 0`),
`‖𝒜_n φ - φ''/2‖_∞ ≤ n^{-1/4} C`. -/
theorem prop_3_1_generator {n C : ℝ} (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hφ : IsC13 1 (fun _ => φ) (fun _ _ => 0) C) (y : ℝ) :
    |AN n φ y - iteratedDeriv 2 φ y / 2| ≤ n ^ (-1 / 4 : ℝ) * C := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨c, hcsum, hc⟩ := hφ.bound
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hcd : ContDiff ℝ 3 φ := hφ.contDiff 0 h0mem
  have hb : ∀ x, |φ x| ≤ c 0 ∧ |(0 : ℝ)| ≤ c 1 ∧ |iteratedDeriv 1 φ x| ≤ c 2 ∧
      |iteratedDeriv 2 φ x| ≤ c 3 ∧ |iteratedDeriv 3 φ x| ≤ c 4 := fun x => hc 0 h0mem x
  have hc0 : 0 ≤ c 0 := (abs_nonneg _).trans (hb 0).1
  have hc1 : 0 ≤ c 1 := (abs_nonneg _).trans (hb 0).2.1
  have hc2 : 0 ≤ c 2 := (abs_nonneg _).trans (hb 0).2.2.1
  have hc3 : 0 ≤ c 3 := (abs_nonneg _).trans (hb 0).2.2.2.1
  have hc4 : 0 ≤ c 4 := (abs_nonneg _).trans (hb 0).2.2.2.2
  have hsum : c 2 + c 3 + c 4 ≤ C := by
    simp only [Fin.sum_univ_five] at hcsum
    linarith
  -- the constants, in terms of `q = θ_n = n^{-1/4}`
  set q := thetaN n with hq_def
  have hq0 : 0 < q := Real.rpow_pos_of_pos hn0 _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hpow : ∀ k : ℕ, q ^ k = n ^ (-(k : ℝ) / 4) := fun k => by
    rw [hq_def, thetaN, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have hq4 : n * q ^ 4 = 1 := by
    rw [hpow 4, show -((4 : ℕ) : ℝ) / 4 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  have hh : n ^ (-1 / 2 : ℝ) = q ^ 2 := by
    rw [hpow 2]; norm_num
  have h14 : n ^ (1 / 4 : ℝ) = n * q ^ 3 := by
    rw [hpow 3, show (1 / 4 : ℝ) = 1 + -((3 : ℕ) : ℝ) / 4 by norm_num, Real.rpow_add hn0,
      Real.rpow_one]
  have hqq : q ^ 2 ≤ q := by nlinarith
  have hcq : cN n = Real.cosh q := rfl
  have hk2 : Real.cosh q ≤ 2 := by
    obtain ⟨-, -, -, -, h1, h2⟩ := constants_bounds hn
    rw [← hcq]; linarith
  have hk1 : 1 ≤ Real.cosh q := Real.one_le_cosh q
  have hE1 := Real.exp_pos q
  have hE2 := Real.exp_pos (-q)
  -- Taylor remainders
  set d1 := deriv φ y with hd1_def
  set d2 := iteratedDeriv 2 φ y with hd2_def
  have hM : ∀ z, |iteratedDeriv 3 φ z| ≤ c 4 := fun z => (hb z).2.2.2.2
  have hd1 : |d1| ≤ c 2 := by have := (hb y).2.2.1; rwa [iteratedDeriv_one] at this
  have hd2 : |d2| ≤ c 3 := (hb y).2.2.2.1
  set Rp := φ (y + q ^ 2) - φ y - q ^ 2 * d1 - (q ^ 2) ^ 2 / 2 * d2 with hRp_def
  set Rm := φ (y + -q ^ 2) - φ y - (-q ^ 2) * d1 - (-q ^ 2) ^ 2 / 2 * d2 with hRm_def
  have hRp : |Rp| ≤ c 4 * q ^ 6 / 6 := by
    have := taylor_two_bound hcd hM y (q ^ 2)
    rw [abs_of_nonneg (sq_nonneg q)] at this
    exact le_of_le_of_eq this (by ring)
  have hRm : |Rm| ≤ c 4 * q ^ 6 / 6 := by
    have := taylor_two_bound hcd hM y (-q ^ 2)
    rw [abs_neg, abs_of_nonneg (sq_nonneg q)] at this
    exact le_of_le_of_eq this (by ring)
  -- the decomposition of `𝒜_n φ - φ''/2`
  have key : AN n φ y - d2 / 2 = n / 2 * (Real.exp q * Rp + Real.exp (-q) * Rm) +
      n * q ^ 2 * (Real.sinh q - q) * d1 + (Real.cosh q - 1) / 2 * d2 := by
    unfold AN
    rw [hh, h14, hcq, Real.sinh_eq, Real.cosh_eq, sub_eq_add_neg y]
    simp only [hRp_def, hRm_def]
    linear_combination ((Real.exp q + Real.exp (-q)) / 4 * d2) * hq4
  have hT1 : |n / 2 * (Real.exp q * Rp + Real.exp (-q) * Rm)| ≤
      q ^ 2 * Real.cosh q * c 4 / 6 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < n / 2)]
    calc n / 2 * |Real.exp q * Rp + Real.exp (-q) * Rm|
        ≤ n / 2 * (Real.exp q * (c 4 * q ^ 6 / 6) + Real.exp (-q) * (c 4 * q ^ 6 / 6)) := by
          gcongr
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hE1, abs_of_pos hE2]
          gcongr
      _ = q ^ 2 * Real.cosh q * c 4 / 6 := by
          rw [Real.cosh_eq]
          linear_combination ((Real.exp q + Real.exp (-q)) * q ^ 2 * c 4 / 12) * hq4
  have hT2 : |n * q ^ 2 * (Real.sinh q - q) * d1| ≤ q * Real.cosh q * c 2 / 6 := by
    obtain ⟨hs0, hs1⟩ := sinh_sub_self_bounds hq0.le
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ n * q ^ 2 * (Real.sinh q - q))]
    calc n * q ^ 2 * (Real.sinh q - q) * |d1| ≤ n * q ^ 2 * (q ^ 3 / 6 * Real.cosh q) * c 2 := by
          gcongr
      _ = q * Real.cosh q * c 2 / 6 := by
          linear_combination (q * Real.cosh q * c 2 / 6) * hq4
  have hT3 : |(Real.cosh q - 1) / 2 * d2| ≤ q ^ 2 * Real.cosh q * c 3 / 4 := by
    have h := (sq_le_two_mul_cosh_sub_one hq0.le).2
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ (Real.cosh q - 1) / 2)]
    calc (Real.cosh q - 1) / 2 * |d2| ≤ (q ^ 2 * Real.cosh q / 4) * c 3 :=
          mul_le_mul (by linarith) hd2 (abs_nonneg _) (by positivity)
      _ = q ^ 2 * Real.cosh q * c 3 / 4 := by ring
  rw [hd2_def] at key
  rw [key, show n ^ (-1 / 4 : ℝ) = q from rfl]
  refine (abs_add_three _ _ _).trans ?_
  have e1 : q ^ 2 * Real.cosh q * c 4 ≤ q * 2 * c 4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul hqq hk2 (by linarith) hq0.le) hc4
  have e2 : q * Real.cosh q * c 2 ≤ q * 2 * c 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 hq0.le) hc2
  have e3 : q ^ 2 * Real.cosh q * c 3 ≤ q * 2 * c 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul hqq hk2 (by linarith) hq0.le) hc3
  have e4 : q * (c 2 + c 3 + c 4) ≤ q * C := mul_le_mul_of_nonneg_left hsum hq0.le
  nlinarith

/-- **Equation (3.18)**: for all real `u, v, θ`,
`(e^{θ/2} u - e^{-θ/2} v)² = 2(cosh θ - 1) u v + (u - v)(e^θ u - e^{-θ} v)`. -/
theorem identity_uv (u v θ : ℝ) :
    (Real.exp (θ / 2) * u - Real.exp (-θ / 2) * v) ^ 2 =
      2 * (Real.cosh θ - 1) * u * v + (u - v) * (Real.exp θ * u - Real.exp (-θ) * v) := by
  have ha : 0 < Real.exp (θ / 2) := Real.exp_pos _
  have h1 : Real.exp θ = Real.exp (θ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : Real.exp (-θ / 2) = (Real.exp (θ / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have h3 : Real.exp (-θ) = (Real.exp (θ / 2) ^ 2)⁻¹ := by
    rw [← h1, ← Real.exp_neg]
  rw [Real.cosh_eq, h1, h2, h3]
  field_simp
  ring

set_option linter.unusedVariables false in
/-- **Equation (3.20)**: for a symmetric `f : ℤ² → ℝ` and `w_θ(x₁,x₂) = e^{θ(x₁+x₂)}`,
`𝒬(w_θ f) = w_θ [𝒬^θ f + 4(cosh θ - 1) f + 2(cosh θ - 1) 𝟙_{|x₁-x₂|=1} f]`. -/
theorem tilt_identity (θ : ℝ) {f : ℤ → ℤ → ℝ} (hf : ∀ x₁ x₂, f x₁ x₂ = f x₂ x₁) (x₁ x₂ : ℤ) :
    inclGen (fun y₁ y₂ => Real.exp (θ * (y₁ + y₂)) * f y₁ y₂) x₁ x₂ =
      Real.exp (θ * (x₁ + x₂)) * (tiltedInclGen θ f x₁ x₂ + 4 * (Real.cosh θ - 1) * f x₁ x₂ +
        2 * (Real.cosh θ - 1) * (if |x₁ - x₂| = 1 then f x₁ x₂ else 0)) := by
  -- the symmetry of `f` is not needed for this identity
  have hc : Real.cosh θ = (Real.exp θ + Real.exp (-θ)) / 2 := Real.cosh_eq θ
  have he : Real.exp (-θ) = (Real.exp θ)⁻¹ := Real.exp_neg θ
  have hpos := Real.exp_pos θ
  unfold inclGen lap tiltedInclGen
  rw [hc, he]
  by_cases h1 : x₂ = x₁ + 1
  · subst h1
    simp only [show x₁ - (x₁ + 1) = -1 by ring, abs_neg, abs_one, show x₁ + 1 ≠ x₁ - 1 by omega,
      ↓reduceIte, add_zero]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_one, mul_add, mul_sub, Real.exp_add,
      Real.exp_sub, mul_one]
    field_simp
    ring
  · by_cases h2 : x₂ = x₁ - 1
    · subst h2
      simp only [show x₁ - (x₁ - 1) = 1 by ring, abs_one, show x₁ - 1 ≠ x₁ + 1 by omega,
        ↓reduceIte, add_zero]
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, mul_add, mul_sub, Real.exp_add,
        Real.exp_sub, mul_one]
      field_simp
      ring
    · have h3 : |x₁ - x₂| ≠ 1 := by
        intro h; rcases (abs_eq zero_le_one).1 h with h | h <;> omega
      simp only [h1, h2, h3, ↓reduceIte, add_zero, mul_zero]
      simp only [Int.cast_add, Int.cast_sub, Int.cast_one, mul_add, mul_sub, Real.exp_add,
        Real.exp_sub, mul_one]
      field_simp
      ring

set_option linter.unusedVariables false in
/-- **Equation (3.23)**: if `f(x₁,x₂) = g(x₂ - x₁)` with `g : ℤ → ℝ` even, then
`𝒬^θ f(x₁,x₂) = cosh θ · 𝓡 g(x₂ - x₁)`, where `𝓡` is the operator (3.24) (`chainGen`). -/
theorem tiltedInclGen_diff (θ : ℝ) {g : ℤ → ℝ} (hg : ∀ r, g (-r) = g r) (x₁ x₂ : ℤ) :
    tiltedInclGen θ (fun y₁ y₂ => g (y₂ - y₁)) x₁ x₂ = Real.cosh θ * chainGen g (x₂ - x₁) := by
  -- the parity of `g` is not needed for this identity
  have hc : Real.cosh θ = (Real.exp θ + Real.exp (-θ)) / 2 := Real.cosh_eq θ
  unfold tiltedInclGen chainGen
  rw [hc]
  by_cases h1 : x₂ = x₁ + 1
  · subst h1
    simp only [sub_self, add_sub_cancel_left, show x₁ + 1 ≠ x₁ - 1 by omega, ↓reduceIte,
      abs_one, add_zero]
    ring_nf
  · by_cases h2 : x₂ = x₁ - 1
    · subst h2
      simp only [sub_self, show x₁ - 1 ≠ x₁ + 1 by omega, ↓reduceIte, add_zero,
        show x₁ - 1 - x₁ = -1 by ring, abs_neg, abs_one]
      ring_nf
    · have h3 : |x₂ - x₁| ≠ 1 := by
        intro h; rcases abs_eq (zero_le_one) |>.1 h with h | h <;> omega
      simp only [h1, h2, h3, ↓reduceIte, add_zero]
      ring_nf

end QSSEPtoKPZ
