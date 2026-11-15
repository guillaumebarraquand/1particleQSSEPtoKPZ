/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import QSSEPtoKPZ.SecondMoments.Generator
public import QSSEPtoKPZ.TiltedField.Constants
public import QSSEPtoKPZ.SecondMoments.Khasminskii
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Lemma 4.2: the function `u_n`

The article defines `u_n(t,r) = 𝔼_r[exp((λ_n/c_n) ∫_0^{n c_n t/2} 𝟙_{|R_v| = 1} dv)]`, equation
(4.4), and shows by the Feynman-Kac formula that it is
`exp(t (n c_n/2 𝓡 + n λ_n/2 𝟙_{|r| = 1})) 𝟏`. As in `DEVIATIONS.md` (Section 4),
this last expression is taken as the definition: `uN n t` is the exponential of the bounded
operator `t (n c_n/2 𝓡 + n λ_n/2 M)` on `ℓ^∞(ℤ)`, where `M` is the multiplication by
`𝟙_{|r| = 1}`, applied to the constant function `𝟏`. The probabilistic expression (4.4) and the
Feynman-Kac formula are not formalized.

The proofs use the tools of `QSSEPtoKPZ.SecondMoments.Khasminskii`: `A_n = genOp a b` with
`a = n c_n/2 > 0` and `b = n λ_n/2 ≥ 0`, and `b² ≤ a` by (3.2) (`generatorU_constants`).
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace QSSEPtoKPZ

/-- The multiplication by `𝟙_{|r| = 1}`, as a bounded operator on `ℓ^∞(ℤ)`. -/
def defectOp : BddZ →L[ℝ] BddZ := ContinuousLinearMap.mul ℝ BddZ defectInd

/-- The operator `(n c_n / 2) 𝓡 + (n λ_n / 2) 𝟙_{|r| = 1}` on `ℓ^∞(ℤ)`, the right-hand side of
(4.5). -/
def generatorU (n : ℝ) : BddZ →L[ℝ] BddZ :=
  (n * cN n / 2) • chainOp + (n * lambdaN n / 2) • defectOp

/-- The function `u_n(t, ·) = exp(t (n c_n/2 𝓡 + n λ_n/2 𝟙_{|r| = 1})) 𝟏 ∈ ℓ^∞(ℤ)` of
Section 4.1 (the article's definition (4.4) is its Feynman-Kac representation). -/
def uN (n t : ℝ) : BddZ := NormedSpace.exp (t • generatorU n) 1

lemma generatorU_eq (n : ℝ) : generatorU n = genOp (n * cN n / 2) (n * lambdaN n / 2) := rfl

/-- The constants of `A_n`, for `n ≥ 1`: with `a = n c_n/2` and `b = n λ_n/2`, one has `a > 0`,
`b ≥ 0` and `b² ≤ a` (from (3.2): `n λ_n² = a_n² ≤ c_n² ≤ 2 c_n`). -/
lemma generatorU_constants {n : ℝ} (hn : 1 ≤ n) :
    0 < n * cN n / 2 ∧ 0 ≤ n * lambdaN n / 2 ∧ (n * lambdaN n / 2) ^ 2 ≤ n * cN n / 2 := by
  obtain ⟨hl1, -, ha1, hac, hc1, hc2⟩ := constants_bounds hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hl0 : 0 ≤ lambdaN n := (Real.rpow_nonneg hn0.le _).trans hl1
  have hx : n ^ (1 / 2 : ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow n).symm
  have hsq := Real.sq_sqrt hn0.le
  have hsn := Real.sqrt_nonneg n
  have haN : aN n = Real.sqrt n * lambdaN n := by rw [aN, hx]
  rw [haN] at ha1 hac
  have hc0 : 0 < cN n := by linarith
  refine ⟨by positivity, by positivity, ?_⟩
  have h1 : (Real.sqrt n * lambdaN n) ^ 2 ≤ cN n ^ 2 := pow_le_pow_left₀ (by positivity) hac 2
  have h2 : n * lambdaN n ^ 2 ≤ 2 * cN n := by
    have : (Real.sqrt n * lambdaN n) ^ 2 = n * lambdaN n ^ 2 := by rw [mul_pow, hsq]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hn0.le]

/-- **Lemma 4.2 (1)**, evenness: `u_n(t, -r) = u_n(t, r)`. -/
theorem uN_neg (n t : ℝ) (r : ℤ) : uN n t (-r) = uN n t r := by
  rw [uN, generatorU_eq]
  exact exp_apply_neg (commute_smul_right' (commute_reflectOp_genOp _ _) t) reflectOp_one r

/-- **Lemma 4.2 (1)**, initial condition in (4.5): `u_n(0, ·) = 𝟏`. -/
theorem uN_zero (n : ℝ) : uN n 0 = 1 := by
  simp [uN]

/-- **Lemma 4.2 (1)**, equation (4.5), pointwise: for every `r ∈ ℤ` and `t ∈ ℝ`,

  `∂_t u_n(t,r) = (n c_n/2) 𝓡 u_n(t,·)(r) + (n λ_n/2) 𝟙_{|r| = 1} u_n(t,r)`. -/
theorem hasDerivAt_uN_apply (n t : ℝ) (r : ℤ) :
    HasDerivAt (fun s => uN n s r)
      (n * cN n / 2 * chainGen (uN n t) r +
        n * lambdaN n / 2 * (if |r| = 1 then 1 else 0) * uN n t r) t := by
  have := HasFDerivAt.comp_hasDerivAt t (coord r).hasFDerivAt
    (hasDerivAt_exp_smul_apply (generatorU n) 1 t)
  simp only [Function.comp_def, coord_apply] at this
  refine this.congr_deriv ?_
  simp only [uN]
  rw [generatorU_eq, genOp_apply]
  ring

/-- **Lemma 4.2 (1)**, regularity: `t ↦ u_n(t, ·)` is `C¹` from `ℝ` to `ℓ^∞(ℤ)`, its derivative
is `(n c_n/2 𝓡 + n λ_n/2 𝟙_{|r| = 1}) u_n(t, ·)` (equation (4.5) in `ℓ^∞(ℤ)`), and `u_n` and
`∂_t u_n` are bounded on `[0, T] × ℤ` for every `T`. -/
theorem uN_regularity (n : ℝ) :
    ContDiff ℝ 1 (uN n) ∧ (∀ t, HasDerivAt (uN n) (generatorU n (uN n t)) t) ∧
      ∀ T : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ r : ℤ,
        |uN n t r| ≤ C ∧ |generatorU n (uN n t) r| ≤ C := by
  have hd : ∀ t, HasDerivAt (uN n) (generatorU n (uN n t)) t :=
    fun t => hasDerivAt_exp_smul_apply (generatorU n) 1 t
  have hc : Continuous (uN n) := continuous_exp_smul_apply _ _
  have hc' : Continuous fun t => generatorU n (uN n t) := (generatorU n).continuous.comp hc
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun t => (hd t).differentiableAt, ?_⟩, hd, fun T => ?_⟩
  · rw [show deriv (uN n) = fun t => generatorU n (uN n t) from funext fun t => (hd t).deriv]
    exact hc'
  · have hK : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
    obtain ⟨C1, h1⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    obtain ⟨C2, h2⟩ := hK.exists_bound_of_continuousOn hc'.continuousOn
    refine ⟨max C1 C2, fun t ht r => ⟨?_, ?_⟩⟩
    · rw [← Real.norm_eq_abs]
      exact ((lp.norm_apply_le_norm ENNReal.top_ne_zero _ r).trans (h1 t ht)).trans
        (le_max_left _ _)
    · rw [← Real.norm_eq_abs]
      exact ((lp.norm_apply_le_norm ENNReal.top_ne_zero _ r).trans (h2 t ht)).trans
        (le_max_right _ _)

/-- **Lemma 4.2 (2)**, equation (4.6), first part: for `n ≥ 1`, `t ≥ 0` and `r ∈ ℤ`,
`1 ≤ u_n(t,r) ≤ 2^{1 + 16 t}`. -/
theorem uN_bounds {n t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) (r : ℤ) :
    1 ≤ uN n t r ∧ uN n t r ≤ (2 : ℝ) ^ (1 + 16 * t) := by
  obtain ⟨ha, hb, hab⟩ := generatorU_constants hn
  rw [uN, generatorU_eq]
  exact ⟨one_le_exp_genOp_one ha.le hb ht r, exp_genOp_one_le_two_rpow ha hb hab ht r⟩

/-- **Lemma 4.2 (2)**, equation (4.6), second part: for `n ≥ 1`, `0 ≤ t ≤ 1/16` and `r ∈ ℤ`,
`u_n(t,r) ≤ 1 + 4 √t`. -/
theorem uN_le_one_add_sqrt {n t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) (ht' : t ≤ 1 / 16) (r : ℤ) :
    uN n t r ≤ 1 + 4 * Real.sqrt t := by
  obtain ⟨ha, hb, hab⟩ := generatorU_constants hn
  rw [uN, generatorU_eq]
  exact exp_genOp_one_le_khasminskii ha hb hab ht ht' r

end QSSEPtoKPZ
