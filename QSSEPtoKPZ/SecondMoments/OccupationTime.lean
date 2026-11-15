/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import QSSEPtoKPZ.SecondMoments.Generator
public import QSSEPtoKPZ.SecondMoments.Semigroup
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lemma 4.1: occupation time of `{-1, 1}`

The article states Lemma 4.1 for the Markov chain `(R_v)` with generator `𝓡`:
`𝔼_r[∫_0^S 𝟙_{|R_v| = 1} dv] ≤ min{S, 1/4 + √S} ≤ (5/4) √S`.

As in `DEVIATIONS.md` (Section 4), the chain is replaced by its semigroup
`e^{v𝓡}` acting on `ℓ^∞(ℤ)`: `𝔼_r[𝟙_{|R_v| = 1}] = (e^{v𝓡} 𝟙_{|·| = 1})(r)`. The quantity
bounded below is therefore `∫_0^S (e^{v𝓡} 𝟙_{|·| = 1})(r) dv`. The Markov chain itself, and the
identity between the two expressions, are not formalized; they are not needed later, since
only the analytic objects enter the proof.

## Proof

The bound by `S` follows from `0 ≤ e^{v𝓡} 𝟙_{|·|=1} ≤ e^{v𝓡} 𝟏 = 𝟏` (positivity of the
semigroup, `Semigroup.lean`). For the bound `1/4 + √S`, the role of Dynkin's formula and
Jensen's inequality in the article is played by the comparison principle: with
`φ_S(r) = √(1 + r² + 4S)`, the function `w(S, r) = (φ_S(r) - max{|r|, 1}) / 2` is bounded in
`r`, satisfies `w(0, ·) ≥ 0` and `∂_S w ≥ 𝓡 w + 𝟙_{|·|=1}` (by (4.3) and the concavity of the
square root), while `V(S) = ∫_0^S e^{u𝓡} 𝟙_{|·|=1} du` satisfies `V' = 𝓡 V + 𝟙_{|·|=1}`,
`V(0) = 0`. Hence `V(S) ≤ w(S, ·) ≤ 1/4 + √S`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace QSSEPtoKPZ

/-- **Equation (4.3)**, first identity: for `f₁(r) = max{|r|, 1}`, `𝓡 f₁ = 2 · 𝟙_{|r| = 1}`. -/
theorem chainGen_max_abs_one (r : ℤ) :
    chainGen (fun s : ℤ => max |(s : ℝ)| 1) r = 2 * (if |r| = 1 then 1 else 0) := by
  have hpos : ∀ x : ℝ, 1 ≤ x → max |x| 1 = x := fun x hx => by
    rw [abs_of_nonneg (by linarith)]; exact max_eq_left hx
  have hneg : ∀ x : ℝ, x ≤ -1 → max |x| 1 = -x := fun x hx => by
    rw [abs_of_neg (by linarith)]; exact max_eq_left (by linarith)
  rcases (by omega : r ≤ -2 ∨ r = -1 ∨ r = 0 ∨ r = 1 ∨ 2 ≤ r) with h | rfl | rfl | rfl | h
  · have hr : |r| ≠ 1 := by rw [abs_of_neg (by omega)]; omega
    have h' : (r : ℝ) ≤ -2 := by exact_mod_cast h
    simp only [chainGen, hr, ite_false]
    push_cast
    rw [hneg _ (by linarith), hneg _ (by linarith), hneg _ (by linarith)]
    ring
  · norm_num [chainGen]
  · norm_num [chainGen]
  · norm_num [chainGen]
  · have hr : |r| ≠ 1 := by rw [abs_of_nonneg (by omega)]; omega
    have h' : (2 : ℝ) ≤ r := by exact_mod_cast h
    simp only [chainGen, hr, ite_false]
    push_cast
    rw [hpos _ (by linarith), hpos _ (by linarith), hpos _ (by linarith)]
    ring

/-- **Equation (4.3)**, second identity: for `f₂(r) = r²`, `𝓡 f₂ = 4 - 2 · 𝟙_{|r| = 1}`. -/
theorem chainGen_sq (r : ℤ) :
    chainGen (fun s : ℤ => (s : ℝ) ^ 2) r = 4 - 2 * (if |r| = 1 then 1 else 0) := by
  simp only [chainGen]
  split_ifs with h
  · have h2 : (r : ℝ) ^ 2 = 1 := by
      have : |r| ^ 2 = r ^ 2 := sq_abs r
      rw [h] at this
      exact_mod_cast this.symm
    push_cast
    linear_combination (-2) * h2
  · push_cast; ring

/-! ### The supersolution `w(S, r) = (√(1 + r² + 4S) - max{|r|, 1}) / 2` -/

/-- `φ_S(r) = √(1 + r² + 4S)`. -/
def sqrtFun (S : ℝ) (r : ℤ) : ℝ := Real.sqrt (1 + (r : ℝ) ^ 2 + 4 * S)

lemma one_le_sqrtFun {S : ℝ} (hS : 0 ≤ S) (r : ℤ) : 1 ≤ sqrtFun S r :=
  Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (r : ℝ)])

lemma sqrtFun_sq {S : ℝ} (hS : 0 ≤ S) (r : ℤ) : sqrtFun S r ^ 2 = 1 + (r : ℝ) ^ 2 + 4 * S :=
  Real.sq_sqrt (by positivity)

/-- For `S ≥ 0`: `0 ≤ (φ_S(r) - max{|r|, 1}) / 2 ≤ 1/4 + √S`. The upper bound is the last step
of the proof of Lemma 4.1: `√(1 + r² + 4S) ≤ max{|r|, 1} + 1/2 + 2√S`. -/
lemma supSol_bounds {S : ℝ} (hS : 0 ≤ S) (r : ℤ) :
    0 ≤ (sqrtFun S r - max |(r : ℝ)| 1) / 2 ∧
      (sqrtFun S r - max |(r : ℝ)| 1) / 2 ≤ 1 / 4 + Real.sqrt S := by
  set m := max |(r : ℝ)| 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hmr : (r : ℝ) ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
  have hm2 : m ^ 2 ≤ 1 + (r : ℝ) ^ 2 := by
    rcases eq_or_ne r 0 with rfl | hr
    · simp [hm]
    · have : (1 : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast Int.one_le_abs hr
      rw [hm, max_eq_left this, sq_abs]; linarith
  have hp := sqrtFun_sq hS r
  have hp0 : 0 ≤ sqrtFun S r := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt hS
  have hs0 := Real.sqrt_nonneg S
  constructor
  · nlinarith
  · have hle : sqrtFun S r ≤ m + 1 / 2 + 2 * Real.sqrt S := by
      rw [sqrtFun, ← Real.sqrt_sq (by positivity : 0 ≤ m + 1 / 2 + 2 * Real.sqrt S)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith

/-- `|√x - √y| ≤ |x - y| / 2` for `x, y ≥ 1`. -/
lemma abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / 2 := by
  have ha : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  have hb : 1 ≤ Real.sqrt y := Real.one_le_sqrt.2 hy
  have ha2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hb2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have e : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
    linear_combination -ha2 + hb2
  rw [e, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt x + Real.sqrt y)]
  nlinarith [mul_nonneg (abs_nonneg (Real.sqrt x - Real.sqrt y))
    (by linarith : (0 : ℝ) ≤ Real.sqrt x + Real.sqrt y - 2)]

/-- Second-order Taylor bound for the square root: for `x ≥ 1` and `x + 4h ≥ 1`,
`|(√(x + 4h) - √x)/2 - h/√x| ≤ h²`. -/
lemma sqrt_remainder {x h : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ x + 4 * h) :
    |(Real.sqrt (x + 4 * h) - Real.sqrt x) / 2 - h * (1 / Real.sqrt x)| ≤ h ^ 2 := by
  have ha : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  have hb : 1 ≤ Real.sqrt (x + 4 * h) := Real.one_le_sqrt.2 hy
  have ha2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hb2 : Real.sqrt (x + 4 * h) ^ 2 = x + 4 * h := Real.sq_sqrt (by linarith)
  set a := Real.sqrt x
  set b := Real.sqrt (x + 4 * h)
  have hh : h = (b ^ 2 - a ^ 2) / 4 := by linarith
  have e : (b - a) / 2 - h * (1 / a) = -((b - a) ^ 2 / (4 * a)) := by
    rw [hh]; field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity), hh]
  have h1 : 4 ≤ a * (a + b) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (b - a))]

/-- The supersolution `w(S, ·) = (φ_{S⁺} - max{|·|, 1}) / 2 ∈ ℓ^∞(ℤ)` (with `S⁺ = max{S, 0}`,
so that it is defined for all real `S`). -/
def supSol (S : ℝ) : BddZ :=
  ⟨fun r => (sqrtFun (max S 0) r - max |(r : ℝ)| 1) / 2, by
    refine memℓp_infty_iff.2 ⟨1 / 4 + Real.sqrt (max S 0), ?_⟩
    rintro _ ⟨r, rfl⟩
    have := supSol_bounds (le_max_right S 0) r
    dsimp only
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.sqrt_nonneg (max S 0)]⟩

@[simp] lemma supSol_apply (S : ℝ) (r : ℤ) :
    supSol S r = (sqrtFun (max S 0) r - max |(r : ℝ)| 1) / 2 := rfl

/-- The time derivative `∂_S w(S, ·) = 1/φ_{S⁺} ∈ ℓ^∞(ℤ)`. -/
def supSolDeriv (S : ℝ) : BddZ :=
  ⟨fun r => 1 / sqrtFun (max S 0) r, by
    refine memℓp_infty_iff.2 ⟨1, ?_⟩
    rintro _ ⟨r, rfl⟩
    have hp := one_le_sqrtFun (le_max_right S 0) r
    have h1 : 0 < 1 / sqrtFun (max S 0) r := by positivity
    have h2 : 1 / sqrtFun (max S 0) r ≤ 1 := by rw [div_le_one (by linarith)]; exact hp
    dsimp only
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith⟩

@[simp] lemma supSolDeriv_apply (S : ℝ) (r : ℤ) :
    supSolDeriv S r = 1 / sqrtFun (max S 0) r := rfl

lemma norm_supSol_sub_le (S S' : ℝ) : ‖supSol S - supSol S'‖ ≤ |S - S'| := by
  refine lp.norm_le_of_forall_le (abs_nonneg _) fun r => ?_
  rw [bddZ_sub_apply, supSol_apply, supSol_apply, Real.norm_eq_abs]
  have hr := sq_nonneg (r : ℝ)
  have key := abs_sqrt_sub_sqrt_le (x := 1 + (r : ℝ) ^ 2 + 4 * max S 0)
    (y := 1 + (r : ℝ) ^ 2 + 4 * max S' 0) (by nlinarith [le_max_right S 0])
    (by nlinarith [le_max_right S' 0])
  have hm := abs_max_sub_max_le_abs S S' 0
  have e1 : (1 + (r : ℝ) ^ 2 + 4 * max S 0) - (1 + (r : ℝ) ^ 2 + 4 * max S' 0) =
      4 * (max S 0 - max S' 0) := by ring
  rw [e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at key
  have e2 : (sqrtFun (max S 0) r - max |(r : ℝ)| 1) / 2 -
      (sqrtFun (max S' 0) r - max |(r : ℝ)| 1) / 2 =
      (sqrtFun (max S 0) r - sqrtFun (max S' 0) r) / 2 := by ring
  rw [e2, abs_div, abs_two]
  unfold sqrtFun
  linarith

lemma continuous_supSol : Continuous supSol :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun S S' => by
    rw [dist_eq_norm, Real.dist_eq]; simpa using norm_supSol_sub_le S S').continuous

/-- For `S > 0`, `S ↦ w(S, ·)` is differentiable in `ℓ^∞(ℤ)`, with derivative `1/φ_S`. -/
lemma hasDerivAt_supSol {S : ℝ} (hS : 0 < S) : HasDerivAt supSol (supSolDeriv S) S := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_
    (Asymptotics.isLittleO_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hS] with h hh
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
  have hh' := abs_lt.1 hh
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  refine lp.norm_le_of_forall_le (sq_nonneg h) fun r => ?_
  have h1 : max (S + h) 0 = S + h := max_eq_left (by linarith)
  have h2 : max S 0 = S := max_eq_left hS.le
  simp only [bddZ_sub_apply, bddZ_smul_apply, supSol_apply, supSolDeriv_apply, h1, h2,
    Real.norm_eq_abs]
  have hr := sq_nonneg (r : ℝ)
  have key := sqrt_remainder (x := 1 + (r : ℝ) ^ 2 + 4 * S) (h := h) (by nlinarith)
    (by nlinarith)
  have e : sqrtFun (S + h) r = Real.sqrt (1 + (r : ℝ) ^ 2 + 4 * S + 4 * h) := by
    rw [sqrtFun]; congr 1; ring
  rw [e, sqrtFun]
  convert key using 2
  ring

/-- **Supersolution inequality** `∂_S w ≥ 𝓡 w + 𝟙_{|·|=1}`, via `𝓡 φ_S ≤ 2/φ_S`: by the
concavity of the square root, `φ_S(r') ≤ φ_S(r) + (r'² - r²)/(2φ_S(r))`, so
`𝓡 φ_S(r) ≤ 𝓡 f₂(r)/(2φ_S(r)) ≤ 2/φ_S(r)` by (4.3). -/
lemma chainGen_sqrtFun_le {S : ℝ} (hS : 0 ≤ S) (r : ℤ) :
    chainGen (sqrtFun S) r ≤ 2 / sqrtFun S r := by
  have hp := one_le_sqrtFun hS r
  have key : ∀ s : ℤ, 2 * sqrtFun S r * sqrtFun S s ≤
      2 * sqrtFun S r ^ 2 + (s : ℝ) ^ 2 - (r : ℝ) ^ 2 := by
    intro s
    have h1 := sqrtFun_sq hS r
    have h2 := sqrtFun_sq hS s
    nlinarith [sq_nonneg (sqrtFun S r - sqrtFun S s)]
  have k1 := key (r + 1)
  have k2 := key (r - 1)
  have k0 := key 0
  push_cast at k1 k2 k0
  rw [le_div_iff₀ (by linarith)]
  unfold chainGen
  split_ifs with h
  · have hr2 : (r : ℝ) ^ 2 = 1 := by
      have : |r| ^ 2 = r ^ 2 := sq_abs r
      rw [h] at this
      exact_mod_cast this.symm
    nlinarith
  · nlinarith

lemma chainGen_supSol {S : ℝ} (hS : 0 ≤ S) (r : ℤ) :
    chainGen (supSol S) r = (chainGen (sqrtFun S) r - 2 * (if |r| = 1 then 1 else 0)) / 2 := by
  have : (⇑(supSol S) : ℤ → ℝ) = fun r => (sqrtFun S r - max |(r : ℝ)| 1) / 2 := by
    funext r; simp [max_eq_left hS]
  rw [this, ← chainGen_max_abs_one]
  unfold chainGen
  split_ifs <;> ring

/-- The expected time spent in `{-1, 1}` before time `S` by the chain started at `r`, in the
analytic form `∫_0^S (e^{v𝓡} 𝟙_{|·| = 1})(r) dv`. -/
def occupationTime (S : ℝ) (r : ℤ) : ℝ :=
  ∫ v in (0 : ℝ)..S, (NormedSpace.exp (v • chainOp) defectInd) r

/-! ### The occupation integral in `ℓ^∞(ℤ)` -/

lemma continuous_semigroup_defect :
    Continuous fun u : ℝ => NormedSpace.exp (u • chainOp) defectInd :=
  continuous_exp_smul_apply _ _

/-- `V(S) = ∫_0^S e^{u𝓡} 𝟙_{|·|=1} du ∈ ℓ^∞(ℤ)`. -/
def occVec (S : ℝ) : BddZ := ∫ u in (0 : ℝ)..S, NormedSpace.exp (u • chainOp) defectInd

lemma occVec_apply (S : ℝ) (r : ℤ) : occVec S r = occupationTime S r := by
  unfold occVec occupationTime
  rw [← coord_apply, ← (coord r).intervalIntegral_comp_comm
    (continuous_semigroup_defect.intervalIntegrable _ _)]
  rfl

lemma hasDerivAt_occVec (S : ℝ) :
    HasDerivAt occVec (NormedSpace.exp (S • chainOp) defectInd) S :=
  (continuous_semigroup_defect.integral_hasStrictDerivAt 0 S).hasDerivAt

lemma continuous_occVec : Continuous occVec :=
  continuous_iff_continuousAt.2 fun S => (hasDerivAt_occVec S).continuousAt

/-- `𝓡 V(S) = e^{S𝓡} 𝟙_{|·|=1} - 𝟙_{|·|=1}`, so that `V' = 𝓡 V + 𝟙_{|·|=1}`. -/
lemma chainOp_occVec (S : ℝ) :
    chainOp (occVec S) = NormedSpace.exp (S • chainOp) defectInd - defectInd := by
  unfold occVec
  rw [← chainOp.intervalIntegral_comp_comm (continuous_semigroup_defect.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_exp_smul_apply chainOp defectInd u)
      ((chainOp.continuous.comp continuous_semigroup_defect).intervalIntegrable _ _)]
  simp

/-- `0 ≤ (e^{v𝓡} 𝟙_{|·|=1})(r) ≤ 1` for `v ≥ 0`. -/
lemma semigroup_defect_mem {v : ℝ} (hv : 0 ≤ v) (r : ℤ) :
    0 ≤ NormedSpace.exp (v • chainOp) defectInd r ∧
      NormedSpace.exp (v • chainOp) defectInd r ≤ 1 := by
  have hh : IsNonneg defectInd := fun s => by
    rw [defectInd_apply]; split_ifs <;> norm_num
  have h1 : IsNonneg (1 - defectInd) := fun s => by
    rw [bddZ_sub_apply, defectInd_apply, lp.infty_coeFn_one]; split_ifs <;> norm_num
  refine ⟨posOp_exp_chainOp hv _ hh r, ?_⟩
  have := posOp_exp_chainOp hv _ h1 r
  rw [map_sub, exp_smul_chainOp_one, bddZ_sub_apply, lp.infty_coeFn_one] at this
  simpa using this

lemma occupationTime_le_self {S : ℝ} (hS : 0 ≤ S) (r : ℤ) : occupationTime S r ≤ S := by
  have hint : IntervalIntegrable (fun v : ℝ => (NormedSpace.exp (v • chainOp) defectInd) r)
      MeasureTheory.volume 0 S :=
    ((coord r).continuous.comp continuous_semigroup_defect).intervalIntegrable 0 S
  have := intervalIntegral.integral_mono_on hS hint intervalIntegrable_const
    (fun v hv => (semigroup_defect_mem hv.1 r).2)
  simpa [occupationTime] using this

/-- The comparison `V(S) ≤ w(S, ·)`, which gives the bound `1/4 + √S`. -/
lemma occupationTime_le_sqrt {S : ℝ} (hS : 0 ≤ S) (r : ℤ) :
    occupationTime S r ≤ 1 / 4 + Real.sqrt S := by
  have hsup : ∀ s ∈ Set.Ioo 0 S, IsNonneg
      ((supSolDeriv s - NormedSpace.exp (s • chainOp) defectInd) -
        chainOp (supSol s - occVec s)) := by
    intro s hs r
    have hs0 : 0 ≤ s := hs.1.le
    rw [map_sub, chainOp_occVec]
    simp only [bddZ_sub_apply, chainOp_apply, supSolDeriv_apply, max_eq_left hs0,
      defectInd_apply]
    rw [chainGen_supSol hs0]
    have h1 := chainGen_sqrtFun_le hs0 r
    have hp := one_le_sqrtFun hs0 r
    have e : 2 / sqrtFun s r = 2 * (1 / sqrtFun s r) := by ring
    linarith
  have h0 : IsNonneg (supSol 0 - occVec 0) := fun r => by
    simp only [occVec, intervalIntegral.integral_same, sub_zero]
    exact (supSol_bounds le_rfl r).1.trans_eq (by simp)
  have hnn := quasiPos_chainOp.comparison_nonneg hS
    (d := fun s => supSol s - occVec s)
    (d' := fun s => supSolDeriv s - NormedSpace.exp (s • chainOp) defectInd)
    ((continuous_supSol.sub continuous_occVec).continuousOn)
    (fun s hs => (hasDerivAt_supSol hs.1).sub (hasDerivAt_occVec s)) hsup h0 r
  simp only [bddZ_sub_apply, occVec_apply, supSol_apply, max_eq_left hS] at hnn
  linarith [(supSol_bounds hS r).2]

lemma min_le_five_quarters {S : ℝ} (hS : 0 ≤ S) :
    min S (1 / 4 + Real.sqrt S) ≤ 5 / 4 * Real.sqrt S := by
  have h1 := Real.sq_sqrt hS
  have h2 := Real.sqrt_nonneg S
  rcases le_total S 1 with h | h
  · have h3 : Real.sqrt S ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h
    exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left h3 h2])
  · have : 1 ≤ Real.sqrt S := Real.one_le_sqrt.2 h
    exact (min_le_right _ _).trans (by linarith)

/-- **Lemma 4.1**, equation (4.2), in analytic form. For all `r ∈ ℤ` and `S ≥ 0`, the function
`v ↦ (e^{v𝓡} 𝟙_{|·| = 1})(r)` is integrable on `[0, S]` and

  `∫_0^S (e^{v𝓡} 𝟙_{|·| = 1})(r) dv ≤ min{S, 1/4 + √S} ≤ (5/4) √S`.

(The integrability is stated so that the bound cannot hold because the integral of a
non-integrable function is `0` in Lean.) -/
theorem occupationTime_le {S : ℝ} (hS : 0 ≤ S) (r : ℤ) :
    IntervalIntegrable (fun v : ℝ => (NormedSpace.exp (v • chainOp) defectInd) r) volume 0 S ∧
      occupationTime S r ≤ min S (1 / 4 + Real.sqrt S) ∧
      min S (1 / 4 + Real.sqrt S) ≤ 5 / 4 * Real.sqrt S :=
  ⟨((coord r).continuous.comp continuous_semigroup_defect).intervalIntegrable 0 S,
    le_min (occupationTime_le_self hS r) (occupationTime_le_sqrt hS r), min_le_five_quarters hS⟩

end QSSEPtoKPZ
