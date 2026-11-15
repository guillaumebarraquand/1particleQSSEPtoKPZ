/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import QSSEPtoKPZ.SecondMoments.OccupationTime

/-!
# Tools for Lemma 4.2: reflection, lower bound, Khas'minskii's bound

We work with the operator `a 𝓡 + b 𝟙_{|r|=1}` on `ℓ^∞(ℤ)` (`genOp a b`; the multiplication by
`𝟙_{|r|=1}` is written out), for constants `a > 0`, `b ≥ 0`, and with
`u(t) = e^{t(a 𝓡 + b 𝟙_{|r|=1})} 𝟏`. The operator `A_n` of Lemma 4.2 is `genOp (n c_n/2) (n λ_n/2)`.

* `exp_apply_neg`: an operator commuting with the reflection `J g(r) = g(-r)` has an
  exponential commuting with `J`; this gives the evenness of `u`.
* `one_le_exp_genOp_one`: `u(t) ≥ 1` for `t ≥ 0` (comparison principle applied to `u - 𝟏`).
* `exp_genOp_one_le_khasminskii`: if `b² ≤ a` and `0 ≤ t ≤ 1/16`, then `u(t) ≤ 1 + 4√t`. This is
  an analytic form of Khas'minskii's lemma: with `U = sup_{[0,t]} ‖u‖`, the comparison principle
  for `a𝓡` gives `u(s) ≤ 𝟏 + (bU/a) V(as)`, where `V(S) = ∫_0^S e^{v𝓡} 𝟙_{|·|=1} dv` is the
  expected occupation time of Lemma 4.1; then `U ≤ 1 + (5/4)√t U`.
* `exp_genOp_one_add_le`, `exp_genOp_one_le_two_rpow`: sub-multiplicativity
  `u(t+s) ≤ ‖u(s)‖ u(t)` (positivity of the semigroup), whence `u(t) ≤ 2^{1+16t}`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-! ### The reflection `J g(r) = g(-r)` -/

/-- The reflection `J g(r) = g(-r)`, as a linear map on `ℓ^∞(ℤ)`. -/
def reflectLinear : BddZ →ₗ[ℝ] BddZ where
  toFun g := ⟨fun r => g (-r), memℓp_infty_iff.2 ⟨‖g‖, by
    rintro _ ⟨r, rfl⟩; exact lp.norm_apply_le_norm ENNReal.top_ne_zero g (-r)⟩⟩
  map_add' f g := rfl
  map_smul' c g := rfl

/-- The reflection `J g(r) = g(-r)`, as a bounded operator on `ℓ^∞(ℤ)`. -/
def reflectOp : BddZ →L[ℝ] BddZ :=
  reflectLinear.mkContinuous 1 fun g => by
    refine lp.norm_le_of_forall_le (by positivity) fun r => ?_
    show ‖g (-r)‖ ≤ 1 * ‖g‖
    rw [one_mul]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero g (-r)

@[simp] lemma reflectOp_apply (g : BddZ) (r : ℤ) : reflectOp g r = g (-r) := rfl

lemma reflectOp_one : reflectOp 1 = 1 := by
  ext r; simp [lp.infty_coeFn_one]

/-- `Commute X Y` implies `Commute X (c • Y)` for operators on `ℓ^∞(ℤ)` (the general
`Commute.smul_right` needs an instance `SMulCommClass` not found here). -/
lemma commute_smul_right' {X Y : BddZ →L[ℝ] BddZ} (h : Commute X Y) (c : ℝ) :
    Commute X (c • Y) := by
  refine ContinuousLinearMap.ext fun g => ?_
  have := DFunLike.congr_fun h.eq g
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at this
  simp [ContinuousLinearMap.mul_def, this]

/-- The reflection commutes with `𝓡`. -/
lemma commute_reflectOp_chainOp : Commute reflectOp chainOp := by
  refine ContinuousLinearMap.ext fun g => lp.ext (funext fun r => ?_)
  show reflectOp (chainOp g) r = chainOp (reflectOp g) r
  simp only [reflectOp_apply, chainOp_apply, chainGen]
  rw [show -(r + 1) = -r - 1 by ring, show -(r - 1) = -r + 1 by ring, abs_neg, neg_zero]
  ring

/-- The reflection commutes with the multiplication by an even function `w`. -/
lemma commute_reflectOp_mul {w : BddZ} (hw : ∀ r, w (-r) = w r) :
    Commute reflectOp (ContinuousLinearMap.mul ℝ BddZ w) := by
  refine ContinuousLinearMap.ext fun g => lp.ext (funext fun r => ?_)
  show reflectOp (w * g) r = (w * reflectOp g) r
  simp [lp.infty_coeFn_mul, hw]

/-- If `A` commutes with the reflection and `g` is even, then `e^A g` is even. -/
lemma exp_apply_neg {A : BddZ →L[ℝ] BddZ} (hA : Commute reflectOp A) {g : BddZ}
    (hg : reflectOp g = g) (r : ℤ) : NormedSpace.exp A g (-r) = NormedSpace.exp A g r := by
  have h := DFunLike.congr_fun hA.exp_right.eq g
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hg] at h
  rw [← reflectOp_apply, h]

/-! ### The operator `a 𝓡 + b 𝟙_{|r|=1}` -/

/-- The operator `a 𝓡 + b 𝟙_{|r|=1}` on `ℓ^∞(ℤ)`. -/
def genOp (a b : ℝ) : BddZ →L[ℝ] BddZ :=
  a • chainOp + b • ContinuousLinearMap.mul ℝ BddZ defectInd

lemma genOp_apply (a b : ℝ) (g : BddZ) (r : ℤ) :
    genOp a b g r = a * chainGen g r + b * ((if |r| = 1 then 1 else 0) * g r) := by
  show (a • chainOp g + b • (defectInd * g)) r = _
  simp [lp.infty_coeFn_mul]

lemma isNonneg_defectInd : IsNonneg defectInd := fun r => by
  rw [defectInd_apply]; split_ifs <;> norm_num

lemma commute_reflectOp_genOp (a b : ℝ) : Commute reflectOp (genOp a b) :=
  (commute_smul_right' commute_reflectOp_chainOp a).add_right
    (commute_smul_right' (commute_reflectOp_mul fun r => by simp) b)

/-- The semigroup property `e^{(s+t)A} = e^{sA} e^{tA}`. -/
lemma exp_add_smul (A : BddZ →L[ℝ] BddZ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  have h : (s + t) • A = s • A + t • A := by module
  rw [h]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (commute_smul_right' (commute_smul_right' (Commute.refl A) s).symm t)
    ((NormedSpace.expSeries_radius_eq_top ℝ (BddZ →L[ℝ] BddZ)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ (BddZ →L[ℝ] BddZ)).symm ▸ edist_lt_top _ _)

/-- **Lower bound.** For `a, b ≥ 0` and `t ≥ 0`, `e^{t(a𝓡 + b𝟙_{|r|=1})} 𝟏 ≥ 𝟏`: the
difference `d = u - 𝟏` satisfies `d' - A d = A 𝟏 = b 𝟙_{|r|=1} ≥ 0` and `d(0) = 0`. -/
lemma one_le_exp_genOp_one {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (r : ℤ) :
    1 ≤ NormedSpace.exp (t • genOp a b) 1 r := by
  have hA : QuasiPos (genOp a b) := quasiPos_generator ha hb isNonneg_defectInd
  have hsup : ∀ s ∈ Set.Ioo 0 t, IsNonneg (genOp a b (NormedSpace.exp (s • genOp a b) 1) -
      genOp a b (NormedSpace.exp (s • genOp a b) 1 - 1)) := by
    intro s _ r
    rw [map_sub, sub_sub_cancel, genOp_apply, ← chainOp_apply, chainOp_one]
    have := isNonneg_defectInd r
    rw [defectInd_apply] at this
    simp only [lp.infty_coeFn_one, lp.coeFn_zero, Pi.zero_apply, mul_zero, Pi.one_apply,
      mul_one, zero_add]
    exact mul_nonneg hb this
  have := hA.comparison_nonneg ht (d := fun s => NormedSpace.exp (s • genOp a b) 1 - 1)
    (d' := fun s => genOp a b (NormedSpace.exp (s • genOp a b) 1))
    ((continuous_exp_smul_apply _ _).sub continuous_const).continuousOn
    (fun s _ => (hasDerivAt_exp_smul_apply _ _ s).sub_const 1) hsup
    (fun r => by simp) r
  simp only [bddZ_sub_apply, lp.infty_coeFn_one, Pi.one_apply] at this
  linarith

/-- `b √(a s) ≤ a √s` when `b² ≤ a`, `a, b, s ≥ 0`. -/
lemma mul_sqrt_le_of_sq_le {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ^ 2 ≤ a)
    (hs : 0 ≤ s) : b * Real.sqrt (a * s) ≤ a * Real.sqrt s := by
  rw [show a * Real.sqrt s = Real.sqrt (a ^ 2 * s) by
      rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha],
    show b * Real.sqrt (a * s) = Real.sqrt (b ^ 2 * (a * s)) by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb]]
  exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hab) ha) hs])

/-- **Khas'minskii's bound**, analytic form. Let `a > 0`, `b ≥ 0` with `b² ≤ a`, and
`0 ≤ t ≤ 1/16`. Then `e^{t(a𝓡 + b𝟙_{|r|=1})} 𝟏 ≤ 1 + 4√t` pointwise. -/
theorem exp_genOp_one_le_khasminskii {a b t : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : b ^ 2 ≤ a)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 16) (r : ℤ) :
    NormedSpace.exp (t • genOp a b) 1 r ≤ 1 + 4 * Real.sqrt t := by
  set u : ℝ → BddZ := fun s => NormedSpace.exp (s • genOp a b) 1 with hu
  have hcont : Continuous u := continuous_exp_smul_apply _ _
  have hlow : ∀ s, 0 ≤ s → ∀ r, 1 ≤ u s r := fun s hs r => one_le_exp_genOp_one ha.le hb hs r
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 ht)
    (continuous_norm.comp hcont).continuousOn
  set U := ‖u s0‖ with hUdef
  have hU0 : 0 ≤ U := norm_nonneg _
  have hU : ∀ s ∈ Set.Icc 0 t, ∀ r, u s r ≤ U := fun s hs r => by
    have h1 := lp.norm_apply_le_norm ENNReal.top_ne_zero (u s) r
    have h2 : ‖u s‖ ≤ U := isMaxOn_iff.1 hmax s hs
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (u s r)]
  -- comparison with `w(s) = 𝟏 + (bU/a) V(as)`
  have hcomp : ∀ s ∈ Set.Icc 0 t, ∀ r, u s r ≤ 1 + b * U / a * occupationTime (a * s) r := by
    intro s hs r
    set c := b * U / a with hc
    have hca : c * a = b * U := by rw [hc]; field_simp
    have hA : QuasiPos (a • chainOp) := quasiPos_chainOp.smul ha.le
    have hderiv : ∀ v, HasDerivAt (fun x => occVec (a * x))
        (a • NormedSpace.exp ((a * v) • chainOp) defectInd) v := fun v => by
      have := (hasDerivAt_occVec (a * v)).scomp v ((hasDerivAt_id v).const_mul a)
      simpa [Function.comp_def] using this
    have hsup : ∀ v ∈ Set.Ioo 0 s, IsNonneg
        ((c • (a • NormedSpace.exp ((a * v) • chainOp) defectInd) - genOp a b (u v)) -
          (a • chainOp) ((1 + c • occVec (a * v)) - u v)) := by
      intro v hv r'
      have hUv := hU v ⟨hv.1.le, hv.2.le.trans hs.2⟩ r'
      have hh := isNonneg_defectInd r'
      rw [defectInd_apply] at hh
      have key : c * a * (if |r'| = 1 then (1 : ℝ) else 0) =
          b * U * (if |r'| = 1 then (1 : ℝ) else 0) := by rw [hca]
      simp only [map_sub, map_add, map_smul, chainOp_one, chainOp_occVec, bddZ_sub_apply,
        bddZ_smul_apply, genOp_apply, smul_apply,
        chainOp_apply, defectInd_apply, smul_zero, zero_add]
      nlinarith [mul_nonneg (mul_nonneg hb hh) (sub_nonneg.2 hUv)]
    have hc2 : Continuous fun v => (1 + c • occVec (a * v)) - u v := by
      have := continuous_occVec; fun_prop
    have hd2 : ∀ v, HasDerivAt (fun v => (1 + c • occVec (a * v)) - u v)
        (c • (a • NormedSpace.exp ((a * v) • chainOp) defectInd) - genOp a b (u v)) v :=
      fun v => (((hderiv v).const_smul c).const_add 1).sub (hasDerivAt_exp_smul_apply _ _ v)
    have h0 : IsNonneg ((1 + c • occVec (a * 0)) - u 0) := by
      have e : (1 + c • occVec (a * 0)) - u 0 = 0 := by
        simp only [hu, mul_zero, occVec, intervalIntegral.integral_same, smul_zero, add_zero,
          exp_zero_smul, one_apply_eq_self, sub_self]
      rw [e]; intro r; simp
    have key := hA.comparison_nonneg hs.1 (d := fun v => (1 + c • occVec (a * v)) - u v)
      hc2.continuousOn (fun v _ => hd2 v) hsup h0 r
    simp only [bddZ_sub_apply, bddZ_add_apply, bddZ_smul_apply, occVec_apply,
      lp.infty_coeFn_one, Pi.one_apply] at key
    linarith
  -- the bound `u(s) ≤ 1 + (5/4)√t U` on `[0, t]`
  have hst : Real.sqrt t ≤ 1 / 4 := by nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  have hbound : ∀ s ∈ Set.Icc 0 t, ∀ r, u s r ≤ 1 + 5 / 4 * Real.sqrt t * U := by
    intro s hs r
    have has : 0 ≤ a * s := mul_nonneg ha.le hs.1
    obtain ⟨-, h1, h2⟩ := occupationTime_le has r
    have hk := mul_sqrt_le_of_sq_le ha.le hb hab hs.1
    have hst' : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hs.2
    have hc0 : 0 ≤ b * U / a := by positivity
    have e : b * U / a * (5 / 4 * Real.sqrt (a * s)) =
        5 / 4 * U * (b * Real.sqrt (a * s)) / a := by ring
    have h3 : b * U / a * occupationTime (a * s) r ≤ 5 / 4 * Real.sqrt t * U := by
      refine (mul_le_mul_of_nonneg_left (h1.trans h2) hc0).trans ?_
      rw [e, div_le_iff₀ ha]
      nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 5 / 4 * U),
        mul_le_mul_of_nonneg_left hst' (by positivity : (0 : ℝ) ≤ 5 / 4 * U * a)]
    linarith [hcomp s hs r]
  have hUle : U ≤ 1 + 5 / 4 * Real.sqrt t * U :=
    lp.norm_le_of_forall_le (by positivity) fun r => by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [hlow s0 hs0.1 r])]
      exact hbound s0 hs0 r
  have hU1 : U ≤ 16 / 5 := by nlinarith [mul_nonneg (sub_nonneg.2 hst) hU0]
  have := hbound t ⟨ht, le_rfl⟩ r
  nlinarith [mul_nonneg (Real.sqrt_nonneg t) (sub_nonneg.2 hU1)]

/-- **Sub-multiplicativity.** For `a, b ≥ 0` and `t ≥ 0`,
`u(t+s) = e^{tA} u(s) ≤ ‖u(s)‖ e^{tA} 𝟏 = ‖u(s)‖ u(t)` pointwise. -/
lemma exp_genOp_one_add_le {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (r : ℤ) :
    NormedSpace.exp ((t + s) • genOp a b) 1 r ≤
      ‖NormedSpace.exp (s • genOp a b) 1‖ * NormedSpace.exp (t • genOp a b) 1 r := by
  set v := NormedSpace.exp (s • genOp a b) 1
  have hnn : IsNonneg (‖v‖ • 1 - v) := fun r => by
    have h1 := lp.norm_apply_le_norm ENNReal.top_ne_zero v r
    rw [Real.norm_eq_abs] at h1
    simp only [bddZ_sub_apply, bddZ_smul_apply, lp.infty_coeFn_one, Pi.one_apply, mul_one]
    linarith [le_abs_self (v r)]
  have := posOp_exp_generator ha hb isNonneg_defectInd ht _ hnn r
  rw [exp_add_smul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  simp only [map_sub, map_smul, bddZ_sub_apply, bddZ_smul_apply] at this
  change 0 ≤ ‖v‖ * NormedSpace.exp (t • genOp a b) 1 r - NormedSpace.exp (t • genOp a b) v r
    at this
  linarith

/-- For `a > 0`, `b ≥ 0`, `b² ≤ a`, `k ∈ ℕ` and `0 ≤ t ≤ (k+1)/16`, `u(t) ≤ 2^{k+1}`. -/
lemma exp_genOp_one_le_two_pow {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : b ^ 2 ≤ a) (k : ℕ) :
    ∀ t : ℝ, 0 ≤ t → t ≤ (k + 1) / 16 → ∀ r, NormedSpace.exp (t • genOp a b) 1 r ≤ 2 ^ (k + 1) := by
  have hsmall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 16 → ∀ r, NormedSpace.exp (t • genOp a b) 1 r ≤ 2 :=
    fun t ht ht' r => (exp_genOp_one_le_khasminskii ha hb hab ht ht' r).trans
      (by nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t])
  induction k with
  | zero => intro t ht ht' r; simpa using hsmall t ht (by simpa using ht') r
  | succ k ih =>
    intro t ht ht' r
    rcases le_total t (1 / 16) with h | h
    · refine (hsmall t ht h r).trans ?_
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    · have hn : ‖NormedSpace.exp ((t - 1 / 16) • genOp a b) 1‖ ≤ 2 ^ (k + 1) :=
        lp.norm_le_of_forall_le (by positivity) fun r => by
          rw [Real.norm_eq_abs, abs_of_pos (by
            linarith [one_le_exp_genOp_one ha.le hb (by linarith : (0 : ℝ) ≤ t - 1 / 16) r])]
          exact ih _ (by linarith) (by push_cast at ht' ⊢; linarith) r
      have h1 := exp_genOp_one_add_le (s := t - 1 / 16) ha.le hb (by norm_num : (0 : ℝ) ≤ 1 / 16) r
      rw [show 1 / 16 + (t - 1 / 16) = t by ring] at h1
      refine h1.trans ?_
      calc _ ≤ 2 ^ (k + 1) * 2 := mul_le_mul hn (hsmall _ (by norm_num) le_rfl r)
              (by linarith [one_le_exp_genOp_one ha.le hb (by norm_num : (0 : ℝ) ≤ 1 / 16) r])
              (by positivity)
        _ = 2 ^ (k + 1 + 1) := by ring

/-- For `a > 0`, `b ≥ 0`, `b² ≤ a` and `t ≥ 0`, `u(t) ≤ 2^{1 + 16 t}`. -/
theorem exp_genOp_one_le_two_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : b ^ 2 ≤ a)
    (ht : 0 ≤ t) (r : ℤ) : NormedSpace.exp (t • genOp a b) 1 r ≤ (2 : ℝ) ^ (1 + 16 * t) := by
  set k := ⌊16 * t⌋₊
  have h1 : 16 * t < k + 1 := Nat.lt_floor_add_one _
  have h2 : (k : ℝ) ≤ 16 * t := Nat.floor_le (by positivity)
  refine (exp_genOp_one_le_two_pow ha hb hab k t ht (by linarith) r).trans ?_
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)

end QSSEPtoKPZ
