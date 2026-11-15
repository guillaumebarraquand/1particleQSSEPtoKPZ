/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import QSSEPtoKPZ.SecondMoments.Generator
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The mollifier of Section 6 and the kernel `k_m`

Section 6 of the article fixes once and for all an even nonnegative function `ρ ∈ C_c^∞(ℝ)`,
supported in `[-1, 1]`, with `∫ ρ = 1`, and sets `κ = ρ ⋆ ρ`. Section 6.1 defines, for an integer
`m ≥ 1`, equation (6.4),

  `b_m = (1/m) ∑_{r ∈ ℤ} π(r) κ(r/m)`,   `k_m(r) = κ(r/m) / (m b_m)`.

Here `ρ` is a parameter, and `IsMollifier ρ` collects the assumptions made on it.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace QSSEPtoKPZ

/-- The assumptions of Section 6 on the function `ρ`: smooth, even, nonnegative, vanishing
outside `[-1, 1]`, with integral `1`. -/
structure IsMollifier (ρ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  even : ∀ x, ρ (-x) = ρ x
  nonneg : ∀ x, 0 ≤ ρ x
  zero_of_one_lt : ∀ x, 1 < |x| → ρ x = 0
  integral_eq_one : ∫ x, ρ x = 1

/-- `κ = ρ ⋆ ρ`, i.e. `κ(x) = ∫ ρ(y) ρ(x - y) dy`. -/
def kappa (ρ : ℝ → ℝ) : ℝ → ℝ :=
  convolution ρ ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-! ### Auxiliary facts on `ρ` and `κ` -/

namespace IsMollifier

variable {ρ : ℝ → ℝ}

lemma continuous (hρ : IsMollifier ρ) : Continuous ρ := hρ.smooth.continuous

/-- `ρ(x) = 0` for `|x| ≥ 1` (at `x = ±1` by continuity). -/
lemma zero_of_one_le (hρ : IsMollifier ρ) {x : ℝ} (hx : 1 ≤ |x|) : ρ x = 0 := by
  have h1 : ρ 1 = 0 := by
    have hcl : IsClosed {y : ℝ | ρ y = 0} := isClosed_eq hρ.continuous continuous_const
    have hsub : Set.Ioi (1 : ℝ) ⊆ {y | ρ y = 0} := fun y hy => by
      rw [Set.mem_Ioi] at hy
      exact hρ.zero_of_one_lt y (by rw [abs_of_pos (by linarith)]; exact hy)
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioi] at this
    exact this Set.self_mem_Ici
  rcases lt_or_eq_of_le hx with h | h
  · exact hρ.zero_of_one_lt x h
  · rcases (abs_eq zero_le_one).1 h.symm with h' | h'
    · rw [h', h1]
    · rw [h', hρ.even, h1]

lemma hasCompactSupport_of {f : ℝ → ℝ} (hf : ∀ x, 1 < |x| → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => by
    apply hf
    by_contra h
    exact hx (abs_le.1 (not_lt.1 h))

lemma hasCompactSupport (hρ : IsMollifier ρ) : HasCompactSupport ρ :=
  hasCompactSupport_of hρ.zero_of_one_lt

lemma integrable (hρ : IsMollifier ρ) : Integrable ρ :=
  hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport

lemma integrable_sq (hρ : IsMollifier ρ) : Integrable (fun x => ρ x ^ 2) :=
  (hρ.continuous.pow 2).integrable_of_hasCompactSupport
    (hasCompactSupport_of fun x hx => by simp [hρ.zero_of_one_lt x hx])

lemma kappa_apply (x : ℝ) : kappa ρ x = ∫ y, ρ y * ρ (x - y) := by
  simp only [kappa, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma kappa_eq_zero (hρ : IsMollifier ρ) {x : ℝ} (hx : 2 ≤ |x|) : kappa ρ x = 0 := by
  rw [kappa_apply]
  have : ∀ y, ρ y * ρ (x - y) = 0 := by
    intro y
    by_cases hy : 1 ≤ |y|
    · rw [hρ.zero_of_one_le hy, zero_mul]
    · have h2 : 1 ≤ |x - y| := by
        have := abs_sub_abs_le_abs_sub x y
        push Not at hy
        linarith
      rw [hρ.zero_of_one_le h2, mul_zero]
  simp [this]

lemma kappa_nonneg (hρ : IsMollifier ρ) (x : ℝ) : 0 ≤ kappa ρ x := by
  rw [kappa_apply]
  exact integral_nonneg fun y => mul_nonneg (hρ.nonneg _) (hρ.nonneg _)

lemma kappa_zero_eq (hρ : IsMollifier ρ) : kappa ρ 0 = ∫ x, ρ x ^ 2 := by
  rw [kappa_apply]
  congr 1
  ext y
  rw [zero_sub, hρ.even, sq]

lemma kappa_zero_pos (hρ : IsMollifier ρ) : 0 < kappa ρ 0 := by
  rw [hρ.kappa_zero_eq]
  rcases (integral_nonneg (fun y => sq_nonneg (ρ y))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hae : (fun y => ρ y ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hρ.integrable_sq).1 h.symm
    have : ∫ y, ρ y = 0 := by
      rw [integral_congr_ae (g := 0) (hae.mono fun y hy => by simpa using hy)]
      simp
    rw [hρ.integral_eq_one] at this
    norm_num at this

lemma kappa_le (hρ : IsMollifier ρ) (x : ℝ) : kappa ρ x ≤ kappa ρ 0 := by
  have hsq := hρ.integrable_sq
  have hsq' : Integrable (fun y => ρ (x - y) ^ 2) := hsq.comp_sub_left x
  rw [hρ.kappa_zero_eq]
  calc kappa ρ x = ∫ y, ρ y * ρ (x - y) := kappa_apply x
    _ ≤ ∫ y, (ρ y ^ 2 + ρ (x - y) ^ 2) / 2 :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => mul_nonneg (hρ.nonneg _) (hρ.nonneg _))
          ((hsq.add hsq').div_const 2)
          (Filter.Eventually.of_forall fun y => by
            nlinarith [sq_nonneg (ρ y - ρ (x - y))])
    _ = ((∫ y, ρ y ^ 2) + ∫ y, ρ (x - y) ^ 2) / 2 := by
        rw [integral_div, integral_add hsq hsq']
    _ = ∫ y, ρ y ^ 2 := by
        rw [integral_sub_left_eq_self (fun y => ρ y ^ 2) volume x]
        ring

end IsMollifier

/-- **Section 6** (properties of `κ` stated before (6.1)): `κ` is even, nonnegative and smooth. -/
theorem IsMollifier.kappa_even_nonneg_smooth {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    (∀ x, kappa ρ (-x) = kappa ρ x) ∧ (∀ x, 0 ≤ kappa ρ x) ∧ ContDiff ℝ (⊤ : ℕ∞) (kappa ρ) := by
  refine ⟨fun x => ?_, hρ.kappa_nonneg, ?_⟩
  · rw [kappa_apply, kappa_apply, ← integral_neg_eq_self (fun y => ρ y * ρ (x - y)) volume]
    congr 1
    ext y
    rw [hρ.even, show -x - y = -(x - -y) by ring, hρ.even]
  · exact hρ.hasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hρ.smooth hρ.integrable.locallyIntegrable

/-- **Section 6** (properties of `κ`): `κ` is supported in `[-2, 2]`, in the precise form
`κ(x) = 0` for `|x| ≥ 2` (the value `0` at `±2` is used for `k_m(±2m) = 0`), and `∫ κ = 1`. -/
theorem IsMollifier.kappa_support_integral {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    (∀ x, 2 ≤ |x| → kappa ρ x = 0) ∧ ∫ x, kappa ρ x = 1 := by
  refine ⟨fun x hx => hρ.kappa_eq_zero hx, ?_⟩
  rw [kappa, integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ.integrable hρ.integrable]
  simp [hρ.integral_eq_one]

/-- **Section 6** (properties of `κ`): `‖κ‖_∞ = κ(0) = ‖ρ‖₂² > 0`. -/
theorem IsMollifier.kappa_le_kappa_zero {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    (∀ x, kappa ρ x ≤ kappa ρ 0) ∧ kappa ρ 0 = ∫ x, ρ x ^ 2 ∧ 0 < kappa ρ 0 := by
  exact ⟨hρ.kappa_le, hρ.kappa_zero_eq, hρ.kappa_zero_pos⟩

/-- `b_m = (1/m) ∑_{r ∈ ℤ} π(r) κ(r/m)`, equation (6.4). -/
def bM (ρ : ℝ → ℝ) (m : ℕ) : ℝ := 1 / m * ∑' r : ℤ, chainPi r * kappa ρ (r / m)

/-- `k_m(r) = κ(r/m) / (m b_m)`, equation (6.4). -/
def kM (ρ : ℝ → ℝ) (m : ℕ) (r : ℤ) : ℝ := kappa ρ (r / m) / (m * bM ρ m)

/-! ### Auxiliary facts on `π`, `b_m` and `k_m` -/

lemma chainPi_ge_one (r : ℤ) : 1 ≤ chainPi r := by
  unfold chainPi; split_ifs <;> norm_num

lemma chainPi_le_two (r : ℤ) : chainPi r ≤ 2 := by
  unfold chainPi; split_ifs <;> norm_num

lemma chainPi_nonneg (r : ℤ) : 0 ≤ chainPi r := by linarith [chainPi_ge_one r]

/-- A function on `ℤ` vanishing for `|r| ≥ N` is summable. -/
lemma summable_of_eq_zero_of_le_abs {f : ℤ → ℝ} (N : ℤ) (hf : ∀ r, N ≤ |r| → f r = 0) :
    Summable f :=
  summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun r hr => hf r (by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with h | h
    · exact le_abs.2 (Or.inr (by omega))
    · exact le_abs.2 (Or.inl (by omega)))

namespace IsMollifier

variable {ρ : ℝ → ℝ}

lemma kappa_div_eq_zero (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) {r : ℤ}
    (hr : 2 * (m : ℤ) ≤ |r|) : kappa ρ (r / m) = 0 := by
  apply hρ.kappa_eq_zero
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : 2 * (m : ℝ) ≤ |(r : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hr
  rw [abs_div, Nat.abs_cast, le_div_iff₀ hm']
  linarith

lemma summable_chainPi_mul_kappa (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun r : ℤ => chainPi r * kappa ρ (r / m)) :=
  summable_of_eq_zero_of_le_abs (2 * m) fun r hr => by
    rw [hρ.kappa_div_eq_zero hm hr, mul_zero]

lemma tsum_chainPi_mul_kappa_pos (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) :
    0 < ∑' r : ℤ, chainPi r * kappa ρ (r / m) := by
  have h0 : chainPi 0 = 2 := by norm_num [chainPi]
  calc (0 : ℝ) < chainPi 0 * kappa ρ ((0 : ℤ) / m) := by
        rw [h0, Int.cast_zero, zero_div]; linarith [hρ.kappa_zero_pos]
    _ ≤ _ := (hρ.summable_chainPi_mul_kappa hm).le_tsum 0 fun j _ =>
        mul_nonneg (chainPi_nonneg j) (hρ.kappa_nonneg _)

lemma bM_pos (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) : 0 < bM ρ m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold bM
  exact mul_pos (by positivity) (hρ.tsum_chainPi_mul_kappa_pos hm)

end IsMollifier

/-- **Section 6.1**, after (6.4): `k_m` is even, nonnegative, and vanishes when `|r| ≥ 2m`. -/
theorem IsMollifier.kM_props {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) :
    (∀ r, kM ρ m (-r) = kM ρ m r) ∧ (∀ r, 0 ≤ kM ρ m r) ∧
      ∀ r : ℤ, 2 * (m : ℤ) ≤ |r| → kM ρ m r = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨fun r => ?_, fun r => ?_, fun r hr => ?_⟩
  · simp only [kM]
    rw [Int.cast_neg, neg_div, hρ.kappa_even_nonneg_smooth.1]
  · exact div_nonneg (hρ.kappa_nonneg _) (mul_nonneg hm'.le (hρ.bM_pos hm).le)
  · simp only [kM]
    rw [hρ.kappa_div_eq_zero hm hr, zero_div]

/-- **Equation (6.5)**: `∑_{r ∈ ℤ} π(r) k_m(r) = 1` (the series is summable, since only finitely
many terms are nonzero). -/
theorem IsMollifier.tsum_chainPi_mul_kM {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun r : ℤ => chainPi r * kM ρ m r) ∧ ∑' r : ℤ, chainPi r * kM ρ m r = 1 := by
  have hb := hρ.bM_pos hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hS : ∑' r : ℤ, chainPi r * kappa ρ (r / m) = m * bM ρ m := by
    unfold bM
    rw [← mul_assoc, mul_one_div_cancel hm'.ne', one_mul]
  have hfun : (fun r : ℤ => chainPi r * kM ρ m r) =
      fun r => chainPi r * kappa ρ (r / m) / (m * bM ρ m) := by
    ext r
    simp only [kM]
    ring
  rw [hfun]
  refine ⟨(hρ.summable_chainPi_mul_kappa hm).div_const _, ?_⟩
  rw [tsum_div_const, hS, div_self (by positivity)]

/-- **Equation (6.6)**: `0 < inf_{m ≥ 1} b_m ≤ sup_{m ≥ 1} b_m < ∞`, in the form: there are
constants `0 < c ≤ C` with `c ≤ b_m ≤ C` for all `m ≥ 1`. (The article deduces it from
`b_m → ∫ κ = 1`; that convergence is not stated here.) -/
theorem IsMollifier.bM_bounds {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → c ≤ bM ρ m ∧ bM ρ m ≤ C := by
  have h0 := hρ.kappa_zero_pos
  obtain ⟨δ, hδ, hδκ⟩ : ∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → kappa ρ 0 / 2 ≤ kappa ρ x := by
    have hc : Continuous (kappa ρ) := hρ.kappa_even_nonneg_smooth.2.2.continuous
    obtain ⟨ε, hε, h⟩ :=
      Metric.continuousAt_iff.1 hc.continuousAt (kappa ρ 0 / 2) (by linarith)
    refine ⟨ε / 2, by linarith, fun x hx => ?_⟩
    have := h (x := x) (by rw [Real.dist_eq, sub_zero]; linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  refine ⟨δ * kappa ρ 0 / 2, 10 * kappa ρ 0, by positivity, fun m hm => ⟨?_, ?_⟩⟩
  · -- lower bound: the terms `0 ≤ r ≤ ⌊m δ⌋` are each at least `κ(0)/2`
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    set N := ⌊(m : ℝ) * δ⌋₊
    have hN : (m : ℝ) * δ < N + 1 := Nat.lt_floor_add_one _
    have hN' : (N : ℝ) ≤ m * δ := Nat.floor_le (by positivity)
    have hle : ∀ r ∈ Finset.Icc (0 : ℤ) N, kappa ρ 0 / 2 ≤ chainPi r * kappa ρ (r / m) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr.1
      have hrN : (r : ℝ) ≤ N := by exact_mod_cast hr.2
      have hk : kappa ρ 0 / 2 ≤ kappa ρ (r / m) := hδκ _ (by
        rw [abs_of_nonneg (div_nonneg hr0 hm'.le), div_le_iff₀ hm']
        linarith)
      have := chainPi_ge_one r
      nlinarith [hρ.kappa_nonneg ((r : ℝ) / m)]
    have hcard : (Finset.Icc (0 : ℤ) N).card = N + 1 := by rw [Int.card_Icc]; omega
    have hsum : ((N : ℝ) + 1) * (kappa ρ 0 / 2) ≤ ∑' r : ℤ, chainPi r * kappa ρ (r / m) :=
      calc ((N : ℝ) + 1) * (kappa ρ 0 / 2) = (Finset.Icc (0 : ℤ) N).card • (kappa ρ 0 / 2) := by
            rw [hcard, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ r ∈ Finset.Icc (0 : ℤ) N, chainPi r * kappa ρ (r / m) :=
            Finset.card_nsmul_le_sum _ _ _ hle
        _ ≤ _ := (hρ.summable_chainPi_mul_kappa hm).sum_le_tsum _ fun r _ =>
            mul_nonneg (chainPi_nonneg r) (hρ.kappa_nonneg _)
    unfold bM
    rw [one_div_mul_eq_div, le_div_iff₀ hm']
    have := mul_le_mul_of_nonneg_right hN.le (by linarith : (0 : ℝ) ≤ kappa ρ 0 / 2)
    nlinarith
  · -- upper bound: at most `4m + 1` nonzero terms, each at most `2 κ(0)`
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hle : ∀ r ∈ Finset.Icc (-(2 * m : ℤ)) (2 * m),
        chainPi r * kappa ρ (r / m) ≤ 2 * kappa ρ 0 := by
      intro r _
      have := chainPi_le_two r
      have := hρ.kappa_le (r / m)
      nlinarith [hρ.kappa_nonneg ((r : ℝ) / m)]
    have hcard : (Finset.Icc (-(2 * m : ℤ)) (2 * m)).card = 4 * m + 1 := by
      rw [Int.card_Icc]; omega
    have hS : ∑' r : ℤ, chainPi r * kappa ρ (r / m) ≤ (4 * m + 1) * (2 * kappa ρ 0) := by
      rw [tsum_eq_sum (s := Finset.Icc (-(2 * m : ℤ)) (2 * m)) fun r hr => ?_]
      · calc _ ≤ (Finset.Icc (-(2 * m : ℤ)) (2 * m)).card • (2 * kappa ρ 0) :=
              Finset.sum_le_card_nsmul _ _ _ hle
          _ = _ := by rw [hcard, nsmul_eq_mul]; push_cast; ring
      · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
        have : 2 * (m : ℤ) ≤ |r| := by
          rcases hr with h | h
          · exact le_abs.2 (Or.inr (by omega))
          · exact le_abs.2 (Or.inl (by omega))
        rw [hρ.kappa_div_eq_zero hm this, mul_zero]
    unfold bM
    rw [one_div_mul_eq_div, div_le_iff₀ hm']
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ m by exact_mod_cast hm) h0.le
    nlinarith

end QSSEPtoKPZ
