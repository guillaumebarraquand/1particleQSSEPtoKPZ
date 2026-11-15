/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Kernel
public import QSSEPtoKPZ.SecondMoments.Semigroup
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# The kernel `p_t` as the unique bounded solution of `∂_t m = Δ m`, `m(0) = δ₀` (task D3)

* `rwKernel_eq_integral`: `p_t(x) = 𝟙_{x=0} + ∫_0^t Δp_s(x) ds` for all `t` (from
  `d/dt e^{tΔ} δ₀ = Δ e^{tΔ} δ₀`).
* `eq_rwKernel_of_integral_eq`: a function `m(t,x)`, continuous in `t`, bounded on `[0,∞) × ℤ`,
  with `m(t,x) = 𝟙_{x=0} + ∫_0^t Δm(s,x) ds` for `t ≥ 0`, is `p_t(x)`. Proof (Picard): the
  difference `d = m - p` satisfies `d(t,x) = ∫_0^t Δd(s,x) ds` and is bounded by `C` on
  `[0,T] × ℤ`; since `|Δf(x)| ≤ 4 sup|f|`, induction gives `|d(t,x)| ≤ C (4t)^n / n!` for all `n`.

This is used in Proposition 2.2 to identify `𝔼 P(t,x)` with `p_t(x)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped lp ENNReal Nat

noncomputable section

namespace QSSEPtoKPZ

/-- `|Δf(x)| ≤ 4c` when `|f| ≤ c` on `ℤ`. -/
lemma kernelU_abs_lap_le {f : ℤ → ℝ} {c : ℝ} (h : ∀ y, |f y| ≤ c) (x : ℤ) :
    |lap f x| ≤ 4 * c := by
  have h1 := h (x + 1); have h2 := h (x - 1); have h3 := h x
  unfold lap
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `t ↦ p_t(x)` is differentiable, with derivative `Δp_t(x)`. -/
lemma hasDerivAt_rwKernel (t : ℝ) (x : ℤ) :
    HasDerivAt (fun s => rwKernel s x) (lap (rwKernel t) x) t := by
  have h := HasFDerivAt.comp_hasDerivAt _ (coord x).hasFDerivAt
    (hasDerivAt_exp_smul_apply lapOp delta0 t)
  exact h

/-- `t ↦ p_t(x)` is continuous. -/
lemma continuous_rwKernel (x : ℤ) : Continuous fun s => rwKernel s x :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_rwKernel t x).continuousAt

/-- `p_0 = δ₀`. -/
lemma rwKernel_zero (x : ℤ) : rwKernel 0 x = if x = 0 then 1 else 0 := by
  simp only [rwKernel, exp_zero_smul]
  rfl

/-- `Δ` is linear: `Δ(f - g) = Δf - Δg`. -/
lemma kernelU_lap_sub (f g : ℤ → ℝ) (x : ℤ) : lap (fun y => f y - g y) x = lap f x - lap g x := by
  unfold lap; ring

/-- `s ↦ Δm(s, x)` is continuous when every `s ↦ m(s, y)` is. -/
lemma kernelU_continuous_lap {m : ℝ → ℤ → ℝ} (hm : ∀ y, Continuous fun s => m s y) (x : ℤ) :
    Continuous fun s => lap (m s) x := by
  unfold lap
  exact ((hm _).add (hm _)).sub (continuous_const.mul (hm _))

/-- **The integral equation of `p`**: `p_t(x) = 𝟙_{x=0} + ∫_0^t Δp_s(x) ds` for all `t`. -/
theorem rwKernel_eq_integral (t : ℝ) (x : ℤ) :
    rwKernel t x = (if x = 0 then 1 else 0) + ∫ s in (0 : ℝ)..t, lap (rwKernel s) x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_rwKernel s x)
    ((kernelU_continuous_lap (fun y => continuous_rwKernel y) x).intervalIntegrable _ _),
    rwKernel_zero]
  ring

/-- Picard iteration: if `|d| ≤ C` on `[0,T] × ℤ` and `d(t,x) = ∫_0^t Δd(s,x) ds` on `[0,T]`,
then `|d(t,x)| ≤ C (4t)^n / n!` on `[0,T] × ℤ`, for every `n`. -/
private lemma kernelU_iterate {d : ℝ → ℤ → ℝ} {T C : ℝ}
    (hC : ∀ s ∈ Set.Icc 0 T, ∀ x, |d s x| ≤ C)
    (heq : ∀ t ∈ Set.Icc 0 T, ∀ x, d t x = ∫ s in (0 : ℝ)..t, lap (d s) x) (n : ℕ) :
    ∀ t ∈ Set.Icc 0 T, ∀ x, |d t x| ≤ C * (4 * t) ^ n / n ! := by
  induction n with
  | zero => intro t ht x; simpa using hC t ht x
  | succ n ih =>
    intro t ht x
    rw [heq t ht x]
    have hb : ∀ s ∈ Set.Ioc 0 t, ‖lap (d s) x‖ ≤ 4 * (C * (4 * s) ^ n / n !) := by
      intro s hs
      rw [Real.norm_eq_abs]
      exact kernelU_abs_lap_le (ih s ⟨hs.1.le, hs.2.trans ht.2⟩) x
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht.1 (ae_of_all _ hb)
      ((by fun_prop : Continuous fun s : ℝ => 4 * (C * (4 * s) ^ n / n !)).intervalIntegrable _ _)
    rw [Real.norm_eq_abs] at hle
    refine hle.trans (le_of_eq ?_)
    have e : (fun s : ℝ => 4 * (C * (4 * s) ^ n / n !)) =
        fun s => (4 * C * 4 ^ n / n !) * s ^ n := by
      funext s; rw [mul_pow]; ring
    rw [e, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    push_cast
    have : (n ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- **Uniqueness**: if `|d| ≤ C` on `[0,T] × ℤ` and `d(t,x) = ∫_0^t Δd(s,x) ds` on `[0,T]`,
then `d = 0` on `[0,T] × ℤ`. -/
private lemma kernelU_eq_zero {d : ℝ → ℤ → ℝ} {T C : ℝ}
    (hC : ∀ s ∈ Set.Icc 0 T, ∀ x, |d s x| ≤ C)
    (heq : ∀ t ∈ Set.Icc 0 T, ∀ x, d t x = ∫ s in (0 : ℝ)..t, lap (d s) x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x, d t x = 0 := by
  intro t ht x
  have hlim : Tendsto (fun n : ℕ => C * ((4 * t) ^ n / n !)) atTop (𝓝 (C * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (4 * t)).const_mul C
  rw [mul_zero] at hlim
  have h : |d t x| ≤ 0 := ge_of_tendsto' hlim fun n => by
    rw [← mul_div_assoc]; exact kernelU_iterate hC heq n t ht x
  exact abs_nonpos_iff.1 h

/-- **Identification of `p_t`**: let `m(t,x)` be continuous in `t`, bounded on `[0,∞) × ℤ`, with
`m(t,x) = 𝟙_{x=0} + ∫_0^t Δm(s,x) ds` for all `t ≥ 0` and `x`. Then `m(t,x) = p_t(x)` for
`t ≥ 0`. -/
theorem eq_rwKernel_of_integral_eq {m : ℝ → ℤ → ℝ} {C : ℝ}
    (hc : ∀ x, Continuous fun s => m s x) (hC : ∀ s, 0 ≤ s → ∀ x, |m s x| ≤ C)
    (heq : ∀ t, 0 ≤ t → ∀ x,
      m t x = (if x = 0 then 1 else 0) + ∫ s in (0 : ℝ)..t, lap (m s) x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℤ) : m t x = rwKernel t x := by
  -- a bound for `p` on `[0, t]`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (continuous_exp_smul_apply lapOp delta0).continuousOn
  set d : ℝ → ℤ → ℝ := fun s y => m s y - rwKernel s y with hd
  have hdC : ∀ s ∈ Set.Icc 0 t, ∀ y, |d s y| ≤ C + M := by
    intro s hs y
    have h1 := hC s hs.1 y
    have h2 : |rwKernel s y| ≤ M := by
      have := lp.norm_apply_le_norm ENNReal.top_ne_zero
        (NormedSpace.exp (s • lapOp) delta0) y
      rw [Real.norm_eq_abs] at this
      exact this.trans (hM s hs)
    calc |d s y| ≤ |m s y| + |rwKernel s y| := abs_sub _ _
      _ ≤ C + M := add_le_add h1 h2
  have hdeq : ∀ s ∈ Set.Icc 0 t, ∀ y, d s y = ∫ r in (0 : ℝ)..s, lap (d r) y := by
    intro s hs y
    simp only [hd]
    rw [heq s hs.1 y, rwKernel_eq_integral s y]
    simp_rw [kernelU_lap_sub]
    rw [intervalIntegral.integral_sub ((kernelU_continuous_lap hc y).intervalIntegrable _ _)
      ((kernelU_continuous_lap (fun z => continuous_rwKernel z) y).intervalIntegrable _ _)]
    ring
  have := kernelU_eq_zero hdC hdeq t ⟨ht, le_rfl⟩ x
  simp only [hd] at this
  linarith

end QSSEPtoKPZ
