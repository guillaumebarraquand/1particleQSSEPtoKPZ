/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Stochastic Fubini, part 1: Riemann sums and kernel estimates (task K3)

Deterministic ingredients of the proof of (7.13) (`heatMild_isWeakMild`, file
`StochFubini.lean`). For `f` continuous, vanishing outside `[-R, R]`, `|f| ≤ M`:

* `stochFub_riemann`: the Riemann sums `∑_{k ≤ n} Δ φ(a_k)`, `a_k = -R + kΔ`, `Δ = 2R/(n+1)`,
  of a continuous function `φ` vanishing outside `[-R,R]` tend to `∫ φ`.
* `stochFubSum f R r n y = ∑_k Δ f(a_k) g_r(a_k - y)`, the Riemann sum of
  `(g_r ⋆ f)(y) = heatConv r f y`; it converges pointwise (`stochFubSum_tendsto`), is bounded by
  `2RM (2πr)^{-1/2}` (`stochFubSum_abs_le`) and satisfies the `L²(dy)` bound
  `∫ (∑_k Δ f(a_k) g_r(a_k - y))² dy ≤ (2RM)² (4πr)^{-1/2}` (`stochFubSum_sq_integral_le`,
  by Cauchy–Schwarz), which is integrable in `r` near `0`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The grid point `a_k = -R + k Δ`, `Δ = 2R/(n+1)`, of the Riemann sums of `stochFub_riemann`
(`a_0 = -R`, `a_{n+1} = R`). -/
def stochFubPt (R : ℝ) (n k : ℕ) : ℝ := -R + k * (2 * R / (n + 1))

/-- A function vanishing outside `[-R, R]` has compact support. -/
theorem stochFub_hasCompactSupport {φ : ℝ → ℝ} {R : ℝ} (hsupp : ∀ x, R ≤ |x| → φ x = 0) :
    HasCompactSupport φ := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun x hx => hsupp x ?_
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
  exact hx.le

/-- **Riemann sums.** For `φ` continuous and vanishing outside `[-R, R]`,
`∑_{k=0}^{n} Δ φ(-R + kΔ) → ∫ φ`, `Δ = 2R/(n+1)`. -/
theorem stochFub_riemann {φ : ℝ → ℝ} (hφ : Continuous φ) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ x, R ≤ |x| → φ x = 0) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), 2 * R / (n + 1) * φ (stochFubPt R n k))
      atTop (𝓝 (∫ x, φ x)) := by
  have huc := (stochFub_hasCompactSupport hsupp).uniformContinuous_of_continuous hφ
  have hint : ∫ x, φ x = ∫ x in (-R)..R, φ x := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    apply hsupp
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hint, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc (ε / (4 * R)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / δ)
  refine ⟨N, fun n hn => ?_⟩
  set Δ := 2 * R / ((n : ℝ) + 1) with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔδ : Δ < δ := by
    rw [hΔ, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hpt : ∀ k : ℕ, stochFubPt R n (k + 1) = stochFubPt R n k + Δ := by
    intro k; simp only [stochFubPt, hΔ]; push_cast; ring
  have h0 : stochFubPt R n 0 = -R := by simp [stochFubPt]
  have hN' : stochFubPt R n (n + 1) = R := by
    simp only [stochFubPt]; push_cast; field_simp; ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ)
    (a := stochFubPt R n) (n := n + 1) (fun k _ => hφ.intervalIntegrable _ _)
  rw [h0, hN'] at hsum
  rw [← hsum, dist_eq_norm, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (n + 1), ‖Δ * φ (stochFubPt R n k) -
      ∫ x in stochFubPt R n k..stochFubPt R n (k + 1), φ x‖ ≤ ε / (4 * R) * Δ := by
    intro k _
    have e : Δ * φ (stochFubPt R n k) =
        ∫ _ in stochFubPt R n k..stochFubPt R n (k + 1), φ (stochFubPt R n k) := by
      rw [intervalIntegral.integral_const, hpt, smul_eq_mul]; ring
    rw [e, ← intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := stochFubPt R n k)
      (b := stochFubPt R n (k + 1)) (C := ε / (4 * R))
      (f := fun x => φ (stochFubPt R n k) - φ x) ?_
    · have hb : stochFubPt R n (k + 1) - stochFubPt R n k = Δ := by rw [hpt]; ring
      rwa [hb, abs_of_pos hΔpos] at this
    intro x hx
    rw [hpt, Set.uIoc_of_le (by linarith)] at hx
    have := hδε (a := stochFubPt R n k) (b := x) (by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2])
    rw [Real.dist_eq] at this
    exact this.le
  calc _ ≤ ∑ k ∈ Finset.range (n + 1), ε / (4 * R) * Δ := norm_sum_le_of_le _ hterm
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hΔ]; push_cast; field_simp; ring
    _ < ε := half_lt_self hε

/-- `g_r(x) ≤ (2πr)^{-1/2}`. -/
theorem stochFub_heatKernel_le (r x : ℝ) : heatKernel r x ≤ 1 / Real.sqrt (2 * Real.pi * r) := by
  unfold heatKernel
  rcases le_or_gt r 0 with h | h
  · rw [Real.sqrt_eq_zero'.2 (by nlinarith [Real.pi_pos]), div_zero, div_zero]
  · gcongr
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x]) (by linarith)

/-- `g_r(x - y) = g_r(y - x)`. -/
theorem stochFub_heatKernel_symm (r x y : ℝ) : heatKernel r (x - y) = heatKernel r (y - x) := by
  unfold heatKernel; rw [← neg_sub, neg_sq]

/-- `x ↦ g_r(x)` is continuous. -/
theorem stochFub_continuous_heatKernel (r : ℝ) : Continuous (heatKernel r) := by
  unfold heatKernel; fun_prop

/-- `(r, x) ↦ g_r(x)` is measurable. -/
theorem stochFub_measurable_heatKernel : Measurable (fun p : ℝ × ℝ => heatKernel p.1 p.2) := by
  unfold heatKernel; fun_prop

/-- The Riemann sum `∑_{k=0}^{n} Δ f(a_k) g_r(a_k - y)` of `(g_r ⋆ f)(y)`. -/
def stochFubSum (f : ℝ → ℝ) (R r : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    2 * R / (n + 1) * f (stochFubPt R n k) * heatKernel r (stochFubPt R n k - y)

/-- The Riemann sums of `g_r ⋆ f` converge pointwise. -/
theorem stochFubSum_tendsto {f : ℝ → ℝ} (hf : Continuous f) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ x, R ≤ |x| → f x = 0) (r y : ℝ) :
    Tendsto (fun n => stochFubSum f R r n y) atTop (𝓝 (heatConv r f y)) := by
  have hc : Continuous (fun x => heatKernel r (y - x) * f x) :=
    ((stochFub_continuous_heatKernel r).comp (continuous_const.sub continuous_id)).mul hf
  have := stochFub_riemann hc hR (fun x hx => by simp [hsupp x hx])
  have e : heatConv r f y = ∫ x, heatKernel r (y - x) * f x := rfl
  rw [e]
  convert this using 2 with n
  unfold stochFubSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stochFub_heatKernel_symm]; ring

/-- The uniform bound `|∑_k Δ f(a_k) g_r(a_k - y)| ≤ 2RM (2πr)^{-1/2}`. -/
theorem stochFubSum_abs_le {f : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M) {R : ℝ} (hR : 0 < R)
    {r : ℝ} (n : ℕ) (y : ℝ) :
    |stochFubSum f R r n y| ≤ 2 * R * M / Real.sqrt (2 * Real.pi * r) := by
  unfold stochFubSum
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc _ ≤ ∑ k ∈ Finset.range (n + 1),
        2 * R / (n + 1) * M * (1 / Real.sqrt (2 * Real.pi * r)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * R / ((n : ℝ) + 1)),
          abs_of_nonneg (heatKernel_nonneg _ _)]
        gcongr <;> first | exact hM _ | exact stochFub_heatKernel_le _ _ |
          exact heatKernel_nonneg _ _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp

/-- `∫ g_r(a - y)² dy = (4πr)^{-1/2}`, with integrability. -/
theorem stochFub_heatKernel_sq_integral_sub {r : ℝ} (hr : 0 < r) (a : ℝ) :
    Integrable (fun y => heatKernel r (a - y) ^ 2) ∧
      ∫ y, heatKernel r (a - y) ^ 2 = 1 / Real.sqrt (4 * Real.pi * r) := by
  obtain ⟨hi, h1⟩ := heatKernel_sq_integral hr
  refine ⟨hi.comp_sub_left a, ?_⟩
  rw [integral_sub_left_eq_self (fun x => heatKernel r x ^ 2) volume a, h1]

/-- **The `L²(dy)` bound** (Cauchy–Schwarz):
`∫ (∑_k Δ f(a_k) g_r(a_k - y))² dy ≤ (2RM)² (4πr)^{-1/2}`, with integrability. -/
theorem stochFubSum_sq_integral_le {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Integrable (fun y => stochFubSum f R r n y ^ 2) ∧
      ∫ y, stochFubSum f R r n y ^ 2 ≤ (2 * R * M) ^ 2 / Real.sqrt (4 * Real.pi * r) := by
  set c : ℕ → ℝ := fun k => 2 * R / (n + 1) * f (stochFubPt R n k) with hc
  set I := Finset.range (n + 1)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hcs : ∑ k ∈ I, |c k| ≤ 2 * R * M := by
    calc ∑ k ∈ I, |c k| ≤ ∑ k ∈ I, 2 * R / (n + 1) * M := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [hc, abs_mul, abs_of_pos (by positivity : 0 < 2 * R / ((n : ℝ) + 1))]
          gcongr; exact hM _
      _ = 2 * R * M := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
  set Φ : ℝ → ℝ := fun y => ∑ k ∈ I, (∑ j ∈ I, |c j|) * |c k| *
    heatKernel r (stochFubPt R n k - y) ^ 2 with hΦ
  have hpt : ∀ y, stochFubSum f R r n y ^ 2 ≤ Φ y := by
    intro y
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul I
      (r := fun k => c k * heatKernel r (stochFubPt R n k - y)) (f := fun k => |c k|)
      (g := fun k => |c k| * heatKernel r (stochFubPt R n k - y) ^ 2)
      (fun k _ => abs_nonneg _) (fun k _ => by positivity)
      (fun k _ => le_of_eq (by rw [mul_pow, ← sq_abs (c k)]; ring))
    calc stochFubSum f R r n y ^ 2 =
          (∑ i ∈ I, c i * heatKernel r (stochFubPt R n i - y)) ^ 2 := by
          simp only [stochFubSum, hc, I]
      _ ≤ _ := h
      _ = Φ y := by
          simp only [hΦ, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hΦi : Integrable Φ := integrable_finsetSum _ fun k _ =>
    (stochFub_heatKernel_sq_integral_sub hr _).1.const_mul _
  have hΦint : ∫ y, Φ y = (∑ j ∈ I, |c j|) ^ 2 / Real.sqrt (4 * Real.pi * r) := by
    rw [integral_finsetSum _ fun k _ => (stochFub_heatKernel_sq_integral_sub hr _).1.const_mul _]
    simp_rw [integral_const_mul, (stochFub_heatKernel_sq_integral_sub hr _).2]
    rw [sq, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hSm : Continuous (fun y => stochFubSum f R r n y ^ 2) := by
    unfold stochFubSum
    have := stochFub_continuous_heatKernel r
    fun_prop
  have hSi : Integrable (fun y => stochFubSum f R r n y ^ 2) :=
    hΦi.mono' hSm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt y)
  refine ⟨hSi, (integral_mono hSi hΦi hpt).trans ?_⟩
  rw [hΦint]
  gcongr

/-- `∫ C g_s(y)² dy = C (4πs)^{-1/2}`, as a lower integral. -/
theorem stochFub_lintegral_heatKernel_sq {s : ℝ} (hs : 0 < s) {C : ℝ} (hC : 0 ≤ C) :
    ∫⁻ y, ENNReal.ofReal (C * heatKernel s y ^ 2) =
      ENNReal.ofReal (C / Real.sqrt (4 * Real.pi * s)) := by
  obtain ⟨hi, h1⟩ := heatKernel_sq_integral hs
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul C)
    (ae_of_all _ fun _ => by positivity), integral_const_mul, h1, mul_one_div]

/-- `(s, y) ↦ (g_{t-s} ⋆ f)(y)` is measurable. -/
theorem stochFub_measurable_heatConv {f : ℝ → ℝ} (hf : Measurable f) (t : ℝ) :
    Measurable (fun q : ℝ × ℝ => heatConv (t - q.1) f q.2) := by
  have hm : StronglyMeasurable
      (fun p : (ℝ × ℝ) × ℝ => heatKernel (t - p.1.1) (p.1.2 - p.2) * f p.2) := by
    apply Measurable.stronglyMeasurable
    unfold heatKernel
    fun_prop
  exact hm.integral_prod_right'.measurable

/-- `(s, y) ↦ ∑_k Δ f(a_k) g_{t-s}(a_k - y)` is measurable. -/
theorem stochFub_measurable_sum {f : ℝ → ℝ} (R t : ℝ) (n : ℕ) :
    Measurable (fun q : ℝ × ℝ => stochFubSum f R (t - q.1) n q.2) := by
  unfold stochFubSum
  refine Finset.measurable_sum _ fun k _ => measurable_const.mul ?_
  unfold heatKernel
  fun_prop

end QSSEPtoKPZ
