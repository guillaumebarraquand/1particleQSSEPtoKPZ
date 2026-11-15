/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorDefs
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Two facts on `κ = ρ ⋆ ρ` used in the proof of Proposition 6.2 (task G3)

* `kappa_riemann_tendsto`: the Riemann sums `(1/m) ∑_{r ∈ ℤ} κ(r/m)` converge to `∫ κ = 1`
  (Section 6.1, sentence before (6.6); used for `b_m → 1`). The proof uses that `κ` is Lipschitz
  (smooth with compact support): `|(1/m) ∑_r κ(r/m) - ∫ κ| ≤ 4 L / m`.
* `replKappaEps_sub_le`: the continuity of `ε ↦ κ_ε` in the uniform norm, in the quantitative form
  `|κ_{ε'}(x) - κ_ε(x)| ≤ (2L/ε'² + κ(0)/(ε ε')) (ε - ε')` for `0 < ε' ≤ ε` (used at the end
  of the proof of Proposition 6.2, where `ε_n = m n^{-1/2} → ε`).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace QSSEPtoKPZ

variable {ρ : ℝ → ℝ}

/-- `κ` is Lipschitz: `|κ(x) - κ(y)| ≤ L |x - y|` (smooth with compact support). -/
theorem IsMollifier.kappa_lipschitz (hρ : IsMollifier ρ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |kappa ρ x - kappa ρ y| ≤ L * |x - y| := by
  have hcs : HasCompactSupport (kappa ρ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun x hx => by
      apply hρ.kappa_eq_zero
      by_contra h
      exact hx (abs_le.1 (not_le.1 h).le)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hcs
    hρ.kappa_even_nonneg_smooth.2.2 (by simp)
  refine ⟨L, L.2, fun x y => ?_⟩
  have := hL.dist_le_mul x y
  simpa [Real.dist_eq] using this

/-- `0 ≤ κ_ε(x) ≤ κ(0)/ε` for `ε > 0`. -/
lemma replKappaEps_nonneg_le (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ kappaEps ρ ε x ∧ kappaEps ρ ε x ≤ kappa ρ 0 / ε :=
  ⟨div_nonneg (hρ.kappa_nonneg _) hε.le, div_le_div_of_nonneg_right (hρ.kappa_le _) hε.le⟩

/-- **Continuity of `ε ↦ κ_ε` in the uniform norm.** If `κ` is `L`-Lipschitz, then for
`0 < ε' ≤ ε` and all `x`, `|κ_{ε'}(x) - κ_ε(x)| ≤ (2L/ε'² + κ(0)/(ε ε')) (ε - ε')`.
Proof: `κ_{ε'}(x) - κ_ε(x) = (κ(x/ε') - κ(x/ε))/ε' + κ(x/ε)(1/ε' - 1/ε)`; the first term
vanishes for `|x| ≥ 2ε` (both points are outside `(-2, 2)`), and otherwise
`|x/ε' - x/ε| ≤ 2(ε - ε')/ε'`. -/
theorem replKappaEps_sub_le (hρ : IsMollifier ρ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, |kappa ρ x - kappa ρ y| ≤ L * |x - y|) {ε ε' : ℝ} (hε' : 0 < ε')
    (hεε : ε' ≤ ε) (x : ℝ) :
    |kappaEps ρ ε' x - kappaEps ρ ε x| ≤ (2 * L / ε' ^ 2 + kappa ρ 0 / (ε * ε')) * (ε - ε') := by
  have hε : 0 < ε := hε'.trans_le hεε
  have hd : 0 ≤ ε - ε' := sub_nonneg.2 hεε
  have e : kappaEps ρ ε' x - kappaEps ρ ε x =
      (kappa ρ (x / ε') - kappa ρ (x / ε)) / ε' + kappa ρ (x / ε) * ((ε - ε') / (ε * ε')) := by
    unfold kappaEps; field_simp; ring
  rw [e]
  have h1 : |(kappa ρ (x / ε') - kappa ρ (x / ε)) / ε'| ≤ 2 * L / ε' ^ 2 * (ε - ε') := by
    rw [abs_div, abs_of_pos hε', div_le_iff₀ hε']
    rcases le_or_gt (2 * ε) |x| with hx | hx
    · have hxe : 2 ≤ |x / ε| := by rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]; linarith
      have hxe' : 2 ≤ |x / ε'| := by
        rw [abs_div, abs_of_pos hε', le_div_iff₀ hε']; nlinarith
      rw [hρ.kappa_eq_zero hxe, hρ.kappa_eq_zero hxe', sub_zero, abs_zero]
      have : 0 ≤ 2 * L / ε' ^ 2 * (ε - ε') := by positivity
      nlinarith
    · have hxx : |x / ε' - x / ε| ≤ 2 * (ε - ε') / ε' := by
        have e2 : x / ε' - x / ε = x * (ε - ε') / (ε * ε') := by field_simp
        rw [e2, abs_div, abs_mul, abs_of_nonneg hd, abs_of_pos (mul_pos hε hε'),
          div_le_div_iff₀ (mul_pos hε hε') hε']
        have := mul_le_mul_of_nonneg_right hx.le hd
        nlinarith [mul_le_mul_of_nonneg_right this hε'.le]
      calc |kappa ρ (x / ε') - kappa ρ (x / ε)| ≤ L * |x / ε' - x / ε| := hL _ _
        _ ≤ L * (2 * (ε - ε') / ε') := mul_le_mul_of_nonneg_left hxx hL0
        _ = 2 * L / ε' ^ 2 * (ε - ε') * ε' := by field_simp
  have h2 : |kappa ρ (x / ε) * ((ε - ε') / (ε * ε'))| ≤ kappa ρ 0 / (ε * ε') * (ε - ε') := by
    rw [abs_mul, abs_of_nonneg (hρ.kappa_nonneg _), abs_of_nonneg (by positivity)]
    calc kappa ρ (x / ε) * ((ε - ε') / (ε * ε')) ≤ kappa ρ 0 * ((ε - ε') / (ε * ε')) :=
          mul_le_mul_of_nonneg_right (hρ.kappa_le _) (by positivity)
      _ = _ := by ring
  calc _ ≤ |(kappa ρ (x / ε') - kappa ρ (x / ε)) / ε'| +
        |kappa ρ (x / ε) * ((ε - ε') / (ε * ε'))| := abs_add_le _ _
    _ ≤ _ := by nlinarith [h1, h2]

/-- The Riemann sum `(1/m) ∑_{r ∈ ℤ} κ(r/m)` is within `4L/m` of `∫ κ = 1`, if `κ` is
`L`-Lipschitz and `m ≥ 1`: on each interval `[r/m, (r+1)/m]`, `-2m ≤ r < 2m`, the difference
between `κ(r/m)/m` and `∫_{r/m}^{(r+1)/m} κ` is at most `L/m²`, and the other terms vanish. -/
theorem kappa_riemann_sub_le (hρ : IsMollifier ρ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, |kappa ρ x - kappa ρ y| ≤ L * |x - y|) {m : ℕ} (hm : 1 ≤ m) :
    |1 / (m : ℝ) * ∑' r : ℤ, kappa ρ (r / m) - 1| ≤ 4 * L / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : Continuous (kappa ρ) := hρ.kappa_even_nonneg_smooth.2.2.continuous
  set a : ℕ → ℝ := fun k => ((k : ℝ) - 2 * m) / m with ha
  -- the series is a finite sum over `k < 4m`, `r = k - 2m`
  have hsum : ∑' r : ℤ, kappa ρ (r / m) = ∑ k ∈ Finset.range (4 * m), kappa ρ (a k) := by
    have hinj : Set.InjOn (fun k : ℕ => (k : ℤ) - 2 * m) (Finset.range (4 * m) : Set ℕ) :=
      fun k _ l _ h => by simpa using h
    rw [tsum_eq_sum (s := (Finset.range (4 * m)).image fun k : ℕ => (k : ℤ) - 2 * m),
      Finset.sum_image hinj]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [a]; push_cast; ring_nf
    · intro r hr
      apply hρ.kappa_div_eq_zero hm
      by_contra h
      apply hr
      rw [Finset.mem_image]
      refine ⟨(r + 2 * m).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := abs_lt.1 (not_le.1 h)
        omega
      · have := abs_lt.1 (not_le.1 h)
        omega
  -- `∫ κ = ∫_{a 0}^{a (4m)} κ`
  have hint : ∫ x, kappa ρ x = ∫ x in a 0..a (4 * m), kappa ρ x := by
    have ha0 : a 0 = -2 := by simp only [a]; field_simp; ring
    have ha4 : a (4 * m) = 2 := by simp only [a]; push_cast; field_simp; ring
    rw [ha0, ha4, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    apply hρ.kappa_eq_zero
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hsplit : ∫ x in a 0..a (4 * m), kappa ρ x =
      ∑ k ∈ Finset.range (4 * m), ∫ x in a k..a (k + 1), kappa ρ x :=
    (intervalIntegral.sum_integral_adjacent_intervals fun k _ =>
      hc.intervalIntegrable _ _).symm
  have hone : (1 : ℝ) = ∑ k ∈ Finset.range (4 * m), ∫ x in a k..a (k + 1), kappa ρ x := by
    rw [← hsplit, ← hint, hρ.kappa_support_integral.2]
  have hstep : ∀ k, a (k + 1) - a k = 1 / m := fun k => by
    simp only [a]; push_cast; field_simp; ring
  have hle : ∀ k, a k ≤ a (k + 1) := fun k => by
    have := hstep k; have : (0 : ℝ) < 1 / m := by positivity
    linarith
  have hterm : ∀ k, |1 / (m : ℝ) * kappa ρ (a k) - ∫ x in a k..a (k + 1), kappa ρ x| ≤
      L / m * (1 / m) := by
    intro k
    have e : 1 / (m : ℝ) * kappa ρ (a k) = ∫ x in a k..a (k + 1), kappa ρ (a k) := by
      rw [intervalIntegral.integral_const, hstep, smul_eq_mul]
    rw [e, ← intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k + 1))
      (C := L / m) (f := fun x => kappa ρ (a k) - kappa ρ x) fun x hx => by
        rw [Set.uIoc_of_le (hle k)] at hx
        rw [Real.norm_eq_abs]
        refine (hL _ _).trans ?_
        rw [div_eq_mul_one_div L]
        refine mul_le_mul_of_nonneg_left ?_ hL0
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1]), ← hstep k]
        linarith [hx.2]
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hle k)), hstep] at this
  have hdiff : 1 / (m : ℝ) * ∑ k ∈ Finset.range (4 * m), kappa ρ (a k) - 1 =
      ∑ k ∈ Finset.range (4 * m), (1 / (m : ℝ) * kappa ρ (a k) -
        ∫ x in a k..a (k + 1), kappa ρ x) := by
    rw [Finset.sum_sub_distrib, ← hone, Finset.mul_sum]
  rw [hsum, hdiff]
  calc |∑ k ∈ Finset.range (4 * m), (1 / (m : ℝ) * kappa ρ (a k) -
        ∫ x in a k..a (k + 1), kappa ρ x)|
      ≤ ∑ k ∈ Finset.range (4 * m), |1 / (m : ℝ) * kappa ρ (a k) -
        ∫ x in a k..a (k + 1), kappa ρ x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (4 * m), L / m * (1 / m) := Finset.sum_le_sum fun k _ => hterm k
    _ = 4 * L / m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp

/-- **Riemann sums of `κ`**: `(1/m) ∑_{r ∈ ℤ} κ(r/m) → ∫ κ = 1` as the integer `m → ∞`. -/
theorem kappa_riemann_tendsto (hρ : IsMollifier ρ) :
    Tendsto (fun m : ℕ => 1 / (m : ℝ) * ∑' r : ℤ, kappa ρ (r / m)) atTop (𝓝 1) := by
  obtain ⟨L, hL0, hL⟩ := hρ.kappa_lipschitz
  have hlim : Tendsto (fun m : ℕ => 4 * L / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs]
  exact kappa_riemann_sub_le hρ hL0 hL hm

end QSSEPtoKPZ
