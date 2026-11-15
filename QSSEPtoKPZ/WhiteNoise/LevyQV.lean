/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.LevyAux

/-!
# Lévy's characterization: the second moment of a discrete quadratic variation (task G7a)

Let `M` be a continuous `L²` martingale, `p_0 ≤ p_1 ≤ ⋯` times, and assume
`|M_{p_k} - M_{p_0}| ≤ R` for every `k`. Then the discrete quadratic variation
`Q_n = ∑_{k < n} (M_{p_{k+1}} - M_{p_k})²` satisfies `𝔼 Q_n² ≤ 6 R⁴`
(`IsCL2Mart.levy_integral_qv_sq_le`).

Proof. Write `y_k = M_{p_k} - M_{p_0}` and `Q_k = ∑_{j<k} (y_{j+1} - y_j)²`. For bounded
`𝓕_{p_k}`-measurable `η`, `𝔼[η (y_{k+1} - y_k)²] = 𝔼[η (y_{k+1}² - y_k²)]` (martingale
increments are orthogonal to `η y_k`). Hence `𝔼 Q_n = 𝔼 y_n² ≤ R²` and, since
`Q_{k+1}² - Q_k² = 2 Q_k (y_{k+1} - y_k)² + (y_{k+1} - y_k)⁴` with `(y_{k+1} - y_k)² ≤ 4R²`,
`𝔼 Q_n² ≤ 𝔼[2 ∑_k Q_k (y_{k+1}² - y_k²) + 4 R² Q_n] ≤ 6 R² 𝔼 Q_n`, by Abel summation
`∑_k Q_k (y_{k+1}² - y_k²) = Q_n y_n² - ∑_k (y_{k+1} - y_k)² y_{k+1}² ≤ R² Q_n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Abel summation for the discrete quadratic variation. -/
private lemma levy_abel (y : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, (∑ j ∈ range k, (y (j + 1) - y j) ^ 2) * (y (k + 1) ^ 2 - y k ^ 2) =
      (∑ j ∈ range n, (y (j + 1) - y j) ^ 2) * y n ^ 2 -
        ∑ k ∈ range n, (y (k + 1) - y k) ^ 2 * y (k + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (y (j + 1) - y j) ^ 2),
      sum_range_succ (fun k => (y (k + 1) - y k) ^ 2 * y (k + 1) ^ 2)]
    ring

/-- A finite sum of `𝓕_r`-measurable functions is `𝓕_r`-measurable. -/
lemma levy_aestronglyMeasurable_sum {𝓕 : Filtration ℝ≥0 mΩ} {r : ℝ≥0} {f : ℕ → Ω → ℝ} {k : ℕ}
    (hf : ∀ j < k, AEStronglyMeasurable[𝓕 r] (f j) μ) :
    AEStronglyMeasurable[𝓕 r] (fun ω => ∑ j ∈ range k, f j ω) μ := by
  induction k with
  | zero =>
    simpa using (aestronglyMeasurable_const : AEStronglyMeasurable[𝓕 r] (fun _ => (0 : ℝ)) μ)
  | succ k ih =>
    simp_rw [sum_range_succ]
    exact (ih fun j hj => hf j (by omega)).add (hf k (by omega))

variable [IsProbabilityMeasure μ] {T : ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ → Ω → ℝ}
  {p : ℕ → ℝ≥0}

/-- Against a bounded `𝓕_{p_k}`-measurable `η`, `𝔼[η (M_{p_{k+1}} - M_{p_k})²] =
𝔼[η ((M_{p_{k+1}} - M_{p_0})² - (M_{p_k} - M_{p_0})²)]`, if `M - M_{p_0}` is bounded at the
times `p_j`. -/
theorem IsCL2Mart.levy_integral_mul_sq_incr (hM : IsCL2Mart T 𝓕 M μ) (hp : Monotone p)
    (hpT : ∀ k, (p k : ℝ) ≤ T) {R : ℝ} (hbd : ∀ ω k, |M (p k) ω - M (p 0) ω| ≤ R) (k : ℕ)
    {η : Ω → ℝ} (hη : AEStronglyMeasurable[𝓕 (p k)] η μ) (hηb : LevyBdd η) :
    ∫ ω, η ω * (M (p (k + 1)) ω - M (p k) ω) ^ 2 ∂μ =
      ∫ ω, η ω * ((M (p (k + 1)) ω - M (p 0) ω) ^ 2 - (M (p k) ω - M (p 0) ω) ^ 2) ∂μ := by
  set y : ℕ → Ω → ℝ := fun j ω => M (p j) ω - M (p 0) ω with hy
  have hyb : ∀ j, LevyBdd (y j) := fun j => levyBdd_of_le fun ω => hbd ω j
  have hym : ∀ j, AEStronglyMeasurable (y j) μ := fun j =>
    ((hM.memLp _ (hpT j)).sub (hM.memLp _ (hpT 0))).aestronglyMeasurable
  have hηm : AEStronglyMeasurable η μ := hη.mono (𝓕.le _)
  -- `y_k` is `𝓕_{p_k}`-measurable
  have hMk : ∀ j, AEStronglyMeasurable[𝓕 (p j)] (M (p j)) μ := fun j =>
    aestronglyMeasurable_of_condExp_eq_self (hM.condExp _ _ le_rfl (hpT j))
  have hyk : AEStronglyMeasurable[𝓕 (p k)] (y k) μ :=
    (hMk k).sub ((hMk 0).mono (𝓕.mono (hp (Nat.zero_le k))))
  have h0 := hM.levy_integral_mul_incr (hp (Nat.le_succ k)) (hpT (k + 1)) (hη.mul hyk)
    ((hηb.mul (hyb k)).memLp (hηm.mul (hym k)) 2)
  simp only [Pi.mul_apply] at h0
  have hdm : AEStronglyMeasurable (fun ω => M (p (k + 1)) ω - M (p k) ω) μ :=
    ((hM.memLp _ (hpT (k + 1))).sub (hM.memLp _ (hpT k))).aestronglyMeasurable
  have hdb : LevyBdd (fun ω => M (p (k + 1)) ω - M (p k) ω) := by
    have : (fun ω => M (p (k + 1)) ω - M (p k) ω) = fun ω => y (k + 1) ω - y k ω := by
      ext ω; simp [hy]
    rw [this]; fun_prop
  have e : ∀ ω, η ω * (M (p (k + 1)) ω - M (p k) ω) ^ 2 =
      η ω * (y (k + 1) ω ^ 2 - y k ω ^ 2) -
        2 * ((η ω * y k ω) * (M (p (k + 1)) ω - M (p k) ω)) := fun ω => by
    simp only [hy]; ring
  simp_rw [e]
  rw [integral_sub (LevyBdd.integrable (by fun_prop) (by fun_prop))
    ((LevyBdd.integrable (by fun_prop) (by fun_prop)).const_mul 2), integral_const_mul, h0,
    mul_zero, sub_zero]

/-- **Second moment of the discrete quadratic variation.** If `M` is a continuous `L²`
martingale on `[0, T]`, `p` is a nondecreasing sequence of times in `[0, T]` and
`|M_{p_k} - M_{p_0}| ≤ R` for every `k`, then
`𝔼 (∑_{k < n} (M_{p_{k+1}} - M_{p_k})²)² ≤ 6 R⁴`. -/
theorem IsCL2Mart.levy_integral_qv_sq_le (hM : IsCL2Mart T 𝓕 M μ) (hp : Monotone p)
    (hpT : ∀ k, (p k : ℝ) ≤ T) {R : ℝ} (hbd : ∀ ω k, |M (p k) ω - M (p 0) ω| ≤ R) (n : ℕ) :
    ∫ ω, (∑ k ∈ range n, (M (p (k + 1)) ω - M (p k) ω) ^ 2) ^ 2 ∂μ ≤ 6 * R ^ 4 := by
  set y : ℕ → Ω → ℝ := fun j ω => M (p j) ω - M (p 0) ω with hy
  have hyb : ∀ j, LevyBdd (y j) := fun j => levyBdd_of_le fun ω => hbd ω j
  have hym : ∀ j, AEStronglyMeasurable (y j) μ := fun j =>
    ((hM.memLp _ (hpT j)).sub (hM.memLp _ (hpT 0))).aestronglyMeasurable
  have hMk : ∀ j, AEStronglyMeasurable[𝓕 (p j)] (M (p j)) μ := fun j =>
    aestronglyMeasurable_of_condExp_eq_self (hM.condExp _ _ le_rfl (hpT j))
  have hyk : ∀ j k, j ≤ k → AEStronglyMeasurable[𝓕 (p k)] (y j) μ := fun j k hjk =>
    ((hMk j).mono (𝓕.mono (hp hjk))).sub ((hMk 0).mono (𝓕.mono (hp (Nat.zero_le k))))
  have hy2 : ∀ ω k, y k ω ^ 2 ≤ R ^ 2 := fun ω k => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd ω k) 2
  have hd2 : ∀ ω k, (y (k + 1) ω - y k ω) ^ 2 ≤ 4 * R ^ 2 := fun ω k => by
    have h1 := hbd ω (k + 1); have h2 := hbd ω k
    have : |y (k + 1) ω - y k ω| ≤ 2 * R := (abs_sub _ _).trans (by simp only [hy]; linarith)
    rw [← sq_abs]; nlinarith [abs_nonneg (y (k + 1) ω - y k ω)]
  -- the orthogonality relation in terms of `y`
  have hA : ∀ k (η : Ω → ℝ), AEStronglyMeasurable[𝓕 (p k)] η μ → LevyBdd η →
      ∫ ω, η ω * (y (k + 1) ω - y k ω) ^ 2 ∂μ =
        ∫ ω, η ω * (y (k + 1) ω ^ 2 - y k ω ^ 2) ∂μ := fun k η hη hηb => by
    have := hM.levy_integral_mul_sq_incr hp hpT hbd k hη hηb
    rw [show (fun ω => η ω * (y (k + 1) ω - y k ω) ^ 2) =
      fun ω => η ω * (M (p (k + 1)) ω - M (p k) ω) ^ 2 from by ext ω; simp only [hy]; ring]
    exact this
  set Q : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ range k, (y (j + 1) ω - y j ω) ^ 2 with hQ
  have hQb : ∀ k, LevyBdd (Q k) := fun k => by simp only [hQ]; fun_prop
  have hQm : ∀ k, AEStronglyMeasurable (Q k) μ := fun k => by simp only [hQ]; fun_prop
  have hQk : ∀ k, AEStronglyMeasurable[𝓕 (p k)] (Q k) μ := fun k => by
    simp only [hQ]
    exact levy_aestronglyMeasurable_sum fun j hj =>
      ((hyk (j + 1) k hj).sub (hyk j k hj.le)).pow 2
  have e0 : ∀ ω, ∑ k ∈ range n, (M (p (k + 1)) ω - M (p k) ω) ^ 2 = Q n ω := fun ω => by
    simp only [hQ, hy]; refine sum_congr rfl fun k _ => by ring
  simp_rw [e0]
  -- `𝔼 Q_n ≤ R²`
  have hEQ : ∫ ω, Q n ω ∂μ ≤ R ^ 2 := by
    have e1 : ∫ ω, Q n ω ∂μ = ∫ ω, y n ω ^ 2 ∂μ := by
      simp only [hQ]
      rw [integral_finsetSum _ fun k _ => LevyBdd.integrable (by fun_prop) (by fun_prop)]
      have e2 : ∀ k, ∫ ω, (y (k + 1) ω - y k ω) ^ 2 ∂μ =
          ∫ ω, (y (k + 1) ω ^ 2 - y k ω ^ 2) ∂μ := fun k => by
        simpa using hA k (fun _ => 1) aestronglyMeasurable_const (levyBdd_const 1)
      simp_rw [e2]
      rw [← integral_finsetSum _ fun k _ => LevyBdd.integrable (by fun_prop) (by fun_prop)]
      congr 1; ext ω
      rw [sum_range_sub (fun k => y k ω ^ 2)]
      simp [hy]
    rw [e1]
    calc ∫ ω, y n ω ^ 2 ∂μ ≤ ∫ _, R ^ 2 ∂μ :=
          integral_mono (LevyBdd.integrable (by fun_prop) (by fun_prop))
            (integrable_const _) fun ω => hy2 ω n
      _ = R ^ 2 := by simp
  -- `𝔼 Q_n² ≤ 6 R² 𝔼 Q_n`
  have hint : ∀ k, Integrable (fun ω => Q k ω * (y (k + 1) ω ^ 2 - y k ω ^ 2)) μ := fun k =>
    LevyBdd.integrable (by fun_prop) (by fun_prop)
  have hstep : ∀ k, ∫ ω, (Q (k + 1) ω ^ 2 - Q k ω ^ 2) ∂μ ≤
      ∫ ω, (2 * (Q k ω * (y (k + 1) ω ^ 2 - y k ω ^ 2)) +
        4 * R ^ 2 * (y (k + 1) ω - y k ω) ^ 2) ∂μ := fun k => by
    have e : ∀ ω, Q (k + 1) ω ^ 2 - Q k ω ^ 2 =
        2 * (Q k ω * (y (k + 1) ω - y k ω) ^ 2) + (y (k + 1) ω - y k ω) ^ 4 := fun ω => by
      simp only [hQ, sum_range_succ]; ring
    simp_rw [e]
    have i1 : Integrable (fun ω => Q k ω * (y (k + 1) ω - y k ω) ^ 2) μ :=
      LevyBdd.integrable (by fun_prop) (by fun_prop)
    have i2 : Integrable (fun ω => (y (k + 1) ω - y k ω) ^ 4) μ :=
      LevyBdd.integrable (by fun_prop) (by fun_prop)
    have i3 : Integrable (fun ω => (y (k + 1) ω - y k ω) ^ 2) μ :=
      LevyBdd.integrable (by fun_prop) (by fun_prop)
    have eL : ∫ ω, (2 * (Q k ω * (y (k + 1) ω - y k ω) ^ 2) + (y (k + 1) ω - y k ω) ^ 4) ∂μ =
        2 * ∫ ω, Q k ω * (y (k + 1) ω - y k ω) ^ 2 ∂μ + ∫ ω, (y (k + 1) ω - y k ω) ^ 4 ∂μ := by
      rw [integral_add (i1.const_mul 2) i2, integral_const_mul]
    have eR : ∫ ω, (2 * (Q k ω * (y (k + 1) ω ^ 2 - y k ω ^ 2)) +
        4 * R ^ 2 * (y (k + 1) ω - y k ω) ^ 2) ∂μ =
        2 * ∫ ω, Q k ω * (y (k + 1) ω ^ 2 - y k ω ^ 2) ∂μ +
          ∫ ω, 4 * R ^ 2 * (y (k + 1) ω - y k ω) ^ 2 ∂μ := by
      rw [integral_add ((hint k).const_mul 2) (i3.const_mul (4 * R ^ 2)), integral_const_mul]
    rw [eL, eR, hA k (Q k) (hQk k) (hQb k)]
    refine add_le_add_right (integral_mono i2 (i3.const_mul (4 * R ^ 2)) fun ω => ?_) _
    have := hd2 ω k
    have h0 := sq_nonneg (y (k + 1) ω - y k ω)
    show (y (k + 1) ω - y k ω) ^ 4 ≤ 4 * R ^ 2 * (y (k + 1) ω - y k ω) ^ 2
    nlinarith
  have hQ0 : ∀ ω, Q 0 ω = 0 := fun ω => by simp [hQ]
  calc ∫ ω, Q n ω ^ 2 ∂μ = ∑ k ∈ range n, ∫ ω, (Q (k + 1) ω ^ 2 - Q k ω ^ 2) ∂μ := by
        rw [← integral_finsetSum _ fun k _ => LevyBdd.integrable (by fun_prop) (by fun_prop)]
        congr 1; ext ω
        rw [sum_range_sub (fun k => Q k ω ^ 2), hQ0]; ring
    _ ≤ ∑ k ∈ range n, ∫ ω, (2 * (Q k ω * (y (k + 1) ω ^ 2 - y k ω ^ 2)) +
        4 * R ^ 2 * (y (k + 1) ω - y k ω) ^ 2) ∂μ := sum_le_sum fun k _ => hstep k
    _ = ∫ ω, (2 * (Q n ω * y n ω ^ 2 - ∑ k ∈ range n, (y (k + 1) ω - y k ω) ^ 2 *
        y (k + 1) ω ^ 2) + 4 * R ^ 2 * Q n ω) ∂μ := by
        rw [← integral_finsetSum _ fun k _ => LevyBdd.integrable (by fun_prop) (by fun_prop)]
        congr 1; ext ω
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        rw [levy_abel (fun k => y k ω) n]
    _ ≤ ∫ ω, 6 * R ^ 2 * Q n ω ∂μ := by
        refine integral_mono (LevyBdd.integrable (by fun_prop) (by fun_prop))
          ((LevyBdd.integrable (hQb n) (hQm n)).const_mul _) fun ω => ?_
        have hQn : 0 ≤ Q n ω := sum_nonneg fun _ _ => sq_nonneg _
        have hs : 0 ≤ ∑ k ∈ range n, (y (k + 1) ω - y k ω) ^ 2 * y (k + 1) ω ^ 2 :=
          sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
        have := mul_le_mul_of_nonneg_left (hy2 ω n) hQn
        nlinarith
    _ ≤ 6 * R ^ 4 := by
        rw [integral_const_mul]
        nlinarith [sq_nonneg R]
end QSSEPtoKPZ
