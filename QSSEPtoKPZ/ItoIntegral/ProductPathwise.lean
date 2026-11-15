/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Basic

/-!
# Product rule: the uniform grid and the pathwise estimates (package C, task C6)

Auxiliary material for `ItoIntegral/Product.lean`.

* `itoProdGrid t m k = k t / m`: the uniform partition of `[0, t]` in `m` cells.
* `itoProd_telescope`: the discrete product rule
  `u_m v_m - u_0 v_0 = ∑_{k < m} (u_k Δv_k + v_k Δu_k + Δu_k Δv_k)`.
* `itoProd_tendsto_drift_riemann`: for `f` continuous on `[0, r]` and `g` bounded and integrable
  on `[0, r]`, `∑_k f(t_k) ∫_{t_k ∧ r}^{t_{k+1} ∧ r} g → ∫_0^{t ∧ r} f g`.
* `itoProd_tendsto_cross`: for continuous `U`, `V` and bounded `a`, `c`,
  `∑_k (ΔU_k ΔV_k - (ΔU_k - Δa_k)(ΔV_k - Δc_k)) → 0`, where `Δa_k = ∫_{t_k ∧ r}^{t_{k+1} ∧ r} a`
  (the drift parts do not contribute to the quadratic covariation).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The grid point `t_k = k (t / m)` of the uniform partition of `[0, t]` in `m` cells. -/
def itoProdGrid (t : ℝ≥0) (m k : ℕ) : ℝ≥0 := (k : ℝ≥0) * (t / m)

lemma itoProdGrid_zero (t : ℝ≥0) (m : ℕ) : itoProdGrid t m 0 = 0 := by
  simp [itoProdGrid]

lemma itoProdGrid_self (t : ℝ≥0) {m : ℕ} (hm : m ≠ 0) : itoProdGrid t m m = t := by
  unfold itoProdGrid
  rw [mul_div_cancel₀]
  exact_mod_cast hm

lemma itoProdGrid_succ (t : ℝ≥0) (m k : ℕ) :
    itoProdGrid t m (k + 1) = itoProdGrid t m k + t / m := by
  unfold itoProdGrid
  push_cast
  ring

lemma itoProdGrid_mono (t : ℝ≥0) (m : ℕ) : Monotone (itoProdGrid t m) := fun k l hkl => by
  unfold itoProdGrid
  gcongr

lemma itoProdGrid_le (t : ℝ≥0) {m k : ℕ} (hk : k ≤ m) : itoProdGrid t m k ≤ t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [itoProdGrid]
  · calc itoProdGrid t m k ≤ itoProdGrid t m m := itoProdGrid_mono t m hk
      _ = t := itoProdGrid_self t hm.ne'

/-- **Discrete product rule.** `u_m v_m - u_0 v_0 = ∑_{k < m} (u_k Δv_k + v_k Δu_k + Δu_k Δv_k)`. -/
lemma itoProd_telescope (u v : ℕ → ℝ) (m : ℕ) :
    u m * v m - u 0 * v 0 = ∑ k ∈ Finset.range m,
      (u k * (v (k + 1) - v k) + v k * (u (k + 1) - u k) + (u (k + 1) - u k) * (v (k + 1) - v k)) := by
  rw [← Finset.sum_range_sub (fun k => u k * v k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The stopped grid points `t_k ∧ r` lie in `[0, r]`. -/
lemma itoProdGrid_min_mem (t r : ℝ≥0) (m k : ℕ) :
    ((min (itoProdGrid t m k) r : ℝ≥0) : ℝ) ∈ Set.Icc (0 : ℝ) r :=
  ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩

/-- Consecutive stopped grid points are at most `t / m` apart. -/
lemma itoProdGrid_min_sub (t r : ℝ≥0) (m k : ℕ) :
    0 ≤ ((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ) - ((min (itoProdGrid t m k) r : ℝ≥0) : ℝ) ∧
    ((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ) - ((min (itoProdGrid t m k) r : ℝ≥0) : ℝ) ≤
      (t : ℝ) / m := by
  have hmono : itoProdGrid t m k ≤ itoProdGrid t m (k + 1) := itoProdGrid_mono t m (Nat.le_succ k)
  constructor
  · rw [sub_nonneg]
    exact NNReal.coe_le_coe.2 (min_le_min_right _ hmono)
  · have h := abs_min_sub_min_le_max ((itoProdGrid t m k : ℝ) + (t : ℝ) / m) (r : ℝ)
      ((itoProdGrid t m k : ℝ)) (r : ℝ)
    rw [sub_self, abs_zero, add_sub_cancel_left, max_eq_left (abs_nonneg _),
      abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) / m by positivity)] at h
    have e : ((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ) =
        min ((itoProdGrid t m k : ℝ) + (t : ℝ) / m) (r : ℝ) := by
      rw [NNReal.coe_min, itoProdGrid_succ, NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast]
    rw [e, NNReal.coe_min]
    exact (le_abs_self _).trans h

/-- A bounded integrand: `|∫_{t_k ∧ r}^{t_{k+1} ∧ r} a| ≤ K t / m`. -/
lemma itoProd_abs_integral_cell_le {a : ℝ → ℝ} {r t : ℝ≥0} {K : ℝ}
    (ha : IntervalIntegrable a volume 0 r) (haK : ∀ s : ℝ, 0 ≤ s → s ≤ r → |a s| ≤ K)
    (m k : ℕ) :
    |(∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ), a s) -
        ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) r : ℝ≥0) : ℝ), a s| ≤ K * ((t : ℝ) / m) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (haK 0 le_rfl r.2)
  have hIcc : Set.uIcc (0 : ℝ) r = Set.Icc (0 : ℝ) (r : ℝ) := Set.uIcc_of_le r.2
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) r := ⟨le_rfl, r.2⟩
  have hint : ∀ x ∈ Set.Icc (0 : ℝ) r, IntervalIntegrable a volume 0 x := fun x hx =>
    ha.mono_set (hIcc ▸ Set.uIcc_subset_Icc h0 hx)
  rw [intervalIntegral.integral_interval_sub_left (hint _ (itoProdGrid_min_mem t r m (k + 1)))
    (hint _ (itoProdGrid_min_mem t r m k))]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := K) (f := a)
    (a := ((min (itoProdGrid t m k) r : ℝ≥0) : ℝ))
    (b := ((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ)) (fun x hx => by
      have hx' := Set.uIcc_subset_Icc (itoProdGrid_min_mem t r m k)
        (itoProdGrid_min_mem t r m (k + 1)) (Set.uIoc_subset_uIcc hx)
      rw [Real.norm_eq_abs]
      exact haK x hx'.1 hx'.2)
  rw [Real.norm_eq_abs] at hb
  have hd := itoProdGrid_min_sub t r m k
  rw [abs_of_nonneg hd.1] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hd.2 hK)

/-- **Drift Riemann sums.** If `f` is continuous on `[0, r]` and `g` is integrable and bounded by
`K` on `[0, r]`, then `∑_{k < m} f(t_k) 𝟙_{t_k ≤ r} ∫_{t_k ∧ r}^{t_{k+1} ∧ r} g → ∫_0^{t ∧ r} f g`
(with `t_k = k t / m`). -/
theorem itoProd_tendsto_drift_riemann {f g : ℝ → ℝ} {r t : ℝ≥0} {K : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 r)) (hg : IntervalIntegrable g volume 0 r)
    (hgK : ∀ s : ℝ, 0 ≤ s → s ≤ r → |g s| ≤ K) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m,
        (if (itoProdGrid t m k : ℝ) ≤ r then f (itoProdGrid t m k) else 0) *
          ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ), g s) -
            ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) r : ℝ≥0) : ℝ), g s))
      atTop (𝓝 (∫ s in (0 : ℝ)..((min t r : ℝ≥0) : ℝ), f s * g s)) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hgK 0 le_rfl r.2)
  have hIcc : Set.uIcc (0 : ℝ) r = Set.Icc (0 : ℝ) (r : ℝ) := Set.uIcc_of_le r.2
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) r := ⟨le_rfl, r.2⟩
  have hfg : IntervalIntegrable (fun s => f s * g s) volume 0 r :=
    hg.continuousOn_mul (by rwa [hIcc])
  have hgi : ∀ x ∈ Set.Icc (0 : ℝ) r, ∀ y ∈ Set.Icc (0 : ℝ) r,
      IntervalIntegrable g volume x y :=
    fun x hx y hy => hg.mono_set (hIcc ▸ Set.uIcc_subset_Icc hx hy)
  have hfgi : ∀ x ∈ Set.Icc (0 : ℝ) r, ∀ y ∈ Set.Icc (0 : ℝ) r,
      IntervalIntegrable (fun s => f s * g s) volume x y :=
    fun x hx y hy => hfg.mono_set (hIcc ▸ Set.uIcc_subset_Icc hx hy)
  have huc := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (K * t + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδf⟩ := huc ε' hε'pos
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / δ)
  refine ⟨N + 1, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hstep : (t : ℝ) / m ≤ δ := by
    rw [div_le_iff₀ hmpos]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) + 1 ≤ m := by exact_mod_cast hm
    nlinarith
  set A : ℕ → ℝ := fun k => ((min (itoProdGrid t m k) r : ℝ≥0) : ℝ) with hA
  set Zc : ℕ → ℝ := fun k =>
    if (itoProdGrid t m k : ℝ) ≤ r then f (itoProdGrid t m k) else 0 with hZc
  show dist (∑ k ∈ Finset.range m,
      Zc k * ((∫ s in (0 : ℝ)..A (k + 1), g s) - ∫ s in (0 : ℝ)..A k, g s))
    (∫ s in (0 : ℝ)..((min t r : ℝ≥0) : ℝ), f s * g s) < ε
  have hmem : ∀ k, A k ∈ Set.Icc (0 : ℝ) r := itoProdGrid_min_mem t r m
  have hA0 : A 0 = 0 := by simp [hA, itoProdGrid_zero]
  have hAm : A m = ((min t r : ℝ≥0) : ℝ) := by simp [hA, itoProdGrid_self t hm0]
  have hL : ∫ s in (0 : ℝ)..((min t r : ℝ≥0) : ℝ), f s * g s =
      ∑ k ∈ Finset.range m, ∫ s in A k..A (k + 1), f s * g s := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hfgi _ (hmem k) _ (hmem (k + 1))), hA0, hAm]
  have hterm : ∀ k, Zc k * ((∫ s in (0 : ℝ)..A (k + 1), g s) - ∫ s in (0 : ℝ)..A k, g s) -
      ∫ s in A k..A (k + 1), f s * g s = ∫ s in A k..A (k + 1), (Zc k - f s) * g s := by
    intro k
    rw [intervalIntegral.integral_interval_sub_left (hgi _ h0 _ (hmem _)) (hgi _ h0 _ (hmem _)),
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hgi _ (hmem k) _ (hmem (k + 1))).const_mul (Zc k))
        (hfgi _ (hmem k) _ (hmem (k + 1)))]
    congr 1
    funext s
    ring
  have hbound : ∀ k ∈ Finset.range m,
      ‖∫ s in A k..A (k + 1), (Zc k - f s) * g s‖ ≤ ε' * K * (A (k + 1) - A k) := by
    intro k _
    have hd := itoProdGrid_min_sub t r m k
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε' * K) (a := A k)
      (b := A (k + 1)) (f := fun s => (Zc k - f s) * g s) ?_
    · rwa [abs_of_nonneg hd.1] at hb
    intro x hx
    have hx' := Set.uIcc_subset_Icc (hmem k) (hmem (k + 1)) (Set.uIoc_subset_uIcc hx)
    rw [Set.uIoc_of_le (sub_nonneg.1 hd.1)] at hx
    by_cases hk : (itoProdGrid t m k : ℝ) ≤ r
    · have hAk : A k = itoProdGrid t m k := by
        simp only [hA]
        rw [NNReal.coe_min, min_eq_left hk]
      have hZk : Zc k = f (itoProdGrid t m k) := by simp only [hZc, hk, ↓reduceIte]
      rw [hZk, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul ?_ (hgK x hx'.1 hx'.2) (abs_nonneg _) hε'pos.le
      have hxk : dist ((itoProdGrid t m k : ℝ)) x ≤ δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.2, hd.2]
      have := hδf _ (hAk ▸ hmem k) _ hx' hxk
      rwa [Real.dist_eq] at this
    · exfalso
      have hAk : A k = r := by
        simp only [hA]
        rw [NNReal.coe_min, min_eq_right (not_le.1 hk).le]
      linarith [hx.1, hx.2, hx'.2]
  rw [dist_eq_norm, hL, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun k _ => hterm k)]
  calc ‖∑ k ∈ Finset.range m, ∫ s in A k..A (k + 1), (Zc k - f s) * g s‖
      ≤ ∑ k ∈ Finset.range m, ‖∫ s in A k..A (k + 1), (Zc k - f s) * g s‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, ε' * K * (A (k + 1) - A k) := Finset.sum_le_sum hbound
    _ = ε' * K * (A m - A 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ ε' * K * t := by
        rw [hA0, sub_zero, hAm]
        exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (min_le_left _ _))
          (mul_nonneg hε'pos.le hK)
    _ = ε * (K * t / (K * t + 1)) := by rw [hε']; ring
    _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (by linarith))

/-- `|xy - (x - p)(y - q)| ≤ 2 c e + c²` when `|x|, |y| ≤ e` and `|p|, |q| ≤ c`. -/
lemma itoProd_cross_le {x y p q e c : ℝ} (hx : |x| ≤ e) (hy : |y| ≤ e) (hp : |p| ≤ c)
    (hq : |q| ≤ c) : |x * y - (x - p) * (y - q)| ≤ 2 * c * e + c ^ 2 := by
  have e1 : x * y - (x - p) * (y - q) = p * y + x * q - p * q := by ring
  rw [e1]
  have hc : 0 ≤ c := (abs_nonneg _).trans hp
  have h1 : |p * y| ≤ c * e := by
    rw [abs_mul]; exact mul_le_mul hp hy (abs_nonneg _) hc
  have h2 : |x * q| ≤ c * e := by
    rw [abs_mul, mul_comm c]; exact mul_le_mul hx hq (abs_nonneg _) ((abs_nonneg _).trans hx)
  have h3 : |p * q| ≤ c ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hp hq (abs_nonneg _) hc
  calc |p * y + x * q - p * q| ≤ |p * y + x * q| + |p * q| := abs_sub _ _
    _ ≤ |p * y| + |x * q| + |p * q| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * c * e + c ^ 2 := by linarith

/-- **The drift parts do not contribute to the quadratic covariation.** If `U`, `V` are
continuous and `a`, `c` are integrable and bounded by `K` on `[0, r]`, then
`∑_{k < m} (ΔU_k ΔV_k - (ΔU_k - Δa_k)(ΔV_k - Δc_k)) → 0`, where `ΔU_k = U(t_{k+1}) - U(t_k)` and
`Δa_k = ∫_0^{t_{k+1} ∧ r} a - ∫_0^{t_k ∧ r} a`. -/
theorem itoProd_tendsto_cross {U V : ℝ≥0 → ℝ} (hU : Continuous U) (hV : Continuous V)
    {a c : ℝ → ℝ} {r t : ℝ≥0} {K : ℝ}
    (ha : IntervalIntegrable a volume 0 r) (hc : IntervalIntegrable c volume 0 r)
    (haK : ∀ s : ℝ, 0 ≤ s → s ≤ r → |a s| ≤ K) (hcK : ∀ s : ℝ, 0 ≤ s → s ≤ r → |c s| ≤ K) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m,
        ((U (itoProdGrid t m (k + 1)) - U (itoProdGrid t m k)) *
            (V (itoProdGrid t m (k + 1)) - V (itoProdGrid t m k)) -
          ((U (itoProdGrid t m (k + 1)) - U (itoProdGrid t m k)) -
              ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ), a s) -
                ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) r : ℝ≥0) : ℝ), a s)) *
            ((V (itoProdGrid t m (k + 1)) - V (itoProdGrid t m k)) -
              ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ), c s) -
                ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) r : ℝ≥0) : ℝ), c s))))
      atTop (𝓝 0) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (haK 0 le_rfl r.2)
  have hUc := Metric.uniformContinuousOn_iff_le.1
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).uniformContinuousOn_of_continuous hU.continuousOn)
  have hVc := Metric.uniformContinuousOn_iff_le.1
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).uniformContinuousOn_of_continuous hV.continuousOn)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (4 * (K * t + 1)) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨δ₁, hδ₁, hU'⟩ := hUc ε' hε'pos
  obtain ⟨δ₂, hδ₂, hV'⟩ := hVc ε' hε'pos
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((t : ℝ) / min δ₁ δ₂) (2 * K ^ 2 * t ^ 2 / ε))
  refine ⟨N + 1, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hmN : (N : ℝ) + 1 ≤ m := by exact_mod_cast hm
  have hδmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hstep : (t : ℝ) / m ≤ min δ₁ δ₂ := by
    have h1 := (le_max_left _ _).trans_lt hN
    rw [div_lt_iff₀ hδmin] at h1
    rw [div_le_iff₀ hmpos]
    nlinarith
  have hsq : 2 * K ^ 2 * t ^ 2 / ε < m := by
    have h1 := (le_max_right _ _).trans_lt hN
    linarith
  have hcell : ∀ k, k < m → dist (itoProdGrid t m (k + 1)) (itoProdGrid t m k) ≤ min δ₁ δ₂ := by
    intro k _
    rw [NNReal.dist_eq, itoProdGrid_succ]
    push_cast
    rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
    exact hstep
  have hmemI : ∀ k, k ≤ m → itoProdGrid t m k ∈ Set.Icc (0 : ℝ≥0) t :=
    fun k hk => ⟨zero_le, itoProdGrid_le t hk⟩
  have hterm : ∀ k ∈ Finset.range m, |(U (itoProdGrid t m (k + 1)) - U (itoProdGrid t m k)) *
          (V (itoProdGrid t m (k + 1)) - V (itoProdGrid t m k)) -
        ((U (itoProdGrid t m (k + 1)) - U (itoProdGrid t m k)) -
            ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ), a s) -
              ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) r : ℝ≥0) : ℝ), a s)) *
          ((V (itoProdGrid t m (k + 1)) - V (itoProdGrid t m k)) -
            ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) r : ℝ≥0) : ℝ), c s) -
              ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) r : ℝ≥0) : ℝ), c s))| ≤
      2 * (K * ((t : ℝ) / m)) * ε' + (K * ((t : ℝ) / m)) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hx : |U (itoProdGrid t m (k + 1)) - U (itoProdGrid t m k)| ≤ ε' := by
      have := hU' _ (hmemI _ hk) _ (hmemI _ hk.le) ((hcell k hk).trans (min_le_left _ _))
      rwa [Real.dist_eq] at this
    have hy : |V (itoProdGrid t m (k + 1)) - V (itoProdGrid t m k)| ≤ ε' := by
      have := hV' _ (hmemI _ hk) _ (hmemI _ hk.le) ((hcell k hk).trans (min_le_right _ _))
      rwa [Real.dist_eq] at this
    exact itoProd_cross_le hx hy (itoProd_abs_integral_cell_le ha haK m k)
      (itoProd_abs_integral_cell_le hc hcK m k)
  rw [dist_zero_right, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ?_
  refine (Finset.sum_le_sum hterm).trans_lt ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e1 : (m : ℝ) * (2 * (K * ((t : ℝ) / m)) * ε' + (K * ((t : ℝ) / m)) ^ 2) =
      2 * (K * t) * ε' + K ^ 2 * t ^ 2 / m := by
    field_simp
  rw [e1]
  have e2 : 2 * (K * t) * ε' < ε / 2 := by
    have : 2 * (K * t) * ε' = ε / 2 * (K * t / (K * t + 1)) := by rw [hε']; field_simp; ring
    rw [this]
    exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
  have e3 : K ^ 2 * t ^ 2 / m < ε / 2 := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hε] at hsq
    nlinarith
  linarith

end QSSEPtoKPZ
