/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.BoundedWeights

/-!
# Auxiliary results for the moment bound (2.2) (task D4)

* The truncated weights `w_{b,R}(x) = e^{b min(|x|, R)}` (`momentWeight b R x`): bounds, the
  shift inequalities `w(x ± 1) ≤ e^b w(x)`, hence `Δw ≤ 2 (e^b - 1) w` and
  `(w(x+1) - w(x))² ≤ ((e^b - 1) e^b)² w(x)²`, and `w_{b,R}^n = w_{nb,R}`.
* Jensen's inequality for the probability `P(t,·)`: `(∑ₓ e(x) P(x))² ≤ ∑ₓ e(x)² P(x)` for bounded
  `e`, hence `V_{b,R}^{2^k} ≤ V_{2^k b,R}` where `V_{b,R}(t) = ∑ₓ w_{b,R}(x) P(t,x)`.
* Measurability of `sup_{t ∈ [0,T]} ∑ₓ g_x(t)` for `g_x ≥ 0` continuous in `t` (the supremum may
  be taken over the countable dyadic grid of `[0, T]`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-! ### The truncated exponential weights -/

/-- The truncated weight `w_{b,R}(x) = e^{b min(|x|, R)}`. -/
def momentWeight (b : ℝ) (R : ℕ) (x : ℤ) : ℝ := Real.exp (b * min |(x : ℝ)| R)

lemma momentWeight_pos (b : ℝ) (R : ℕ) (x : ℤ) : 0 < momentWeight b R x := Real.exp_pos _

lemma momentWeight_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    momentWeight b R x ≤ Real.exp (b * R) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)

lemma abs_momentWeight_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    |momentWeight b R x| ≤ Real.exp (b * R) := by
  rw [abs_of_pos (momentWeight_pos b R x)]; exact momentWeight_le hb R x

lemma momentWeight_mono {b : ℝ} (hb : 0 ≤ b) {R R' : ℕ} (h : R ≤ R') (x : ℤ) :
    momentWeight b R x ≤ momentWeight b R' x :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_min_left _ (by exact_mod_cast h)) hb)

/-- `w_{b,R}(x) = e^{b|x|}` for `R ≥ |x|`. -/
lemma momentWeight_eq_of_le (b : ℝ) {R : ℕ} {x : ℤ} (h : x.natAbs ≤ R) :
    momentWeight b R x = Real.exp (b * |(x : ℝ)|) := by
  unfold momentWeight
  rw [min_eq_left]
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast h

lemma momentWeight_le_exp_abs {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    momentWeight b R x ≤ Real.exp (b * |(x : ℝ)|) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)

/-- `w_{b,R}^n = w_{nb,R}`. -/
lemma momentWeight_pow (b : ℝ) (R : ℕ) (x : ℤ) (n : ℕ) :
    momentWeight b R x ^ n = momentWeight (n * b) R x := by
  unfold momentWeight
  rw [← Real.exp_nat_mul]
  ring_nf

/-- `|min(|x+1|, R) - min(|x|, R)| ≤ 1`. -/
lemma abs_min_succ_sub_le (R : ℕ) (x : ℤ) :
    |min |((x + 1 : ℤ) : ℝ)| (R : ℝ) - min |(x : ℝ)| R| ≤ 1 := by
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ (by simp))
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  push_cast
  simp

/-- `w(x+1) ≤ e^b w(x)`. -/
lemma momentWeight_succ_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    momentWeight b R (x + 1) ≤ Real.exp b * momentWeight b R x := by
  unfold momentWeight
  rw [← Real.exp_add, Real.exp_le_exp]
  have := (abs_le.1 (abs_min_succ_sub_le R x)).2
  nlinarith

/-- `w(x) ≤ e^b w(x+1)`. -/
lemma momentWeight_le_succ {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    momentWeight b R x ≤ Real.exp b * momentWeight b R (x + 1) := by
  unfold momentWeight
  rw [← Real.exp_add, Real.exp_le_exp]
  have := (abs_le.1 (abs_min_succ_sub_le R x)).1
  nlinarith

/-- `Δw_{b,R} ≤ 2 (e^b - 1) w_{b,R}`. -/
lemma lap_momentWeight_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    lap (momentWeight b R) x ≤ 2 * (Real.exp b - 1) * momentWeight b R x := by
  have h1 := momentWeight_succ_le hb R x
  have h2 := momentWeight_le_succ hb R (x - 1)
  rw [sub_add_cancel] at h2
  unfold lap
  linarith

/-- `(w(x+1) - w(x))² ≤ ((e^b - 1) e^b)² w(x)²`. -/
lemma sq_momentWeight_sub_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (x : ℤ) :
    (momentWeight b R (x + 1) - momentWeight b R x) ^ 2 ≤
      ((Real.exp b - 1) * Real.exp b) ^ 2 * momentWeight b R x ^ 2 := by
  have h1 := momentWeight_succ_le hb R x
  have h2 := momentWeight_le_succ hb R x
  have he : 1 ≤ Real.exp b := Real.one_le_exp hb
  have hw := momentWeight_pos b R x
  have hw1 := momentWeight_pos b R (x + 1)
  rw [← mul_pow]
  refine sq_le_sq' ?_ ?_
  · -- `w(x) - w(x+1) ≤ (e^b - 1) w(x+1) ≤ (e^b - 1) e^b w(x)`
    have : (Real.exp b - 1) * momentWeight b R (x + 1) ≤
        (Real.exp b - 1) * (Real.exp b * momentWeight b R x) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  · have : (Real.exp b - 1) * momentWeight b R x ≤
        (Real.exp b - 1) * Real.exp b * momentWeight b R x := by
      have := mul_le_mul_of_nonneg_left he (show 0 ≤ (Real.exp b - 1) * momentWeight b R x by
        nlinarith)
      nlinarith
    nlinarith

/-! ### Jensen's inequality for `P(t, ·)` -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Jensen** (`P(t,·)` is a probability on `ℤ`): `(∑ₓ e(x) P(x))² ≤ ∑ₓ e(x)² P(x)` for
bounded `e`. -/
lemma IsUnitWave.sq_tsum_mul_density_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s) {e : ℤ → ℝ} {C : ℝ}
    (he : ∀ x, |e x| ≤ C) :
    (∑' x, e x * density ψ' ω s x) ^ 2 ≤ ∑' x, e x ^ 2 * density ψ' ω s x := by
  set m := ∑' x, e x * density ψ' ω s x with hm
  have hP := weight_summable_density ψ' ω s
  have h1 := weight_summable_mul_of_abs_le he hP
  have he2 : ∀ x, |e x ^ 2| ≤ C ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (he x) 2
  have h2 := weight_summable_mul_of_abs_le he2 hP
  have e1 : (fun x => (e x - m) ^ 2 * density ψ' ω s x) = fun x =>
      e x ^ 2 * density ψ' ω s x - 2 * m * (e x * density ψ' ω s x) +
        m ^ 2 * density ψ' ω s x := by
    funext x; ring
  have hnn : 0 ≤ ∑' x, (e x - m) ^ 2 * density ψ' ω s x :=
    tsum_nonneg fun x => mul_nonneg (sq_nonneg _) (density_nonneg ψ' ω s x)
  rw [e1, (h2.sub (h1.mul_left _)).tsum_add (hP.mul_left _), h2.tsum_sub (h1.mul_left _),
    tsum_mul_left, tsum_mul_left, hu.weight_tsum_density ω hs, ← hm] at hnn
  nlinarith

/-- `V_{b,R}(s) = ∑ₓ w_{b,R}(x) P(s,x)`. -/
def momentV (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (b : ℝ) (R : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  ∑' x, momentWeight b R x * density ψ ω s x

lemma momentV_nonneg (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (b : ℝ) (R : ℕ) (s : ℝ) (ω : Ω) :
    0 ≤ momentV ψ b R s ω :=
  tsum_nonneg fun x => mul_nonneg (momentWeight_pos b R x).le (IsUnitWave.density_nonneg ψ ω s x)

lemma summable_momentV {b : ℝ} (hb : 0 ≤ b) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (R : ℕ) (s : ℝ)
    (ω : Ω) : Summable fun x => momentWeight b R x * density ψ ω s x :=
  weight_summable_mul_of_abs_le (abs_momentWeight_le hb R) (weight_summable_density ψ ω s)

/-- **Iterated Jensen**: `V_{b,R}^{2^k} ≤ V_{2^k b,R}`. -/
lemma IsUnitWave.momentV_pow_le (hu : IsUnitWave 𝓕 B ψ ψ' μ)
    (ω : Ω) {s : ℝ} (hs : 0 ≤ s) {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (k : ℕ) :
    momentV ψ' b R s ω ^ (2 ^ k) ≤ momentV ψ' (2 ^ k * b) R s ω := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb' : 0 ≤ 2 ^ k * b := by positivity
    calc momentV ψ' b R s ω ^ 2 ^ (k + 1) = (momentV ψ' b R s ω ^ 2 ^ k) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ momentV ψ' (2 ^ k * b) R s ω ^ 2 :=
          pow_le_pow_left₀ (pow_nonneg (momentV_nonneg _ _ _ _ _) _) ih 2
      _ ≤ ∑' x, momentWeight (2 ^ k * b) R x ^ 2 * density ψ' ω s x :=
          hu.sq_tsum_mul_density_le ω hs (abs_momentWeight_le hb' R)
      _ = momentV ψ' (2 ^ (k + 1) * b) R s ω := by
          unfold momentV
          congr 1
          funext x
          rw [momentWeight_pow]
          push_cast
          ring_nf

/-! ### Measurability of suprema over `[0, T]` -/

/-- If `t ↦ g_x(t, ω) ∈ [0, ∞]` is continuous on `[0, T]` for every `x` and `ω`, and
`ω ↦ g_x(t, ω)` is measurable for `t ∈ [0, T]`, then `ω ↦ sup_{t ∈ [0,T]} ∑ₓ g_x(t, ω)` is measurable: the
supremum equals the supremum over the dyadic grid of `[0, T]` (each finite partial sum is
continuous, and the series is the supremum of its partial sums). -/
lemma measurable_iSup_Icc_tsum {T : ℝ} {g : ℤ → ℝ → Ω → ℝ≥0∞}
    (hc : ∀ x ω, ContinuousOn (fun t => g x t ω) (Set.Icc 0 T))
    (hm : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (g x t)) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x, g x t ω := by
  rcases lt_or_ge T 0 with hT | hT
  · simp only [Set.Icc_eq_empty (not_le.2 hT), Set.mem_empty_iff_false, iSup_false,
      iSup_const]
    exact measurable_const
  set τ := T.toNNReal with hτ
  have hτT : (τ : ℝ) = T := Real.coe_toNNReal _ hT
  have hgrid : ∀ j k, ((gridPt τ j k : ℝ≥0) : ℝ) ∈ Set.Icc (0 : ℝ) T := fun j k =>
    ⟨NNReal.coe_nonneg _, hτT ▸ NNReal.coe_le_coe.2 (gridPt_le τ j k)⟩
  have e : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x, g x t ω) =
      fun ω => ⨆ j : ℕ, ⨆ k : ℕ, ∑' x, g x (gridPt τ j k) ω := by
    funext ω
    apply le_antisymm
    · refine iSup₂_le fun t ht => ?_
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun F => ?_
      obtain ⟨_, hlim⟩ := tendsto_gridPt hT ht
      have hcF : ContinuousOn (fun t => ∑ x ∈ F, g x t ω) (Set.Icc 0 T) :=
        continuousOn_finsetSum _ fun x _ => hc x ω
      have hl : Tendsto (fun j : ℕ => ∑ x ∈ F, g x (gridPt τ j ⌊2 ^ j * t / T⌋₊) ω) atTop
          (𝓝 (∑ x ∈ F, g x t ω)) :=
        (hcF t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim,
          Eventually.of_forall fun j => hgrid j _⟩)
      refine le_of_tendsto' hl fun j => ?_
      exact (ENNReal.sum_le_tsum F).trans (le_iSup_of_le j (le_iSup_of_le _ le_rfl))
    · exact iSup_le fun j => iSup_le fun k =>
        le_iSup₂ (f := fun t _ => ∑' x, g x t ω) _ (hgrid j k)
  rw [e]
  exact Measurable.iSup fun j => Measurable.iSup fun k =>
    Measurable.tsum fun x => hm x _ (hgrid j k)

end QSSEPtoKPZ
