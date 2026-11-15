/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.BoundedWeights
public import QSSEPtoKPZ.WaveFunction.MomentBound

/-!
# Deterministic estimates for exponentially growing weights (task D5)

Let `E_b(x) = e^{b|x|}`, `b ≥ 0`. For a nonnegative `p : ℤ → ℝ` with `∑ₓ E_b(x) p(x) < ∞` and
weights `|w(x)|, |w'(x)| ≤ C E_b(x)`:

* `linExp_drift_facts`: the drift series `∑ₓ (w'(x) p(x) + w(x) Δp(x))` converges absolutely,
  equals `∑ₓ (w' + Δw)(x) p(x)` (summation by parts), and its partial sums are bounded by
  `C (3 + 2 e^b) ∑ₓ E_b(x) p(x)`;
* `linExp_bracket_term_le`: if `|w(x)| ≤ C E_a(x)` and `0 ≤ p ≤ 1`, then
  `(w(y+1) - w(y))² · 2 p(y) p(y+1) ≤ 4 C² (E_{2a}(y+1) p(y+1) + E_{2a}(y) p(y))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- `E_b(x + c) ≤ e^{b |c|} E_b(x)` for `b ≥ 0`. -/
lemma linExp_exp_shift_le {b : ℝ} (hb : 0 ≤ b) (x c : ℤ) :
    Real.exp (b * |((x + c : ℤ) : ℝ)|) ≤ Real.exp (b * |(c : ℝ)|) * Real.exp (b * |(x : ℝ)|) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  push_cast
  have := abs_add_le (x : ℝ) (c : ℝ)
  nlinarith

/-- `E_a(x)² = E_{2a}(x)`. -/
lemma linExp_exp_sq (a : ℝ) (x : ℤ) :
    Real.exp (a * |(x : ℝ)|) ^ 2 = Real.exp (2 * a * |(x : ℝ)|) := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- `E_a(x) ≤ E_{2a}(x)` for `a ≥ 0`. -/
lemma linExp_exp_le_two {a : ℝ} (ha : 0 ≤ a) (x : ℤ) :
    Real.exp (a * |(x : ℝ)|) ≤ Real.exp (2 * a * |(x : ℝ)|) := by
  rw [Real.exp_le_exp]
  have := abs_nonneg (x : ℝ)
  nlinarith

/-- If `∑ₓ E_b(x) p(x)` converges (`p ≥ 0`), so does `∑ₓ E_b(x) p(x + c)`, with sum at most
`e^{b|c|} ∑ₓ E_b(x) p(x)`. -/
lemma linExp_summable_shift {b : ℝ} (hb : 0 ≤ b) {p : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hs : Summable fun x : ℤ => Real.exp (b * |(x : ℝ)|) * p x) (c : ℤ) :
    Summable (fun x : ℤ => Real.exp (b * |(x : ℝ)|) * p (x + c)) ∧
    ∑' x : ℤ, Real.exp (b * |(x : ℝ)|) * p (x + c) ≤
      Real.exp (b * |(c : ℝ)|) * ∑' x : ℤ, Real.exp (b * |(x : ℝ)|) * p x := by
  have hs' : Summable fun x : ℤ => Real.exp (b * |(c : ℝ)|) *
      (Real.exp (b * |((x + c : ℤ) : ℝ)|) * p (x + c)) :=
    ((Equiv.addRight c).summable_iff.2 hs).mul_left _
  have hle : ∀ x : ℤ, Real.exp (b * |(x : ℝ)|) * p (x + c) ≤ Real.exp (b * |(c : ℝ)|) *
      (Real.exp (b * |((x + c : ℤ) : ℝ)|) * p (x + c)) := fun x => by
    have h := linExp_exp_shift_le hb (x + c) (-c)
    simp only [add_neg_cancel_right, Int.cast_neg, abs_neg] at h
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (hp _)
  have hsum : Summable fun x : ℤ => Real.exp (b * |(x : ℝ)|) * p (x + c) :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (Real.exp_pos _).le (hp _)) hle hs'
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs').trans (le_of_eq ?_)⟩
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight c).tsum_eq (fun x : ℤ => Real.exp (b * |(x : ℝ)|) * p x)

/-- A weight bounded by `C E_b` times `p` is summable when `∑ E_b p` converges. -/
lemma linExp_summable_mul {b C : ℝ} {p w : ℤ → ℝ}
    (hs : Summable fun x : ℤ => Real.exp (b * |(x : ℝ)|) * p x)
    (hw : ∀ x, |w x| ≤ C * Real.exp (b * |(x : ℝ)|)) (hp : ∀ x, 0 ≤ p x) :
    Summable fun x => w x * p x :=
  Summable.of_norm_bounded (hs.mul_left C) fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp x), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hw x) (hp x)

/-- **Summation by parts on `ℤ`** under summability hypotheses only:
`∑ₓ f(x) Δg(x) = ∑ₓ Δf(x) g(x)`. -/
lemma linExp_tsum_mul_lap_eq {f g : ℤ → ℝ}
    (s1 : Summable fun x => f x * g (x + 1)) (s2 : Summable fun x => f x * g (x - 1))
    (s3 : Summable fun x => f x * g x)
    (t1 : Summable fun x => f (x + 1) * g x) (t2 : Summable fun x => f (x - 1) * g x) :
    ∑' x, f x * lap g x = ∑' x, lap f x * g x := by
  have r1 : ∑' x, f x * g (x + 1) = ∑' x, f (x - 1) * g x := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun x => f (x - 1) * g x)]
    simp
  have r2 : ∑' x, f x * g (x - 1) = ∑' x, f (x + 1) * g x := by
    rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq (fun x => f (x + 1) * g x)]
    simp [sub_eq_add_neg]
  have e1 : (fun x => f x * lap g x) = fun x =>
      f x * g (x + 1) + f x * g (x - 1) - 2 * (f x * g x) := by
    funext x; simp only [lap]; ring
  have e2 : (fun x => lap f x * g x) = fun x =>
      f (x - 1) * g x + f (x + 1) * g x - 2 * (f x * g x) := by
    funext x; simp only [lap]; ring
  rw [e1, e2, (s1.add s2).tsum_sub (s3.mul_left 2), s1.tsum_add s2, (t2.add t1).tsum_sub
    (s3.mul_left 2), t2.tsum_add t1, r1, r2]

/-- **The drift series for exponentially growing weights.** If `p ≥ 0`, `∑ E_b p < ∞` and
`|w|, |w'| ≤ C E_b`, then `∑ₓ (w'(x) p(x) + w(x) Δp(x))` converges, equals
`∑ₓ (w' + Δw)(x) p(x)`, and its partial sums are bounded by `C (3 + 2 e^b) ∑ E_b p`. -/
lemma linExp_drift_facts {b C : ℝ} (hb : 0 ≤ b) {p w w' : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hs : Summable fun x : ℤ => Real.exp (b * |(x : ℝ)|) * p x)
    (hw : ∀ x, |w x| ≤ C * Real.exp (b * |(x : ℝ)|))
    (hw' : ∀ x, |w' x| ≤ C * Real.exp (b * |(x : ℝ)|)) :
    Summable (fun x => w' x * p x + w x * lap p x) ∧
    ∑' x, (w' x * p x + w x * lap p x) = ∑' x, (w' x + lap w x) * p x ∧
    ∀ S : Finset ℤ, |∑ x ∈ S, (w' x * p x + w x * lap p x)| ≤
      C * (3 + 2 * Real.exp b) * ∑' x : ℤ, Real.exp (b * |(x : ℝ)|) * p x := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hw 0)
    simpa using this
  set E : ℤ → ℝ := fun x : ℤ => Real.exp (b * |(x : ℝ)|) with hE
  have hE0 : ∀ x, 0 ≤ E x := fun x => (Real.exp_pos _).le
  obtain ⟨hs1, hs1le⟩ := linExp_summable_shift hb hp hs 1
  obtain ⟨hs2, hs2le⟩ := linExp_summable_shift hb hp hs (-1)
  simp only [Int.cast_one, abs_one, mul_one, Int.cast_neg, abs_neg] at hs1le hs2le
  have hp1 : ∀ x, 0 ≤ p (x + 1) := fun x => hp _
  have hp2 : ∀ x, 0 ≤ p (x + -1) := fun x => hp _
  -- shifted weights
  have hwsh : ∀ c : ℤ, ∀ x, |w (x + c)| ≤ (C * Real.exp (b * |(c : ℝ)|)) * E x := fun c x => by
    refine (hw (x + c)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (linExp_exp_shift_le hb x c) hC
  have a1 := linExp_summable_mul hs1 hw hp1
  have a2 := linExp_summable_mul hs2 hw hp2
  have a3 := linExp_summable_mul hs hw hp
  have b1 := linExp_summable_mul hs (hwsh 1) hp
  have b2 := linExp_summable_mul hs (hwsh (-1)) hp
  have a2' : Summable fun x => w x * p (x - 1) := by simpa [sub_eq_add_neg] using a2
  have b2' : Summable fun x => w (x - 1) * p x := by simpa [sub_eq_add_neg] using b2
  have hlapp : Summable fun x => w x * lap p x := by
    have := (a1.add a2').sub (a3.mul_left 2)
    refine this.congr fun x => ?_
    simp only [lap]; ring
  have h1 := linExp_summable_mul hs hw' hp
  refine ⟨h1.add hlapp, ?_, fun S => ?_⟩
  · rw [h1.tsum_add hlapp, linExp_tsum_mul_lap_eq a1 a2' a3 b1 b2']
    have hl : Summable fun x => lap w x * p x := by
      have := (b1.add b2').sub (a3.mul_left 2)
      refine this.congr fun x => ?_
      simp only [lap]; ring
    rw [← h1.tsum_add hl]
    congr 1
    funext x
    ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ x, |w' x * p x + w x * lap p x| ≤
        C * (E x * p x) + C * (E x * p (x + 1) + E x * p (x + -1) + 2 * (E x * p x)) :=
      fun x => by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (hp x), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hw' x) (hp x)
      · have hl : |lap p x| ≤ p (x + 1) + p (x + -1) + 2 * p x := by
          have := hp (x + 1); have := hp (x - 1); have := hp x
          rw [lap, ← sub_eq_add_neg, abs_le]
          constructor <;> linarith
        rw [abs_mul]
        calc |w x| * |lap p x| ≤ (C * E x) * (p (x + 1) + p (x + -1) + 2 * p x) :=
              mul_le_mul (hw x) hl (abs_nonneg _) (mul_nonneg hC (hE0 x))
          _ = _ := by ring
    refine (Finset.sum_le_sum fun x _ => hterm x).trans ?_
    have e0 := hs.sum_le_tsum S fun x _ => mul_nonneg (hE0 x) (hp x)
    have e1 := hs1.sum_le_tsum S fun x _ => mul_nonneg (hE0 x) (hp1 x)
    have e2 := hs2.sum_le_tsum S fun x _ => mul_nonneg (hE0 x) (hp2 x)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    set T := ∑' x, E x * p x
    have := mul_le_mul_of_nonneg_left (e1.trans hs1le) hC
    have := mul_le_mul_of_nonneg_left (e2.trans hs2le) hC
    have := mul_le_mul_of_nonneg_left e0 hC
    nlinarith

/-- `|Δw(x)| ≤ C (2 e^b + 2) E_b(x)` when `|w| ≤ C E_b`, `b ≥ 0`. -/
lemma linExp_abs_lap_le {b C : ℝ} (hb : 0 ≤ b) {w : ℤ → ℝ}
    (hw : ∀ x, |w x| ≤ C * Real.exp (b * |(x : ℝ)|)) (x : ℤ) :
    |lap w x| ≤ C * (2 * Real.exp b + 2) * Real.exp (b * |(x : ℝ)|) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hw 0)
    simpa using this
  have h1 := linExp_exp_shift_le hb x 1
  have h2 := linExp_exp_shift_le hb x (-1)
  simp only [Int.cast_one, abs_one, mul_one, Int.cast_neg, abs_neg] at h1 h2
  have a1 := (hw (x + 1)).trans (mul_le_mul_of_nonneg_left h1 hC)
  have a2 := (hw (x + -1)).trans (mul_le_mul_of_nonneg_left h2 hC)
  have a3 := hw x
  rw [lap, ← sub_eq_add_neg] at *
  rw [sub_eq_add_neg] at a2
  calc |w (x + 1) + w (x - 1) - 2 * w x| ≤ |w (x + 1)| + |w (x + -1)| + 2 * |w x| := by
        rw [← sub_eq_add_neg]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_two]
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by nlinarith

/-- **Bracket term.** If `0 ≤ p ≤ 1` and `w(x)² p(x) ≤ K q(x)` for all `x`, then
`(w(y+1) - w(y))² · 2 p(y) p(y+1) ≤ 4 K (q(y+1) + q(y))`. -/
lemma linExp_bracket_term_le {K : ℝ} {p w q : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) (hwq : ∀ x, w x ^ 2 * p x ≤ K * q x) (y : ℤ) :
    (w (y + 1) - w y) ^ 2 * (2 * p y * p (y + 1)) ≤ 4 * K * (q (y + 1) + q y) := by
  have h1 := hwq y
  have h2 := hwq (y + 1)
  have hp0 := hp y
  have hp1' := hp (y + 1)
  have hq0 := hp1 y
  have hq1 := hp1 (y + 1)
  have hd : (w (y + 1) - w y) ^ 2 ≤ 2 * w (y + 1) ^ 2 + 2 * w y ^ 2 := by
    nlinarith [sq_nonneg (w (y + 1) + w y)]
  have hpq : 0 ≤ p y * p (y + 1) := mul_nonneg hp0 hp1'
  have k1 : w (y + 1) ^ 2 * (p y * p (y + 1)) ≤ w (y + 1) ^ 2 * p (y + 1) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  have k2 : w y ^ 2 * (p y * p (y + 1)) ≤ w y ^ 2 * p y :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hd hpq]

/-- `w(x)² p(x) ≤ C² E_{2a}(x) p(x)` when `|w| ≤ C E_a` and `p ≥ 0`. -/
lemma linExp_sq_mul_le {a C : ℝ} {p w : ℤ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hw : ∀ x, |w x| ≤ C * Real.exp (a * |(x : ℝ)|)) (x : ℤ) :
    w x ^ 2 * p x ≤ C ^ 2 * (Real.exp (2 * a * |(x : ℝ)|) * p x) := by
  have hsq : w x ^ 2 ≤ C ^ 2 * Real.exp (2 * a * |(x : ℝ)|) := by
    rw [← linExp_exp_sq, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw x) 2
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hsq (hp x)

/-- **Tails of a convergent series in `[0, ∞]`**: `∑_{|y| > K} g(y) → 0` as `K → ∞`. -/
lemma linExp_tendsto_tail {g : ℤ → ℝ≥0∞} (hg : ∑' y, g y ≠ ∞) :
    Tendsto (fun K : ℕ => ∑' y, if y ∈ Finset.Icc (-(K : ℤ)) K then 0 else g y) atTop
      (𝓝 0) := by
  have h := (ENNReal.tendsto_tsum_compl_atTop_zero hg).comp Finset.tendsto_Icc_neg
  refine h.congr fun K => ?_
  simp only [Function.comp_apply]
  rw [show (∑' b : {x // x ∉ Finset.Icc (-(K : ℤ)) K}, g b) =
      ∑' b : ({x | x ∉ Finset.Icc (-(K : ℤ)) K} : Set ℤ), g b from rfl, tsum_subtype]
  congr 1
  funext y
  by_cases hy : y ∈ Finset.Icc (-(K : ℤ)) K <;>
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hy, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false]

end QSSEPtoKPZ
