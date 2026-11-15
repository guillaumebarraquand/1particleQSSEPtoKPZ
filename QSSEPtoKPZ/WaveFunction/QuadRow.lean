/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.QuadSeries

/-!
# The weights of the martingale part of a quadratic functional (task D6)

The martingale part of `∑_{x₁,x₂} f(x₁,x₂) P(x₁) P(x₂)` is `∫ ∑ₓ (V(x+1) - V(x)) dJ(x)`, with
the random weight `V(x) = 2 ∑_{x'} f(x,x') P(x')` (`2 quadRow f P x`), so that
`V(x+1) - V(x) = 2 D(x)` with `D` the series of the last term of (2.8). Under `QuadDecay` and
`|f| ≤ K W W`:

* `QuadDecay.summable_row`, `QuadDecay.abs_row_le`, `QuadDecay.abs_sum_row_le`: the rows
  converge absolutely and `|∑_{x' ∈ S} f(x,x') P(x')| ≤ K R σ W(x)` with `σ = ∑ ρ`;
* `QuadDecay.summable_sq_mul`: `|v| ≤ L W` implies `∑ v(x)² P(x) < ∞`;
* `quad_tsum_diff_sq_le`: for `0 ≤ P ≤ 1`,
  `∑_y (v(y+1) - v(y))² · 2 P(y) P(y+1) ≤ 8 ∑_y v(y)² P(y)` (the bracket density of
  `∫ ∑_y (v(y+1) - v(y)) dJ(y)` is controlled by the weight).
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace QSSEPtoKPZ

/-- The row sums `∑_{x'} f(x,x') P(x')`. -/
def quadRow (f : ℤ → ℤ → ℝ) (P : ℤ → ℝ) (x : ℤ) : ℝ := ∑' x', f x x' * P x'

/-- `σ = ∑ₓ ρ(x)`. -/
def quadSigma : ℝ := ∑' x, quadRho x

lemma quadSigma_nonneg : 0 ≤ quadSigma := tsum_nonneg fun x => (quadRho_pos x).le

namespace QuadDecay

variable {a R : ℝ} {P : ℤ → ℝ}

/-- `|f(x,x') P(x')| ≤ K R W(x) ρ(x')`. -/
lemma abs_row_term_le (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x x' : ℤ) :
    |f x x' * P x'| ≤ K * R * quadW a x * quadRho x' := by
  rw [abs_mul, abs_of_nonneg (h.nonneg x')]
  have w := h.w_le ha x'
  have := quadW_pos a x
  calc |f x x'| * P x' ≤ K * quadW a x * quadW a x' * P x' :=
        mul_le_mul_of_nonneg_right (hf x x') (h.nonneg x')
    _ = K * quadW a x * (quadW a x' * P x') := by ring
    _ ≤ K * quadW a x * (R * quadRho x') :=
        mul_le_mul_of_nonneg_left w (mul_nonneg hK this.le)
    _ = _ := by ring

/-- The rows converge absolutely. -/
lemma summable_row (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ) :
    Summable fun x' => f x x' * P x' :=
  Summable.of_norm_bounded (summable_quadRho.mul_left (K * R * quadW a x)) fun x' => by
    rw [Real.norm_eq_abs]; exact h.abs_row_term_le ha hK hf x x'

/-- `∑_{x'} |f(x,x') P(x')| ≤ K R σ W(x)`. -/
lemma tsum_abs_row_le (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ) :
    ∑' x', |f x x' * P x'| ≤ K * R * quadSigma * quadW a x := by
  have hs := (h.summable_row ha hK hf x).abs
  calc ∑' x', |f x x' * P x'| ≤ ∑' x', K * R * quadW a x * quadRho x' :=
        hs.tsum_le_tsum (h.abs_row_term_le ha hK hf x) (summable_quadRho.mul_left _)
    _ = _ := by rw [tsum_mul_left, quadSigma]; ring

/-- `|∑_{x'} f(x,x') P(x')| ≤ K R σ W(x)`. -/
lemma abs_row_le (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ) :
    |quadRow f P x| ≤ K * R * quadSigma * quadW a x := by
  have hs := (h.summable_row ha hK hf x)
  have key : |∑' x', f x x' * P x'| ≤ ∑' x', |f x x' * P x'| := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun x' => f x x' * P x')
      (by simpa [Real.norm_eq_abs] using hs.abs)
  exact key.trans (h.tsum_abs_row_le ha hK hf x)

/-- `|∑_{x' ∈ S} f(x,x') P(x')| ≤ K R σ W(x)` for every finite `S`. -/
lemma abs_sum_row_le (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ)
    (S : Finset ℤ) : |∑ x' ∈ S, f x x' * P x'| ≤ K * R * quadSigma * quadW a x := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (h.tsum_abs_row_le ha hK hf x)
  exact (h.summable_row ha hK hf x).abs.sum_le_tsum S fun _ _ => abs_nonneg _

/-- The difference of two consecutive rows is a row:
`∑_{x'} (f(x+1,x') - f(x,x')) P(x') = V(x+1) - V(x)`. -/
lemma tsum_row_sub (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ) :
    ∑' x', (f (x + 1) x' - f x x') * P x' = quadRow f P (x + 1) - quadRow f P x := by
  rw [quadRow, quadRow, ← (h.summable_row ha hK hf (x + 1)).tsum_sub (h.summable_row ha hK hf x)]
  congr 1; funext x'; ring

/-- `|∑_{x'} (f(x+1,x') - f(x,x')) P(x')| ≤ 2 e^a K R σ W(x)`. -/
lemma abs_row_sub_le (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ) :
    |∑' x', (f (x + 1) x' - f x x') * P x'| ≤
      2 * Real.exp a * K * R * quadSigma * quadW a x := by
  rw [h.tsum_row_sub ha hK hf x]
  have h1 := h.abs_row_le ha hK hf (x + 1)
  have h2 := h.abs_row_le ha hK hf x
  have e := quadW_add_le ha x 1 (by norm_num)
  have hea := Real.one_le_exp ha
  have hc : 0 ≤ K * R * quadSigma := mul_nonneg (mul_nonneg hK h.R_nonneg) quadSigma_nonneg
  have w := quadW_pos a x
  have := mul_le_mul_of_nonneg_left e hc
  have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left w.le hea) hc
  calc _ ≤ |quadRow f P (x + 1)| + |quadRow f P x| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- `∑_{x'} |f(x+1,x') - f(x,x')| P(x') < ∞`. -/
lemma summable_abs_row_sub (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x : ℤ) :
    Summable fun x' => |f (x + 1) x' - f x x'| * P x' := by
  refine (((h.summable_row ha hK hf (x + 1)).abs).add
    (h.summable_row ha hK hf x).abs).of_nonneg_of_le
    (fun x' => mul_nonneg (abs_nonneg _) (h.nonneg x')) fun x' => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (h.nonneg x'), ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_sub _ _) (h.nonneg x')

/-- `|v| ≤ L W` implies `v(x)² P(x) ≤ L² R ρ(x)`. -/
lemma sq_mul_le (h : QuadDecay a R P) {v : ℤ → ℝ} {L : ℝ}
    (hv : ∀ x, |v x| ≤ L * quadW a x) (x : ℤ) : v x ^ 2 * P x ≤ L ^ 2 * R * quadRho x := by
  have h1 : v x ^ 2 ≤ L ^ 2 * quadW a x ^ 2 := by
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hv x) 2
  calc v x ^ 2 * P x ≤ L ^ 2 * quadW a x ^ 2 * P x := mul_le_mul_of_nonneg_right h1 (h.nonneg x)
    _ = L ^ 2 * (quadW a x ^ 2 * P x) := by ring
    _ ≤ L ^ 2 * (R * quadRho x) := mul_le_mul_of_nonneg_left (h.sq_le x) (sq_nonneg _)
    _ = _ := by ring

/-- `|v| ≤ L W` implies `∑ v(x)² P(x) < ∞`. -/
lemma summable_sq_mul (h : QuadDecay a R P) {v : ℤ → ℝ} {L : ℝ}
    (hv : ∀ x, |v x| ≤ L * quadW a x) : Summable fun x => v x ^ 2 * P x :=
  (summable_quadRho.mul_left (L ^ 2 * R)).of_nonneg_of_le
    (fun x => mul_nonneg (sq_nonneg _) (h.nonneg x)) (h.sq_mul_le hv)

end QuadDecay

/-- **Bracket density of `∫ ∑_y (v(y+1) - v(y)) dJ(y)`.** For `0 ≤ P ≤ 1` and
`∑ v² P < ∞`: the series `∑_y (v(y+1) - v(y))² · 2 P(y) P(y+1)` converges and is at most
`8 ∑_y v(y)² P(y)`. -/
lemma quad_tsum_diff_sq_le {P v : ℤ → ℝ} (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    (hv : Summable fun x => v x ^ 2 * P x) :
    Summable (fun y => (v (y + 1) - v y) ^ 2 * (2 * P y * P (y + 1))) ∧
    ∑' y, (v (y + 1) - v y) ^ 2 * (2 * P y * P (y + 1)) ≤ 8 * ∑' y, v y ^ 2 * P y := by
  have hv1 : Summable fun y => v (y + 1) ^ 2 * P (y + 1) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.2 hv
  have hterm : ∀ y, (v (y + 1) - v y) ^ 2 * (2 * P y * P (y + 1)) ≤
      4 * (v (y + 1) ^ 2 * P (y + 1) + v y ^ 2 * P y) := by
    intro y
    have p0 := hP0 y; have p1 := hP0 (y + 1); have q0 := hP1 y; have q1 := hP1 (y + 1)
    have hd : (v (y + 1) - v y) ^ 2 ≤ 2 * v (y + 1) ^ 2 + 2 * v y ^ 2 := by
      nlinarith [sq_nonneg (v (y + 1) + v y)]
    have hpq : 0 ≤ P y * P (y + 1) := mul_nonneg p0 p1
    have k1 : v (y + 1) ^ 2 * (P y * P (y + 1)) ≤ v (y + 1) ^ 2 * P (y + 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    have k2 : v y ^ 2 * (P y * P (y + 1)) ≤ v y ^ 2 * P y :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hd hpq]
  have hs : Summable fun y => (v (y + 1) - v y) ^ 2 * (2 * P y * P (y + 1)) :=
    ((hv1.add hv).mul_left 4).of_nonneg_of_le
      (fun y => mul_nonneg (sq_nonneg _) (by have := hP0 y; have := hP0 (y + 1); positivity))
      hterm
  refine ⟨hs, ?_⟩
  have e : ∑' y, v (y + 1) ^ 2 * P (y + 1) = ∑' y, v y ^ 2 * P y :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun y => v y ^ 2 * P y)
  calc _ ≤ ∑' y, 4 * (v (y + 1) ^ 2 * P (y + 1) + v y ^ 2 * P y) :=
        hs.tsum_le_tsum hterm ((hv1.add hv).mul_left 4)
    _ = _ := by rw [tsum_mul_left, hv1.tsum_add hv, e]; ring

end QSSEPtoKPZ
