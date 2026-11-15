/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.WaveFunction.Good

/-!
# Lemma 6.4: double sums `∑_{x₁,x₂} z(x₁) z(x₂) f(x₁,x₂)`

Task G1. For a nonnegative summable `z : ℤ → ℝ` (the tilted field `𝔷_n(t,·)`, almost surely),
`corrPair z f = ∑_{x₁} ∑_{x₂} z(x₁) z(x₂) f(x₁,x₂)` (so that `pairZ2 n ψ ω t f` is
`corrPair (zN n ψ ω t) f`):

* `abs_corrPair_le`: `|corrPair z f| ≤ M (∑ z)²` when `|f| ≤ M`;
* `corrPair_add`, `corrPair_sub`, `corrPair_const_mul`: linearity for bounded `f`;
* `corrPair_adjacent`: `corrPair z ((1/2) 𝟙_{|x₂-x₁|=1} Φ) = ∑ₓ z(x) z(x+1) Φ(x,x+1)` for a
  symmetric bounded `Φ` (this turns the term `n^{1/2} Φ_t (1/2) 𝟙_{|r|=1}` into `ℰ_n(t;φ_t)`);
* `corrPair_delta`: `corrPair δ₀ f = f(0,0)` (at time `0`, `𝒵_n(0) = δ₀`).
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace QSSEPtoKPZ

/-- `∑_{x₁,x₂ ∈ ℤ} z(x₁) z(x₂) f(x₁,x₂)`. -/
def corrPair (z : ℤ → ℝ) (f : ℤ → ℤ → ℝ) : ℝ := ∑' a, ∑' b, z a * z b * f a b

lemma pairZ2_eq_corrPair {Ω : Type*} (n : ℝ) (ψ : ℝ → Ω → lp (fun _ : ℤ => ℂ) 2) (ω : Ω) (t : ℝ)
    (f : ℤ → ℤ → ℝ) : pairZ2 n ψ ω t f = corrPair (zN n ψ ω t) f := rfl

/-- `|∑ f| ≤ ∑ g` when `|f| ≤ g` and `g` is summable. -/
lemma corr_abs_tsum_le {f g : ℤ → ℝ} (hg : Summable g) (h : ∀ i, |f i| ≤ g i) :
    |∑' i, f i| ≤ ∑' i, g i := by
  have hf : Summable f := Summable.of_norm_bounded hg (by simpa [Real.norm_eq_abs] using h)
  rw [abs_le]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun i => (abs_le.1 (h i)).1) hg.neg hf
  · exact Summable.tsum_le_tsum (fun i => le_of_abs_le (h i)) hf hg

variable {z : ℤ → ℝ}

lemma corrPair_term_le (hz0 : ∀ x, 0 ≤ z x) {f : ℤ → ℤ → ℝ} {M : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) (a b : ℤ) : |z a * z b * f a b| ≤ z a * M * z b := by
  rw [abs_mul, abs_mul, abs_of_nonneg (hz0 a), abs_of_nonneg (hz0 b)]
  have := mul_le_mul_of_nonneg_left (hf a b) (mul_nonneg (hz0 a) (hz0 b))
  linarith

lemma corrPair_summable_inner (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {f : ℤ → ℤ → ℝ} {M : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) (a : ℤ) : Summable fun b => z a * z b * f a b :=
  Summable.of_norm_bounded (hz.mul_left (z a * M)) fun b => by
    rw [Real.norm_eq_abs]; exact corrPair_term_le hz0 hf a b

lemma abs_corrPair_inner_le (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {f : ℤ → ℤ → ℝ} {M : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) (a : ℤ) :
    |∑' b, z a * z b * f a b| ≤ M * (∑' x, z x) * z a := by
  have := corr_abs_tsum_le (hz.mul_left (z a * M)) (corrPair_term_le hz0 hf a)
  rw [tsum_mul_left] at this
  linarith

lemma corrPair_summable_outer (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {f : ℤ → ℤ → ℝ} {M : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) : Summable fun a => ∑' b, z a * z b * f a b :=
  Summable.of_norm_bounded (hz.mul_left (M * ∑' x, z x)) fun a => by
    rw [Real.norm_eq_abs]; exact abs_corrPair_inner_le hz0 hz hf a

/-- `|∑_{x₁,x₂} z(x₁) z(x₂) f(x₁,x₂)| ≤ M (∑ z)²` when `|f| ≤ M`. -/
theorem abs_corrPair_le (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {f : ℤ → ℤ → ℝ} {M : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) : |corrPair z f| ≤ M * (∑' x, z x) ^ 2 := by
  have := corr_abs_tsum_le (hz.mul_left (M * ∑' x, z x)) (abs_corrPair_inner_le hz0 hz hf)
  rw [tsum_mul_left] at this
  unfold corrPair
  linarith

/-- Linearity: `corrPair z (f + g) = corrPair z f + corrPair z g` for bounded `f, g`. -/
theorem corrPair_add (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {f g : ℤ → ℤ → ℝ} {M N : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) (hg : ∀ a b, |g a b| ≤ N) :
    corrPair z (fun a b => f a b + g a b) = corrPair z f + corrPair z g := by
  unfold corrPair
  have e : ∀ a, ∑' b, z a * z b * (f a b + g a b) =
      ∑' b, z a * z b * f a b + ∑' b, z a * z b * g a b := fun a => by
    rw [← Summable.tsum_add (corrPair_summable_inner hz0 hz hf a)
      (corrPair_summable_inner hz0 hz hg a)]
    congr 1; ext b; ring
  simp only [e]
  exact Summable.tsum_add (corrPair_summable_outer hz0 hz hf) (corrPair_summable_outer hz0 hz hg)

/-- Linearity: `corrPair z (f - g) = corrPair z f - corrPair z g` for bounded `f, g`. -/
theorem corrPair_sub (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {f g : ℤ → ℤ → ℝ} {M N : ℝ}
    (hf : ∀ a b, |f a b| ≤ M) (hg : ∀ a b, |g a b| ≤ N) :
    corrPair z (fun a b => f a b - g a b) = corrPair z f - corrPair z g := by
  unfold corrPair
  have e : ∀ a, ∑' b, z a * z b * (f a b - g a b) =
      ∑' b, z a * z b * f a b - ∑' b, z a * z b * g a b := fun a => by
    rw [← Summable.tsum_sub (corrPair_summable_inner hz0 hz hf a)
      (corrPair_summable_inner hz0 hz hg a)]
    congr 1; ext b; ring
  simp only [e]
  exact Summable.tsum_sub (corrPair_summable_outer hz0 hz hf) (corrPair_summable_outer hz0 hz hg)

/-- `corrPair z (c f) = c corrPair z f` (no summability needed). -/
theorem corrPair_const_mul (c : ℝ) (f : ℤ → ℤ → ℝ) :
    corrPair z (fun a b => c * f a b) = c * corrPair z f := by
  unfold corrPair
  rw [← tsum_mul_left]
  congr 1; ext a
  rw [← tsum_mul_left]
  congr 1; ext b; ring

/-- **The term `(1/2) 𝟙_{|x₂-x₁|=1}`**: for a symmetric bounded `Φ`,
`∑_{x₁,x₂} z(x₁) z(x₂) (1/2) 𝟙_{|x₂-x₁|=1} Φ(x₁,x₂) = ∑ₓ z(x) z(x+1) Φ(x,x+1)`. -/
theorem corrPair_adjacent (hz0 : ∀ x, 0 ≤ z x) (hz : Summable z) {Φ : ℤ → ℤ → ℝ} {M : ℝ}
    (hΦ : ∀ a b, Φ a b = Φ b a) (hM : ∀ a b, |Φ a b| ≤ M) :
    corrPair z (fun a b => 1 / 2 * (if |b - a| = 1 then 1 else 0) * Φ a b) =
      ∑' x, z x * z (x + 1) * Φ x (x + 1) := by
  set P : ℤ → ℝ := fun a => 1 / 2 * (z a * z (a + 1) * Φ a (a + 1))
  have hinner : ∀ a, ∑' b, z a * z b * (1 / 2 * (if |b - a| = 1 then 1 else 0) * Φ a b) =
      P a + P (a - 1) := by
    intro a
    have e : (fun b => z a * z b * (1 / 2 * (if |b - a| = 1 then 1 else 0) * Φ a b)) =
        fun b => (if b = a + 1 then P a else 0) + (if b = a - 1 then P (a - 1) else 0) := by
      ext b
      simp only [P]
      by_cases h1 : b = a + 1
      · subst h1
        have : ¬ (a + 1 = a - 1) := by omega
        simp [this]
        ring
      · by_cases h2 : b = a - 1
        · subst h2
          have : |a - 1 - a| = 1 := by simp
          simp only [this, h1, ↓reduceIte, sub_add_cancel, hΦ a (a - 1)]
          ring
        · have : ¬ |b - a| = 1 := by
            rw [abs_eq (zero_le_one' ℤ)]; omega
          simp [this, h1, h2]
    rw [e, Summable.tsum_add (hasSum_ite_eq _ _).summable (hasSum_ite_eq _ _).summable,
      tsum_ite_eq, tsum_ite_eq]
  have hP : Summable P := by
    refine Summable.of_norm_bounded (hz.mul_left (1 / 2 * ((∑' x, z x) * M))) fun a => ?_
    rw [Real.norm_eq_abs]
    simp only [P]
    have h1 : z (a + 1) ≤ ∑' x, z x := hz.le_tsum _ fun x _ => hz0 x
    have h2 := corrPair_term_le hz0 hM a (a + 1)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : z a * M * z (a + 1) ≤ z a * M * ∑' x, z x :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (hz0 a) hM0)
    nlinarith [hz0 a]
  have hshift : ∑' a, P (a - 1) = ∑' a, P a :=
    (Equiv.subRight (1 : ℤ)).tsum_eq P
  unfold corrPair
  simp only [hinner]
  have hP' : Summable fun a => P (a - 1) := (Equiv.subRight (1 : ℤ)).summable_iff.2 hP
  rw [Summable.tsum_add hP hP', hshift]
  simp only [P]
  rw [tsum_mul_left]
  ring

/-- At a Dirac mass at `0`: `corrPair δ₀ f = f(0,0)`. -/
theorem corrPair_delta (hz : ∀ x, z x = if x = 0 then 1 else 0) (f : ℤ → ℤ → ℝ) :
    corrPair z f = f 0 0 := by
  unfold corrPair
  have hi : ∀ a, ∑' b, z a * z b * f a b = z a * f a 0 := fun a => by
    rw [tsum_eq_single 0 fun b hb => by simp [hz b, hb]]
    simp [hz 0]
  simp only [hi]
  rw [tsum_eq_single 0 fun a ha => by simp [hz a, ha]]
  simp [hz 0]

end QSSEPtoKPZ
