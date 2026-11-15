/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.QuadSeries

/-!
# The drift of a quadratic functional of `P` (task D6)

The product rule for `f(x₁,x₂) P(x₁) P(x₂)` gives the drift
`∂ₜf P(x₁) P(x₂) + f (P(x₁) ΔP(x₂) + P(x₂) ΔP(x₁) + X(x₁,x₂))`
(`quadDriftTerm`), where `X(x₁,x₂) = ∑ᵢ (c_{x₁-1} - c_{x₁})ᵢ (c_{x₂-1} - c_{x₂})ᵢ` is the
covariation density of `P(x₁)` and `P(x₂)`, computed with (2.5) in `quadCross`:
`X(x,x) = 2 P(x-1) P(x) + 2 P(x) P(x+1)`, `X(x,x-1) = -2 P(x-1) P(x)`,
`X(x,x+1) = -2 P(x) P(x+1)`, and `0` otherwise.

`QuadDecay.hasSum_quadDriftTerm`: under exponential decay of `P` and exponential growth of `f`,
the drift summed over `ℤ²` is `∑_{x₁,x₂} (∂ₜf + 𝒬f)(x₁,x₂) P(x₁) P(x₂)`: two summations by parts
(the Laplacians, `quad_tsum_lap_snd`, `quad_tsum_lap_fst`) and the identification of the
covariation terms with the jump part of `𝒬` (`QuadDecay.tsum_mul_quadCross`). This is the formal
computation of the article's proof of Lemma 2.3 (2), done directly on `ℤ²` with absolutely
convergent series (no boundary terms).
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace QSSEPtoKPZ

/-- The covariation density `d⟨P(x₁), P(x₂)⟩/dt` of (2.5), as a function of `P`. -/
def quadCross (P : ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ :=
  (if x₂ = x₁ then 2 * P (x₁ - 1) * P x₁ + 2 * P x₁ * P (x₁ + 1) else 0) -
  (if x₂ = x₁ - 1 then 2 * P (x₁ - 1) * P x₁ else 0) -
  (if x₂ = x₁ + 1 then 2 * P x₁ * P (x₁ + 1) else 0)

/-- The drift of `f(x₁,x₂) P(x₁) P(x₂)` given by the product rule. -/
def quadDriftTerm (f f' : ℤ → ℤ → ℝ) (P : ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ :=
  f' x₁ x₂ * P x₁ * P x₂ + f x₁ x₂ * (P x₁ * lap P x₂ + P x₂ * lap P x₁ + quadCross P x₁ x₂)

/-- `|X(x₁,x₂)| ≤ 4 P₃(x₁) P₃(x₂)`. -/
lemma abs_quadCross_le {P : ℤ → ℝ} (hP : ∀ x, 0 ≤ P x) (x₁ x₂ : ℤ) :
    |quadCross P x₁ x₂| ≤ 4 * quadP3 P x₁ * quadP3 P x₂ := by
  obtain ⟨a1, b1, c1⟩ := le_quadP3 hP x₁
  obtain ⟨a2, b2, c2⟩ := le_quadP3 hP x₂
  have q1 := quadP3_nonneg hP x₁
  have q2 := quadP3_nonneg hP x₂
  have p0 := hP (x₁ - 1); have p1 := hP x₁; have p2 := hP (x₁ + 1)
  unfold quadCross
  split_ifs with h1 h2 h3 h3 h2 h3 h3
  all_goals try (exfalso; omega)
  · subst h1
    rw [sub_zero, sub_zero, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul a1 b2 p1 q1, mul_le_mul b1 c2 p2 q1]
  · subst h2
    simp only [zero_sub, sub_zero, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    have : x₁ - 1 + 1 = x₁ := by omega
    rw [this] at c2
    nlinarith [mul_le_mul b2 b1 p1 q2]
  · subst h3
    simp only [zero_sub, sub_zero, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul b1 b2 p2 q1]
  · simp only [sub_zero, abs_zero]
    positivity

namespace QuadDecay

variable {a R : ℝ} {P : ℤ → ℝ}

/-- `|F P(y₁) P(y₂)| ≤ c W(x₁) W(x₂) P₃(x₁) P₃(x₂)` when `|F| ≤ c W(x₁) W(x₂)`,
`P(y₁) ≤ P₃(x₁)`, `P(y₂) ≤ P₃(x₂)`. -/
lemma abs_mul_le (h : QuadDecay a R P) {F c : ℝ} {x₁ x₂ y₁ y₂ : ℤ}
    (hF : |F| ≤ c * quadW a x₁ * quadW a x₂) (hy₁ : P y₁ ≤ quadP3 P x₁)
    (hy₂ : P y₂ ≤ quadP3 P x₂) :
    |F * P y₁ * P y₂| ≤ c * quadW a x₁ * quadW a x₂ * quadP3 P x₁ * quadP3 P x₂ := by
  rw [abs_mul, abs_mul, abs_of_nonneg (h.nonneg y₁), abs_of_nonneg (h.nonneg y₂)]
  have := h.nonneg y₁; have := h.nonneg y₂
  have := (abs_nonneg F).trans hF
  have := quadP3_nonneg h.nonneg x₁
  calc |F| * P y₁ * P y₂ ≤ (c * quadW a x₁ * quadW a x₂) * quadP3 P x₁ * P y₂ := by gcongr
    _ ≤ _ := by gcongr

end QuadDecay

/-- `|Δ₂ f(x₁,x₂)| ≤ 4 e^a K W(x₁) W(x₂)` when `|f| ≤ K W W`. -/
lemma quad_abs_lap_snd_le {a K : ℝ} (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ}
    (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x₁ x₂ : ℤ) :
    |lap (f x₁) x₂| ≤ 4 * Real.exp a * K * quadW a x₁ * quadW a x₂ := by
  have hK : 0 ≤ K * quadW a x₁ := by
    have := (abs_nonneg _).trans (hf x₁ x₂)
    have h2 := quadW_pos a x₂
    by_contra hc; push Not at hc; nlinarith
  have e1 := quadW_add_le ha x₂ 1 (by norm_num)
  have e2 := quadW_add_le ha x₂ (-1) (by norm_num)
  rw [← sub_eq_add_neg] at e2
  have hea := Real.one_le_exp ha
  have w2 := quadW_pos a x₂
  have k1 := hf x₁ (x₂ + 1); have k2 := hf x₁ (x₂ - 1); have k3 := hf x₁ x₂
  unfold lap
  have t1 : K * quadW a x₁ * quadW a (x₂ + 1) ≤ K * quadW a x₁ * (Real.exp a * quadW a x₂) :=
    mul_le_mul_of_nonneg_left e1 hK
  have t2 : K * quadW a x₁ * quadW a (x₂ - 1) ≤ K * quadW a x₁ * (Real.exp a * quadW a x₂) :=
    mul_le_mul_of_nonneg_left e2 hK
  have t3 : K * quadW a x₁ * quadW a x₂ ≤ K * quadW a x₁ * (Real.exp a * quadW a x₂) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left w2.le hea) hK
  calc |f x₁ (x₂ + 1) + f x₁ (x₂ - 1) - 2 * f x₁ x₂|
      ≤ |f x₁ (x₂ + 1)| + |f x₁ (x₂ - 1)| + 2 * |f x₁ x₂| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_two]
        exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by nlinarith

/-- `|Δ₁ f(x₁,x₂)| ≤ 4 e^a K W(x₁) W(x₂)` when `|f| ≤ K W W`. -/
lemma quad_abs_lap_fst_le {a K : ℝ} (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ}
    (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x₁ x₂ : ℤ) :
    |lap (fun y => f y x₂) x₁| ≤ 4 * Real.exp a * K * quadW a x₁ * quadW a x₂ := by
  have := quad_abs_lap_snd_le ha (f := fun x y => f y x)
    (fun x y => by rw [mul_right_comm]; exact hf y x) x₂ x₁
  rw [mul_right_comm] at this
  exact this

/-- The jump part of `𝒬`: `|𝟙_{|x₁-x₂|=1} [f(x₁,x₁) + f(x₂,x₂) - 2 f(x₁,x₂)]| ≤ 4 e^a K W W`. -/
lemma quad_abs_jump_le {a K : ℝ} (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ}
    (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x₁ x₂ : ℤ) :
    |if |x₁ - x₂| = 1 then f x₁ x₁ + f x₂ x₂ - 2 * f x₁ x₂ else 0| ≤
      4 * Real.exp a * K * quadW a x₁ * quadW a x₂ := by
  have w1 := quadW_pos a x₁; have w2 := quadW_pos a x₂
  have hea := Real.one_le_exp ha
  have hK : 0 ≤ K := by
    have := (abs_nonneg _).trans (hf x₁ x₂)
    by_contra hc; push Not at hc
    have : K * quadW a x₁ * quadW a x₂ < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc w1) w2
    linarith
  split_ifs with hx
  · have e1 : quadW a x₁ ≤ Real.exp a * quadW a x₂ := by
      have := quadW_add_le ha x₂ (x₁ - x₂) hx.le
      rwa [add_sub_cancel] at this
    have e2 : quadW a x₂ ≤ Real.exp a * quadW a x₁ := by
      have := quadW_add_le ha x₁ (x₂ - x₁) (by rw [abs_sub_comm]; exact hx.le)
      rwa [add_sub_cancel] at this
    have k1 := hf x₁ x₁; have k2 := hf x₂ x₂; have k3 := hf x₁ x₂
    have t1 : K * quadW a x₁ * quadW a x₁ ≤ Real.exp a * K * quadW a x₁ * quadW a x₂ := by
      have := mul_le_mul_of_nonneg_left e1 (mul_nonneg hK w1.le); nlinarith
    have t2 : K * quadW a x₂ * quadW a x₂ ≤ Real.exp a * K * quadW a x₁ * quadW a x₂ := by
      have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hK w2.le); nlinarith
    have t3 : K * quadW a x₁ * quadW a x₂ ≤ Real.exp a * K * quadW a x₁ * quadW a x₂ := by
      have := mul_nonneg (mul_nonneg hK w1.le) w2.le; nlinarith
    calc |f x₁ x₁ + f x₂ x₂ - 2 * f x₁ x₂| ≤ |f x₁ x₁| + |f x₂ x₂| + 2 * |f x₁ x₂| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_two]
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  · rw [abs_zero]
    positivity

/-! ### Summation by parts on `ℤ²` -/

/-- `Δ(c g) = c Δg`. -/
lemma lap_mul_const (g : ℤ → ℝ) (c : ℝ) (x : ℤ) :
    lap (fun y => g y * c) x = lap g x * c := by
  unfold lap; ring

/-- **Summation by parts in the second variable**:
`∑_{x₁,x₂} F(x₁,x₂) ΔP(x₂) = ∑_{x₁,x₂} Δ₂F(x₁,x₂) P(x₂)`. -/
lemma quad_tsum_lap_snd (F : ℤ → ℤ → ℝ) (P : ℤ → ℝ)
    (h₁ : Summable fun p : ℤ × ℤ => F p.1 p.2 * P (p.2 + 1))
    (h₂ : Summable fun p : ℤ × ℤ => F p.1 p.2 * P (p.2 - 1))
    (h₃ : Summable fun p : ℤ × ℤ => F p.1 p.2 * P p.2) :
    ∑' p : ℤ × ℤ, F p.1 p.2 * lap P p.2 = ∑' p : ℤ × ℤ, lap (F p.1) p.2 * P p.2 := by
  set e₁ : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.refl ℤ).prodCongr (Equiv.subRight 1) with he₁
  set e₂ : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.refl ℤ).prodCongr (Equiv.addRight 1) with he₂
  have r₁ : ∑' p : ℤ × ℤ, F p.1 p.2 * P (p.2 + 1) =
      ∑' p : ℤ × ℤ, F p.1 (p.2 - 1) * P p.2 := by
    rw [← e₁.tsum_eq (fun p : ℤ × ℤ => F p.1 p.2 * P (p.2 + 1))]
    simp [he₁]
  have r₂ : ∑' p : ℤ × ℤ, F p.1 p.2 * P (p.2 - 1) =
      ∑' p : ℤ × ℤ, F p.1 (p.2 + 1) * P p.2 := by
    rw [← e₂.tsum_eq (fun p : ℤ × ℤ => F p.1 p.2 * P (p.2 - 1))]
    simp [he₂]
  have s₁ : Summable fun p : ℤ × ℤ => F p.1 (p.2 - 1) * P p.2 := by
    have := e₁.summable_iff.2 h₁
    simpa [he₁, Function.comp_def] using this
  have s₂ : Summable fun p : ℤ × ℤ => F p.1 (p.2 + 1) * P p.2 := by
    have := e₂.summable_iff.2 h₂
    simpa [he₂, Function.comp_def] using this
  have eL : (fun p : ℤ × ℤ => F p.1 p.2 * lap P p.2) = fun p =>
      F p.1 p.2 * P (p.2 + 1) + F p.1 p.2 * P (p.2 - 1) - 2 * (F p.1 p.2 * P p.2) := by
    funext p; unfold lap; ring
  have eR : (fun p : ℤ × ℤ => lap (F p.1) p.2 * P p.2) = fun p =>
      F p.1 (p.2 + 1) * P p.2 + F p.1 (p.2 - 1) * P p.2 - 2 * (F p.1 p.2 * P p.2) := by
    funext p; unfold lap; ring
  rw [eL, eR, (h₁.add h₂).tsum_sub (h₃.mul_left 2), h₁.tsum_add h₂,
    (s₂.add s₁).tsum_sub (h₃.mul_left 2), s₂.tsum_add s₁, r₁, r₂]
  ring

/-- **Summation by parts in the first variable**:
`∑_{x₁,x₂} F(x₁,x₂) ΔP(x₁) = ∑_{x₁,x₂} Δ₁F(x₁,x₂) P(x₁)`. -/
lemma quad_tsum_lap_fst (F : ℤ → ℤ → ℝ) (P : ℤ → ℝ)
    (h₁ : Summable fun p : ℤ × ℤ => F p.1 p.2 * P (p.1 + 1))
    (h₂ : Summable fun p : ℤ × ℤ => F p.1 p.2 * P (p.1 - 1))
    (h₃ : Summable fun p : ℤ × ℤ => F p.1 p.2 * P p.1) :
    ∑' p : ℤ × ℤ, F p.1 p.2 * lap P p.1 =
      ∑' p : ℤ × ℤ, lap (fun y => F y p.2) p.1 * P p.1 := by
  set e : ℤ × ℤ ≃ ℤ × ℤ := Equiv.prodComm ℤ ℤ with he
  have sw : ∀ g : ℤ × ℤ → ℝ, ∑' p : ℤ × ℤ, g p = ∑' p : ℤ × ℤ, g (p.2, p.1) := fun g =>
    (e.tsum_eq g).symm
  have sws : ∀ g : ℤ × ℤ → ℝ, Summable g → Summable fun p : ℤ × ℤ => g (p.2, p.1) :=
    fun g hg => e.summable_iff.2 hg
  rw [sw, sw (fun p : ℤ × ℤ => lap (fun y => F y p.2) p.1 * P p.1)]
  exact quad_tsum_lap_snd (fun x y => F y x) P (sws _ h₁) (sws _ h₂) (sws _ h₃)

/-! ### The covariation terms and the jumps of `𝒬` -/

/-- A family on `ℤ²` supported on the graph of `e`. -/
lemma quad_hasSum_graph {H : ℤ × ℤ → ℝ} (e : ℤ → ℤ) {s : ℝ}
    (h : HasSum (fun x => H (x, e x)) s) :
    HasSum (fun p : ℤ × ℤ => if p.2 = e p.1 then H p else 0) s := by
  have hg : Function.Injective (fun x : ℤ => (x, e x)) := fun x y hxy =>
    congrArg Prod.fst hxy
  refine (hg.hasSum_iff fun p hp => ?_).1 ?_
  · split_ifs with h'
    · exact absurd ⟨p.1, by ext <;> simp [h']⟩ hp
    · rfl
  · simpa [Function.comp_def] using h

/-- `𝟙_{|x₁ - x₂| = 1} = 𝟙_{x₂ = x₁ + 1} + 𝟙_{x₂ = x₁ - 1}`. -/
lemma quad_ite_abs_eq_one (x₁ x₂ : ℤ) (v : ℝ) :
    (if |x₁ - x₂| = 1 then v else 0) =
      (if x₂ = x₁ + 1 then v else 0) + (if x₂ = x₁ - 1 then v else 0) := by
  have key : |x₁ - x₂| = 1 ↔ (x₂ = x₁ + 1 ∨ x₂ = x₁ - 1) := by
    rw [abs_eq (by norm_num)]; omega
  split_ifs with h0 h1 h2 h2 h1 h2 h2 <;> first
    | (exfalso; omega)
    | simp

namespace QuadDecay

variable {a R : ℝ} {P : ℤ → ℝ}

/-- **Domination on `ℤ`.** If `|g(y)| ≤ K W(y)² P₃(y)²` with `K ≥ 0`, then `g` is summable. -/
lemma summable_one_of_le (h : QuadDecay a R P) (ha : 0 ≤ a) {g : ℤ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ y, |g y| ≤ K * quadW a y * quadW a y * quadP3 P y * quadP3 P y) : Summable g := by
  refine Summable.of_norm_bounded
    (summable_quadRho3.mul_left (K * (3 * Real.exp a * R) ^ 2 * 3)) fun y => ?_
  rw [Real.norm_eq_abs]
  refine (hg y).trans ?_
  have hW : 0 ≤ K * quadW a y * quadW a y :=
    mul_nonneg (mul_nonneg hK (quadW_pos a y).le) (quadW_pos a y).le
  have := h.pair_le ha (F := K * quadW a y * quadW a y) (K := K) y y (by rw [abs_of_nonneg hW])
  rw [abs_of_nonneg hW] at this
  refine this.trans ?_
  have r := quadRho3_nonneg y; have r3 := quadRho3_le_three y
  have : 0 ≤ K * (3 * Real.exp a * R) ^ 2 := mul_nonneg hK (sq_nonneg _)
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right r3 r) this
  nlinarith

/-- **The covariation terms are the jumps of `𝒬`**:
`∑_{x₁,x₂} f(x₁,x₂) X(x₁,x₂) = ∑_{x₁,x₂} 𝟙_{|x₁-x₂|=1} [f(x₁,x₁) + f(x₂,x₂) - 2 f(x₁,x₂)] P(x₁) P(x₂)`
(both sides reduce to series over the bonds `(y, y+1)`). -/
theorem hasSum_mul_quadCross (h : QuadDecay a R P) (ha : 0 ≤ a) {f : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) :
    HasSum (fun p : ℤ × ℤ => f p.1 p.2 * quadCross P p.1 p.2)
      (∑' p : ℤ × ℤ, (if |p.1 - p.2| = 1 then f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2 else 0) *
        P p.1 * P p.2) := by
  set u : ℤ → ℝ := fun y => P y * P (y + 1) with hu
  set α : ℤ → ℝ := fun y => f y y * u y with hα
  set β : ℤ → ℝ := fun y => f (y + 1) (y + 1) * u y with hβ
  set γ : ℤ → ℝ := fun y => f (y + 1) y * u y with hγ
  set δ : ℤ → ℝ := fun y => f y (y + 1) * u y with hδ
  have hea := Real.one_le_exp ha
  have hl := fun x => le_quadP3 h.nonneg x
  have hb : ∀ c c' : ℤ, |c| ≤ 1 → |c'| ≤ 1 → ∀ y, |f (y + c) (y + c') * u y| ≤
      (Real.exp a ^ 2 * K) * quadW a y * quadW a y * quadP3 P y * quadP3 P y := by
    intro c c' hc hc' y
    have e1 := quadW_add_le ha y c hc
    have e2 := quadW_add_le ha y c' hc'
    have k := hf (y + c) (y + c')
    have w := quadW_pos a y
    have p0 := quadP3_nonneg h.nonneg y
    have hfb : |f (y + c) (y + c')| ≤ (Real.exp a ^ 2 * K) * quadW a y * quadW a y := by
      refine k.trans ?_
      have := mul_le_mul e1 e2 (quadW_pos a _).le (by positivity)
      calc K * quadW a (y + c) * quadW a (y + c') = K * (quadW a (y + c) * quadW a (y + c')) :=
            by ring
        _ ≤ K * ((Real.exp a * quadW a y) * (Real.exp a * quadW a y)) :=
            mul_le_mul_of_nonneg_left this hK
        _ = _ := by ring
    rw [hu, ← mul_assoc]
    exact h.abs_mul_le hfb (hl y).2.1 (hl y).2.2
  have hK' : 0 ≤ Real.exp a ^ 2 * K := mul_nonneg (sq_nonneg _) hK
  have sα : Summable α := h.summable_one_of_le ha hK' fun y => by
    have := hb 0 0 (by norm_num) (by norm_num) y
    simp only [add_zero] at this
    exact this
  have sβ : Summable β := h.summable_one_of_le ha hK' fun y => by
    exact hb 1 1 (by norm_num) (by norm_num) y
  have sγ : Summable γ := h.summable_one_of_le ha hK' fun y => by
    have := hb 1 0 (by norm_num) (by norm_num) y
    simp only [add_zero] at this
    exact this
  have sδ : Summable δ := h.summable_one_of_le ha hK' fun y => by
    have := hb 0 1 (by norm_num) (by norm_num) y
    simp only [add_zero] at this
    exact this
  have shift : ∀ g : ℤ → ℝ, Summable g → HasSum (fun x => g (x - 1)) (∑' y, g y) := fun g hg => by
    have := (Equiv.subRight (1 : ℤ)).hasSum_iff.2 hg.hasSum
    simpa [Function.comp_def] using this
  -- the left side
  have hA := quad_hasSum_graph (H := fun p : ℤ × ℤ =>
      f p.1 p.2 * (2 * P (p.1 - 1) * P p.1 + 2 * P p.1 * P (p.1 + 1))) (fun x => x)
      (s := 2 * ∑' y, β y + 2 * ∑' y, α y) (by
        convert ((shift β sβ).mul_left 2).add (sα.hasSum.mul_left 2) using 1
        funext x
        simp only [hβ, hα, hu, sub_add_cancel]
        ring)
  have hB := quad_hasSum_graph (H := fun p : ℤ × ℤ => f p.1 p.2 * (2 * P (p.1 - 1) * P p.1))
      (fun x => x - 1) (s := 2 * ∑' y, γ y) (by
        convert (shift γ sγ).mul_left 2 using 1
        funext x
        simp only [hγ, hu, sub_add_cancel]
        ring)
  have hC := quad_hasSum_graph (H := fun p : ℤ × ℤ => f p.1 p.2 * (2 * P p.1 * P (p.1 + 1)))
      (fun x => x + 1) (s := 2 * ∑' y, δ y) (by
        convert sδ.hasSum.mul_left 2 using 1
        funext x
        simp only [hδ, hu]
        ring)
  have hL := (hA.sub hB).sub hC
  -- the right side
  have hJp := quad_hasSum_graph (H := fun p : ℤ × ℤ =>
      (f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2) * P p.1 * P p.2) (fun x => x + 1)
      (s := ∑' y, α y + ∑' y, β y - 2 * ∑' y, δ y) (by
        convert (sα.hasSum.add sβ.hasSum).sub (sδ.hasSum.mul_left 2) using 1
        funext x
        simp only [hα, hβ, hδ, hu]
        ring)
  have hJm := quad_hasSum_graph (H := fun p : ℤ × ℤ =>
      (f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2) * P p.1 * P p.2) (fun x => x - 1)
      (s := ∑' y, β y + ∑' y, α y - 2 * ∑' y, γ y) (by
        convert ((shift β sβ).add (shift α sα)).sub ((shift γ sγ).mul_left 2) using 1
        funext x
        simp only [hα, hβ, hγ, hu, sub_add_cancel]
        ring)
  have hR := hJp.add hJm
  have eR : (fun p : ℤ × ℤ => (if |p.1 - p.2| = 1 then f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2
      else 0) * P p.1 * P p.2) = fun p =>
      (if p.2 = p.1 + 1 then (f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2) * P p.1 * P p.2 else 0) +
      (if p.2 = p.1 - 1 then (f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2) * P p.1 * P p.2
        else 0) := by
    funext p
    rw [quad_ite_abs_eq_one]
    split_ifs <;> ring
  rw [eR, hR.tsum_eq]
  convert hL using 1
  · funext p
    simp only [quadCross]
    split_ifs <;> first | (exfalso; omega) | ring
  · ring

/-- **The drift of the quadratic functional** (formal computation of the proof of Lemma 2.3
(2)): if `|f|, |∂ₜf| ≤ K W(x₁) W(x₂)`, the drift of the product rule summed over `ℤ²` is
`∑_{x₁,x₂} (∂ₜf + 𝒬f)(x₁,x₂) P(x₁) P(x₂)`. -/
theorem hasSum_quadDriftTerm (h : QuadDecay a R P) (ha : 0 ≤ a) {f f' : ℤ → ℤ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂)
    (hf' : ∀ x₁ x₂, |f' x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) :
    HasSum (fun p : ℤ × ℤ => quadDriftTerm f f' P p.1 p.2)
      (∑' x₁, ∑' x₂, (f' x₁ x₂ + inclGen f x₁ x₂) * P x₁ * P x₂) := by
  have hl := fun x => le_quadP3 h.nonneg x
  have hK4 : 0 ≤ 4 * Real.exp a * K := by positivity
  -- the four parts of the target
  have S0 : Summable fun p : ℤ × ℤ => f' p.1 p.2 * P p.1 * P p.2 :=
    h.summable_of_le ha hK fun p => h.abs_mul_le (hf' _ _) (hl _).2.1 (hl _).2.1
  have S1 : Summable fun p : ℤ × ℤ => lap (f p.1) p.2 * P p.1 * P p.2 :=
    h.summable_of_le ha hK4 fun p =>
      h.abs_mul_le (quad_abs_lap_snd_le ha hf _ _) (hl _).2.1 (hl _).2.1
  have S2 : Summable fun p : ℤ × ℤ => lap (fun y => f y p.2) p.1 * P p.1 * P p.2 :=
    h.summable_of_le ha hK4 fun p =>
      h.abs_mul_le (quad_abs_lap_fst_le ha hf _ _) (hl _).2.1 (hl _).2.1
  have S3 : Summable fun p : ℤ × ℤ => (if |p.1 - p.2| = 1 then
      f p.1 p.1 + f p.2 p.2 - 2 * f p.1 p.2 else 0) * P p.1 * P p.2 :=
    h.summable_of_le ha hK4 fun p =>
      h.abs_mul_le (quad_abs_jump_le ha hf _ _) (hl _).2.1 (hl _).2.1
  -- summability of the shifted families
  have hs : ∀ (g : ℤ × ℤ → ℤ) (k : ℤ × ℤ → ℤ), (∀ p, P (g p) ≤ quadP3 P p.1) →
      (∀ p, P (k p) ≤ quadP3 P p.2) →
      Summable fun p : ℤ × ℤ => f p.1 p.2 * P (g p) * P (k p) := fun g k hg hk =>
    h.summable_of_le ha hK fun p => h.abs_mul_le (hf _ _) (hg p) (hk p)
  have h₁ := hs (fun p => p.1) (fun p => p.2 + 1) (fun p => (hl _).2.1) (fun p => (hl _).2.2)
  have h₂ := hs (fun p => p.1) (fun p => p.2 - 1) (fun p => (hl _).2.1) (fun p => (hl _).1)
  have h₃ := hs (fun p => p.1) (fun p => p.2) (fun p => (hl _).2.1) (fun p => (hl _).2.1)
  have g₁ := hs (fun p => p.1 + 1) (fun p => p.2) (fun p => (hl _).2.2) (fun p => (hl _).2.1)
  have g₂ := hs (fun p => p.1 - 1) (fun p => p.2) (fun p => (hl _).1) (fun p => (hl _).2.1)
  -- the two summations by parts
  have e1 : ∑' p : ℤ × ℤ, f p.1 p.2 * P p.1 * lap P p.2 =
      ∑' p : ℤ × ℤ, lap (f p.1) p.2 * P p.1 * P p.2 := by
    have := quad_tsum_lap_snd (fun x₁ x₂ => f x₁ x₂ * P x₁) P h₁ h₂ h₃
    rw [this]
    congr 1
    funext p
    rw [lap_mul_const]
  have e2 : ∑' p : ℤ × ℤ, f p.1 p.2 * P p.2 * lap P p.1 =
      ∑' p : ℤ × ℤ, lap (fun y => f y p.2) p.1 * P p.1 * P p.2 := by
    have := quad_tsum_lap_fst (fun x₁ x₂ => f x₁ x₂ * P x₂) P
      (g₁.congr fun p => by ring) (g₂.congr fun p => by ring) (h₃.congr fun p => by ring)
    rw [this]
    congr 1
    funext p
    rw [lap_mul_const (fun y => f y p.2)]
    ring
  have T1 : Summable fun p : ℤ × ℤ => f p.1 p.2 * P p.1 * lap P p.2 :=
    ((h₁.add h₂).sub (h₃.mul_left 2)).congr fun p => by unfold lap; ring
  have T2 : Summable fun p : ℤ × ℤ => f p.1 p.2 * P p.2 * lap P p.1 :=
    ((g₁.add g₂).sub (h₃.mul_left 2)).congr fun p => by unfold lap; ring
  have hT1 : HasSum (fun p : ℤ × ℤ => f p.1 p.2 * P p.1 * lap P p.2)
      (∑' p : ℤ × ℤ, lap (f p.1) p.2 * P p.1 * P p.2) := e1 ▸ T1.hasSum
  have hT2 : HasSum (fun p : ℤ × ℤ => f p.1 p.2 * P p.2 * lap P p.1)
      (∑' p : ℤ × ℤ, lap (fun y => f y p.2) p.1 * P p.1 * P p.2) := e2 ▸ T2.hasSum
  have hT3 := h.hasSum_mul_quadCross ha hK hf
  have hall := ((S0.hasSum.add hT1).add hT2).add hT3
  have htarget : Summable fun p : ℤ × ℤ => (f' p.1 p.2 + inclGen f p.1 p.2) * P p.1 * P p.2 :=
    (((S0.add S1).add S2).add S3).congr fun p => by simp only [inclGen]; ring
  rw [← htarget.tsum_prod]
  convert hall using 1
  · funext p
    simp only [quadDriftTerm]
    ring
  · rw [← S0.tsum_add S1, ← (S0.add S1).tsum_add S2, ← ((S0.add S1).add S2).tsum_add S3]
    congr 1
    funext p
    simp only [inclGen]
    ring

/-- `|quadDriftTerm| ≤ 9 K W(x₁) W(x₂) P₃(x₁) P₃(x₂)` when `|f|, |∂ₜf| ≤ K W W`. -/
lemma abs_quadDriftTerm_le (h : QuadDecay a R P) {f f' : ℤ → ℤ → ℝ} {K : ℝ}
    (hf : ∀ x₁ x₂, |f x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂)
    (hf' : ∀ x₁ x₂, |f' x₁ x₂| ≤ K * quadW a x₁ * quadW a x₂) (x₁ x₂ : ℤ) :
    |quadDriftTerm f f' P x₁ x₂| ≤
      9 * K * quadW a x₁ * quadW a x₂ * quadP3 P x₁ * quadP3 P x₂ := by
  obtain ⟨a1, b1, c1⟩ := le_quadP3 h.nonneg x₁
  obtain ⟨a2, b2, c2⟩ := le_quadP3 h.nonneg x₂
  have q1 := quadP3_nonneg h.nonneg x₁; have q2 := quadP3_nonneg h.nonneg x₂
  have p1 := h.nonneg x₁; have p2 := h.nonneg x₂
  have l1 := abs_lap_le_quadP3 h.nonneg x₁; have l2 := abs_lap_le_quadP3 h.nonneg x₂
  have cr := abs_quadCross_le h.nonneg x₁ x₂
  have t0 := h.abs_mul_le (hf' x₁ x₂) b1 b2
  have hin : |P x₁ * lap P x₂ + P x₂ * lap P x₁ + quadCross P x₁ x₂| ≤
      8 * (quadP3 P x₁ * quadP3 P x₂) := by
    have e1 : |P x₁ * lap P x₂| ≤ 2 * (quadP3 P x₁ * quadP3 P x₂) := by
      rw [abs_mul, abs_of_nonneg p1]
      nlinarith [mul_le_mul b1 l2 (abs_nonneg _) q1]
    have e2 : |P x₂ * lap P x₁| ≤ 2 * (quadP3 P x₁ * quadP3 P x₂) := by
      rw [abs_mul, abs_of_nonneg p2]
      nlinarith [mul_le_mul b2 l1 (abs_nonneg _) q2]
    calc _ ≤ |P x₁ * lap P x₂| + |P x₂ * lap P x₁| + |quadCross P x₁ x₂| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hK : 0 ≤ K * quadW a x₁ * quadW a x₂ := (abs_nonneg _).trans (hf x₁ x₂)
  have t1 : |f x₁ x₂ * (P x₁ * lap P x₂ + P x₂ * lap P x₁ + quadCross P x₁ x₂)| ≤
      K * quadW a x₁ * quadW a x₂ * (8 * (quadP3 P x₁ * quadP3 P x₂)) := by
    rw [abs_mul]; exact mul_le_mul (hf x₁ x₂) hin (abs_nonneg _) hK
  unfold quadDriftTerm
  calc _ ≤ |f' x₁ x₂ * P x₁ * P x₂| +
        |f x₁ x₂ * (P x₁ * lap P x₂ + P x₂ * lap P x₁ + quadCross P x₁ x₂)| := abs_add_le _ _
    _ ≤ _ := by nlinarith

end QuadDecay

end QSSEPtoKPZ
