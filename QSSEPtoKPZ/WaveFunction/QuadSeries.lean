/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Series on `ℤ` and `ℤ²` with exponential weights (task D6)

Deterministic estimates for the proof of Lemma 2.3 (2). Fix `a ≥ 0` and a nonnegative sequence
`P : ℤ → ℝ` with `e^{(2a+1)|x|} P(x) ≤ R` for all `x` (`QuadDecay a R P`; along the paths of the
wave function this holds for all `t ∈ [0,T]` with `R = sup_{t ≤ T} ‖ψ_t‖²_{2a+1}`, which is
finite almost surely by (2.2)). With the weights `W(x) = e^{a|x|}` (`quadW`) and
`ρ(x) = e^{-|x|}` (`quadRho`):

* `W(x) P(x) ≤ W(x)² P(x) ≤ R ρ(x)` (`QuadDecay.sq_le`), and with
  `P₃(x) = P(x-1) + P(x) + P(x+1)` (`quadP3`), `W(x) P₃(x) ≤ 3 e^a R ρ₃(x)` where
  `ρ₃(x) = ρ(x-1) + ρ(x) + ρ(x+1)` is summable (`QuadDecay.w_p3_le`);
* hence every family on `ℤ²` bounded by `K W(x₁) W(x₂) P₃(x₁) P₃(x₂)` is summable
  (`quad_summable_of_le`), which is the article's remark
  `e^{a|x|} P(t,x) ≤ e^{-|x|} N_{a+1}`.
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace QSSEPtoKPZ

/-- The weight `W(x) = e^{a|x|}`. -/
def quadW (a : ℝ) (x : ℤ) : ℝ := Real.exp (a * |(x : ℝ)|)

/-- The summable weight `ρ(x) = e^{-|x|}`. -/
def quadRho (x : ℤ) : ℝ := Real.exp (-|(x : ℝ)|)

/-- `ρ₃(x) = ρ(x-1) + ρ(x) + ρ(x+1)`. -/
def quadRho3 (x : ℤ) : ℝ := quadRho (x - 1) + quadRho x + quadRho (x + 1)

/-- `P₃(x) = P(x-1) + P(x) + P(x+1)`. -/
def quadP3 (P : ℤ → ℝ) (x : ℤ) : ℝ := P (x - 1) + P x + P (x + 1)

/-- **Exponential decay** of a nonnegative sequence: `0 ≤ P(x)` and `e^{(2a+1)|x|} P(x) ≤ R`. -/
structure QuadDecay (a R : ℝ) (P : ℤ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ P x
  le : ∀ x : ℤ, Real.exp ((2 * a + 1) * |(x : ℝ)|) * P x ≤ R

lemma quadW_pos (a : ℝ) (x : ℤ) : 0 < quadW a x := Real.exp_pos _

lemma one_le_quadW {a : ℝ} (ha : 0 ≤ a) (x : ℤ) : 1 ≤ quadW a x :=
  Real.one_le_exp (mul_nonneg ha (abs_nonneg _))

lemma quadRho_pos (x : ℤ) : 0 < quadRho x := Real.exp_pos _

lemma quadRho_le_one (x : ℤ) : quadRho x ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (abs_nonneg _))

lemma quadRho3_nonneg (x : ℤ) : 0 ≤ quadRho3 x := by
  unfold quadRho3
  have := quadRho_pos (x - 1); have := quadRho_pos x; have := quadRho_pos (x + 1)
  positivity

lemma quadRho3_le_three (x : ℤ) : quadRho3 x ≤ 3 := by
  unfold quadRho3
  have := quadRho_le_one (x - 1); have := quadRho_le_one x; have := quadRho_le_one (x + 1)
  linarith

/-- `ρ` is summable on `ℤ`. -/
lemma summable_quadRho : Summable quadRho := by
  refine Summable.of_nat_of_neg ?_ ?_ <;> simpa [quadRho] using Real.summable_exp_neg_nat

/-- `ρ₃` is summable on `ℤ`. -/
lemma summable_quadRho3 : Summable quadRho3 := by
  have h1 : Summable fun x : ℤ => quadRho (x - 1) := by
    simpa [Function.comp_def] using (Equiv.subRight (1 : ℤ)).summable_iff.2 summable_quadRho
  have h2 : Summable fun x : ℤ => quadRho (x + 1) := by
    simpa [Function.comp_def] using (Equiv.addRight (1 : ℤ)).summable_iff.2 summable_quadRho
  exact (h1.add summable_quadRho).add h2

/-- `W(x + c) ≤ e^a W(x)` for `|c| ≤ 1`. -/
lemma quadW_add_le {a : ℝ} (ha : 0 ≤ a) (x c : ℤ) (hc : |c| ≤ 1) :
    quadW a (x + c) ≤ Real.exp a * quadW a x := by
  unfold quadW
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hc' : |(c : ℝ)| ≤ 1 := by exact_mod_cast hc
  have : |((x + c : ℤ) : ℝ)| ≤ |(x : ℝ)| + 1 := by
    push_cast
    exact (abs_add_le _ _).trans (by linarith)
  nlinarith

/-- `W(x) ≤ e^a W(x + c)` for `|c| ≤ 1`. -/
lemma quadW_le_add {a : ℝ} (ha : 0 ≤ a) (x c : ℤ) (hc : |c| ≤ 1) :
    quadW a x ≤ Real.exp a * quadW a (x + c) := by
  have h := quadW_add_le ha (x + c) (-c) (by rwa [abs_neg])
  rwa [add_neg_cancel_right] at h

/-- `W(x)² = e^{2a|x|}`. -/
lemma quadW_sq (a : ℝ) (x : ℤ) : quadW a x ^ 2 = Real.exp (2 * a * |(x : ℝ)|) := by
  rw [quadW, sq, ← Real.exp_add]
  congr 1
  ring

/-- `|f(x₁,x₂)| ≤ C e^{a(|x₁|+|x₂|)}` is `|f(x₁,x₂)| ≤ C W(x₁) W(x₂)`. -/
lemma quadW_mul (a : ℝ) (x₁ x₂ : ℤ) :
    Real.exp (a * (|(x₁ : ℝ)| + |(x₂ : ℝ)|)) = quadW a x₁ * quadW a x₂ := by
  rw [quadW, quadW, ← Real.exp_add, mul_add]

lemma le_quadP3 {P : ℤ → ℝ} (hP : ∀ x, 0 ≤ P x) (x : ℤ) :
    P (x - 1) ≤ quadP3 P x ∧ P x ≤ quadP3 P x ∧ P (x + 1) ≤ quadP3 P x := by
  unfold quadP3
  have := hP (x - 1); have := hP x; have := hP (x + 1)
  refine ⟨by linarith, by linarith, by linarith⟩

lemma quadP3_nonneg {P : ℤ → ℝ} (hP : ∀ x, 0 ≤ P x) (x : ℤ) : 0 ≤ quadP3 P x := by
  unfold quadP3
  have := hP (x - 1); have := hP x; have := hP (x + 1)
  positivity

/-- `|ΔP(x)| ≤ 2 P₃(x)` for `P ≥ 0`. -/
lemma abs_lap_le_quadP3 {P : ℤ → ℝ} (hP : ∀ x, 0 ≤ P x) (x : ℤ) :
    |lap P x| ≤ 2 * quadP3 P x := by
  unfold lap quadP3
  have := hP (x - 1); have := hP x; have := hP (x + 1)
  rw [abs_le]
  constructor <;> linarith

namespace QuadDecay

variable {a R : ℝ} {P : ℤ → ℝ}

lemma R_nonneg (h : QuadDecay a R P) : 0 ≤ R :=
  (mul_nonneg (Real.exp_pos _).le (h.nonneg 0)).trans (h.le 0)

lemma le_R (h : QuadDecay a R P) (ha : 0 ≤ a) (x : ℤ) : P x ≤ R :=
  (le_mul_of_one_le_left (h.nonneg x) (Real.one_le_exp (by positivity))).trans (h.le x)

/-- `W(x)² P(x) ≤ R ρ(x)`. -/
lemma sq_le (h : QuadDecay a R P) (x : ℤ) : quadW a x ^ 2 * P x ≤ R * quadRho x := by
  have e : quadW a x ^ 2 * P x =
      (Real.exp ((2 * a + 1) * |(x : ℝ)|) * P x) * quadRho x := by
    rw [quadW_sq, quadRho, show Real.exp (2 * a * |(x : ℝ)|) =
      Real.exp ((2 * a + 1) * |(x : ℝ)|) * Real.exp (-|(x : ℝ)|) by
        rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (h.le x) (quadRho_pos x).le

/-- `W(x) P(x) ≤ R ρ(x)`. -/
lemma w_le (h : QuadDecay a R P) (ha : 0 ≤ a) (x : ℤ) : quadW a x * P x ≤ R * quadRho x := by
  refine le_trans ?_ (h.sq_le x)
  refine mul_le_mul_of_nonneg_right ?_ (h.nonneg x)
  have := one_le_quadW ha x
  nlinarith

/-- `W(x) P₃(x) ≤ 3 e^a R ρ₃(x)`. -/
lemma w_p3_le (h : QuadDecay a R P) (ha : 0 ≤ a) (x : ℤ) :
    quadW a x * quadP3 P x ≤ 3 * Real.exp a * R * quadRho3 x := by
  have hR := h.R_nonneg
  have hea : 1 ≤ Real.exp a := Real.one_le_exp ha
  have k : ∀ c : ℤ, |c| ≤ 1 → quadW a x * P (x + c) ≤ Real.exp a * (R * quadRho (x + c)) :=
    fun c hc => by
    calc quadW a x * P (x + c) ≤ (Real.exp a * quadW a (x + c)) * P (x + c) :=
          mul_le_mul_of_nonneg_right (quadW_le_add ha x c hc) (h.nonneg _)
      _ = Real.exp a * (quadW a (x + c) * P (x + c)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h.w_le ha _) (Real.exp_pos _).le
  have k1 := k (-1) (by norm_num)
  have k2 := k 0 (by norm_num)
  have k3 := k 1 (by norm_num)
  simp only [add_zero, ← sub_eq_add_neg] at k1 k2 k3
  have r1 := quadRho_pos (x - 1); have r2 := quadRho_pos x; have r3 := quadRho_pos (x + 1)
  unfold quadP3 quadRho3
  have : 0 ≤ Real.exp a * R := mul_nonneg (Real.exp_pos _).le hR
  nlinarith

/-- **Domination on `ℤ²`.** If `|F| ≤ K W(x₁) W(x₂)` then
`|F| P₃(x₁) P₃(x₂) ≤ K (3 e^a R)² ρ₃(x₁) ρ₃(x₂)`. -/
lemma pair_le (h : QuadDecay a R P) (ha : 0 ≤ a) {F K : ℝ} (x₁ x₂ : ℤ)
    (hF : |F| ≤ K * quadW a x₁ * quadW a x₂) :
    |F| * quadP3 P x₁ * quadP3 P x₂ ≤
      K * (3 * Real.exp a * R) ^ 2 * (quadRho3 x₁ * quadRho3 x₂) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg F).trans hF
    have h1 := quadW_pos a x₁; have h2 := quadW_pos a x₂
    by_contra hK
    push Not at hK
    have : K * quadW a x₁ * quadW a x₂ < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hK h1) h2
    linarith
  have p1 := quadP3_nonneg h.nonneg x₁; have p2 := quadP3_nonneg h.nonneg x₂
  have w1 := h.w_p3_le ha x₁; have w2 := h.w_p3_le ha x₂
  have q1 : 0 ≤ quadW a x₁ * quadP3 P x₁ := mul_nonneg (quadW_pos a x₁).le p1
  have q2 : 0 ≤ quadW a x₂ * quadP3 P x₂ := mul_nonneg (quadW_pos a x₂).le p2
  have hR := h.R_nonneg
  have r1 := quadRho3_nonneg x₁
  have e0 := (Real.exp_pos a).le
  calc |F| * quadP3 P x₁ * quadP3 P x₂ ≤ K * quadW a x₁ * quadW a x₂ * quadP3 P x₁ *
        quadP3 P x₂ := by gcongr
    _ = K * ((quadW a x₁ * quadP3 P x₁) * (quadW a x₂ * quadP3 P x₂)) := by ring
    _ ≤ K * ((3 * Real.exp a * R * quadRho3 x₁) * (3 * Real.exp a * R * quadRho3 x₂)) := by
        gcongr
    _ = _ := by ring

end QuadDecay

/-- A family on `ℤ²` dominated by `K ρ₃(x₁) ρ₃(x₂)` is summable. -/
lemma quad_summable_of_le {g : ℤ × ℤ → ℝ} {K : ℝ}
    (hg : ∀ p, |g p| ≤ K * (quadRho3 p.1 * quadRho3 p.2)) : Summable g :=
  Summable.of_norm_bounded ((summable_quadRho3.mul_of_nonneg summable_quadRho3
    (fun x => quadRho3_nonneg x) (fun x => quadRho3_nonneg x)).mul_left K)
    fun p => by simpa [Real.norm_eq_abs] using hg p

/-- **Domination on `ℤ²`, packaged.** If `|g(p)| ≤ K W(x₁) W(x₂) P₃(x₁) P₃(x₂)` with `K ≥ 0`,
then `g` is summable. -/
lemma QuadDecay.summable_of_le {a R : ℝ} {P : ℤ → ℝ} (h : QuadDecay a R P) (ha : 0 ≤ a)
    {g : ℤ × ℤ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ p : ℤ × ℤ, |g p| ≤ K * quadW a p.1 * quadW a p.2 * quadP3 P p.1 * quadP3 P p.2) :
    Summable g := by
  refine quad_summable_of_le (K := K * (3 * Real.exp a * R) ^ 2) fun p => (hg p).trans ?_
  have := h.pair_le ha (F := K * quadW a p.1 * quadW a p.2) (K := K) p.1 p.2 (by
    rw [abs_of_nonneg (by have := quadW_pos a p.1; have := quadW_pos a p.2; positivity)])
  rwa [abs_of_nonneg (by have := quadW_pos a p.1; have := quadW_pos a p.2; positivity)] at this

end QSSEPtoKPZ
