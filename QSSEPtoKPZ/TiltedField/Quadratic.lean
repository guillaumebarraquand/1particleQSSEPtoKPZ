/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.TiltedField.Martingales
public import QSSEPtoKPZ.WaveFunction.Quadratic
public import QSSEPtoKPZ.Martingales.NullAug
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Lemma 3.2: quadratic functionals of the tilted field

Statement: Stage 2, task T0; proof: task E3. As in the article, Lemma 3.2 is Lemma 2.3 (2)
(`lemma_2_3_quadratic`) applied on `[0, nT/2]` to
`F_s(x₁,x₂) = e^{θ_n(x₁+x₂) - 2λ_n s} f_{2s/n}(x₁,x₂)` (`quadTiltF`), with the tilt identity
(3.20) (`tilt_identity`) for the drift, and the change of time `s = nu/2` (`HasBracket.timeChange`,
`filtN`); the integrals in time are transformed by the change of variables `s = nu/2`.
The summability of `∑ₓ 𝔷_n(t,x)` is the first part of `WN_moments` (3.7).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The function `F_s(x₁,x₂) = e^{θ_n(x₁+x₂) - 2λ_n s} f_{2s/n}(x₁,x₂)` of the proof of
Lemma 3.2. -/
private def quadTiltF (n : ℝ) (f : ℝ → ℤ → ℤ → ℝ) (s : ℝ) (y₁ y₂ : ℤ) : ℝ :=
  Real.exp (thetaN n * (y₁ + y₂) - 2 * lambdaN n * s) * f (2 * s / n) y₁ y₂

/-- Its time derivative `∂ₛF_s = e^{θ_n(x₁+x₂) - 2λ_n s} ((2/n) ∂ₜf_{2s/n} - 2λ_n f_{2s/n})`. -/
private def quadTiltF' (n : ℝ) (f f' : ℝ → ℤ → ℤ → ℝ) (s : ℝ) (y₁ y₂ : ℤ) : ℝ :=
  Real.exp (thetaN n * (y₁ + y₂) - 2 * lambdaN n * s) *
    (2 / n * f' (2 * s / n) y₁ y₂ - 2 * lambdaN n * f (2 * s / n) y₁ y₂)

/-- `𝔷_n(t,x₁) 𝔷_n(t,x₂) = e^{θ_n(x₁+x₂) - 2λ_n (nt/2)} P(nt/2,x₁) P(nt/2,x₂)`. -/
private lemma quadTilt_zN_mul_zN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x₁ x₂ : ℤ) :
    zN n ψ ω t x₁ * zN n ψ ω t x₂ =
      Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * (n * t / 2)) *
        density ψ ω (n * t / 2) x₁ * density ψ ω (n * t / 2) x₂ := by
  have e : Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * (n * t / 2)) =
      Real.exp (thetaN n * x₁ - n * lambdaN n / 2 * t) *
        Real.exp (thetaN n * x₂ - n * lambdaN n / 2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]; unfold zN; ring

/-- `2 (nu/2) / n = u`. -/
private lemma quadTilt_time {n : ℝ} (hn : n ≠ 0) (u : ℝ) : 2 * (n * u / 2) / n = u := by
  field_simp

/-- `𝒵_n^{⊗2}(t;f_t) = ∑_{x₁,x₂} F_{nt/2}(x₁,x₂) P(nt/2,x₁) P(nt/2,x₂)`. -/
private lemma quadTilt_pairZ2 {n : ℝ} (hn : n ≠ 0) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω)
    (f : ℝ → ℤ → ℤ → ℝ) (t : ℝ) :
    pairZ2 n ψ ω t (f t) = ∑' x₁ : ℤ, ∑' x₂ : ℤ, quadTiltF n f (n * t / 2) x₁ x₂ *
      density ψ ω (n * t / 2) x₁ * density ψ ω (n * t / 2) x₂ := by
  unfold pairZ2 quadTiltF
  refine tsum_congr fun x₁ => tsum_congr fun x₂ => ?_
  rw [quadTilt_time hn, quadTilt_zN_mul_zN]; ring

/-- The generator `𝒬` of (2.6) is linear: `𝒬 (c g) = c 𝒬 g`. -/
private lemma quadTilt_inclGen_const_mul (c : ℝ) (g : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) :
    inclGen (fun y₁ y₂ => c * g y₁ y₂) x₁ x₂ = c * inclGen g x₁ x₂ := by
  unfold inclGen lap; split_ifs <;> ring

/-- The drift of `F`, by the tilt identity (3.20) and `2(cosh θ_n - 1) = λ_n`:
`∂ₛF_s + 𝒬F_s = (2/n) e^{θ_n(x₁+x₂) - 2λ_n s} [∂ₜf_t + (n/2) 𝒬^{θ_n} f_t + (nλ_n/2) 𝟙 f_t]`
with `t = 2s/n` and `𝟙 = 𝟙_{|x₁-x₂|=1}`. -/
private lemma quadTilt_drift {n : ℝ} (hn : n ≠ 0) {f f' : ℝ → ℤ → ℤ → ℝ} {u : ℝ}
    (hsymm : ∀ x₁ x₂, f u x₁ x₂ = f u x₂ x₁) (x₁ x₂ : ℤ) :
    quadTiltF' n f f' (n * u / 2) x₁ x₂ + inclGen (quadTiltF n f (n * u / 2)) x₁ x₂ =
      2 / n * Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * (n * u / 2)) *
        (f' u x₁ x₂ + n / 2 * tiltedInclGen (thetaN n) (f u) x₁ x₂ +
          n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then f u x₁ x₂ else 0)) := by
  have e : quadTiltF n f (n * u / 2) = fun y₁ y₂ : ℤ =>
      Real.exp (-(2 * lambdaN n * (n * u / 2))) *
        (Real.exp (thetaN n * (y₁ + y₂)) * f u y₁ y₂) := by
    funext y₁ y₂
    rw [quadTiltF, quadTilt_time hn, sub_eq_add_neg, Real.exp_add]; ring
  rw [e, quadTilt_inclGen_const_mul, tilt_identity _ hsymm, quadTiltF', quadTilt_time hn,
    sub_eq_add_neg (thetaN n * _), Real.exp_add]
  unfold lambdaN
  field_simp
  ring

/-- The drift term of (2.8) for `F` at time `nu/2` is `(2/n)` times the drift term of (3.21). -/
private lemma quadTilt_drift_sum {n : ℝ} (hn : n ≠ 0) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω)
    {f f' : ℝ → ℤ → ℤ → ℝ} {u : ℝ} (hsymm : ∀ x₁ x₂, f u x₁ x₂ = f u x₂ x₁) :
    ∑' x₁ : ℤ, ∑' x₂ : ℤ, (quadTiltF' n f f' (n * u / 2) x₁ x₂ +
        inclGen (quadTiltF n f (n * u / 2)) x₁ x₂) * density ψ ω (n * u / 2) x₁ *
        density ψ ω (n * u / 2) x₂ =
      2 / n * pairZ2 n ψ ω u (fun x₁ x₂ => f' u x₁ x₂ +
        n / 2 * tiltedInclGen (thetaN n) (f u) x₁ x₂ +
          n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then f u x₁ x₂ else 0)) := by
  rw [pairZ2, ← tsum_mul_left]
  refine tsum_congr fun x₁ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun x₂ => ?_
  rw [quadTilt_drift hn hsymm, quadTilt_zN_mul_zN]; ring

/-- The quantity `D_s(x)` of (2.8) for `F`, at time `s = nu/2`:
`D_s(x) = e^{θ_n(x+1/2) - λ_n s} ∑_{x'} 𝔷_n(u,x') (e^{θ_n/2} f_u(x+1,x') - e^{-θ_n/2} f_u(x,x'))`.
-/
private lemma quadTilt_quadDiff {n : ℝ} (hn : n ≠ 0) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ))
    (f : ℝ → ℤ → ℤ → ℝ) (u : ℝ) (ω : Ω) (x : ℤ) :
    quadDiff ψ (quadTiltF n f) (n * u / 2) ω x =
      Real.exp (thetaN n * (x + 1 / 2) - lambdaN n * (n * u / 2)) *
        ∑' x' : ℤ, zN n ψ ω u x' *
          (Real.exp (thetaN n / 2) * f u (x + 1) x' - Real.exp (-thetaN n / 2) * f u x x') := by
  rw [quadDiff, ← tsum_mul_left]
  refine tsum_congr fun x' => ?_
  have e1 : Real.exp (thetaN n * (((x + 1 : ℤ) : ℝ) + x') - 2 * lambdaN n * (n * u / 2)) =
      Real.exp (thetaN n * (x + 1 / 2) - lambdaN n * (n * u / 2)) *
        (Real.exp (thetaN n * x' - n * lambdaN n / 2 * u) * Real.exp (thetaN n / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have e2 : Real.exp (thetaN n * ((x : ℝ) + x') - 2 * lambdaN n * (n * u / 2)) =
      Real.exp (thetaN n * (x + 1 / 2) - lambdaN n * (n * u / 2)) *
        (Real.exp (thetaN n * x' - n * lambdaN n / 2 * u) * Real.exp (-thetaN n / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  simp only [quadTiltF, quadTilt_time hn, e1, e2, zN]
  ring

/-- The bracket density of (2.8) for `F` at time `nu/2` is `(2/n)` times `bracketDensN2` at `u`. -/
private lemma quadTilt_bracket {n : ℝ} (hn : n ≠ 0) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ))
    (f : ℝ → ℤ → ℤ → ℝ) (u : ℝ) (ω : Ω) :
    ∑' x : ℤ, 2 * (2 * quadDiff ψ (quadTiltF n f) (n * u / 2) ω x) ^ 2 *
        density ψ ω (n * u / 2) x * density ψ ω (n * u / 2) (x + 1) =
      2 / n * bracketDensN2 n ψ f u ω := by
  rw [bracketDensN2, ← mul_assoc, show 2 / n * (4 * n) = 8 by field_simp; ring,
    ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  have e : zN n ψ ω u x * zN n ψ ω u (x + 1) =
      Real.exp (thetaN n * (x + 1 / 2) - lambdaN n * (n * u / 2)) ^ 2 *
        density ψ ω (n * u / 2) x * density ψ ω (n * u / 2) (x + 1) := by
    have e' : Real.exp (thetaN n * (x + 1 / 2) - lambdaN n * (n * u / 2)) ^ 2 =
        Real.exp (thetaN n * x - n * lambdaN n / 2 * u) *
          Real.exp (thetaN n * ((x + 1 : ℤ) : ℝ) - n * lambdaN n / 2 * u) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
    rw [e']; unfold zN; ring
  rw [quadTilt_quadDiff hn, e]; ring

/-- Change of variables `s = nu/2` in a time integral. -/
private lemma quadTilt_integral_comp {n t : ℝ} (hn : 0 < n) (ht : 0 ≤ t) {g h : ℝ → ℝ}
    (hgh : ∀ u ∈ Set.Icc 0 t, g (n * u / 2) = 2 / n * h u) :
    ∫ s in (0 : ℝ)..n * t / 2, g s = ∫ u in (0 : ℝ)..t, h u := by
  have e := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := t) g (n / 2)
  rw [mul_zero, smul_eq_mul, ← intervalIntegral.integral_const_mul] at e
  rw [show n * t / 2 = n / 2 * t by ring, ← e]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le ht] at hu
  rw [show n / 2 * u = n * u / 2 by ring, hgh u hu]
  field_simp

/-- Interval integrability is preserved by the change of variables `s = nu/2`. -/
private lemma quadTilt_intervalIntegrable {n T : ℝ} (hn : 0 < n) (hT : 0 ≤ T) {g h : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 (n / 2 * T))
    (hgh : ∀ u ∈ Set.Icc 0 T, g (n * u / 2) = 2 / n * h u) :
    IntervalIntegrable h volume 0 T := by
  have := (hg.comp_mul_left (c := n / 2)).const_mul (n / 2)
  rw [zero_div, mul_div_cancel_left₀ _ (by positivity : n / 2 ≠ 0)] at this
  refine this.congr_ae ?_
  rw [Set.uIoc_of_le hT]
  refine (ae_restrict_mem measurableSet_Ioc).mono fun u hu => ?_
  show n / 2 * g (n / 2 * u) = h u
  rw [show n / 2 * u = n * u / 2 by ring, hgh u (Set.Ioc_subset_Icc_self hu)]
  field_simp

/-- **Lemma 3.2**, equations (3.21), (3.22). Let `n ≥ 1`, `T > 0`, and let `f_t(x₁,x₂)` be symmetric
in `(x₁,x₂)`, bounded by `C`, `C¹` in `t ∈ [0,T]` (derivative `f'`, continuous in `t`, one-sided at
`0` and `T`) with `|f'| ≤ C`. Then almost surely `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`, and the
drift and bracket density below are integrable on `[0,T]`; and
`N_n^f(t) = 𝒵_n^{⊗2}(t;f_t) - f_0(0,0) - ∫_0^t 𝒵_n^{⊗2}(s; ∂ₛf_s + (n/2) 𝒬^{θ_n} f_s + (nλ_n/2) 𝟙_{|x₁-x₂|=1} f_s) ds`
is a continuous square-integrable `(𝓕ⁿ_t)`-martingale on `[0,T]` (this is (3.21)), with bracket
`⟨N_n^f⟩_t = ∫_0^t 4n ∑ₓ 𝔷_n(s,x) 𝔷_n(s,x+1) [∑_{x'} 𝔷_n(s,x') (e^{θ_n/2} f_s(x+1,x') - e^{-θ_n/2} f_s(x,x'))]² ds`,
the bracket of the stochastic integral (3.22), computed with (3.11). -/
theorem lemma_3_2 (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n T C : ℝ} (hn : 1 ≤ n) (hT : 0 < T) {f f' : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 T) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 T))
    (hbd : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, |f t x₁ x₂| ≤ C ∧ |f' t x₁ x₂| ≤ C) :
    (∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => pairZ2 n ψ ω s
        (fun x₁ x₂ => f' s x₁ x₂ + n / 2 * tiltedInclGen (thetaN n) (f s) x₁ x₂ +
          n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then f s x₁ x₂ else 0))) volume 0 T ∧
      IntervalIntegrable (fun s => bracketDensN2 n ψ f s ω) volume 0 T) ∧
    HasBracket T (filtN n 𝓕)
      (fun t ω => pairZ2 n ψ ω t (f t) - f 0 0 0 - ∫ s in (0 : ℝ)..t, pairZ2 n ψ ω s
        (fun x₁ x₂ => f' s x₁ x₂ + n / 2 * tiltedInclGen (thetaN n) (f s) x₁ x₂ +
          n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then f s x₁ x₂ else 0)))
      (fun t ω => ∫ s in (0 : ℝ)..t, bracketDensN2 n ψ f s ω) μ := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnne : n ≠ 0 := hn0.ne'
  have hθ : 0 ≤ thetaN n := by unfold thetaN; positivity
  have hlam : 0 ≤ lambdaN n := by
    unfold lambdaN; have := Real.one_le_cosh (thetaN n); linarith
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbd 0 ⟨le_rfl, hT.le⟩ 0 0).1
  have hcR : (((n / 2).toNNReal : ℝ≥0) : ℝ) = n / 2 := Real.coe_toNNReal _ (by positivity)
  -- the map `s ↦ 2s/n` sends `[0, nT/2]` to `[0, T]`
  have hmaps : Set.MapsTo (fun s : ℝ => 2 * s / n)
      (Set.Icc 0 (((n / 2).toNNReal : ℝ) * T)) (Set.Icc 0 T) := by
    intro s hs
    rw [hcR] at hs
    constructor
    · exact div_nonneg (by linarith [hs.1]) hn0.le
    · rw [div_le_iff₀ hn0]; nlinarith [hs.2]
  have hfc : ∀ x₁ x₂, ContinuousOn (f · x₁ x₂) (Set.Icc 0 T) :=
    fun x₁ x₂ t ht => (hf x₁ x₂ t ht).continuousWithinAt
  have hlin : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 2 * s / n) (2 / n) s := by
    intro s
    have := ((hasDerivAt_id s).const_mul 2).div_const n
    simp only [id, mul_one] at this
    exact this
  -- the hypotheses of Lemma 2.3 (2) for `F`
  have hsym2 : ∀ s ∈ Set.Icc (0 : ℝ) (((n / 2).toNNReal : ℝ) * T), ∀ x₁ x₂,
      quadTiltF n f s x₁ x₂ = quadTiltF n f s x₂ x₁ := by
    intro s hs x₁ x₂
    rw [quadTiltF, quadTiltF, hsymm _ (hmaps hs) x₁ x₂, add_comm (x₁ : ℝ)]
  have hderiv : ∀ x₁ x₂, ∀ s ∈ Set.Icc (0 : ℝ) (((n / 2).toNNReal : ℝ) * T),
      HasDerivWithinAt (quadTiltF n f · x₁ x₂) (quadTiltF' n f f' s x₁ x₂)
        (Set.Icc 0 (((n / 2).toNNReal : ℝ) * T)) s := by
    intro x₁ x₂ s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s))
        (Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s) * (-(2 * lambdaN n))) s := by
      have := (((hasDerivAt_id s).const_mul (2 * lambdaN n)).const_sub
        (thetaN n * (x₁ + x₂))).exp
      simp only [id, mul_one] at this
      exact this
    have h2 : HasDerivWithinAt (fun s : ℝ => f (2 * s / n) x₁ x₂)
        (f' (2 * s / n) x₁ x₂ * (2 / n)) (Set.Icc 0 (((n / 2).toNNReal : ℝ) * T)) s :=
      HasDerivWithinAt.comp (x := s) (h₂ := (f · x₁ x₂)) (hf x₁ x₂ _ (hmaps hs))
        (hlin s).hasDerivWithinAt hmaps
    convert h1.hasDerivWithinAt.mul h2 using 1
    · funext x; rfl
    · rw [quadTiltF']; ring
  have hcont : ∀ x₁ x₂, ContinuousOn (quadTiltF' n f f' · x₁ x₂)
      (Set.Icc 0 (((n / 2).toNNReal : ℝ) * T)) := by
    intro x₁ x₂
    unfold quadTiltF'
    refine ContinuousOn.mul (by fun_prop)
      (ContinuousOn.sub (continuousOn_const.mul ?_) (continuousOn_const.mul ?_))
    · exact (hf' x₁ x₂).comp (f := fun s : ℝ => 2 * s / n) (by fun_prop) hmaps
    · exact (hfc x₁ x₂).comp (f := fun s : ℝ => 2 * s / n) (by fun_prop) hmaps
  have hbound : ∀ x₁ x₂, ∀ s ∈ Set.Icc (0 : ℝ) (((n / 2).toNNReal : ℝ) * T),
      |quadTiltF n f s x₁ x₂| + |quadTiltF' n f f' s x₁ x₂| ≤
        C * (1 + 2 / n + 2 * lambdaN n) * Real.exp (thetaN n * (|(x₁ : ℝ)| + |(x₂ : ℝ)|)) := by
    intro x₁ x₂ s hs
    obtain ⟨hb1, hb2⟩ := hbd _ (hmaps hs) x₁ x₂
    have hs0 : 0 ≤ s := hs.1
    have hE : Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s) ≤
        Real.exp (thetaN n * (|(x₁ : ℝ)| + |(x₂ : ℝ)|)) := by
      apply Real.exp_le_exp.2
      have : thetaN n * (x₁ + x₂) ≤ thetaN n * (|(x₁ : ℝ)| + |(x₂ : ℝ)|) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) (le_abs_self _)) hθ
      nlinarith
    have hE0 := (Real.exp_pos (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s)).le
    have h3 : |2 / n * f' (2 * s / n) x₁ x₂ - 2 * lambdaN n * f (2 * s / n) x₁ x₂| ≤
        2 / n * C + 2 * lambdaN n * C := by
      refine (abs_sub_le _ 0 _).trans ?_
      rw [sub_zero, zero_sub, abs_neg]
      refine add_le_add ?_ ?_
      · rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hb2 (by positivity)
      · rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    simp only [quadTiltF, quadTiltF', abs_mul, Real.abs_exp]
    calc _ ≤ Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s) * C +
          Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s) * (2 / n * C + 2 * lambdaN n * C) :=
          add_le_add (mul_le_mul_of_nonneg_left hb1 hE0) (mul_le_mul_of_nonneg_left h3 hE0)
      _ = C * (1 + 2 / n + 2 * lambdaN n) *
          Real.exp (thetaN n * (x₁ + x₂) - 2 * lambdaN n * s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)
  -- Lemma 2.3 (2) on `[0, nT/2]`
  obtain ⟨hae, hbr⟩ := lemma_2_3_quadratic hB hψ (T := ((n / 2).toNNReal : ℝ) * T)
    (a := thetaN n) (C := C * (1 + 2 / n + 2 * lambdaN n)) (f := quadTiltF n f)
    (f' := quadTiltF' n f f') (by rw [hcR]; positivity) hθ hsym2 hderiv hcont hbound
  refine ⟨?_, ?_⟩
  · filter_upwards [(WN_moments hB hψ (T := T) hn 0).1, hae] with ω hsum hω
    obtain ⟨-, hI1, hI2⟩ := hω
    rw [hcR] at hI1 hI2
    refine ⟨hsum, quadTilt_intervalIntegrable hn0 hT.le hI1 fun u hu => ?_,
      quadTilt_intervalIntegrable hn0 hT.le hI2 fun u _ => ?_⟩
    · exact quadTilt_drift_sum hnne ψ ω (hsymm u hu)
    · exact quadTilt_bracket hnne ψ f u ω
  · refine (hbr.timeChange).congr hT.le (Filter.Eventually.of_forall fun ω t ht => ?_)
      (Filter.Eventually.of_forall fun ω t ht => ?_)
    · simp only [hcR, show n / 2 * t = n * t / 2 by ring]
      rw [quadTilt_pairZ2 hnne, quadTilt_integral_comp hn0 ht.1 fun u hu =>
        quadTilt_drift_sum hnne ψ ω (hsymm u ⟨hu.1, hu.2.trans ht.2⟩)]
      simp [quadTiltF]
    · simp only [hcR, show n / 2 * t = n * t / 2 by ring]
      exact quadTilt_integral_comp hn0 ht.1 fun u _ => quadTilt_bracket hnne ψ f u ω

end QSSEPtoKPZ
