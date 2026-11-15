/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.TiltedField.MartingalesBounds
public import QSSEPtoKPZ.WaveFunction.Linear
public import QSSEPtoKPZ.WaveFunction.Good
public import QSSEPtoKPZ.Martingales.Doob
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Auxiliary results for Lemma 5.2 (task Q1)

The proof of Lemma 5.2 in the article. For `n ≥ 1` and `b ∈ ℝ`, let
`θ' = θ_n + b n^{-1/2}` (`expMomTheta`), `α_s(x) = e^{θ' x - 2 (cosh θ' - 1) s}` (`expMomAlpha`),
`N_b(s) = ∑ₓ α_s(x) P(s,x)` (`expMomN`) and `κ = n (cosh θ' - cosh θ_n) - b n^{1/4}`
(`expMomKappa`). Then:
* `𝖹_n(t;e_b) = e^{κ t} N_b(nt/2)` (`expMom_pairZ_eq`), for every realization;
* `κ ≤ 2` for `n ≥ 1`, `|b| ≤ 1` (`expMom_kappa_le`), from
  `κ = n (sinh θ_n sinh δ - θ_n δ) + n cosh θ_n (cosh δ - 1)`, `δ = b n^{-1/2}`, and the
  inequalities of Section 3.1;
* `∂ₛα + Δα = 0`, so by Lemma 2.3 (1) `N_b` is a nonnegative continuous square-integrable
  martingale with `𝔼[N_b(s)] = 1` (`expMom_isCL2Mart`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `θ' = θ_n + b n^{-1/2}` (proof of Lemma 5.2). -/
def expMomTheta (n b : ℝ) : ℝ := thetaN n + b * n ^ (-1 / 2 : ℝ)

/-- `κ = n (cosh θ' - cosh θ_n) - b n^{1/4}` (proof of Lemma 5.2). -/
def expMomKappa (n b : ℝ) : ℝ :=
  n * (Real.cosh (expMomTheta n b) - Real.cosh (thetaN n)) - b * n ^ (1 / 4 : ℝ)

/-- `α_s(x) = e^{θ' x - 2 (cosh θ' - 1) s}` (proof of Lemma 5.2). -/
def expMomAlpha (n b s : ℝ) (x : ℤ) : ℝ :=
  Real.exp (expMomTheta n b * x - 2 * (Real.cosh (expMomTheta n b) - 1) * s)

/-- `N_b(s) = ∑ₓ α_s(x) P(s,x)` (proof of Lemma 5.2). -/
def expMomN (n b : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω) : ℝ :=
  ∑' x : ℤ, expMomAlpha n b s x * density ψ ω s x

/-! ### The bound `κ ≤ 2` -/

/-- `cosh 1 ≤ 8/5`. -/
private lemma expMom_cosh_one_le : Real.cosh 1 ≤ 8 / 5 := by
  rw [Real.cosh_eq, Real.exp_neg]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have h3 : (Real.exp 1)⁻¹ ≤ 2 / 5 := by
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  linarith

/-- `|sinh d| ≤ |d| cosh d` and `|sinh d - d| ≤ |d|³ cosh d / 6` and
`0 ≤ cosh d - 1 ≤ d² cosh d / 2`, for every real `d`. -/
private lemma expMom_d_bounds (d : ℝ) :
    |Real.sinh d| ≤ |d| * Real.cosh d ∧ |Real.sinh d - d| ≤ |d| ^ 3 / 6 * Real.cosh d ∧
      0 ≤ Real.cosh d - 1 ∧ Real.cosh d - 1 ≤ d ^ 2 * Real.cosh d / 2 := by
  have ha := abs_nonneg d
  have hc : Real.cosh |d| = Real.cosh d := Real.cosh_abs d
  have hs : |Real.sinh d| = Real.sinh |d| := Real.abs_sinh d
  have hsd : |Real.sinh d - d| = Real.sinh |d| - |d| := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg]
      linarith [Real.self_le_sinh_iff.2 h]
    · rw [abs_of_nonpos h, abs_of_nonpos, Real.sinh_neg]
      · ring
      · linarith [Real.sinh_le_self_iff.2 h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs, ← hc]; exact sinh_le_mul_cosh ha
  · rw [hsd, ← hc]; exact (sinh_sub_self_bounds ha).2
  · linarith [Real.one_le_cosh d]
  · have := (sq_le_two_mul_cosh_sub_one ha).2
    rw [hc, sq_abs] at this
    linarith

/-- The computation of the article: if `0 < θ ≤ 1`, `n θ⁴ = 1` and `|δ| ≤ θ²`, then
`n (cosh(θ + δ) - cosh θ - θ δ) ≤ 2`. Indeed this is
`n (sinh θ - θ) sinh δ + n θ (sinh δ - δ) + n cosh θ (cosh δ - 1)
  ≤ θ c²/6 + θ³ c/6 + c²/2 ≤ 2 c²/3 + c/6 ≤ 2` with `c = cosh 1 ≤ 8/5`. -/
private lemma expMom_kappa_aux {n θ d : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hnθ : n * θ ^ 4 = 1)
    (hd : |d| ≤ θ ^ 2) : n * (Real.cosh (θ + d) - Real.cosh θ - θ * d) ≤ 2 := by
  set c := Real.cosh 1 with hc_def
  have hc := expMom_cosh_one_le
  have hc1 : 1 ≤ c := Real.one_le_cosh 1
  have hn0 : 0 < n := by
    by_contra h
    push Not at h
    nlinarith [pow_pos hθ0 4]
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have hcθ : Real.cosh θ ≤ c := by
    rw [hc_def, Real.cosh_le_cosh, abs_of_pos hθ0, abs_one]; exact hθ1
  have hcd : Real.cosh d ≤ c := by
    rw [hc_def, Real.cosh_le_cosh, abs_one]; exact hd.trans hθ2
  obtain ⟨hS, hD, hE0, hE⟩ := expMom_d_bounds d
  obtain ⟨hA0, hA⟩ := sinh_sub_self_bounds hθ0.le
  set A := Real.sinh θ - θ
  set S := Real.sinh d
  set D := Real.sinh d - d
  set E := Real.cosh d - 1
  have hcθ0 : 0 ≤ Real.cosh θ := (Real.cosh_pos θ).le
  have hcd0 : 0 ≤ Real.cosh d := (Real.cosh_pos d).le
  have hd0 := abs_nonneg d
  have e : Real.cosh (θ + d) - Real.cosh θ - θ * d = A * S + θ * D + Real.cosh θ * E := by
    rw [Real.cosh_add]; ring
  -- the three terms
  have hA' : A ≤ θ ^ 3 * c / 6 := by
    calc A ≤ θ ^ 3 / 6 * Real.cosh θ := hA
      _ ≤ θ ^ 3 / 6 * c := by gcongr
      _ = θ ^ 3 * c / 6 := by ring
  have hS' : |S| ≤ θ ^ 2 * c := hS.trans (mul_le_mul hd hcd hcd0 (by positivity))
  have hD' : |D| ≤ θ ^ 6 * c / 6 := by
    have h3 : |d| ^ 3 ≤ (θ ^ 2) ^ 3 := pow_le_pow_left₀ hd0 hd 3
    calc |D| ≤ |d| ^ 3 / 6 * Real.cosh d := hD
      _ ≤ (θ ^ 2) ^ 3 / 6 * c := by gcongr
      _ = θ ^ 6 * c / 6 := by ring
  have hE' : E ≤ θ ^ 4 * c / 2 := by
    have h2 : d ^ 2 ≤ (θ ^ 2) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ hd0 hd 2
    calc E ≤ d ^ 2 * Real.cosh d / 2 := hE
      _ ≤ (θ ^ 2) ^ 2 * c / 2 := by gcongr
      _ = θ ^ 4 * c / 2 := by ring
  have t1 : A * S ≤ θ ^ 5 * c ^ 2 / 6 := by
    calc A * S ≤ |A * S| := le_abs_self _
      _ = A * |S| := by rw [abs_mul, abs_of_nonneg hA0]
      _ ≤ θ ^ 3 * c / 6 * (θ ^ 2 * c) := mul_le_mul hA' hS' (abs_nonneg _) (by positivity)
      _ = θ ^ 5 * c ^ 2 / 6 := by ring
  have t2 : θ * D ≤ θ ^ 7 * c / 6 := by
    calc θ * D ≤ θ * |D| := mul_le_mul_of_nonneg_left (le_abs_self _) hθ0.le
      _ ≤ θ * (θ ^ 6 * c / 6) := mul_le_mul_of_nonneg_left hD' hθ0.le
      _ = θ ^ 7 * c / 6 := by ring
  have t3 : Real.cosh θ * E ≤ θ ^ 4 * c ^ 2 / 2 := by
    calc Real.cosh θ * E ≤ c * (θ ^ 4 * c / 2) := mul_le_mul hcθ hE' hE0 (by positivity)
      _ = θ ^ 4 * c ^ 2 / 2 := by ring
  have hθ3 : θ ^ 3 ≤ 1 := pow_le_one₀ hθ0.le hθ1
  calc n * (Real.cosh (θ + d) - Real.cosh θ - θ * d)
      = n * (A * S + θ * D + Real.cosh θ * E) := by rw [e]
    _ ≤ n * (θ ^ 5 * c ^ 2 / 6 + θ ^ 7 * c / 6 + θ ^ 4 * c ^ 2 / 2) := by gcongr
    _ = (n * θ ^ 4) * (θ * c ^ 2 / 6 + θ ^ 3 * c / 6 + c ^ 2 / 2) := by ring
    _ = θ * c ^ 2 / 6 + θ ^ 3 * c / 6 + c ^ 2 / 2 := by rw [hnθ, one_mul]
    _ ≤ 1 * c ^ 2 / 6 + 1 * c / 6 + c ^ 2 / 2 := by gcongr
    _ ≤ 2 := by nlinarith

/-- **`κ ≤ 2`** (proof of Lemma 5.2): for `n ≥ 1` and `b ∈ [-1,1]`,
`κ = n (cosh(θ_n + b n^{-1/2}) - cosh θ_n) - b n^{1/4} ≤ 2`. -/
theorem expMom_kappa_le {n b : ℝ} (hn : 1 ≤ n) (hb : b ∈ Icc (-1 : ℝ) 1) :
    expMomKappa n b ≤ 2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hθ0 : 0 < thetaN n := Real.rpow_pos_of_pos hn0 _
  have hθ1 : thetaN n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hθsq : thetaN n ^ 2 = n ^ (-1 / 2 : ℝ) := by
    rw [thetaN, ← Real.rpow_mul_natCast hn0.le]; norm_num
  have hθ4 : n * thetaN n ^ 4 = 1 := by
    rw [thetaN, ← Real.rpow_mul_natCast hn0.le]; norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hn0.ne']
  have hθb : n * thetaN n * (b * n ^ (-1 / 2 : ℝ)) = b * n ^ (1 / 4 : ℝ) := by
    have : n * thetaN n * n ^ (-1 / 2 : ℝ) = n ^ (1 / 4 : ℝ) := by
      rw [thetaN, mul_assoc, ← Real.rpow_add hn0]
      nth_rw 1 [← Real.rpow_one n]
      rw [← Real.rpow_add hn0]; norm_num
    rw [← this]; ring
  have hd : |b * n ^ (-1 / 2 : ℝ)| ≤ thetaN n ^ 2 := by
    rw [hθsq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    exact mul_le_of_le_one_left (Real.rpow_pos_of_pos hn0 _).le (abs_le.2 hb)
  have := expMom_kappa_aux hθ0 hθ1 hθ4 hd
  calc expMomKappa n b
      = n * (Real.cosh (thetaN n + b * n ^ (-1 / 2 : ℝ)) - Real.cosh (thetaN n) -
          thetaN n * (b * n ^ (-1 / 2 : ℝ))) := by
        rw [expMomKappa, expMomTheta, ← hθb]; ring
    _ ≤ 2 := this

/-- `|θ'| ≤ 2` for `n ≥ 1` and `b ∈ [-1,1]`. -/
lemma expMom_abs_theta_le {n b : ℝ} (hn : 1 ≤ n) (hb : b ∈ Icc (-1 : ℝ) 1) :
    |expMomTheta n b| ≤ 2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hθ0 : 0 < thetaN n := Real.rpow_pos_of_pos hn0 _
  have hθ1 : thetaN n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hp0 : 0 < n ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hp1 : n ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have : |b * n ^ (-1 / 2 : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hp0]
    exact (mul_le_mul (abs_le.2 hb) hp1 hp0.le zero_le_one).trans (by norm_num)
  rw [expMomTheta]
  calc |thetaN n + b * n ^ (-1 / 2 : ℝ)| ≤ |thetaN n| + |b * n ^ (-1 / 2 : ℝ)| := abs_add_le _ _
    _ ≤ 2 := by rw [abs_of_pos hθ0]; linarith

/-! ### The identity `𝖹_n(t;e_b) = e^{κ t} N_b(nt/2)` -/

/-- Termwise: `𝔷_n(t,x) e^{b y_n(t,x)} = e^{κ t} α_{nt/2}(x) P(nt/2,x)`. -/
lemma expMom_term_eq {n : ℝ} (hn : 1 ≤ n) (b : ℝ) (ω : Ω) (t : ℝ) (x : ℤ) :
    zN n ψ ω t x * Real.exp (b * rescaledPosition n t x) =
      Real.exp (expMomKappa n b * t) *
        (expMomAlpha n b (n * t / 2) x * density ψ ω (n * t / 2) x) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hh : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have h1 : n ^ (-1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hn0]; norm_num
  have h2 : n ^ (3 / 4 : ℝ) = n ^ (1 / 4 : ℝ) * n ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have h1' : n ^ (-1 / 2 : ℝ) = 1 / n ^ (1 / 2 : ℝ) := by field_simp; linarith
  have e : thetaN n * x - n * lambdaN n / 2 * t + b * ((x - n ^ (3 / 4 : ℝ) * t) / n ^ (1 / 2 : ℝ))
      = expMomKappa n b * t + (expMomTheta n b * x -
        2 * (Real.cosh (expMomTheta n b) - 1) * (n * t / 2)) := by
    rw [expMomKappa, expMomTheta, lambdaN, h2, h1']
    field_simp
    ring
  rw [zN, expMomAlpha, rescaledPosition,
    show ∀ A P B : ℝ, Real.exp A * P * Real.exp B = Real.exp (A + B) * P from fun A P B => by
      rw [Real.exp_add]; ring, e, Real.exp_add]
  ring

/-- **`𝖹_n(t;e_b) = e^{κ t} N_b(nt/2)`**, for every realization and every `t` (both sides are
`tsum`s of the same terms, up to the constant factor `e^{κ t}`). -/
theorem expMom_pairZ_eq {n : ℝ} (hn : 1 ≤ n) (b : ℝ) (ω : Ω) (t : ℝ) :
    pairZ n ψ ω t (fun y => Real.exp (b * y)) =
      Real.exp (expMomKappa n b * t) * expMomN n b ψ (n * t / 2) ω := by
  rw [pairZ, expMomN, ← tsum_mul_left]
  exact tsum_congr fun x => expMom_term_eq hn b ω t x

/-! ### The martingale `N_b` -/

/-- `α_s(x) ≤ e^{|θ'| |x|}` for `s ≥ 0`. -/
lemma expMom_alpha_le (n b : ℝ) {s : ℝ} (hs : 0 ≤ s) (x : ℤ) :
    expMomAlpha n b s x ≤ Real.exp (|expMomTheta n b| * |(x : ℝ)|) := by
  rw [expMomAlpha]
  gcongr
  have h1 : 0 ≤ 2 * (Real.cosh (expMomTheta n b) - 1) * s := by
    have := Real.one_le_cosh (expMomTheta n b)
    have : 0 ≤ Real.cosh (expMomTheta n b) - 1 := by linarith
    positivity
  have h2 : expMomTheta n b * x ≤ |expMomTheta n b| * |(x : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  linarith

/-- `N_b(s) ≥ 0`. -/
lemma expMomN_nonneg (n b : ℝ) (s : ℝ) (ω : Ω) : 0 ≤ expMomN n b ψ s ω :=
  tsum_nonneg fun x => mul_nonneg (Real.exp_pos _).le (tilt_density_nonneg ω s x)

/-- `∂ₛα_s(x) + Δα_s(x) = 0`, with `∂ₛα_s = -2 (cosh θ' - 1) α_s`. -/
private lemma expMom_heat (n b s : ℝ) (x : ℤ) :
    -(2 * (Real.cosh (expMomTheta n b) - 1)) * expMomAlpha n b s x +
      lap (expMomAlpha n b s) x = 0 := by
  simp only [lap, expMomAlpha]
  push_cast
  have e1 : ∀ θ k : ℝ, Real.exp (θ * ((x : ℝ) + 1) - k * s) =
      Real.exp (θ * x - k * s) * Real.exp θ := fun θ k => by
    rw [← Real.exp_add]; ring_nf
  have e2 : ∀ θ k : ℝ, Real.exp (θ * ((x : ℝ) - 1) - k * s) =
      Real.exp (θ * x - k * s) * Real.exp (-θ) := fun θ k => by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2, Real.cosh_eq]
  ring

/-- The derivative of `s ↦ α_s(x)`. -/
private lemma expMom_hasDerivAt (n b s : ℝ) (x : ℤ) :
    HasDerivAt (fun s => expMomAlpha n b s x)
      (-(2 * (Real.cosh (expMomTheta n b) - 1)) * expMomAlpha n b s x) s := by
  have h := (((hasDerivAt_id s).const_mul (2 * (Real.cosh (expMomTheta n b) - 1))).const_sub
    (expMomTheta n b * x)).exp
  refine h.congr_deriv ?_
  show _ = -(2 * (Real.cosh (expMomTheta n b) - 1)) * Real.exp (expMomTheta n b * x -
    2 * (Real.cosh (expMomTheta n b) - 1) * s)
  simp only [id]; ring

/-- `waveInit` gives `P(0,·) = 𝟙_{· = 0}`; so `N_b(0) = 1`. -/
private lemma expMomN_zero_of_init {ω : Ω} (h : ψ 0 ω = waveInit) (n b : ℝ) :
    expMomN n b ψ 0 ω = 1 := by
  have hd : ∀ x, density ψ ω 0 x = if x = 0 then 1 else 0 := fun x => by
    rw [density, h, waveInit_apply]
    split_ifs <;> simp
  simp only [expMomN, hd, mul_ite, mul_one, mul_zero]
  rw [tsum_ite_eq]
  simp [expMomAlpha]

/-- **`N_b` is a martingale** (Lemma 2.3 (1) with `α_s(x) = e^{θ' x - 2 (cosh θ' - 1) s}`): for
`T > 0`, `N_b` is a continuous square-integrable `𝓕`-martingale on `[0,T]`, and
`𝔼[N_b(s)] = 1` for `s ∈ [0,T]`. -/
theorem expMom_isCL2Mart [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (n b : ℝ) {T : ℝ} (hT : 0 < T) :
    IsCL2Mart T 𝓕 (expMomN n b ψ) μ ∧
      ∀ s ∈ Icc (0 : ℝ) T, ∫ ω, expMomN n b ψ s ω ∂μ = 1 := by
  set k := 2 * (Real.cosh (expMomTheta n b) - 1) with hk
  have hk0 : 0 ≤ k := by have := Real.one_le_cosh (expMomTheta n b); rw [hk]; linarith
  have hbd : ∀ x : ℤ, ∀ t ∈ Icc 0 T, |expMomAlpha n b t x| + |-k * expMomAlpha n b t x| ≤
      (1 + k) * Real.exp (|expMomTheta n b| * |(x : ℝ)|) := by
    intro x t ht
    have h0 : 0 ≤ expMomAlpha n b t x := (Real.exp_pos _).le
    have h1 := expMom_alpha_le n b ht.1 x
    rw [abs_of_nonneg h0, abs_mul, abs_neg, abs_of_nonneg hk0, abs_of_nonneg h0]
    nlinarith
  obtain ⟨-, hL⟩ := lemma_2_3_linear hB hψ hT (abs_nonneg (expMomTheta n b))
    (α := expMomAlpha n b) (α' := fun s x => -k * expMomAlpha n b s x)
    (fun x t _ => (expMom_hasDerivAt n b t x).hasDerivWithinAt)
    (fun x => (Continuous.continuousOn (by unfold expMomAlpha; fun_prop))) hbd
  -- the drift vanishes, so the martingale of Lemma 2.3 (1) is `N_b - 1`
  have hM : (fun t ω => ∑' x, expMomAlpha n b t x * density ψ ω t x - expMomAlpha n b 0 0 -
      ∫ s in (0 : ℝ)..t, ∑' x, ((fun s x => -k * expMomAlpha n b s x) s x +
        lap (expMomAlpha n b s) x) * density ψ ω s x) =
      fun t ω => expMomN n b ψ t ω + (-1) := by
    funext t ω
    simp only [expMom_heat, zero_mul, tsum_zero, intervalIntegral.integral_zero, sub_zero, hk]
    simp [expMomN, expMomAlpha, sub_eq_add_neg]
  have h1 : IsCL2Mart T 𝓕 (fun t ω => expMomN n b ψ t ω + (-1)) μ := hM ▸ hL.toIsCL2Mart
  have hconst : IsCL2Mart T 𝓕 (fun _ _ => (1 : ℝ)) μ :=
    isCL2Mart_of_martingale (martingale_const 𝓕 μ 1) (ae_of_all _ fun _ => continuousOn_const)
      fun _ _ => memLp_const 1
  have h2 : IsCL2Mart T 𝓕 (expMomN n b ψ) μ := by
    have := h1.add hconst
    simp only [neg_add_cancel_right] at this
    exact this
  refine ⟨h2, fun s hs => ?_⟩
  have hc := h2.condExp 0 s.toNNReal (by positivity) (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  rw [Real.coe_toNNReal _ hs.1, NNReal.coe_zero] at hc
  rw [← integral_condExp (𝓕.le 0), integral_congr_ae hc]
  calc ∫ ω, expMomN n b ψ 0 ω ∂μ = ∫ _, (1 : ℝ) ∂μ :=
        integral_congr_ae (hψ.ae_init.mono fun ω h => expMomN_zero_of_init h n b)
    _ = 1 := by simp

/-- Almost surely, for all `t ≥ 0` and `b ∈ [-1,1]`, `∑ₓ 𝔷_n(t,x) e^{b y_n(t,x)}` converges
(domination by `e^{κ t} e^{2|x|} P(nt/2,x) ≤ e^{κ t} K e^{-|x|}`, moment bound (2.2)). -/
theorem expMom_ae_summable [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → ∀ b ∈ Icc (-1 : ℝ) 1,
      Summable fun x => zN n ψ ω t x * Real.exp (b * rescaledPosition n t x) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  filter_upwards [tilt_ae_dom hB hψ (a := 3) (by norm_num)] with ω hω t ht b hb
  obtain ⟨K, hK⟩ := hω ⌈n * t / 2⌉₊
  have hs : n * t / 2 ∈ Icc (0 : ℝ) ⌈n * t / 2⌉₊ := ⟨by positivity, Nat.le_ceil _⟩
  refine Summable.of_nonneg_of_le (fun x => mul_nonneg (tiltZ_nonneg n ω t x)
    (Real.exp_pos _).le) (fun x => ?_)
    (tilt_summable_exp_neg_abs.mul_left (Real.exp (expMomKappa n b * t) * K))
  rw [expMom_term_eq hn b ω t x]
  have hP := tilt_density_nonneg (ψ := ψ) ω (n * t / 2) x
  have hα := expMom_alpha_le n b (by positivity : 0 ≤ n * t / 2) x
  have hθ := expMom_abs_theta_le hn hb
  have hx := abs_nonneg (x : ℝ)
  have e : Real.exp (3 * |(x : ℝ)|) = Real.exp (2 * |(x : ℝ)|) * Real.exp (|(x : ℝ)|) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := hK _ hs x
  rw [e] at h3
  have h4 : expMomAlpha n b (n * t / 2) x ≤ Real.exp (2 * |(x : ℝ)|) :=
    hα.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hθ hx))
  have h5 : expMomAlpha n b (n * t / 2) x * density ψ ω (n * t / 2) x ≤
      K * Real.exp (-|(x : ℝ)|) := by
    have hmul : Real.exp (|(x : ℝ)|) * Real.exp (-|(x : ℝ)|) = 1 := by
      rw [← Real.exp_add]; simp
    calc expMomAlpha n b (n * t / 2) x * density ψ ω (n * t / 2) x
        ≤ Real.exp (2 * |(x : ℝ)|) * density ψ ω (n * t / 2) x := by gcongr
      _ = Real.exp (2 * |(x : ℝ)|) * density ψ ω (n * t / 2) x * Real.exp (|(x : ℝ)|) *
          Real.exp (-|(x : ℝ)|) := by rw [mul_assoc _ (Real.exp _), hmul, mul_one]
      _ ≤ K * Real.exp (-|(x : ℝ)|) := by
          gcongr
          linarith
  calc Real.exp (expMomKappa n b * t) *
        (expMomAlpha n b (n * t / 2) x * density ψ ω (n * t / 2) x)
      ≤ Real.exp (expMomKappa n b * t) * (K * Real.exp (-|(x : ℝ)|)) := by gcongr
    _ = _ := by ring

/-! ### The two estimates of Lemma 5.2 -/

/-- **First part of Lemma 5.2**: for `b ∈ [-1,1]` and `t ≥ 0`, `𝖹_n(t;e_b) = e^{κ t} N_b(nt/2)`
is integrable and `𝔼[𝖹_n(t;e_b)] = e^{κ t} ≤ e^{2t}`. -/
theorem expMom_integral_le [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => pairZ n ψ ω t fun y => Real.exp (b * y)) μ ∧
      ∫ ω, pairZ n ψ ω t (fun y => Real.exp (b * y)) ∂μ ≤ Real.exp (2 * t) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨hM, hE⟩ := expMom_isCL2Mart hB hψ n b (T := n * t / 2 + 1) (by positivity)
  have hs : n * t / 2 ∈ Icc (0 : ℝ) (n * t / 2 + 1) := ⟨by positivity, by linarith⟩
  have hL := hM.memLp (n * t / 2).toNNReal (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  rw [Real.coe_toNNReal _ hs.1] at hL
  have e : (fun ω => pairZ n ψ ω t fun y => Real.exp (b * y)) =
      fun ω => Real.exp (expMomKappa n b * t) * expMomN n b ψ (n * t / 2) ω :=
    funext fun ω => expMom_pairZ_eq hn b ω t
  rw [e]
  refine ⟨(hL.integrable one_le_two).const_mul _, ?_⟩
  rw [integral_const_mul, hE _ hs, mul_one]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (expMom_kappa_le hn hb) ht)

/-- Doob's maximal inequality for `𝖹_n(·;e_b)`: for `b ∈ [-1,1]`, `T > 0` and `K > 0`,
`ℙ(∃ t ∈ [0,T], 𝖹_n(t;e_b) ≥ K) ≤ e^{2T}/K` (from `𝖹_n(t;e_b) ≤ e^{2T} N_b(nt/2)` and Doob's
inequality for the nonnegative martingale `N_b` on `[0, nT/2]`, with `𝔼[N_b(nT/2)] = 1`). -/
theorem expMom_measure_exists_ge_le [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1)
    {T K : ℝ} (hT : 0 < T) (hK : 0 < K) :
    μ {ω | ∃ t ∈ Icc (0 : ℝ) T, K ≤ pairZ n ψ ω t fun y => Real.exp (b * y)} ≤
      ENNReal.ofReal (Real.exp (2 * T) / K) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hT' : 0 < n * T / 2 := by positivity
  obtain ⟨hM, hE⟩ := expMom_isCL2Mart hB hψ n b hT'
  have hD := hM.measure_exists_ge_le (ae_of_all _ fun ω t _ => expMomN_nonneg n b t ω)
    (K := K * Real.exp (-(2 * T))) (by positivity)
  rw [hE _ ⟨hT'.le, le_rfl⟩] at hD
  refine le_trans (measure_mono ?_) (hD.trans_eq ?_)
  · rintro ω ⟨t, ht, hKt⟩
    refine ⟨n * t / 2, ⟨by have := ht.1; positivity, by have := ht.2; nlinarith⟩, ?_⟩
    rw [expMom_pairZ_eq hn b ω t] at hKt
    have hk : Real.exp (expMomKappa n b * t) ≤ Real.exp (2 * T) :=
      Real.exp_le_exp.2 (by nlinarith [expMom_kappa_le hn hb, ht.1, ht.2])
    have hN := expMomN_nonneg (ψ := ψ) n b (n * t / 2) ω
    have h1 : K ≤ Real.exp (2 * T) * expMomN n b ψ (n * t / 2) ω :=
      hKt.trans (mul_le_mul_of_nonneg_right hk hN)
    rw [Real.exp_neg]
    calc K * (Real.exp (2 * T))⁻¹
        ≤ Real.exp (2 * T) * expMomN n b ψ (n * t / 2) ω * (Real.exp (2 * T))⁻¹ := by gcongr
      _ = expMomN n b ψ (n * t / 2) ω := by field_simp
  · congr 1
    rw [Real.exp_neg]
    field_simp

/-- **(5.1)**: for `T > 0` and `K > 0`, `ℙ(sup_{t ∈ [0,T]} 𝖹_n(t;cosh) ≥ K) ≤ 2 e^{2T}/K`
(outer probability, supremum in `[0,∞]`). On the almost sure event where the series converge,
`𝖹_n(t;cosh) = (𝖹_n(t;e_1) + 𝖹_n(t;e_{-1}))/2`, so for `0 < K' < K` the event is contained in
`{∃ t, 𝖹_n(t;e_1) ≥ K'} ∪ {∃ t, 𝖹_n(t;e_{-1}) ≥ K'}`, of probability at most `2 e^{2T}/K'`;
then `K' → K`. -/
theorem expMom_compact_containment [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {T K : ℝ} (hT : 0 < T) (hK : 0 < K) :
    μ {ω | ENNReal.ofReal K ≤ ⨆ t ∈ Icc (0 : ℝ) T,
      ENNReal.ofReal (pairZ n ψ ω t Real.cosh)} ≤
      ENNReal.ofReal (2 * Real.exp (2 * T) / K) := by
  set S := {ω | ENNReal.ofReal K ≤ ⨆ t ∈ Icc (0 : ℝ) T,
      ENNReal.ofReal (pairZ n ψ ω t Real.cosh)} with hS_def
  have hsum := expMom_ae_summable hB hψ hn
  have hb1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hb2 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hbound : ∀ K' : ℝ, K' ∈ Ioo 0 K → μ S ≤ ENNReal.ofReal (2 * Real.exp (2 * T) / K') := by
    rintro K' ⟨hK', hKK⟩
    set E : ℝ → Set Ω := fun b =>
      {ω | ∃ t ∈ Icc (0 : ℝ) T, K' ≤ pairZ n ψ ω t fun y => Real.exp (b * y)} with hE_def
    have hsub : S ≤ᵐ[μ] (E 1 ∪ E (-1) : Set Ω) := by
      filter_upwards [hsum] with ω hω hSω
      by_contra hnot
      simp only [hE_def, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
        not_le] at hnot
      have hlt : ∀ t ∈ Icc (0 : ℝ) T, pairZ n ψ ω t Real.cosh < K' := by
        intro t ht
        have h1 := hω t ht.1 1 hb1
        have h2 := hω t ht.1 (-1) hb2
        have e : pairZ n ψ ω t Real.cosh = ((pairZ n ψ ω t fun y => Real.exp (1 * y)) +
            pairZ n ψ ω t fun y => Real.exp (-1 * y)) / 2 := by
          rw [pairZ, pairZ, pairZ, ← h1.tsum_add h2, ← tsum_div_const]
          congr 1
          funext x
          rw [Real.cosh_eq]
          simp only [one_mul, neg_one_mul]
          ring
        rw [e]
        linarith [hnot.1 t ht, hnot.2 t ht]
      have hle : (⨆ t ∈ Icc (0 : ℝ) T, ENNReal.ofReal (pairZ n ψ ω t Real.cosh)) ≤
          ENNReal.ofReal K' :=
        iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal (hlt t ht).le
      have := (show ω ∈ S from hSω).trans hle
      rw [ENNReal.ofReal_le_ofReal_iff hK'.le] at this
      linarith
    calc μ S ≤ μ (E 1 ∪ E (-1)) := measure_mono_ae hsub
      _ ≤ μ (E 1) + μ (E (-1)) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (2 * T) / K') + ENNReal.ofReal (Real.exp (2 * T) / K') :=
          add_le_add (expMom_measure_exists_ge_le hB hψ hn hb1 hT hK')
            (expMom_measure_exists_ge_le hB hψ hn hb2 hT hK')
      _ = ENNReal.ofReal (2 * Real.exp (2 * T) / K') := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hlim : Tendsto (fun K' => ENNReal.ofReal (2 * Real.exp (2 * T) / K')) (𝓝[<] K)
      (𝓝 (ENNReal.ofReal (2 * Real.exp (2 * T) / K))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds.div tendsto_id hK.ne').mono_left nhdsWithin_le_nhds)
  exact ge_of_tendsto hlim (Filter.eventually_of_mem (Ioo_mem_nhdsLT hK) hbound)

end QSSEPtoKPZ
