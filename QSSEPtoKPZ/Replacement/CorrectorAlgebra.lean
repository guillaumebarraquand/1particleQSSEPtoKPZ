/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorDefs
public import QSSEPtoKPZ.Replacement.CorrectorCalculus

/-!
# Lemma 6.4: the functions `f_t`, `∂ₜf_t`, the drift and the remainder (6.16)

Task G1. For `n ≥ 1`, `m ≥ 1` and `φ ∈ C_b^{1,3}([0,T] × ℝ)` we define, following the proof of
Lemma 6.4 (with `κ_n = 2/(c_n n^{1/2})`, `G(x₁,x₂) = g_m(x₂ - x₁)` and
`Φ_t(x₁,x₂) = φ_t(y_n(t,x₁)) φ_t(y_n(t,x₂))`):

* `corrF`: `f_t = κ_n G Φ_t`, so that `𝖥_n(t) = 𝒵_n^{⊗2}(t;f_t)`;
* `corrDt`: `∂ₜ[φ_t(y_n(t,x))] = ∂ₜφ_t(y_n(t,x)) - n^{1/4} ∂ₓφ_t(y_n(t,x))`, and `corrF'`: `∂ₜf_t`;
* `corrDrift`: the integrand `∂ₜf_t + (n/2) 𝒬^{θ_n} f_t + (nλ_n/2) 𝟙_{|x₁-x₂|=1} f_t` of (3.21);
* `corrEdens`, `corrBdens`: the integrands of `ℰ_n(t;φ_t)` (after symmetrization) and
  `𝖡_n(t;φ_t)`;
* `corrRem = corrDrift - corrEdens + corrBdens`: the integrand of the remainder (6.16).

Main results: the product rule `corr_tiltedInclGen_mul` for `𝒬^θ` (with the carré du champ
`corrGamma = Γ^θ`), the identity `corrRem_eq`
`corrRem = κ_n G ((∂ₜ + 𝒜_n)φ_t ⊗ φ_t + φ_t ⊗ (∂ₜ + 𝒜_n)φ_t) + (n/2) κ_n Γ^{θ_n}(G, Φ_t)`
(equation (6.16) and the computation following it), the bound (6.14) at the level of the
integrand (`abs_corrRem_le`), its vanishing for `φ ≡ 1`, and the bound on the integrand of the
bracket used for (6.15) (`abs_corrBracket_le`).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace QSSEPtoKPZ

/-! ### Definitions -/

/-- `κ_n = 2/(c_n n^{1/2})`, the prefactor of (6.9). -/
def corrPref (n : ℝ) : ℝ := 2 / (cN n * n ^ (1 / 2 : ℝ))

/-- `f_t(x₁,x₂) = κ_n g_m(x₂ - x₁) φ_t(y_n(t,x₁)) φ_t(y_n(t,x₂))` (proof of Lemma 6.4). -/
def corrF (n : ℝ) (ρ : ℝ → ℝ) (m : ℕ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (x₁ x₂ : ℤ) : ℝ :=
  corrPref n * (gM ρ m (x₂ - x₁) * φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂))

/-- `∂ₜ[φ_t(y_n(t,x))] = ∂ₜφ_t(y_n(t,x)) - n^{1/4} ∂ₓφ_t(y_n(t,x))`. -/
def corrDt (n : ℝ) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (x : ℤ) : ℝ :=
  φt t (rescaledPosition n t x) - n ^ (1 / 4 : ℝ) * deriv (φ t) (rescaledPosition n t x)

/-- `∂ₜf_t(x₁,x₂)`. -/
def corrF' (n : ℝ) (ρ : ℝ → ℝ) (m : ℕ) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (x₁ x₂ : ℤ) : ℝ :=
  corrPref n * (gM ρ m (x₂ - x₁) * (corrDt n φ φt t x₁ * φ t (rescaledPosition n t x₂) +
    φ t (rescaledPosition n t x₁) * corrDt n φ φt t x₂))

/-- The integrand of the drift in (3.21) for `f = f_t`. -/
def corrDrift (n : ℝ) (ρ : ℝ → ℝ) (m : ℕ) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (x₁ x₂ : ℤ) : ℝ :=
  corrF' n ρ m φ φt t x₁ x₂ + n / 2 * tiltedInclGen (thetaN n) (corrF n ρ m φ t) x₁ x₂ +
    n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then corrF n ρ m φ t x₁ x₂ else 0)

/-- `n^{1/2} (1/2) 𝟙_{|x₂-x₁|=1} Φ_t(x₁,x₂)`, whose `𝒵_n^{⊗2}(t)`-integral is `ℰ_n(t;φ_t)`. -/
def corrEdens (n : ℝ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (x₁ x₂ : ℤ) : ℝ :=
  n ^ (1 / 2 : ℝ) * (1 / 2 * (if |x₂ - x₁| = 1 then 1 else 0)) *
    (φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂))

/-- `n^{1/2} k_m(x₂ - x₁) Φ_t(x₁,x₂)`, whose `𝒵_n^{⊗2}(t)`-integral is `𝖡_n(t;φ_t)`. -/
def corrBdens (n : ℝ) (ρ : ℝ → ℝ) (m : ℕ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (x₁ x₂ : ℤ) : ℝ :=
  n ^ (1 / 2 : ℝ) * (kM ρ m (x₂ - x₁) * φ t (rescaledPosition n t x₁) *
    φ t (rescaledPosition n t x₂))

/-- The integrand of the remainder (6.16): `corrDrift - corrEdens + corrBdens`. -/
def corrRem (n : ℝ) (ρ : ℝ → ℝ) (m : ℕ) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (x₁ x₂ : ℤ) : ℝ :=
  corrDrift n ρ m φ φt t x₁ x₂ - corrEdens n φ t x₁ x₂ + corrBdens n ρ m φ t x₁ x₂

/-- The free part of the carré du champ `Γ^θ(G,Φ)` of `𝒬^θ` (jumps of the first line of (3.19)). -/
def corrGammaFree (θ : ℝ) (G Φ : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ :=
  Real.exp θ * ((G (x₁ + 1) x₂ - G x₁ x₂) * (Φ (x₁ + 1) x₂ - Φ x₁ x₂) +
      (G x₁ (x₂ + 1) - G x₁ x₂) * (Φ x₁ (x₂ + 1) - Φ x₁ x₂)) +
  Real.exp (-θ) * ((G (x₁ - 1) x₂ - G x₁ x₂) * (Φ (x₁ - 1) x₂ - Φ x₁ x₂) +
      (G x₁ (x₂ - 1) - G x₁ x₂) * (Φ x₁ (x₂ - 1) - Φ x₁ x₂))

/-- The inclusion part of the carré du champ `Γ^θ(G,Φ)` (additional jumps when `|x₁-x₂| = 1`). -/
def corrGammaIncl (θ : ℝ) (G Φ : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ :=
  (if x₂ = x₁ + 1 then Real.exp θ * ((G x₂ x₂ - G x₁ x₂) * (Φ x₂ x₂ - Φ x₁ x₂)) +
      Real.exp (-θ) * ((G x₁ x₁ - G x₁ x₂) * (Φ x₁ x₁ - Φ x₁ x₂)) else 0) +
  (if x₂ = x₁ - 1 then Real.exp (-θ) * ((G x₂ x₂ - G x₁ x₂) * (Φ x₂ x₂ - Φ x₁ x₂)) +
      Real.exp θ * ((G x₁ x₁ - G x₁ x₂) * (Φ x₁ x₁ - Φ x₁ x₂)) else 0)

/-! ### Algebra of `𝒬^θ` -/

/-- The product rule for `𝒬^θ`: `𝒬^θ(GΦ) = Φ 𝒬^θG + G 𝒬^θΦ + Γ^θ(G,Φ)`. -/
lemma corr_tiltedInclGen_mul (θ : ℝ) (G Φ : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) :
    tiltedInclGen θ (fun a b => G a b * Φ a b) x₁ x₂ =
      Φ x₁ x₂ * tiltedInclGen θ G x₁ x₂ + G x₁ x₂ * tiltedInclGen θ Φ x₁ x₂ +
        (corrGammaFree θ G Φ x₁ x₂ + corrGammaIncl θ G Φ x₁ x₂) := by
  unfold tiltedInclGen corrGammaFree corrGammaIncl
  split_ifs <;> ring

/-- `𝒬^θ` is linear: `𝒬^θ(κ F) = κ 𝒬^θ F`. -/
lemma corr_tiltedInclGen_const_mul (θ κ : ℝ) (F : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) :
    tiltedInclGen θ (fun a b => κ * F a b) x₁ x₂ = κ * tiltedInclGen θ F x₁ x₂ := by
  unfold tiltedInclGen
  split_ifs <;> ring

/-- On a product `U ⊗ U`, away from the diagonal neighbours, the two particles move
independently: `𝒬^θ(U ⊗ U) = U(x₂) L U(x₁) + U(x₁) L U(x₂)` with
`L U(x) = e^θ (U(x+1) - U(x)) + e^{-θ} (U(x-1) - U(x))`. -/
lemma corr_tiltedInclGen_prod (θ : ℝ) (U : ℤ → ℝ) {x₁ x₂ : ℤ} (h₁ : x₂ ≠ x₁ + 1)
    (h₂ : x₂ ≠ x₁ - 1) :
    tiltedInclGen θ (fun a b => U a * U b) x₁ x₂ =
      U x₂ * (Real.exp θ * (U (x₁ + 1) - U x₁) + Real.exp (-θ) * (U (x₁ - 1) - U x₁)) +
      U x₁ * (Real.exp θ * (U (x₂ + 1) - U x₂) + Real.exp (-θ) * (U (x₂ - 1) - U x₂)) := by
  unfold tiltedInclGen
  simp only [h₁, h₂, ↓reduceIte]
  ring

/-! ### Elementary facts -/

/-- `y_n(t,x+1) = y_n(t,x) + n^{-1/2}`. -/
lemma corr_rescaledPosition_add_one {n : ℝ} (hn : 0 < n) (t : ℝ) (x : ℤ) :
    rescaledPosition n t (x + 1) = rescaledPosition n t x + n ^ (-1 / 2 : ℝ) := by
  have hS : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hn.le]
  unfold rescaledPosition
  push_cast
  field_simp
  ring

/-- `y_n(t,x-1) = y_n(t,x) - n^{-1/2}`. -/
lemma corr_rescaledPosition_sub_one {n : ℝ} (hn : 0 < n) (t : ℝ) (x : ℤ) :
    rescaledPosition n t (x - 1) = rescaledPosition n t x - n ^ (-1 / 2 : ℝ) := by
  have := corr_rescaledPosition_add_one hn t (x - 1)
  rw [sub_add_cancel] at this
  linarith

/-- `y_n(t,x₂) - y_n(t,x₁) = (x₂ - x₁) n^{-1/2}`. -/
lemma corr_rescaledPosition_sub {n : ℝ} (hn : 0 < n) (t : ℝ) (x₁ x₂ : ℤ) :
    rescaledPosition n t x₂ - rescaledPosition n t x₁ = ((x₂ - x₁ : ℤ) : ℝ) * n ^ (-1 / 2 : ℝ) := by
  have hS : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hn.le]
  unfold rescaledPosition
  push_cast
  field_simp
  ring

/-- `y_n(t,x) = x n^{-1/2} - n^{1/4} t`, an affine function of `t`. -/
lemma corr_rescaledPosition_eq_line {n : ℝ} (hn : 0 < n) (t : ℝ) (x : ℤ) :
    rescaledPosition n t x = (x : ℝ) / n ^ (1 / 2 : ℝ) + -n ^ (1 / 4 : ℝ) * t := by
  have hS : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  have h : n ^ (3 / 4 : ℝ) = n ^ (1 / 4 : ℝ) * n ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hn]; norm_num
  unfold rescaledPosition
  rw [h]
  field_simp
  ring

/-- Constants: `n^{1/2} n^{-1/2} = 1`, `(n^{1/2})² = n`, `e^{±θ} = c ± s`. -/
lemma corr_consts {n : ℝ} (hn : 1 ≤ n) :
    n ^ (1 / 2 : ℝ) * n ^ (-1 / 2 : ℝ) = 1 ∧ n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) = n ∧
      0 < n ^ (1 / 2 : ℝ) ∧ 0 < n ^ (-1 / 2 : ℝ) ∧ 1 ≤ cN n ∧
      Real.exp (thetaN n) = cN n + Real.sinh (thetaN n) ∧
      Real.exp (-thetaN n) = cN n - Real.sinh (thetaN n) ∧ 0 ≤ Real.sinh (thetaN n) ∧
      Real.sinh (thetaN n) ≤ n ^ (-1 / 4 : ℝ) * cN n ∧ 0 < thetaN n := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hθ : 0 < thetaN n := Real.rpow_pos_of_pos hn0 _
  refine ⟨?_, ?_, Real.rpow_pos_of_pos hn0 _, Real.rpow_pos_of_pos hn0 _, Real.one_le_cosh _,
    (Real.cosh_add_sinh _).symm, (Real.cosh_sub_sinh _).symm, Real.sinh_nonneg_iff.2 hθ.le,
    sinh_le_mul_cosh hθ.le, hθ⟩
  · rw [← Real.rpow_add hn0]; norm_num
  · rw [← Real.rpow_add hn0]; norm_num

/-- `κ_n n/2 c_n = n^{1/2}`, `κ_n ≥ 0`, `κ_n ≤ 2 n^{-1/2}`. -/
lemma corrPref_props {n : ℝ} (hn : 1 ≤ n) :
    n / 2 * corrPref n * cN n = n ^ (1 / 2 : ℝ) ∧ 0 ≤ corrPref n ∧
      corrPref n ≤ 2 * n ^ (-1 / 2 : ℝ) ∧ corrPref n * n ^ (1 / 2 : ℝ) * cN n = 2 := by
  obtain ⟨h1, h2, hS, hh, hc, -⟩ := corr_consts hn
  have hc0 : 0 < cN n := zero_lt_one.trans_le hc
  unfold corrPref
  refine ⟨?_, by positivity, ?_, ?_⟩
  · field_simp; nlinarith
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ n ^ (-1 / 2 : ℝ) *
      n ^ (1 / 2 : ℝ))]
  · field_simp

/-- `|a b c| ≤ A B C`. -/
lemma corr_abs_mul3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C := by
  rw [abs_mul, abs_mul]
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hA) hc (abs_nonneg _) (mul_nonneg hA hB)

/-- The free part of `Γ^θ(G,Φ)` for `G = g(x₂-x₁)`, `Φ = U ⊗ U`, written with real numbers: it is
`c h (g(r+1) - g(r-1)) (U₁ V₂ - V₁ U₂)` up to an error `≤ s h C² + c h² C²` (proof of
Lemma 6.4, bound on `Γ_free`), where `e^{±θ} = c ± s`, `h = n^{-1/2}` and `V = ∂ₓφ`. -/
lemma corr_gammaFree_bound {ep em c s h C gp gm gr U1 U2 U1p U1m U2p U2m V1 V2 : ℝ}
    (hep : ep = c + s) (hem : em = c - s) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hgp : |gp - gr| ≤ 1 / 4) (hgm : |gm - gr| ≤ 1 / 4) (hU1 : |U1| ≤ C) (hU2 : |U2| ≤ C)
    (h1p : |U1p - U1| ≤ C * h) (h1m : |U1m - U1| ≤ C * h) (h2p : |U2p - U2| ≤ C * h)
    (h2m : |U2m - U2| ≤ C * h) (t1p : |U1p - U1 - h * V1| ≤ C * h ^ 2)
    (t1m : |U1m - U1 + h * V1| ≤ C * h ^ 2) (t2p : |U2p - U2 - h * V2| ≤ C * h ^ 2)
    (t2m : |U2m - U2 + h * V2| ≤ C * h ^ 2) :
    |ep * ((gm - gr) * (U1p * U2 - U1 * U2) + (gp - gr) * (U1 * U2p - U1 * U2)) +
        em * ((gp - gr) * (U1m * U2 - U1 * U2) + (gm - gr) * (U1 * U2m - U1 * U2)) -
        c * h * (gp - gm) * (U1 * V2 - V1 * U2)| ≤ s * h * C ^ 2 + c * h ^ 2 * C ^ 2 := by
  set X := (gm - gr) * (U1p - U1) * U2 + (gp - gr) * U1 * (U2p - U2) -
    (gp - gr) * (U1m - U1) * U2 - (gm - gr) * U1 * (U2m - U2)
  set Y := (gm - gr) * (U1p - U1 - h * V1) * U2 + (gp - gr) * U1 * (U2p - U2 - h * V2) +
    (gp - gr) * (U1m - U1 + h * V1) * U2 + (gm - gr) * U1 * (U2m - U2 + h * V2)
  have e : ep * ((gm - gr) * (U1p * U2 - U1 * U2) + (gp - gr) * (U1 * U2p - U1 * U2)) +
        em * ((gp - gr) * (U1m * U2 - U1 * U2) + (gm - gr) * (U1 * U2m - U1 * U2)) -
        c * h * (gp - gm) * (U1 * V2 - V1 * U2) = s * X + c * Y := by
    rw [hep, hem]; ring
  have hU1' : |U1| ≤ C := hU1
  have hX : |X| ≤ h * C ^ 2 := by
    have a1 := corr_abs_mul3_le hgm h1p hU2
    have a2 := corr_abs_mul3_le hgp hU1' h2p
    have a3 := corr_abs_mul3_le hgp h1m hU2
    have a4 := corr_abs_mul3_le hgm hU1' h2m
    calc |X| ≤ |(gm - gr) * (U1p - U1) * U2| + |(gp - gr) * U1 * (U2p - U2)| +
          |(gp - gr) * (U1m - U1) * U2| + |(gm - gr) * U1 * (U2m - U2)| := by
          simp only [X]
          refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by nlinarith
  have hY : |Y| ≤ h ^ 2 * C ^ 2 := by
    have a1 := corr_abs_mul3_le hgm t1p hU2
    have a2 := corr_abs_mul3_le hgp hU1' t2p
    have a3 := corr_abs_mul3_le hgp t1m hU2
    have a4 := corr_abs_mul3_le hgm hU1' t2m
    calc |Y| ≤ |(gm - gr) * (U1p - U1 - h * V1) * U2| + |(gp - gr) * U1 * (U2p - U2 - h * V2)| +
          |(gp - gr) * (U1m - U1 + h * V1) * U2| + |(gm - gr) * U1 * (U2m - U2 + h * V2)| := by
          simp only [Y]
          exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by nlinarith
  rw [e]
  calc |s * X + c * Y| ≤ |s * X| + |c * Y| := abs_add_le _ _
    _ = s * |X| + c * |Y| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hc]
    _ ≤ s * (h * C ^ 2) + c * (h ^ 2 * C ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hX hs) (mul_le_mul_of_nonneg_left hY hc)
    _ = _ := by ring

/-! ### The identity (6.16) -/

variable {ρ : ℝ → ℝ} {m : ℕ} {n : ℝ} {φ φt : ℝ → ℝ → ℝ}

/-- `G(x₁,x₂) = g_m(x₂ - x₁)`. -/
abbrev corrG (ρ : ℝ → ℝ) (m : ℕ) : ℤ → ℤ → ℝ := fun a b => gM ρ m (b - a)

/-- `Φ_t(x₁,x₂) = φ_t(y_n(t,x₁)) φ_t(y_n(t,x₂))`. -/
abbrev corrPhi (n : ℝ) (φ : ℝ → ℝ → ℝ) (t : ℝ) : ℤ → ℤ → ℝ :=
  fun a b => φ t (rescaledPosition n t a) * φ t (rescaledPosition n t b)

/-- `g_m(±1) = 0`. -/
lemma corr_gM_eq_zero_of_abs_eq_one (hρ : IsMollifier ρ) (hm : 1 ≤ m) {r : ℤ} (hr : |r| = 1) :
    gM ρ m r = 0 := by
  obtain ⟨hev, -, h1, -⟩ := hρ.gM_spec hm
  rcases abs_eq (zero_le_one' ℤ) |>.1 hr with rfl | rfl
  · exact h1
  · rw [hev]; exact h1

/-- **The identity (6.16)**, at the level of the integrand: with `a_i = (∂ₜ + 𝒜_n)φ_t(y_n(t,x_i))`,
`corrRem = κ_n g_m(x₂ - x₁) (a₁ φ_t(y₂) + φ_t(y₁) a₂) + (n/2) κ_n Γ^{θ_n}(G, Φ_t)(x₁,x₂)`. -/
lemma corrRem_eq (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) (x₁ x₂ : ℤ) :
    corrRem n ρ m φ φt t x₁ x₂ =
      corrPref n * gM ρ m (x₂ - x₁) *
        ((φt t (rescaledPosition n t x₁) + AN n (φ t) (rescaledPosition n t x₁)) *
            φ t (rescaledPosition n t x₂) +
          φ t (rescaledPosition n t x₁) *
            (φt t (rescaledPosition n t x₂) + AN n (φ t) (rescaledPosition n t x₂))) +
      n / 2 * corrPref n * (corrGammaFree (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂ +
        corrGammaIncl (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  set Γ := corrGammaFree (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂ +
    corrGammaIncl (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂ with hΓ
  have hF : corrF n ρ m φ t = fun a b => corrPref n * (corrG ρ m a b * corrPhi n φ t a b) := by
    funext a b; simp only [corrF, corrG, corrPhi]; ring
  have hev : ∀ r, gM ρ m (-r) = gM ρ m r := (hρ.gM_spec hm).1
  have hQG : tiltedInclGen (thetaN n) (corrG ρ m) x₁ x₂ =
      cN n * (1 / 2 * (if |x₂ - x₁| = 1 then 1 else 0) - kM ρ m (x₂ - x₁)) := by
    rw [tiltedInclGen_diff (thetaN n) hev x₁ x₂, hρ.chainGen_gM hm]; rfl
  have hlam : (if |x₁ - x₂| = 1 then corrF n ρ m φ t x₁ x₂ else 0) = 0 := by
    split_ifs with h
    · rw [abs_sub_comm] at h
      simp only [corrF, corr_gM_eq_zero_of_abs_eq_one hρ hm h, zero_mul, mul_zero]
    · rfl
  have hGQ : corrG ρ m x₁ x₂ * tiltedInclGen (thetaN n) (corrPhi n φ t) x₁ x₂ =
      gM ρ m (x₂ - x₁) *
        (φ t (rescaledPosition n t x₂) * (Real.exp (thetaN n) *
            (φ t (rescaledPosition n t (x₁ + 1)) - φ t (rescaledPosition n t x₁)) +
          Real.exp (-thetaN n) *
            (φ t (rescaledPosition n t (x₁ - 1)) - φ t (rescaledPosition n t x₁))) +
        φ t (rescaledPosition n t x₁) * (Real.exp (thetaN n) *
            (φ t (rescaledPosition n t (x₂ + 1)) - φ t (rescaledPosition n t x₂)) +
          Real.exp (-thetaN n) *
            (φ t (rescaledPosition n t (x₂ - 1)) - φ t (rescaledPosition n t x₂)))) := by
    by_cases h : x₂ = x₁ + 1 ∨ x₂ = x₁ - 1
    · have : |x₂ - x₁| = 1 := by rcases h with h | h <;> rw [h] <;> simp
      simp only [corrG, corr_gM_eq_zero_of_abs_eq_one hρ hm this, zero_mul]
    · push Not at h
      rw [corr_tiltedInclGen_prod _ (fun a => φ t (rescaledPosition n t a)) h.1 h.2]
  have hκ := (corrPref_props hn).1
  have h2c : Real.exp (thetaN n) + Real.exp (-thetaN n) = 2 * cN n := by
    rw [cN, Real.cosh_eq]; ring
  unfold corrRem corrDrift corrEdens corrBdens
  rw [hF, corr_tiltedInclGen_const_mul, corr_tiltedInclGen_mul, hQG, ← hF, hlam, ← hΓ, hGQ]
  simp only [corrF', corrDt, AN, corrPhi, corr_rescaledPosition_add_one hn0,
    corr_rescaledPosition_sub_one hn0]
  linear_combination (-(corrPref n) * gM ρ m (x₂ - x₁) * n *
      φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂)) * h2c +
    ((φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂)) *
      (1 / 2 * (if |x₂ - x₁| = 1 then 1 else 0) - kM ρ m (x₂ - x₁))) * hκ

end QSSEPtoKPZ
