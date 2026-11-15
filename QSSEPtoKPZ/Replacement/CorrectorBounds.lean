/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorAlgebra

/-!
# Lemma 6.4: pointwise bounds on the remainder and on the bracket integrand

Task G1. With `h = n^{-1/2}`, `θ = θ_n`, `c = c_n`, `s = sinh θ_n`, for `t ∈ [0,T]` and
`‖φ‖_{1,3} ≤ C` (proof of Lemma 6.4 in the article):

* `abs_corrGammaFree_le`: `|Γ_free| ≤ 2 c m h² C² + s h C² + c h² C²`;
* `abs_corrGammaIncl_le`: `|Γ_incl| ≤ 2 c g_m(0) h C²`;
* `abs_corrRem_le`: the integrand of the remainder (6.16) is bounded by
  `(9 + 2C_ρ)(m/n^{1/2} + 1/n^{1/4} + 1/m) C²` when `g_m(0) ≤ C_ρ/m`; this gives (6.14);
* `corrRem_eq_zero_of_const`: it vanishes when `φ ≡ 1` (and `∂ₜφ = 0`);
* `abs_corrBracket_le`, `corrBracket_sq_le`: the bound on the integrand of the bracket of `N_n`,
  which gives (6.15).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace QSSEPtoKPZ

variable {ρ : ℝ → ℝ} {m : ℕ} {n T C : ℝ} {φ φt : ℝ → ℝ → ℝ}

/-- Increments of `φ_t` over a step `h ≥ 0`: Lipschitz and Taylor bounds. -/
lemma IsC13.corr_step_bounds (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) {h : ℝ}
    (hh : 0 ≤ h) (y : ℝ) :
    |φ t (y + h) - φ t y| ≤ C * h ∧ |φ t (y - h) - φ t y| ≤ C * h ∧
      |φ t (y + h) - φ t y - h * deriv (φ t) y| ≤ C * h ^ 2 ∧
      |φ t (y - h) - φ t y + h * deriv (φ t) y| ≤ C * h ^ 2 := by
  have a1 := hφ.corr_abs_sub_le hT ht y (y + h)
  have a2 := hφ.corr_abs_sub_le hT ht y (y - h)
  have a3 := hφ.corr_abs_taylor_le hT ht y (y + h)
  have a4 := hφ.corr_abs_taylor_le hT ht y (y - h)
  simp only [add_sub_cancel_left, sub_sub_cancel_left, abs_neg, abs_of_nonneg hh, neg_sq,
    neg_mul, sub_neg_eq_add] at a1 a2 a3 a4
  exact ⟨a1, a2, a3, a4⟩

/-- `g_m(r ± 1) - g_m(r)` are bounded by `1/4`. -/
lemma corr_gM_incr_bounds (hρ : IsMollifier ρ) (hm : 1 ≤ m) (r : ℤ) :
    |gM ρ m (r + 1) - gM ρ m r| ≤ 1 / 4 ∧ |gM ρ m (r - 1) - gM ρ m r| ≤ 1 / 4 := by
  refine ⟨hρ.abs_gM_succ_sub_le hm r, ?_⟩
  have := hρ.abs_gM_succ_sub_le hm (r - 1)
  rwa [sub_add_cancel, abs_sub_comm] at this

/-- **Bound on `Γ_free`** (proof of Lemma 6.4): `|Γ_free| ≤ 2 c m h² C² + s h C² + c h² C²`. -/
lemma abs_corrGammaFree_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (x₁ x₂ : ℤ) :
    |corrGammaFree (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂| ≤
      cN n * (2 * m * (n ^ (-1 / 2 : ℝ)) ^ 2 * C ^ 2) +
        Real.sinh (thetaN n) * (n ^ (-1 / 2 : ℝ) * C ^ 2) +
        cN n * ((n ^ (-1 / 2 : ℝ)) ^ 2 * C ^ 2) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨-, -, -, hh, hc1, hep, hem, hs0, -, -⟩ := corr_consts hn
  have hC := hφ.corr_C_nonneg hT
  set h := n ^ (-1 / 2 : ℝ) with hhdef
  set r := x₂ - x₁ with hr
  have e1 : x₂ - (x₁ + 1) = r - 1 := by rw [hr]; ring
  have e2 : x₂ + 1 - x₁ = r + 1 := by rw [hr]; ring
  have e3 : x₂ - (x₁ - 1) = r + 1 := by rw [hr]; ring
  have e4 : x₂ - 1 - x₁ = r - 1 := by rw [hr]; ring
  have hF : corrGammaFree (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂ =
      Real.exp (thetaN n) * ((gM ρ m (r - 1) - gM ρ m r) *
          (φ t (rescaledPosition n t x₁ + h) * φ t (rescaledPosition n t x₂) -
            φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂)) +
        (gM ρ m (r + 1) - gM ρ m r) *
          (φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂ + h) -
            φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂))) +
      Real.exp (-thetaN n) * ((gM ρ m (r + 1) - gM ρ m r) *
          (φ t (rescaledPosition n t x₁ - h) * φ t (rescaledPosition n t x₂) -
            φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂)) +
        (gM ρ m (r - 1) - gM ρ m r) *
          (φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂ - h) -
            φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂))) := by
    simp only [corrGammaFree, corrG, corrPhi, e1, e2, e3, e4, ← hr,
      corr_rescaledPosition_add_one hn0, corr_rescaledPosition_sub_one hn0]
    rfl
  set y₁ := rescaledPosition n t x₁
  set y₂ := rescaledPosition n t x₂
  obtain ⟨u1p, u1m, t1p, t1m⟩ := hφ.corr_step_bounds hT ht hh.le y₁
  obtain ⟨u2p, u2m, t2p, t2m⟩ := hφ.corr_step_bounds hT ht hh.le y₂
  obtain ⟨b1, -, d1, -⟩ := hφ.corr_abs_le_C hT ht y₁
  obtain ⟨b2, -, d2, -⟩ := hφ.corr_abs_le_C hT ht y₂
  obtain ⟨gp, gm⟩ := corr_gM_incr_bounds hρ hm r
  have key := corr_gammaFree_bound hep hem hs0 (zero_le_one.trans hc1) gp gm b1 b2 u1p u1m u2p
    u2m t1p t1m t2p t2m
  rw [hF]
  -- the main term, of order `h` times `g(r+1) - g(r-1)`, which vanishes for `|r| ≥ 2m`
  have hmain : |cN n * h * (gM ρ m (r + 1) - gM ρ m (r - 1)) *
      (φ t y₁ * deriv (φ t) y₂ - deriv (φ t) y₁ * φ t y₂)| ≤ cN n * (2 * m * h ^ 2 * C ^ 2) := by
    have hc0 : 0 ≤ cN n := zero_le_one.trans hc1
    by_cases hr2 : 2 * (m : ℤ) ≤ |r|
    · rw [hρ.gM_add_one_eq_sub_one hm hr2, sub_self, mul_zero, zero_mul, abs_zero]
      positivity
    · push Not at hr2
      have hrm : |(r : ℝ)| ≤ 2 * m := by
        rw [← Int.cast_abs]; exact_mod_cast hr2.le
      have hg : |gM ρ m (r + 1) - gM ρ m (r - 1)| ≤ 1 / 2 := by
        have := abs_sub_le (gM ρ m (r + 1)) (gM ρ m r) (gM ρ m (r - 1))
        rw [abs_sub_comm (gM ρ m r)] at this
        linarith
      have hy : |y₂ - y₁| ≤ 2 * m * h := by
        have hy' := corr_rescaledPosition_sub hn0 t x₁ x₂
        rw [← hr] at hy'
        rw [hy', abs_mul, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_right hrm hh.le
      have hφ' : |φ t y₁ * deriv (φ t) y₂ - deriv (φ t) y₁ * φ t y₂| ≤ 4 * m * h * C ^ 2 := by
        have l1 := hφ.corr_abs_deriv_sub_le hT ht y₁ y₂
        have l2 := hφ.corr_abs_sub_le hT ht y₂ y₁
        rw [abs_sub_comm y₁ y₂] at l2
        have e : φ t y₁ * deriv (φ t) y₂ - deriv (φ t) y₁ * φ t y₂ =
          φ t y₁ * (deriv (φ t) y₂ - deriv (φ t) y₁) + deriv (φ t) y₁ * (φ t y₁ - φ t y₂) := by
          ring
        rw [e]
        calc _ ≤ |φ t y₁ * (deriv (φ t) y₂ - deriv (φ t) y₁)| +
              |deriv (φ t) y₁ * (φ t y₁ - φ t y₂)| := abs_add_le _ _
          _ = |φ t y₁| * |deriv (φ t) y₂ - deriv (φ t) y₁| +
              |deriv (φ t) y₁| * |φ t y₁ - φ t y₂| := by rw [abs_mul, abs_mul]
          _ ≤ C * (C * |y₂ - y₁|) + C * (C * |y₂ - y₁|) := by
              gcongr
          _ ≤ C * (C * (2 * m * h)) + C * (C * (2 * m * h)) := by gcongr
          _ = 4 * m * h * C ^ 2 := by ring
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_pos hh]
      calc cN n * h * |gM ρ m (r + 1) - gM ρ m (r - 1)| *
            |φ t y₁ * deriv (φ t) y₂ - deriv (φ t) y₁ * φ t y₂| ≤
          cN n * h * (1 / 2) * (4 * m * h * C ^ 2) := by gcongr
        _ = cN n * (2 * m * h ^ 2 * C ^ 2) := by ring
  have := abs_sub_abs_le_abs_sub (Real.exp (thetaN n) * ((gM ρ m (r - 1) - gM ρ m r) *
          (φ t (y₁ + h) * φ t y₂ - φ t y₁ * φ t y₂) +
        (gM ρ m (r + 1) - gM ρ m r) * (φ t y₁ * φ t (y₂ + h) - φ t y₁ * φ t y₂)) +
      Real.exp (-thetaN n) * ((gM ρ m (r + 1) - gM ρ m r) *
          (φ t (y₁ - h) * φ t y₂ - φ t y₁ * φ t y₂) +
        (gM ρ m (r - 1) - gM ρ m r) * (φ t y₁ * φ t (y₂ - h) - φ t y₁ * φ t y₂)))
    (cN n * h * (gM ρ m (r + 1) - gM ρ m (r - 1)) *
      (φ t y₁ * deriv (φ t) y₂ - deriv (φ t) y₁ * φ t y₂))
  linarith

/-- **Bound on `Γ_incl`** (proof of Lemma 6.4): `|Γ_incl| ≤ 2 c g_m(0) h C²`. -/
lemma abs_corrGammaIncl_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (x₁ x₂ : ℤ) :
    |corrGammaIncl (thetaN n) (corrG ρ m) (corrPhi n φ t) x₁ x₂| ≤
      cN n * (2 * gM ρ m 0 * n ^ (-1 / 2 : ℝ) * C ^ 2) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨-, -, -, hh, hc1, -, -, -, -, -⟩ := corr_consts hn
  have hC := hφ.corr_C_nonneg hT
  have h2c : Real.exp (thetaN n) + Real.exp (-thetaN n) = 2 * cN n := by
    rw [cN, Real.cosh_eq]; ring
  have he1 := Real.exp_pos (thetaN n)
  have he2 := Real.exp_pos (-thetaN n)
  have hg1 : gM ρ m 1 = 0 := (hρ.gM_spec hm).2.2.1
  have hg0 : 0 ≤ gM ρ m 0 := (hρ.gM_nonneg_le hm 0).1
  set h := n ^ (-1 / 2 : ℝ)
  set e := Real.exp (thetaN n)
  set e' := Real.exp (-thetaN n)
  -- the generic estimate for the two additional jumps
  have gen : ∀ U V : ℝ, |U| ≤ C → |V| ≤ C → |V - U| ≤ C * h → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 2 * cN n →
      |a * (gM ρ m 0 * (V * V - U * V)) + b * (gM ρ m 0 * (U * U - U * V))| ≤
        cN n * (2 * gM ρ m 0 * h * C ^ 2) := by
    intro U V hU hV hUV a b ha hb hab
    have e : a * (gM ρ m 0 * (V * V - U * V)) + b * (gM ρ m 0 * (U * U - U * V)) =
      gM ρ m 0 * (a * (V * (V - U)) - b * (U * (V - U))) := by ring
    rw [e, abs_mul, abs_of_nonneg hg0]
    have h1 : |a * (V * (V - U)) - b * (U * (V - U))| ≤ a * (C * (C * h)) + b * (C * (C * h)) := by
      calc _ ≤ |a * (V * (V - U))| + |b * (U * (V - U))| := abs_sub _ _
        _ = a * (|V| * |V - U|) + b * (|U| * |V - U|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ _ := by gcongr
    calc gM ρ m 0 * |a * (V * (V - U)) - b * (U * (V - U))| ≤
        gM ρ m 0 * (a * (C * (C * h)) + b * (C * (C * h))) := mul_le_mul_of_nonneg_left h1 hg0
      _ = gM ρ m 0 * ((a + b) * (C * (C * h))) := by ring
      _ = _ := by rw [hab]; ring
  unfold corrGammaIncl
  by_cases h1 : x₂ = x₁ + 1
  · subst h1
    have hne : ¬ (x₁ + 1 = x₁ - 1) := by omega
    simp only [corrG, corrPhi, ↓reduceIte, hne, sub_self, add_sub_cancel_left, hg1, sub_zero,
      add_zero]
    obtain ⟨b1, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x₁)
    obtain ⟨b2, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t (x₁ + 1))
    have := (hφ.corr_step_bounds hT ht hh.le (rescaledPosition n t x₁)).1
    rw [← corr_rescaledPosition_add_one hn0] at this
    exact gen _ _ b1 b2 this e e' he1.le he2.le h2c
  · by_cases h2 : x₂ = x₁ - 1
    · subst h2
      have hne : ¬ (x₁ - 1 = x₁ + 1) := by omega
      have hm1 : x₁ - 1 - x₁ = -1 := by ring
      simp only [corrG, corrPhi, ↓reduceIte, hne, sub_self, hm1, (hρ.gM_spec hm).1, hg1,
        sub_zero, zero_add]
      obtain ⟨b1, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x₁)
      obtain ⟨b2, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t (x₁ - 1))
      have := (hφ.corr_step_bounds hT ht hh.le (rescaledPosition n t x₁)).2.1
      rw [← corr_rescaledPosition_sub_one hn0] at this
      exact gen _ _ b1 b2 this e' e he2.le he1.le (by rw [add_comm]; exact h2c)
    · simp only [h1, h2, ↓reduceIte, add_zero, abs_zero]
      have : 0 ≤ cN n := zero_le_one.trans hc1
      positivity

/-- **The bound (6.14) on the integrand of the remainder**: if `g_m(0) ≤ C_ρ/m` with `C_ρ ≥ 0`,
then for `t ∈ [0,T]`,
`|corrRem_t(x₁,x₂)| ≤ (9 + 2C_ρ)(m/n^{1/2} + 1/n^{1/4} + 1/m) C²`. -/
theorem abs_corrRem_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hφ : IsC13 T φ φt C)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) {Cρ : ℝ} (hCρ0 : 0 ≤ Cρ)
    (hCρ : gM ρ m 0 ≤ Cρ / m) (x₁ x₂ : ℤ) :
    |corrRem n ρ m φ φt t x₁ x₂| ≤
      (9 + 2 * Cρ) * (m / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m) * C ^ 2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨hSh, -, hS, hh, hc1, -, -, hs0, hsθ, hθ⟩ := corr_consts hn
  obtain ⟨hK2c, hκ0, hκh, -⟩ := corrPref_props hn
  have hC := hφ.corr_C_nonneg hT
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hΓF := abs_corrGammaFree_le hρ hm hn hφ hT ht x₁ x₂
  have hΓI := abs_corrGammaIncl_le hρ hm hn hφ hT ht x₁ x₂
  rw [corrRem_eq hρ hm hn]
  obtain ⟨b1, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x₁)
  obtain ⟨b2, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x₂)
  have a1 := hφ.corr_abs_dt_add_AN_le hT ht hn (rescaledPosition n t x₁)
  have a2 := hφ.corr_abs_dt_add_AN_le hT ht hn (rescaledPosition n t x₂)
  have hg := hρ.gM_nonneg_le hm (x₂ - x₁)
  have hg0 := (hρ.gM_nonneg_le hm 0).1
  set h := n ^ (-1 / 2 : ℝ)
  set S := n ^ (1 / 2 : ℝ)
  set c := cN n
  set θ := thetaN n
  set s := Real.sinh θ
  set κ := corrPref n
  set g0 := gM ρ m 0
  set A1 := φt t (rescaledPosition n t x₁) + AN n (φ t) (rescaledPosition n t x₁)
  set A2 := φt t (rescaledPosition n t x₂) + AN n (φ t) (rescaledPosition n t x₂)
  set U1 := φ t (rescaledPosition n t x₁)
  set U2 := φ t (rescaledPosition n t x₂)
  set ΓF := corrGammaFree θ (corrG ρ m) (corrPhi n φ t) x₁ x₂
  set ΓI := corrGammaIncl θ (corrG ρ m) (corrPhi n φ t) x₁ x₂
  have hP1 : |κ * gM ρ m (x₂ - x₁) * (A1 * U2 + U1 * A2)| ≤ 6 * m * h * C ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hg.1]
    have hA : |A1 * U2 + U1 * A2| ≤ 6 * C ^ 2 := by
      calc _ ≤ |A1 * U2| + |U1 * A2| := abs_add_le _ _
        _ = |A1| * |U2| + |U1| * |A2| := by rw [abs_mul, abs_mul]
        _ ≤ 3 * C * C + C * (3 * C) := by gcongr
        _ = 6 * C ^ 2 := by ring
    calc κ * gM ρ m (x₂ - x₁) * |A1 * U2 + U1 * A2| ≤ (2 * h) * (m / 2) * (6 * C ^ 2) := by
          gcongr
          · exact hg.1
          · exact hg.2
      _ = 6 * m * h * C ^ 2 := by ring
  have hK2 : 0 ≤ n / 2 * κ := by positivity
  have hK2s : n / 2 * κ * s ≤ S * θ := by
    calc n / 2 * κ * s ≤ n / 2 * κ * (θ * c) := mul_le_mul_of_nonneg_left hsθ hK2
      _ = θ * (n / 2 * κ * c) := by ring
      _ = S * θ := by rw [hK2c]; ring
  have hP2 : |n / 2 * κ * (ΓF + ΓI)| ≤ 2 * m * h * C ^ 2 + h * C ^ 2 + 2 * g0 * C ^ 2 +
      θ * C ^ 2 := by
    rw [abs_mul, abs_of_nonneg hK2]
    have hsum : |ΓF + ΓI| ≤ c * (2 * m * h ^ 2 * C ^ 2) + s * (h * C ^ 2) +
        c * (h ^ 2 * C ^ 2) + c * (2 * g0 * h * C ^ 2) := (abs_add_le _ _).trans (by linarith)
    calc n / 2 * κ * |ΓF + ΓI| ≤ n / 2 * κ * (c * (2 * m * h ^ 2 * C ^ 2) + s * (h * C ^ 2) +
          c * (h ^ 2 * C ^ 2) + c * (2 * g0 * h * C ^ 2)) := mul_le_mul_of_nonneg_left hsum hK2
      _ = (n / 2 * κ * c) * (2 * m * h ^ 2 * C ^ 2 + h ^ 2 * C ^ 2 + 2 * g0 * h * C ^ 2) +
          (n / 2 * κ * s) * (h * C ^ 2) := by ring
      _ ≤ S * (2 * m * h ^ 2 * C ^ 2 + h ^ 2 * C ^ 2 + 2 * g0 * h * C ^ 2) +
          (S * θ) * (h * C ^ 2) := by
          rw [hK2c]; gcongr
      _ = (S * h) * (2 * m * h * C ^ 2 + h * C ^ 2 + 2 * g0 * C ^ 2) +
          (S * h) * (θ * C ^ 2) := by ring
      _ = _ := by rw [hSh]; ring
  have e1 : (m : ℝ) / S = m * h := by
    field_simp; linarith
  have e2 : (1 : ℝ) / n ^ (1 / 4 : ℝ) = θ := by
    simp only [θ, thetaN]
    rw [show (-1 / 4 : ℝ) = -(1 / 4) by norm_num, Real.rpow_neg hn0.le, one_div]
  have hg0' : 2 * g0 * C ^ 2 ≤ 2 * (Cρ / m) * C ^ 2 := by gcongr
  have hhm : h * C ^ 2 ≤ m * h * C ^ 2 := by
    have := mul_le_mul_of_nonneg_right hm1 (by positivity : (0 : ℝ) ≤ h * C ^ 2)
    linarith
  have eR : (9 + 2 * Cρ) * (m / S + 1 / n ^ (1 / 4 : ℝ) + 1 / m) * C ^ 2 =
      9 * m * h * C ^ 2 + θ * C ^ 2 + 2 * (Cρ / m) * C ^ 2 +
        (8 * θ * C ^ 2 + 9 * C ^ 2 / m + 2 * Cρ * m * h * C ^ 2 + 2 * Cρ * θ * C ^ 2) := by
    rw [e1, e2]; ring
  have hrest : 0 ≤ 8 * θ * C ^ 2 + 9 * C ^ 2 / m + 2 * Cρ * m * h * C ^ 2 +
      2 * Cρ * θ * C ^ 2 := by positivity
  rw [eR]
  calc _ ≤ |κ * gM ρ m (x₂ - x₁) * (A1 * U2 + U1 * A2)| + |n / 2 * κ * (ΓF + ΓI)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

/-- **`𝖱_n ≡ 0` when `φ ≡ 1`** (end of the proof of Lemma 6.4): if `φ_t ≡ 1` and `∂ₜφ_t ≡ 0`,
the integrand of the remainder vanishes. -/
theorem corrRem_eq_zero_of_const (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n) {t : ℝ}
    (hφ1 : ∀ y, φ t y = 1) (hφt : ∀ y, φt t y = 0) (x₁ x₂ : ℤ) :
    corrRem n ρ m φ φt t x₁ x₂ = 0 := by
  have hφ' : φ t = fun _ => 1 := funext hφ1
  have h2c : Real.exp (thetaN n) + Real.exp (-thetaN n) = 2 * cN n := by
    rw [cN, Real.cosh_eq]; ring
  have hA : ∀ y, φt t y + AN n (φ t) y = 0 := fun y => by
    rw [hφt, hφ', AN, deriv_const]
    linear_combination n / 2 * h2c
  rw [corrRem_eq hρ hm hn, hA, hA]
  simp only [corrGammaFree, corrGammaIncl, corrPhi, hφ1]
  simp

/-- **Bound on the integrand of the bracket** (proof of Lemma 6.4, "The martingale"): with
`A = e^{θ/2} - e^{-θ/2}` and `h = n^{-1/2}`, for `t ∈ [0,T]`,
`|e^{θ/2} f_t(x+1,x') - e^{-θ/2} f_t(x,x')| ≤ κ_n C² (A m/2 + 1/4 + m h/2)`. -/
theorem abs_corrBracket_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (x x' : ℤ) :
    |Real.exp (thetaN n / 2) * corrF n ρ m φ t (x + 1) x' -
        Real.exp (-thetaN n / 2) * corrF n ρ m φ t x x'| ≤
      corrPref n * C ^ 2 * ((Real.exp (thetaN n / 2) - Real.exp (-thetaN n / 2)) * m / 2 +
        1 / 4 + m * n ^ (-1 / 2 : ℝ) / 2) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨-, -, -, hh, -, -, -, -, -, hθ⟩ := corr_consts hn
  obtain ⟨-, hκ0, -, -⟩ := corrPref_props hn
  have hC := hφ.corr_C_nonneg hT
  set h := n ^ (-1 / 2 : ℝ)
  set e := Real.exp (thetaN n / 2)
  set e' := Real.exp (-thetaN n / 2)
  have he' : e' ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he'0 : 0 ≤ e' := (Real.exp_pos _).le
  have hA : 0 ≤ e - e' := sub_nonneg.2 (Real.exp_le_exp.2 (by linarith))
  set g1 := gM ρ m (x' - (x + 1))
  set g2 := gM ρ m (x' - x)
  have hg1 := hρ.gM_nonneg_le hm (x' - (x + 1))
  have hg2 := hρ.gM_nonneg_le hm (x' - x)
  have hg12 : |g1 - g2| ≤ 1 / 4 := by
    have := hρ.abs_gM_succ_sub_le hm (x' - (x + 1))
    rw [show x' - (x + 1) + 1 = x' - x by ring, abs_sub_comm] at this
    exact this
  set y := rescaledPosition n t x
  obtain ⟨bU, -⟩ := hφ.corr_abs_le_C hT ht y
  obtain ⟨bUp, -⟩ := hφ.corr_abs_le_C hT ht (y + h)
  obtain ⟨bU', -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x')
  have hstep := (hφ.corr_step_bounds hT ht hh.le y).1
  have e0 : Real.exp (thetaN n / 2) * corrF n ρ m φ t (x + 1) x' -
      Real.exp (-thetaN n / 2) * corrF n ρ m φ t x x' =
      corrPref n * φ t (rescaledPosition n t x') * ((e - e') * g1 * φ t (y + h) +
        e' * (g1 - g2) * φ t (y + h) + e' * g2 * (φ t (y + h) - φ t y)) := by
    simp only [corrF, corr_rescaledPosition_add_one hn0]
    ring
  rw [e0, abs_mul, abs_mul, abs_of_nonneg hκ0]
  have hin : |(e - e') * g1 * φ t (y + h) + e' * (g1 - g2) * φ t (y + h) +
      e' * g2 * (φ t (y + h) - φ t y)| ≤
      (e - e') * (m / 2) * C + 1 * (1 / 4) * C + 1 * (m / 2) * (C * h) := by
    have t1 : |(e - e') * g1 * φ t (y + h)| ≤ (e - e') * (m / 2) * C :=
      corr_abs_mul3_le (by rw [abs_of_nonneg hA]) (by rw [abs_of_nonneg hg1.1]; exact hg1.2) bUp
    have t2 : |e' * (g1 - g2) * φ t (y + h)| ≤ 1 * (1 / 4) * C :=
      corr_abs_mul3_le (by rwa [abs_of_nonneg he'0]) hg12 bUp
    have t3 : |e' * g2 * (φ t (y + h) - φ t y)| ≤ 1 * (m / 2) * (C * h) :=
      corr_abs_mul3_le (by rwa [abs_of_nonneg he'0]) (by rw [abs_of_nonneg hg2.1]; exact hg2.2)
        hstep
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)
  calc corrPref n * |φ t (rescaledPosition n t x')| * |(e - e') * g1 * φ t (y + h) +
        e' * (g1 - g2) * φ t (y + h) + e' * g2 * (φ t (y + h) - φ t y)| ≤
      corrPref n * C * ((e - e') * (m / 2) * C + 1 * (1 / 4) * C + 1 * (m / 2) * (C * h)) := by
        gcongr
    _ = _ := by ring

/-- **The constant of (6.15)**: `4n M² ≤ 24 (m²/n + 1/n^{1/2}) C⁴ a_n n^{1/2}` for the bound `M`
of `abs_corrBracket_le` (uses `(e^{θ/2} - e^{-θ/2})² = λ_n`, `κ_n ≤ 2 n^{-1/2}` and (3.2)). -/
theorem corrBracket_sq_le (hn : 1 ≤ n) (hm : 1 ≤ m) :
    4 * n * (corrPref n * C ^ 2 * ((Real.exp (thetaN n / 2) - Real.exp (-thetaN n / 2)) * m / 2 +
        1 / 4 + m * n ^ (-1 / 2 : ℝ) / 2)) ^ 2 ≤
      24 * (m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * (aN n * n ^ (1 / 2 : ℝ)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨hSh, hSS, hS, hh, -, -, -, -, -, hθ⟩ := corr_consts hn
  obtain ⟨-, hκ0, hκh, -⟩ := corrPref_props hn
  obtain ⟨hl1, -, ha1, -⟩ := constants_bounds hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set h := n ^ (-1 / 2 : ℝ)
  set S := n ^ (1 / 2 : ℝ)
  set κ := corrPref n
  set A := Real.exp (thetaN n / 2) - Real.exp (-thetaN n / 2)
  set lam := lambdaN n
  have hA0 : 0 ≤ A := sub_nonneg.2 (Real.exp_le_exp.2 (by linarith))
  have hA2 : A ^ 2 = lam := by
    have q1 : Real.exp (thetaN n / 2) * Real.exp (thetaN n / 2) = Real.exp (thetaN n) := by
      rw [← Real.exp_add]; ring_nf
    have q2 : Real.exp (-thetaN n / 2) * Real.exp (-thetaN n / 2) = Real.exp (-thetaN n) := by
      rw [← Real.exp_add]; ring_nf
    have q3 : Real.exp (thetaN n / 2) * Real.exp (-thetaN n / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    simp only [A, lam, lambdaN, Real.cosh_eq]
    linear_combination q1 + q2 - 2 * q3
  have hnh : n * h ^ 2 = 1 := by rw [← hSS]; linear_combination (S * h + 1) * hSh
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hhl : h ^ 2 ≤ lam := by nlinarith
  have hSl : 1 ≤ S * lam := ha1
  have hκ2 : κ ^ 2 ≤ 4 * h ^ 2 := by nlinarith
  set X := A * m / 2 + 1 / 4 + m * h / 2
  have h3 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := fun a b c => by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have hX2 : X ^ 2 ≤ 3 * (A ^ 2 * m ^ 2 / 4 + 1 / 16 + m ^ 2 * h ^ 2 / 4) := by
    calc X ^ 2 = (A * m / 2 + 1 / 4 + m * h / 2) ^ 2 := rfl
      _ ≤ 3 * ((A * m / 2) ^ 2 + (1 / 4) ^ 2 + (m * h / 2) ^ 2) := h3 _ _ _
      _ = _ := by ring
  have eL : 4 * n * (κ * C ^ 2 * X) ^ 2 = 4 * n * C ^ 4 * (κ ^ 2 * X ^ 2) := by ring
  have hL : κ ^ 2 * X ^ 2 ≤ (4 * h ^ 2) * (3 * (lam * m ^ 2 / 4 + 1 / 16 + m ^ 2 * h ^ 2 / 4)) := by
    rw [← hA2]; exact mul_le_mul hκ2 hX2 (sq_nonneg _) (by positivity)
  have eR : (m ^ 2 / n + 1 / S) * (aN n * S) = m ^ 2 * lam + S * lam := by
    have : aN n = S * lam := rfl
    rw [this]
    field_simp
    linear_combination (m ^ 2 * lam) * hSS
  calc 4 * n * (κ * C ^ 2 * X) ^ 2 = 4 * n * C ^ 4 * (κ ^ 2 * X ^ 2) := eL
    _ ≤ 4 * n * C ^ 4 * ((4 * h ^ 2) * (3 * (lam * m ^ 2 / 4 + 1 / 16 + m ^ 2 * h ^ 2 / 4))) := by
        gcongr
    _ = 48 * C ^ 4 * (n * h ^ 2) * (lam * m ^ 2 / 4 + 1 / 16 + m ^ 2 * h ^ 2 / 4) := by ring
    _ = 48 * C ^ 4 * (lam * m ^ 2 / 4 + 1 / 16 + m ^ 2 * h ^ 2 / 4) := by rw [hnh, mul_one]
    _ ≤ 24 * C ^ 4 * (m ^ 2 * lam + S * lam) := by
        have : m ^ 2 * h ^ 2 ≤ m ^ 2 * lam := mul_le_mul_of_nonneg_left hhl (by positivity)
        have hC4 : 0 ≤ C ^ 4 := by positivity
        nlinarith
    _ = 24 * (m ^ 2 / n + 1 / S) * C ^ 4 * (aN n * S) := by
        rw [show 24 * (m ^ 2 / n + 1 / S) * C ^ 4 * (aN n * S) =
          24 * C ^ 4 * ((m ^ 2 / n + 1 / S) * (aN n * S)) by ring, eR]

end QSSEPtoKPZ
