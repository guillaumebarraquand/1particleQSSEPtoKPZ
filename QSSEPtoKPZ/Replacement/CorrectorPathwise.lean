/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorMeasurable
public import QSSEPtoKPZ.Replacement.CorrectorBounds

/-!
# Lemma 6.4: pathwise bounds in terms of the total mass `𝒲_n(t)`

Task G1. For a realization where `x ↦ 𝔷_n(t,x)` is summable (almost surely, for all `t ≥ 0`),
with `𝒲_n(t) = ∑ₓ 𝔷_n(t,x)`:

* `corr_abs_EN_le`: `|ℰ_n(t;G)| ≤ n^{1/2} C_G² 𝒲_n(t)²` when `|G| ≤ C_G`;
* `corr_abs_FN_le`: the bound (6.13), `|𝖥_n(t)| ≤ (m/n^{1/2}) C² 𝒲_n(t)²`;
* `corr_bracketDensN2_le`: `4n ∑ₓ 𝔷𝔷 [∑_{x'} 𝔷 (…)]² ≤ 4n M² 𝒲_n(t)² ∑ₓ 𝔷_n(t,x) 𝔷_n(t,x+1)` when the
  bracket integrand is bounded by `M`;
* `corr_abs_kM_le`: `|k_m| ≤ κ(0)/(m b_m)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {n : ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {t : ℝ}

/-- `𝒲_n(t) = ∑ₓ 𝔷_n(t,x)`. -/
lemma corr_WN_eq_tsum : WN n ψ t ω = ∑' x, zN n ψ ω t x := by
  simp [WN, pairZ]

/-- `𝔷_n(t,x) ≤ 𝒲_n(t)`. -/
lemma corr_zN_le_WN (hz : Summable (zN n ψ ω t)) (x : ℤ) : zN n ψ ω t x ≤ WN n ψ t ω := by
  rw [corr_WN_eq_tsum]; exact hz.le_tsum x fun y _ => corr_zN_nonneg n ψ ω t y

/-- `|ℰ_n(t;G)| ≤ n^{1/2} C_G² 𝒲_n(t)²` when `|G(y_n(t,x))| ≤ C_G`. -/
lemma corr_abs_EN_le (hn : 0 ≤ n) (hz : Summable (zN n ψ ω t)) {G : ℝ → ℝ} {Cg : ℝ}
    (hG : ∀ x : ℤ, |G (rescaledPosition n t x)| ≤ Cg) :
    |EN n ψ ω t G| ≤ n ^ (1 / 2 : ℝ) * Cg ^ 2 * WN n ψ t ω ^ 2 := by
  have hz0 := corr_zN_nonneg n ψ ω t
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hG 0)
  set z := zN n ψ ω t
  set W := WN n ψ t ω
  have hb : ∀ x, |z x * z (x + 1) * G (rescaledPosition n t x) * G (rescaledPosition n t (x + 1))|
      ≤ Cg ^ 2 * W * z x := fun x => by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hz0 x), abs_of_nonneg (hz0 (x + 1))]
    have h1 := corr_zN_le_WN hz (x + 1)
    have := mul_le_mul (mul_le_mul h1 (hG x) (abs_nonneg _) ((hz0 _).trans h1)) (hG (x + 1))
      (abs_nonneg _) (mul_nonneg ((hz0 _).trans h1) hCg)
    nlinarith [hz0 x, mul_nonneg (hz0 x) (abs_nonneg (G (rescaledPosition n t x)))]
  have := corr_abs_tsum_le (hz.mul_left (Cg ^ 2 * W)) hb
  rw [tsum_mul_left, ← corr_WN_eq_tsum] at this
  have hS := Real.rpow_nonneg hn (1 / 2 : ℝ)
  unfold EN
  rw [abs_mul, abs_of_nonneg hS]
  calc _ ≤ n ^ (1 / 2 : ℝ) * (Cg ^ 2 * W * W) := mul_le_mul_of_nonneg_left this hS
    _ = _ := by ring

/-- `|k_m(r)| ≤ κ(0)/(m b_m)`. -/
lemma corr_abs_kM_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) (r : ℤ) :
    |kM ρ m r| ≤ kappa ρ 0 / (m * bM ρ m) := by
  have hb := hρ.bM_pos hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [abs_of_nonneg ((hρ.kM_props hm).2.1 r), kM]
  exact div_le_div_of_nonneg_right (hρ.kappa_le_kappa_zero.1 _) (by positivity)

/-- **The bound (6.13)**: `|𝖥_n(t)| ≤ (m/n^{1/2}) C² 𝒲_n(t)²` when `|φ_t| ≤ C`. -/
lemma corr_abs_FN_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hz : Summable (zN n ψ ω t)) {φ : ℝ → ℝ → ℝ} {C : ℝ} (hφ : ∀ y, |φ t y| ≤ C) :
    |FN n ψ ρ m φ t ω| ≤ m / n ^ (1 / 2 : ℝ) * C ^ 2 * WN n ψ t ω ^ 2 := by
  obtain ⟨hSh, -, hS, -, -⟩ := corr_consts hn
  obtain ⟨-, hκ0, hκh, -⟩ := corrPref_props hn
  have hC : 0 ≤ C := (abs_nonneg _).trans (hφ 0)
  have hb : ∀ a b, |gM ρ m (b - a) * φ t (rescaledPosition n t a) * φ t (rescaledPosition n t b)|
      ≤ m / 2 * C ^ 2 := fun a b => by
    have hg := hρ.gM_nonneg_le hm (b - a)
    have := corr_abs_mul3_le ((abs_of_nonneg hg.1).trans_le hg.2) (hφ (rescaledPosition n t a))
      (hφ (rescaledPosition n t b))
    linarith [show (m : ℝ) / 2 * C * C = m / 2 * C ^ 2 by ring]
  have h := abs_corrPair_le (corr_zN_nonneg n ψ ω t) hz hb
  rw [← corr_WN_eq_tsum] at h
  have e : FN n ψ ρ m φ t ω = corrPref n * corrPair (zN n ψ ω t) fun a b =>
      gM ρ m (b - a) * φ t (rescaledPosition n t a) * φ t (rescaledPosition n t b) := rfl
  rw [e, abs_mul, abs_of_nonneg hκ0]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e2 : (m : ℝ) / n ^ (1 / 2 : ℝ) = 2 * n ^ (-1 / 2 : ℝ) * (m / 2) := by
    field_simp; linarith
  rw [e2]
  calc corrPref n * |corrPair (zN n ψ ω t) _| ≤ (2 * n ^ (-1 / 2 : ℝ)) *
      (m / 2 * C ^ 2 * WN n ψ t ω ^ 2) := mul_le_mul hκh h (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **The bracket density** of `N_n^f`, bounded through a bound `M` on its integrand:
`4n ∑ₓ 𝔷𝔷 [∑_{x'} 𝔷(x') (…)]² ≤ 4n M² 𝒲_n(t)² ∑ₓ 𝔷_n(t,x) 𝔷_n(t,x+1)`. -/
lemma corr_bracketDensN2_le (hn : 0 ≤ n) (hz : Summable (zN n ψ ω t)) {f : ℝ → ℤ → ℤ → ℝ} {M : ℝ}
    (hM : ∀ x x', |Real.exp (thetaN n / 2) * f t (x + 1) x' - Real.exp (-thetaN n / 2) * f t x x'|
      ≤ M) :
    bracketDensN2 n ψ f t ω ≤
      4 * n * M ^ 2 * WN n ψ t ω ^ 2 * ∑' x, zN n ψ ω t x * zN n ψ ω t (x + 1) := by
  have hz0 := corr_zN_nonneg n ψ ω t
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  set z := zN n ψ ω t
  set W := WN n ψ t ω
  have hW0 : 0 ≤ W := by show 0 ≤ WN n ψ t ω; rw [corr_WN_eq_tsum]; exact tsum_nonneg hz0
  set D : ℤ → ℝ := fun x => ∑' x', z x' *
    (Real.exp (thetaN n / 2) * f t (x + 1) x' - Real.exp (-thetaN n / 2) * f t x x')
  have hD : ∀ x, D x ^ 2 ≤ M ^ 2 * W ^ 2 := fun x => by
    have h := corr_abs_tsum_le (f := fun x' => z x' * (Real.exp (thetaN n / 2) * f t (x + 1) x' -
        Real.exp (-thetaN n / 2) * f t x x')) (hz.mul_left M) fun x' => by
      calc _ = z x' * |Real.exp (thetaN n / 2) * f t (x + 1) x' -
            Real.exp (-thetaN n / 2) * f t x x'| := by rw [abs_mul, abs_of_nonneg (hz0 x')]
        _ ≤ z x' * M := mul_le_mul_of_nonneg_left (hM x x') (hz0 x')
        _ = M * z x' := mul_comm _ _
    rw [tsum_mul_left, ← corr_WN_eq_tsum] at h
    change |D x| ≤ M * W at h
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hP : Summable fun x => z x * z (x + 1) :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (hz0 x) (hz0 _))
      (fun x => mul_le_mul_of_nonneg_left (corr_zN_le_WN hz (x + 1)) (hz0 x)) (hz.mul_right W)
  have hle : ∀ x, z x * z (x + 1) * D x ^ 2 ≤ M ^ 2 * W ^ 2 * (z x * z (x + 1)) := fun x => by
    rw [mul_comm (M ^ 2 * W ^ 2)]
    exact mul_le_mul_of_nonneg_left (hD x) (mul_nonneg (hz0 x) (hz0 _))
  have hsum := Summable.tsum_le_tsum hle
    (Summable.of_nonneg_of_le (fun x => mul_nonneg (mul_nonneg (hz0 x) (hz0 _)) (sq_nonneg _))
      hle (hP.mul_left _)) (hP.mul_left _)
  rw [tsum_mul_left] at hsum
  show 4 * n * ∑' x, z x * z (x + 1) * D x ^ 2 ≤ _
  calc 4 * n * ∑' x, z x * z (x + 1) * D x ^ 2 ≤ 4 * n * (M ^ 2 * W ^ 2 *
      ∑' x, z x * z (x + 1)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end QSSEPtoKPZ
