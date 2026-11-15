/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorDefs
public import QSSEPtoKPZ.Replacement.Corrector
public import QSSEPtoKPZ.SecondMoments.TotalMass
public import QSSEPtoKPZ.TiltedField.MartingalesBounds
public import QSSEPtoKPZ.WaveFunction.Good
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Equations (6.1), (6.11) and Proposition 6.1

Statements: Stage 2, task T0; proofs: task G2.

* `kappaEps_eq_conv`: `κ_ε = ρ_ε ⋆ ρ_ε`, by the change of variables `y = ε u` (it holds for any
  `ρ`, so the hypothesis `IsMollifier ρ` is unused).
* `smoothedNormSq_eq` (6.1): writing `(∫ φ(x) ρ_ε(y - x) ν(dx))²` as an integral over `ν ⊗ ν`
  (`integral_prod_mul`), Fubini in `(y, (x₁, x₂))` (the integrand is dominated by
  `c² ‖ρ_ε‖_∞ ρ_ε(y - x₁)`, integrable since `ν` is finite) and
  `∫ ρ_ε(y - x₁) ρ_ε(y - x₂) dy = κ_ε(x₁ - x₂)` (`ρ` even).
* `BN_eq` (6.11): integrals against `𝒵_n(t) = ∑ₓ 𝔷_n(t,x) δ_{y_n(t,x)}` are sums, and
  `κ_ε(y_n(t,x₁) - y_n(t,x₂)) = n^{1/2} b_m k_m(x₂ - x₁)` for `ε = m n^{-1/2}`.
* `prop_6_1`: as in the article, Lemma 6.4 with `φ ≡ 1` (`𝖱_n ≡ 0`, `𝖥_n ≥ 0`), the expectation
  of the martingale `N_n(T)` (zero), `𝖥_n(0) = 2 g_m(0) / (c_n n^{1/2}) ≤ 1` (`𝒵_n(0) = δ_0`),
  Proposition 4.3 (`𝔼 ∫_0^T ℰ_n ≤ 2^{1+16T}`), (6.11) and `b_m ≤ sup_m b_m` (6.6); the constant
  is `C = 3 sup_m b_m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-! ### Auxiliary facts on `ρ_ε` -/

/-- `ρ_ε` is continuous. -/
private lemma l2b_rhoEps_continuous {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (rhoEps ρ ε) :=
  show Continuous fun x => ρ (x / ε) / ε from
    (hρ.continuous.comp (continuous_id.div_const ε)).div_const ε

/-- `ρ_ε` is even. -/
private lemma l2b_rhoEps_neg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ε x : ℝ) :
    rhoEps ρ ε (-x) = rhoEps ρ ε x := by
  simp only [rhoEps, neg_div, hρ.even]

/-- `ρ_ε` is integrable. -/
private lemma l2b_rhoEps_integrable {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    Integrable (rhoEps ρ ε) := by
  show Integrable (fun x => ρ (x / ε) / ε)
  exact (hρ.integrable.comp_div hε).div_const ε

/-- `ρ_ε` is bounded. -/
private lemma l2b_rhoEps_bdd {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ε : ℝ) :
    ∃ M, ∀ x, |rhoEps ρ ε x| ≤ M := by
  obtain ⟨M, hM⟩ := hρ.continuous.bounded_above_of_compact_support hρ.hasCompactSupport
  refine ⟨M / |ε|, fun x => ?_⟩
  rw [rhoEps, abs_div]
  exact div_le_div_of_nonneg_right (by simpa using hM (x / ε)) (abs_nonneg _)

/-- `κ_ε` is continuous, and `0 ≤ κ_ε ≤ κ(0)/ε` for `ε > 0`. -/
private lemma l2b_kappaEps_props {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (kappaEps ρ ε) ∧ ∀ x, |kappaEps ρ ε x| ≤ kappa ρ 0 / ε := by
  refine ⟨show Continuous fun x => kappa ρ (x / ε) / ε from
    (hρ.kappa_even_nonneg_smooth.2.2.continuous.comp (continuous_id.div_const ε)).div_const ε,
    fun x => ?_⟩
  rw [kappaEps, abs_of_nonneg (div_nonneg (hρ.kappa_nonneg _) hε.le)]
  exact div_le_div_of_nonneg_right (hρ.kappa_le _) hε.le

set_option linter.unusedVariables false in
/-- `κ_ε = ρ_ε ⋆ ρ_ε` (beginning of Section 6), for `ε > 0`. -/
theorem kappaEps_eq_conv {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    kappaEps ρ ε x = ∫ y, rhoEps ρ ε y * rhoEps ρ ε (x - y) := by
  have e : ∀ y, rhoEps ρ ε y * rhoEps ρ ε (x - y) =
      (fun u => ρ u * ρ (x / ε - u)) (y / ε) / ε ^ 2 := by
    intro y
    simp only [rhoEps]
    rw [sub_div]
    field_simp
  rw [integral_congr_ae (ae_of_all _ e), integral_div,
    Measure.integral_comp_div (fun u => ρ u * ρ (x / ε - u)) ε, kappaEps, IsMollifier.kappa_apply,
    abs_of_pos hε, smul_eq_mul]
  field_simp

/-- **Equation (6.1)**: for a finite measure `ν` on `ℝ`, a bounded continuous `φ` and `ε > 0`,
the function `(φν) ⋆ ρ_ε` is square integrable, `(x,y) ↦ φ(x) φ(y) κ_ε(x - y)` is integrable for
`ν ⊗ ν`, and `‖(φν) ⋆ ρ_ε‖₂² = ∫∫ φ(x) φ(y) κ_ε(x - y) ν(dx) ν(dy)`. -/
theorem smoothedNormSq_eq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφb : ∃ c, ∀ x, |φ x| ≤ c) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun y => (∫ x, φ x * rhoEps ρ ε (y - x) ∂ν) ^ 2) ∧
    Integrable (fun p : ℝ × ℝ => φ p.1 * φ p.2 * kappaEps ρ ε (p.1 - p.2)) (ν.prod ν) ∧
    smoothedNormSq ν φ ρ ε = ∫ p, φ p.1 * φ p.2 * kappaEps ρ ε (p.1 - p.2) ∂(ν.prod ν) := by
  obtain ⟨c, hc⟩ := hφb
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  obtain ⟨M, hM⟩ := l2b_rhoEps_bdd hρ ε
  have hr := l2b_rhoEps_continuous hρ ε
  have hri := l2b_rhoEps_integrable hρ hε.ne'
  obtain ⟨hκc, hκb⟩ := l2b_kappaEps_props hρ hε
  -- the integrand `G(y, (x₁, x₂)) = φ(x₁) ρ_ε(y - x₁) φ(x₂) ρ_ε(y - x₂)`
  set G : ℝ → ℝ × ℝ → ℝ := fun y p =>
    φ p.1 * rhoEps ρ ε (y - p.1) * (φ p.2 * rhoEps ρ ε (y - p.2)) with hG
  have hGc : Continuous (Function.uncurry G) := by
    simp only [hG, Function.uncurry_def]
    fun_prop
  have hGi : Integrable (Function.uncurry G) (volume.prod (ν.prod ν)) := by
    have hdom : Integrable (fun q : ℝ × (ℝ × ℝ) => c * c * M * |rhoEps ρ ε (q.1 - q.2.1)|)
        (volume.prod (ν.prod ν)) := by
      refine Integrable.const_mul ?_ _
      refine (integrable_prod_iff' ?_).2 ⟨ae_of_all _ fun p => ?_, ?_⟩
      · exact (hr.comp (continuous_fst.sub (continuous_fst.comp continuous_snd))).abs
          |>.aestronglyMeasurable
      · exact (hri.comp_sub_right p.1).abs
      · have e : ∀ p : ℝ × ℝ, ∫ x, ‖|rhoEps ρ ε (x - p.1)|‖ = ∫ x, ‖rhoEps ρ ε x‖ := fun p => by
          simp only [norm_abs_eq_norm]
          exact integral_sub_right_eq_self (fun x => ‖rhoEps ρ ε x‖) p.1
        simp_rw [e]
        exact integrable_const _
    refine hdom.mono' hGc.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    simp only [hG, Function.uncurry_def, Real.norm_eq_abs, abs_mul]
    have h1 := hc q.2.1
    have h2 := hc q.2.2
    have h3 := hM (q.1 - q.2.2)
    calc |φ q.2.1| * |rhoEps ρ ε (q.1 - q.2.1)| * (|φ q.2.2| * |rhoEps ρ ε (q.1 - q.2.2)|)
        ≤ c * |rhoEps ρ ε (q.1 - q.2.1)| * (c * M) := by gcongr
      _ = c * c * M * |rhoEps ρ ε (q.1 - q.2.1)| := by ring
  have hsq : ∀ y, (∫ x, φ x * rhoEps ρ ε (y - x) ∂ν) ^ 2 = ∫ p, G y p ∂(ν.prod ν) := fun y => by
    rw [sq, ← integral_prod_mul]
  have hconv : ∀ a b : ℝ, ∫ y, rhoEps ρ ε (y - a) * rhoEps ρ ε (y - b) = kappaEps ρ ε (a - b) := by
    intro a b
    rw [kappaEps_eq_conv hρ hε, ← integral_add_right_eq_self
      (fun y => rhoEps ρ ε (y - a) * rhoEps ρ ε (y - b)) b]
    congr 1
    ext y
    rw [add_sub_cancel_right, show y + b - a = -(a - b - y) by ring, l2b_rhoEps_neg hρ, mul_comm]
  have hfun : (fun y => (∫ x, φ x * rhoEps ρ ε (y - x) ∂ν) ^ 2) =
      fun y => ∫ p, G y p ∂(ν.prod ν) := funext hsq
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hGi.integral_prod_left
  · refine Integrable.of_bound (C := c * c * (kappa ρ 0 / ε)) ?_ (ae_of_all _ fun p => ?_)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => φ p.1 * φ p.2 * kappaEps ρ ε (p.1 - p.2))
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have := hκb (p.1 - p.2)
      gcongr
      exacts [hc _, hc _]
  · unfold smoothedNormSq
    rw [hfun, integral_integral_swap hGi]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    have e : ∀ y, G y p = φ p.1 * φ p.2 * (rhoEps ρ ε (y - p.1) * rhoEps ρ ε (y - p.2)) :=
      fun y => by simp only [hG]; ring
    simp only [e]
    rw [integral_const_mul, hconv]

/-! ### Integrals against the discrete measure `𝒵_n(t)` -/

section Tilted

variable {Ω : Type*} {n : ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {t : ℝ}

/-- `𝔷_n(t,x) ≥ 0`. -/
private lemma l2b_zN_nonneg (x : ℤ) : 0 ≤ zN n ψ ω t x :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- `𝒵_n(t)` is a finite measure when `∑ₓ 𝔷_n(t,x)` converges. -/
private lemma l2b_isFiniteMeasure (hz : Summable (zN n ψ ω t)) :
    IsFiniteMeasure (tiltedMeasure n ψ ω t) := by
  refine ⟨?_⟩
  rw [tiltedMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg l2b_zN_nonneg hz]
  exact ENNReal.ofReal_lt_top

/-- `∫ g d𝒵_n(t) = ∑ₓ 𝔷_n(t,x) g(y_n(t,x))` for `g` integrable. -/
private lemma l2b_integral_tilted {g : ℝ → ℝ} (hg : Integrable g (tiltedMeasure n ψ ω t)) :
    ∫ y, g y ∂(tiltedMeasure n ψ ω t) = ∑' x, zN n ψ ω t x * g (rescaledPosition n t x) := by
  rw [tiltedMeasure] at hg ⊢
  rw [integral_sum_measure hg]
  congr 1
  ext x
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (l2b_zN_nonneg x), smul_eq_mul]

end Tilted

/-- **Equation (6.11)**: for `n ≥ 1`, an integer `m ≥ 1`, a bounded continuous `φ`, and a realization
`ω` and a time `t` at which `∑ₓ 𝔷_n(t,x)` converges (true almost surely for all `t ≥ 0`, by (3.7)),
`𝖡_n(t;φ) = b_m^{-1} ‖(φ 𝒵_n(t)) ⋆ ρ_{m n^{-1/2}}‖₂²`. -/
theorem BN_eq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {Ω : Type*} {n : ℝ} (hn : 1 ≤ n) {m : ℕ}
    (hm : 1 ≤ m) {φ : ℝ → ℝ} (hφ : Continuous φ) (hφb : ∃ c, ∀ x, |φ x| ≤ c)
    (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (hz : Summable (zN n ψ ω t)) :
    BN n ψ ρ m t φ ω =
      smoothedNormSq (tiltedMeasure n ψ ω t) φ ρ (m * n ^ (-1 / 2 : ℝ)) / bM ρ m := by
  have := l2b_isFiniteMeasure hz
  have hn0 : 0 < n := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := hρ.bM_pos hm
  have hε : 0 < (m : ℝ) * n ^ (-1 / 2 : ℝ) := by positivity
  obtain ⟨c, hc⟩ := hφb
  obtain ⟨hκc, hκb⟩ := l2b_kappaEps_props hρ hε
  obtain ⟨-, hint, heq⟩ := smoothedNormSq_eq hρ (tiltedMeasure n ψ ω t) hφ ⟨c, hc⟩ hε
  -- `κ_ε(y_n(t,x₁) - y_n(t,x₂)) = n^{1/2} b_m k_m(x₂ - x₁)` for `ε = m n^{-1/2}`
  have hk : ∀ x₁ x₂ : ℤ, kappaEps ρ (m * n ^ (-1 / 2 : ℝ))
      (rescaledPosition n t x₁ - rescaledPosition n t x₂) =
        n ^ (1 / 2 : ℝ) * bM ρ m * kM ρ m (x₂ - x₁) := by
    intro x₁ x₂
    have hs : 0 < n ^ (1 / 2 : ℝ) := by positivity
    have e1 : n ^ (-1 / 2 : ℝ) = (n ^ (1 / 2 : ℝ))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hn0.le]
    have e2 : (rescaledPosition n t x₁ - rescaledPosition n t x₂) / (m * n ^ (-1 / 2 : ℝ)) =
        ((x₁ - x₂ : ℤ) : ℝ) / m := by
      rw [rescaledPosition, rescaledPosition, e1]
      push_cast
      field_simp
      ring
    rw [kappaEps, e2, kM, show ((x₂ - x₁ : ℤ) : ℝ) / m = -(((x₁ - x₂ : ℤ) : ℝ) / m) by
      push_cast; ring, hρ.kappa_even_nonneg_smooth.1, e1]
    field_simp
  have hinner : ∀ a : ℝ, Integrable (fun y => φ a * φ y * kappaEps ρ (m * n ^ (-1 / 2 : ℝ)) (a - y))
      (tiltedMeasure n ψ ω t) := fun a => by
    refine Integrable.of_bound (C := c * c * (kappa ρ 0 / (m * n ^ (-1 / 2 : ℝ)))) ?_
      (ae_of_all _ fun y => ?_)
    · exact (by fun_prop : Continuous fun y =>
        φ a * φ y * kappaEps ρ (m * n ^ (-1 / 2 : ℝ)) (a - y)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have := hκb (a - y)
      have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
      gcongr
      exacts [hc _, hc _]
  rw [heq, integral_prod _ hint]
  rw [l2b_integral_tilted hint.integral_prod_left]
  have key : ∀ x₁ : ℤ, zN n ψ ω t x₁ * ∫ y, φ (rescaledPosition n t x₁) * φ y *
      kappaEps ρ (m * n ^ (-1 / 2 : ℝ)) (rescaledPosition n t x₁ - y) ∂(tiltedMeasure n ψ ω t) =
      n ^ (1 / 2 : ℝ) * bM ρ m * ∑' x₂, zN n ψ ω t x₁ * zN n ψ ω t x₂ *
        (kM ρ m (x₂ - x₁) * φ (rescaledPosition n t x₁) * φ (rescaledPosition n t x₂)) := by
    intro x₁
    rw [l2b_integral_tilted (hinner _), ← tsum_mul_left, ← tsum_mul_left]
    congr 1
    ext x₂
    rw [hk]
    ring
  rw [tsum_congr key, tsum_mul_left, BN, pairZ2]
  field_simp

/-! ### Proposition 6.1 -/

/-- `𝖡_n(t;1) ≥ 0`. -/
private lemma l2b_BN_one_nonneg {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {Ω : Type*} {n : ℝ}
    (hn : 0 ≤ n) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (ω : Ω) :
    0 ≤ BN n ψ ρ m t (fun _ => 1) ω := by
  unfold BN pairZ2
  refine mul_nonneg (Real.rpow_nonneg hn _) (tsum_nonneg fun x₁ => tsum_nonneg fun x₂ => ?_)
  simp only [mul_one]
  exact mul_nonneg (mul_nonneg (l2b_zN_nonneg _) (l2b_zN_nonneg _)) ((hρ.kM_props hm).2.1 _)

/-- `𝖥_n(0) = 2 g_m(0) / (c_n n^{1/2}) ∈ [0, 1]` for `φ ≡ 1`, since `𝒵_n(0) = δ_0`. -/
private lemma l2b_FN_zero {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {m : ℕ}
    (hm : 1 ≤ m) :
    (∀ᵐ ω ∂μ, FN n ψ ρ m (fun _ _ => 1) 0 ω = 2 / (cN n * n ^ (1 / 2 : ℝ)) * gM ρ m 0) ∧
      0 ≤ 2 / (cN n * n ^ (1 / 2 : ℝ)) * gM ρ m 0 ∧
      2 / (cN n * n ^ (1 / 2 : ℝ)) * gM ρ m 0 ≤ 1 := by
  obtain ⟨-, -, ha1, hac, -, -⟩ := constants_bounds hn
  have hs : 1 ≤ n ^ (1 / 2 : ℝ) := Real.one_le_rpow hn (by norm_num)
  have hg := hρ.gM_nonneg_le hm 0
  have hg0 : gM ρ m 0 ≤ 1 / 8 := by
    rw [(hρ.gM_spec hm).2.1]; linarith [hρ.kM_zero_le hm]
  have hcn : 1 ≤ cN n * n ^ (1 / 2 : ℝ) := by nlinarith
  refine ⟨?_, mul_nonneg (div_nonneg zero_le_two (by linarith)) hg.1, ?_⟩
  · filter_upwards [hψ.ae_init] with ω hω
    have e : ∀ x : ℤ, zN n ψ ω 0 x = if x = 0 then 1 else 0 := fun x => by
      by_cases hx : x = 0 <;> simp [zN, density, hω, waveInit_apply, hx]
    simp only [FN, pairZ2, e]
    rw [tsum_eq_single 0 (fun x₁ h => by simp [h])]
    rw [tsum_eq_single 0 (fun x₂ h => by simp [h])]
    simp
  · rw [div_mul_eq_mul_div, div_le_one (by linarith)]
    linarith

/-- **Proposition 6.1**, equation (6.2). There is a constant `C`, depending only on `ρ`, such that
for every probability space, Brownian family and wave function (`L = ∞`), all `n ≥ 1`, all integers
`m ≥ 1` and all `T > 0`,
`𝔼[∫_0^T ‖𝒵_n(t) ⋆ ρ_{m n^{-1/2}}‖₂² dt] ≤ C 2^{16T}`.
The integrals are computed in `[0, ∞]`, and the integrands (in `t` almost surely, then in `ω`) are
stated to be almost everywhere measurable, so that both are genuine integrals. -/
theorem prop_6_1 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
      IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ →
      ∀ {n T : ℝ} {m : ℕ}, 1 ≤ n → 1 ≤ m → 0 < T →
        (∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
        (∀ᵐ ω ∂μ, AEMeasurable (fun t => ENNReal.ofReal
          (smoothedNormSq (tiltedMeasure n ψ ω t) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ))))
          (volume.restrict (Set.Icc 0 T))) ∧
        AEMeasurable (fun ω => ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal
          (smoothedNormSq (tiltedMeasure n ψ ω t) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ)))) μ ∧
        ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal
          (smoothedNormSq (tiltedMeasure n ψ ω t) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ)))) ∂μ ≤
        ENNReal.ofReal (C * 2 ^ (16 * T)) := by
  obtain ⟨K, hK⟩ := lemma_6_4 hρ
  obtain ⟨cb, Cb, hcb, hbb⟩ := hρ.bM_bounds
  have hCb : 0 < Cb := hcb.trans_le ((hbb 1 le_rfl).1.trans (hbb 1 le_rfl).2)
  refine ⟨3 * Cb, ?_⟩
  intro Ω mΩ 𝓕 μ _ B ψ hB hψ n T m hn hm hT
  have hn0 : 0 < n := by linarith
  have hφ1 : IsC13 T (fun _ _ => (1 : ℝ)) (fun _ _ => 0) 1 := by
    refine ⟨fun _ _ => contDiff_const, fun _ _ _ => hasDerivWithinAt_const _ _ _,
      ⟨continuousOn_const, fun k _ => ?_⟩, ⟨![1, 0, 0, 0, 0], ?_, fun t _ x => ?_⟩⟩
    · simp only [iteratedDeriv_const]; exact continuousOn_const
    · simp [Fin.sum_univ_five]
    · simp [iteratedDeriv_const]
  -- Lemma 6.4 with `φ ≡ 1`: `𝖱_n ≡ 0` and `𝖥_n ≥ 0`
  obtain ⟨R, q, -, -, hae1, -, hBr, hconst⟩ := hK hB hψ hn hm hT hφ1
  obtain ⟨hR0, hFnn⟩ := hconst fun _ _ => rfl
  -- Proposition 4.3: `𝔼[∫_0^T ℰ_n(s) ds] ≤ 2^{1+16T}`
  obtain ⟨-, -, -, hEi, hEle⟩ := prop_4_3_bounds hB hψ hn hT.le
  obtain ⟨hFzero, hF0nn, hF0le⟩ := l2b_FN_zero hρ hψ hn hm
  set F0 := 2 / (cN n * n ^ (1 / 2 : ℝ)) * gM ρ m 0 with hF0def
  have hb := hρ.bM_pos hm
  have hbC := (hbb m hm).2
  -- the martingale `N_n` of (6.12)
  set N : ℝ → Ω → ℝ := fun t ω => FN n ψ ρ m (fun _ _ => 1) t ω -
    FN n ψ ρ m (fun _ _ => 1) 0 ω - ∫ s in (0 : ℝ)..t,
      (EN n ψ ω s (fun _ => 1) - BN n ψ ρ m s (fun _ => 1) ω + R s ω) with hN
  have hBr' : HasBracket T (filtN n 𝓕) N (fun t ω => ∫ s in (0 : ℝ)..t, q s ω) μ := hBr
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.le
  have hNi : Integrable (N T) μ := by
    have := (hBr'.memLp T.toNNReal hTT.le).integrable one_le_two
    rwa [hTT] at this
  -- `𝔼[N_n(T)] = 𝔼[N_n(0)] = 0`
  have hNE : ∫ ω, N T ω ∂μ = 0 := by
    have hce := hBr'.condExp 0 T.toNNReal zero_le hTT.le
    rw [hTT] at hce
    rw [← integral_condExp ((filtN n 𝓕).le 0), integral_congr_ae hce]
    simp [hN]
  set Y : Ω → ℝ := fun ω => N T ω + F0 + ∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1 with hY
  have hYi : Integrable Y μ := (hNi.add (integrable_const F0)).add hEi
  have hYE : ∫ ω, Y ω ∂μ ≤ 1 + 2 ^ (1 + 16 * T) := by
    have hA : Integrable (fun ω => N T ω + F0) μ := hNi.add (integrable_const F0)
    have hE' : Integrable (fun ω => ∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) μ := hEi
    simp only [hY]
    rw [integral_add hA hE', integral_add hNi (integrable_const F0), hNE, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, zero_add]
    linarith
  -- pathwise: `‖𝒵_n(t) ⋆ ρ_ε‖₂² = b_m 𝖡_n(t;1)` and `∫_0^T 𝖡_n(s;1) ds = Y - 𝖥_n(T) ≤ Y`
  have hgood : ∀ᵐ ω ∂μ, (∀ t, 0 ≤ t → smoothedNormSq (tiltedMeasure n ψ ω t) (fun _ => 1) ρ
      (m * n ^ (-1 / 2 : ℝ)) = bM ρ m * BN n ψ ρ m t (fun _ => 1) ω) ∧
      IntervalIntegrable (fun s => BN n ψ ρ m s (fun _ => 1) ω) volume 0 T ∧
      ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω ≤ Y ω ∧
      ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω = Y ω - FN n ψ ρ m (fun _ _ => 1) T ω := by
    filter_upwards [hae1, hFnn, hFzero] with ω h1 h2 h3
    obtain ⟨hsum, hEI, hBI, -, -⟩ := h1
    refine ⟨fun t ht => ?_, hBI, ?_⟩
    · rw [BN_eq hρ hn hm continuous_const ⟨1, fun _ => by simp⟩ ψ ω t (hsum t ht)]
      field_simp
    have hid : ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω =
        Y ω - FN n ψ ρ m (fun _ _ => 1) T ω := by
      have e : N T ω = FN n ψ ρ m (fun _ _ => 1) T ω - FN n ψ ρ m (fun _ _ => 1) 0 ω -
          ((∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) -
            ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω) := by
        simp only [hN, hR0, add_zero]
        rw [intervalIntegral.integral_sub hEI hBI]
      simp only [hY]
      rw [e, h3]
      ring
    have hFT := h2 T ⟨hT.le, le_rfl⟩
    exact ⟨by rw [hid]; linarith, hid⟩
  have hBnn : ∀ ω, 0 ≤ ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω := fun ω =>
    intervalIntegral.integral_nonneg hT.le fun s _ => l2b_BN_one_nonneg hρ hn0.le ψ hm s ω
  have hIcc : ∀ ω, IntervalIntegrable (fun s => BN n ψ ρ m s (fun _ => 1) ω) volume 0 T →
      IntegrableOn (fun s => BN n ψ ρ m s (fun _ => 1) ω) (Set.Icc 0 T) := fun ω h => by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 h
  -- the time integral
  have hlin : ∀ᵐ ω ∂μ, ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (smoothedNormSq
      (tiltedMeasure n ψ ω t) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ))) =
      ENNReal.ofReal (bM ρ m * ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω) := by
    filter_upwards [hgood] with ω h
    obtain ⟨h1, hBI, -, -⟩ := h
    rw [setLIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [h1 t ht.1]),
      ← ofReal_integral_eq_lintegral_ofReal ((hIcc ω hBI).const_mul _)
        (ae_of_all _ fun s => mul_nonneg hb.le (l2b_BN_one_nonneg hρ hn0.le ψ hm s ω)),
      integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  have hFTm : Measurable fun ω => FN n ψ ρ m (fun _ _ => 1) T ω := by
    simp only [FN, pairZ2]
    exact measurable_const.mul (Measurable.tsum fun x₁ => Measurable.tsum fun x₂ =>
      ((tiltZ_measurable hψ hn hT.le x₁).mul (tiltZ_measurable hψ hn hT.le x₂)).mul
        measurable_const)
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hae1] with ω h using h.1
  · filter_upwards [hgood] with ω h
    obtain ⟨h1, hBI, -, -⟩ := h
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hIcc ω hBI).aestronglyMeasurable.aemeasurable.const_mul (bM ρ m))).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht => by
      simp only [Function.comp_apply]
      rw [h1 t ht.1]
  · refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hYi.aemeasurable.sub hFTm.aemeasurable).const_mul (bM ρ m))).congr ?_
    filter_upwards [hlin, hgood] with ω h1 h2
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [h1, h2.2.2.2]
  · have h2 : (2 : ℝ) ^ (1 + 16 * T) = 2 * 2 ^ (16 * T) := by
      rw [Real.rpow_add two_pos, Real.rpow_one]
    have h1 : (1 : ℝ) ≤ 2 ^ (16 * T) := Real.one_le_rpow one_le_two (by linarith)
    calc ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (smoothedNormSq
          (tiltedMeasure n ψ ω t) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ)))) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (bM ρ m * ∫ s in (0 : ℝ)..T, BN n ψ ρ m s (fun _ => 1) ω) ∂μ :=
          lintegral_congr_ae hlin
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Cb * Y ω) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hgood] with ω h
          exact ENNReal.ofReal_le_ofReal (mul_le_mul hbC h.2.2.1 (hBnn ω) hCb.le)
      _ = ENNReal.ofReal (∫ ω, Cb * Y ω ∂μ) := by
          refine (ofReal_integral_eq_lintegral_ofReal (hYi.const_mul Cb) ?_).symm
          filter_upwards [hgood] with ω h
          exact mul_nonneg hCb.le ((hBnn ω).trans h.2.2.1)
      _ ≤ ENNReal.ofReal (3 * Cb * 2 ^ (16 * T)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          nlinarith

end QSSEPtoKPZ
