/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.Prop73Aux
public import QSSEPtoKPZ.Uniqueness.Volterra

/-!
# Proposition 7.3, with (7.13) written out (task K1)

`prop73_main`: Proposition 7.3 with the hypotheses of `IsWeakMild` written out field by field,
the value of the stochastic integral in (7.13) being `(∫ Z(t,x) f(x) dx) - ∫ g_t(x) f(x) dx`.

Proof (decision D5″ of `docs/stage4-design.md`, Section 1.2 (g)): with `D = Z¹ - Z²` and
`F(t) = 𝔼 ‖D(t)‖₂²`, `F` is integrable on `[0,T]`; for almost every `t`,
`F(t) ≤ (2√π)⁻¹ ∫_0^t F(s) (t-s)^{-1/2} ds` (`prop73_mollified_le`, `prop73_fatou`); hence
`F = 0` almost everywhere on `[0,T]` (`volterra_ae_eq_zero`), and `D = 0` almost everywhere on
`Ω × [0,T] × ℝ` (Tonelli).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `(a - b)² ≤ 2a² + 2b²`, in `[0, ∞]`. -/
private lemma prop73_ofReal_sq_sub_le (a b : ℝ) :
    ENNReal.ofReal ((a - b) ^ 2) ≤ 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a + b)])

/-- `∫ (f - g)² ≤ 2 ∫ f² + 2 ∫ g²`, in `[0, ∞]`. -/
private lemma prop73_lintegral_sq_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal ((f x - g x) ^ 2) ∂μ ≤
      2 * (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) + 2 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ := by
  calc _ ≤ ∫⁻ x, (2 * ENNReal.ofReal (f x ^ 2) + 2 * ENNReal.ofReal (g x ^ 2)) ∂μ :=
        lintegral_mono fun x => prop73_ofReal_sq_sub_le _ _
    _ = _ := by
        rw [lintegral_add_left ((hf.pow_const 2).ennreal_ofReal.const_mul 2),
          lintegral_const_mul _ (hf.pow_const 2).ennreal_ofReal, lintegral_const_mul' _ _ (by simp)]

/-- **Proposition 7.3**, with the hypotheses of `IsWeakMild` written out: two random fields
`Z¹, Z² ∈ ℋ_T` which satisfy (7.13), with the value `(∫ Z(t,x) f(x) dx) - ∫ g_t(x) f(x) dx` of the
stochastic integral, for almost every `t ∈ (0,T]` and every `f ∈ C_c^∞(ℝ)`, agree almost
everywhere on `Ω × [0,T] × ℝ`. -/
theorem prop73_main {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}
    (hS : IsWhiteNoise 𝓖 S ν) {T : ℝ} {Z₁ Z₂ : ℝ → ℝ → Ω → ℝ}
    (hm₁ : Measurable (uncurryField Z₁)) (hm₂ : Measurable (uncurryField Z₂))
    (hsq₁ : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z₁ t x ω ^ 2)) ∂ν < ⊤)
    (hsq₂ : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z₂ t x ω ^ 2)) ∂ν < ⊤)
    (hw₁ : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ f : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      IsWalshIntegral 𝓖 S ν
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₁ s y ω else 0)
        (fun ω => (∫ x, Z₁ t x ω * f x) - ∫ x, heatKernel t x * f x))
    (hw₂ : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ f : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      IsWalshIntegral 𝓖 S ν
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₂ s y ω else 0)
        (fun ω => (∫ x, Z₂ t x ω * f x) - ∫ x, heatKernel t x * f x)) :
    ∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
      Z₁ p.2.1 p.2.2 p.1 = Z₂ p.2.1 p.2.2 p.1 := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  obtain ⟨ρ, hρ⟩ := prop73_exists_mollifier
  have hD : Measurable (uncurryField fun s x ω => Z₁ s x ω - Z₂ s x ω) := hm₁.sub hm₂
  have hFm := prop73_measurable_F hD ν
  have hF₁m := prop73_measurable_F hm₁ ν
  have hF₂m := prop73_measurable_F hm₂ ν
  have hF₁i : ∫⁻ t in Set.Icc 0 T, (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (Z₁ t x ω ^ 2)) ∂ν) < ⊤ := by
    rw [prop73_lintegral_swap hm₁ ν]; exact hsq₁
  have hF₂i : ∫⁻ t in Set.Icc 0 T, (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (Z₂ t x ω ^ 2)) ∂ν) < ⊤ := by
    rw [prop73_lintegral_swap hm₂ ν]; exact hsq₂
  -- `F` is integrable on `[0,T]`
  have hFle : ∀ t, ∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2)) ∂ν ≤
      2 * (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (Z₁ t x ω ^ 2)) ∂ν) +
        2 * ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (Z₂ t x ω ^ 2)) ∂ν := by
    intro t
    have h₁ : ∀ ω, Measurable (fun x => Z₁ t x ω) := fun ω =>
      hm₁.comp (f := fun x => (ω, t, x)) (by fun_prop)
    have hi₁ : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (Z₁ t x ω ^ 2)) :=
      (prop73_measurable_inner hm₁).comp (f := fun ω => (t, ω)) (by fun_prop)
    calc _ ≤ ∫⁻ ω, (2 * (∫⁻ x, ENNReal.ofReal (Z₁ t x ω ^ 2)) +
          2 * ∫⁻ x, ENNReal.ofReal (Z₂ t x ω ^ 2)) ∂ν :=
          lintegral_mono fun ω => prop73_lintegral_sq_sub_le (g := fun x => Z₂ t x ω) (h₁ ω)
      _ = _ := by
          rw [lintegral_add_left (hi₁.const_mul 2), lintegral_const_mul _ hi₁,
            lintegral_const_mul' _ _ (by simp)]
  have hFi : ∫⁻ t in Set.Icc 0 T,
      (∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2)) ∂ν) < ⊤ := by
    refine (lintegral_mono hFle).trans_lt ?_
    rw [lintegral_add_left (hF₁m.const_mul 2), lintegral_const_mul _ hF₁m,
      lintegral_const_mul' _ _ (by simp)]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hF₁i,
      ENNReal.mul_lt_top (by simp) hF₂i⟩
  -- the Volterra inequality for almost every `t`
  have hw : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), t ∈ Set.Ioc 0 T ∧
      (∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        IsWalshIntegral 𝓖 S ν
          (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₁ s y ω else 0)
          (fun ω => (∫ x, Z₁ t x ω * f x) - ∫ x, heatKernel t x * f x)) ∧
      (∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        IsWalshIntegral 𝓖 S ν
          (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z₂ s y ω else 0)
          (fun ω => (∫ x, Z₂ t x ω * f x) - ∫ x, heatKernel t x * f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hw₁, hw₂] with t ht h1 h2
    exact ⟨ht, h1, h2⟩
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hw
  have hle : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      (∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2)) ∂ν) ≤
        ENNReal.ofReal prop73Const * ∫⁻ s in Set.Ioo 0 t,
          (∫⁻ ω, (∫⁻ x, ENNReal.ofReal ((Z₁ s x ω - Z₂ s x ω) ^ 2)) ∂ν) *
            ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [hw, ae_lt_top' hF₁m.aemeasurable hF₁i.ne,
      ae_lt_top' hF₂m.aemeasurable hF₂i.ne] with t ⟨_, h1, h2⟩ f1 f2
    exact prop73_fatou hρ hm₁ hm₂ f1 f2 fun δ hδ => prop73_mollified_le hS hρ hm₁ hm₂ h1 h2 hδ
  have hF0 := volterra_ae_eq_zero hFm.aemeasurable hFi hle
  -- conclusion by Tonelli
  have hmeas := prop73_measurable_sq hD
  have hzero : ∫⁻ p, ENNReal.ofReal ((Z₁ p.2.1 p.2.2 p.1 - Z₂ p.2.1 p.2.2 p.1) ^ 2)
      ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)) = 0 := by
    rw [lintegral_prod _ hmeas.aemeasurable]
    have h1 : ∀ ω, ∫⁻ q, ENNReal.ofReal ((Z₁ q.1 q.2 ω - Z₂ q.1 q.2 ω) ^ 2)
        ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume) =
        ∫⁻ t in Set.Icc 0 T, ∫⁻ x, ENNReal.ofReal ((Z₁ t x ω - Z₂ t x ω) ^ 2) := fun ω =>
      lintegral_prod _ (hmeas.comp (f := fun q : ℝ × ℝ => (ω, q)) (by fun_prop)).aemeasurable
    rw [lintegral_congr h1, ← prop73_lintegral_swap hD ν (volume.restrict (Set.Icc 0 T)),
      lintegral_congr_ae hF0, lintegral_zero]
  filter_upwards [(lintegral_eq_zero_iff hmeas).1 hzero] with p hp
  have h := ENNReal.ofReal_eq_zero.1 hp
  nlinarith [sq_nonneg (Z₁ p.2.1 p.2.2 p.1 - Z₂ p.2.1 p.2.2 p.1)]

end QSSEPtoKPZ
