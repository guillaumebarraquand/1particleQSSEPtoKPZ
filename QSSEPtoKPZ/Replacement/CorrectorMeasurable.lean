/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorSums
public import QSSEPtoKPZ.WaveFunction.Good

/-!
# Lemma 6.4: joint measurability

Task G1. The processes `𝖱_n` and `q` of Lemma 6.4 must be jointly measurable in `(t, ω)`.
They are built from the good version `ψ'` of the wave function (`IsGoodWave`, all paths
continuous), extended to negative times by `ψ'_{max(t,0)}` (`corrWave`). By Carathéodory's
criterion (continuous in `t`, measurable in `ω`), `(t,ω) ↦ 𝔷_n(t,x)` is jointly measurable
(`measurable_zN_corrWave`), and so are the double sums `corrPair`, the bracket density and the
sums defining `ℰ_n`. `corr_intervalIntegrable_of_bound` turns a bound into integrability.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- The good version extended to negative times: `t ↦ ψ'_{max(t,0)}`. -/
def corrWave (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (ω : Ω) : ℓ²(ℤ, ℂ) := ψ' (Real.toNNReal t) ω

lemma corrWave_of_nonneg (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    corrWave ψ' t ω = ψ' t ω := by
  rw [corrWave, Real.coe_toNNReal _ ht]

/-- `𝔷_n(t,x) ≥ 0`. -/
lemma corr_zN_nonneg (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) : 0 ≤ zN n ψ ω t x :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- `(t,ω) ↦ 𝔷_n(t,x)` computed with `corrWave ψ'` is jointly measurable. -/
lemma measurable_zN_corrWave {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsGoodWave 𝓕 B ψ ψ' μ) (n : ℝ)
    (x : ℤ) : Measurable (Function.uncurry fun t ω => zN n (corrWave ψ') ω t x) := by
  set u : ℝ → Ω → ℂ := fun t ω => corrWave ψ' (n * t / 2) ω x
  have hu : Measurable (Function.uncurry u) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun t => ?_)
    · exact (h.continuous_apply ω x).comp
        (continuous_real_toNNReal.comp ((continuous_const.mul continuous_id).div_const 2))
    · exact (h.measurable_apply _ x).mono ((nullAug μ 𝓕).le _) le_rfl
  have e : (Function.uncurry fun t ω => zN n (corrWave ψ') ω t x) = fun p =>
      Real.exp (thetaN n * x - n * lambdaN n / 2 * p.1) * ‖Function.uncurry u p‖ ^ 2 := by
    ext p; rfl
  rw [e]
  exact ((measurable_const.sub (measurable_const.mul measurable_fst)).exp).mul
    (hu.norm.pow_const 2)

/-- Joint measurability of `(t,ω) ↦ ∑_{x₁,x₂} Z_t(ω)(x₁) Z_t(ω)(x₂) F_t(x₁,x₂)`. -/
lemma measurable_corrPair {Z : ℝ → Ω → ℤ → ℝ}
    (hZ : ∀ x, Measurable (Function.uncurry fun t ω => Z t ω x)) {F : ℝ → ℤ → ℤ → ℝ}
    (hF : ∀ a b, Measurable fun t => F t a b) :
    Measurable (Function.uncurry fun t ω => corrPair (Z t ω) (F t)) := by
  show Measurable fun p : ℝ × Ω => ∑' a, ∑' b, Z p.1 p.2 a * Z p.1 p.2 b * F p.1 a b
  exact Measurable.tsum fun a => Measurable.tsum fun b =>
    ((hZ a).mul (hZ b)).mul ((hF a b).comp measurable_fst)

/-- Joint measurability of the bracket density `bracketDensN2`. -/
lemma corr_measurable_bracketDensN2 {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsGoodWave 𝓕 B ψ ψ' μ) (n : ℝ)
    {f : ℝ → ℤ → ℤ → ℝ} (hf : ∀ a b, Measurable fun t => f t a b) :
    Measurable (Function.uncurry fun t ω => bracketDensN2 n (corrWave ψ') f t ω) := by
  have hZ := measurable_zN_corrWave h n
  show Measurable fun p : ℝ × Ω => 4 * n * ∑' x : ℤ, zN n (corrWave ψ') p.2 p.1 x *
    zN n (corrWave ψ') p.2 p.1 (x + 1) * (∑' x' : ℤ, zN n (corrWave ψ') p.2 p.1 x' *
      (Real.exp (thetaN n / 2) * f p.1 (x + 1) x' - Real.exp (-thetaN n / 2) * f p.1 x x')) ^ 2
  refine measurable_const.mul (Measurable.tsum fun x => ((hZ x).mul (hZ (x + 1))).mul ?_)
  refine (Measurable.tsum fun x' => (hZ x').mul ?_).pow_const 2
  exact (measurable_const.mul ((hf _ _).comp measurable_fst)).sub
    (measurable_const.mul ((hf _ _).comp measurable_fst))

/-- Joint measurability of `(t,ω) ↦ ℰ_n(t; G_t)` (computed with `corrWave ψ'`), for test functions
`G_t` with `t ↦ G_t(y_n(t,x))` measurable. -/
lemma measurable_EN_corrWave {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsGoodWave 𝓕 B ψ ψ' μ) (n : ℝ)
    {G : ℝ → ℝ → ℝ} (hG : ∀ x : ℤ, Measurable fun t => G t (rescaledPosition n t x)) :
    Measurable (Function.uncurry fun t ω => EN n (corrWave ψ') ω t (G t)) := by
  have hZ := measurable_zN_corrWave h n
  show Measurable fun p : ℝ × Ω => n ^ (1 / 2 : ℝ) * ∑' x : ℤ, zN n (corrWave ψ') p.2 p.1 x *
    zN n (corrWave ψ') p.2 p.1 (x + 1) * G p.1 (rescaledPosition n p.1 x) *
      G p.1 (rescaledPosition n p.1 (x + 1))
  exact measurable_const.mul (Measurable.tsum fun x => (((hZ x).mul (hZ (x + 1))).mul
    ((hG x).comp measurable_fst)).mul ((hG (x + 1)).comp measurable_fst))

/-- A function equal on `[0,T]` to a measurable function and bounded there is integrable on
`[0,T]`. -/
lemma corr_intervalIntegrable_of_bound {T M : ℝ} (hT : 0 ≤ T) {F G : ℝ → ℝ} (hG : Measurable G)
    (hFG : ∀ s ∈ Icc 0 T, F s = G s) (hM : ∀ s ∈ Icc 0 T, |F s| ≤ M) :
    IntervalIntegrable F volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hae : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)), F s = G s :=
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => hFG s (Ioc_subset_Icc_self hs))
  have hc : IntegrableOn (fun _ : ℝ => M) (Ioc 0 T) volume :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine Integrable.mono' hc ((hG.aestronglyMeasurable).congr (hae.mono fun s hs => hs.symm)) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => by
    rw [Real.norm_eq_abs]; exact hM s (Ioc_subset_Icc_self hs))

end QSSEPtoKPZ
