/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.TiltedField.MartingalesCalc
public import QSSEPtoKPZ.WaveFunction.MomentBound
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Pathwise bounds on the tilted field (task E2)

From the moment bound (2.2) with `a = θ_n + 1` and the continuity of `ψ`: almost surely, for
every `T`, the paths `t ↦ 𝔷_n(t,x)` are continuous on `[0,T]` and
`0 ≤ 𝔷_n(t,x) ≤ K e^{-|x|}` for `t ∈ [0,T]` (`TiltGood`), since
`𝔷_n(t,x) ≤ e^{θ_n |x|} P(nt/2,x) ≤ e^{-|x|} sup_{s ≤ nT/2} ‖ψ_s‖²_{θ_n+1}`.
Consequences (Weierstrass M-test): all the series `∑ₓ 𝔷_n(t,x) 𝔷_n(t,x+1) G(t,x)` with bounded
continuous `G` converge and are continuous in `t`, and so is `𝒲_n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `∑_{x ∈ ℤ} e^{-|x|} < ∞`. -/
lemma tilt_summable_exp_neg_abs : Summable fun x : ℤ => Real.exp (-|(x : ℝ)|) := by
  apply Summable.of_nat_of_neg
  · simpa using Real.summable_exp_neg_nat
  · simpa using Real.summable_exp_neg_nat

/-- `P(t,x) ≥ 0`. -/
lemma tilt_density_nonneg (ω : Ω) (t : ℝ) (x : ℤ) : 0 ≤ density ψ ω t x := by
  unfold density; positivity

/-- `𝔷_n(t,x) ≥ 0`. -/
lemma tiltZ_nonneg (n : ℝ) (ω : Ω) (t : ℝ) (x : ℤ) : 0 ≤ zN n ψ ω t x := by
  unfold zN; exact mul_nonneg (Real.exp_pos _).le (tilt_density_nonneg ω _ x)

/-- `𝔷_n(t,x) ≤ e^{θ_n |x|} P(nt/2, x)` for `t ≥ 0`. -/
lemma tiltZ_le_exp {n : ℝ} (hn : 1 ≤ n) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) (x : ℤ) :
    zN n ψ ω t x ≤ Real.exp (thetaN n * |(x : ℝ)|) * density ψ ω (n * t / 2) x := by
  unfold zN
  gcongr
  · exact tilt_density_nonneg ω _ x
  · have h1 := mul_le_mul_of_nonneg_left (le_abs_self (x : ℝ)) (tiltTheta_nonneg hn)
    have h2 : 0 ≤ n * lambdaN n / 2 * t := by
      have := tiltLambda_nonneg n
      have : 0 ≤ n := zero_le_one.trans hn
      positivity
    linarith

/-- **Domination**, from (2.2) with `k = 1`: almost surely, for every `N`, there is `K` with
`e^{a|x|} P(s,x) ≤ K` for all `s ∈ [0,N]` and `x ∈ ℤ`. -/
lemma tilt_ae_dom [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, ∃ K : ℝ, ∀ s ∈ Icc (0 : ℝ) N, ∀ x : ℤ,
      Real.exp (a * |(x : ℝ)|) * density ψ ω s x ≤ K := by
  refine ae_all_iff.2 fun N => ?_
  obtain ⟨hm, hi⟩ := moment_bound hB hψ ha (T := N) 1
  simp only [pow_one] at hi
  filter_upwards [ae_lt_top' hm hi.ne] with ω hω
  refine ⟨(⨆ t ∈ Icc (0 : ℝ) N,
      ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)).toReal,
    fun s hs x => ?_⟩
  rw [← ENNReal.ofReal_le_iff_le_toReal hω.ne]
  refine le_trans ?_ (le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) N) =>
    ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)) s hs)
  exact ENNReal.le_tsum (f := fun x : ℤ =>
    ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω s x)) x

/-- Almost surely, the paths `s ↦ P(s,x)` are continuous on `[0, ∞)`. -/
lemma tilt_ae_cont (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) :
    ∀ᵐ ω ∂μ, ∀ x : ℤ, ContinuousOn (fun s => density ψ ω s x) (Ici 0) := by
  filter_upwards [hψ.continuous] with ω hω x
  have hc : Continuous fun s : ℝ => ‖ψ (s.toNNReal : ℝ) ω x‖ ^ 2 :=
    (continuous_norm.pow 2).comp ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp
      (hω.comp continuous_real_toNNReal))
  refine hc.continuousOn.congr fun s hs => ?_
  simp only [density, Real.coe_toNNReal s hs]

/-- **A good path of the tilted field on `[0,T]`**: the paths `t ↦ 𝔷_n(t,x)` are continuous on
`[0,T]`, and `𝔷_n(t,x) ≤ K e^{-|x|}` on `[0,T]` for some `K ≥ 0`. -/
structure TiltGood (n T : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) : Prop where
  cont : ∀ x, ContinuousOn (fun t => zN n ψ ω t x) (Icc 0 T)
  dom : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 T, ∀ x : ℤ, zN n ψ ω t x ≤ K * Real.exp (-|(x : ℝ)|)

/-- Almost surely, the path of the tilted field is good on every `[0,T]`. -/
lemma ae_tiltGood [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ, TiltGood n T ψ ω := by
  have hθ := tiltTheta_nonneg hn
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  filter_upwards [tilt_ae_dom hB hψ (a := thetaN n + 1) (by linarith), tilt_ae_cont hψ]
    with ω hd hc T
  refine ⟨fun x => ?_, ?_⟩
  · have he : Continuous fun t : ℝ => Real.exp (thetaN n * x - n * lambdaN n / 2 * t) := by
      fun_prop
    refine he.continuousOn.mul ((hc x).comp
      (by fun_prop : Continuous fun t : ℝ => n * t / 2).continuousOn ?_)
    intro t ht
    exact mem_Ici.2 (by have := ht.1; positivity)
  · obtain ⟨K, hK⟩ := hd ⌈n * T / 2⌉₊
    refine ⟨max K 0, le_max_right _ _, fun t ht x => ?_⟩
    have hs : n * t / 2 ∈ Icc (0 : ℝ) ⌈n * T / 2⌉₊ := by
      refine ⟨by have := ht.1; positivity, le_trans ?_ (Nat.le_ceil _)⟩
      have := ht.2; gcongr
    have h1 := tiltZ_le_exp (ψ := ψ) hn ω ht.1 x
    have h2 := hK _ hs x
    have e : Real.exp (thetaN n * |(x : ℝ)|) =
        Real.exp ((thetaN n + 1) * |(x : ℝ)|) * Real.exp (-|(x : ℝ)|) := by
      rw [← Real.exp_add]; ring_nf
    rw [e] at h1
    calc zN n ψ ω t x ≤ Real.exp ((thetaN n + 1) * |(x : ℝ)|) * density ψ ω (n * t / 2) x *
          Real.exp (-|(x : ℝ)|) := by linarith
      _ ≤ max K 0 * Real.exp (-|(x : ℝ)|) := by
          gcongr; exact h2.trans (le_max_left _ _)

namespace TiltGood

variable {n T : ℝ} {ω : Ω}

/-- `∑ₓ 𝔷_n(t,x)` converges for `t ∈ [0,T]`. -/
lemma summable (h : TiltGood n T ψ ω) {t : ℝ} (ht : t ∈ Icc 0 T) : Summable (zN n ψ ω t) := by
  obtain ⟨K, -, hK⟩ := h.dom
  refine Summable.of_nonneg_of_le (fun x => tiltZ_nonneg n ω t x) (fun x => hK t ht x)
    (tilt_summable_exp_neg_abs.mul_left K)

/-- The bound on the products `𝔷_n(t,x) 𝔷_n(t,x+1) G(x)` for `|G| ≤ b`. -/
lemma norm_zz_le {K b : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t ∈ Icc 0 T, ∀ x : ℤ, zN n ψ ω t x ≤ K * Real.exp (-|(x : ℝ)|)) {t : ℝ}
    (ht : t ∈ Icc 0 T) {G : ℤ → ℝ} (hG : ∀ x, |G x| ≤ b) (x : ℤ) :
    ‖zN n ψ ω t x * zN n ψ ω t (x + 1) * G x‖ ≤ K * K * b * Real.exp (-|(x : ℝ)|) := by
  have h0 := tiltZ_nonneg (ψ := ψ) n ω t x
  have h1 := tiltZ_nonneg (ψ := ψ) n ω t (x + 1)
  have h2 : zN n ψ ω t (x + 1) ≤ K := (hK t ht (x + 1)).trans
    (mul_le_of_le_one_right hK0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (abs_nonneg _))))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
  calc zN n ψ ω t x * zN n ψ ω t (x + 1) * |G x|
      ≤ (K * Real.exp (-|(x : ℝ)|)) * K * b := by
        gcongr
        · exact hK t ht x
        · exact hG x
    _ = _ := by ring

/-- `∑ₓ 𝔷_n(t,x) 𝔷_n(t,x+1) G(x)` converges for `t ∈ [0,T]` and bounded `G`. -/
lemma summable_zz (h : TiltGood n T ψ ω) {t : ℝ} (ht : t ∈ Icc 0 T) {G : ℤ → ℝ} {b : ℝ}
    (hG : ∀ x, |G x| ≤ b) :
    Summable fun x => zN n ψ ω t x * zN n ψ ω t (x + 1) * G x := by
  obtain ⟨K, hK0, hK⟩ := h.dom
  exact Summable.of_norm_bounded (tilt_summable_exp_neg_abs.mul_left (K * K * b))
    (norm_zz_le hK0 hK ht hG)

/-- `t ↦ ∑ₓ 𝔷_n(t,x) 𝔷_n(t,x+1) G(t,x)` is continuous on `[0,T]` for `G` bounded on `[0,T]`
and continuous in `t` (Weierstrass M-test). -/
lemma continuousOn_zz (h : TiltGood n T ψ ω) {G : ℝ → ℤ → ℝ} {b : ℝ}
    (hGc : ∀ x, ContinuousOn (G · x) (Icc 0 T)) (hGb : ∀ t ∈ Icc 0 T, ∀ x, |G t x| ≤ b) :
    ContinuousOn (fun t => ∑' x, zN n ψ ω t x * zN n ψ ω t (x + 1) * G t x) (Icc 0 T) := by
  obtain ⟨K, hK0, hK⟩ := h.dom
  refine continuousOn_tsum (fun x => ((h.cont x).mul (h.cont (x + 1))).mul (hGc x))
    (tilt_summable_exp_neg_abs.mul_left (K * K * b)) fun x t ht => ?_
  exact norm_zz_le hK0 hK ht (hGb t ht) x

/-- `t ↦ 𝒲_n(t)` is continuous on `[0,T]`. -/
lemma continuousOn_WN (h : TiltGood n T ψ ω) :
    ContinuousOn (fun t => WN n ψ t ω) (Icc 0 T) := by
  obtain ⟨K, hK0, hK⟩ := h.dom
  simp only [WN, pairZ, mul_one]
  refine continuousOn_tsum (fun x => h.cont x) (tilt_summable_exp_neg_abs.mul_left K)
    fun x t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (tiltZ_nonneg n ω t x)]
  exact hK t ht x

end TiltGood

/-- Almost surely, `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`. -/
lemma tilt_ae_summable [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t) := by
  filter_upwards [ae_tiltGood hB hψ hn] with ω hω t ht
  exact (hω t).summable ⟨ht, le_rfl⟩

/-- `ω ↦ 𝔷_n(r,x)` is measurable for `r ≥ 0`. -/
lemma tiltZ_measurable (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r)
    (x : ℤ) : Measurable fun ω => zN n ψ ω r x := by
  have hs : 0 ≤ n * r / 2 := by have := zero_le_one.trans hn; positivity
  have h := (hψ.adapted (n * r / 2).toNNReal x).mono (𝓕.le _) le_rfl
  rw [Real.coe_toNNReal _ hs] at h
  unfold zN density
  exact measurable_const.mul ((continuous_norm.pow 2).measurable.comp h)

end QSSEPtoKPZ
