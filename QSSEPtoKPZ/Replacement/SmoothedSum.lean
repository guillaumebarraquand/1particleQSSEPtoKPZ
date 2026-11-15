/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.L2Bound
public import QSSEPtoKPZ.Replacement.KappaRiemann
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# `‖(φ 𝒵_n(t)) ⋆ ρ_ε‖₂²` for the discrete measures `𝒵_n(t)` (task G3)

Auxiliary results for the proof of Proposition 6.2, for the measure
`𝒵_n(t) = ∑ₓ 𝔷_n(t,x) δ_{y_n(t,x)}` of (3.5) at a time where `𝒲_n(t) = ∑ₓ 𝔷_n(t,x)` converges.
They rest on (6.1) (`smoothedNormSq_eq`, task G2), which writes
`‖(φν) ⋆ ρ_ε‖₂² = ∫∫ φ(x) φ(y) κ_ε(x - y) ν(dx) ν(dy)`.

* `smoothedNormSq_tilted_eq`: the double integral is the double series
  `∑_{x₁} 𝔷_n(t,x₁) ∑_{x₂} 𝔷_n(t,x₂) φ(y₁) φ(y₂) κ_ε(y₁ - y₂)`;
* `abs_smoothedNormSq_tilted_le`: `|‖(φ 𝒵_n(t)) ⋆ ρ_ε‖₂²| ≤ C² (κ(0)/ε) 𝒲_n(t)²` if `|φ| ≤ C`;
* `abs_smoothedNormSq_tilted_sub_le`: if `|κ_{ε'}/b - κ_ε| ≤ Δ`, then
  `|‖(φ 𝒵_n(t)) ⋆ ρ_{ε'}‖₂²/b - ‖(φ 𝒵_n(t)) ⋆ ρ_ε‖₂²| ≤ Δ C² 𝒲_n(t)²`;
* `intervalIntegrable_smoothedNormSq_tilted`: `s ↦ ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²` is integrable on
  `[0,T]` when `ψ` has continuous paths, `𝒲_n` converges and is continuous on `[0,T]`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {ρ : ℝ → ℝ}

/-! ### Discrete measures `∑ₓ c(x) δ_{y(x)}` -/

/-- The total mass of `∑ₓ c(x) δ_{y(x)}` is `∑ₓ c(x)` (for `c ≥ 0` summable). -/
lemma discreteMeasure_univ {c : ℤ → ℝ} (hc : ∀ x, 0 ≤ c x) (hs : Summable c) (y : ℤ → ℝ) :
    (Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x)) Set.univ =
      ENNReal.ofReal (∑' x, c x) := by
  rw [Measure.sum_apply _ MeasurableSet.univ, ENNReal.ofReal_tsum_of_nonneg hc hs]
  simp

lemma isFiniteMeasure_discreteMeasure {c : ℤ → ℝ} (hc : ∀ x, 0 ≤ c x) (hs : Summable c)
    (y : ℤ → ℝ) :
    IsFiniteMeasure (Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x)) :=
  ⟨by rw [discreteMeasure_univ hc hs]; exact ENNReal.ofReal_lt_top⟩

/-- `∫ g d(∑ₓ c(x) δ_{y(x)}) = ∑ₓ c(x) g(y(x))` for `g` bounded measurable. -/
lemma integral_discreteMeasure {c : ℤ → ℝ} (hc : ∀ x, 0 ≤ c x) (hs : Summable c) (y : ℤ → ℝ)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∫ x, g x ∂(Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x)) =
      ∑' x, c x * g (y x) := by
  have := isFiniteMeasure_discreteMeasure hc hs y
  rw [integral_sum_measure]
  · congr 1; ext x
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc x), smul_eq_mul]
  · exact Integrable.of_bound hg.aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- **Double integral against a discrete measure.** For `ν = ∑ₓ c(x) δ_{y(x)}` and `f` bounded
measurable on `ℝ²`: `∫ f d(ν ⊗ ν) = ∑_a c(a) ∑_b c(b) f(y(a), y(b))`. -/
lemma integral_prod_discreteMeasure {c : ℤ → ℝ} (hc : ∀ x, 0 ≤ c x) (hs : Summable c)
    (y : ℤ → ℝ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ p, |f p| ≤ M) :
    ∫ p, f p ∂((Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x)).prod
        (Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x))) =
      ∑' a, c a * ∑' b, c b * f (y a, y b) := by
  set ν := Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_discreteMeasure hc hs y
  have hfi : Integrable f (ν.prod ν) := Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hM p)
  rw [integral_prod f hfi]
  have hin : ∀ x, ∫ y', f (x, y') ∂ν = ∑' b, c b * f (x, y b) := fun x =>
    integral_discreteMeasure hc hs y (hf.comp measurable_prodMk_left) fun _ => hM _
  rw [integral_discreteMeasure hc hs y (g := fun x => ∫ y', f (x, y') ∂ν)
    hf.stronglyMeasurable.integral_prod_right'.measurable (M := M * ν.real Set.univ)]
  · simp only [hin]
  · intro x
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun y' => by
      rw [Real.norm_eq_abs]; exact hM _)

/-- `|∫ f d(ν ⊗ ν)| ≤ M (∑ₓ c(x))²` for `ν = ∑ₓ c(x) δ_{y(x)}` and `|f| ≤ M`. -/
lemma abs_integral_prod_discreteMeasure_le {c : ℤ → ℝ} (hc : ∀ x, 0 ≤ c x) (hs : Summable c)
    (y : ℤ → ℝ) {f : ℝ × ℝ → ℝ} {M : ℝ} (hM : ∀ p, |f p| ≤ M) :
    |∫ p, f p ∂((Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x)).prod
        (Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x)))| ≤
      M * (∑' x, c x) ^ 2 := by
  set ν := Measure.sum fun x => ENNReal.ofReal (c x) • Measure.dirac (y x) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_discreteMeasure hc hs y
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun p => by
    rw [Real.norm_eq_abs]; exact hM p)).trans (le_of_eq ?_)
  rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, hν, discreteMeasure_univ hc hs,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (tsum_nonneg hc), sq]

/-! ### The tilted field -/

lemma replZN_nonneg (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) : 0 ≤ zN n ψ ω t x :=
  mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

lemma replWN_eq_tsum (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (ω : Ω) :
    WN n ψ t ω = ∑' x, zN n ψ ω t x := by
  simp [WN, pairZ]

lemma replWN_nonneg (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (ω : Ω) : 0 ≤ WN n ψ t ω := by
  rw [replWN_eq_tsum]; exact tsum_nonneg (replZN_nonneg n ψ ω t)

/-- `|φ_t(x)| ≤ C` on `[0, T] × ℝ` for `φ ∈ C_b^{1,3}` with `‖φ‖_{1,3} ≤ C`. -/
lemma IsC13.replAbs_le {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) (x : ℝ) : |φ t x| ≤ C := by
  obtain ⟨c, hsum, hb⟩ := hφ.bound
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    obtain ⟨h0, h1, h2, h3, h4⟩ := hb t ht x
    fin_cases i
    exacts [(abs_nonneg _).trans h0, (abs_nonneg _).trans h1, (abs_nonneg _).trans h2,
      (abs_nonneg _).trans h3, (abs_nonneg _).trans h4]
  exact (hb t ht x).1.trans ((Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ 0)).trans
    hsum)

lemma IsC13.replContinuous {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : Continuous (φ t) :=
  (hφ.contDiff t ht).continuous

lemma replContinuous_kappaEps (hρ : IsMollifier ρ) (ε : ℝ) : Continuous (kappaEps ρ ε) :=
  (hρ.kappa_even_nonneg_smooth.2.2.continuous.comp (continuous_id.div_const ε)).div_const ε

/-- **(6.1) for `𝒵_n(t)`, as a double series.** -/
theorem smoothedNormSq_tilted_eq (hρ : IsMollifier ρ) {n : ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    {t : ℝ} (hz : Summable (zN n ψ ω t)) {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hφb : ∀ x, |φ x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    smoothedNormSq (tiltedMeasure n ψ ω t) φ ρ ε =
      ∑' a, zN n ψ ω t a * ∑' b, zN n ψ ω t b *
        (φ (rescaledPosition n t a) * φ (rescaledPosition n t b) *
          kappaEps ρ ε (rescaledPosition n t a - rescaledPosition n t b)) := by
  have : IsFiniteMeasure (tiltedMeasure n ψ ω t) :=
    isFiniteMeasure_discreteMeasure (replZN_nonneg n ψ ω t) hz (rescaledPosition n t)
  have h := (smoothedNormSq_eq hρ (tiltedMeasure n ψ ω t) hφ ⟨C, hφb⟩ hε).2.2
  rw [h]
  refine integral_prod_discreteMeasure (replZN_nonneg n ψ ω t) hz (rescaledPosition n t)
    (f := fun p : ℝ × ℝ => φ p.1 * φ p.2 * kappaEps ρ ε (p.1 - p.2)) ?_
    (M := C * C * (kappa ρ 0 / ε)) fun p => ?_
  · exact ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd)).mul
      ((replContinuous_kappaEps hρ ε).comp (continuous_fst.sub continuous_snd)) |>.measurable
  · have hk := replKappaEps_nonneg_le hρ hε (p.1 - p.2)
    rw [abs_mul, abs_mul, abs_of_nonneg hk.1]
    exact mul_le_mul (mul_le_mul (hφb _) (hφb _) (abs_nonneg _) ((abs_nonneg _).trans (hφb 0)))
      hk.2 hk.1 (mul_nonneg ((abs_nonneg _).trans (hφb 0)) ((abs_nonneg _).trans (hφb 0)))

/-- `|‖(φ 𝒵_n(t)) ⋆ ρ_ε‖₂²| ≤ C² (κ(0)/ε) 𝒲_n(t)²` if `|φ| ≤ C`. -/
theorem abs_smoothedNormSq_tilted_le (hρ : IsMollifier ρ) {n : ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    {ω : Ω} {t : ℝ} (hz : Summable (zN n ψ ω t)) {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hφb : ∀ x, |φ x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    |smoothedNormSq (tiltedMeasure n ψ ω t) φ ρ ε| ≤ C ^ 2 * (kappa ρ 0 / ε) * WN n ψ t ω ^ 2 := by
  have : IsFiniteMeasure (tiltedMeasure n ψ ω t) :=
    isFiniteMeasure_discreteMeasure (replZN_nonneg n ψ ω t) hz (rescaledPosition n t)
  rw [(smoothedNormSq_eq hρ (tiltedMeasure n ψ ω t) hφ ⟨C, hφb⟩ hε).2.2, replWN_eq_tsum]
  refine abs_integral_prod_discreteMeasure_le (replZN_nonneg n ψ ω t) hz (rescaledPosition n t)
    fun p => ?_
  have hk := replKappaEps_nonneg_le hρ hε (p.1 - p.2)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hφb 0)
  rw [abs_mul, abs_mul, abs_of_nonneg hk.1, sq]
  exact mul_le_mul (mul_le_mul (hφb _) (hφb _) (abs_nonneg _) hC) hk.2 hk.1 (mul_nonneg hC hC)

/-- **Comparison of two smoothings.** If `|κ_{ε'}(x)/b - κ_ε(x)| ≤ Δ` for all `x`, then
`|‖(φ 𝒵_n(t)) ⋆ ρ_{ε'}‖₂²/b - ‖(φ 𝒵_n(t)) ⋆ ρ_ε‖₂²| ≤ Δ C² 𝒲_n(t)²` if `|φ| ≤ C`
(by (6.1), as in the last display but one of the proof of Proposition 6.2). -/
theorem abs_smoothedNormSq_tilted_sub_le (hρ : IsMollifier ρ) {n : ℝ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {t : ℝ} (hz : Summable (zN n ψ ω t)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {C : ℝ} (hφb : ∀ x, |φ x| ≤ C) {ε ε' b Δ : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') (hΔ : ∀ x, |kappaEps ρ ε' x / b - kappaEps ρ ε x| ≤ Δ) :
    |smoothedNormSq (tiltedMeasure n ψ ω t) φ ρ ε' / b -
      smoothedNormSq (tiltedMeasure n ψ ω t) φ ρ ε| ≤ Δ * C ^ 2 * WN n ψ t ω ^ 2 := by
  have : IsFiniteMeasure (tiltedMeasure n ψ ω t) :=
    isFiniteMeasure_discreteMeasure (replZN_nonneg n ψ ω t) hz (rescaledPosition n t)
  have h1 := smoothedNormSq_eq hρ (tiltedMeasure n ψ ω t) hφ ⟨C, hφb⟩ hε'
  have h2 := smoothedNormSq_eq hρ (tiltedMeasure n ψ ω t) hφ ⟨C, hφb⟩ hε
  rw [h1.2.2, h2.2.2, ← integral_div, ← integral_sub (h1.2.1.div_const b) h2.2.1, replWN_eq_tsum]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hφb 0)
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
  refine (abs_integral_prod_discreteMeasure_le (replZN_nonneg n ψ ω t) hz (rescaledPosition n t)
    (M := Δ * C ^ 2) fun p => ?_).trans (le_of_eq (by ring))
  have e : φ p.1 * φ p.2 * kappaEps ρ ε' (p.1 - p.2) / b - φ p.1 * φ p.2 * kappaEps ρ ε (p.1 - p.2)
      = φ p.1 * φ p.2 * (kappaEps ρ ε' (p.1 - p.2) / b - kappaEps ρ ε (p.1 - p.2)) := by ring
  rw [e, abs_mul, abs_mul, sq]
  calc |φ p.1| * |φ p.2| * |kappaEps ρ ε' (p.1 - p.2) / b - kappaEps ρ ε (p.1 - p.2)|
      ≤ C * C * Δ := mul_le_mul (mul_le_mul (hφb _) (hφb _) (abs_nonneg _) hC) (hΔ _)
        (abs_nonneg _) (mul_nonneg hC hC)
    _ = Δ * (C * C) := by ring

/-- `s ↦ 𝔷_n(s,x)` is continuous on `[0, ∞)` when `t ↦ ψ_t` is continuous. -/
lemma replContinuousOn_zN {n : ℝ} (hn : 0 ≤ n) {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hψc : Continuous fun t : ℝ≥0 => ψ t ω) (x : ℤ) :
    ContinuousOn (fun s => zN n ψ ω s x) (Set.Ici 0) := by
  have hg : Continuous fun s : ℝ => ψ ((n * s / 2).toNNReal : ℝ) ω x :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp hψc).comp
      (continuous_real_toNNReal.comp (by fun_prop))
  have hcont : Continuous fun s : ℝ => Real.exp (thetaN n * x - n * lambdaN n / 2 * s) *
      ‖ψ ((n * s / 2).toNNReal : ℝ) ω x‖ ^ 2 :=
    (Real.continuous_exp.comp (by fun_prop)).mul ((continuous_norm.comp hg).pow 2)
  refine hcont.continuousOn.congr fun s hs => ?_
  simp only [zN, density]
  rw [Real.coe_toNNReal _ (by have : (0 : ℝ) ≤ s := hs; positivity)]

/-- **Integrability of `s ↦ ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²` on `[0, T]`** (first item of
Proposition 6.2), for a realization `ω` such that `t ↦ ψ_t` is continuous, `∑ₓ 𝔷_n(t,x)`
converges for all `t ≥ 0`, and `𝒲_n` is continuous on `[0, T]`: the function is the double
series of `smoothedNormSq_tilted_eq`, whose terms are continuous in `s`, and it is bounded by
`C² (κ(0)/ε) sup_{[0,T]} 𝒲_n²`. -/
theorem intervalIntegrable_smoothedNormSq_tilted (hρ : IsMollifier ρ) {T C : ℝ} (hT : 0 ≤ T)
    {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {n : ℝ} (hn : 0 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} (hψc : Continuous fun t : ℝ≥0 => ψ t ω)
    (hz : ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t))
    (hW : ContinuousOn (fun t => WN n ψ t ω) (Set.Icc 0 T)) :
    IntervalIntegrable (fun s => smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) volume 0 T := by
  set G : ℝ → ℝ := fun s => ∑' a, zN n ψ ω s a * ∑' b, zN n ψ ω s b *
    (φ s (rescaledPosition n s a) * φ s (rescaledPosition n s b) *
      kappaEps ρ ε (rescaledPosition n s a - rescaledPosition n s b)) with hG
  have hzc : ∀ x, ContinuousOn (fun s => zN n ψ ω s x) (Set.Icc 0 T) := fun x =>
    (replContinuousOn_zN hn hψc x).mono fun s hs => hs.1
  have hφc : ∀ x : ℤ, ContinuousOn (fun s => φ s (rescaledPosition n s x)) (Set.Icc 0 T) := by
    intro x
    have h := hφ.continuousOn.2 0 (by norm_num)
    simp only [iteratedDeriv_zero] at h
    refine h.comp (continuousOn_id.prodMk ?_) fun s hs => ⟨hs, Set.mem_univ _⟩
    fun_prop
  have hκc : ∀ a b : ℤ, Continuous fun s =>
      kappaEps ρ ε (rescaledPosition n s a - rescaledPosition n s b) := fun a b =>
    (replContinuous_kappaEps hρ ε).comp (by unfold rescaledPosition; fun_prop)
  have hGm : AEStronglyMeasurable G (volume.restrict (Set.Icc 0 T)) := by
    refine AEStronglyMeasurable.tsum fun a => ?_
    refine ((hzc a).aestronglyMeasurable measurableSet_Icc).mul
      (AEStronglyMeasurable.tsum fun b => ?_)
    exact (((hzc b).mul (((hφc a).mul (hφc b)).mul (hκc a b).continuousOn))).aestronglyMeasurable
      measurableSet_Icc
  have heq : ∀ s ∈ Set.Icc 0 T,
      smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε = G s := fun s hs =>
    smoothedNormSq_tilted_eq hρ (hz s hs.1) (hφ.replContinuous hs) (hφ.replAbs_le hs) hε
  obtain ⟨Wm, hWm⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  refine ⟨?_, HasFiniteIntegral.restrict_of_bounded (C := C ^ 2 * (kappa ρ 0 / ε) * Wm ^ 2)
    measure_Ioc_lt_top ?_⟩
  · refine (hGm.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    exact (heq s (Set.Ioc_subset_Icc_self hs)).symm
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    have hs' := Set.Ioc_subset_Icc_self hs
    rw [Real.norm_eq_abs]
    refine (abs_smoothedNormSq_tilted_le hρ (hz s hs'.1) (hφ.replContinuous hs')
      (hφ.replAbs_le hs') hε).trans ?_
    have hk : 0 ≤ C ^ 2 * (kappa ρ 0 / ε) :=
      mul_nonneg (sq_nonneg _) (div_nonneg hρ.kappa_zero_pos.le hε.le)
    refine mul_le_mul_of_nonneg_left ?_ hk
    have := hWm s hs'
    rw [Real.norm_eq_abs] at this
    exact sq_le_sq' (by linarith [abs_le.1 this, replWN_nonneg n ψ s ω]) (le_trans (le_abs_self _) this)

end QSSEPtoKPZ
