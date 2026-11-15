/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Increments
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Moments of order up to four of Brownian increments against the past (package C, task C2,
auxiliary)

For a Brownian family `B` and times `s ≤ t`, write `Zᵢ = Bᵢ(t) - Bᵢ(s)` and `Δ = t - s`.

* `fourthMom_integral_gaussianReal_pow_three`, `fourthMom_integral_gaussianReal_pow_four`:
  `∫ x³ dN(0, v) = 0`, `∫ x⁴ dN(0, v) = 3 v²` (derivatives of the moment generating function
  `exp (v t² / 2)`).
* `IsBrownianFamily.fourthMom_integral_incr_mul₃`, `IsBrownianFamily.fourthMom_integral_incr_mul₄`:
  Isserlis' formulas `𝔼[Zᵢ Zⱼ Zₖ] = 0`, `𝔼[Zᵢ Zⱼ Zₖ Zₗ] = Δ² (δᵢⱼ δₖₗ + δᵢₖ δⱼₗ + δᵢₗ δⱼₖ)`.
* `IsBrownianFamily.fourthMom_integral_mul_sum_pow_*`: for `D = ∑_{i ∈ F} xᵢ Zᵢ` with bounded
  `𝓖_s`-measurable `xᵢ`, `σ² = ∑_{i ∈ F} xᵢ²`, and `η` square integrable and `𝓖_s`-measurable,
  `𝔼[η D] = 0`, `𝔼[η D²] = Δ 𝔼[η σ²]`, `𝔼[η D³] = 0`, `𝔼[η D⁴] = 3 Δ² 𝔼[η σ⁴]`: the conditional
  law of `D` given `𝓖_s` is `N(0, σ² Δ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### Third and fourth moments of a centered Gaussian -/

private lemma deriv_poly_mul_exp (v : ℝ) (p p' : ℝ → ℝ) (hp : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * Real.exp (v * t ^ 2 / 2)) =
      fun t => (p' t + p t * (v * t)) * Real.exp (v * t ^ 2 / 2) := by
  funext t
  have hq : HasDerivAt (fun t : ℝ => v * t ^ 2 / 2) (v * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul v).div_const 2
    convert this using 1; push_cast; ring
  exact ((hp t).fun_mul hq.exp).deriv.trans (by ring)

/-- The derivatives of order `3` and `4` at `0` of the moment generating function
`t ↦ exp (v t² / 2)` of `N(0, v)` are `0` and `3 v²`. -/
private lemma gaussianReal_moments_three_four (v : ℝ≥0) :
    ∫ x, x ^ 3 ∂gaussianReal 0 v = 0 ∧ ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  have hI : ∀ n, ∫ x, x ^ n ∂gaussianReal 0 v =
      iteratedDeriv n (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 := fun n => by
    have hm := mgf_fun_id_gaussianReal (μ := 0) (v := v)
    simp only [zero_mul, zero_add] at hm
    rw [← hm, iteratedDeriv_mgf_zero] <;> simp
  have hE := deriv_poly_mul_exp (v : ℝ)
  have i0 : iteratedDeriv 0 (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => 1 * Real.exp (v * t ^ 2 / 2) := by simp
  have i1 : iteratedDeriv 1 (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (v * t) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, i0, hE (fun _ => 1) (fun _ => 0) (fun t => hasDerivAt_const t 1)]
    funext t; ring
  have i2 : iteratedDeriv 2 (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (v + v ^ 2 * t ^ 2) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, i1, hE _ (fun _ => (v : ℝ)) (fun t => by
      simpa using (hasDerivAt_id t).const_mul (v : ℝ))]
    funext t; ring
  have i3 : iteratedDeriv 3 (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, i2, hE _ (fun t => 2 * (v : ℝ) ^ 2 * t) (fun t => by
      convert ((hasDerivAt_pow 2 t).const_mul ((v : ℝ) ^ 2)).const_add (v : ℝ) using 1
      push_cast; ring)]
    funext t; ring
  have i4 : iteratedDeriv 4 (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, i3, hE _ (fun t => 3 * (v : ℝ) ^ 2 + 3 * v ^ 3 * t ^ 2) (fun t => by
      convert ((hasDerivAt_id t).const_mul (3 * (v : ℝ) ^ 2)).add
        ((hasDerivAt_pow 3 t).const_mul ((v : ℝ) ^ 3)) using 1
      · funext t; simp
      · push_cast; ring)]
    funext t; ring
  refine ⟨?_, ?_⟩
  · rw [hI, i3]; simp
  · rw [hI, i4]; simp

/-- `∫ x³ dN(0, v) = 0`. -/
lemma fourthMom_integral_gaussianReal_pow_three (v : ℝ≥0) : ∫ x, x ^ 3 ∂gaussianReal 0 v = 0 :=
  (gaussianReal_moments_three_four v).1

/-- `∫ x⁴ dN(0, v) = 3 v²`. -/
lemma fourthMom_integral_gaussianReal_pow_four (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 :=
  (gaussianReal_moments_three_four v).2

/-! ### Products of functions with moments of all orders -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- If `f` and `g` have moments of all finite orders, so does `f g`. -/
lemma fourthMom_memLp_mul {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ) (hg : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp g p μ) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun ω => f ω * g ω) p μ := by
  intro p hp
  have : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
        ENNReal.inv_two_add_inv_two, one_mul]⟩
  exact (hf (2 * p) (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp)).fun_mul
    (hg (2 * p) (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp))

/-! ### Moments of Brownian increments -/

namespace IsBrownianFamily

variable {ι : Type*} {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {B : ι → ℝ → Ω → ℝ}

/-- The increment `Zᵢ` is measurable. -/
lemma fourthMom_measurable_incr (hB : IsBrownianFamily 𝓖 B μ) (i : ι) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable (fun ω => B i t ω - B i s ω) :=
  (hB.measurable_incr i hst).mono (𝓖.le t) le_rfl

/-- `𝔼[Zᵢ³] = 0`. -/
lemma fourthMom_integral_incr_pow_three (hB : IsBrownianFamily 𝓖 B μ) (i : ι) {s t : ℝ≥0}
    (hst : s ≤ t) : ∫ ω, (B i t ω - B i s ω) ^ 3 ∂μ = 0 := by
  have := (hB.gaussian i s t hst).integral_comp (f := fun x : ℝ => x ^ 3)
    (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, fourthMom_integral_gaussianReal_pow_three]

/-- `𝔼[Zᵢ⁴] = 3 Δ²`. -/
lemma fourthMom_integral_incr_pow_four (hB : IsBrownianFamily 𝓖 B μ) (i : ι) {s t : ℝ≥0}
    (hst : s ≤ t) : ∫ ω, (B i t ω - B i s ω) ^ 4 ∂μ = 3 * ((t : ℝ) - s) ^ 2 := by
  have := (hB.gaussian i s t hst).integral_comp (f := fun x : ℝ => x ^ 4)
    (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, fourthMom_integral_gaussianReal_pow_four, NNReal.coe_sub hst]

/-- `𝔼[Zᵢ²] = Δ`. -/
lemma fourthMom_integral_incr_sq (hB : IsBrownianFamily 𝓖 B μ) (i : ι) {s t : ℝ≥0}
    (hst : s ≤ t) : ∫ ω, (B i t ω - B i s ω) ^ 2 ∂μ = (t : ℝ) - s := by
  simpa [sq] using hB.integral_incr_mul_incr i i hst

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A lonely index: if `i ∉ T`, then `𝔼[Zᵢ g((Zⱼ)_{j ∈ T})] = 0`. -/
private lemma integral_incr_mul_comp (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t)
    {i : ι} {T : Finset ι} (hi : i ∉ T) {g : (T → ℝ) → ℝ} (hg : Measurable g) :
    ∫ ω, (B i t ω - B i s ω) * g (fun a : T => B a t ω - B a s ω) ∂μ = 0 := by
  have hind := (hB.indep s t hst).indepFun_finset {i} T (Finset.disjoint_singleton_left.2 hi)
    (fun j => hB.fourthMom_measurable_incr j hst)
  have h2 := hind.comp (φ := fun y : ({i} : Finset ι) → ℝ => y ⟨i, Finset.mem_singleton_self i⟩)
    (ψ := g) (_mγ := inferInstance) (_mγ' := inferInstance) (by fun_prop) hg
  have := h2.integral_fun_mul_eq_mul_integral
    (hB.fourthMom_measurable_incr i hst).aestronglyMeasurable
    (hg.comp (measurable_pi_iff.2 fun a => hB.fourthMom_measurable_incr a hst)).aestronglyMeasurable
  simp only [Function.comp_def] at this
  rw [this, hB.integral_incr i hst, zero_mul]

omit [IsProbabilityMeasure μ] in
/-- `𝔼[Zᵢ Zⱼ Zₖ] = 0` if `i ∉ {j, k}`. -/
private lemma lonely3 (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t) {i j k : ι}
    (hj : i ≠ j) (hk : i ≠ k) :
    ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) ∂μ = 0 := by
  classical
  have hi : i ∉ ({j, k} : Finset ι) := by simp [hj, hk]
  have h := hB.integral_incr_mul_comp hst hi
    (g := fun y => y ⟨j, by simp⟩ * y ⟨k, by simp⟩) (by fun_prop)
  simp only at h
  rw [← h]; congr 1; funext ω; ring

omit [IsProbabilityMeasure μ] in
/-- `𝔼[Zᵢ Zⱼ Zₖ Zₗ] = 0` if `i ∉ {j, k, l}`. -/
private lemma lonely4 (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t) {i j k l : ι}
    (hj : i ≠ j) (hk : i ≠ k) (hl : i ≠ l) :
    ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) *
      (B l t ω - B l s ω) ∂μ = 0 := by
  classical
  have hi : i ∉ ({j, k, l} : Finset ι) := by simp [hj, hk, hl]
  have h := hB.integral_incr_mul_comp hst hi
    (g := fun y => y ⟨j, by simp⟩ * y ⟨k, by simp⟩ * y ⟨l, by simp⟩) (by fun_prop)
  simp only at h
  rw [← h]; congr 1; funext ω; ring

omit [IsProbabilityMeasure μ] in
/-- `𝔼[Zᵢ² Zₖ²] = Δ²` if `i ≠ k`. -/
private lemma pair4 (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t) {i k : ι}
    (hik : i ≠ k) :
    ∫ ω, (B i t ω - B i s ω) * (B i t ω - B i s ω) * (B k t ω - B k s ω) *
      (B k t ω - B k s ω) ∂μ = ((t : ℝ) - s) ^ 2 := by
  have hind := ((hB.indep s t hst).indepFun hik).comp (φ := fun x : ℝ => x ^ 2)
    (ψ := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
  have := hind.integral_fun_mul_eq_mul_integral
    ((hB.fourthMom_measurable_incr i hst).pow_const 2).aestronglyMeasurable
    ((hB.fourthMom_measurable_incr k hst).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_def] at this
  rw [show (fun ω => (B i t ω - B i s ω) * (B i t ω - B i s ω) * (B k t ω - B k s ω) *
      (B k t ω - B k s ω)) = fun ω => (B i t ω - B i s ω) ^ 2 * (B k t ω - B k s ω) ^ 2 from
    funext fun ω => by ring, this, hB.fourthMom_integral_incr_sq i hst,
    hB.fourthMom_integral_incr_sq k hst, sq]

omit [IsProbabilityMeasure μ] in
/-- **Isserlis, order three.** `𝔼[Zᵢ Zⱼ Zₖ] = 0`. -/
lemma fourthMom_integral_incr_mul₃ (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t)
    (i j k : ι) :
    ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) ∂μ = 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hik : i = k
    · subst hik
      rw [← hB.fourthMom_integral_incr_pow_three i hst]; congr 1; funext ω; ring
    · rw [← hB.lonely3 hst (Ne.symm hik) (Ne.symm hik)]; congr 1; funext ω; ring
  · by_cases hik : i = k
    · subst hik
      rw [← hB.lonely3 hst (Ne.symm hij) (Ne.symm hij)]; congr 1; funext ω; ring
    · exact hB.lonely3 hst hij hik

omit [IsProbabilityMeasure μ] in
open Classical in
/-- **Isserlis, order four.**
`𝔼[Zᵢ Zⱼ Zₖ Zₗ] = Δ² (δᵢⱼ δₖₗ + δᵢₖ δⱼₗ + δᵢₗ δⱼₖ)`. -/
lemma fourthMom_integral_incr_mul₄ (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t)
    (i j k l : ι) :
    ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) *
      (B l t ω - B l s ω) ∂μ = ((t : ℝ) - s) ^ 2 *
      ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0)) := by
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        have h : ∫ ω, (B i t ω - B i s ω) * (B i t ω - B i s ω) * (B i t ω - B i s ω) *
            (B i t ω - B i s ω) ∂μ = 3 * ((t : ℝ) - s) ^ 2 := by
          rw [← hB.fourthMom_integral_incr_pow_four i hst]; congr 1; funext ω; ring
        rw [h]; simp; ring
      · rw [hB.pair4 hst hik]; simp [hik]
    · by_cases hik : i = k
      · subst hik
        have h : ∫ ω, (B i t ω - B i s ω) * (B i t ω - B i s ω) * (B i t ω - B i s ω) *
            (B l t ω - B l s ω) ∂μ = 0 := by
          rw [← hB.lonely4 hst (Ne.symm hkl) (Ne.symm hkl) (Ne.symm hkl) (i := l) (j := i)
            (k := i) (l := i)]
          congr 1; funext ω; ring
        rw [h]; simp [hkl]
      · have h : ∫ ω, (B i t ω - B i s ω) * (B i t ω - B i s ω) * (B k t ω - B k s ω) *
            (B l t ω - B l s ω) ∂μ = 0 := by
          rw [← hB.lonely4 hst (Ne.symm hik) (Ne.symm hik) hkl (i := k) (j := i) (k := i)
            (l := l)]
          congr 1; funext ω; ring
        rw [h]; simp [hik, hkl]
  · by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · subst hjl
        have h : ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B i t ω - B i s ω) *
            (B j t ω - B j s ω) ∂μ = ((t : ℝ) - s) ^ 2 := by
          rw [← hB.pair4 hst hij]; congr 1; funext ω; ring
        rw [h]; simp [hij]
      · have h : ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B i t ω - B i s ω) *
            (B l t ω - B l s ω) ∂μ = 0 := by
          rw [← hB.lonely4 hst (Ne.symm hij) (Ne.symm hij) hjl (i := j) (j := i) (k := i)
            (l := l)]
          congr 1; funext ω; ring
        rw [h]; simp [hij, hjl, Ne.symm hij]
    · by_cases hil : i = l
      · subst hil
        by_cases hjk : j = k
        · subst hjk
          have h : ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B j t ω - B j s ω) *
              (B i t ω - B i s ω) ∂μ = ((t : ℝ) - s) ^ 2 := by
            rw [← hB.pair4 hst hij]; congr 1; funext ω; ring
          rw [h]; simp [hij]
        · have h : ∫ ω, (B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) *
              (B i t ω - B i s ω) ∂μ = 0 := by
            rw [← hB.lonely4 hst (Ne.symm hij) hjk (Ne.symm hij) (i := j) (j := i) (k := k)
              (l := i)]
            congr 1; funext ω; ring
          rw [h]; simp [hij, hjk, hik]
      · rw [hB.lonely4 hst hij hik hil]; simp [hij, hik, hil]

end IsBrownianFamily

/-! ### Finite sums -/

/-- Expansion of a fourth power of a finite sum. -/
lemma fourthMom_sum_pow_four {ι : Type*} (F : Finset ι) (a : ι → ℝ) : (∑ i ∈ F, a i) ^ 4 =
    ∑ l ∈ F, ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, a i * a j * a k * a l := by
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]

/-- Expansion of a third power of a finite sum. -/
lemma fourthMom_sum_pow_three {ι : Type*} (F : Finset ι) (a : ι → ℝ) : (∑ i ∈ F, a i) ^ 3 =
    ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, a i * a j * a k := by
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]

/-- Expansion of a square of a finite sum. -/
lemma fourthMom_sum_sq {ι : Type*} (F : Finset ι) (a : ι → ℝ) : (∑ i ∈ F, a i) ^ 2 =
    ∑ j ∈ F, ∑ i ∈ F, a i * a j := by
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]

open Classical in
/-- `∑ᵢⱼₖₗ η xᵢ xⱼ xₖ xₗ (δᵢⱼ δₖₗ + δᵢₖ δⱼₗ + δᵢₗ δⱼₖ) = 3 η (∑ᵢ xᵢ²)²`. -/
private lemma sum_isserlis {ι : Type*} (F : Finset ι) (x : ι → ℝ) (η : ℝ) :
    ∑ l ∈ F, ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, η * x i * x j * x k * x l *
      ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0)) =
    3 * (η * (∑ i ∈ F, x i ^ 2) ^ 2) := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']
  rw [sq (∑ i ∈ F, x i ^ 2), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Product of two square integrable functions, in lambda form. -/
private lemma integrable_mul_two {μ : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : Integrable (fun ω => f ω * g ω) μ :=
  hf.integrable_mul hg

/-- Integral of a double finite sum. -/
private lemma integral_sum₂ {μ : Measure Ω} {ι : Type*} (F : Finset ι) {f : ι → ι → Ω → ℝ}
    (hf : ∀ i j, Integrable (f i j) μ) :
    ∫ ω, ∑ j ∈ F, ∑ i ∈ F, f i j ω ∂μ = ∑ j ∈ F, ∑ i ∈ F, ∫ ω, f i j ω ∂μ := by
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hf i j]
  exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun i _ => hf i j

/-- Integral of a triple finite sum. -/
private lemma integral_sum₃ {μ : Measure Ω} {ι : Type*} (F : Finset ι)
    {f : ι → ι → ι → Ω → ℝ} (hf : ∀ i j k, Integrable (f i j k) μ) :
    ∫ ω, ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, f i j k ω ∂μ =
      ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, ∫ ω, f i j k ω ∂μ := by
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun i _ => hf i j k]
  exact Finset.sum_congr rfl fun k _ => integral_sum₂ F fun i j => hf i j k

/-- Integral of a quadruple finite sum. -/
private lemma integral_sum₄ {μ : Measure Ω} {ι : Type*} (F : Finset ι)
    {f : ι → ι → ι → ι → Ω → ℝ} (hf : ∀ i j k l, Integrable (f i j k l) μ) :
    ∫ ω, ∑ l ∈ F, ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, f i j k l ω ∂μ =
      ∑ l ∈ F, ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, ∫ ω, f i j k l ω ∂μ := by
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hf i j k l]
  exact Finset.sum_congr rfl fun l _ => integral_sum₃ F fun i j k => hf i j k l

/-! ### Conditional moments of `∑ᵢ xᵢ Zᵢ` given the past -/

namespace IsBrownianFamily

variable {ι : Type*} {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ι → ℝ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- A function measurable for the increments on `[s, t]` is measurable. -/
lemma fourthMom_measurable_of_incrSigma (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t)
    {W : Ω → ℝ} (hW : Measurable[incrSigma B s t] W) : Measurable W :=
  hW.mono (iSup_le fun i => (hB.fourthMom_measurable_incr i hst).comap_le) le_rfl

omit [IsProbabilityMeasure μ] in
/-- `𝔼[c W] = 𝔼[c] 𝔼[W]` for `c` known at time `s` and `W` a function of the increments on
`[s, t]`. -/
lemma fourthMom_integral_past_mul (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t)
    {c W : Ω → ℝ} (hc : Measurable[𝓖 s] c) (hW : Measurable[incrSigma B s t] W) :
    ∫ ω, c ω * W ω ∂μ = (∫ ω, c ω ∂μ) * ∫ ω, W ω ∂μ :=
  (hB.indepFun_past hst hc hW).integral_fun_mul_eq_mul_integral
    (hc.mono (𝓖.le s) le_rfl).aestronglyMeasurable
    (hB.fourthMom_measurable_of_incrSigma hst hW).aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
/-- Increments have moments of all finite orders. -/
lemma fourthMom_memLp_incr (hB : IsBrownianFamily 𝓖 B μ) (i : ι) {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun ω => B i t ω - B i s ω) p μ :=
  fun _ hp => hB.memLp_incr i hst hp

variable (hB : IsBrownianFamily 𝓖 B μ) {s t : ℝ≥0} (hst : s ≤ t) (F : Finset ι)
  {x : ι → Ω → ℝ} (hx : ∀ i, Measurable[𝓖 s] (x i)) (hxb : ∀ i, MemLp (x i) ∞ μ)
  {η : Ω → ℝ} (hη : Measurable[𝓖 s] η) (hη2 : MemLp η 2 μ)
include hB hst hx hxb hη hη2

omit [IsProbabilityMeasure μ] in
/-- `𝔼[η ∑ᵢ xᵢ Zᵢ] = 0`. -/
lemma fourthMom_integral_mul_sum_pow_one :
    ∫ ω, η ω * ∑ i ∈ F, x i ω * (B i t ω - B i s ω) ∂μ = 0 := by
  have hpt : ∀ ω, η ω * ∑ i ∈ F, x i ω * (B i t ω - B i s ω) =
      ∑ i ∈ F, (η ω * x i ω) * (B i t ω - B i s ω) := fun ω => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_mul_two (hη2.fun_mul (r := 2) (hxb i))
    (hB.memLp_incr i hst (p := 2) (by simp))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hB.fourthMom_integral_past_mul hst (hη.fun_mul (hx i)) (measurable_incrSigma i s t),
    hB.integral_incr i hst, mul_zero]

/-- `𝔼[η (∑ᵢ xᵢ Zᵢ)²] = Δ 𝔼[η ∑ᵢ xᵢ²]`. -/
lemma fourthMom_integral_mul_sum_pow_two :
    ∫ ω, η ω * (∑ i ∈ F, x i ω * (B i t ω - B i s ω)) ^ 2 ∂μ =
      ((t : ℝ) - s) * ∫ ω, η ω * ∑ i ∈ F, x i ω ^ 2 ∂μ := by
  classical
  have hpt : ∀ ω, η ω * (∑ i ∈ F, x i ω * (B i t ω - B i s ω)) ^ 2 =
      ∑ j ∈ F, ∑ i ∈ F, (η ω * x i ω * x j ω) *
        ((B i t ω - B i s ω) * (B j t ω - B j s ω)) := fun ω => by
    rw [fourthMom_sum_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hc2 : ∀ i j, MemLp (fun ω => η ω * x i ω * x j ω) 2 μ := fun i j =>
    (hη2.fun_mul (r := 2) (hxb i)).fun_mul (r := 2) (hxb j)
  have hW : ∀ i j, ∀ p : ℝ≥0∞, p ≠ ∞ →
      MemLp (fun ω => (B i t ω - B i s ω) * (B j t ω - B j s ω)) p μ := fun i j =>
    fourthMom_memLp_mul (hB.fourthMom_memLp_incr i hst) (hB.fourthMom_memLp_incr j hst)
  simp_rw [hpt]
  rw [integral_sum₂ F fun i j => integrable_mul_two (hc2 i j) (hW i j 2 (by simp))]
  have hterm : ∀ i j, ∫ ω, (η ω * x i ω * x j ω) *
      ((B i t ω - B i s ω) * (B j t ω - B j s ω)) ∂μ =
      ∫ ω, (η ω * x i ω * x j ω) * (((t : ℝ) - s) * (if i = j then 1 else 0)) ∂μ := by
    intro i j
    rw [hB.fourthMom_integral_past_mul hst ((hη.fun_mul (hx i)).fun_mul (hx j))
      ((measurable_incrSigma i s t).fun_mul (measurable_incrSigma j s t)),
      hB.integral_incr_mul_incr i j hst, integral_mul_const]
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← integral_sum₂ F fun i j => ((hc2 i j).integrable (by simp)).mul_const _,
    ← integral_const_mul]
  congr 1; funext ω
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [hi, ite_true]; ring

omit [IsProbabilityMeasure μ] in
/-- `𝔼[η (∑ᵢ xᵢ Zᵢ)³] = 0`. -/
lemma fourthMom_integral_mul_sum_pow_three :
    ∫ ω, η ω * (∑ i ∈ F, x i ω * (B i t ω - B i s ω)) ^ 3 ∂μ = 0 := by
  have hpt : ∀ ω, η ω * (∑ i ∈ F, x i ω * (B i t ω - B i s ω)) ^ 3 =
      ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, (η ω * x i ω * x j ω * x k ω) *
        ((B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω)) := fun ω => by
    rw [fourthMom_sum_pow_three, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hc2 : ∀ i j k, MemLp (fun ω => η ω * x i ω * x j ω * x k ω) 2 μ := fun i j k =>
    ((hη2.fun_mul (r := 2) (hxb i)).fun_mul (r := 2) (hxb j)).fun_mul (r := 2) (hxb k)
  have hW : ∀ i j k, ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun ω => (B i t ω - B i s ω) *
      (B j t ω - B j s ω) * (B k t ω - B k s ω)) p μ := fun i j k =>
    fourthMom_memLp_mul (fourthMom_memLp_mul (hB.fourthMom_memLp_incr i hst)
      (hB.fourthMom_memLp_incr j hst)) (hB.fourthMom_memLp_incr k hst)
  simp_rw [hpt]
  rw [integral_sum₃ F fun i j k => integrable_mul_two (hc2 i j k) (hW i j k 2 (by simp))]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun i _ => ?_
  rw [hB.fourthMom_integral_past_mul hst (((hη.fun_mul (hx i)).fun_mul (hx j)).fun_mul (hx k))
    (((measurable_incrSigma i s t).fun_mul (measurable_incrSigma j s t)).fun_mul
      (measurable_incrSigma k s t)), hB.fourthMom_integral_incr_mul₃ hst i j k, mul_zero]

/-- `𝔼[η (∑ᵢ xᵢ Zᵢ)⁴] = 3 Δ² 𝔼[η (∑ᵢ xᵢ²)²]`. -/
lemma fourthMom_integral_mul_sum_pow_four :
    ∫ ω, η ω * (∑ i ∈ F, x i ω * (B i t ω - B i s ω)) ^ 4 ∂μ =
      3 * ((t : ℝ) - s) ^ 2 * ∫ ω, η ω * (∑ i ∈ F, x i ω ^ 2) ^ 2 ∂μ := by
  classical
  have hpt : ∀ ω, η ω * (∑ i ∈ F, x i ω * (B i t ω - B i s ω)) ^ 4 =
      ∑ l ∈ F, ∑ k ∈ F, ∑ j ∈ F, ∑ i ∈ F, (η ω * x i ω * x j ω * x k ω * x l ω) *
        ((B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) *
          (B l t ω - B l s ω)) := fun ω => by
    rw [fourthMom_sum_pow_four, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hc2 : ∀ i j k l, MemLp (fun ω => η ω * x i ω * x j ω * x k ω * x l ω) 2 μ :=
    fun i j k l => (((hη2.fun_mul (r := 2) (hxb i)).fun_mul (r := 2) (hxb j)).fun_mul (r := 2)
      (hxb k)).fun_mul (r := 2) (hxb l)
  have hW : ∀ i j k l, ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun ω => (B i t ω - B i s ω) *
      (B j t ω - B j s ω) * (B k t ω - B k s ω) * (B l t ω - B l s ω)) p μ := fun i j k l =>
    fourthMom_memLp_mul (fourthMom_memLp_mul (fourthMom_memLp_mul
      (hB.fourthMom_memLp_incr i hst) (hB.fourthMom_memLp_incr j hst))
      (hB.fourthMom_memLp_incr k hst)) (hB.fourthMom_memLp_incr l hst)
  simp_rw [hpt]
  rw [integral_sum₄ F fun i j k l => integrable_mul_two (hc2 i j k l) (hW i j k l 2 (by simp))]
  have hterm : ∀ i j k l, ∫ ω, (η ω * x i ω * x j ω * x k ω * x l ω) *
      ((B i t ω - B i s ω) * (B j t ω - B j s ω) * (B k t ω - B k s ω) *
          (B l t ω - B l s ω)) ∂μ =
      ∫ ω, (η ω * x i ω * x j ω * x k ω * x l ω) * (((t : ℝ) - s) ^ 2 *
        ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0))) ∂μ := by
    intro i j k l
    rw [hB.fourthMom_integral_past_mul hst
      ((((hη.fun_mul (hx i)).fun_mul (hx j)).fun_mul (hx k)).fun_mul (hx l))
      ((((measurable_incrSigma i s t).fun_mul (measurable_incrSigma j s t)).fun_mul
        (measurable_incrSigma k s t)).fun_mul (measurable_incrSigma l s t)),
      hB.fourthMom_integral_incr_mul₄ hst i j k l, integral_mul_const]
  simp_rw [hterm]
  rw [← integral_sum₄ F fun i j k l => ((hc2 i j k l).integrable (by simp)).mul_const _,
    ← integral_const_mul]
  congr 1; funext ω
  rw [show 3 * ((t : ℝ) - s) ^ 2 * (η ω * (∑ i ∈ F, x i ω ^ 2) ^ 2) =
    ((t : ℝ) - s) ^ 2 * (3 * (η ω * (∑ i ∈ F, x i ω ^ 2) ^ 2)) by ring,
    ← sum_isserlis F (fun i => x i ω) (η ω), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

end IsBrownianFamily

end QSSEPtoKPZ
