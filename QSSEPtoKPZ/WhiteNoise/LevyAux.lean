/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Stopping
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Lévy's characterization: auxiliary results (task G7a)

* Increments of a martingale against the past: `∫ η (M_{r'} - M_r) = 0` for `η ∈ L²`
  measurable for `𝓕_r` (`IsCL2Mart.levy_integral_mul_incr`), and
  `∫ ξ ((M_{r'} - M_r)² - (A_{r'} - A_r)) = 0` for bounded `ξ` measurable for `𝓕_r`
  (`HasBracket.levy_integral_mul_incr_sq`); complex versions for bounded complex `ξ`.
* The third-order Taylor bound for `exp (i u x + β)` (`levy_norm_exp_sub_le`).
* The points `t_k = s + k (t - s) / n` of the uniform partition of `[s, t]` (`levyPt`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Increments against the past -/

/-- Pull-out property, integrated: if `𝔼[Y' | m] = Y` and `η` is `m`-measurable with `η Y'`
integrable, then `∫ η Y' = ∫ η Y`. -/
theorem levy_integral_mul_eq_of_condExp [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {η Y Y' : Ω → ℝ} (hη : AEStronglyMeasurable[m] η μ) (hY' : Integrable Y' μ)
    (hηY' : Integrable (fun ω => η ω * Y' ω) μ) (hc : μ[Y' | m] =ᵐ[μ] Y) :
    ∫ ω, η ω * Y' ω ∂μ = ∫ ω, η ω * Y ω ∂μ := by
  rw [← integral_condExp hm]
  refine integral_congr_ae ?_
  filter_upwards [condExp_mul_of_aestronglyMeasurable_left hη hηY' hY', hc] with ω h1 h2
  change μ[η * Y' | m] ω = _
  rw [h1, Pi.mul_apply, h2]

/-- **Martingale increments are orthogonal to the past**: if `M` is a continuous `L²`
martingale on `[0, T]`, `r ≤ r' ≤ T` and `η ∈ L²` is `𝓕_r`-measurable, then
`∫ η (M_{r'} - M_r) = 0`. -/
theorem IsCL2Mart.levy_integral_mul_incr [IsFiniteMeasure μ] {T : ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {M : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M μ) {r r' : ℝ≥0} (hrr' : r ≤ r') (hr'T : (r' : ℝ) ≤ T)
    {η : Ω → ℝ} (hη : AEStronglyMeasurable[𝓕 r] η μ) (hη2 : MemLp η 2 μ) :
    ∫ ω, η ω * (M r' ω - M r ω) ∂μ = 0 := by
  have hrT : (r : ℝ) ≤ T := (NNReal.coe_le_coe.2 hrr').trans hr'T
  have h1 : Integrable (fun ω => η ω * M r' ω) μ := hη2.integrable_mul (hM.memLp r' hr'T)
  have h2 : Integrable (fun ω => η ω * M r ω) μ := hη2.integrable_mul (hM.memLp r hrT)
  simp_rw [mul_sub]
  rw [integral_sub h1 h2, levy_integral_mul_eq_of_condExp (𝓕.le r) hη
    ((hM.memLp r' hr'T).integrable one_le_two) h1 (hM.condExp r r' hrr' hr'T), sub_self]

/-- **Bracket increments are orthogonal to the past**: if `⟨M⟩ = A` on `[0, T]`, `r ≤ r' ≤ T`
and `ξ` is bounded and `𝓕_r`-measurable, then `∫ ξ ((M_{r'} - M_r)² - (A_{r'} - A_r)) = 0`. -/
theorem HasBracket.levy_integral_mul_incr_sq [IsFiniteMeasure μ] {T : ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ) {r r' : ℝ≥0}
    (hrr' : r ≤ r') (hr'T : (r' : ℝ) ≤ T) {ξ : Ω → ℝ} (hξ : AEStronglyMeasurable[𝓕 r] ξ μ)
    {K : ℝ} (hK : ∀ ω, |ξ ω| ≤ K) :
    ∫ ω, ξ ω * ((M r' ω - M r ω) ^ 2 - (A r' ω - A r ω)) ∂μ = 0 := by
  have hrT : (r : ℝ) ≤ T := (NNReal.coe_le_coe.2 hrr').trans hr'T
  have hξm : AEStronglyMeasurable ξ μ := hξ.mono (𝓕.le r)
  have hKa : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ K := ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (hK ω)
  have hX : ∀ v : ℝ≥0, (v : ℝ) ≤ T → Integrable (fun ω => M v ω ^ 2 - A v ω) μ := fun v hv =>
    (h.memLp v hv).integrable_sq.sub (h.integrable_bracket v hv)
  have hξX : ∀ v : ℝ≥0, (v : ℝ) ≤ T → Integrable (fun ω => ξ ω * (M v ω ^ 2 - A v ω)) μ :=
    fun v hv => (hX v hv).bdd_mul hξm hKa
  -- the product `ξ M_r` is in `L²` and `𝓕_r`-measurable
  have hMr : AEStronglyMeasurable[𝓕 r] (M r) μ :=
    aestronglyMeasurable_of_condExp_eq_self (h.condExp r r le_rfl hrT)
  have hξ2 : MemLp (fun ω => ξ ω * M r ω) 2 μ := by
    have hξt : MemLp ξ ∞ μ := memLp_top_of_bound hξm K hKa
    exact hξt.mul (h.memLp r hrT)
  have hP1 := h.toIsCL2Mart.levy_integral_mul_incr hrr' hr'T (hξ.mul hMr) hξ2
  have e : ∀ ω, ξ ω * ((M r' ω - M r ω) ^ 2 - (A r' ω - A r ω)) =
      ξ ω * (M r' ω ^ 2 - A r' ω) - ξ ω * (M r ω ^ 2 - A r ω) -
        2 * ((ξ ω * M r ω) * (M r' ω - M r ω)) := fun ω => by ring
  simp_rw [e]
  have hi3 : Integrable (fun ω => (ξ ω * M r ω) * (M r' ω - M r ω)) μ :=
    hξ2.integrable_mul ((h.memLp r' hr'T).sub (h.memLp r hrT))
  have i1 := integral_sub ((hξX r' hr'T).sub (hξX r hrT)) (hi3.const_mul 2)
  have i2 := integral_sub (hξX r' hr'T) (hξX r hrT)
  simp only [Pi.sub_apply, Pi.mul_apply] at i1 i2 hP1
  rw [i1, i2, integral_const_mul, hP1,
    levy_integral_mul_eq_of_condExp (𝓕.le r) hξ (hX r' hr'T) (hξX r' hr'T)
      (h.condExp_sq r r' hrr' hr'T)]
  ring

/-- Complex form of an orthogonality relation: if `∫ η g = 0` for every real `𝓕_r`-measurable `η`
bounded by `K`, then `∫ ξ g = 0` for every complex `𝓕_r`-measurable `ξ` bounded by `K` (apply
it to the real and imaginary parts). -/
theorem levy_integral_complex_of_real {𝓕 : Filtration ℝ≥0 mΩ} {r : ℝ≥0} {g : Ω → ℝ}
    (hg : Integrable g μ) {ξ : Ω → ℂ} (hξ : AEStronglyMeasurable[𝓕 r] ξ μ) {K : ℝ}
    (hK : ∀ ω, ‖ξ ω‖ ≤ K)
    (h : ∀ η : Ω → ℝ, AEStronglyMeasurable[𝓕 r] η μ → (∀ ω, |η ω| ≤ K) →
      ∫ ω, η ω * g ω ∂μ = 0) :
    ∫ ω, ξ ω * (g ω : ℂ) ∂μ = 0 := by
  have hI : Integrable (fun ω => ξ ω * (g ω : ℂ)) μ :=
    hg.ofReal.bdd_mul (hξ.mono (𝓕.le r)) (ae_of_all _ hK)
  apply Complex.ext
  · have e := Complex.reCLM.integral_comp_comm hI
    simp only [Complex.reCLM_apply] at e
    rw [← e, Complex.zero_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact h _ (Complex.continuous_re.comp_aestronglyMeasurable (m := 𝓕 r) hξ)
      fun ω => (Complex.abs_re_le_norm _).trans (hK ω)
  · have e := Complex.imCLM.integral_comp_comm hI
    simp only [Complex.imCLM_apply] at e
    rw [← e, Complex.zero_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    exact h _ (Complex.continuous_im.comp_aestronglyMeasurable (m := 𝓕 r) hξ)
      fun ω => (Complex.abs_im_le_norm _).trans (hK ω)

/-- Complex version of `IsCL2Mart.levy_integral_mul_incr`, for a bounded `𝓕_r`-measurable
`ξ`. -/
theorem IsCL2Mart.levy_integral_mul_incr_complex [IsFiniteMeasure μ] {T : ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M μ) {r r' : ℝ≥0}
    (hrr' : r ≤ r') (hr'T : (r' : ℝ) ≤ T) {ξ : Ω → ℂ} (hξ : AEStronglyMeasurable[𝓕 r] ξ μ)
    {K : ℝ} (hK : ∀ ω, ‖ξ ω‖ ≤ K) :
    ∫ ω, ξ ω * ((M r' ω - M r ω : ℝ) : ℂ) ∂μ = 0 := by
  have hrT : (r : ℝ) ≤ T := (NNReal.coe_le_coe.2 hrr').trans hr'T
  refine levy_integral_complex_of_real
    (((hM.memLp r' hr'T).sub (hM.memLp r hrT)).integrable one_le_two) hξ hK
    fun η hη hηK => hM.levy_integral_mul_incr hrr' hr'T hη ?_
  exact memLp_of_bounded (a := -K) (b := K) (ae_of_all _ fun ω => abs_le.1 (hηK ω))
    (hη.mono (𝓕.le r)) 2

/-- Complex version of `HasBracket.levy_integral_mul_incr_sq`. -/
theorem HasBracket.levy_integral_mul_incr_sq_complex [IsFiniteMeasure μ] {T : ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ) {r r' : ℝ≥0}
    (hrr' : r ≤ r') (hr'T : (r' : ℝ) ≤ T) {ξ : Ω → ℂ} (hξ : AEStronglyMeasurable[𝓕 r] ξ μ)
    {K : ℝ} (hK : ∀ ω, ‖ξ ω‖ ≤ K) :
    ∫ ω, ξ ω * (((M r' ω - M r ω) ^ 2 - (A r' ω - A r ω) : ℝ) : ℂ) ∂μ = 0 := by
  have hrT : (r : ℝ) ≤ T := (NNReal.coe_le_coe.2 hrr').trans hr'T
  refine levy_integral_complex_of_real ?_ hξ hK
    fun η hη hηK => h.levy_integral_mul_incr_sq hrr' hr'T hη hηK
  exact (((h.memLp r' hr'T).sub (h.memLp r hrT)).integrable_sq).sub
    ((h.integrable_bracket r' hr'T).sub (h.integrable_bracket r hrT))

/-! ### Taylor expansion of `exp (i y + β)` -/

/-- Third-order Taylor bound: for real `y`, `β`,
`|e^{iy + β} - 1 - iy - (β - y²/2)| ≤ |y| |β| + β²/2 + (|y| + |β|)³ e^{|y| + |β|}`. -/
theorem levy_norm_exp_sub_le (y β : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I + (β : ℂ)) - 1 - (y : ℂ) * Complex.I -
        ((β - y ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      |y| * |β| + β ^ 2 / 2 + (|y| + |β|) ^ 3 * Real.exp (|y| + |β|) := by
  set w : ℂ := (y : ℂ) * Complex.I + (β : ℂ) with hw
  have hE := Complex.norm_exp_sub_sum_le_norm_mul_exp w 3
  have hs : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hE
  have hwn : ‖w‖ ≤ |y| + |β| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have key : Complex.exp w - 1 - (y : ℂ) * Complex.I - ((β - y ^ 2 / 2 : ℝ) : ℂ) =
      (Complex.exp w - (1 + w + w ^ 2 / 2)) + ((y * β : ℝ) : ℂ) * Complex.I +
        ((β ^ 2 / 2 : ℝ) : ℂ) := by
    rw [hw]; push_cast
    linear_combination ((y : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [key]
  have h1 : ‖Complex.exp w - (1 + w + w ^ 2 / 2)‖ ≤ (|y| + |β|) ^ 3 * Real.exp (|y| + |β|) :=
    hE.trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwn 3) (Real.exp_le_exp.2 hwn)
      (Real.exp_pos _).le (by positivity))
  have h2 : ‖((y * β : ℝ) : ℂ) * Complex.I‖ = |y| * |β| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h3 : ‖((β ^ 2 / 2 : ℝ) : ℂ)‖ = β ^ 2 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ ‖Complex.exp w - (1 + w + w ^ 2 / 2)‖ + ‖((y * β : ℝ) : ℂ) * Complex.I‖ +
        ‖((β ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add₃_le
    _ ≤ _ := by rw [h2, h3]; linarith

/-! ### Bounded functions -/

/-- `f` is bounded: `|f| ≤ C` everywhere, for some `C` (a `fun_prop` predicate, used for
integrability of the many bounded random variables of the discretization). -/
@[fun_prop] def LevyBdd {α : Type*} (f : α → ℝ) : Prop := ∃ C, ∀ x, |f x| ≤ C

section LevyBdd

variable {α : Type*}

/-- Constants are bounded. -/
@[fun_prop] lemma levyBdd_const (c : ℝ) : LevyBdd (fun _ : α => c) := ⟨|c|, fun _ => le_rfl⟩

/-- Sums of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.add {f g : α → ℝ} (hf : LevyBdd f) (hg : LevyBdd g) :
    LevyBdd (fun x => f x + g x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

/-- Products of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.mul {f g : α → ℝ} (hf : LevyBdd f) (hg : LevyBdd g) :
    LevyBdd (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  exact ⟨C * D, fun x => by
    rw [abs_mul]; exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))⟩

/-- Opposites of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.neg {f : α → ℝ} (hf : LevyBdd f) : LevyBdd (fun x => -f x) := by
  obtain ⟨C, hC⟩ := hf; exact ⟨C, fun x => by rw [abs_neg]; exact hC x⟩

/-- Differences of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.sub {f g : α → ℝ} (hf : LevyBdd f) (hg : LevyBdd g) :
    LevyBdd (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Powers of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.pow {f : α → ℝ} (hf : LevyBdd f) (k : ℕ) :
    LevyBdd (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using levyBdd_const (α := α) 1
  | succ k ih => simpa [pow_succ] using ih.mul hf

/-- Absolute values of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.abs {f : α → ℝ} (hf : LevyBdd f) : LevyBdd (fun x => |f x|) := by
  obtain ⟨C, hC⟩ := hf; exact ⟨C, fun x => by rw [abs_abs]; exact hC x⟩

/-- Finite sums of bounded functions are bounded. -/
@[fun_prop] lemma LevyBdd.sum {ι : Type*} (s : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ s, LevyBdd (f i)) : LevyBdd (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using levyBdd_const (α := α) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

/-- A function bounded by `C` is bounded. -/
lemma levyBdd_of_le {f : α → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) : LevyBdd f := ⟨C, h⟩

variable {mα : MeasurableSpace α} {ν : Measure α}

/-- A bounded, almost everywhere strongly measurable function is in every `Lᵖ` (finite
measure). -/
lemma LevyBdd.memLp [IsFiniteMeasure ν] {f : α → ℝ} (hf : LevyBdd f)
    (hm : AEStronglyMeasurable f ν) (p : ℝ≥0∞) : MemLp f p ν := by
  obtain ⟨C, hC⟩ := hf
  exact memLp_of_bounded (a := -C) (b := C) (ae_of_all _ fun x => abs_le.1 (hC x)) hm p

/-- A bounded, almost everywhere strongly measurable function is integrable (finite
measure). -/
lemma LevyBdd.integrable [IsFiniteMeasure ν] {f : α → ℝ} (hf : LevyBdd f)
    (hm : AEStronglyMeasurable f ν) : Integrable f ν :=
  memLp_one_iff_integrable.1 (hf.memLp hm 1)

end LevyBdd

/-- The maximum of finitely many almost everywhere strongly measurable real functions is almost
everywhere strongly measurable. -/
lemma levy_aestronglyMeasurable_sup' {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ k, AEStronglyMeasurable (f k) ν) (n : ℕ) :
    AEStronglyMeasurable
      (fun x => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k x) ν := by
  refine (AEMeasurable.aestronglyMeasurable ?_)
  refine ⟨fun x => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => (hf k).mk (f k) x,
    Finset.measurable_range_sup'' fun k _ => (hf k).stronglyMeasurable_mk.measurable, ?_⟩
  filter_upwards [ae_all_iff.2 fun k => (hf k).ae_eq_mk] with x hx
  exact Finset.sup'_congr _ rfl fun k _ => hx k

/-! ### The uniform partition of `[s, t]` -/

/-- The point `t_k = s + (k ∧ n) (t - s) / n` of the uniform partition of `[s, t]` into `n`
pieces (frozen at `t` for `k ≥ n`). -/
def levyPt (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := s + ((min k n : ℕ) : ℝ≥0) * ((t - s) / n)

/-- `t_0 = s`. -/
lemma levyPt_zero (s t : ℝ≥0) (n : ℕ) : levyPt s t n 0 = s := by simp [levyPt]

/-- `s ≤ t_k`. -/
lemma le_levyPt (s t : ℝ≥0) (n k : ℕ) : s ≤ levyPt s t n k := le_self_add

/-- `k ↦ t_k` is nondecreasing. -/
lemma levyPt_mono (s t : ℝ≥0) (n : ℕ) : Monotone (levyPt s t n) := fun a b hab => by
  unfold levyPt
  gcongr

/-- `t_k = t` for `k ≥ n ≥ 1`. -/
lemma levyPt_of_le {s t : ℝ≥0} (hst : s ≤ t) {n k : ℕ} (hn : n ≠ 0) (hk : n ≤ k) :
    levyPt s t n k = t := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  rw [levyPt, min_eq_right hk, mul_div_cancel₀ _ hn', add_tsub_cancel_of_le hst]

/-- `t_k ≤ t`. -/
lemma levyPt_le {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) : levyPt s t n k ≤ t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [levyPt, hst]
  · calc levyPt s t n k ≤ levyPt s t n n := by
          unfold levyPt; rw [min_self]; gcongr; exact min_le_right k n
      _ = t := levyPt_of_le hst hn.ne' le_rfl

/-- `t_k` as a real number, for `k ≤ n`. -/
lemma coe_levyPt {s t : ℝ≥0} (hst : s ≤ t) {n k : ℕ} (hk : k ≤ n) :
    (levyPt s t n k : ℝ) = s + k * ((t - s) / n) := by
  simp [levyPt, min_eq_left hk, NNReal.coe_sub hst]

/-- The mesh: `t_{k+1} - t_k = (t - s) / n` for `k < n`. -/
lemma levyPt_succ_sub {s t : ℝ≥0} (hst : s ≤ t) {n k : ℕ} (hk : k < n) :
    (levyPt s t n (k + 1) : ℝ) - levyPt s t n k = (t - s) / n := by
  rw [coe_levyPt hst hk, coe_levyPt hst hk.le]; push_cast; ring

end QSSEPtoKPZ
