/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Basic
public import QSSEPtoKPZ.ItoIntegral.GaussMoments
public import QSSEPtoKPZ.ItoIntegral.ElemClip

/-!
# Fourth moment of the Itô integral (package C, task C2)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces, proved by
task C2. See `docs/stage2-design.md`, Section 2.2 ("Fourth moment"), and
`docs/stage2-interfaces.md`.

If `∑ᵢ hᵢ(s)² ≤ K` on `(u, v]`, then `𝔼[(I_v(h) - I_u(h))⁴] ≤ 6 K² (v - u)²` (the sharp constant
is `3`). For elementary integrands, by induction over a common grid with the Gaussian moments
`𝔼 G⁴ = 3 σ⁴`; in general, by Fatou along an almost surely convergent subsequence of clipped
elementary approximations (the radial projection onto the ball of radius `√K` of `ℓ²(ι)` is
`1`-Lipschitz). Used for the quadratic covariation term of the product rule.

Proof (task C2). Elementary case: with `S_r = I_r(e) - I_u(e)` and `s < t` consecutive grid
points, `S_t = S_s + ∑ᵢ xᵢ ΔBᵢ` with `xᵢ` bounded and `𝓖_s`-measurable, so by the conditional
Gaussian moments of `GaussMoments.lean`,
`𝔼 S_t⁴ = 𝔼 S_s⁴ + 6 Δ 𝔼[S_s² σ²] + 3 Δ² 𝔼 σ⁴` and `𝔼 S_t² = 𝔼 S_s² + Δ 𝔼 σ²` (`elem_step`);
induction over the grid gives `𝔼 S_v⁴ ≤ 3 K² (v - u)²` (`elem_moments`). General case: the
clipped fast approximations `elemClip e_k u v K` (`ElemClip.lean`) satisfy the bound, converge
to `h` for the energy on `[0, v]`, hence their increments converge almost surely; Fatou.
The hypothesis `∑' i, hᵢ² ≤ K` is only used through `elemClip_dist_le`, where a non-summable
`(hᵢ(s, ω))ᵢ` makes the energy distance infinite, so no null set has to be removed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-! ### Elementary integrands: one step between grid points -/

omit [Countable ι] in
/-- Powers of a function with moments of all orders. -/
private lemma memLp_pow_all {f : Ω → ℝ} (hf : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ) (n : ℕ) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (fun ω => f ω ^ n) p μ := by
  induction n with
  | zero => intro p _; simpa using memLp_const (1 : ℝ)
  | succ n ih => simpa [pow_succ] using fourthMom_memLp_mul ih hf

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- A function with moments of all orders is integrable. -/
private lemma integrable_of_all {f : Ω → ℝ} (hf : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ) :
    Integrable f μ :=
  memLp_one_iff_integrable.1 (hf 1 ENNReal.one_ne_top)

omit [Countable ι] in
/-- **One step of the recursion.** Let `u ≤ s ≤ t` with no endpoint of `e` in `(s, t)`, and
`σ² = ∑ᵢ eᵢ(t)² ≤ K`. With `S_r = I_r(e) - I_u(e)`:
`𝔼 S_t² ≤ 𝔼 S_s² + (t - s) K` and `𝔼 S_t⁴ ≤ 𝔼 S_s⁴ + 6 (t - s) K 𝔼 S_s² + 3 (t - s)² K²`. -/
private lemma elem_step (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) {u s t : ℝ≥0}
    (hus : u ≤ s) (hst : s ≤ t) (hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p) {K : ℝ}
    (hK : 0 ≤ K) (hσ : ∀ ω, ∑ i ∈ elemGridIdx e, e.toFun i t ω ^ 2 ≤ K) :
    ∫ ω, (e.integral B t ω - e.integral B u ω) ^ 2 ∂μ ≤
        ∫ ω, (e.integral B s ω - e.integral B u ω) ^ 2 ∂μ + ((t : ℝ) - s) * K ∧
      ∫ ω, (e.integral B t ω - e.integral B u ω) ^ 4 ∂μ ≤
        ∫ ω, (e.integral B s ω - e.integral B u ω) ^ 4 ∂μ +
          6 * ((t : ℝ) - s) * K * ∫ ω, (e.integral B s ω - e.integral B u ω) ^ 2 ∂μ +
          3 * ((t : ℝ) - s) ^ 2 * K ^ 2 := by
  set F := elemGridIdx e
  set S : Ω → ℝ := fun ω => e.integral B s ω - e.integral B u ω with hSdef
  set D : Ω → ℝ := fun ω => ∑ i ∈ F, e.toFun i t ω * (B i t ω - B i s ω) with hDdef
  set σ : Ω → ℝ := fun ω => ∑ i ∈ F, e.toFun i t ω ^ 2 with hσdef
  have hSD : ∀ ω, e.integral B t ω - e.integral B u ω = S ω + D ω := fun ω => by
    have := elemGrid_integral_sub hst hno subset_rfl B ω
    simp only [hSdef, hDdef]; linarith
  simp_rw [hSD]
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  -- measurability and integrability
  have hx : ∀ i, Measurable[𝓖 s] (e.toFun i t) := fun i => elemGrid_measurable_toFun hno i
  have hxb : ∀ i, MemLp (e.toFun i t) ∞ μ := fun i =>
    elemGrid_memLp_toFun e ((hx i).mono (𝓖.le s) le_rfl)
  have hxa : ∀ i, ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (e.toFun i t) p μ := fun i p _ =>
    (hxb i).mono_exponent le_top
  have hSm : Measurable[𝓖 s] S :=
    (ElemIntegrand.integral_adapted hB e s).sub
      ((ElemIntegrand.integral_adapted hB e u).mono (𝓖.mono hus) le_rfl)
  have hSa : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp S p μ := fun p hp =>
    (ElemIntegrand.memLp_integral hB e s hp).sub (ElemIntegrand.memLp_integral hB e u hp)
  have hDa : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp D p μ := fun p hp =>
    memLp_finsetSum F fun i _ => fourthMom_memLp_mul (hxa i) (hB.fourthMom_memLp_incr i hst) p hp
  have hσa : ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp σ p μ := fun p hp =>
    memLp_finsetSum F fun i _ => memLp_pow_all (hxa i) 2 p hp
  have h2 : ∀ {f : Ω → ℝ}, (∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ) → MemLp f 2 μ :=
    fun hf => hf 2 (by simp)
  have hσle : ∀ ω, σ ω ≤ K := hσ
  have hσnn : ∀ ω, 0 ≤ σ ω := fun ω => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSm2 : ∀ n : ℕ, Measurable[𝓖 s] (fun ω => S ω ^ n) := fun n => hSm.pow_const n
  have hm1 : Measurable[𝓖 s] (fun _ : Ω => (1 : ℝ)) := measurable_const
  have h1a : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const 1
  -- the conditional moments
  have M1 := hB.fourthMom_integral_mul_sum_pow_one hst F hx hxb (hSm2 3)
    (h2 (memLp_pow_all hSa 3))
  have M2S := hB.fourthMom_integral_mul_sum_pow_two hst F hx hxb (hSm2 2)
    (h2 (memLp_pow_all hSa 2))
  have M21 := hB.fourthMom_integral_mul_sum_pow_two hst F hx hxb hm1 h1a
  have M3 := hB.fourthMom_integral_mul_sum_pow_three hst F hx hxb (hSm2 1)
    (h2 (memLp_pow_all hSa 1))
  have M4 := hB.fourthMom_integral_mul_sum_pow_four hst F hx hxb hm1 h1a
  have M1' := hB.fourthMom_integral_mul_sum_pow_one hst F hx hxb (hSm2 1)
    (h2 (memLp_pow_all hSa 1))
  simp only [one_mul, pow_one] at M1 M2S M21 M3 M4 M1'
  -- integrability of the monomials
  have hI : ∀ m n : ℕ, Integrable (fun ω => S ω ^ m * D ω ^ n) μ := fun m n =>
    integrable_of_all (fourthMom_memLp_mul (memLp_pow_all hSa m) (memLp_pow_all hDa n))
  have hIS : ∀ m : ℕ, Integrable (fun ω => S ω ^ m) μ := fun m =>
    integrable_of_all (memLp_pow_all hSa m)
  have hID : ∀ m : ℕ, Integrable (fun ω => D ω ^ m) μ := fun m =>
    integrable_of_all (memLp_pow_all hDa m)
  -- bounds on the moments of `σ`
  have hσ1 : ∫ ω, σ ω ∂μ ≤ K := by
    calc ∫ ω, σ ω ∂μ ≤ ∫ _, K ∂μ :=
          integral_mono (integrable_of_all hσa) (integrable_const K) hσle
      _ = K := by simp
  have hσ2 : ∫ ω, σ ω ^ 2 ∂μ ≤ K ^ 2 := by
    calc ∫ ω, σ ω ^ 2 ∂μ ≤ ∫ _, K ^ 2 ∂μ :=
          integral_mono (integrable_of_all (memLp_pow_all hσa 2)) (integrable_const _)
            fun ω => pow_le_pow_left₀ (hσnn ω) (hσle ω) 2
      _ = K ^ 2 := by simp
  have hSσ : ∫ ω, S ω ^ 2 * σ ω ∂μ ≤ K * ∫ ω, S ω ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_of_all (fourthMom_memLp_mul (memLp_pow_all hSa 2) hσa))
      ((hIS 2).const_mul K) fun ω => by
        rw [mul_comm K]; exact mul_le_mul_of_nonneg_left (hσle ω) (sq_nonneg _)
  have hts : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hst'
  constructor
  · have e2 : ∫ ω, (S ω + D ω) ^ 2 ∂μ =
        ∫ ω, S ω ^ 2 ∂μ + 2 * ∫ ω, S ω * D ω ∂μ + ∫ ω, D ω ^ 2 ∂μ := by
      have hpt : (fun ω => (S ω + D ω) ^ 2) =
          fun ω => (S ω ^ 2 + 2 * (S ω ^ 1 * D ω ^ 1)) + D ω ^ 2 := by
        funext ω; ring
      rw [hpt, integral_add ((hIS 2).fun_add ((hI 1 1).const_mul 2)) (hID 2),
        integral_add (hIS 2) ((hI 1 1).const_mul 2), integral_const_mul]
      simp only [pow_one]
    rw [e2, M1', M21]
    nlinarith [mul_le_mul_of_nonneg_left hσ1 hts]
  · have e4 : ∫ ω, (S ω + D ω) ^ 4 ∂μ =
        ∫ ω, S ω ^ 4 ∂μ + 4 * ∫ ω, S ω ^ 3 * D ω ∂μ + 6 * ∫ ω, S ω ^ 2 * D ω ^ 2 ∂μ +
          4 * ∫ ω, S ω * D ω ^ 3 ∂μ + ∫ ω, D ω ^ 4 ∂μ := by
      have hpt : (fun ω => (S ω + D ω) ^ 4) =
          fun ω => (((S ω ^ 4 + 4 * (S ω ^ 3 * D ω ^ 1)) + 6 * (S ω ^ 2 * D ω ^ 2)) +
            4 * (S ω ^ 1 * D ω ^ 3)) + D ω ^ 4 := by
        funext ω; ring
      rw [hpt, integral_add ((((hIS 4).fun_add ((hI 3 1).const_mul 4)).fun_add
          ((hI 2 2).const_mul 6)).fun_add ((hI 1 3).const_mul 4)) (hID 4),
        integral_add (((hIS 4).fun_add ((hI 3 1).const_mul 4)).fun_add ((hI 2 2).const_mul 6))
          ((hI 1 3).const_mul 4),
        integral_add ((hIS 4).fun_add ((hI 3 1).const_mul 4)) ((hI 2 2).const_mul 6),
        integral_add (hIS 4) ((hI 3 1).const_mul 4),
        integral_const_mul, integral_const_mul, integral_const_mul]
      simp only [pow_one]
    rw [e4, M1, M2S, M3, M4]
    have hA : 0 ≤ ((t : ℝ) - s) * K := mul_nonneg hts hK
    nlinarith [mul_le_mul_of_nonneg_left hSσ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hts),
      mul_le_mul_of_nonneg_left hσ2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg
        ((t : ℝ) - s)))]

omit [Countable ι] in
/-- **Second and fourth moments of an elementary integral, by induction over the grid.**
If `∑ᵢ eᵢ(r)² ≤ K` for `r ∈ (u, v]`, then `𝔼 (I_v - I_u)² ≤ K (v - u)` and
`𝔼 (I_v - I_u)⁴ ≤ 3 K² (v - u)²`. Induction on the number of endpoints in `(u, v)`: with
`s` the largest of them (or `s = u`), one applies `elem_step` between `s` and `v`. -/
private lemma elem_moments (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) (u : ℝ≥0)
    {K : ℝ} (hK : 0 ≤ K) (n : ℕ) : ∀ v : ℝ≥0, u ≤ v →
    ((elemGridPts e).filter (fun p => u < p ∧ p < v)).card = n →
    (∀ ω (r : ℝ), (u : ℝ) < r → r ≤ v → ∑' i, e.toFun i r ω ^ 2 ≤ K) →
    ∫ ω, (e.integral B v ω - e.integral B u ω) ^ 2 ∂μ ≤ K * ((v : ℝ) - u) ∧
      ∫ ω, (e.integral B v ω - e.integral B u ω) ^ 4 ∂μ ≤ 3 * K ^ 2 * ((v : ℝ) - u) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v huv hcard hbd
  rcases eq_or_lt_of_le huv with rfl | huv'
  · simp
  set Q := (elemGridPts e).filter (fun p => u < p ∧ p < v) with hQ
  -- the last grid point `s` before `v`
  set s : ℝ≥0 := if hne : Q.Nonempty then Q.max' hne else u with hs
  have hus : u ≤ s := by
    rw [hs]; split_ifs with hne
    · exact (Finset.mem_filter.1 (Q.max'_mem hne)).2.1.le
    · exact le_rfl
  have hsv : s < v := by
    rw [hs]; split_ifs with hne
    · exact (Finset.mem_filter.1 (Q.max'_mem hne)).2.2
    · exact huv'
  have hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ v ≤ p := by
    intro p hp
    by_cases h1 : p ≤ u
    · exact Or.inl (h1.trans hus)
    by_cases h2 : v ≤ p
    · exact Or.inr h2
    have hpQ : p ∈ Q := Finset.mem_filter.2 ⟨hp, lt_of_not_ge h1, lt_of_not_ge h2⟩
    left
    have hne : Q.Nonempty := ⟨p, hpQ⟩
    simp only [hs, hne, ↓reduceDIte]
    exact Q.le_max' p hpQ
  -- the bounds at `s`
  have hbd_s : ∀ ω (r : ℝ), (u : ℝ) < r → r ≤ s → ∑' i, e.toFun i r ω ^ 2 ≤ K :=
    fun ω r h1 h2 => hbd ω r h1 (h2.trans (NNReal.coe_le_coe.2 hsv.le))
  have hIH : ∫ ω, (e.integral B s ω - e.integral B u ω) ^ 2 ∂μ ≤ K * ((s : ℝ) - u) ∧
      ∫ ω, (e.integral B s ω - e.integral B u ω) ^ 4 ∂μ ≤ 3 * K ^ 2 * ((s : ℝ) - u) ^ 2 := by
    by_cases hne : Q.Nonempty
    · have hsQ : s ∈ Q := by simp only [hs, hne, ↓reduceDIte]; exact Q.max'_mem hne
      refine ih _ ?_ s hus rfl hbd_s
      rw [← hcard]
      have hsub : (elemGridPts e).filter (fun p => u < p ∧ p < s) ⊆ Q := fun p hp => by
        simp only [hQ, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, hp.2.2.trans hsv⟩
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨s, hsQ, fun h => ?_⟩)
      simp only [Finset.mem_filter] at h
      exact lt_irrefl _ h.2.2
    · have : s = u := by simp only [hs, hne, ↓reduceDIte]
      rw [this]; simp
  -- the bound on `σ² = ∑ᵢ eᵢ(v)²`
  have hσ : ∀ ω, ∑ i ∈ elemGridIdx e, e.toFun i v ω ^ 2 ≤ K := by
    intro ω
    have h := hbd ω v (NNReal.coe_lt_coe.2 huv') le_rfl
    rwa [tsum_eq_sum (s := elemGridIdx e) (fun i hi => by
      rw [elemGrid_toFun_eq_zero e hi]; ring)] at h
  obtain ⟨h2, h4⟩ := elem_step hB e hus hsv.le hno hK hσ
  have hsu : 0 ≤ (s : ℝ) - u := sub_nonneg.2 (NNReal.coe_le_coe.2 hus)
  have hvs : 0 ≤ (v : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hsv.le)
  constructor
  · nlinarith [hIH.1]
  · have hA : 0 ≤ 6 * ((v : ℝ) - s) * K := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hIH.1 hA, hIH.2]

set_option linter.unusedSectionVars false in
/-- **Fourth moment, elementary integrands.** If `∑ᵢ eᵢ(s, ω)² ≤ K` for `s ∈ (u, v]` and all
`ω`, then `𝔼[(I_v(e) - I_u(e))⁴] ≤ 6 K² (v - u)²`. -/
theorem lintegral_elem_integral_sub_pow_four_le (hB : IsBrownianFamily 𝓖 B μ)
    (e : ElemIntegrand 𝓖 ι) {u v : ℝ≥0} (huv : u ≤ v) {K : ℝ}
    (hbd : ∀ ω (s : ℝ), (u : ℝ) < s → s ≤ v → ∑' i, e.toFun i s ω ^ 2 ≤ K) :
    ∫⁻ ω, ENNReal.ofReal ((e.integral B v ω - e.integral B u ω) ^ 4) ∂μ ≤
      ENNReal.ofReal (6 * K ^ 2 * ((v : ℝ) - u) ^ 2) := by
  rcases eq_or_lt_of_le huv with rfl | huv'
  · simp
  have hK : 0 ≤ K := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
    exact (tsum_nonneg fun i => sq_nonneg _).trans
      (hbd ω v (NNReal.coe_lt_coe.2 huv') le_rfl)
  have h4 := (elem_moments hB e u hK _ v huv rfl fun ω r h1 h2 => hbd ω r h1 h2).2
  have hint : Integrable (fun ω => (e.integral B v ω - e.integral B u ω) ^ 4) μ :=
    memLp_one_iff_integrable.1 (memLp_pow_all (fun p hp =>
      (ElemIntegrand.memLp_integral hB e v hp).sub (ElemIntegrand.memLp_integral hB e u hp))
      4 1 ENNReal.one_ne_top)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)]
  have h36 : 3 * K ^ 2 * ((v : ℝ) - u) ^ 2 ≤ 6 * K ^ 2 * ((v : ℝ) - u) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg ((v : ℝ) - u))]
  exact ENNReal.ofReal_le_ofReal (h4.trans h36)

/-! ### Passage to the limit -/

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- The energy on `[0, T]` is nondecreasing in `T`. -/
private lemma energy_mono_time (g : ι → ℝ → Ω → ℝ) {T T' : ℝ} (hT : T ≤ T') :
    energy μ g T ≤ energy μ g T' :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Ioc_subset_Ioc_right hT)

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- Clipping `e` on `(u, v]` does not increase its energy distance on `[0, v]` to an
integrand `h` with `∑ᵢ hᵢ² ≤ K` on `(u, v]`. -/
private lemma energy_elemClip_sub_le (e : ElemIntegrand 𝓖 ι) {h : ι → ℝ → Ω → ℝ}
    {u v : ℝ≥0} {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ ω (s : ℝ), (u : ℝ) < s → s ≤ v → ∑' i, h i s ω ^ 2 ≤ K) :
    energy μ (fun i s ω => (elemClip e u v K).toFun i s ω - h i s ω) v ≤
      energy μ (fun i s ω => e.toFun i s ω - h i s ω) v := by
  refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  by_cases hus : (u : ℝ) < s
  · exact elemClip_dist_le e u v hK hus hs.2 ω (fun i => h i s ω) fun _ => hbd ω s hus hs.2
  · simp only [elemClip_toFun, hus, false_and, ite_false]
    exact le_rfl

/-- `𝔼[((I_v(ē) - I_u(ē)) - (I_v(h) - I_u(h)))²] ≤ 4 energy(ē - h, v)`, by the isometry
applied to `ē - h`. -/
private lemma lintegral_elem_sub_stochInt_sq_le (hB : IsBrownianFamily 𝓖 B μ)
    (e : ElemIntegrand 𝓖 ι) {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) {u v : ℝ≥0}
    (huv : u ≤ v) :
    ∫⁻ ω, ENNReal.ofReal (((e.integral B v ω - e.integral B u ω) -
        (stochInt 𝓖 μ B h v ω - stochInt 𝓖 μ B h u ω)) ^ 2) ∂μ ≤
      4 * energy μ (fun i s ω => e.toFun i s ω - h i s ω) v := by
  set g : ι → ℝ → Ω → ℝ := fun i s ω => e.toFun i s ω - h i s ω with hgdef
  have hfun : (fun i s ω => e.toFun i s ω + -1 * h i s ω) = g := by
    funext i s ω; rw [hgdef]; ring
  have hg : IsItoIntegrable 𝓖 μ g := by
    rw [← hfun]; exact (isItoIntegrable_elem e).add (hh.const_mul (-1))
  have h1 := stochInt_add hB (isItoIntegrable_elem e) (hh.const_mul (-1))
  rw [hfun] at h1
  have h2 := stochInt_const_mul hB hh (-1)
  have h3 := stochInt_elem hB e
  have hae : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      stochInt 𝓖 μ B g t ω = e.integral B t ω - stochInt 𝓖 μ B h t ω := by
    filter_upwards [h1, h2, h3] with ω h1 h2 h3 t
    rw [h1 t, h2 t, h3 t]; ring
  have hmeas : ∀ t : ℝ≥0, Measurable fun ω => ENNReal.ofReal (stochInt 𝓖 μ B g t ω ^ 2) :=
    fun t => ENNReal.measurable_ofReal.comp
      (((stochInt_adapted hB g t).mono (𝓖.le t) le_rfl).pow_const 2)
  calc ∫⁻ ω, ENNReal.ofReal (((e.integral B v ω - e.integral B u ω) -
        (stochInt 𝓖 μ B h v ω - stochInt 𝓖 μ B h u ω)) ^ 2) ∂μ
      = ∫⁻ ω, ENNReal.ofReal ((stochInt 𝓖 μ B g v ω - stochInt 𝓖 μ B g u ω) ^ 2) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω hω
        rw [hω v, hω u]; ring_nf
    _ ≤ ∫⁻ ω, (2 * ENNReal.ofReal (stochInt 𝓖 μ B g v ω ^ 2) +
          2 * ENNReal.ofReal (stochInt 𝓖 μ B g u ω ^ 2)) ∂μ := by
        refine lintegral_mono fun ω => ?_
        set a := stochInt 𝓖 μ B g v ω
        set b := stochInt 𝓖 μ B g u ω
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a + b)])
    _ = 2 * energy μ g v + 2 * energy μ g u := by
        rw [lintegral_add_left ((hmeas v).const_mul 2), lintegral_const_mul _ (hmeas v),
          lintegral_const_mul _ (hmeas u), lintegral_stochInt_sq hB hg,
          lintegral_stochInt_sq hB hg]
    _ ≤ 2 * energy μ g v + 2 * energy μ g v := by
        gcongr; exact energy_mono_time g (NNReal.coe_le_coe.2 huv)
    _ = 4 * energy μ g v := by rw [← add_mul]; norm_num

/-- **Fourth moment of the Itô integral.** If `h` is Itô-integrable and `∑ᵢ hᵢ(s, ω)² ≤ K` for
`s ∈ (u, v]` and all `ω`, then `𝔼[(I_v(h) - I_u(h))⁴] ≤ 6 K² (v - u)²`. (Where the series
diverges the hypothesis says nothing, Lean's `tsum` being `0`; this happens only on a
`ds ⊗ dℙ`-null set, since the energy of `h` is finite.) -/
theorem lintegral_stochInt_sub_pow_four_le (hB : IsBrownianFamily 𝓖 B μ)
    {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) {u v : ℝ≥0} (huv : u ≤ v) {K : ℝ}
    (hbd : ∀ ω (s : ℝ), (u : ℝ) < s → s ≤ v → ∑' i, h i s ω ^ 2 ≤ K) :
    ∫⁻ ω, ENNReal.ofReal ((stochInt 𝓖 μ B h v ω - stochInt 𝓖 μ B h u ω) ^ 4) ∂μ ≤
      ENNReal.ofReal (6 * K ^ 2 * ((v : ℝ) - u) ^ 2) := by
  rcases eq_or_lt_of_le huv with rfl | huv'
  · simp
  have hK : 0 ≤ K := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
    exact (tsum_nonneg fun i => sq_nonneg _).trans
      (hbd ω v (NNReal.coe_lt_coe.2 huv') le_rfl)
  obtain ⟨e, he⟩ := hh.exists_fast
  set N : ℕ := ⌈(v : ℝ)⌉₊
  -- the clipped fast approximations and their increments
  set E : ℕ → ElemIntegrand 𝓖 ι := fun k => elemClip (e (k + N)) u v K with hE
  set X : Ω → ℝ := fun ω => stochInt 𝓖 μ B h v ω - stochInt 𝓖 μ B h u ω with hX
  set Y : ℕ → Ω → ℝ := fun k ω => (E k).integral B v ω - (E k).integral B u ω with hY
  -- `𝔼 (Y_k - X)² ≤ 4 ⬝ 8⁻ᵏ`
  have hL2 : ∀ k, ∫⁻ ω, ENNReal.ofReal ((Y k ω - X ω) ^ 2) ∂μ ≤ 4 * (8 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    refine (lintegral_elem_sub_stochInt_sq_le hB (E k) hh huv).trans ?_
    gcongr
    calc energy μ (fun i s ω => (E k).toFun i s ω - h i s ω) v
        ≤ energy μ (fun i s ω => (e (k + N)).toFun i s ω - h i s ω) v :=
          energy_elemClip_sub_le (e (k + N)) hK hbd
      _ ≤ energy μ (fun i s ω => (e (k + N)).toFun i s ω - h i s ω) ((k + N : ℕ) : ℝ) :=
          energy_mono_time _ (by
            have := Nat.le_ceil (v : ℝ); push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      _ ≤ (8 : ℝ≥0∞)⁻¹ ^ (k + N) := he (k + N)
      _ ≤ (8 : ℝ≥0∞)⁻¹ ^ k := pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_add_right k N)
  -- measurability
  have hXm : Measurable X :=
    ((stochInt_adapted hB h v).mono (𝓖.le v) le_rfl).sub
      ((stochInt_adapted hB h u).mono (𝓖.le u) le_rfl)
  have hYm : ∀ k, Measurable (Y k) := fun k =>
    ((ElemIntegrand.integral_adapted hB (E k) v).mono (𝓖.le v) le_rfl).sub
      ((ElemIntegrand.integral_adapted hB (E k) u).mono (𝓖.le u) le_rfl)
  -- almost sure convergence `Y_k → X`
  have hfm : ∀ k, Measurable (fun ω => ENNReal.ofReal ((Y k ω - X ω) ^ 2)) := fun k =>
    ENNReal.measurable_ofReal.comp (((hYm k).sub hXm).pow_const 2)
  have hsum : ∫⁻ ω, ∑' k, ENNReal.ofReal ((Y k ω - X ω) ^ 2) ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => (hfm k).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hL2)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.2 (by
      rw [ne_eq, tsub_eq_zero_iff_le, not_le]
      exact ENNReal.inv_lt_one.2 (by norm_num)))
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun k => Y k ω) atTop (𝓝 (X ω)) := by
    filter_upwards [ae_lt_top' (Measurable.tsum hfm).aemeasurable hsum] with ω hω
    have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
    have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0)
    simp only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_zero] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using h2
  -- Fatou
  have hlim : ∀ᵐ ω ∂μ, ENNReal.ofReal (X ω ^ 4) =
      liminf (fun k => ENNReal.ofReal (Y k ω ^ 4)) atTop := by
    filter_upwards [hae] with ω hω
    exact (((ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_pow 4).tendsto _ |>.comp hω)).liminf_eq).symm
  calc ∫⁻ ω, ENNReal.ofReal ((stochInt 𝓖 μ B h v ω - stochInt 𝓖 μ B h u ω) ^ 4) ∂μ
      = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (Y k ω ^ 4)) atTop ∂μ := lintegral_congr_ae hlim
    _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (Y k ω ^ 4) ∂μ) atTop :=
        lintegral_liminf_le' fun k =>
          (ENNReal.measurable_ofReal.comp ((hYm k).pow_const 4)).aemeasurable
    _ ≤ ENNReal.ofReal (6 * K ^ 2 * ((v : ℝ) - u) ^ 2) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun k =>
          lintegral_elem_integral_sub_pow_four_le hB (E k) huv fun ω s hus hsv =>
            elemClip_sq_le _ u v hK hus hsv ω)

end QSSEPtoKPZ
