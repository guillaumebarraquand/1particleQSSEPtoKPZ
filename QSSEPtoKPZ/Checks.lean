/-
Formal statement of the main theorem of
  G. Barraquand, "Convergence of the one-particle quantum symmetric simple exclusion process
  to the KPZ equation" (2026).
Lean 4 / Mathlib formalization written by Claude (Anthropic) at the request of the author,
November 2026. See README.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance

/-!
# Checks of the definitions

The statement of the main theorem is only as good as the definitions on which it relies. This
file contains lemmas, with complete proofs, which test these definitions: each of them would
fail if the corresponding definition had a wrong normalization, a wrong sign, an off-by-one
error, or if Lean's conventions for partial operations made it degenerate.

* The lattice and the size of the system: `box_top`, `mem_box_natCast`, `degree_top`,
  `degree_natCast`, `tendsto_size_iff`, `tendsto_size_top`.
* Riemann sums: `itoSum_const`.
* Brownian motions: `IsBrownianFamily.isBrownianReal` (each member of a Brownian family is a
  Brownian motion in the sense of Mathlib), `integral_normSq_complexBM` (`𝔼|W_t|² = t`).
* The rescaling and the initial condition: `rescaledPosition_spec`, `rescaledField_eq`,
  `rescaledMeasure_zero`, `IsWaveFunction.initial` (`ψ_0 = e₀`),
  `IsWaveFunction.rescaledMeasure_zero` (`𝒵ₙ(0) = δ₀` almost surely).
* The white noise: `isWalshIntegral_rect`, `integral_sq_rectMass`,
  `IsWhiteNoise.isPreBrownianReal` (the mass of `(0,t] × (a,a+1]` is a Brownian motion in `t`),
  `IsWalshIntegral.memLp_and_integral_eq_zero` (stochastic integrals are centered and square
  integrable).
* The heat kernel and the limit: `heatKernel_eq_gaussianPDFReal`, `sheMeasure_heatKernel`,
  `sheMeasure_zero`, `integral_sheMeasure` (`𝒵(t)` has density `max(Z(t,x), 0)`),
  `integral_sheMeasure_of_nonneg`, `IsMildSolution.integral_eq_heatKernel` (`𝔼[Z(t,x)] = g_t(x)`).
* Convergence in `C([0,T], ℳ₊(ℝ))` implies the convergence in distribution of the integrals of
  bounded continuous functions at a fixed time: `tendstoInDistribution_integral`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The lattice -/

/-- `Λ_∞ = ℤ`. -/
@[simp] lemma box_top : box ⊤ = Set.univ := by
  ext x
  simp [box]

/-- `Λ_L = {x : |x| ≤ L}` when `L` is finite. -/
lemma mem_box_natCast {L : ℕ} {x : ℤ} : x ∈ box L ↔ |x| ≤ L := by
  rw [box, Set.mem_ofPred_eq, Nat.cast_le, ← Int.natCast_natAbs, Nat.cast_le]

/-- On `ℤ`, every site has two neighbours. -/
lemma degree_top (x : ℤ) : degree ⊤ x = 2 := by
  simp [degree]

/-- On `Λ_L` with `1 ≤ L < ∞`, `D(x,x) = 2 - 𝟙_{|x| = L}`, as in Definition 1.1. -/
lemma degree_natCast {L : ℕ} (hL : 1 ≤ L) {x : ℤ} (hx : x ∈ box L) :
    degree L x = if |x| = L then 1 else 2 := by
  have hL' : (0 : ℤ) ≤ L := by positivity
  rw [mem_box_natCast, abs_le] at hx
  have h1 : x + 1 ∈ box (L : ℕ∞) ↔ x + 1 ≤ L := by rw [mem_box_natCast, abs_le]; omega
  have h2 : x - 1 ∈ box (L : ℕ∞) ↔ -(L : ℤ) ≤ x - 1 := by rw [mem_box_natCast, abs_le]; omega
  classical
  simp only [degree, Set.indicator_apply, h1, h2, Pi.one_apply, abs_eq hL']
  split_ifs <;> omega

/-- The assumption `L / n^{3/4} → ∞` of the main theorem, which is stated in `[0, ∞]`, means that
for every constant `C`, eventually `C n^{3/4} < L`. -/
lemma tendsto_size_iff {n : ℕ → ℝ} (hn₁ : ∀ k, 1 ≤ n k) {L : ℕ → ℕ∞} :
    Tendsto (fun k => (L k : ℝ≥0∞) / ENNReal.ofReal (n k ^ (3 / 4 : ℝ))) atTop (𝓝 ⊤) ↔
      ∀ C : ℝ≥0, ∀ᶠ k in atTop, C * ENNReal.ofReal (n k ^ (3 / 4 : ℝ)) < L k := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  refine forall_congr' fun C => eventually_congr (Eventually.of_forall fun k => ?_)
  have hpos : 0 < n k ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (hn₁ k)) _
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
    (Or.inl ENNReal.ofReal_ne_top)]

/-- The assumption `L / n^{3/4} → ∞` of the main theorem holds when all the systems are
infinite. -/
lemma tendsto_size_top (n : ℕ → ℝ) :
    Tendsto (fun k => ((⊤ : ℕ∞) : ℝ≥0∞) / ENNReal.ofReal (n k ^ (3 / 4 : ℝ))) atTop (𝓝 ⊤) := by
  simp [ENNReal.top_div_of_ne_top]

/-! ### Riemann sums -/

/-- The subdivision used in `itoSum` covers `[0,t]`: for a constant integrand, the Riemann sum
is `c (W_t - W_0)`. -/
lemma itoSum_const (c : ℂ) (W : ℝ → Ω → ℂ) (t : ℝ) {m : ℕ} (hm : m ≠ 0) (ω : Ω) :
    itoSum (fun _ _ => c) W t m ω = c * (W t ω - W 0 ω) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have h := Finset.sum_range_sub (fun k : ℕ => W ((k : ℝ) * t / m) ω) m
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, zero_div] at h
  rw [itoSum, ← Finset.mul_sum, h, mul_div_cancel_left₀ t hm']

/-! ### Brownian motions -/

/-- The second moment of a centered Gaussian random variable. -/
lemma integral_sq_of_hasLaw {X : Ω → ℝ} {μ : Measure Ω} {v : ℝ≥0}
    (h : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 2 ∂μ = v := by
  rw [← variance_of_integral_eq_zero h.aemeasurable, h.variance_eq, variance_id_gaussianReal]
  rw [h.integral_eq, integral_id_gaussianReal]

/-- Random variables `X j` such that `X j` is measurable with respect to `m (j+1)` and
independent of `m j`, for an increasing family `m` of σ-algebras, are independent. -/
lemma iIndepFun_of_indep_past {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin n → Ω → ℝ}
    (m : Fin (n + 1) → MeasurableSpace Ω) (hm : Monotone m)
    (hmeas : ∀ j : Fin n, Measurable[m j.succ] (X j))
    (hind : ∀ j : Fin n, Indep (MeasurableSpace.comap (X j) inferInstance) (m j.castSucc) μ) :
    iIndepFun X μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hS ih =>
    have ha : a ∉ S := fun h => lt_irrefl a (hS a h)
    have hF : MeasurableSet[m a.castSucc] (⋂ j ∈ S, X j ⁻¹' sets j) := by
      refine Finset.measurableSet_biInter S fun j hj => ?_
      have hle : m j.succ ≤ m a.castSucc := hm (Fin.succ_le_castSucc_iff.2 (hS j hj))
      exact hle _ (hmeas j (hsets j (Finset.mem_insert_of_mem hj)))
    have hE : MeasurableSet[MeasurableSpace.comap (X a) inferInstance] (X a ⁻¹' sets a) :=
      ⟨sets a, hsets a (Finset.mem_insert_self a S), rfl⟩
    rw [Finset.set_biInter_insert, Finset.prod_insert ha,
      (Indep_iff _ _ μ).1 (hind a) _ _ hE hF,
      ih fun j hj => hsets j (Finset.mem_insert_of_mem hj)]

/-- Each member of a Brownian family, in the sense of `IsBrownianFamily`, is a Brownian motion
in the sense of Mathlib. -/
theorem IsBrownianFamily.isBrownianReal {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ι → ℝ → Ω → ℝ} {μ : Measure Ω} (hB : IsBrownianFamily 𝓕 B μ) (i : ι) :
    IsBrownianReal (fun (t : ℝ≥0) (ω : Ω) => B i t ω) μ where
  toIsPreBrownianReal := by
    have : IsProbabilityMeasure μ := (hB.gaussian i 0 0 le_rfl).isProbabilityMeasure
    refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t => ?_) (fun n t ht => ?_)
    · have h := hB.gaussian i 0 t zero_le
      rw [tsub_zero] at h
      refine h.congr ?_
      filter_upwards [hB.zero i] with ω hω
      simp [hω]
    · refine iIndepFun_of_indep_past (fun j => 𝓕 (t j)) (fun a b hab => 𝓕.mono (ht hab))
        (fun j => ?_) (fun j => ?_)
      · exact (hB.adapted i (t j.succ)).sub
          ((hB.adapted i (t j.castSucc)).mono (𝓕.mono (ht (Fin.castSucc_le_succ j))) le_rfl)
      · exact indep_of_indep_of_le_left
          (hB.indep_past (t j.castSucc) (t j.succ) (ht (Fin.castSucc_le_succ j)))
          (le_iSup (fun i => MeasurableSpace.comap
            (fun ω => B i (t j.succ) ω - B i (t j.castSucc) ω) inferInstance) i)
  cont := hB.continuous i

/-- The complex Brownian motions `W⁽ˣ⁾` are normalized so that `𝔼|W_t|² = t`, in agreement
with the Itô rules (1.2). -/
theorem integral_normSq_complexBM {𝓕 : Filtration ℝ≥0 mΩ} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}
    {μ : Measure Ω} (hB : IsBrownianFamily 𝓕 B μ) (x : ℤ) (t : ℝ≥0) :
    ∫ ω, ‖complexBM B x t ω‖ ^ 2 ∂μ = t := by
  have key : ∀ i, ∫ ω, B i t ω ^ 2 ∂μ = t ∧ Integrable (fun ω => B i t ω ^ 2) μ := by
    intro i
    have h := hB.gaussian i 0 t zero_le
    rw [tsub_zero] at h
    have h' : HasLaw (B i t) (gaussianReal 0 t) μ := by
      refine h.congr ?_
      filter_upwards [hB.zero i] with ω hω
      simp [hω]
    exact ⟨integral_sq_of_hasLaw h', h'.hasGaussianLaw.memLp_two.integrable_sq⟩
  have hnorm : ∀ ω, ‖complexBM B x t ω‖ ^ 2 = (B (x, 0) t ω ^ 2 + B (x, 1) t ω ^ 2) / 2 := by
    intro ω
    rw [complexBM, norm_div, mul_comm Complex.I, Complex.norm_add_mul_I, Complex.norm_real,
      div_pow, Real.sq_sqrt (by positivity), Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by norm_num)]
  simp_rw [hnorm]
  rw [integral_div, integral_add (key _).2 (key _).2, (key _).1, (key _).1]
  ring

/-! ### The rescaling -/

/-- `rescaledPosition n t y` is the solution `x` of `n^{3/4} t + n^{1/2} x = y`. -/
lemma rescaledPosition_spec {n : ℝ} (hn : 0 < n) (t : ℝ) (y : ℤ) :
    n ^ (3 / 4 : ℝ) * t + n ^ (1 / 2 : ℝ) * rescaledPosition n t y = y := by
  have h : n ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  rw [rescaledPosition]
  field_simp
  ring

/-- In terms of the lattice site `y`, the weight of the atom of `𝒵ₙ(t)` located at
`rescaledPosition n t y` is `exp(n^{-1/4} y - (n^{1/2}/2 + 1/24) t) P(nt/2, y)`. This is the
relation (3.6) between `𝒵ₙ` and the tilted field (3.2) of the article. -/
lemma rescaledField_eq {n : ℝ} (hn : 0 < n) (P : ℝ → ℤ → ℝ) (t : ℝ) (y : ℤ) :
    n ^ (-1 / 2 : ℝ) * rescaledField n P t y =
      Real.exp (n ^ (-1 / 4 : ℝ) * y - (n ^ (1 / 2 : ℝ) / 2 + 1 / 24) * t) * P (n * t / 2) y := by
  set r : ℝ := n ^ (1 / 4 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hn _
  have h2 : n ^ (1 / 2 : ℝ) = r ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  have h3 : n ^ (3 / 4 : ℝ) = r ^ 3 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  have hm2 : n ^ (-1 / 2 : ℝ) = (r ^ 2)⁻¹ := by
    rw [← h2, ← Real.rpow_neg hn.le]; norm_num
  have hm4 : n ^ (-1 / 4 : ℝ) = r⁻¹ := by
    rw [hr, ← Real.rpow_neg hn.le]; norm_num
  rw [rescaledField, rescaledPosition, hm2, hm4, h2, h3]
  have hexp : r ^ 2 * t / 2 + r * ((y - r ^ 3 * t) / r ^ 2) - t / 24 =
      r⁻¹ * y - (r ^ 2 / 2 + 1 / 24) * t := by
    field_simp
    ring
  rw [hexp]
  field_simp

/-- At time `0`, `𝒵ₙ(0) = δ₀`, for the initial condition `P(0, ·) = 𝟙_{· = 0}`. -/
theorem rescaledMeasure_zero (L : ℕ∞) {n : ℝ} (hn : 0 < n) {P : ℝ → ℤ → ℝ}
    (hP : ∀ y, P 0 y = if y = 0 then 1 else 0) :
    rescaledMeasure L n P 0 = Measure.dirac 0 := by
  have h0 : (0 : ℤ) ∈ box L := by simp [box]
  ext s hs
  rw [rescaledMeasure, Measure.sum_apply _ hs, tsum_eq_single (⟨0, h0⟩ : box L)]
  · rw [rescaledField_eq hn]
    simp [hP, rescaledPosition]
  · intro y hy
    have hy' : (y : ℤ) ≠ 0 := fun h => hy (Subtype.ext h)
    rw [rescaledField_eq hn]
    simp [hP, hy']

/-- A wave function, in the sense of `IsWaveFunction`, starts from `e₀`: almost surely,
`ψ_0(x) = 𝟙_{x = 0}` for all `x`. -/
theorem IsWaveFunction.initial {L : ℕ∞} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {μ : Measure Ω} (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    ∀ᵐ ω ∂μ, ∀ x : ℤ, ψ 0 ω x = if x = 0 then 1 else 0 := by
  have h0 : (0 : ℤ) ∈ box L := by simp [box]
  rw [ae_all_iff]
  intro x
  by_cases hx : x ∈ box L
  · have hzero : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => (0 : ℂ)) atTop (fun _ => 0) := by
      intro ε hε
      simp [hε.ne']
    have h : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => (0 : ℂ)) atTop
        (fun ω => ψ 0 ω x - (if x = 0 then 1 else 0)) := by
      simpa [itoSum] using hψ.sde 0 x hx
    filter_upwards [tendstoInMeasure_ae_unique hzero h] with ω hω
    exact sub_eq_zero.1 hω.symm
  · filter_upwards [hψ.support] with ω hω
    have hx0 : x ≠ 0 := fun h => hx (h ▸ h0)
    simpa [hx0] using hω 0 x hx

/-- For the one-particle QSSEP started from the origin, `𝒵ₙ(0) = δ₀` almost surely. -/
theorem IsWaveFunction.rescaledMeasure_zero {L : ℕ∞} {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {μ : Measure Ω}
    (hψ : IsWaveFunction L 𝓕 B ψ μ) {n : ℝ} (hn : 0 < n) :
    ∀ᵐ ω ∂μ, rescaledMeasure L n (density ψ ω) 0 = Measure.dirac 0 := by
  filter_upwards [hψ.initial] with ω hω
  refine QSSEPtoKPZ.rescaledMeasure_zero L hn fun y => ?_
  rw [density, hω y]
  split_ifs <;> simp

/-! ### The white noise -/

/-- The indicator function of a rectangle is integrable against the white noise, and its
integral is the mass of the rectangle. -/
lemma isWalshIntegral_rect (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω)
    {s t : ℝ≥0} {a b : ℝ} (hst : s ≤ t) (hab : a ≤ b) :
    IsWalshIntegral 𝓖 S ν
      (fun r y _ => if (s : ℝ) < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then 1 else 0)
      (rectMass S s t a b) := by
  have h := IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s t a b (fun _ => 1) hst hab
    measurable_const ⟨1, by simp⟩
  simpa using h

/-- Itô's isometry in the simplest case: the second moment of the mass of the rectangle
`(s,t] × (a,b]` is its area. -/
lemma integral_sq_rectMass {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}
    (hS : IsWhiteNoise 𝓖 S ν) {s t : ℝ≥0} {a b : ℝ} (hst : s ≤ t) (hab : a ≤ b) :
    ∫ ω, rectMass S s t a b ω ^ 2 ∂ν = (t - s) * (b - a) := by
  rw [integral_sq_of_hasLaw (hS.gaussian s t a b hst hab)]
  simp [NNReal.coe_sub hst, sub_nonneg.2 hab]

/-- The mass that the white noise gives to `(0, t] × (a, a + 1]` is, as a function of `t`, a
process with the finite-dimensional distributions of Brownian motion (Mathlib's
`IsPreBrownianReal`). -/
theorem IsWhiteNoise.isPreBrownianReal {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) (a : ℝ) :
    IsPreBrownianReal (fun (t : ℝ≥0) (ω : Ω) => rectMass S 0 t a (a + 1) ω) ν := by
  have ha : a ≤ a + 1 := by linarith
  have : IsProbabilityMeasure ν := (hS.gaussian 0 0 a (a + 1) le_rfl ha).isProbabilityMeasure
  have hmeas : ∀ u v : ℝ≥0, u ≤ v → Measurable[𝓖 v] (rectMass S 0 u a (a + 1)) := by
    intro u v huv
    have h1 : ∀ x, Measurable[𝓖 v] (S u x) := fun x =>
      (hS.adapted u x).mono (𝓖.mono huv) le_rfl
    have h0 : ∀ x, Measurable[𝓖 v] (S 0 x) := fun x => by
      simpa using (hS.adapted 0 x).mono (𝓖.mono (zero_le (a := v))) le_rfl
    exact (((h1 (a + 1)).sub (h1 a)).sub (h0 (a + 1))).add (h0 a)
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t => ?_) (fun n t ht => ?_)
  · simpa using hS.gaussian 0 t a (a + 1) zero_le ha
  · refine iIndepFun_of_indep_past (fun j => 𝓖 (t j)) (fun i j hij => 𝓖.mono (ht hij))
      (fun j => ?_) (fun j => ?_)
    · exact (hmeas (t j.succ) (t j.succ) le_rfl).sub
        (hmeas (t j.castSucc) (t j.succ) (ht (Fin.castSucc_le_succ j)))
    · have hX : (fun ω => rectMass S 0 (t j.succ) a (a + 1) ω -
          rectMass S 0 (t j.castSucc) a (a + 1) ω) =
          rectMass S (t j.castSucc) (t j.succ) a (a + 1) := by
        funext ω
        simp only [rectMass]
        ring
      have h := indep_of_indep_of_le_left
        (hS.indep_past (t j.castSucc) (t j.succ) (ht (Fin.castSucc_le_succ j)))
        (le_iSup₂ (f := fun a b => MeasurableSpace.comap
          (rectMass S (t j.castSucc) (t j.succ) a b) inferInstance) a (a + 1))
      rw [← hX] at h
      exact h

/-- Stochastic integrals against the white noise, in the sense of `IsWalshIntegral`, are
centered square-integrable random variables. -/
theorem IsWalshIntegral.memLp_and_integral_eq_zero {𝓖 : Filtration ℝ≥0 mΩ}
    {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ}
    {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) : MemLp X 2 ν ∧ ∫ ω, X ω ∂ν = 0 := by
  have : IsProbabilityMeasure ν := (hS.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    obtain ⟨C, hC⟩ := hbdd
    have hξ := hS.gaussian s t a b hst hab
    have hξ2 : MemLp (rectMass S s t a b) 2 ν := hξ.hasGaussianLaw.memLp_two
    have hcm : Measurable c := hc.mono (𝓖.le s) le_rfl
    have hind : IndepFun c (rectMass S s t a b) ν := by
      rw [IndepFun_iff_Indep]
      exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep_past s t hst)
        (le_iSup₂ (f := fun a b => MeasurableSpace.comap (rectMass S s t a b) inferInstance)
          a b)) hc.comap_le).symm
    refine ⟨?_, ?_⟩
    · refine MemLp.of_le_mul (c := |C|) hξ2
        (hcm.aestronglyMeasurable.mul hξ2.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
      rw [norm_mul]
      gcongr
      exact (hC ω).trans (le_abs_self C)
    · rw [hind.integral_fun_mul_eq_mul_integral hcm.aestronglyMeasurable
        hξ2.aestronglyMeasurable, hξ.integral_eq, integral_id_gaussianReal, mul_zero]
  | add h h' X X' _ _ ih ih' =>
    refine ⟨ih.1.add ih'.1, ?_⟩
    rw [integral_add (ih.1.integrable one_le_two) (ih'.1.integrable one_le_two), ih.2, ih'.2,
      add_zero]
  | limit h X hs Xs _ _ hXm _ hXs ih =>
    refine ⟨hXm, ?_⟩
    have h1 : Tendsto (fun k => ∫ ω, Xs k ω ∂ν) atTop (𝓝 (∫ ω, X ω ∂ν)) := by
      refine tendsto_integral_of_L1 X hXm.aestronglyMeasurable
        (Eventually.of_forall fun k => (ih k).1.integrable one_le_two) ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hXs
        (fun k => zero_le) (fun k => ?_)
      have hm : AEStronglyMeasurable (Xs k - X) ν :=
        (ih k).1.aestronglyMeasurable.sub hXm.aestronglyMeasurable
      calc ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ∂ν = eLpNorm (Xs k - X) 1 ν :=
            (eLpNorm_one_eq_lintegral_enorm hm).symm
        _ ≤ eLpNorm (Xs k - X) 2 ν := eLpNorm_le_eLpNorm_of_exponent_le one_le_two
    simp only [(ih _).2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- The expectation of the solution of the stochastic heat equation is the heat kernel:
`𝔼[Z(t,x)] = g_t(x)`, as noticed in Section 1.4 of the article. -/
theorem IsMildSolution.integral_eq_heatKernel {𝓖 : Filtration ℝ≥0 mΩ} {S Z : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) (hZ : IsMildSolution 𝓖 S Z ν) {t : ℝ}
    (ht : 0 < t) (x : ℝ) : ∫ ω, Z t x ω ∂ν = heatKernel t x := by
  have : IsProbabilityMeasure ν := (hS.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure
  obtain ⟨h2, h0⟩ := (hZ.mild t x ht).memLp_and_integral_eq_zero hS
  have hint : Integrable (fun ω => Z t x ω) ν := by
    refine ((h2.integrable one_le_two).add (integrable_const (heatKernel t x))).congr
      (ae_of_all _ fun ω => ?_)
    simp
  rw [integral_sub hint (integrable_const _)] at h0
  simpa [sub_eq_zero] using h0

/-! ### The heat kernel and the limit -/

/-- The heat kernel is the density of the Gaussian distribution with variance `t`. -/
lemma heatKernel_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x = gaussianPDFReal 0 t.toNNReal x := by
  rw [heatKernel, gaussianPDFReal, Real.coe_toNNReal t ht.le, sub_zero, div_eq_inv_mul]

/-- If `Z(t,x)` is replaced by its expectation `g_t(x)`, the measure `𝒵(t)` is the Gaussian
distribution with variance `t`. -/
theorem sheMeasure_heatKernel {t : ℝ} (ht : 0 < t) :
    sheMeasure heatKernel t = gaussianReal 0 t.toNNReal := by
  have hv : t.toNNReal ≠ 0 := (Real.toNNReal_pos.2 ht).ne'
  rw [sheMeasure, ite_eq_right ht.ne', gaussianReal_of_var_ne_zero 0 hv]
  congr 1
  ext x
  rw [gaussianPDF, heatKernel_eq_gaussianPDFReal ht]

/-- `𝒵(0) = δ₀`. -/
@[simp] lemma sheMeasure_zero (Z : ℝ → ℝ → ℝ) : sheMeasure Z 0 = Measure.dirac 0 := by
  simp [sheMeasure]

/-- For `t ≠ 0`, the measure `𝒵(t)` has density `max(Z(t,x), 0)` with respect to Lebesgue
measure, and not `Z(t,x)`: for every function `φ`,

  `∫ φ d𝒵(t) = ∫ max(Z(t,x), 0) φ(x) dx`,

provided `x ↦ Z(t,x)` is measurable (both sides are Bochner integrals). The two coincide when
`Z(t,·) ≥ 0` (`integral_sheMeasure_of_nonneg`); for the solution of the stochastic heat
equation this is the statement `IsMildSolution.nonneg` of `Companions.lean`. -/
theorem integral_sheMeasure {Z : ℝ → ℝ → ℝ} {t : ℝ} (ht : t ≠ 0) (hZ : Measurable (Z t))
    (φ : ℝ → ℝ) :
    ∫ x, φ x ∂(sheMeasure Z t) = ∫ x, max (Z t x) 0 * φ x := by
  simp only [sheMeasure, ht, ite_false]
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (Z t x))
    (ENNReal.measurable_ofReal.comp hZ) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) φ]
  simp [ENNReal.toReal_ofReal']

/-- If `Z(t,·) ≥ 0` and `t ≠ 0`, then `𝒵(t)(dx) = Z(t,x) dx`, in the sense that
`∫ φ d𝒵(t) = ∫ Z(t,x) φ(x) dx` for every function `φ`. -/
theorem integral_sheMeasure_of_nonneg {Z : ℝ → ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hZ : Measurable (Z t)) (hpos : ∀ x, 0 ≤ Z t x) (φ : ℝ → ℝ) :
    ∫ x, φ x ∂(sheMeasure Z t) = ∫ x, Z t x * φ x := by
  rw [integral_sheMeasure ht hZ φ]
  simp only [max_eq_left (hpos _)]

/-! ### Convergence at a fixed time -/

/-- Convergence in distribution in `C([0,T], ℳ₊(ℝ))` implies that, for any fixed time `t` and
any bounded continuous function `φ`, the integrals of `φ` at time `t` converge in
distribution. -/
theorem tendstoInDistribution_integral
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)} {μ : ∀ k, Measure (Ω k)}
    [∀ k, IsProbabilityMeasure (μ k)]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {T : ℝ} {𝒵n : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (h : TendstoInDistribution 𝒵n atTop 𝒵 μ ν) (t : Set.Icc (0 : ℝ) T)
    (φ : BoundedContinuousFunction ℝ ℝ) :
    TendstoInDistribution (fun k ω => ∫ x, φ x ∂(𝒵n k ω t : Measure ℝ)) atTop
      (fun ω => ∫ x, φ x ∂(𝒵 ω t : Measure ℝ)) μ ν := by
  have hg : Continuous fun f : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      ∫ x, φ x ∂(f t : Measure ℝ) :=
    (FiniteMeasure.continuous_integral_boundedContinuousFunction φ).comp
      (continuous_eval_const t)
  exact h.continuous_comp hg

end QSSEPtoKPZ
