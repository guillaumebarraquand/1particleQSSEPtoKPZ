/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.UnitNorm
public import QSSEPtoKPZ.WaveFunction.KernelUnique
public import QSSEPtoKPZ.Martingales.Covariation

/-!
# Auxiliary results for Proposition 2.2 (task D3)

Let `ψ'` be a unit-norm version of the wave function `ψ` (`IsUnitWave`), and
`J(x) = I(c_x)` with `c_x = waveCurrent ψ' x` (the currents of `UnitNorm.lean`).

* `IsUnitWave.eqP_tendstoInMeasure_riemann` ((2.3)): the Riemann sums
  `2 Im ∑_k conj(ψ_{t_k}(x)) ψ_{t_k}(x+1) (W⁽ˣ⁾_{t_{k+1}} - W⁽ˣ⁾_{t_k})` of the *original* `ψ`
  converge in probability to `J_t(x)`. (Write them as real Riemann sums of `c_x` against
  `B_{x,0}`, `B_{x,1}`; these converge in `L²` to `I_t(c_x)`.)
* `IsUnitWave.eqP_integral_stochInt`: `𝔼 J_t(x) = 0`.
* `IsUnitWave.eqP_integral_density_eq`: `m(t,x) = 𝔼 P(t,x)` satisfies
  `m(t,x) = 𝟙_{x=0} + ∫_0^t Δm(s,x) ds` (expectation of the equation of `P`, with Fubini), and
  hence `IsUnitWave.eqP_integral_density_eq_rwKernel`: `𝔼 P(t,x) = p_t(x)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `R(c f, W) = c R(f, W)` for the real Riemann sums. -/
lemma eqP_realRiemann_const_mul (c : ℝ) (f W : ℝ → Ω → ℝ) (t : ℝ) (m : ℕ) (ω : Ω) :
    realRiemann (fun s ω => c * f s ω) W t m ω = c * realRiemann f W t m ω := by
  simp only [realRiemann, Finset.mul_sum, mul_assoc]

/-- The imaginary part of `(a + i b) / c` is `b / c` for real `a, b, c`. -/
private lemma eqP_im_div (a b c : ℝ) :
    (((a : ℂ) + Complex.I * (b : ℂ)) / (c : ℂ)).im = b / c := by
  rw [Complex.div_ofReal_im]
  simp

/-- `2 Im itoSum (conj ψ(x) ψ(x+1)) W⁽ˣ⁾` is the sum of the real Riemann sums of the current
coefficients `c_x` against `B_{x,0}` and `B_{x,1}`. -/
lemma eqP_two_im_itoSum (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ) (t : ℝ)
    (m : ℕ) (ω : Ω) :
    2 * (itoSum (fun s ω => conj (ψ s ω x) * ψ s ω (x + 1)) (complexBM B x) t m ω).im =
      ∑ j ∈ ({(x, 0), (x, 1)} : Finset (ℤ × Fin 2)),
        realRiemann (waveCurrent ψ x j) (B j) t m ω := by
  rw [itoSum_complexBM, eqP_im_div, Finset.sum_pair (by simp)]
  have e0 : waveCurrent ψ x (x, 0) =
      fun s ω => Real.sqrt 2 * (conj (ψ s ω x) * ψ s ω (x + 1)).im := by
    funext s ω; exact waveCurrent_zero ψ x s ω
  have e1 : waveCurrent ψ x (x, 1) =
      fun s ω => Real.sqrt 2 * (conj (ψ s ω x) * ψ s ω (x + 1)).re := by
    funext s ω; exact waveCurrent_one ψ x s ω
  rw [e0, e1, eqP_realRiemann_const_mul, eqP_realRiemann_const_mul]
  have h2 : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := Real.div_sqrt
  rw [← h2]
  have : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

namespace IsUnitWave

/-- If `ψ' = ψ` on `[0, ∞)` at `ω`, then `P(s, ·)` computed from `ψ` and from `ψ'` agree for
`s ≥ 0`. -/
lemma eqP_density_eq {ω : Ω} (h : ∀ t : ℝ≥0, ψ' t ω = ψ t ω) {s : ℝ} (hs : 0 ≤ s) :
    density ψ ω s = density ψ' ω s := by
  funext y
  have : ψ' s ω = ψ s ω := h ⟨s, hs⟩
  simp only [density, this]

/-- `ω ↦ P(t,x)` (for `ψ'`) is measurable. -/
lemma eqP_measurable_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable fun ω => density ψ' ω t x :=
  ((hu.measurable_apply t x).mono ((nullAug μ 𝓕).le t) le_rfl).norm.pow_const 2

/-- `|P(t,x)| ≤ 1` (for `ψ'`, `t ≥ 0`). -/
lemma eqP_abs_density_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) (t : ℝ≥0) (x : ℤ) :
    |density ψ' ω t x| ≤ 1 := by
  rw [abs_of_nonneg (density_nonneg ψ' ω _ x)]
  exact hu.density_le_one ω t.coe_nonneg x

variable [IsProbabilityMeasure μ]

/-- **(2.3)**: the Riemann sums of `2 Im ∫ conj(ψ(x)) ψ(x+1) dW⁽ˣ⁾` (of the original `ψ`)
converge in probability to `J_t(x) = I_t(c_x)`. -/
theorem eqP_tendstoInMeasure_riemann (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) (t : ℝ≥0) :
    TendstoInMeasure μ (fun m ω => 2 * (itoSum
        (fun s ω => conj (ψ s ω x) * ψ s ω (x + 1)) (complexBM B x) t m ω).im) atTop
      (stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) t) := by
  classical
  set S : Finset (ℤ × Fin 2) := {(x, 0), (x, 1)} with hS
  have hbd : ∀ j ∈ S, ∀ s : ℝ, 0 ≤ s → ∀ ω, |waveCurrent ψ' x j s ω| ≤ 2 := by
    intro j _ s hs ω
    have hsum := summable_waveCurrent_mul ψ' x (fun i => waveCurrent ψ' x i s ω) s ω
    have hle : waveCurrent ψ' x j s ω ^ 2 ≤ 2 := by
      refine le_trans ?_ (hu.tsum_waveCurrent_sq_le x hs ω)
      exact (hsum.congr fun i => (sq _).symm).le_tsum j fun i _ => sq_nonneg _
    exact abs_le_of_sq_le_sq' (by nlinarith) (by norm_num) |> fun h => abs_le.2 h
  have hlc : ∀ j ∈ S, ∀ ω (s : ℝ), 0 < s →
      ContinuousWithinAt (fun r => waveCurrent ψ' x j r ω) (Set.Iic s) s :=
    fun j _ ω s hs =>
      (wavePath_continuousAt (hu.continuous_waveCurrent x j ω) hs).continuousWithinAt
  obtain ⟨-, hL2⟩ := tendsto_riemann_stochInt_finset hB.nullAug S hbd
    (fun j _ t => hu.measurable_waveCurrent x j t) hlc t
  have hfun : (fun j s ω => if j ∈ S then waveCurrent ψ' x j s ω else 0) = waveCurrent ψ' x := by
    funext j s ω
    split_ifs with hj
    · rfl
    · simp only [hS, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact (waveCurrent_of_ne ψ' hj.1 hj.2 s ω).symm
  rw [hfun] at hL2
  have hconv : TendstoInMeasure μ (fun m ω => ∑ j ∈ S, realRiemann (waveCurrent ψ' x j) (B j) t m ω)
      atTop (stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero hL2
  refine hconv.congr (fun m => ?_) (ae_of_all _ fun _ => rfl)
  filter_upwards [hu.ae_eq] with ω hω
  have hω' : ∀ r : ℝ, 0 ≤ r → ψ' r ω = ψ r ω := fun r hr => hω ⟨r, hr⟩
  refine (eqP_two_im_itoSum ψ' B x t m ω).symm.trans ?_
  congr 2
  unfold itoSum
  refine Finset.sum_congr rfl fun k _ => ?_
  have h' := hω' ((k : ℝ) * t / m) (by positivity)
  simp only [h']

/-- `J(x) = I(c_x)` is centered: `𝔼 J_t(x) = 0`, and integrable. -/
theorem eqP_integral_stochInt (hB : IsBrownianFamily 𝓕 B μ) (hu : IsUnitWave 𝓕 B ψ ψ' μ)
    (x : ℤ) (u : ℝ≥0) :
    Integrable (stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) u) μ ∧
      ∫ ω, stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) u ω ∂μ = 0 := by
  have hb := hu.hasBracket_waveCurrent hB x u
  refine ⟨(hb.memLp u le_rfl).integrable one_le_two, ?_⟩
  have hc := hb.condExp 0 u zero_le le_rfl
  rw [← integral_condExp ((nullAug μ 𝓕).le 0), integral_congr_ae hc]
  simp [stochInt_of_nonpos B _ (le_refl (0 : ℝ))]

/-- The expectation `m(s,y) = 𝔼 P(s⁺,y)` (with `s⁺ = max s 0`). -/
def eqPMean (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) (s : ℝ) (y : ℤ) : ℝ :=
  ∫ ω, density ψ' ω (s.toNNReal : ℝ) y ∂μ

/-- `s ↦ m(s,y)` is continuous (dominated convergence). -/
lemma eqP_continuous_mean (hu : IsUnitWave 𝓕 B ψ ψ' μ) (y : ℤ) :
    Continuous fun s => eqPMean ψ' μ s y := by
  refine continuous_of_dominated (bound := fun _ => 1)
    (fun s => (hu.eqP_measurable_density _ y).aestronglyMeasurable)
    (fun s => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
  · rw [Real.norm_eq_abs]; exact hu.eqP_abs_density_le ω _ y
  · exact (((hu.continuous_apply ω y).comp continuous_real_toNNReal).norm.pow 2)

/-- `|m(s,y)| ≤ 1`. -/
lemma eqP_abs_mean_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (s : ℝ) (y : ℤ) :
    |eqPMean ψ' μ s y| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => density ψ' ω (s.toNNReal : ℝ) y) (C := 1)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hu.eqP_abs_density_le ω _ y)
  simpa [eqPMean] using h

/-- `𝔼 ΔP(s,y) = Δm(s,y)`. -/
lemma eqP_integral_lap (hu : IsUnitWave 𝓕 B ψ ψ' μ) (s : ℝ) (y : ℤ) :
    ∫ ω, lap (fun z => density ψ' ω (s.toNNReal : ℝ) z) y ∂μ = lap (eqPMean ψ' μ s) y := by
  have hi : ∀ z, Integrable (fun ω => density ψ' ω (s.toNNReal : ℝ) z) μ := fun z =>
    Integrable.of_bound (hu.eqP_measurable_density _ z).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hu.eqP_abs_density_le ω _ z)
  simp only [lap, eqPMean]
  rw [integral_sub (f := fun ω => density ψ' ω (s.toNNReal : ℝ) (y + 1) +
      density ψ' ω (s.toNNReal : ℝ) (y - 1))
    (g := fun ω => 2 * density ψ' ω (s.toNNReal : ℝ) y) ((hi _).add (hi _)) ((hi _).const_mul 2),
    integral_add (hi _) (hi _), integral_const_mul]

/-- **Expectation of the equation of `P`**: for `t ≥ 0`,
`m(t,y) = 𝟙_{y=0} + ∫_0^t Δm(s,y) ds`. -/
theorem eqP_mean_eq (hB : IsBrownianFamily 𝓕 B μ) (hu : IsUnitWave 𝓕 B ψ ψ' μ) {t : ℝ}
    (ht : 0 ≤ t) (y : ℤ) :
    eqPMean ψ' μ t y = (if y = 0 then 1 else 0) + ∫ s in (0 : ℝ)..t, lap (eqPMean ψ' μ s) y := by
  set tn : ℝ≥0 := t.toNNReal with htn
  have htn' : (tn : ℝ) = t := Real.coe_toNNReal t ht
  set F : ℝ → Ω → ℝ := fun s ω => lap (fun z => density ψ' ω (s.toNNReal : ℝ) z) y with hF
  have hFm : Measurable (Function.uncurry F) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun s => ?_)
    · have hc : ∀ z, Continuous fun s : ℝ => density ψ' ω (s.toNNReal : ℝ) z := fun z =>
        (((hu.continuous_apply ω z).comp continuous_real_toNNReal).norm.pow 2)
      exact kernelU_continuous_lap (m := fun s z => density ψ' ω (s.toNNReal : ℝ) z) hc y
    · simp only [hF, lap]
      exact ((hu.eqP_measurable_density _ _).add (hu.eqP_measurable_density _ _)).sub
        ((hu.eqP_measurable_density _ _).const_mul 2)
  have hFb : ∀ s ω, ‖F s ω‖ ≤ 4 := fun s ω => by
    rw [Real.norm_eq_abs]
    simpa using kernelU_abs_lap_le (fun z => hu.eqP_abs_density_le ω _ z) y
  set ν := volume.restrict (Set.Ioc (0 : ℝ) t) with hν
  have hint : Integrable (Function.uncurry fun ω s => F s ω) (μ.prod ν) := by
    refine Integrable.of_bound ?_ 4 (ae_of_all _ fun p => hFb p.2 p.1)
    exact (hFm.comp measurable_swap).aestronglyMeasurable
  -- the time integral in the equation of `P` is `∫_{(0,t]} F`
  set I : Ω → ℝ := fun ω => ∫ s, F s ω ∂ν with hI
  have hIeq : ∀ ω, ∫ s in (0 : ℝ)..tn, lap (density ψ' ω s) y = I ω := by
    intro ω
    rw [htn', intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [hF, Real.coe_toNNReal s hs.1.le]
  have hIint : Integrable I μ := hint.integral_prod_left
  have hEI : ∫ ω, I ω ∂μ = ∫ s in (0 : ℝ)..t, lap (eqPMean ψ' μ s) y := by
    rw [hI, integral_integral_swap hint, intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    exact hu.eqP_integral_lap s y
  obtain ⟨hJ1i, hJ1⟩ := hu.eqP_integral_stochInt hB (y - 1) tn
  obtain ⟨hJ2i, hJ2⟩ := hu.eqP_integral_stochInt hB y tn
  have hae : (fun ω => density ψ' ω (t.toNNReal : ℝ) y) =ᵐ[μ] fun ω =>
      (if y = 0 then 1 else 0) + I ω +
        stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' (y - 1)) tn ω -
          stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' y) tn ω := by
    filter_upwards [hu.ae_density_eq hB] with ω hω
    rw [hω tn y, hIeq ω]
  have h1 : Integrable (fun ω => (if y = 0 then (1 : ℝ) else 0) + I ω) μ :=
    (integrable_const _).add hIint
  have h2 : Integrable (fun ω => (if y = 0 then (1 : ℝ) else 0) + I ω +
      stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' (y - 1)) tn ω) μ := h1.add hJ1i
  rw [eqPMean, integral_congr_ae hae, integral_sub h2 hJ2i, integral_add h1 hJ1i,
    integral_add (integrable_const _) hIint, hJ1, hJ2, hEI]
  simp

/-- **`𝔼 P(t,x) = p_t(x)`** for `ψ'` (and `t ≥ 0`). -/
theorem eqP_integral_density_eq_rwKernel (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    ∫ ω, density ψ' ω t x ∂μ = rwKernel t x := by
  have h := eq_rwKernel_of_integral_eq (m := eqPMean ψ' μ) (C := 1)
    (fun y => hu.eqP_continuous_mean y) (fun s _ y => hu.eqP_abs_mean_le s y)
    (fun s hs y => hu.eqP_mean_eq hB hs y) t.coe_nonneg x
  rw [← h, eqPMean, Real.toNNReal_coe]

end IsUnitWave

end QSSEPtoKPZ
