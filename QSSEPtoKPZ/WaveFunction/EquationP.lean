/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Kernel
public import QSSEPtoKPZ.Martingales.Covariation
public import QSSEPtoKPZ.WaveFunction.EquationPAux

/-!
# Proposition 2.2: the equation satisfied by `P` (case `L = ∞`)

Statement: Stage 2, task T0; proof: task D3. Only the case `L = ∞` is stated
(`docs/stage2-design.md`, decision D7).

Proof: take a unit-norm version `ψ'` of `ψ` (`IsWaveFunction.exists_isUnitWave`) and
`J(x) = I(c_x)`, `c_x = waveCurrent ψ' x`. Then (2.3) is
`IsUnitWave.eqP_tendstoInMeasure_riemann`, (2.4) is `IsUnitWave.ae_density_eq` (transferred
from `ψ'` to `ψ`), the brackets (2.5) are `IsUnitWave.hasBracket_waveCurrent` and
`condExp_stochInt_mul` with the orthogonality `tsum_waveCurrent_mul_waveCurrent` (transferred
from `𝓕ᵃ` to `𝓕`), and `𝔼 P(t,x) = p_t(x)` is `IsUnitWave.eqP_integral_density_eq_rwKernel`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Proposition 2.2**, equations (2.3), (2.4), (2.5), and `𝔼 P(t,x) = p_t(x)`, for `L = ∞`.
With `P = density ψ ω`, there are processes `J(x)`, `x ∈ ℤ`, such that:
* (2.3) for all `x` and `t ≥ 0`, `J_t(x) = 2 ∫_0^t Im(conj(ψ_s(x)) ψ_s(x+1) dW_s^{(x)})`, the
  stochastic integral being the limit in probability of left-point Riemann sums (`itoSum`, as in
  the frozen definition `IsWaveFunction`);
* (2.4) almost surely, for all `t ≥ 0` and `x`, `s ↦ ΔP(s,x)` and `s ↦ P(s,x) P(s,x+1)` are
  integrable on `[0,t]`, and `P(t,x) = 𝟙_{x=0} + ∫_0^t ΔP(s,x) ds + J_t(x-1) - J_t(x)`;
* (2.5) each `J(x)` is a continuous square-integrable martingale with
  `⟨J(x)⟩_t = 2 ∫_0^t P(s,x) P(s,x+1) ds`, and `⟨J(x), J(y)⟩ = 0` for `x ≠ y` (on every
  `[0,T]`);
* `P(t,x)` is integrable and `𝔼 P(t,x) = p_t(x)`. -/
theorem prop_2_2 (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) :
    ∃ J : ℤ → ℝ → Ω → ℝ,
      (∀ (x : ℤ) (t : ℝ≥0), TendstoInMeasure μ (fun m ω => 2 * (itoSum
          (fun s ω => conj (ψ s ω x) * ψ s ω (x + 1)) (complexBM B x) t m ω).im) atTop
          (J x t)) ∧
      (∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ),
          IntervalIntegrable (fun s => lap (density ψ ω s) x) volume 0 t ∧
          IntervalIntegrable (fun s => density ψ ω s x * density ψ ω s (x + 1)) volume 0 t ∧
          density ψ ω t x = (if x = 0 then 1 else 0) +
            (∫ s in (0 : ℝ)..t, lap (density ψ ω s) x) + J (x - 1) t ω - J x t ω) ∧
      (∀ (x : ℤ) (T : ℝ), HasBracket T 𝓕 (J x)
          (fun t ω => 2 * ∫ s in (0 : ℝ)..t, density ψ ω s x * density ψ ω s (x + 1)) μ) ∧
      (∀ x y : ℤ, x ≠ y → ∀ T : ℝ, HasCovariation T 𝓕 (J x) (J y) 0 μ) ∧
      (∀ (t : ℝ≥0) (x : ℤ), Integrable (fun ω => density ψ ω t x) μ ∧
          ∫ ω, density ψ ω t x ∂μ = rwKernel t x) := by
  obtain ⟨ψ', hu⟩ := hψ.exists_isUnitWave hB
  -- (2.5), the brackets
  have hbr : ∀ (x : ℤ) (T : ℝ), HasBracket T 𝓕 (stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x))
      (fun t ω => 2 * ∫ s in (0 : ℝ)..t, density ψ ω s x * density ψ ω s (x + 1)) μ := by
    intro x T
    have h := hasBracket_nullAug_iff.1 (hu.hasBracket_waveCurrent hB x (max T 0))
    refine (h.congr (le_max_right T 0) (ae_of_all _ fun _ _ _ => rfl) ?_).mono_horizon
      (le_max_left T 0)
    filter_upwards [hu.ae_eq] with ω hω t ht
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    simp only [IsUnitWave.eqP_density_eq hω hs.1]
  refine ⟨fun x => stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x),
    fun x t => hu.eqP_tendstoInMeasure_riemann hB x t, ?_, hbr, ?_, ?_⟩
  · -- (2.4)
    filter_upwards [hu.ae_eq, hu.ae_density_eq hB] with ω hω hP t x
    have hc : ∀ z, Continuous fun s : ℝ => density ψ' ω (s.toNNReal : ℝ) z := fun z =>
      ((hu.continuous_apply ω z).comp continuous_real_toNNReal).norm.pow 2
    have hEq : ∀ s : ℝ, 0 ≤ s → density ψ ω s = fun z => density ψ' ω (s.toNNReal : ℝ) z := by
      intro s hs
      rw [IsUnitWave.eqP_density_eq hω hs, Real.coe_toNNReal s hs]
    have hon : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        density ψ ω s = fun z => density ψ' ω (s.toNNReal : ℝ) z := fun s hs => by
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      exact hEq s hs.1
    refine ⟨?_, ?_, ?_⟩
    · exact ((kernelU_continuous_lap hc x).continuousOn.congr fun s hs => by
        rw [hon s hs]).intervalIntegrable
    · exact (((hc x).mul (hc (x + 1))).continuousOn.congr fun s hs => by
        rw [hon s hs]; rfl).intervalIntegrable
    · have hI : ∫ s in (0 : ℝ)..t, lap (density ψ ω s) x =
          ∫ s in (0 : ℝ)..t, lap (density ψ' ω s) x :=
        intervalIntegral.integral_congr fun s hs => by
          rw [Set.uIcc_of_le t.coe_nonneg] at hs
          simp only [IsUnitWave.eqP_density_eq hω hs.1]
      rw [IsUnitWave.eqP_density_eq hω t.coe_nonneg, hI]
      exact hP t x
  · -- (2.5), orthogonality of the currents
    intro x y hxy T
    refine { left := (hbr x T).toIsCL2Mart, right := (hbr y T).toIsCL2Mart,
             integrable_cov := fun _ _ => integrable_zero _ _ _,
             zero := ae_of_all _ fun _ => rfl,
             cont_cov := ae_of_all _ fun _ => continuousOn_const,
             bv := ae_of_all _ fun ω => ?_,
             condExp_mul := fun s t hst _ => ?_ }
    · show eVariationOn _ _ ≠ ⊤
      rw [eVariationOn.constant_on (Set.subsingleton_of_forall_eq 0 ?_)]
      · exact ENNReal.zero_ne_top
      · rintro _ ⟨r, _, rfl⟩
        rfl
    · have h := condExp_stochInt_mul hB.nullAug (hu.isItoIntegrable_waveCurrent x)
        (hu.isItoIntegrable_waveCurrent y) hst
      simp only [tsum_waveCurrent_mul_waveCurrent ψ' hxy, intervalIntegral.integral_zero,
        sub_zero] at h
      simp only [Pi.zero_apply, sub_zero]
      exact (condExp_nullAug (𝓕 := 𝓕) _ s).symm.trans h
  · -- `𝔼 P(t,x) = p_t(x)`
    intro t x
    have hae : (fun ω => density ψ' ω t x) =ᵐ[μ] fun ω => density ψ ω t x := by
      filter_upwards [hu.ae_eq] with ω hω
      rw [IsUnitWave.eqP_density_eq hω t.coe_nonneg]
    refine ⟨(Integrable.of_bound (hu.eqP_measurable_density t x).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hu.eqP_abs_density_le ω t x)).congr hae, ?_⟩
    rw [← integral_congr_ae hae]
    exact hu.eqP_integral_density_eq_rwKernel hB t x

end QSSEPtoKPZ
