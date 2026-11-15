/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Frame
public import QSSEPtoKPZ.ItoIntegral.ContIntegrable
public import QSSEPtoKPZ.Uniqueness.Volterra
public import QSSEPtoKPZ.FiniteSystems.UniquenessAux

/-!
# Pathwise uniqueness of the wave function, every `L` (companion U1; task L5)

STATEMENT FILE (task T0‴ of Stage 5, `docs/stage5-statements.md`); the proof is task L5, in this
file (`docs/stage5-design.md`, Section 1.2 (i), decision D8‴: unit-norm Itô versions
(`IsWaveFunction.exists_unitIto`), Itô's isometry for the difference, `F(t) ≤ (4 + 2T) ∫_0^t F`,
and `volterra_ae_eq_zero`).

`isWaveFunction_unique_lib` is the companion statement **U1** of `Companions.lean`
(`isWaveFunction_unique`), word for word (checked with `pp.all` and by the kernel,
`docs/stage5-statements.md`). The hypothesis "probability measure" is not stated; it follows from
`IsBrownianFamily` (`IsBrownianFamily.isProbabilityMeasure`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **U1** (pathwise uniqueness of the wave function; Proposition 2.1 when `L = ∞`, linear
stochastic differential equations in finite dimension when `L < ∞`), library copy of
`isWaveFunction_unique`. Two wave functions on `Λ_L` driven by the same Brownian family, with
respect to the same filtration, are indistinguishable: almost surely, `ψ_t = ψ'_t` for all
`t ≥ 0`. -/
theorem isWaveFunction_unique_lib {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {L : ℕ∞}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℤ × Fin 2 → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ)
    (hψ' : IsWaveFunction L 𝓕 B ψ' μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ t ω = ψ' t ω := by
  have := hB.isProbabilityMeasure
  have hB' := hB.nullAug
  obtain ⟨φ, hφ, hn, hae⟩ := hψ.exists_unitIto hB
  obtain ⟨φ', hφ', hn', hae'⟩ := hψ'.exists_unitIto hB
  set F := waveUniqF μ φ φ' with hFdef
  -- `F ≤ 4` on `[0, ∞)`: the two solutions have norm one
  have hbound : ∀ t : ℝ≥0, F t ≤ 4 := by
    intro t
    have hpt : ∀ ω, (∑' x, ‖φ t ω x - φ' t ω x‖ₑ ^ 2) ≤ 4 := by
      intro ω
      have e := waveUniq_tsum_enorm_sq (φ t ω - φ' t ω)
      simp only [lp.coeFn_sub, Pi.sub_apply] at e
      rw [e]
      have h2 : ‖φ t ω - φ' t ω‖ ≤ 2 := by
        calc ‖φ t ω - φ' t ω‖ ≤ ‖φ t ω‖ + ‖φ' t ω‖ := norm_sub_le _ _
          _ = 2 := by rw [hn ω t, hn' ω t]; norm_num
      calc ENNReal.ofReal (‖φ t ω - φ' t ω‖ ^ 2) ≤ ENNReal.ofReal (2 ^ 2) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h2 2)
        _ = 4 := by norm_num
    calc F t ≤ ∫⁻ _, 4 ∂μ := lintegral_mono hpt
      _ = 4 := by simp
  -- `F = 0` on `[0, ∞)`: the Gronwall inequality and the Volterra lemma
  have hzero : ∀ t : ℝ≥0, F t = 0 := by
    intro t
    set N : ℝ≥0 := t + 1 with hN
    have htN : t ≤ N := by rw [hN]; exact le_add_of_nonneg_right zero_le_one
    have hNpos : (0 : ℝ) < N := by rw [hN]; push_cast; positivity
    have hFm : AEMeasurable F (volume.restrict (Set.Icc 0 (N : ℝ))) := by
      refine ((waveUniq_measurable hφ hφ').lintegral_prod_right' (ν := μ)).aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simp only [hFdef, waveUniqF, Real.coe_toNNReal s hs.1]
    have hFi : ∫⁻ s in Set.Icc 0 (N : ℝ), F s < ⊤ := by
      calc ∫⁻ s in Set.Icc 0 (N : ℝ), F s ≤ ∫⁻ _ in Set.Icc 0 (N : ℝ), 4 :=
            setLIntegral_mono' measurableSet_Icc fun s hs => by
              have h := hbound s.toNNReal
              rwa [Real.coe_toNNReal s hs.1] at h
        _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Icc]
          exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
    have hle : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 (N : ℝ))),
        F s ≤ ENNReal.ofReal ((4 + 2 * N) * Real.sqrt N) *
          ∫⁻ r in Set.Ioo 0 s, F r * ENNReal.ofReal ((s - r) ^ (-(1 / 2 : ℝ))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hsN : s.toNNReal ≤ N := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
      have h := waveUniq_gronwall hB' hφ hφ' hsN
      rw [Real.coe_toNNReal s hs.1, ← setLIntegral_congr Ioo_ae_eq_Ioc, ← hFdef] at h
      refine h.trans ?_
      rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      gcongr
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
      have hk : 1 ≤ Real.sqrt N * (s - r) ^ (-(1 / 2 : ℝ)) := by
        have hsr : 0 < s - r := by linarith [hr.2]
        rw [Real.rpow_neg hsr.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
          one_le_div (Real.sqrt_pos.2 hsr)]
        exact Real.sqrt_le_sqrt (by linarith [hr.1, hs.2])
      calc F r = F r * 1 := (mul_one _).symm
        _ ≤ F r * ENNReal.ofReal (Real.sqrt N * (s - r) ^ (-(1 / 2 : ℝ))) := by
            gcongr
            exact ENNReal.one_le_ofReal.2 hk
        _ = ENNReal.ofReal (Real.sqrt N) * (F r * ENNReal.ofReal ((s - r) ^ (-(1 / 2 : ℝ)))) := by
            rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
            ring
    have hvol := volterra_ae_eq_zero hFm hFi hle
    have h := waveUniq_gronwall hB' hφ hφ' htN
    have hsub : Set.Ioc 0 (t : ℝ) ⊆ Set.Icc 0 (N : ℝ) := fun s hs =>
      ⟨hs.1.le, hs.2.trans (by exact_mod_cast htN)⟩
    have hI : ∫⁻ s in Set.Ioc 0 (t : ℝ), F s = 0 := by
      calc ∫⁻ s in Set.Ioc 0 (t : ℝ), F s = ∫⁻ _ in Set.Ioc 0 (t : ℝ), 0 :=
            lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hvol)
        _ = 0 := lintegral_zero
    rw [← hFdef, hI, mul_zero] at h
    exact le_zero_iff.mp h
  -- almost surely `φ_t = φ'_t`, for each `t`
  have hpt : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, φ t ω = φ' t ω := by
    intro t
    have h := hzero t
    have hm : Measurable fun ω => ∑' x, ‖φ t ω x - φ' t ω x‖ₑ ^ 2 :=
      Measurable.tsum fun x =>
        ((((hφ.adapted t x).sub (hφ'.adapted t x)).mono ((QSSEPtoKPZ.nullAug μ 𝓕).le t)
          le_rfl).enorm.pow_const 2)
    rw [hFdef, waveUniqF, lintegral_eq_zero_iff hm] at h
    filter_upwards [h] with ω hω
    refine lp.ext (funext fun x => ?_)
    have hx := ENNReal.tsum_eq_zero.1 hω x
    simpa [sub_eq_zero] using hx
  -- continuity of the paths
  have hall : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, φ t ω = φ' t ω := by
    have hq : ∀ᵐ ω ∂μ, ∀ q : ℚ, φ ((q : ℝ).toNNReal) ω = φ' ((q : ℝ).toNNReal) ω :=
      ae_all_iff.2 fun q => hpt _
    filter_upwards [hq] with ω hω t
    have hc : Continuous fun r : ℝ => φ (r.toNNReal : ℝ) ω :=
      (hφ.continuous ω).comp continuous_real_toNNReal
    have hc' : Continuous fun r : ℝ => φ' (r.toNNReal : ℝ) ω :=
      (hφ'.continuous ω).comp continuous_real_toNNReal
    have heq := Continuous.ext_on Rat.denseRange_cast hc hc' (by
      rintro _ ⟨q, rfl⟩
      exact hω q)
    have := congrFun heq (t : ℝ)
    simpa using this
  filter_upwards [hae, hae', hall] with ω h1 h2 h3 t
  rw [← h1 t, ← h2 t, h3 t]

end QSSEPtoKPZ
