/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.MassLimit

/-!
# The unit-norm version `ψ̂` of the wave function; global Itô relations of `P` (task D2)

See `docs/stage2-design.md`, Section 1.2 (a), point 3, and (f). After the conservation of the
mass (`IsGoodWave.ae_norm_eq_one`), a good version can be modified on a null set so that
`‖ψ̂_t‖_{ℓ²} = 1` for *every* `t ≥ 0` and *every* `ω`:

* `IsUnitWave 𝓕 B ψ ψ̂ μ`: `ψ̂` is a good version of `ψ` (`IsGoodWave`) with `‖ψ̂_t‖ = 1` for all
  `t ≥ 0` and all `ω`; `IsWaveFunction.exists_isUnitWave`: it exists.
* Then `|ψ̂_t(x)| ≤ 1`, `0 ≤ P(t,x) ≤ 1`, `∑ₓ P(t,x) = 1` for all `t, ω`, and the localizing
  times are trivial: `τ_2 ∧ N = N` (`IsUnitWave.waveStop_eq`). Hence the relations of D1 and of
  `LocalP.lean` hold up to the deterministic time `N`, for every `N`:
  `IsUnitWave.isItoProcessUpTo_re`, `_im` (for `u_x`, `v_x`), `IsUnitWave.isItoProcessUpTo_density`
  (for `P(x)`: drift `ΔP(x)`, diffusion `c_{x-1} - c_x`).
* The currents `J(x) = I(c_x)` (`c_x = waveCurrent ψ̂ x`) are global Itô integrals
  (`IsUnitWave.isItoIntegrable_waveCurrent`) with `⟨J(x)⟩_t = 2 ∫_0^t P(s,x) P(s,x+1) ds`
  (`IsUnitWave.hasBracket_waveCurrent`, for `𝓕ᵃ`), and the equation of `P` holds globally
  (`IsUnitWave.ae_density_eq`): almost surely, for all `t ≥ 0` and `x`,
  `P(t,x) = 𝟙_{x=0} + ∫_0^t ΔP(s,x) ds + J_t(x-1) - J_t(x)`.

All the integrands of these relations are bounded by `1` (`∑ᵢ (c_x)ᵢ² = 2 P(x) P(x+1) ≤ 2`,
`∑ᵢ (c_{x-1} - c_x)ᵢ² ≤ 4`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- **Unit-norm version of the wave function.** `IsUnitWave 𝓕 B ψ ψ' μ`: `ψ'` is a good version
of `ψ` (`IsGoodWave`: a wave function for `𝓕ᵃ` with all paths continuous, starting from `e₀`,
indistinguishable from `ψ`), and `‖ψ'_t‖_{ℓ²} = 1` for all `t ≥ 0` and all `ω`. -/
structure IsUnitWave (𝓕 : Filtration ℝ≥0 mΩ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ)
    (ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop extends IsGoodWave 𝓕 B ψ ψ' μ where
  /-- `‖ψ'_t‖ = 1` for all `t ≥ 0` and all `ω`. -/
  norm_eq_one : ∀ ω (t : ℝ≥0), ‖ψ' t ω‖ = 1

/-- **Existence of a unit-norm version.** Every wave function on `ℤ` has a version `ψ'` with
`IsUnitWave 𝓕 B ψ ψ' μ`. (Take a good version `ψ₁`; by `IsGoodWave.ae_norm_eq_one` the set where
`‖ψ₁_t‖ ≠ 1` for some `t` is null; put `ψ' = e₀` on a measurable null set containing it.) -/
theorem IsWaveFunction.exists_isUnitWave [IsProbabilityMeasure μ] {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) :
    ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsUnitWave 𝓕 B ψ ψ' μ := by
  classical
  obtain ⟨ψ₁, hg⟩ := hψ.exists_isGoodWave
  set N := toMeasurable μ {ω | ¬ ∀ t : ℝ≥0, ‖ψ₁ t ω‖ = 1} with hNdef
  have hN0 : μ N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 (hg.ae_norm_eq_one hB)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω, ω ∉ N → ∀ t : ℝ≥0, ‖ψ₁ t ω‖ = 1 := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  set ψ' : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω => if ω ∈ N then waveInit else ψ₁ t ω with hψ'
  have h11 : ∀ᵐ ω ∂μ, ∀ t : ℝ, ψ' t ω = ψ₁ t ω := by
    filter_upwards [hNa] with ω hω t; simp [ψ', hω]
  refine ⟨ψ', ⟨⟨fun t x => ?_, ae_of_all _ fun ω => ?_, ae_of_all _ fun ω t x hx =>
    absurd (waveBox_top_mem x) hx, fun t x hx => ?_⟩, fun ω => ?_, fun ω => ?_, ?_⟩,
    fun ω t => ?_⟩
  · have e : (fun ω => ψ' t ω x) = fun ω => if ω ∈ N then waveInit x else ψ₁ t ω x := by
      ext ω; by_cases hω : ω ∈ N <;> simp [ψ', hω]
    rw [e]
    exact Measurable.ite (nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0))
      measurable_const (hg.measurable_apply t x)
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact continuous_const
    · simp only [ψ', hω, ite_false]; exact hg.continuous ω
  · refine (hg.wave.sde t x hx).congr (fun m => ?_) ?_
    · filter_upwards [h11] with ω hω
      simp only [itoSum, hω]
    · filter_upwards [h11] with ω hω
      simp only [hω]
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact continuous_const
    · simp only [ψ', hω, ite_false]; exact hg.continuous ω
  · by_cases hω : ω ∈ N
    · simp [ψ', hω]
    · simp only [ψ', hω, ite_false]; exact hg.init ω
  · filter_upwards [h11, hg.ae_eq] with ω h1 h2 t
    rw [h1, h2]
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact norm_waveInit
    · simp only [ψ', hω, ite_false]; exact hgood ω hω t

namespace IsUnitWave

variable {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `|ψ'_s(x)| ≤ 1` for `s ≥ 0`. -/
lemma norm_apply_le_one (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s) (x : ℤ) :
    ‖ψ' s ω x‖ ≤ 1 := by
  have h := hu.norm_eq_one ω ⟨s, hs⟩
  exact (lp.norm_apply_le_norm two_ne_zero _ x).trans h.le

/-- `0 ≤ P(s,x)`. -/
lemma density_nonneg (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) (x : ℤ) : 0 ≤ density ψ ω s x :=
  sq_nonneg _

/-- `P(s,x) ≤ 1` for `s ≥ 0`. -/
lemma density_le_one (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s) (x : ℤ) :
    density ψ' ω s x ≤ 1 :=
  pow_le_one₀ (norm_nonneg _) (hu.norm_apply_le_one ω hs x)

/-- **Conservation of the mass** for `ψ'`, for every `t ≥ 0` and every `ω`:
`∑ₓ P(t,x) = 1`. -/
lemma hasSum_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) (t : ℝ≥0) :
    HasSum (density ψ' ω t) 1 := by
  have h := hasSum_density_norm_sq ψ' ω t
  rwa [hu.norm_eq_one ω t, one_pow] at h

/-- The localizing times are trivial: `τ_2 ∧ N = N`. -/
lemma waveStop_eq (hu : IsUnitWave 𝓕 B ψ ψ' μ) (N : ℝ≥0) :
    waveStop ψ' 2 N = fun _ => N :=
  funext fun ω => hitTime_eq_of_forall_lt fun t _ => by
    simp only [hu.norm_eq_one ω t]; norm_num

/-- The coefficients of the current: `∑ᵢ (c_x)ᵢ² = 2 P(x) P(x+1) ≤ 2` at times `s ≥ 0`. -/
lemma tsum_waveCurrent_sq_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) {s : ℝ} (hs : 0 ≤ s)
    (ω : Ω) : ∑' i, waveCurrent ψ' x i s ω ^ 2 ≤ 2 := by
  rw [tsum_waveCurrent_sq]
  have h1 := hu.density_le_one ω hs x
  have h2 := hu.density_le_one ω hs (x + 1)
  have := mul_le_mul h1 h2 (density_nonneg ψ' ω s _) zero_le_one
  nlinarith [density_nonneg ψ' ω s x]

/-- The diffusion of `P(x)`: `∑ᵢ (c_{x-1} - c_x)ᵢ² ≤ 4` at times `s ≥ 0`. -/
lemma tsum_waveCurrent_sub_succ_sq_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) {s : ℝ}
    (hs : 0 ≤ s) (ω : Ω) :
    ∑' i, (waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) ^ 2 ≤ 4 := by
  rw [tsum_waveCurrent_sub_succ_sq]
  have h0 := hu.density_le_one ω hs (x - 1)
  have h1 := hu.density_le_one ω hs x
  have h2 := hu.density_le_one ω hs (x + 1)
  have a := mul_le_mul h0 h1 (density_nonneg ψ' ω s _) zero_le_one
  have b := mul_le_mul h1 h2 (density_nonneg ψ' ω s _) zero_le_one
  nlinarith

/-- Every path `t ↦ c_x(t)` of the current coefficients is continuous on `[0, ∞)`. -/
lemma continuous_waveCurrent (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) (i : ℤ × Fin 2) (ω : Ω) :
    Continuous fun t : ℝ≥0 => waveCurrent ψ' x i t ω := by
  have h1 := hu.continuous_apply ω x
  have h2 := hu.continuous_apply ω (x + 1)
  unfold waveCurrent
  split_ifs
  · exact continuous_const.mul (Complex.continuous_im.comp
      ((Complex.continuous_conj.comp h1).mul h2))
  · exact continuous_const.mul (Complex.continuous_re.comp
      ((Complex.continuous_conj.comp h1).mul h2))
  · exact continuous_const

/-- The current coefficients `c_x(t)` are `𝓕ᵃ_t`-measurable. -/
lemma measurable_waveCurrent (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) (i : ℤ × Fin 2) (t : ℝ≥0) :
    Measurable[nullAug μ 𝓕 t] (waveCurrent ψ' x i t) := by
  have h1 := hu.measurable_apply t x
  have h2 := hu.measurable_apply t (x + 1)
  unfold waveCurrent
  split_ifs
  · exact (Complex.measurable_im.comp ((Complex.continuous_conj.measurable.comp h1).mul
      h2)).const_mul _
  · exact (Complex.measurable_re.comp ((Complex.continuous_conj.measurable.comp h1).mul
      h2)).const_mul _
  · exact measurable_const

/-- **The currents are global Itô integrals**: `c_x = waveCurrent ψ' x` is Itô-integrable for
`𝓕ᵃ` (bounded, continuous, adapted), so `J(x) = I(c_x)` is defined on `[0, ∞)`. -/
theorem isItoIntegrable_waveCurrent [IsProbabilityMeasure μ] (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) :
    IsItoIntegrable (nullAug μ 𝓕) μ (waveCurrent ψ' x) := by
  refine isItoIntegrable_of_leftContinuous (K := 2) (fun ω s hs => ⟨?_, ?_⟩)
    (fun i t => hu.measurable_waveCurrent x i t) fun i ω s hs => ?_
  · exact (summable_waveCurrent_mul ψ' x (fun i => waveCurrent ψ' x i s ω) s ω).congr
      fun i => (sq _).symm
  · exact hu.tsum_waveCurrent_sq_le x hs.le ω
  · exact (wavePath_continuousAt (hu.continuous_waveCurrent x i ω) hs).continuousWithinAt

/-- **Bracket of a current** (for `𝓕ᵃ`): on every `[0, T]`, `J(x) = I(c_x)` is a continuous `L²`
martingale with `⟨J(x)⟩_t = 2 ∫_0^t P(s,x) P(s,x+1) ds` ((2.5)). -/
theorem hasBracket_waveCurrent [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) (T : ℝ) :
    HasBracket T (nullAug μ 𝓕) (stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x))
      (fun t ω => 2 * ∫ s in (0 : ℝ)..t, density ψ' ω s x * density ψ' ω s (x + 1)) μ := by
  have h := hasBracket_stochInt hB.nullAug (hu.isItoIntegrable_waveCurrent x) T
  convert h using 2 with t ω
  simp only [tsum_waveCurrent_sq, mul_assoc, intervalIntegral.integral_const_mul]

/-- `u_x = Re ψ'(x)` is an Itô process up to every deterministic time `N` (D1 with `τ_2 ∧ N = N`). -/
theorem isItoProcessUpTo_re [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (N : ℝ≥0) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N) (fun t ω => (ψ' t ω x).re)
      (fun s ω => -(ψ' s ω x).re) (waveDiffRe ψ' x) := by
  rw [← hu.waveStop_eq N]
  exact hu.toIsGoodWave.isItoProcessUpTo_re hB 2 N x

/-- `v_x = Im ψ'(x)` is an Itô process up to every deterministic time `N` (D1 with `τ_2 ∧ N = N`). -/
theorem isItoProcessUpTo_im [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (N : ℝ≥0) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N) (fun t ω => (ψ' t ω x).im)
      (fun s ω => -(ψ' s ω x).im) (waveDiffIm ψ' x) := by
  rw [← hu.waveStop_eq N]
  exact hu.toIsGoodWave.isItoProcessUpTo_im hB 2 N x

/-- **Equation of `P(x)` up to every deterministic time `N`**: `P(x)` is an Itô process up to
`N`, with drift `ΔP(x)` and diffusion `c_{x-1} - c_x`. -/
theorem isItoProcessUpTo_density [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (N : ℝ≥0) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N) (fun t ω => density ψ' ω t x)
      (fun s ω => lap (density ψ' ω s) x)
      (fun i s ω => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) := by
  rw [← hu.waveStop_eq N]
  exact hu.toIsGoodWave.isItoProcessUpTo_density hB 2 N x

/-- `I(c_{x-1} - c_x) = J(x-1) - J(x)`, almost surely, for all `t`. -/
private lemma unitWave_stochInt_sub [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) (x : ℤ) :
    IsItoIntegrable (nullAug μ 𝓕) μ
        (fun i s ω => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt (nullAug μ 𝓕) μ B
        (fun i s ω => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) t ω =
        stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' (x - 1)) t ω -
          stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) t ω := by
  have h1 := hu.isItoIntegrable_waveCurrent (x - 1)
  have h2 := (hu.isItoIntegrable_waveCurrent x).const_mul (-1)
  have e : (fun i s ω => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) =
      fun i s ω => waveCurrent ψ' (x - 1) i s ω + -1 * waveCurrent ψ' x i s ω := by
    funext i s ω; ring
  rw [e]
  refine ⟨h1.add h2, ?_⟩
  filter_upwards [stochInt_add hB.nullAug h1 h2,
    stochInt_const_mul hB.nullAug (hu.isItoIntegrable_waveCurrent x) (-1)] with ω ha hc t
  rw [ha t, hc t]
  ring

/-- **Global equation of `P`** ((2.4) for `ψ'`, with `J(x) = I(c_x)`): almost surely, for all
`t ≥ 0` and `x ∈ ℤ`, `P(t,x) = 𝟙_{x=0} + ∫_0^t ΔP(s,x) ds + J_t(x-1) - J_t(x)`. -/
theorem ae_density_eq [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) :
    ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ), density ψ' ω t x = (if x = 0 then 1 else 0) +
      (∫ s in (0 : ℝ)..t, lap (density ψ' ω s) x) +
        stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' (x - 1)) t ω -
          stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) t ω := by
  have hN : ∀ (N : ℕ) (x : ℤ), ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ N →
      density ψ' ω t x = (if x = 0 then 1 else 0) +
        (∫ s in (0 : ℝ)..t, lap (density ψ' ω s) x) +
          stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' (x - 1)) t ω -
            stochInt (nullAug μ 𝓕) μ B (waveCurrent ψ' x) t ω := by
    intro N x
    obtain ⟨hint, hsub⟩ := unitWave_stochInt_sub hB hu x
    have hP := (hu.isItoProcessUpTo_density hB N x).eq
    have hstop := stochInt_indicator_stoppingTime hB.nullAug hint
      (τ := fun _ => (N : ℝ≥0)) (isStoppingTime_const _ _)
    filter_upwards [hP, hstop, hsub] with ω h1 h2 h3 t ht
    have e := h1 t
    rw [h2 t, min_eq_left ht, h3 t] at e
    rw [e, density, hu.init_apply ω x]
    split_ifs <;> simp <;> ring
  filter_upwards [ae_all_iff.2 fun N => ae_all_iff.2 (hN N)] with ω hω t x
  obtain ⟨N, hN⟩ : ∃ N : ℕ, t ≤ N := ⟨⌈(t : ℝ)⌉₊, by
    rw [← NNReal.coe_le_coe]; push_cast; exact Nat.le_ceil _⟩
  exact hω N x t hN

end IsUnitWave

end QSSEPtoKPZ
