/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.WaveIto
public import QSSEPtoKPZ.ItoIntegral.ContIntegrable
public import QSSEPtoKPZ.FiniteSystems.PicardBounds

/-!
# Picard iteration for the wave equation on `Λ_L`: the iterates (task L2a)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L2a.
`docs/stage5-design.md`, Section 1.2 (a) and note on L2a.

For `L ∈ ℕ ∪ {∞}` and `ψ₀ ∈ ℓ²` supported in `Λ_L`, the Picard map sends a process `φ` to
`Φ(φ)_t(x) = ψ₀(x) + ∫_0^t waveDiffRe φ x · dB + i ∫_0^t waveDiffIm φ x · dB
  - (D_L(x,x)/2) ∫_0^t φ_s(x) ds` for `x ∈ Λ_L`, and `0` outside `Λ_L` (`picardCoord`, defined
coordinatewise; it need not be in `ℓ²` for every `ω`).

* `IsPicardAdmissible L 𝓖 ψ₀ φ μ`: `φ` is adapted, has continuous `ℓ²` paths for every `ω`,
  vanishes outside `Λ_L`, starts from `ψ₀`, and `𝔼 sup_{t ≤ T} ‖φ_t‖² < ∞` for every `T`.
* `IsPicardAdmissible.isItoIntegrable_re/im`: the coefficients `waveDiffRe φ x`,
  `waveDiffIm φ x` of an admissible `φ` are Itô-integrable (G11a).
* `picard_step_exists`: for the augmented filtration `𝓕ᵃ = nullAug μ 𝓕`, the Picard image of an
  admissible process has an admissible version (built as in `IsWaveFunction.exists_good`: on a
  measurable null set the iterate is put equal to `ψ₀`).
* `picard_step_bound`: the contraction estimate
  `𝔼 sup_{s ≤ t} ‖Φ(φ₁)_s - Φ(φ₂)_s‖² ≤ (16 + 2T) ∫_0^t 𝔼 sup_{u ≤ s} ‖φ₁_u - φ₂_u‖² ds`
  for `0 ≤ t ≤ T` (Doob, Itô's isometry, Cauchy–Schwarz, `∑_{x,i} σ_{x,i}(φ)² ≤ 2 ‖φ‖²`).
* `picard_iterates`: the sequence of admissible iterates `φ⁽⁰⁾ = ψ₀`, `φ⁽ᵐ⁺¹⁾ = Φ(φ⁽ᵐ⁾)` a.s.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

open Classical in
/-- **The Picard map, coordinatewise**: for `x ∈ Λ_L`,
`Φ(φ)_t(x) = ψ₀(x) + (I_t(waveDiffRe φ x) + i I_t(waveDiffIm φ x)) - (D_L(x,x)/2) ∫_0^t φ_s(x) ds`
(`I_t` the Itô integral `stochInt` against the real Brownian family `B`), and `0` outside `Λ_L`. -/
def picardCoord (𝓖 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (L : ℕ∞)
    (ψ0 : ℓ²(ℤ, ℂ)) (φ : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (ω : Ω) (x : ℤ) : ℂ :=
  if x ∈ box L then
    ψ0 x + ((stochInt 𝓖 μ B (waveDiffRe φ x) t ω : ℂ)
        + Complex.I * (stochInt 𝓖 μ B (waveDiffIm φ x) t ω : ℂ))
      - ((degree L x : ℂ) / 2) * (∫ s in (0 : ℝ)..t, φ s ω x)
  else 0

/-- **Admissible processes for the Picard iteration**: adapted to `𝓖`, continuous `ℓ²` paths and
support in `Λ_L` for every `ω`, initial value `ψ0` for every `ω`, and
`𝔼 sup_{t ∈ [0,T]} ‖φ_t‖² < ∞` for every `T`. -/
structure IsPicardAdmissible (L : ℕ∞) (𝓖 : Filtration ℝ≥0 mΩ) (ψ0 : ℓ²(ℤ, ℂ))
    (φ : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop where
  adapted : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => φ t ω x
  continuous : ∀ ω, Continuous fun t : ℝ≥0 => φ t ω
  support : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → φ t ω x = 0
  init : ∀ ω, φ 0 ω = ψ0
  moment : ∀ T : ℝ, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖φ t ω‖ ^ 2)) ∂μ < ⊤

/-! ### Auxiliary results (task L2a) -/

/-- For an admissible process, `𝔼 ∫_0^T ‖φ_u‖² du < ∞`. -/
private lemma picardIter_lintegral_J_lt_top {𝓖 : Filtration ℝ≥0 mΩ} {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)}
    {φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsPicardAdmissible L 𝓖 ψ0 φ μ) (T : ℝ) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖φ u ω‖ ^ 2)) ∂μ < ⊤ := by
  calc ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖φ u ω‖ ^ 2)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal T * (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖φ t ω‖ ^ 2)) ∂μ :=
        lintegral_mono fun ω => picardBd_setLIntegral_le φ ω T
    _ = ENNReal.ofReal T *
          ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖φ t ω‖ ^ 2)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.moment T)

/-! ### Itô-integrability of the coefficients -/

/-- The real coefficients of an admissible process are Itô-integrable. -/
theorem IsPicardAdmissible.isItoIntegrable_re [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsPicardAdmissible L 𝓖 ψ0 φ μ)
    (x : ℤ) : IsItoIntegrable 𝓖 μ (waveDiffRe φ x) := by
  have hca : ∀ ω y, Continuous fun t : ℝ≥0 => φ t ω y := fun ω y =>
    picardBd_continuous_coord (h.continuous ω) y
  refine isItoIntegrable_of_continuous (fun i t => ?_) (fun i ω => ?_) (fun ω s => ?_)
    (fun ω => ?_) (fun T => ?_)
  · unfold waveDiffRe
    split_ifs
    · exact (Complex.measurable_im.comp (h.adapted t _)).neg.div_const _
    · exact (Complex.measurable_re.comp (h.adapted t _)).neg.div_const _
    · exact (Complex.measurable_im.comp (h.adapted t _)).neg.div_const _
    · exact (Complex.measurable_re.comp (h.adapted t _)).div_const _
    · exact measurable_const
  · simp only [waveDiffRe]
    split_ifs
    · exact (Complex.continuous_im.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_re.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_im.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_re.comp (hca ω _)).div_const _
    · exact continuous_const
  · exact summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffRe_of_notMem φ hi]; norm_num
  · simp_rw [tsum_waveDiffRe_sq]
    exact (((hca ω _).norm.pow 2).add ((hca ω _).norm.pow 2)).div_const 2
  · exact (picardBd_energy_re_le φ x T).trans_lt (picardIter_lintegral_J_lt_top h T)

/-- The imaginary coefficients of an admissible process are Itô-integrable. -/
theorem IsPicardAdmissible.isItoIntegrable_im [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsPicardAdmissible L 𝓖 ψ0 φ μ)
    (x : ℤ) : IsItoIntegrable 𝓖 μ (waveDiffIm φ x) := by
  have hca : ∀ ω y, Continuous fun t : ℝ≥0 => φ t ω y := fun ω y =>
    picardBd_continuous_coord (h.continuous ω) y
  refine isItoIntegrable_of_continuous (fun i t => ?_) (fun i ω => ?_) (fun ω s => ?_)
    (fun ω => ?_) (fun T => ?_)
  · unfold waveDiffIm
    split_ifs
    · exact (Complex.measurable_re.comp (h.adapted t _)).div_const _
    · exact (Complex.measurable_im.comp (h.adapted t _)).neg.div_const _
    · exact (Complex.measurable_re.comp (h.adapted t _)).div_const _
    · exact (Complex.measurable_im.comp (h.adapted t _)).div_const _
    · exact measurable_const
  · simp only [waveDiffIm]
    split_ifs
    · exact (Complex.continuous_re.comp (hca ω _)).div_const _
    · exact (Complex.continuous_im.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_re.comp (hca ω _)).div_const _
    · exact (Complex.continuous_im.comp (hca ω _)).div_const _
    · exact continuous_const
  · exact summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffIm_of_notMem φ hi]; norm_num
  · simp_rw [tsum_waveDiffIm_sq]
    exact (((hca ω _).norm.pow 2).add ((hca ω _).norm.pow 2)).div_const 2
  · exact (picardBd_energy_im_le φ x T).trans_lt (picardIter_lintegral_J_lt_top h T)

/-! ### Auxiliary results (task L2a): the family of all coefficients -/

/-- The family of all diffusion coefficients, indexed by `(x, j)`: `waveDiffRe ψ x` for
`j = 0` and `waveDiffIm ψ x` for `j = 1`. -/
private def picardFam (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (k : ℤ × Fin 2) : ℤ × Fin 2 → ℝ → Ω → ℝ :=
  if k.2 = 0 then waveDiffRe ψ k.1 else waveDiffIm ψ k.1

/-- `σ_{(x,0)}(ψ) = waveDiffRe ψ x`. -/
private lemma picardFam_zero (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) :
    picardFam ψ (x, 0) = waveDiffRe ψ x := by
  simp [picardFam]

/-- `σ_{(x,1)}(ψ) = waveDiffIm ψ x`. -/
private lemma picardFam_one (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) :
    picardFam ψ (x, 1) = waveDiffIm ψ x := by
  simp [picardFam]

/-- `∑_{(x,j)} f(x,j) = ∑ₓ (f(x,0) + f(x,1))` in `[0, ∞]`. -/
private lemma picardIter_tsum_prod (f : ℤ × Fin 2 → ℝ≥0∞) :
    ∑' k, f k = ∑' x, (f (x, 0) + f (x, 1)) := by
  rw [ENNReal.tsum_prod']
  exact tsum_congr fun x => by rw [tsum_fintype, Fin.sum_univ_two]

/-- The coefficients of an admissible process are Itô-integrable. -/
private lemma picardIter_isItoIntegrable_fam [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsPicardAdmissible L 𝓖 ψ0 φ μ)
    (k : ℤ × Fin 2) : IsItoIntegrable 𝓖 μ (picardFam φ k) := by
  unfold picardFam
  split_ifs
  exacts [h.isItoIntegrable_re _, h.isItoIntegrable_im _]

/-- `∑_{(x,j)} energy(σ_{x,j}(ψ)) ≤ 2 𝔼 ∫_0^T ‖ψ_u‖² du` (`∑_{x,i} σ_{x,i}(ψ)² = 2 ‖ψ‖²`). -/
private lemma picardIter_tsum_energy_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (T : ℝ) :
    ∑' k, energy μ (picardFam ψ k) T ≤
      2 * ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ := by
  have hpt : ∀ u ω, ∑' k, ∑' i, ‖picardFam ψ k i u ω‖ₑ ^ 2 =
      2 * ENNReal.ofReal (‖ψ u ω‖ ^ 2) := by
    intro u ω
    rw [picardIter_tsum_prod (fun k => ∑' i, ‖picardFam ψ k i u ω‖ₑ ^ 2),
      ← picardAux_tsum_shift]
    refine tsum_congr fun x => ?_
    simp only [picardFam_zero, picardFam_one]
    rw [picardBd_tsum_enorm_re, picardBd_tsum_enorm_im,
      ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  calc ∑' k, energy μ (picardFam ψ k) T
      ≤ ∫⁻ ω, (∑' k, pathEnergy (picardFam ψ k) T ω) ∂μ := picardAux_tsum_lintegral_le _
    _ ≤ ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, 2 * ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ := by
        refine lintegral_mono fun ω => (picardAux_tsum_lintegral_le _).trans_eq ?_
        simp_rw [hpt]
    _ = 2 * ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ := by
        simp_rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

/-- `∑_{(x,j)} energy(σ_{x,j}(φ)) < ∞` for an admissible `φ`. -/
private lemma picardIter_tsum_energy_lt_top [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsPicardAdmissible L 𝓖 ψ0 φ μ)
    (T : ℝ) : ∑' k, energy μ (picardFam φ k) T < ⊤ :=
  (picardIter_tsum_energy_le φ T).trans_lt
    (ENNReal.mul_lt_top (by norm_num) (picardIter_lintegral_J_lt_top h T))

/-- **Bound on one coordinate of the Picard map.** -/
private lemma picardIter_coord_bound {𝓖 : Filtration ℝ≥0 mΩ} {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)}
    {φ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} (hc : Continuous fun t : ℝ≥0 => φ t ω) {t : ℝ}
    (ht : 0 ≤ t) (x : ℤ) :
    ENNReal.ofReal (‖picardCoord 𝓖 μ B L ψ0 φ t ω x‖ ^ 2) ≤
      3 * ENNReal.ofReal (‖ψ0 x‖ ^ 2) +
        3 * (ENNReal.ofReal (stochInt 𝓖 μ B (picardFam φ (x, 0)) t ω ^ 2) +
          ENNReal.ofReal (stochInt 𝓖 μ B (picardFam φ (x, 1)) t ω ^ 2)) +
        3 * (ENNReal.ofReal t * ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖φ u ω x‖ ^ 2)) := by
  unfold picardCoord
  split_ifs
  · rw [picardFam_zero, picardFam_one]
    refine (picardBd_coord_le3 _ _ _ _ L x).trans ?_
    gcongr
    exact picardAux_sq_integral_le ht ((picardBd_continuousOn hc x).mono Set.Icc_subset_Ici_self)
  · simp

/-- **Bound on one coordinate of the difference of two Picard images.** -/
private lemma picardIter_coord_sub_bound {𝓖 : Filtration ℝ≥0 mΩ} {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)}
    {φ₁ φ₂ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} (hc₁ : Continuous fun t : ℝ≥0 => φ₁ t ω)
    (hc₂ : Continuous fun t : ℝ≥0 => φ₂ t ω) {t : ℝ} (ht : 0 ≤ t) (x : ℤ) :
    ENNReal.ofReal (‖picardCoord 𝓖 μ B L ψ0 φ₁ t ω x - picardCoord 𝓖 μ B L ψ0 φ₂ t ω x‖ ^ 2) ≤
      2 * (ENNReal.ofReal ((stochInt 𝓖 μ B (waveDiffRe φ₁ x) t ω -
            stochInt 𝓖 μ B (waveDiffRe φ₂ x) t ω) ^ 2) +
          ENNReal.ofReal ((stochInt 𝓖 μ B (waveDiffIm φ₁ x) t ω -
            stochInt 𝓖 μ B (waveDiffIm φ₂ x) t ω) ^ 2)) +
        2 * (ENNReal.ofReal t *
          ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖φ₁ u ω x - φ₂ u ω x‖ ^ 2)) := by
  unfold picardCoord
  split_ifs
  · have hsub := intervalIntegral.integral_sub (picardBd_intervalIntegrable hc₁ x ht)
      (picardBd_intervalIntegrable hc₂ x ht)
    have e : ψ0 x + ((stochInt 𝓖 μ B (waveDiffRe φ₁ x) t ω : ℂ) +
          Complex.I * (stochInt 𝓖 μ B (waveDiffIm φ₁ x) t ω : ℂ)) -
          (degree L x : ℂ) / 2 * (∫ s in (0 : ℝ)..t, φ₁ s ω x) -
        (ψ0 x + ((stochInt 𝓖 μ B (waveDiffRe φ₂ x) t ω : ℂ) +
          Complex.I * (stochInt 𝓖 μ B (waveDiffIm φ₂ x) t ω : ℂ)) -
          (degree L x : ℂ) / 2 * (∫ s in (0 : ℝ)..t, φ₂ s ω x)) =
        (((stochInt 𝓖 μ B (waveDiffRe φ₁ x) t ω - stochInt 𝓖 μ B (waveDiffRe φ₂ x) t ω : ℝ) :
            ℂ) + Complex.I * ((stochInt 𝓖 μ B (waveDiffIm φ₁ x) t ω -
              stochInt 𝓖 μ B (waveDiffIm φ₂ x) t ω : ℝ) : ℂ)) -
          (degree L x : ℂ) / 2 * (∫ s in (0 : ℝ)..t, (φ₁ s ω x - φ₂ s ω x)) := by
      rw [hsub]
      push_cast
      ring
    rw [e]
    refine (picardBd_coord_le2 _ _ _ L x).trans ?_
    gcongr
    exact picardAux_sq_integral_le ht
      (((picardBd_continuousOn hc₁ x).sub (picardBd_continuousOn hc₂ x)).mono
        Set.Icc_subset_Ici_self)
  · simp

/-- **One Picard step.** For the augmented filtration `𝓕ᵃ`, the Picard image of an admissible
process has an admissible version, equal to `picardCoord` for all `t` and `x`, almost surely. -/
theorem picard_step_exists [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) {L : ℕ∞}
    {ψ0 : ℓ²(ℤ, ℂ)} (hψ0 : ∀ x, x ∉ box L → ψ0 x = 0) {φ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hφ : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 φ μ) :
    ∃ φ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsPicardAdmissible L (nullAug μ 𝓕) ψ0 φ' μ ∧
      ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ), φ' t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 φ t ω x := by
  classical
  have hB' := hB.nullAug
  set 𝓖 := nullAug μ 𝓕 with h𝓖
  have hca : ∀ ω y, Continuous fun t : ℝ≥0 => φ t ω y := fun ω y =>
    picardBd_continuous_coord (hφ.continuous ω) y
  have hF := picardIter_isItoIntegrable_fam hφ
  set c : ℝ → Ω → ℤ → ℂ := fun t ω x => picardCoord 𝓖 μ B L ψ0 φ t ω x with hcdef
  -- adaptedness of the coordinates of the Picard image
  have hcm : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => c t ω x := by
    intro t x
    simp only [hcdef, picardCoord]
    split_ifs
    · have hd : Measurable[𝓖 t] fun ω => ∫ s in (0 : ℝ)..t, φ s ω x :=
        @picardAux_measurable_intervalIntegral Ω (𝓖 t) (fun s ω => φ s ω x) t
          (fun s hs => (hφ.adapted s x).mono (𝓖.mono hs) le_rfl) (fun ω => hca ω x)
      exact (measurable_const.add ((Complex.measurable_ofReal.comp (stochInt_adapted hB' _ t)).add
        (measurable_const.mul (Complex.measurable_ofReal.comp (stochInt_adapted hB' _ t))))).sub
        (measurable_const.mul hd)
    · exact measurable_const
  -- the martingale parts: continuity and summed Doob inequality
  have hE1 : ∀ᵐ ω ∂μ, ∀ k, Continuous fun t : ℝ≥0 => stochInt 𝓖 μ B (picardFam φ k) t ω :=
    ae_all_iff.2 fun k => stochInt_continuous hB' (hF k)
  have hSm : ∀ k (r : ℝ), Measurable (stochInt 𝓖 μ B (picardFam φ k) r) := by
    intro k r
    rcases le_or_gt r 0 with hr | hr
    · have : stochInt 𝓖 μ B (picardFam φ k) r = fun _ => 0 :=
        funext fun ω => stochInt_of_nonpos B _ hr ω
      rw [this]
      exact measurable_const
    · have := (stochInt_adapted hB' (picardFam φ k) r.toNNReal).mono (𝓖.le _) le_rfl
      rwa [Real.coe_toNNReal _ hr.le] at this
  set S : ℝ → ℤ × Fin 2 → Ω → ℝ≥0∞ := fun T k ω =>
    ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (stochInt 𝓖 μ B (picardFam φ k) t ω ^ 2) with hSdef
  have hSint : ∀ T, ∫⁻ ω, (∑' k, S T k ω) ∂μ < ⊤ := fun T =>
    (lintegral_tsum_iSup_stochInt_sq_le hB' hF T).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (picardIter_tsum_energy_lt_top hφ T))
  set Q : ℕ → ℤ × Fin 2 → Ω → ℝ≥0∞ := fun n k ω =>
    ⨆ q : ℚ, ENNReal.ofReal (stochInt 𝓖 μ B (picardFam φ k) (max 0 (min (q : ℝ) n)) ω ^ 2)
    with hQdef
  have hE2 : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∑' k, Q n k ω < ⊤ := by
    rw [ae_all_iff]
    intro n
    refine ae_lt_top (Measurable.tsum fun k => Measurable.iSup fun q =>
      ENNReal.measurable_ofReal.comp ((hSm k _).pow_const 2)) ?_
    exact ne_top_of_le_ne_top (hSint n).ne (lintegral_mono fun ω => ENNReal.tsum_le_tsum fun k =>
      picardAux_iSup_rat_le (X := fun t => stochInt 𝓖 μ B (picardFam φ k) t ω) (Nat.cast_nonneg n))
  -- the good event
  set G : Set Ω := {ω | (∀ x, Continuous fun t : ℝ≥0 => c t ω x) ∧
      ∀ n : ℕ, ∑' x, (⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖c t ω x‖ ^ 2)) < ⊤} with hGdef
  have hG : ∀ᵐ ω ∂μ, ω ∈ G := by
    filter_upwards [hE1, hE2] with ω h1 h2
    refine ⟨fun x => ?_, fun n => ?_⟩
    · simp only [hcdef, picardCoord]
      split_ifs
      · have hr := h1 (x, 0)
        have hi := h1 (x, 1)
        rw [picardFam_zero] at hr
        rw [picardFam_one] at hi
        exact (continuous_const.add ((Complex.continuous_ofReal.comp hr).add
          (continuous_const.mul (Complex.continuous_ofReal.comp hi)))).sub
          (continuous_const.mul (picardBd_continuous_drift (hφ.continuous ω) x))
      · exact continuous_const
    · calc ∑' x, (⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖c t ω x‖ ^ 2))
          ≤ ∑' x, (3 * ENNReal.ofReal (‖ψ0 x‖ ^ 2) + 3 * (Q n (x, 0) ω + Q n (x, 1) ω) +
              3 * (ENNReal.ofReal n *
                ∫⁻ u in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (‖φ u ω x‖ ^ 2))) := by
            refine ENNReal.tsum_le_tsum fun x => iSup₂_le fun t ht => ?_
            refine (picardIter_coord_bound (hφ.continuous ω) ht.1 x).trans ?_
            exact add_le_add (add_le_add le_rfl (picardBd_mul_le (add_le_add
              (picardAux_ofReal_sq_le_iSup_rat
                (X := fun t => stochInt 𝓖 μ B (picardFam φ (x, 0)) t ω) (h1 (x, 0)) ht)
              (picardAux_ofReal_sq_le_iSup_rat
                (X := fun t => stochInt 𝓖 μ B (picardFam φ (x, 1)) t ω) (h1 (x, 1)) ht)) 3))
              (picardBd_mul_le (mul_le_mul' (ENNReal.ofReal_le_ofReal ht.2)
                (lintegral_mono_set (Set.Ioc_subset_Ioc_right ht.2))) 3)
        _ = 3 * ∑' x, ENNReal.ofReal (‖ψ0 x‖ ^ 2) + 3 * ∑' k, Q n k ω +
              3 * (ENNReal.ofReal n *
                ∑' x, ∫⁻ u in Set.Ioc 0 (n : ℝ), ENNReal.ofReal (‖φ u ω x‖ ^ 2)) := by
            rw [picardIter_tsum_prod (fun k => Q n k ω)]
            simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        _ < ⊤ := by
            rw [← picardAux_ofReal_norm_sq]
            refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
              ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by norm_num) (h2 n)⟩,
              ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)⟩
            exact ((picardBd_tsum_J_le φ ω n).trans (picardBd_setLIntegral_le φ ω n)).trans_lt
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (picardBd_iSup_lt_top (hφ.continuous ω) n))
  -- the null set
  set N := toMeasurable μ Gᶜ with hNdef
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hG
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNG : ∀ ω, ω ∉ N → ω ∈ G := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hNt : ∀ t, MeasurableSet[𝓖 t] N := fun t =>
    nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0)
  have hmem : ∀ ω, ω ∈ G → ∀ t : ℝ≥0, Memℓp (fun x => c t ω x) 2 := by
    intro ω hω t
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    obtain ⟨g, hg, hgb⟩ := picardBd_bound_of_lt_top (c := fun t x => c t ω x) (hω.2 n)
    refine memℓp_gen ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact Summable.of_nonneg_of_le (fun x => by positivity) (fun x => hgb t ⟨t.2, hn⟩ x) hg
  -- the version
  set φ' : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω => if h : ω ∈ N then ψ0 else
    ⟨fun x => c (t.toNNReal : ℝ) ω x, hmem ω (hNG ω h) t.toNNReal⟩ with hφ'def
  have hφ'x : ∀ t ω x, φ' t ω x = if ω ∈ N then ψ0 x else c (t.toNNReal : ℝ) ω x := by
    intro t ω x
    by_cases h : ω ∈ N
    · simp [hφ'def, h]
    · simp [hφ'def, h]
  refine ⟨φ', ⟨fun t x => ?_, fun ω => ?_, fun ω t x hx => ?_, fun ω => ?_, fun T => ?_⟩, ?_⟩
  · -- adapted
    have e : (fun ω => φ' t ω x) = fun ω => if ω ∈ N then ψ0 x else c t ω x := by
      funext ω
      rw [hφ'x, Real.toNNReal_coe]
    rw [e]
    exact Measurable.ite (hNt t) measurable_const (hcm t x)
  · -- continuous
    by_cases h : ω ∈ N
    · have : (fun t : ℝ≥0 => φ' t ω) = fun _ => ψ0 := funext fun t => by
        simp [hφ'def, h]
      rw [this]
      exact continuous_const
    · have hωG := hNG ω h
      have hcont := picardBd_continuous_lp (c := fun t x => c t ω x) (hmem ω hωG) hωG.1
        (fun n => by
          obtain ⟨g, hg, hgb⟩ := picardBd_bound_of_lt_top (c := fun t x => c t ω x) (hωG.2 n)
          exact ⟨g, hg, fun t ht x => hgb t ⟨t.2, by exact_mod_cast ht⟩ x⟩)
      refine hcont.congr fun t => lp.ext (funext fun x => ?_)
      rw [hφ'x, ite_eq_right h, Real.toNNReal_coe]
  · -- support
    rw [hφ'x]
    split_ifs
    · exact hψ0 x hx
    · simp [hcdef, picardCoord, hx]
  · -- init
    refine lp.ext (funext fun x => ?_)
    rw [hφ'x]
    split_ifs
    · rfl
    · simp only [hcdef, picardCoord, Real.toNNReal_zero, NNReal.coe_zero]
      split_ifs with hx
      · simp [stochInt_of_nonpos B _ le_rfl]
      · exact (hψ0 x hx).symm
  · -- moment
    set J : Ω → ℝ≥0∞ := fun ω => ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖φ u ω‖ ^ 2) with hJ
    have hJm : Measurable J := picardBd_measurable_J hφ.adapted hφ.continuous T
    have hpt : ∀ᵐ ω ∂μ, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖φ' t ω‖ ^ 2)) ≤
        3 * ∑' k, S T k ω + (3 * ENNReal.ofReal (‖ψ0‖ ^ 2) + 3 * (ENNReal.ofReal T * J ω)) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
      refine iSup₂_le fun t ht => ?_
      rw [picardAux_ofReal_norm_sq]
      simp only [hφ'x, ite_eq_right hω, Real.coe_toNNReal _ ht.1]
      calc ∑' x, ENNReal.ofReal (‖c t ω x‖ ^ 2)
          ≤ ∑' x, (3 * ENNReal.ofReal (‖ψ0 x‖ ^ 2) + 3 * (S T (x, 0) ω + S T (x, 1) ω) +
              3 * (ENNReal.ofReal T *
                ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖φ u ω x‖ ^ 2))) := by
            refine ENNReal.tsum_le_tsum fun x => ?_
            refine (picardIter_coord_bound (hφ.continuous ω) ht.1 x).trans ?_
            exact add_le_add (add_le_add le_rfl (picardBd_mul_le (add_le_add
              (le_iSup₂_of_le (f := fun t _ =>
                ENNReal.ofReal (stochInt 𝓖 μ B (picardFam φ (x, 0)) t ω ^ 2)) t ht le_rfl)
              (le_iSup₂_of_le (f := fun t _ =>
                ENNReal.ofReal (stochInt 𝓖 μ B (picardFam φ (x, 1)) t ω ^ 2)) t ht le_rfl)) 3))
              (picardBd_mul_le (mul_le_mul' (ENNReal.ofReal_le_ofReal ht.2)
                (lintegral_mono_set (Set.Ioc_subset_Ioc_right ht.2))) 3)
        _ = 3 * ∑' x, ENNReal.ofReal (‖ψ0 x‖ ^ 2) + 3 * ∑' k, S T k ω +
              3 * (ENNReal.ofReal T *
                ∑' x, ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖φ u ω x‖ ^ 2)) := by
            rw [picardIter_tsum_prod (fun k => S T k ω)]
            simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        _ ≤ 3 * ENNReal.ofReal (‖ψ0‖ ^ 2) + 3 * ∑' k, S T k ω + 3 * (ENNReal.ofReal T * J ω) := by
            rw [← picardAux_ofReal_norm_sq]
            exact add_le_add le_rfl (picardBd_mul_le (picardBd_mul_le
              (picardBd_tsum_J_le φ ω T) _) 3)
        _ = _ := by ring
    refine (lintegral_mono_ae hpt).trans_lt ?_
    rw [lintegral_add_right (g := fun ω => 3 * ENNReal.ofReal (‖ψ0‖ ^ 2) +
      3 * (ENNReal.ofReal T * J ω)) _ (measurable_const.add (measurable_const.mul
      (measurable_const.mul hJm))), lintegral_const_mul' _ _ (by norm_num),
      lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, measure_univ, mul_one]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) (hSint T),
      ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top,
        ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (picardIter_lintegral_J_lt_top hφ T))⟩⟩
  · -- the version equals the Picard image almost surely
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t x
    rw [hφ'x, ite_eq_right hω, Real.toNNReal_coe]

/-- **Contraction estimate.** If `φ₁'`, `φ₂'` are admissible versions of the Picard images of
the admissible processes `φ₁`, `φ₂`, then for `0 ≤ t ≤ T`,
`𝔼 sup_{s ∈ [0,t]} ‖φ₁'_s - φ₂'_s‖² ≤ (16 + 2T) ∫_0^t 𝔼 sup_{u ∈ [0,s]} ‖φ₁_u - φ₂_u‖² ds`. -/
theorem picard_step_bound [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) {L : ℕ∞}
    {ψ0 : ℓ²(ℤ, ℂ)} {φ₁ φ₂ φ₁' φ₂' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h₁ : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 φ₁ μ)
    (h₂ : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 φ₂ μ)
    (h₁' : ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ), φ₁' t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 φ₁ t ω x)
    (h₂' : ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ), φ₂' t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 φ₂ t ω x)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal (‖φ₁' s ω - φ₂' s ω‖ ^ 2)) ∂μ ≤
      ENNReal.ofReal (16 + 2 * T) * ∫⁻ s in Set.Icc (0 : ℝ) t,
        ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ) s, ENNReal.ofReal (‖φ₁ u ω - φ₂ u ω‖ ^ 2)) ∂μ := by
  classical
  have hB' := hB.nullAug
  set 𝓖 := nullAug μ 𝓕 with h𝓖
  set D : ℝ → Ω → ℓ²(ℤ, ℂ) := fun s ω => φ₁ s ω - φ₂ s ω with hD
  have hDc : ∀ ω, Continuous fun t : ℝ≥0 => D t ω := fun ω =>
    (h₁.continuous ω).sub (h₂.continuous ω)
  have hDa : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => D t ω x := fun t x => by
    simp only [hD, lp.coeFn_sub, Pi.sub_apply]
    exact (h₁.adapted t x).sub (h₂.adapted t x)
  have hF₁ := picardIter_isItoIntegrable_fam h₁
  have hF₂ := picardIter_isItoIntegrable_fam h₂
  have hFeq : ∀ k, picardFam D k = fun i s ω => picardFam φ₁ k i s ω - picardFam φ₂ k i s ω := by
    intro k
    unfold picardFam
    split_ifs
    · funext i s ω; exact waveDiffRe_sub φ₁ φ₂ k.1 i s ω
    · funext i s ω; exact waveDiffIm_sub φ₁ φ₂ k.1 i s ω
  have hFD : ∀ k, IsItoIntegrable 𝓖 μ (picardFam D k) := fun k => by
    rw [hFeq]; exact itoProd_isItoIntegrable_sub (hF₁ k) (hF₂ k)
  have hsub : ∀ᵐ ω ∂μ, ∀ k (s : ℝ≥0), stochInt 𝓖 μ B (picardFam D k) s ω =
      stochInt 𝓖 μ B (picardFam φ₁ k) s ω - stochInt 𝓖 μ B (picardFam φ₂ k) s ω := by
    rw [ae_all_iff]
    intro k
    rw [hFeq]
    exact itoProd_stochInt_sub hB' (hF₁ k) (hF₂ k)
  set S : ℤ × Fin 2 → Ω → ℝ≥0∞ := fun k ω =>
    ⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal (stochInt 𝓖 μ B (picardFam D k) s ω ^ 2) with hSdef
  set J : Ω → ℝ≥0∞ := fun ω => ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖D u ω‖ ^ 2) with hJ
  have hJm : Measurable J := picardBd_measurable_J hDa hDc t
  have hpt : ∀ᵐ ω ∂μ, (⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal (‖φ₁' s ω - φ₂' s ω‖ ^ 2)) ≤
      2 * ∑' k, S k ω + 2 * (ENNReal.ofReal t * J ω) := by
    filter_upwards [h₁', h₂', hsub] with ω e₁ e₂ e₃
    refine iSup₂_le fun s hs => ?_
    rw [picardAux_ofReal_norm_sq]
    have hx : ∀ x, (φ₁' s ω - φ₂' s ω) x =
        picardCoord 𝓖 μ B L ψ0 φ₁ s ω x - picardCoord 𝓖 μ B L ψ0 φ₂ s ω x := fun x => by
      rw [lp.coeFn_sub, Pi.sub_apply]
      have a₁ := e₁ s.toNNReal x
      have a₂ := e₂ s.toNNReal x
      rw [Real.coe_toNNReal _ hs.1] at a₁ a₂
      rw [a₁, a₂]
    simp only [hx]
    have hR : ∀ x, stochInt 𝓖 μ B (waveDiffRe φ₁ x) s ω - stochInt 𝓖 μ B (waveDiffRe φ₂ x) s ω =
        stochInt 𝓖 μ B (picardFam D (x, 0)) s ω := fun x => by
      have := e₃ (x, 0) s.toNNReal
      rw [Real.coe_toNNReal _ hs.1] at this
      rw [this, picardFam_zero, picardFam_zero]
    have hI : ∀ x, stochInt 𝓖 μ B (waveDiffIm φ₁ x) s ω - stochInt 𝓖 μ B (waveDiffIm φ₂ x) s ω =
        stochInt 𝓖 μ B (picardFam D (x, 1)) s ω := fun x => by
      have := e₃ (x, 1) s.toNNReal
      rw [Real.coe_toNNReal _ hs.1] at this
      rw [this, picardFam_one, picardFam_one]
    have hDx : ∀ u x, φ₁ u ω x - φ₂ u ω x = D u ω x := fun u x => by
      simp only [hD, lp.coeFn_sub, Pi.sub_apply]
    calc ∑' x, ENNReal.ofReal
          (‖picardCoord 𝓖 μ B L ψ0 φ₁ s ω x - picardCoord 𝓖 μ B L ψ0 φ₂ s ω x‖ ^ 2)
        ≤ ∑' x, (2 * (S (x, 0) ω + S (x, 1) ω) +
            2 * (ENNReal.ofReal t * ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖D u ω x‖ ^ 2))) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          refine (picardIter_coord_sub_bound (h₁.continuous ω) (h₂.continuous ω) hs.1 x).trans ?_
          rw [hR, hI]
          simp only [hDx]
          exact add_le_add (picardBd_mul_le (add_le_add
            (le_iSup₂_of_le (f := fun s _ =>
              ENNReal.ofReal (stochInt 𝓖 μ B (picardFam D (x, 0)) s ω ^ 2)) s hs le_rfl)
            (le_iSup₂_of_le (f := fun s _ =>
              ENNReal.ofReal (stochInt 𝓖 μ B (picardFam D (x, 1)) s ω ^ 2)) s hs le_rfl)) 2)
            (picardBd_mul_le (mul_le_mul' (ENNReal.ofReal_le_ofReal hs.2)
              (lintegral_mono_set (Set.Ioc_subset_Ioc_right hs.2))) 2)
      _ = 2 * ∑' k, S k ω +
            2 * (ENNReal.ofReal t * ∑' x, ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖D u ω x‖ ^ 2)) := by
          rw [picardIter_tsum_prod (fun k => S k ω)]
          simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
      _ ≤ 2 * ∑' k, S k ω + 2 * (ENNReal.ofReal t * J ω) := by
          exact add_le_add le_rfl (picardBd_mul_le (picardBd_mul_le
            (picardBd_tsum_J_le D ω t) _) 2)
  have hconst : (16 : ℝ≥0∞) + 2 * ENNReal.ofReal t ≤ ENNReal.ofReal (16 + 2 * T) := by
    rw [ENNReal.ofReal_add (by norm_num) (by linarith), ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    gcongr
  calc ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, ENNReal.ofReal (‖φ₁' s ω - φ₂' s ω‖ ^ 2)) ∂μ
      ≤ ∫⁻ ω, (2 * ∑' k, S k ω + 2 * (ENNReal.ofReal t * J ω)) ∂μ := lintegral_mono_ae hpt
    _ = 2 * ∫⁻ ω, (∑' k, S k ω) ∂μ + 2 * (ENNReal.ofReal t * ∫⁻ ω, J ω ∂μ) := by
        rw [lintegral_add_right (g := fun ω => 2 * (ENNReal.ofReal t * J ω)) _
            (measurable_const.mul (measurable_const.mul hJm)),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ 2 * (4 * (2 * ∫⁻ ω, J ω ∂μ)) + 2 * (ENNReal.ofReal t * ∫⁻ ω, J ω ∂μ) := by
        gcongr
        exact (lintegral_tsum_iSup_stochInt_sq_le hB' hFD t).trans
          (by gcongr; exact picardIter_tsum_energy_le D t)
    _ = (16 + 2 * ENNReal.ofReal t) * ∫⁻ ω, J ω ∂μ := by ring
    _ ≤ ENNReal.ofReal (16 + 2 * T) * ∫⁻ ω, J ω ∂μ := by gcongr
    _ ≤ _ := by gcongr; exact picardBd_swap_le hDa hDc t

/-- **The Picard iterates**: admissible processes `φ⁽ᵐ⁾` for `𝓕ᵃ` with `φ⁽⁰⁾ = ψ₀` and, almost
surely, `φ⁽ᵐ⁺¹⁾_t(x) = Φ(φ⁽ᵐ⁾)_t(x)` for all `t ≥ 0` and `x`. -/
theorem picard_iterates [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞)
    (ψ0 : ℓ²(ℤ, ℂ)) (hψ0 : ∀ x, x ∉ box L → ψ0 x = 0) :
    ∃ φ : ℕ → ℝ → Ω → ℓ²(ℤ, ℂ), (∀ m, IsPicardAdmissible L (nullAug μ 𝓕) ψ0 (φ m) μ) ∧
      (∀ t ω, φ 0 t ω = ψ0) ∧
      ∀ m, ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ),
        φ (m + 1) t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 (φ m) t ω x := by
  classical
  let step : (ℝ → Ω → ℓ²(ℤ, ℂ)) → (ℝ → Ω → ℓ²(ℤ, ℂ)) := fun φ =>
    if h : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 φ μ then (picard_step_exists hB hψ0 h).choose
    else φ
  have hstep : ∀ ψ (h : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 ψ μ),
      step ψ = (picard_step_exists hB hψ0 h).choose := fun ψ h => by
    simp only [step, dite_eq_left h]
  have h0 : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 (fun _ _ => ψ0) μ := by
    refine ⟨fun t x => measurable_const, fun ω => continuous_const, fun ω t x hx => hψ0 x hx,
      fun ω => rfl, fun T => ?_⟩
    refine (lintegral_mono fun ω => iSup₂_le fun _ _ => le_rfl).trans_lt ?_
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  let φ : ℕ → ℝ → Ω → ℓ²(ℤ, ℂ) := fun m => step^[m] (fun _ _ => ψ0)
  have hadm : ∀ m, IsPicardAdmissible L (nullAug μ 𝓕) ψ0 (φ m) μ := by
    intro m
    induction m with
    | zero => exact h0
    | succ m ih =>
      have e : φ (m + 1) = step (φ m) := Function.iterate_succ_apply' _ _ _
      rw [e, hstep _ ih]
      exact (picard_step_exists hB hψ0 ih).choose_spec.1
  refine ⟨φ, hadm, fun t ω => rfl, fun m => ?_⟩
  have e : φ (m + 1) = (picard_step_exists hB hψ0 (hadm m)).choose := by
    rw [show φ (m + 1) = step (φ m) from Function.iterate_succ_apply' _ _ _, hstep _ (hadm m)]
  rw [e]
  exact (picard_step_exists hB hψ0 (hadm m)).choose_spec.2

end QSSEPtoKPZ
