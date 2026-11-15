/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.WaveIto

/-!
# Identification of a wave function on `Λ_L` as an Itô process, every `L` (task L3)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L3.
`docs/stage5-design.md`, Section 1.2 (b) and note on L3: copy-adapt Stage 2's
`WaveFunction/Good.lean` and `WaveFunction/Identification.lean` with the drift `-D_L(x,x)/2` and
the support clause (decision D9‴: the Stage 2 files are not modified).

* `IsGoodWaveBox L 𝓕 B ψ ψ' μ`: `ψ'` is a version of the wave function `ψ` on `Λ_L` which is a
  wave function for the augmented filtration `𝓕ᵃ = nullAug μ 𝓕`, all of whose paths are
  continuous, vanish outside `Λ_L` and start from `e₀` (the `L`-analogue of Stage 2's
  `IsGoodWave`).
* `IsWaveFunction.exists_isGoodWaveBox`: it exists.
* `IsGoodWaveBox.isItoProcessUpTo_re/im`: for `x ∈ Λ_L`, `Re ψ'(x)`, `Im ψ'(x)` are Itô processes
  up to `τ_R ∧ N` (`waveStop ψ' R N`) for `𝓕ᵃ`, with drift `-(D_L(x,x)/2) ψ'(x)` and the
  coefficients `waveDiffRe ψ' x`, `waveDiffIm ψ' x`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- **Good version of the wave function on `Λ_L`.** `ψ'` is a wave function on `Λ_L` for the
null augmentation `𝓕ᵃ = nullAug μ 𝓕`, all of whose paths are continuous on `[0, ∞)`, vanish
outside `Λ_L` and start from `e₀`, and which is indistinguishable from `ψ` on `[0, ∞)`. -/
structure IsGoodWaveBox (L : ℕ∞) (𝓕 : Filtration ℝ≥0 mΩ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ)
    (ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop where
  /-- `ψ'` is a wave function on `Λ_L` for `𝓕ᵃ`. -/
  wave : IsWaveFunction L (nullAug μ 𝓕) B ψ' μ
  /-- Every path `t ↦ ψ'_t` is continuous from `[0, ∞)` to `ℓ²(ℤ)`. -/
  continuous : ∀ ω, Continuous fun t : ℝ≥0 => ψ' t ω
  /-- Every path vanishes outside `Λ_L`. -/
  support : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ' t ω x = 0
  /-- Every path starts from `e₀`. -/
  init : ∀ ω, ψ' 0 ω = waveInit
  /-- `ψ'` is indistinguishable from `ψ` on `[0, ∞)`. -/
  ae_eq : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω

/-- `0 ∈ Λ_L` for every `L`. -/
private lemma boxIdent_zero_mem (L : ℕ∞) : (0 : ℤ) ∈ box L := by
  simp [box]

/-- `e₀` vanishes outside `Λ_L`. -/
private lemma boxIdent_waveInit_of_notMem {L : ℕ∞} {x : ℤ} (hx : x ∉ box L) : waveInit x = 0 := by
  have : x ≠ 0 := fun h => hx (h ▸ boxIdent_zero_mem L)
  simp [waveInit_apply, this]

/-- The Riemann sums `itoSum` vanish at time `t = 0`. -/
private lemma boxIdent_itoSum_zero_time (f W : ℝ → Ω → ℂ) (m : ℕ) (ω : Ω) :
    itoSum f W 0 m ω = 0 := by
  simp [itoSum]

/-- A wave function on `Λ_L` starts from `e₀`, almost surely (every `L`; for `L = ∞` this is
Stage 2's `IsWaveFunction.ae_init`). -/
theorem IsWaveFunction.ae_init_box {L : ℕ∞} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hψ : IsWaveFunction L 𝓕 B ψ μ) : ∀ᵐ ω ∂μ, ψ 0 ω = waveInit := by
  have hx : ∀ x : ℤ, ∀ᵐ ω ∂μ, ψ 0 ω x = waveInit x := by
    intro x
    by_cases hxL : x ∈ box L
    · have h := hψ.sde 0 x hxL
      simp only [NNReal.coe_zero, boxIdent_itoSum_zero_time, mul_zero, add_zero,
        intervalIntegral.integral_same] at h
      have h0 : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => (0 : ℂ)) atTop (fun _ => (0 : ℂ)) :=
        tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero (by simp)
      filter_upwards [tendstoInMeasure_ae_unique h h0] with ω hω
      rw [waveInit_apply]
      exact sub_eq_zero.1 hω
    · filter_upwards [hψ.support] with ω hω
      rw [boxIdent_waveInit_of_notMem hxL]
      exact hω 0 x hxL
  filter_upwards [ae_all_iff.2 hx] with ω hω
  exact lp.ext (funext hω)

/-- **Existence of a good version on `Λ_L`** (every `L`). -/
theorem IsWaveFunction.exists_isGoodWaveBox {L : ℕ∞} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hψ : IsWaveFunction L 𝓕 B ψ μ) : ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsGoodWaveBox L 𝓕 B ψ ψ' μ := by
  classical
  obtain ⟨ψ₁, hw, hc, hsupp, hae⟩ := hψ.exists_good
  set N := toMeasurable μ {ω | ψ₁ 0 ω ≠ waveInit} with hNdef
  have hN0 : μ N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 (hw.ae_init_box.mono fun ω h => by simpa using h)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω, ω ∉ N → ψ₁ 0 ω = waveInit := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  set ψ' : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω => if ω ∈ N then waveInit else ψ₁ t ω with hψ'
  have h11 : ∀ᵐ ω ∂μ, ∀ t : ℝ, ψ' t ω = ψ₁ t ω := by
    filter_upwards [hNa] with ω hω t; simp [ψ', hω]
  have hsupp' : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ' t ω x = 0 := by
    intro ω t x hx
    by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact boxIdent_waveInit_of_notMem hx
    · simp only [ψ', hω, ite_false]; exact hsupp ω t x hx
  have hcont : ∀ ω, Continuous fun t : ℝ≥0 => ψ' t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact continuous_const
    · simp only [ψ', hω, ite_false]; exact hc ω
  refine ⟨ψ', ⟨⟨fun t x => ?_, ae_of_all _ hcont, ae_of_all _ hsupp', fun t x hx => ?_⟩,
    hcont, hsupp', fun ω => ?_, ?_⟩⟩
  · have e : (fun ω => ψ' t ω x) = fun ω => if ω ∈ N then waveInit x else ψ₁ t ω x := by
      ext ω; by_cases hω : ω ∈ N <;> simp [ψ', hω]
    rw [e]
    exact Measurable.ite (nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0))
      measurable_const (hw.adapted t x)
  · refine (hw.sde t x hx).congr (fun m => ?_) ?_
    · filter_upwards [h11] with ω hω
      simp only [itoSum, hω]
    · filter_upwards [h11] with ω hω
      simp only [hω]
  · by_cases hω : ω ∈ N
    · simp [ψ', hω]
    · simp only [ψ', hω, ite_false]; exact hgood ω hω
  · filter_upwards [h11, hae] with ω h1 h2 t
    rw [h1, h2]

namespace IsGoodWaveBox

variable {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The coordinates `ψ'_t(x)` are `𝓕ᵃ_t`-measurable. -/
lemma measurable_apply (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => ψ' t ω x :=
  h.wave.adapted t x

/-- `Re ψ'_t(x)` is `𝓕ᵃ_t`-measurable. -/
lemma measurable_re (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => (ψ' t ω x).re :=
  Complex.measurable_re.comp (h.measurable_apply t x)

/-- `Im ψ'_t(x)` is `𝓕ᵃ_t`-measurable. -/
lemma measurable_im (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => (ψ' t ω x).im :=
  Complex.measurable_im.comp (h.measurable_apply t x)

/-- The norm `‖ψ'_t‖_{ℓ²}` is `𝓕ᵃ_t`-measurable. -/
lemma measurable_norm (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (t : ℝ≥0) :
    Measurable[nullAug μ 𝓕 t] fun ω => ‖ψ' t ω‖ := by
  simp only [lp2_norm_eq_sqrt_tsum]
  have hm : ∀ x, Measurable[nullAug μ 𝓕 t] fun ω => ‖ψ' t ω x‖ ^ 2 := fun x =>
    (continuous_norm.pow 2).measurable.comp (h.measurable_apply t x)
  exact Real.continuous_sqrt.measurable.comp
    (@Measurable.tsum Ω ℝ ℤ (nullAug μ 𝓕 t) _ _ _ _ _ _ _ _ _ _ _ _ hm)

/-- Every path `t ↦ ψ'_t(x)` is continuous on `[0, ∞)`. -/
lemma continuous_apply (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => ψ' t ω x :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (h.continuous ω)

/-- Every path `t ↦ Re ψ'_t(x)` is continuous on `[0, ∞)`. -/
lemma continuous_re (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => (ψ' t ω x).re :=
  Complex.continuous_re.comp (h.continuous_apply ω x)

/-- Every path `t ↦ Im ψ'_t(x)` is continuous on `[0, ∞)`. -/
lemma continuous_im (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => (ψ' t ω x).im :=
  Complex.continuous_im.comp (h.continuous_apply ω x)

/-- Every path `t ↦ ‖ψ'_t‖_{ℓ²}` is continuous on `[0, ∞)`. -/
lemma continuous_norm (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (ω : Ω) :
    Continuous fun t : ℝ≥0 => ‖ψ' t ω‖ :=
  (h.continuous ω).norm

/-- `ψ'_0(x) = 𝟙_{x = 0}` for every `ω`. -/
lemma init_apply (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    ψ' 0 ω x = if x = 0 then 1 else 0 := by
  rw [h.init ω, waveInit_apply]

end IsGoodWaveBox

/-- `τ_R ∧ N` is a stopping time of `𝓕ᵃ` for a good version. -/
theorem IsGoodWaveBox.isStoppingTime_waveStop {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0) :
    IsStoppingTime (nullAug μ 𝓕) (fun ω => (waveStop ψ' R N ω : WithTop ℝ≥0)) :=
  isStoppingTime_hitTime (X := fun t ω => ‖ψ' t ω‖) (fun t => h.measurable_norm t)
    (fun ω => h.continuous_norm ω) R N

/-- **Bound before `τ_R ∧ N`.** For `0 ≤ s ≤ τ_R ∧ N`, `‖ψ'_s‖_{ℓ²} ≤ max R 1` (and `≤ R` when
`R ≥ 1`; when `R < 1`, `τ_R = 0` since `‖ψ'_0‖ = 1`). -/
theorem IsGoodWaveBox.norm_le_of_le_waveStop {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) {R : ℝ} {N : ℝ≥0} {ω : Ω} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ waveStop ψ' R N ω) : ‖ψ' s ω‖ ≤ max R 1 := by
  have hX0 : ‖ψ' 0 ω‖ = 1 := by rw [h.init ω, norm_waveInit]
  set s' : ℝ≥0 := ⟨s, hs0⟩ with hs'
  have hss : (s' : ℝ) = s := rfl
  have hle : s' ≤ waveStop ψ' R N ω := by rw [← NNReal.coe_le_coe, hss]; exact hs
  rcases le_or_gt 1 R with hR | hR
  · have := le_of_le_hitTime (X := fun t ω => ‖ψ' t ω‖) (h.continuous_norm ω)
      (by simpa [hX0] using hR) hle
    rw [hss] at this
    exact this.trans (le_max_left _ _)
  · -- `R < 1 = ‖ψ'_0‖`, so `τ_R = 0` and `s = 0`
    have h0 : waveStop ψ' R N ω ≤ 0 := inf_le_left.trans (csInf_le (OrderBot.bddBelow _)
      (Or.inl (show R ≤ ‖ψ' ((0 : ℝ≥0) : ℝ) ω‖ by simpa [hX0] using hR.le)))
    have : s = 0 := le_antisymm (by exact_mod_cast hs.trans (NNReal.coe_le_coe.2 h0)) hs0
    rw [this, hX0]
    exact le_max_right _ _

/-- **Coordinates before `τ_R ∧ N`.** For `0 ≤ s ≤ τ_R ∧ N` and every `x`,
`|ψ'_s(x)| ≤ max R 1`. -/
theorem IsGoodWaveBox.norm_apply_le_of_le_waveStop {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsGoodWaveBox L 𝓕 B ψ ψ' μ) {R : ℝ} {N : ℝ≥0} {ω : Ω} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ waveStop ψ' R N ω) (x : ℤ) : ‖ψ' s ω x‖ ≤ max R 1 :=
  (lp.norm_apply_le_norm two_ne_zero _ x).trans (h.norm_le_of_le_waveStop hs0 hs)

/-- A function continuous on `[0, ∞)` (as a function of `t : ℝ≥0`) is continuous on `Ici 0`. -/
private lemma boxIdent_continuousOn {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) : ContinuousOn f (Set.Ici 0) :=
  (hf.comp continuous_real_toNNReal).continuousOn.congr fun r hr => by
    simp [Real.coe_toNNReal _ (Set.mem_Ici.1 hr)]

/-- The limit in the frozen equation, for a good version on `Λ_L`: `∫_0^t ψ'(x)` commutes with
`Re`, `Im`. -/
private lemma boxIdent_limit {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hg : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) (ω : Ω) :
    (ψ' t ω x - (if x = 0 then 1 else 0) +
        (degree L x : ℂ) / 2 * ∫ s in (0 : ℝ)..t, ψ' s ω x) =
      ((ψ' t ω x).re - (ψ' 0 ω x).re +
          (degree L x : ℝ) / 2 * (∫ s in (0 : ℝ)..t, (ψ' s ω x).re) : ℝ) +
        Complex.I * ((ψ' t ω x).im - (ψ' 0 ω x).im +
          (degree L x : ℝ) / 2 * (∫ s in (0 : ℝ)..t, (ψ' s ω x).im) : ℝ) := by
  have hii : IntervalIntegrable (fun s => ψ' s ω x) volume 0 t := by
    refine ContinuousOn.intervalIntegrable
      ((boxIdent_continuousOn (hg.continuous_apply ω x)).mono ?_)
    rw [Set.uIcc_of_le (NNReal.coe_nonneg _)]
    exact Set.Icc_subset_Ici_self
  have hre : (∫ s in (0 : ℝ)..t, (ψ' s ω x).re) = (∫ s in (0 : ℝ)..t, ψ' s ω x).re :=
    Complex.reCLM.intervalIntegral_comp_comm hii
  have him : (∫ s in (0 : ℝ)..t, (ψ' s ω x).im) = (∫ s in (0 : ℝ)..t, ψ' s ω x).im :=
    Complex.imCLM.intervalIntegral_comp_comm hii
  rw [hre, him, hg.init_apply ω x]
  apply Complex.ext <;> split_ifs <;> simp

/-- `|Re z / √2| ≤ |z|` and `|Im z / √2| ≤ |z|`. -/
private lemma boxIdent_div_sqrt_two (z : ℂ) :
    |z.re / Real.sqrt 2| ≤ ‖z‖ ∧ |z.im / Real.sqrt 2| ≤ ‖z‖ := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  simp only [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2)]
  exact ⟨(div_le_self (abs_nonneg _) h2).trans (Complex.abs_re_le_norm z),
    (div_le_self (abs_nonneg _) h2).trans (Complex.abs_im_le_norm z)⟩

/-- **Identification, real part, every `L`.** For a good version `ψ'` on `Λ_L`, `x ∈ Λ_L`,
`R ∈ ℝ`, `N ≥ 0`: `Re ψ'(x)` is an Itô process up to `τ_R ∧ N` for `𝓕ᵃ`, with drift
`-(D_L(x,x)/2) Re ψ'(x)` and diffusion coefficients `waveDiffRe ψ' x`. -/
theorem IsGoodWaveBox.isItoProcessUpTo_re [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (hg : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0)
    {x : ℤ} (hx : x ∈ box L) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (waveStop ψ' R N) (fun t ω => (ψ' t ω x).re)
      (fun s ω => -((degree L x : ℝ) / 2) * (ψ' s ω x).re) (waveDiffRe ψ' x) := by
  have hdiv := boxIdent_div_sqrt_two
  refine isItoProcessUpTo_of_riemann hB.nullAug (hg.isStoppingTime_waveStop R N) (waveSites x)
    (K := max R 1) (fun i hi s ω => waveDiffRe_of_notMem ψ' hi s ω) ?_ ?_ ?_
    (fun ω => hg.continuous_re ω x) (fun ω => continuous_const.mul (hg.continuous_re ω x))
    fun t => ?_
  · intro i ω s hs0 hs
    have hb := fun y => hg.norm_apply_le_of_le_waveStop hs0 hs y
    simp only [waveDiffRe]
    split_ifs
    · rw [neg_div, abs_neg]; exact (hdiv _).2.trans (hb _)
    · rw [neg_div, abs_neg]; exact (hdiv _).1.trans (hb _)
    · rw [neg_div, abs_neg]; exact (hdiv _).2.trans (hb _)
    · exact (hdiv _).1.trans (hb _)
    · rw [abs_zero]; exact zero_le_one.trans (le_max_right _ _)
  · intro i t
    unfold waveDiffRe
    split_ifs
    · exact ((hg.measurable_im t _).neg).div_const _
    · exact ((hg.measurable_re t _).neg).div_const _
    · exact ((hg.measurable_im t _).neg).div_const _
    · exact (hg.measurable_re t _).div_const _
    · exact measurable_const
  · intro i ω
    simp only [waveDiffRe]
    split_ifs
    · exact ((hg.continuous_im ω _).neg).div_const _
    · exact ((hg.continuous_re ω _).neg).div_const _
    · exact ((hg.continuous_im ω _).neg).div_const _
    · exact (hg.continuous_re ω _).div_const _
    · exact continuous_const
  · have h := (tendstoInMeasure_complex_iff μ).1 (hg.wave.sde t x hx) |>.1
    refine h.congr (fun m => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (sum_realRiemann_waveDiffRe ψ' B x t m ω).symm
    · rw [boxIdent_limit hg t x ω]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, intervalIntegral.integral_const_mul]
      ring

/-- **Identification, imaginary part, every `L`** (as `IsGoodWaveBox.isItoProcessUpTo_re`). -/
theorem IsGoodWaveBox.isItoProcessUpTo_im [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {L : ℕ∞} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} (hg : IsGoodWaveBox L 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0)
    {x : ℤ} (hx : x ∈ box L) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (waveStop ψ' R N) (fun t ω => (ψ' t ω x).im)
      (fun s ω => -((degree L x : ℝ) / 2) * (ψ' s ω x).im) (waveDiffIm ψ' x) := by
  have hdiv := boxIdent_div_sqrt_two
  refine isItoProcessUpTo_of_riemann hB.nullAug (hg.isStoppingTime_waveStop R N) (waveSites x)
    (K := max R 1) (fun i hi s ω => waveDiffIm_of_notMem ψ' hi s ω) ?_ ?_ ?_
    (fun ω => hg.continuous_im ω x) (fun ω => continuous_const.mul (hg.continuous_im ω x))
    fun t => ?_
  · intro i ω s hs0 hs
    have hb := fun y => hg.norm_apply_le_of_le_waveStop hs0 hs y
    simp only [waveDiffIm]
    split_ifs
    · exact (hdiv _).1.trans (hb _)
    · rw [neg_div, abs_neg]; exact (hdiv _).2.trans (hb _)
    · exact (hdiv _).1.trans (hb _)
    · exact (hdiv _).2.trans (hb _)
    · rw [abs_zero]; exact zero_le_one.trans (le_max_right _ _)
  · intro i t
    unfold waveDiffIm
    split_ifs
    · exact (hg.measurable_re t _).div_const _
    · exact ((hg.measurable_im t _).neg).div_const _
    · exact (hg.measurable_re t _).div_const _
    · exact (hg.measurable_im t _).div_const _
    · exact measurable_const
  · intro i ω
    simp only [waveDiffIm]
    split_ifs
    · exact (hg.continuous_re ω _).div_const _
    · exact ((hg.continuous_im ω _).neg).div_const _
    · exact (hg.continuous_re ω _).div_const _
    · exact (hg.continuous_im ω _).div_const _
    · exact continuous_const
  · have h := (tendstoInMeasure_complex_iff μ).1 (hg.wave.sde t x hx) |>.2
    refine h.congr (fun m => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (sum_realRiemann_waveDiffIm ψ' B x t m ω).symm
    · rw [boxIdent_limit hg t x ω]
      simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, intervalIntegral.integral_const_mul]
      ring

end QSSEPtoKPZ
