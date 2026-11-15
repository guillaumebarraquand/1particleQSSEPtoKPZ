/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.NullAug
public import QSSEPtoKPZ.Martingales.Stopping
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A good version of the wave function; the localizing times `τ_R ∧ N` (package D, task D1)

See `docs/stage2-design.md`, Section 1.2 (a), point 3, and (e).

Let `ψ` be a wave function on `ℤ` (`IsWaveFunction ⊤ 𝓕 B ψ μ`). Its paths are continuous only
almost surely, and it is adapted to the raw filtration `𝓕`. We replace it by a version `ψ̃`:

* `IsGoodWave 𝓕 B ψ ψ̃ μ`: `ψ̃` is a wave function for the null augmentation
  `𝓕ᵃ = nullAug μ 𝓕`, *every* path `t ↦ ψ̃_t ∈ ℓ²(ℤ)` is continuous on `[0, ∞)`, `ψ̃_0 = e₀`
  for *every* `ω`, and `ψ̃` is indistinguishable from `ψ` (on `t ≥ 0`).
* `IsWaveFunction.exists_isGoodWave`: such a version exists. (Start from
  `IsWaveFunction.exists_good` and change the paths to the constant `e₀` on a measurable null set
  containing `{ψ_0 ≠ e₀}`; the equation at `t = 0` gives `ψ_0 = e₀` almost surely, since all
  Riemann sums vanish at `t = 0`.)
* `waveStop ψ̃ R N = τ_R ∧ N`, the first time `‖ψ̃_t‖_{ℓ²} ≥ R`, capped at `N`. It is a stopping
  time of `𝓕ᵃ` (`IsGoodWave.isStoppingTime_waveStop`), and `‖ψ̃_s‖ ≤ max R 1` for `s ≤ τ_R ∧ N`
  (`IsGoodWave.norm_le_of_le_waveStop`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- The initial condition `e₀ = 𝟙_{x = 0}` of the wave function, as an element of `ℓ²(ℤ)`. -/
def waveInit : ℓ²(ℤ, ℂ) := lp.single 2 0 1

/-- The coordinates of `e₀`: `e₀(x) = 𝟙_{x = 0}`. -/
lemma waveInit_apply (x : ℤ) : waveInit x = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; simp [waveInit]
  · simp [waveInit, hx]

/-- `‖e₀‖_{ℓ²} = 1`. -/
lemma norm_waveInit : ‖waveInit‖ = 1 := by
  rw [waveInit, lp.norm_single (by norm_num)]
  simp

/-- `‖f‖_{ℓ²} = (∑ₓ |f(x)|²)^{1/2}`. -/
lemma lp2_norm_eq_sqrt_tsum (f : ℓ²(ℤ, ℂ)) : ‖f‖ = Real.sqrt (∑' x, ‖f x‖ ^ 2) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- `Λ_∞ = ℤ`: every site belongs to the box `box ⊤`. -/
lemma waveBox_top_mem (x : ℤ) : x ∈ box ⊤ := by
  simp [box]

/-- For `L = ∞` every site has two neighbours: `D(x,x) = 2`. -/
lemma waveDegree_top (x : ℤ) : degree ⊤ x = 2 := by
  simp [degree, waveBox_top_mem]

/-- **Good version of the wave function.** `IsGoodWave 𝓕 B ψ ψ' μ` means that `ψ'` is a wave
function on `ℤ` for the null augmentation `𝓕ᵃ = nullAug μ 𝓕` of `𝓕`, all of whose paths are
continuous on `[0, ∞)` and start from `e₀`, and which is indistinguishable from `ψ` on
`[0, ∞)`. -/
structure IsGoodWave (𝓕 : Filtration ℝ≥0 mΩ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ)
    (ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop where
  /-- `ψ'` is a wave function on `ℤ` for `𝓕ᵃ`. -/
  wave : IsWaveFunction ⊤ (nullAug μ 𝓕) B ψ' μ
  /-- Every path `t ↦ ψ'_t` is continuous from `[0, ∞)` to `ℓ²(ℤ)`. -/
  continuous : ∀ ω, Continuous fun t : ℝ≥0 => ψ' t ω
  /-- Every path starts from `e₀`. -/
  init : ∀ ω, ψ' 0 ω = waveInit
  /-- `ψ'` is indistinguishable from `ψ` on `[0, ∞)`. -/
  ae_eq : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω

/-- The Riemann sums `itoSum` vanish at time `t = 0`. -/
private lemma itoSum_zero_time (f W : ℝ → Ω → ℂ) (m : ℕ) (ω : Ω) : itoSum f W 0 m ω = 0 := by
  simp [itoSum]

/-- A wave function on `ℤ` starts from `e₀`, almost surely (the equation at `t = 0`). -/
lemma IsWaveFunction.ae_init {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) :
    ∀ᵐ ω ∂μ, ψ 0 ω = waveInit := by
  have hx : ∀ x : ℤ, ∀ᵐ ω ∂μ, ψ 0 ω x = waveInit x := by
    intro x
    have h := hψ.sde 0 x (waveBox_top_mem x)
    simp only [NNReal.coe_zero, itoSum_zero_time, mul_zero, add_zero,
      intervalIntegral.integral_same] at h
    have h0 : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => (0 : ℂ)) atTop (fun _ => (0 : ℂ)) :=
      tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero (by simp)
    filter_upwards [tendstoInMeasure_ae_unique h h0] with ω hω
    rw [waveInit_apply]
    exact sub_eq_zero.1 hω
  filter_upwards [ae_all_iff.2 hx] with ω hω
  exact lp.ext (funext hω)

/-- **Existence of a good version.** Every wave function `ψ` on `ℤ` for `𝓕` has a good version
`ψ'` (`IsGoodWave`): a wave function for `𝓕ᵃ`, indistinguishable from `ψ`, with all paths
continuous and starting from `e₀`. -/
theorem IsWaveFunction.exists_isGoodWave {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) : ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsGoodWave 𝓕 B ψ ψ' μ := by
  classical
  obtain ⟨ψ₁, hw, hc, -, hae⟩ := hψ.exists_good
  set N := toMeasurable μ {ω | ψ₁ 0 ω ≠ waveInit} with hNdef
  have hN0 : μ N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 (hw.ae_init.mono fun ω h => by simpa using h)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω, ω ∉ N → ψ₁ 0 ω = waveInit := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  set ψ' : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω => if ω ∈ N then waveInit else ψ₁ t ω with hψ'
  have h11 : ∀ᵐ ω ∂μ, ∀ t : ℝ, ψ' t ω = ψ₁ t ω := by
    filter_upwards [hNa] with ω hω t; simp [ψ', hω]
  refine ⟨ψ', ⟨⟨fun t x => ?_, ae_of_all _ fun ω => ?_, ae_of_all _ fun ω t x hx =>
    absurd (waveBox_top_mem x) hx, fun t x hx => ?_⟩, fun ω => ?_, fun ω => ?_, ?_⟩⟩
  · have e : (fun ω => ψ' t ω x) = fun ω => if ω ∈ N then waveInit x else ψ₁ t ω x := by
      ext ω; by_cases hω : ω ∈ N <;> simp [ψ', hω]
    rw [e]
    exact Measurable.ite (nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0))
      measurable_const (hw.adapted t x)
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact continuous_const
    · simp only [ψ', hω, ite_false]; exact hc ω
  · refine (hw.sde t x hx).congr (fun m => ?_) ?_
    · filter_upwards [h11] with ω hω
      simp only [itoSum, hω]
    · filter_upwards [h11] with ω hω
      simp only [hω]
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact continuous_const
    · simp only [ψ', hω, ite_false]; exact hc ω
  · by_cases hω : ω ∈ N
    · simp [ψ', hω]
    · simp only [ψ', hω, ite_false]; exact hgood ω hω
  · filter_upwards [h11, hae] with ω h1 h2 t
    rw [h1, h2]

namespace IsGoodWave

variable {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The coordinates `ψ'_t(x)` are `𝓕ᵃ_t`-measurable. -/
lemma measurable_apply (h : IsGoodWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => ψ' t ω x :=
  h.wave.adapted t x

/-- `Re ψ'_t(x)` is `𝓕ᵃ_t`-measurable. -/
lemma measurable_re (h : IsGoodWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => (ψ' t ω x).re :=
  Complex.measurable_re.comp (h.measurable_apply t x)

/-- `Im ψ'_t(x)` is `𝓕ᵃ_t`-measurable. -/
lemma measurable_im (h : IsGoodWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => (ψ' t ω x).im :=
  Complex.measurable_im.comp (h.measurable_apply t x)

/-- The norm `‖ψ'_t‖_{ℓ²}` is `𝓕ᵃ_t`-measurable. -/
lemma measurable_norm (h : IsGoodWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) :
    Measurable[nullAug μ 𝓕 t] fun ω => ‖ψ' t ω‖ := by
  simp only [lp2_norm_eq_sqrt_tsum]
  have hm : ∀ x, Measurable[nullAug μ 𝓕 t] fun ω => ‖ψ' t ω x‖ ^ 2 := fun x =>
    (continuous_norm.pow 2).measurable.comp (h.measurable_apply t x)
  exact Real.continuous_sqrt.measurable.comp
    (@Measurable.tsum Ω ℝ ℤ (nullAug μ 𝓕 t) _ _ _ _ _ _ _ _ _ _ _ _ hm)

/-- Every path `t ↦ ψ'_t(x)` is continuous on `[0, ∞)`. -/
lemma continuous_apply (h : IsGoodWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => ψ' t ω x :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (h.continuous ω)

/-- Every path `t ↦ Re ψ'_t(x)` is continuous on `[0, ∞)`. -/
lemma continuous_re (h : IsGoodWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => (ψ' t ω x).re :=
  Complex.continuous_re.comp (h.continuous_apply ω x)

/-- Every path `t ↦ Im ψ'_t(x)` is continuous on `[0, ∞)`. -/
lemma continuous_im (h : IsGoodWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => (ψ' t ω x).im :=
  Complex.continuous_im.comp (h.continuous_apply ω x)

/-- Every path `t ↦ ‖ψ'_t‖_{ℓ²}` is continuous on `[0, ∞)`. -/
lemma continuous_norm (h : IsGoodWave 𝓕 B ψ ψ' μ) (ω : Ω) :
    Continuous fun t : ℝ≥0 => ‖ψ' t ω‖ :=
  (h.continuous ω).norm

/-- `ψ'_0(x) = 𝟙_{x = 0}` for every `ω`. -/
lemma init_apply (h : IsGoodWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    ψ' 0 ω x = if x = 0 then 1 else 0 := by
  rw [h.init ω, waveInit_apply]

/-- If `ψ'` is a good version of `ψ` and `ψ₀` is indistinguishable from `ψ`, then `ψ'` is also a
good version of `ψ₀`. -/
lemma congr_left {ψ₀ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsGoodWave 𝓕 B ψ ψ' μ)
    (h0 : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ t ω = ψ₀ t ω) : IsGoodWave 𝓕 B ψ₀ ψ' μ :=
  ⟨h.wave, h.continuous, h.init, by filter_upwards [h.ae_eq, h0] with ω h1 h2 t; rw [h1, h2]⟩

end IsGoodWave

/-! ### The localizing times `τ_R ∧ N` -/

/-- `τ_R ∧ N`: the first time `t ≥ 0` at which `‖ψ'_t‖_{ℓ²} ≥ R`, capped at `N`. -/
def waveStop (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (R : ℝ) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hitTime (fun t ω => ‖ψ' t ω‖) R N ω

/-- `τ_R ∧ N ≤ N`. -/
lemma waveStop_le (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (R : ℝ) (N : ℝ≥0) (ω : Ω) : waveStop ψ' R N ω ≤ N :=
  hitTime_le _ _ _ _

/-- `τ_R ∧ N` is a stopping time of the augmented filtration `𝓕ᵃ`. -/
theorem IsGoodWave.isStoppingTime_waveStop {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsGoodWave 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0) :
    IsStoppingTime (nullAug μ 𝓕) (fun ω => (waveStop ψ' R N ω : WithTop ℝ≥0)) :=
  isStoppingTime_hitTime (X := fun t ω => ‖ψ' t ω‖) (fun t => h.measurable_norm t)
    (fun ω => h.continuous_norm ω) R N

/-- **Bound before `τ_R ∧ N`.** For `0 ≤ s ≤ τ_R ∧ N`, `‖ψ'_s‖_{ℓ²} ≤ max R 1` (and `≤ R` when
`R ≥ 1`; when `R < 1`, `τ_R = 0` since `‖ψ'_0‖ = 1`). -/
theorem IsGoodWave.norm_le_of_le_waveStop {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsGoodWave 𝓕 B ψ ψ' μ) {R : ℝ} {N : ℝ≥0} {ω : Ω} {s : ℝ} (hs0 : 0 ≤ s)
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
theorem IsGoodWave.norm_apply_le_of_le_waveStop {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsGoodWave 𝓕 B ψ ψ' μ) {R : ℝ} {N : ℝ≥0} {ω : Ω} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ waveStop ψ' R N ω) (x : ℤ) : ‖ψ' s ω x‖ ≤ max R 1 :=
  (lp.norm_apply_le_norm two_ne_zero _ x).trans (h.norm_le_of_le_waveStop hs0 hs)

end QSSEPtoKPZ
