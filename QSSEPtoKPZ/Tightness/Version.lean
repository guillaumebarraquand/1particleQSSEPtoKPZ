/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.MartingalesBounds
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.Martingales.NullAug
public import QSSEPtoKPZ.Tightness.FiniteMeasureEmbed
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# A continuous measurable version of `t ↦ 𝖹_n(t)` (task Q3)

See `docs/stage3-design.md`, Sections 1.2 (f) and 2.6.

On a good path of the tilted field (`TiltGood n T ψ ω`: the `t ↦ 𝔷_n(t,x)` are continuous on
`[0,T]` and `𝔷_n(t,x) ≤ K e^{-|x|}` there), the measures `𝖹_n(t) = ∑ₓ 𝔷_n(t,x) δ_{y_n(t,x)}`
of (3.5) are finite, `∫ φ d𝖹_n(t) = ∑ₓ 𝔷_n(t,x) φ(y_n(t,x))` for bounded continuous `φ`, and
`t ↦ 𝖹_n(t)` is continuous for the weak topology on `[0,T]` (Weierstrass M-test: the article's
argument, "uniformly convergent sum of continuous functions").

* `tiltVerFM`: `𝖹_n(t)` as an element of `ℳ₊(ℝ) = FiniteMeasure ℝ` (and `0` when
  `∑ₓ 𝔷_n(t,x)` diverges).
* `tiltVer_continuousOn_pairZ`, `tiltVer_continuous_path`: continuity on good paths.
* `exists_tiltedPath_version_bcf`, `exists_tiltedPath_version`: a version on `[0,T]` with all
  paths continuous, measurable for the Borel σ-algebra of `C([0,T], ℳ₊(ℝ))`, whose test
  integrals `ω ↦ ∫ φ d Zv(ω)(t)` are measurable for `𝓕ⁿ_t` augmented by the null sets.
* `exists_rescaledPath_version`: the corresponding version of the measures `𝒵_n(t)` of
  Theorem 1.2, `𝒵_n(t) = ϱ_n(t) 𝖹_n(t)` (3.8).
* `tiltVer_ae_continuous`: almost surely, `t ↦ 𝖹_n(t)` is continuous on `[0, ∞)`.

The integral formula is proved here directly (not through `integral_tiltedMeasure` of task Q1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-! ### The measure `𝖹_n(t)` and its integrals -/

/-- The total mass of `𝖹_n(t)`: `𝖹_n(t)(ℝ) = ∑ₓ ofReal 𝔷_n(t,x)`. -/
private lemma tiltVer_univ (n : ℝ) (ω : Ω) (t : ℝ) :
    tiltedMeasure n ψ ω t univ = ∑' x, ENNReal.ofReal (zN n ψ ω t x) := by
  simp [tiltedMeasure, Measure.sum_apply _ MeasurableSet.univ]

/-- If `∑ₓ 𝔷_n(t,x) < ∞`, the measure `𝖹_n(t)` of (3.5) is finite. -/
lemma tiltVer_isFiniteMeasure {n t : ℝ} {ω : Ω} (hs : Summable (zN n ψ ω t)) :
    IsFiniteMeasure (tiltedMeasure n ψ ω t) := by
  refine ⟨?_⟩
  rw [tiltVer_univ, ← ENNReal.ofReal_tsum_of_nonneg (fun x => tiltZ_nonneg n ω t x) hs]
  exact ENNReal.ofReal_lt_top

/-- `∫ φ d𝖹_n(t) = ∑ₓ 𝔷_n(t,x) φ(y_n(t,x)) = 𝖹_n(t;φ)` for `φ` bounded continuous, when
`∑ₓ 𝔷_n(t,x) < ∞`. -/
lemma tiltVer_integral {n t : ℝ} {ω : Ω} (hs : Summable (zN n ψ ω t)) (f : ℝ →ᵇ ℝ) :
    ∫ y, f y ∂(tiltedMeasure n ψ ω t) = pairZ n ψ ω t f := by
  have := tiltVer_isFiniteMeasure hs
  have hi : Integrable f (tiltedMeasure n ψ ω t) := f.integrable _
  rw [tiltedMeasure] at hi ⊢
  rw [integral_sum_measure hi]
  unfold pairZ
  congr 1
  funext x
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (tiltZ_nonneg n ω t x),
    smul_eq_mul]

open Classical in
/-- `𝖹_n(t)` as an element of `ℳ₊(ℝ) = FiniteMeasure ℝ`, when `∑ₓ 𝔷_n(t,x) < ∞`
(and `0` otherwise). -/
def tiltVerFM (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) : FiniteMeasure ℝ :=
  if hs : Summable (zN n ψ ω t) then ⟨tiltedMeasure n ψ ω t, tiltVer_isFiniteMeasure hs⟩ else 0

lemma tiltVerFM_coe {n t : ℝ} {ω : Ω} (hs : Summable (zN n ψ ω t)) :
    (tiltVerFM n ψ ω t : Measure ℝ) = tiltedMeasure n ψ ω t := by
  simp [tiltVerFM, hs]

lemma tiltVerFM_integral {n t : ℝ} {ω : Ω} (hs : Summable (zN n ψ ω t)) (f : ℝ →ᵇ ℝ) :
    ∫ y, f y ∂(tiltVerFM n ψ ω t : Measure ℝ) = pairZ n ψ ω t f := by
  rw [tiltVerFM_coe hs, tiltVer_integral hs]

/-! ### Continuity on good paths -/

/-- `t ↦ y_n(t,x)` is continuous. -/
private lemma tiltVer_continuous_pos (n : ℝ) (x : ℤ) :
    Continuous fun t => rescaledPosition n t x := by
  unfold rescaledPosition; fun_prop

/-- On a good path, `t ↦ 𝖹_n(t;φ) = ∑ₓ 𝔷_n(t,x) φ(y_n(t,x))` is continuous on `[0,T]` for `φ`
bounded continuous (Weierstrass M-test, with the bound `‖φ‖_∞ K e^{-|x|}`). -/
lemma tiltVer_continuousOn_pairZ {n T : ℝ} {ω : Ω} (h : TiltGood n T ψ ω) (f : ℝ →ᵇ ℝ) :
    ContinuousOn (fun t => pairZ n ψ ω t f) (Icc 0 T) := by
  obtain ⟨K, hK0, hK⟩ := h.dom
  unfold pairZ
  refine continuousOn_tsum (fun x => (h.cont x).mul
      (f.continuous.comp (tiltVer_continuous_pos n x)).continuousOn)
    (tilt_summable_exp_neg_abs.mul_left (‖f‖ * K)) fun x t ht => ?_
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (tiltZ_nonneg n ω t x)]
  calc zN n ψ ω t x * ‖f (rescaledPosition n t x)‖ ≤ (K * Real.exp (-|(x : ℝ)|)) * ‖f‖ :=
        mul_le_mul (hK t ht x) (f.norm_coe_le_norm _) (norm_nonneg _)
          (mul_nonneg hK0 (Real.exp_pos _).le)
    _ = ‖f‖ * K * Real.exp (-|(x : ℝ)|) := by ring

/-- On a good path, `t ↦ 𝖹_n(t)` is continuous from `[0,T]` to `ℳ₊(ℝ)` (weak topology). -/
lemma tiltVer_continuous_path {n T : ℝ} {ω : Ω} (h : TiltGood n T ψ ω) :
    Continuous fun t : Icc (0 : ℝ) T => tiltVerFM n ψ ω t := by
  refine FiniteMeasure.continuous_iff_forall_continuous_integral.2 fun f => ?_
  have e : (fun t : Icc (0 : ℝ) T => ∫ y, f y ∂(tiltVerFM n ψ ω t : Measure ℝ)) =
      (Icc (0 : ℝ) T).domRestrict fun t => pairZ n ψ ω t f := by
    funext t
    exact tiltVerFM_integral (h.summable t.2) f
  rw [e]
  exact (tiltVer_continuousOn_pairZ h f).domRestrict

open Classical in
/-- The path `t ↦ 𝖹_n(t)` on `[0,T]` as an element of `C([0,T], ℳ₊(ℝ))`, on good paths
(the constant path `0` otherwise). -/
def tiltVerPath (n T : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) : C(Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  if h : TiltGood n T ψ ω then ⟨fun t => tiltVerFM n ψ ω t, tiltVer_continuous_path h⟩ else 0

lemma tiltVerPath_apply {n T : ℝ} {ω : Ω} (h : TiltGood n T ψ ω) (t : Icc (0 : ℝ) T) :
    tiltVerPath n T ψ ω t = tiltVerFM n ψ ω t := by
  simp [tiltVerPath, h]

/-! ### Measurability -/

/-- `ω ↦ 𝔷_n(t,x)` is `𝓕ⁿ_t`-measurable (`𝓕ⁿ_t = 𝓕_{nt/2}`), for `t ≥ 0`. -/
lemma tiltVer_zN_adapted (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (x : ℤ) :
    Measurable[filtN n 𝓕 t.toNNReal] fun ω => zN n ψ ω t x := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have h := hψ.adapted ((n / 2).toNNReal * t.toNNReal) x
  have e : (((n / 2).toNNReal * t.toNNReal : ℝ≥0) : ℝ) = n * t / 2 := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ ht]; ring
  rw [e] at h
  change Measurable[𝓕 ((n / 2).toNNReal * t.toNNReal)] _
  unfold zN density
  exact measurable_const.mul ((continuous_norm.pow 2).measurable.comp h)

/-- The partial sums `∑_{|x| ≤ N} 𝔷_n(t,x) φ(y_n(t,x))`. -/
private def tiltVerPartial (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (f : ℝ → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ x ∈ Finset.Icc (-(N : ℤ)) N, zN n ψ ω t x * f (rescaledPosition n t x)

/-- On a set `S` of the augmented filtration on which `∑ₓ 𝔷_n(t,x)` converges,
`ω ↦ 𝟙_S(ω) 𝖹_n(t;φ)` is `𝓕ⁿ_t ∨ σ(null sets)`-measurable (limit of finite sums). -/
private lemma tiltVer_indicator_measurable (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) {S : Set Ω} (hS : MeasurableSet[nullAug μ (filtN n 𝓕) t.toNNReal] S)
    (hsum : ∀ ω ∈ S, Summable (zN n ψ ω t)) (f : ℝ →ᵇ ℝ) :
    Measurable[nullAug μ (filtN n 𝓕) t.toNNReal]
      (S.indicator fun ω => pairZ n ψ ω t f) := by
  refine @measurable_of_tendsto_metrizable Ω ℝ (nullAug μ (filtN n 𝓕) t.toNNReal) _ _ _ _
    (fun N => S.indicator (tiltVerPartial n ψ t f N)) _ (fun N => ?_) ?_
  · refine Measurable.indicator ?_ hS
    refine Finset.measurable_sum _ fun x _ => ?_
    exact ((tiltVer_zN_adapted hψ hn ht x).mono (le_nullAug μ (filtN n 𝓕) _) le_rfl).mul_const _
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ S
    · simp only [indicator_of_mem hω]
      have hs : Summable fun x => zN n ψ ω t x * f (rescaledPosition n t x) := by
        refine Summable.of_norm_bounded ((hsum ω hω).mul_left ‖f‖) fun x => ?_
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (tiltZ_nonneg n ω t x), mul_comm]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (tiltZ_nonneg n ω t x)
      exact hs.hasSum.comp Finset.tendsto_Icc_neg
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds

/-- **A version of `t ↦ 𝖹_n(t)` on `[0,T]`**, for every bounded continuous test function:
there is `Zv : Ω → C([0,T], ℳ₊(ℝ))` (every path continuous), measurable for the Borel σ-algebra
of `C([0,T], ℳ₊(ℝ))`, such that `ω ↦ ∫ φ dZv(ω)(t)` is measurable for `𝓕ⁿ_t ∨ σ(null sets)`
for every `t ∈ [0,T]` and every bounded continuous `φ`, and almost surely `Zv(ω)(t) = 𝖹_n(t)`
for all `t ∈ [0,T]`. -/
theorem exists_tiltedPath_version_bcf [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable Zv ∧
      (∀ (t : Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
        Measurable[nullAug μ (filtN n 𝓕) (t : ℝ).toNNReal]
          fun ω => ∫ x, f x ∂(Zv ω t : Measure ℝ)) ∧
      ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t := by
  classical
  -- the good set `S`: measurable, of full measure, contained in `{TiltGood n T ψ ·}`
  set S : Set Ω := (toMeasurable μ {ω | ¬ TiltGood n T ψ ω})ᶜ with hS_def
  have hbad : μ {ω | ¬ TiltGood n T ψ ω} = 0 := by
    have := ae_tiltGood hB hψ hn
    rw [ae_iff] at this
    refine measure_mono_null (fun ω hω => ?_) this
    simp only [mem_ofPred_eq, not_forall] at hω ⊢
    exact ⟨T, hω⟩
  have hSc : μ Sᶜ = 0 := by rw [hS_def, compl_compl, measure_toMeasurable, hbad]
  have hSgood : ∀ ω ∈ S, TiltGood n T ψ ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable μ _ h)
  have hSm : ∀ s : ℝ≥0, MeasurableSet[nullAug μ (filtN n 𝓕) s] S := fun s => by
    have : MeasurableSet[nullAug μ (filtN n 𝓕) s] Sᶜ :=
      nullSets_le_nullAug s _ (measurableSet_nullSets (by
        rw [hS_def, compl_compl]; exact measurableSet_toMeasurable μ _) hSc)
    simpa using this.compl
  refine ⟨fun ω => if ω ∈ S then tiltVerPath n T ψ ω else 0, ?_⟩
  -- the test integrals
  have hint : ∀ (t : Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
      (fun ω => ∫ x, f x ∂((if ω ∈ S then tiltVerPath n T ψ ω else 0) t : Measure ℝ)) =
        S.indicator fun ω => pairZ n ψ ω t f := by
    intro t f
    funext ω
    by_cases hω : ω ∈ S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hω), indicator_of_mem hω, tiltVerPath_apply (hSgood ω hω),
        tiltVerFM_integral ((hSgood ω hω).summable t.2)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hω), indicator_of_notMem hω]
      simp
  have hadapt : ∀ (t : Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
      Measurable[nullAug μ (filtN n 𝓕) (t : ℝ).toNNReal]
        fun ω => ∫ x, f x ∂((if ω ∈ S then tiltVerPath n T ψ ω else 0) t : Measure ℝ) := by
    intro t f
    rw [hint t f]
    exact tiltVer_indicator_measurable hψ hn t.2.1 (hSm _)
      (fun ω hω => (hSgood ω hω).summable t.2) f
  refine ⟨?_, hadapt, ?_⟩
  · refine measurable_pathFiniteMeasure_iff_tightEmb.2 fun t j => ?_
    exact (hadapt t (bumpTest j)).mono ((nullAug μ (filtN n 𝓕)).le _) le_rfl
  · have : ∀ᵐ ω ∂μ, ω ∈ S := by
      rw [ae_iff]; exact hSc
    filter_upwards [this] with ω hω t
    rw [ite_eq_left_of_eq_true _ _ (eq_true hω), tiltVerPath_apply (hSgood ω hω), tiltVerFM_coe ((hSgood ω hω).summable t.2)]

/-- **The version of `t ↦ 𝖹_n(t)` on `[0,T]`** (`docs/stage3-design.md`, Section 2.6): a map
`Zv : Ω → C([0,T], ℳ₊(ℝ))` (every path continuous), measurable for the Borel σ-algebra of
`C([0,T], ℳ₊(ℝ))`, whose test integrals `ω ↦ ∫ f_j dZv(ω)(t)` are measurable for
`𝓕ⁿ_t ∨ σ(null sets)`, and with, almost surely, `Zv(ω)(t) = 𝖹_n(t)` for all `t ∈ [0,T]`. -/
theorem exists_tiltedPath_version [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable Zv ∧
      (∀ (t : Icc (0 : ℝ) T) (j : ℕ), Measurable[nullAug μ (filtN n 𝓕) (t : ℝ).toNNReal]
        fun ω => ∫ x, bumpTest j x ∂(Zv ω t : Measure ℝ)) ∧
      ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t := by
  obtain ⟨Zv, hm, ha, he⟩ := exists_tiltedPath_version_bcf hB hψ hn T
  exact ⟨Zv, hm, fun t j => ha t (bumpTest j), he⟩

/-! ### Continuity on `[0, ∞)` -/

/-- **Continuity of `t ↦ 𝖹_n(t)` on `[0, ∞)`**: almost surely there is a continuous
`γ : [0, ∞) → ℳ₊(ℝ)` with `γ(t) = 𝖹_n(t)` for every `t ≥ 0`. -/
theorem tiltVer_ae_continuous [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, ∃ γ : C(ℝ≥0, FiniteMeasure ℝ), ∀ t : ℝ≥0,
      (γ t : Measure ℝ) = tiltedMeasure n ψ ω t := by
  filter_upwards [ae_tiltGood hB hψ hn] with ω hω
  have hs : ∀ t : ℝ≥0, Summable (zN n ψ ω t) := fun t => (hω t).summable ⟨t.2, le_rfl⟩
  have hc : Continuous fun t : ℝ≥0 => tiltVerFM n ψ ω t := by
    refine FiniteMeasure.continuous_iff_forall_continuous_integral.2 fun f => ?_
    have e : (fun t : ℝ≥0 => ∫ y, f y ∂(tiltVerFM n ψ ω t : Measure ℝ)) =
        fun t : ℝ≥0 => pairZ n ψ ω t f := funext fun t => tiltVerFM_integral (hs t) f
    rw [e, continuous_iff_continuousAt]
    intro t₀
    have h1 : ContinuousWithinAt (fun t => pairZ n ψ ω t f) (Icc 0 (t₀ + 1)) t₀ :=
      tiltVer_continuousOn_pairZ (hω _) f _ ⟨t₀.2, by linarith⟩
    have h2 := h1.comp NNReal.continuous_coe.continuousWithinAt (mapsTo_preimage _ _)
    refine h2.continuousAt (mem_of_superset (Iio_mem_nhds (lt_add_one t₀)) fun t ht => ?_)
    exact ⟨t.2, by have : t < t₀ + 1 := ht; exact_mod_cast this.le⟩
  exact ⟨⟨_, hc⟩, fun t => tiltVerFM_coe (hs t)⟩

/-! ### The measures `𝒵_n(t)` of Theorem 1.2 -/

/-- **A version of `t ↦ 𝒵_n(t)` on `[0,T]`** (the measures of Theorem 1.2, `rescaledMeasure ⊤`):
`t ↦ ϱ_n(t) Zv(ω)(t)`, with `Zv` the version of `exists_tiltedPath_version_bcf`, by (3.8)
`𝒵_n(t) = ϱ_n(t) 𝖹_n(t)` (`rescaledMeasure_eq`). -/
theorem exists_rescaledPath_version [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable Zv ∧
      ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ) T,
        (Zv ω t : Measure ℝ) = rescaledMeasure ⊤ n (density ψ ω) t := by
  obtain ⟨Zv, -, ha, he⟩ := exists_tiltedPath_version_bcf hB hψ hn T
  set c : C(Icc (0 : ℝ) T, ℝ≥0) := ⟨fun t => (varrhoN n t).toNNReal, by
    unfold varrhoN; fun_prop⟩ with hc_def
  refine ⟨fun ω => ⟨fun t => c t • Zv ω t, by fun_prop⟩, ?_, ?_⟩
  · refine measurable_pathFiniteMeasure_iff_tightEmb.2 fun t j => ?_
    have e : (fun ω => ∫ x, bumpTest j x ∂((⟨fun t => c t • Zv ω t, by fun_prop⟩ :
          C(Icc (0 : ℝ) T, FiniteMeasure ℝ)) t : Measure ℝ)) =
        fun ω => (c t : ℝ) * ∫ x, bumpTest j x ∂(Zv ω t : Measure ℝ) := by
      funext ω
      simp only [ContinuousMap.coe_mk, FiniteMeasure.toMeasure_smul]
      rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    rw [e]
    exact ((ha t (bumpTest j)).mono ((nullAug μ (filtN n 𝓕)).le _) le_rfl).const_mul _
  · filter_upwards [he] with ω hω t
    simp only [ContinuousMap.coe_mk, FiniteMeasure.toMeasure_smul]
    rw [rescaledMeasure_eq hn, hω t, hc_def]
    simp only [ContinuousMap.coe_mk]
    rfl

end QSSEPtoKPZ
