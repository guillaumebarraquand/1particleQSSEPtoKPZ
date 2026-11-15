/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.Replacement.Mollifier
public import QSSEPtoKPZ.LimitPoints.MollifyCont
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Densities of limit points (task G3)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G3
(except `limDensity_nonneg`, proved here). See `docs/stage4-design.md`, Sections 1.2 (e) and
3.2, and `docs/stage4-interfaces.md`.

Proof of Proposition 7.1 (2), with the change of argument of 1.2 (e): from a bound
`|μ(f)| ≤ C ‖f‖₂` on `f ∈ C_c(ℝ)` one gets (Riesz) a density in `L²`, and Lebesgue's
differentiation theorem for the mollifiers `ρ_{1/k}` identifies it with `limDensity`.
Also: joint measurability and predictability of `limField`, and Fatou's bound on its `L²` norm.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- `limDensity` is nonnegative (it is the real part of an element of `[0, ∞]`). -/
theorem limDensity_nonneg (ρ : ℝ → ℝ) (μ : FiniteMeasure ℝ) (x : ℝ) : 0 ≤ limDensity ρ μ x :=
  ENNReal.toReal_nonneg

/-! ### Auxiliary results -/

section DensAux

variable {ρ : ℝ → ℝ}

/-- `ρ_ε` is even. -/
private lemma dens_rhoEps_neg (hρ : IsMollifier ρ) (ε z : ℝ) : rhoEps ρ ε (-z) = rhoEps ρ ε z := by
  simp only [rhoEps, neg_div, hρ.even]

/-- `(γ, t) ↦ γ(t)` is continuous (evaluation is continuous on `C([0,T], ℳ₊)`). -/
private lemma dens_continuous_pathAt {T : ℝ} :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => pathAt p.1 p.2 := by
  unfold pathAt
  by_cases hT : 0 ≤ T
  · simp only [hT, ↓reduceDIte]
    exact continuous_eval.comp (continuous_fst.prodMk
      ((continuous_projIcc (a := 0) (b := T) (h := hT)).comp continuous_snd))
  · simp only [hT, ↓reduceDIte]
    exact continuous_const

/-- The mollified measure `x ↦ (μ ⋆ ρ_ε)(x)` is continuous. -/
private lemma dens_continuous_conv (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (μ : FiniteMeasure ℝ) :
    Continuous fun x => ∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ) :=
  (densFM_continuous_conv hρ hε).comp (continuous_const.prodMk continuous_id)

/-- `(μ ⋆ ρ_ε) ≥ 0`. -/
private lemma dens_conv_nonneg (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (μ : FiniteMeasure ℝ)
    (x : ℝ) : 0 ≤ ∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ) :=
  integral_nonneg fun _ => mollif_rhoEps_nonneg hρ hε.le _

/-- `‖μ ⋆ ρ_ε‖₂² = smoothedNormSq μ 1 ρ ε`, and `(μ ⋆ ρ_ε)²` is integrable. -/
private lemma dens_smoothedNormSq_eq (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (μ : FiniteMeasure ℝ) :
    Integrable (fun x => (∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ)) ^ 2) ∧
      smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ ε =
        ∫ x, (∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ)) ^ 2 := by
  have h := (smoothedNormSq_eq hρ (μ : Measure ℝ) (φ := fun _ => 1) continuous_const
    ⟨1, fun _ => by simp⟩ hε).1
  simp only [one_mul] at h
  refine ⟨h, ?_⟩
  simp only [smoothedNormSq, one_mul]

/-- Fatou's bound, in the form of `lintegral_limDensity_sq_le` (proved first, as it is used in
`withDensity_limDensity_of_bound`). -/
private lemma dens_lintegral_sq_le (hρ : IsMollifier ρ) (μ : FiniteMeasure ℝ) :
    ∫⁻ x, ENNReal.ofReal (limDensity ρ μ x ^ 2) ≤
      liminf (fun k : ℕ => ENNReal.ofReal
        (smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ (1 / ((k : ℝ) + 1)))) atTop := by
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  set a : ℕ → ℝ → ℝ≥0∞ := fun k x => ENNReal.ofReal
    (∫ y, rhoEps ρ (1 / ((k : ℝ) + 1)) (x - y) ∂(μ : Measure ℝ)) with ha
  have hpt : ∀ x, ENNReal.ofReal (limDensity ρ μ x ^ 2) ≤ liminf (fun k => a k x ^ 2) atTop := by
    intro x
    have hL : limDensity ρ μ x = (liminf (fun k => a k x) atTop).toReal := rfl
    rw [hL, ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    calc ENNReal.ofReal (liminf (fun k => a k x) atTop).toReal ^ 2
        ≤ (liminf (fun k => a k x) atTop) ^ 2 := pow_le_pow_left' ENNReal.ofReal_toReal_le 2
      _ = liminf (fun k => a k x ^ 2) atTop :=
          Monotone.map_liminf_of_continuousAt (f := fun t : ℝ≥0∞ => t ^ 2)
            (fun s t h => pow_le_pow_left' h 2) _ (ENNReal.continuous_pow 2).continuousAt
  calc ∫⁻ x, ENNReal.ofReal (limDensity ρ μ x ^ 2)
      ≤ ∫⁻ x, liminf (fun k => a k x ^ 2) atTop := lintegral_mono hpt
    _ ≤ liminf (fun k => ∫⁻ x, a k x ^ 2) atTop :=
        lintegral_liminf_le' fun k => ((ENNReal.measurable_ofReal.comp
          (dens_continuous_conv hρ (hε k) μ).measurable).pow_const 2).aemeasurable
    _ = _ := by
        congr 1
        funext k
        obtain ⟨hi, he⟩ := dens_smoothedNormSq_eq hρ (hε k) μ
        rw [he, ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
        refine lintegral_congr fun x => ?_
        rw [ha, ← ENNReal.ofReal_pow (dens_conv_nonneg hρ (hε k) μ x)]

/-- The positive part of the constant: `C₊ = max C 0`. -/
private lemma dens_bound_pos {μ : FiniteMeasure ℝ} {C : ℝ}
    (hC : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ))
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    |∫ x, f x ∂(μ : Measure ℝ)| ≤ max C 0 * Real.sqrt (∫ x, f x ^ 2) := by
  rw [Real.sqrt_eq_rpow]
  exact (hC f hf hfc).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _))

/-- The cutoff `χ_n(x) = max(0, min(1, n + 1 - |x|))`. -/
private def densCut (n : ℕ) (x : ℝ) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - |x|))

/-- `χ_n` is continuous. -/
private lemma densCut_continuous (n : ℕ) : Continuous (densCut n) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

/-- `0 ≤ χ_n ≤ 1`. -/
private lemma densCut_mem (n : ℕ) (x : ℝ) : 0 ≤ densCut n x ∧ densCut n x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- `χ_n` vanishes outside `[-(n+1), n+1]`. -/
private lemma densCut_hasCompactSupport (n : ℕ) : HasCompactSupport (densCut n) :=
  HasCompactSupport.intro (isCompact_Icc (a := -((n : ℝ) + 1)) (b := (n : ℝ) + 1)) fun x hx => by
    have : (n : ℝ) + 1 < |x| := by
      by_contra h
      exact hx (abs_le.1 (not_lt.1 h))
    exact max_eq_left ((min_le_right _ _).trans (by linarith))

/-- `χ_n(x) = 1` for `n ≥ |x|`. -/
private lemma densCut_eq_one {n : ℕ} {x : ℝ} (h : |x| ≤ n) : densCut n x = 1 := by
  rw [densCut, min_eq_left (by linarith), max_eq_right zero_le_one]

/-- **Extension of the bound** from `C_c` to bounded continuous square integrable functions:
`|∫ h dμ| ≤ C₊ ‖h‖₂` (cut off by `χ_n` and let `n → ∞`, dominated convergence). -/
private lemma dens_bound_extend {μ : FiniteMeasure ℝ} {C : ℝ}
    (hC : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ))
    {h : ℝ → ℝ} (hh : Continuous h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (hh2 : Integrable fun x => h x ^ 2) :
    |∫ x, h x ∂(μ : Measure ℝ)| ≤ max C 0 * Real.sqrt (∫ x, h x ^ 2) := by
  have hn : ∀ n : ℕ, |∫ x, h x * densCut n x ∂(μ : Measure ℝ)| ≤
      max C 0 * Real.sqrt (∫ x, h x ^ 2) := by
    intro n
    refine (dens_bound_pos hC (hh.mul (densCut_continuous n))
      ((densCut_hasCompactSupport n).mul_left)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (le_max_right _ _)
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hh2
      (ae_of_all _ fun x => ?_)
    obtain ⟨h0, h1⟩ := densCut_mem n x
    simp only [Pi.mul_apply]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ h0 h1)
  have hlim : Tendsto (fun n : ℕ => ∫ x, h x * densCut n x ∂(μ : Measure ℝ)) atTop
      (𝓝 (∫ x, h x ∂(μ : Measure ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hh.mul (densCut_continuous n)).aestronglyMeasurable) (integrable_const B)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · obtain ⟨h0, h1⟩ := densCut_mem n x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      exact (mul_le_of_le_one_right (abs_nonneg _) h1).trans (hB x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with n hn
      rw [densCut_eq_one ((Nat.le_ceil _).trans (by exact_mod_cast hn)), mul_one]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hn

/-- `(μ ⋆ ρ_ε)` is integrable (Tonelli: its integral is the mass of `μ`). -/
private lemma dens_conv_integrable (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (μ : FiniteMeasure ℝ) :
    Integrable fun x => ∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ) := by
  have hr := mollif_rhoEps_continuous hρ ε
  refine ⟨(dens_continuous_conv hρ hε μ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (dens_conv_nonneg hρ hε μ))]
  have hint : ∀ x, Integrable (fun y => rhoEps ρ ε (x - y)) (μ : Measure ℝ) := fun x =>
    Integrable.of_bound (hr.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (mollifSup ρ / ε) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]; exact mollif_abs_rhoEps_le hρ hε _)
  calc ∫⁻ x, ENNReal.ofReal (∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (rhoEps ρ ε (x - y)) ∂(μ : Measure ℝ) := by
        refine lintegral_congr fun x => ?_
        exact ofReal_integral_eq_lintegral_ofReal (hint x)
          (ae_of_all _ fun _ => mollif_rhoEps_nonneg hρ hε.le _)
    _ = ∫⁻ y, (∫⁻ x, ENNReal.ofReal (rhoEps ρ ε (x - y))) ∂(μ : Measure ℝ) :=
        lintegral_lintegral_swap (f := fun x y => ENNReal.ofReal (rhoEps ρ ε (x - y)))
          (ENNReal.measurable_ofReal.comp
          (hr.comp (continuous_fst.sub continuous_snd)).measurable).aemeasurable
    _ = ∫⁻ _, 1 ∂(μ : Measure ℝ) := by
        refine lintegral_congr fun y => ?_
        exact mollif_lintegral_rhoEps_sub hρ hε y
    _ < ∞ := by simp

/-- **`L²` bound on mollified measures** under the duality bound: `‖μ ⋆ ρ_ε‖₂² ≤ C₊²`.
Writing `u = μ ⋆ ρ_ε` and `h = ρ_ε ⋆ u`: `∫ u² = ∫ h dμ ≤ C₊ ‖h‖₂ ≤ C₊ ‖u‖₂` (Fubini, the
extended bound and Young's inequality). -/
private lemma dens_smoothedNormSq_le {μ : FiniteMeasure ℝ} {C : ℝ}
    (hρ : IsMollifier ρ)
    (hC : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ ε ≤ max C 0 ^ 2 := by
  set u : ℝ → ℝ := fun x => ∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ) with hu
  obtain ⟨hu2, he⟩ := dens_smoothedNormSq_eq hρ hε μ
  rw [he]
  have huc : Continuous u := dens_continuous_conv hρ hε μ
  have hui : Integrable u := dens_conv_integrable hρ hε μ
  have hr := mollif_rhoEps_continuous hρ ε
  set M := mollifSup ρ / ε
  have hM : ∀ z, |rhoEps ρ ε z| ≤ M := mollif_abs_rhoEps_le hρ hε
  set h : ℝ → ℝ := fun y => ∫ x, rhoEps ρ ε (y - x) * u x with hh
  -- `h` is continuous and bounded
  have hhc : Continuous h := by
    refine continuous_of_dominated (bound := fun x => M * |u x|)
      (fun y => ((hr.comp (continuous_const.sub continuous_id)).mul huc).aestronglyMeasurable)
      (fun y => ae_of_all _ fun x => ?_) (hui.abs.const_mul M)
      (ae_of_all _ fun x => (hr.comp (continuous_id.sub continuous_const)).mul continuous_const)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  have hhb : ∀ y, |h y| ≤ M * ∫ x, |u x| := by
    intro y
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (integral_mono
      (mollif_integrable_mul hρ hε huc.aestronglyMeasurable hu2 y).norm (hui.abs.const_mul M)
      fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  -- Young: `∫ h² ≤ ∫ u²`
  have hY := mollif_lintegral_sq_le hρ hε huc.measurable hu2
  have hufin : ∫⁻ x, ENNReal.ofReal (u x ^ 2) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hu2 (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hh2 : Integrable fun y => h y ^ 2 :=
    ⟨(hhc.pow 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun _ => sq_nonneg _)).2 (hY.trans_lt hufin)⟩
  have hhu : ∫ y, h y ^ 2 ≤ ∫ x, u x ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hhc.pow 2).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (huc.pow 2).aestronglyMeasurable]
    exact ENNReal.toReal_mono hufin.ne hY
  -- Fubini: `∫ u² = ∫ h dμ`
  have hF : ∫ x, u x ^ 2 = ∫ y, h y ∂(μ : Measure ℝ) := by
    have hint : Integrable (fun p : ℝ × ℝ => u p.1 * rhoEps ρ ε (p.1 - p.2))
        (volume.prod (μ : Measure ℝ)) := by
      refine (hui.mul_prod (integrable_const M)).mono'
        (((huc.comp continuous_fst).mul (hr.comp (continuous_fst.sub continuous_snd)))
          |>.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dens_conv_nonneg hρ hε μ p.1)]
      exact mul_le_mul_of_nonneg_left (hM _) (dens_conv_nonneg hρ hε μ p.1)
    calc ∫ x, u x ^ 2 = ∫ x, ∫ y, u x * rhoEps ρ ε (x - y) ∂(μ : Measure ℝ) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only
          rw [integral_const_mul, sq]
      _ = ∫ y, (∫ x, u x * rhoEps ρ ε (x - y)) ∂(μ : Measure ℝ) :=
          integral_integral_swap (f := fun x y => u x * rhoEps ρ ε (x - y)) hint
      _ = ∫ y, h y ∂(μ : Measure ℝ) := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [hh]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only
          rw [mul_comm, ← dens_rhoEps_neg hρ, neg_sub]
  -- conclusion: `S ≤ C₊ √S`
  have hS0 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hb := dens_bound_extend hC hhc hhb hh2
  have h1 : ∫ x, u x ^ 2 ≤ max C 0 * Real.sqrt (∫ x, u x ^ 2) := by
    rw [hF]
    exact (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hF ▸ hhu)) (le_max_right _ _)))
  set S := ∫ x, u x ^ 2
  have hs := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have : Real.sqrt S ≤ max C 0 := by nlinarith
  nlinarith

/-- **Absolute continuity** under the duality bound: `μ(K) ≤ ∫ f dμ ≤ C₊ ‖f‖₂ ≤ C₊ |U|^{1/2}`
for a compact Lebesgue-null `K`, an open `U ⊇ K` and an Urysohn function `1_K ≤ f ≤ 1_U`. -/
private lemma dens_absolutelyContinuous {μ : FiniteMeasure ℝ} {C : ℝ}
    (hC : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ)) :
    (μ : Measure ℝ) ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [hs.measure_eq_iSup_isCompact (μ : Measure ℝ)]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKs hK
  have hK0 : volume K = 0 := measure_mono_null hKs hs0
  have hbd : ∀ δ : ℝ, 0 < δ → (μ : Measure ℝ).real K ≤ max C 0 * Real.sqrt δ := by
    intro δ hδ
    obtain ⟨U, hKU, hU, hUδ⟩ := Set.exists_isOpen_lt_of_lt K (ENNReal.ofReal δ)
      (by rw [hK0]; exact ENNReal.ofReal_pos.2 hδ)
    obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK
      hU.isClosed_compl (Set.disjoint_compl_right_iff_subset.2 hKU)
    have hfi : Integrable (fun x => f x) (μ : Measure ℝ) :=
      Integrable.of_bound f.continuous.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]; exact (hf01 x).2)
    have hUfin : volume U < ∞ := hUδ.trans ENNReal.ofReal_lt_top
    have h1 : (μ : Measure ℝ).real K ≤ ∫ x, f x ∂(μ : Measure ℝ) := by
      rw [← integral_indicator_one hK.measurableSet]
      refine integral_mono ((integrable_const 1).indicator hK.measurableSet) hfi fun x => ?_
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, hf1 hx]
      · rw [Set.indicator_of_notMem hx]; exact (hf01 x).1
    have h2 : ∫ x, f x ^ 2 ≤ δ := by
      calc ∫ x, f x ^ 2 ≤ ∫ x, U.indicator 1 x :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
              ((integrable_indicator_iff hU.measurableSet).2
                (integrableOn_const (C := (1 : ℝ)) hUfin.ne))
              (ae_of_all _ fun x => ?_)
        _ = volume.real U := integral_indicator_one hU.measurableSet
        _ ≤ δ := by
            rw [Measure.real]
            exact ENNReal.toReal_le_of_le_ofReal hδ.le hUδ.le
      show f x ^ 2 ≤ _
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx]
        simp only [Pi.one_apply]
        exact pow_le_one₀ (hf01 x).1 (hf01 x).2
      · rw [Set.indicator_of_notMem hx, hf0 hx]; simp
    calc (μ : Measure ℝ).real K ≤ ∫ x, f x ∂(μ : Measure ℝ) := h1
      _ ≤ |∫ x, f x ∂(μ : Measure ℝ)| := le_abs_self _
      _ ≤ max C 0 * Real.sqrt (∫ x, f x ^ 2) := dens_bound_pos hC f.continuous hfc
      _ ≤ max C 0 * Real.sqrt δ :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (le_max_right _ _)
  have hlim : Tendsto (fun δ : ℝ => max C 0 * Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun δ : ℝ => max C 0 * Real.sqrt δ) (𝓝 0) (𝓝 (max C 0 * Real.sqrt 0)) :=
      tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0)
    rw [Real.sqrt_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hle : (μ : Measure ℝ).real K ≤ 0 :=
    ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun δ hδ => hbd δ hδ)
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm hle measureReal_nonneg)

end DensAux

/-! ### Main results -/

/-- **L² density criterion** (proof of Proposition 7.1 (2)). A finite measure whose pairings with
continuous compactly supported functions are bounded by `C ‖f‖₂` has a density in `L²`, and
`limDensity ρ μ` is that density. -/
theorem withDensity_limDensity_of_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {μ : FiniteMeasure ℝ}
    {C : ℝ} (hC : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ)) :
    MemLp (limDensity ρ μ) 2 volume ∧
      (μ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (limDensity ρ μ x) := by
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  -- the Radon–Nikodym density `v` of `μ`
  have hac := dens_absolutelyContinuous hC
  set v : ℝ → ℝ := fun x => ((μ : Measure ℝ).rnDeriv volume x).toReal with hv
  have hv0 : ∀ x, 0 ≤ v x := fun _ => ENNReal.toReal_nonneg
  have hvm : Measurable v := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hvi : Integrable v := Measure.integrable_toReal_rnDeriv
  have hμv : (μ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (v x) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top (μ : Measure ℝ) volume] with x hx
    rw [hv, ENNReal.ofReal_toReal hx.ne]
  have hconv : ∀ ε, ∀ x, ∫ y, rhoEps ρ ε (x - y) ∂(μ : Measure ℝ) =
      ∫ y, rhoEps ρ ε (x - y) * v y := by
    intro ε x
    have hm : Measurable fun x => ENNReal.ofReal (v x) := ENNReal.measurable_ofReal.comp hvm
    rw [hμv, integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    rw [ENNReal.toReal_ofReal (hv0 y), smul_eq_mul, mul_comm]
  -- Lebesgue's differentiation theorem: `limDensity ρ μ = v` a.e.
  have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hε⟩
  have hlim : limDensity ρ μ =ᵐ[volume] v := by
    filter_upwards [mollif_ae_tendsto hρ hvi.locallyIntegrable] with x hx
    have h1 := (ENNReal.continuous_ofReal.tendsto _).comp (hx.comp hseq)
    have h2 : liminf (fun k : ℕ => ENNReal.ofReal
        (∫ y, rhoEps ρ (1 / ((k : ℝ) + 1)) (x - y) ∂(μ : Measure ℝ))) atTop =
        ENNReal.ofReal (v x) := by
      simp_rw [hconv]
      exact h1.liminf_eq
    show ENNReal.toReal _ = v x
    rw [h2, ENNReal.toReal_ofReal (hv0 x)]
  refine ⟨?_, hμv.trans (withDensity_congr_ae (hlim.mono fun x hx => by rw [hx])).symm⟩
  -- `L²`: Fatou and the uniform bound `‖μ ⋆ ρ_ε‖₂² ≤ C₊²`
  have hmeas : Measurable (limDensity ρ μ) :=
    (Measurable.liminf fun k => ENNReal.measurable_ofReal.comp
      (dens_continuous_conv hρ (hε k) μ).measurable).ennreal_toReal
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)]
  refine (dens_lintegral_sq_le hρ μ).trans_lt (lt_of_le_of_lt
    (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ENNReal.ofReal_le_ofReal
      (dens_smoothedNormSq_le hρ hC (hε k)))) ENNReal.ofReal_lt_top)

/-- **Fatou's bound**: `∫ (limDensity ρ μ)² ≤ liminf_k ‖μ ⋆ ρ_{1/(k+1)}‖₂²` (in `[0, ∞]`). -/
theorem lintegral_limDensity_sq_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (μ : FiniteMeasure ℝ) :
    ∫⁻ x, ENNReal.ofReal (limDensity ρ μ x ^ 2) ≤
      liminf (fun k : ℕ => ENNReal.ofReal
        (smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ (1 / ((k : ℝ) + 1)))) atTop :=
  dens_lintegral_sq_le hρ μ

/-- `(γ, t, x) ↦ limDensity ρ (γ(t)) x` is measurable on `C([0,T], ℳ₊) × ℝ × ℝ`. -/
theorem measurable_limDensity_pathAt {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T : ℝ} :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ × ℝ =>
      limDensity ρ (pathAt p.1 p.2.1) p.2.2 := by
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  unfold limDensity
  refine (Measurable.liminf fun k => ENNReal.measurable_ofReal.comp ?_).ennreal_toReal
  exact ((densFM_continuous_conv hρ (hε k)).comp
    ((dens_continuous_pathAt.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))).measurable

/-- **Predictability of the density** (Proposition 7.1 (2), "this defines a predictable random
field"): for a measurable `Y`, `limField ρ Y` is measurable for the predictable σ-algebra of the
natural filtration of `Y` times the Borel σ-algebra of `ℝ` (no null sets needed). -/
theorem measurable_limField_predictable {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {T : ℝ} {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hY : Measurable Y) :
    Measurable[((pathFiltration (mΩ := mΩ) Y).predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => limField ρ Y p.1.1 p.2 p.1.2 := by
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  -- the mollified field `F_k(t, x, ω) = (Y(ω)(t) ⋆ ρ_{1/(k+1)})(x)`
  set F : ℕ → ℝ≥0 → ℝ → Ω → ℝ := fun k t x ω =>
    ∫ y, rhoEps ρ (1 / ((k : ℝ) + 1)) (x - y) ∂(pathAt (Y ω) t : Measure ℝ) with hF
  have hFc : ∀ k ω, Continuous fun p : ℝ≥0 × ℝ => F k p.1 p.2 ω := fun k ω =>
    (densFM_continuous_conv hρ (hε k)).comp ((dens_continuous_pathAt.comp
      (continuous_const.prodMk (NNReal.continuous_coe.comp continuous_fst))).prodMk continuous_snd)
  have hFa : ∀ k t x, Measurable[pathFiltration (mΩ := mΩ) Y t] (F k t x) := by
    intro k t x
    have h1 : @Measurable _ _ (pathFiltrationCan T t) (borel (FiniteMeasure ℝ))
        fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => pathAt γ t :=
      measurable_pathAt_pathFiltrationCan le_rfl
    have h2 : @Measurable _ _ (borel (FiniteMeasure ℝ)) _ fun ν : FiniteMeasure ℝ =>
        ∫ y, rhoEps ρ (1 / ((k : ℝ) + 1)) (x - y) ∂(ν : Measure ℝ) :=
      @Continuous.measurable _ _ _ (borel _) (@OpensMeasurableSpace.mk (FiniteMeasure ℝ) _ (borel _)
        le_rfl) _ _ _ _ ((densFM_continuous_conv hρ (hε k)).comp (continuous_id.prodMk continuous_const))
    have h3 : @Measurable _ _ (pathFiltration (mΩ := mΩ) Y t) (pathFiltrationCan T t) Y :=
      fun A hA => MeasurableSpace.measurableSet_inf.2
        ⟨⟨A, hA, rfl⟩, hY ((pathFiltrationCan T).le t A hA)⟩
    exact h2.comp (h1.comp h3)
  have hk : ∀ k, Measurable[((pathFiltration (mΩ := mΩ) Y).predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => F k p.1.1 p.2 p.1.2 := fun k =>
    measurable_predictable_of_continuous (hFc k) (hFa k)
  exact (Measurable.liminf fun k => ENNReal.measurable_ofReal.comp (hk k)).ennreal_toReal

end QSSEPtoKPZ
