/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Energy

/-!
# Convergence tools for the Itô integral (package C, task C3, auxiliary)

All results are in the namespace `QSSEPtoKPZ.StochIntAux`.

* `pathBracket f g T ω = ∫_0^T ∑ᵢ fᵢ(s, ω) gᵢ(s, ω) ds`; the bound
  `|∫ ∑ f g - ∫ ∑ f' g'| ≤ λ ∫ ∑ (f - f')² + λ⁻¹ ∫ ∑ g² + λ⁻¹ ∫ ∑ f'² + λ ∫ ∑ (g - g')²`
  (`enorm_pathBracket_sub_le`), measurability and integrability, and `L¹` convergence of
  `pathBracket f_k g_k` when `f_k → f`, `g_k → g` for the energy
  (`tendsto_lintegral_pathBracket_sub`).
* Random variables: `L¹` convergence of products `X_k Y_k → X Y` from `L²` convergence
  (`tendsto_lintegral_mul_sub`); `L² ⇒ L¹` (`tendsto_lintegral_enorm_of_sq`).
* `condExp_ae_eq_of_tendsto`: if `𝔼[X_k | m] = Z_k`, `X_k → X` and `Z_k → Z` in `L¹`, then
  `𝔼[X | m] = Z`.
* `ae_forall_le_eq_of_continuous`, `ae_forall_eq_of_continuous`: two processes with almost
  surely continuous paths which are versions of each other are indistinguishable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

namespace StochIntAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*} {μ : Measure Ω}

/-- `∫ (λ A + λ⁻¹ B + λ⁻¹ C + λ D) = λ ∫ A + λ⁻¹ ∫ B + λ⁻¹ ∫ C + λ ∫ D`. -/
lemma lintegral_lam_four {α : Type*} [MeasurableSpace α] {ν : Measure α} {A B C D : α → ℝ≥0∞}
    (hA : AEMeasurable A ν) (hB : AEMeasurable B ν) (hC : AEMeasurable C ν) {l : ℝ≥0∞}
    (hl0 : l ≠ 0) (hlt : l ≠ ∞) :
    ∫⁻ x, (l * A x + l⁻¹ * B x + l⁻¹ * C x + l * D x) ∂ν =
      l * ∫⁻ x, A x ∂ν + l⁻¹ * ∫⁻ x, B x ∂ν + l⁻¹ * ∫⁻ x, C x ∂ν + l * ∫⁻ x, D x ∂ν := by
  have hi : l⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hl0
  have h3 : AEMeasurable (fun x => l * A x + l⁻¹ * B x + l⁻¹ * C x) ν :=
    ((hA.const_mul l).add (hB.const_mul l⁻¹)).add (hC.const_mul l⁻¹)
  have h2 : AEMeasurable (fun x => l * A x + l⁻¹ * B x) ν :=
    (hA.const_mul l).add (hB.const_mul l⁻¹)
  have h1 : AEMeasurable (fun x => l * A x) ν := hA.const_mul l
  rw [lintegral_add_left' h3, lintegral_add_left' h2, lintegral_add_left' h1,
    lintegral_const_mul' _ _ hlt,
    lintegral_const_mul' _ _ hi, lintegral_const_mul' _ _ hi, lintegral_const_mul' _ _ hlt]

/-! ### The pathwise bracket -/

/-- `∫_0^T ∑ᵢ fᵢ(s, ω) gᵢ(s, ω) ds`. -/
def pathBracket (f g : ι → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..T, ∑' i, f i s ω * g i s ω

/-- `∫_0^T ∑ᵢ |fᵢ gᵢ| ≤ ∫_0^T ∑ᵢ fᵢ² + ∫_0^T ∑ᵢ gᵢ²`. -/
lemma lintegral_tsum_enorm_mul_le [Countable ι] {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (T : ℝ) (ω : Ω) :
    ∫⁻ s in Set.Ioc 0 T, ∑' i, ‖f i s ω * g i s ω‖ₑ ≤ pathEnergy f T ω + pathEnergy g T ω := by
  unfold pathEnergy
  rw [← lintegral_add_left' (aemeasurable_tsum_sq hf T ω)]
  refine lintegral_mono fun s => ?_
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun i => by
    simpa using enorm_mul_le_lam (f i s ω) (g i s ω) one_ne_zero ENNReal.one_ne_top

/-- If the path energies of `f` and `g` are finite, `s ↦ ∑ᵢ fᵢ gᵢ` is integrable on `(0, T]` and
the series converges for almost every `s`. -/
lemma integrableOn_tsum_mul [Countable ι] {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (hg : EnergyMeas g) (T : ℝ) (ω : Ω) (hfT : pathEnergy f T ω ≠ ∞)
    (hgT : pathEnergy g T ω ≠ ∞) :
    MeasureTheory.IntegrableOn (fun s => ∑' i, f i s ω * g i s ω) (Set.Ioc 0 T) ∧
      ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), Summable fun i => f i s ω * g i s ω := by
  have hfin : ∫⁻ s in Set.Ioc 0 T, ∑' i, ‖f i s ω * g i s ω‖ₑ < ∞ :=
    (lintegral_tsum_enorm_mul_le hf T ω).trans_lt
      (ENNReal.add_lt_top.2 ⟨hfT.lt_top, hgT.lt_top⟩)
  have hmeas : AEMeasurable (fun s => ∑' i, ‖f i s ω * g i s ω‖ₑ)
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    refine (measurable_tsum_ennreal fun i =>
      ((hf.measurable_ext i ω).mul (hg.measurable_ext i ω)).enorm).aemeasurable.congr ?_
    filter_upwards [ae_restrict_Ioc_pos T] with s hs
    simp [hs]
  have hmext : Measurable fun s => ∑' i, (if 0 < s then f i s ω else 0) *
      (if 0 < s then g i s ω else 0) :=
    measurable_tsum_real fun i => (hf.measurable_ext i ω).mul (hg.measurable_ext i ω)
  have hae : (fun s => ∑' i, (if 0 < s then f i s ω else 0) * (if 0 < s then g i s ω else 0))
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] fun s => ∑' i, f i s ω * g i s ω := by
    filter_upwards [ae_restrict_Ioc_pos T] with s hs
    simp [hs]
  refine ⟨⟨hmext.aestronglyMeasurable.congr hae, ?_⟩,
    (ae_lt_top' hmeas hfin.ne).mono fun s hs => Summable.of_enorm hs.ne⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_mono fun s => enorm_tsum_le_tsum_enorm).trans_lt hfin

/-- `|∫_0^T ∑ᵢ fᵢ gᵢ| ≤ ∫_0^T ∑ᵢ fᵢ² + ∫_0^T ∑ᵢ gᵢ²`. -/
lemma enorm_pathBracket_le [Countable ι] {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) {T : ℝ}
    (hT : 0 ≤ T) (ω : Ω) :
    ‖pathBracket f g T ω‖ₑ ≤ pathEnergy f T ω + pathEnergy g T ω := by
  unfold pathBracket
  rw [intervalIntegral.integral_of_le hT]
  exact (enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono fun s => enorm_tsum_le_tsum_enorm).trans (lintegral_tsum_enorm_mul_le hf T ω))

/-- **Pathwise bilinear bound.** For `0 < λ < ∞` and finite path energies,
`|∫ ∑ f g - ∫ ∑ f' g'| ≤ λ ∫ ∑ (f - f')² + λ⁻¹ ∫ ∑ g² + λ⁻¹ ∫ ∑ f'² + λ ∫ ∑ (g - g')²`. -/
lemma enorm_pathBracket_sub_le [Countable ι] {f g f' g' : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (hg : EnergyMeas g) (hf' : EnergyMeas f') (hg' : EnergyMeas g') {T : ℝ} (hT : 0 ≤ T)
    (ω : Ω) (hfT : pathEnergy f T ω ≠ ∞) (hgT : pathEnergy g T ω ≠ ∞)
    (hf'T : pathEnergy f' T ω ≠ ∞) (hg'T : pathEnergy g' T ω ≠ ∞) {l : ℝ≥0∞} (hl0 : l ≠ 0)
    (hlt : l ≠ ∞) :
    ‖pathBracket f g T ω - pathBracket f' g' T ω‖ₑ ≤
      l * pathEnergy (fun i s ω => f i s ω - f' i s ω) T ω + l⁻¹ * pathEnergy g T ω +
        l⁻¹ * pathEnergy f' T ω + l * pathEnergy (fun i s ω => g i s ω - g' i s ω) T ω := by
  obtain ⟨i1, s1⟩ := integrableOn_tsum_mul hf hg T ω hfT hgT
  obtain ⟨i2, s2⟩ := integrableOn_tsum_mul hf' hg' T ω hf'T hg'T
  unfold pathBracket
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    ← integral_sub i1 i2]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ s in Set.Ioc 0 T, ‖∑' i, f i s ω * g i s ω - ∑' i, f' i s ω * g' i s ω‖ₑ
      ≤ ∫⁻ s in Set.Ioc 0 T, (l * ∑' i, ‖f i s ω - f' i s ω‖ₑ ^ 2 +
          l⁻¹ * ∑' i, ‖g i s ω‖ₑ ^ 2 + l⁻¹ * ∑' i, ‖f' i s ω‖ₑ ^ 2 +
          l * ∑' i, ‖g i s ω - g' i s ω‖ₑ ^ 2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [s1, s2] with s h1 h2
        rw [← h1.tsum_sub h2]
        refine enorm_tsum_le_tsum_enorm.trans ?_
        simp only [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum fun i => enorm_mul_sub_mul_le _ _ _ _ hl0 hlt
    _ = _ := lintegral_lam_four (aemeasurable_tsum_sq (hf.sub hf') T ω)
          (aemeasurable_tsum_sq hg T ω) (aemeasurable_tsum_sq hf' T ω) hl0 hlt

/-- The pathwise bracket is measurable in `ω`. -/
lemma measurable_pathBracket [Countable ι] {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (hg : EnergyMeas g) {T : ℝ} (hT : 0 ≤ T) : Measurable (pathBracket f g T) := by
  have : pathBracket f g T = fun ω => ∫ s in Set.Ioc 0 T,
      ∑' i, (if 0 < s then f i s ω else 0) * (if 0 < s then g i s ω else 0) := by
    funext ω
    unfold pathBracket
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_congr_fun measurableSet_Ioc fun s hs => by simp [hs.1]
  rw [this]
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : Ω × ℝ => ∑' i, (if 0 < p.2 then f i p.2 p.1 else 0) *
      (if 0 < p.2 then g i p.2 p.1 else 0))
    (measurable_tsum_real fun i => ((hf i).comp measurable_swap).mul
      ((hg i).comp measurable_swap)).stronglyMeasurable).measurable

/-- The pathwise bracket of two families of finite energy is integrable. -/
lemma integrable_pathBracket [Countable ι] {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (hg : EnergyMeas g) {T : ℝ} (hT : 0 ≤ T) (hEf : energy μ f T ≠ ∞)
    (hEg : energy μ g T ≠ ∞) : Integrable (pathBracket f g T) μ := by
  refine ⟨(measurable_pathBracket hf hg hT).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ ω, ‖pathBracket f g T ω‖ₑ ∂μ ≤ ∫⁻ ω, (pathEnergy f T ω + pathEnergy g T ω) ∂μ :=
        lintegral_mono fun ω => enorm_pathBracket_le hf hT ω
    _ = energy μ f T + energy μ g T :=
        lintegral_add_left' (measurable_pathEnergy hf T).aemeasurable _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hEf.lt_top, hEg.lt_top⟩

/-- `∫_0^T ∑ᵢ fᵢ² = (pathEnergy f T ω)` when the path energy is finite. -/
lemma ofReal_pathBracket_self [Countable ι] {f : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) {T : ℝ}
    (hT : 0 ≤ T) (ω : Ω) (hfin : pathEnergy f T ω ≠ ∞) :
    ENNReal.ofReal (pathBracket f f T ω) = pathEnergy f T ω := by
  unfold pathBracket
  rw [intervalIntegral.integral_of_le hT]
  have : ∀ s, ∑' i, f i s ω * f i s ω = (∑' i, ‖f i s ω‖ₑ ^ 2).toReal := fun s => by
    rw [ENNReal.tsum_toReal_eq (fun i => by finiteness)]
    congr 1
    funext i
    rw [enorm_sq_eq, ENNReal.toReal_ofReal (sq_nonneg _), sq]
  simp_rw [this]
  rw [integral_toReal (aemeasurable_tsum_sq hf T ω) (ae_lt_top' (aemeasurable_tsum_sq hf T ω) hfin)]
  exact ENNReal.ofReal_toReal hfin

/-- Finite energy implies finite path energy almost surely. -/
lemma ae_pathEnergy_ne_top [Countable ι] {f : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) {T : ℝ}
    (hE : energy μ f T ≠ ∞) : ∀ᵐ ω ∂μ, pathEnergy f T ω ≠ ∞ :=
  (ae_lt_top' (measurable_pathEnergy hf T).aemeasurable hE).mono fun _ h => h.ne

/-- **`L¹` convergence of brackets.** If `f_k → f` and `g_k → g` for the energy on `[0, T]`,
all of finite energy, then `∫_0^T ∑ᵢ f_{k,i} g_{k,i} → ∫_0^T ∑ᵢ fᵢ gᵢ` in `L¹`. -/
lemma tendsto_lintegral_pathBracket_sub [Countable ι] {fs gs : ℕ → ι → ℝ → Ω → ℝ}
    {f g : ι → ℝ → Ω → ℝ} (hfs : ∀ k, EnergyMeas (fs k)) (hgs : ∀ k, EnergyMeas (gs k))
    (hf : EnergyMeas f) (hg : EnergyMeas g) {T : ℝ} (hT : 0 ≤ T)
    (hEfs : ∀ k, energy μ (fs k) T ≠ ∞) (hEgs : ∀ k, energy μ (gs k) T ≠ ∞)
    (hEf : energy μ f T ≠ ∞) (hEg : energy μ g T ≠ ∞)
    (hlf : Tendsto (fun k => energy μ (fun i s ω => fs k i s ω - f i s ω) T) atTop (𝓝 0))
    (hlg : Tendsto (fun k => energy μ (fun i s ω => gs k i s ω - g i s ω) T) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ‖pathBracket (fs k) (gs k) T ω - pathBracket f g T ω‖ₑ ∂μ)
      atTop (𝓝 0) := by
  have hfin : ∀ᵐ ω ∂μ, (∀ k, pathEnergy (fs k) T ω ≠ ∞) ∧ (∀ k, pathEnergy (gs k) T ω ≠ ∞) ∧
      pathEnergy f T ω ≠ ∞ ∧ pathEnergy g T ω ≠ ∞ := by
    filter_upwards [ae_all_iff.2 fun k => ae_pathEnergy_ne_top (hfs k) (hEfs k),
      ae_all_iff.2 fun k => ae_pathEnergy_ne_top (hgs k) (hEgs k),
      ae_pathEnergy_ne_top hf hEf, ae_pathEnergy_ne_top hg hEg] with ω a b c d
    exact ⟨a, b, c, d⟩
  refine tendsto_zero_of_le_lam
    (a := fun k => energy μ (fun i s ω => fs k i s ω - f i s ω) T +
      energy μ (fun i s ω => gs k i s ω - g i s ω) T)
    (b := fun k => 2 * energy μ (fun i s ω => gs k i s ω - g i s ω) T + 2 * energy μ g T +
      energy μ f T) (β := 2 * energy μ g T + energy μ f T) ?_ ?_ ?_ ?_
  · simpa using hlf.add hlg
  · have := ((ENNReal.Tendsto.const_mul hlg (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))).add
      (tendsto_const_nhds (x := 2 * energy μ g T))).add (tendsto_const_nhds (x := energy μ f T))
    simpa using this
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hEg, hEf⟩
  intro l hl0 hlt
  refine Eventually.of_forall fun k => ?_
  have hgk : energy μ (gs k) T ≤ 2 * energy μ (fun i s ω => gs k i s ω - g i s ω) T +
      2 * energy μ g T := energy_add_le ((hgs k).sub hg) (fun i s ω => by ring) T
  calc ∫⁻ ω, ‖pathBracket (fs k) (gs k) T ω - pathBracket f g T ω‖ₑ ∂μ
      ≤ ∫⁻ ω, (l * pathEnergy (fun i s ω => fs k i s ω - f i s ω) T ω +
          l⁻¹ * pathEnergy (gs k) T ω + l⁻¹ * pathEnergy f T ω +
          l * pathEnergy (fun i s ω => gs k i s ω - g i s ω) T ω) ∂μ := by
        refine lintegral_mono_ae (hfin.mono fun ω hω => ?_)
        exact enorm_pathBracket_sub_le (hfs k) (hgs k) hf hg hT ω (hω.1 k) (hω.2.1 k) hω.2.2.1
          hω.2.2.2 hl0 hlt
    _ = l * energy μ (fun i s ω => fs k i s ω - f i s ω) T + l⁻¹ * energy μ (gs k) T +
          l⁻¹ * energy μ f T + l * energy μ (fun i s ω => gs k i s ω - g i s ω) T :=
        lintegral_lam_four (measurable_pathEnergy ((hfs k).sub hf) T).aemeasurable
          (measurable_pathEnergy (hgs k) T).aemeasurable
          (measurable_pathEnergy hf T).aemeasurable hl0 hlt
    _ ≤ l * energy μ (fun i s ω => fs k i s ω - f i s ω) T +
          l⁻¹ * (2 * energy μ (fun i s ω => gs k i s ω - g i s ω) T + 2 * energy μ g T) +
          l⁻¹ * energy μ f T + l * energy μ (fun i s ω => gs k i s ω - g i s ω) T := by
        gcongr
    _ = _ := by ring

/-! ### Random variables -/

/-- **`L¹` convergence of products.** If `X_k → X` and `Y_k → Y` in `L²`, then
`X_k Y_k → X Y` in `L¹`. -/
lemma tendsto_lintegral_mul_sub {Xs Ys : ℕ → Ω → ℝ} {X Y : Ω → ℝ}
    (hXs : ∀ k, AEMeasurable (Xs k) μ) (hYs : ∀ k, AEMeasurable (Ys k) μ)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hX2 : ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ ≠ ∞)
    (hY2 : ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ ≠ ∞)
    (hXl : Tendsto (fun k => ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ^ 2 ∂μ) atTop (𝓝 0))
    (hYl : Tendsto (fun k => ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ‖Xs k ω * Ys k ω - X ω * Y ω‖ₑ ∂μ) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_lam
    (a := fun k => ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ^ 2 ∂μ + ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ)
    (b := fun k => 2 * ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ + 2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ +
      ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) (β := 2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ + ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) ?_ ?_ ?_ ?_
  · simpa using hXl.add hYl
  · have := ((ENNReal.Tendsto.const_mul hYl (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))).add
      (tendsto_const_nhds (x := 2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ))).add
        (tendsto_const_nhds (x := ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ))
    simpa using this
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hY2, hX2⟩
  intro l hl0 hlt
  refine Eventually.of_forall fun k => ?_
  have hYk : ∫⁻ ω, ‖Ys k ω‖ₑ ^ 2 ∂μ ≤ 2 * ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ +
      2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
      ← lintegral_add_left' (by
        exact (((hYs k).sub hY).enorm.pow_const 2).const_mul 2 :
          AEMeasurable (fun ω => 2 * ‖Ys k ω - Y ω‖ₑ ^ 2) μ)]
    refine lintegral_mono fun ω => ?_
    have := enorm_add_sq_le (Ys k ω - Y ω) (Y ω)
    rwa [sub_add_cancel] at this
  calc ∫⁻ ω, ‖Xs k ω * Ys k ω - X ω * Y ω‖ₑ ∂μ
      ≤ ∫⁻ ω, (l * ‖Xs k ω - X ω‖ₑ ^ 2 + l⁻¹ * ‖Ys k ω‖ₑ ^ 2 + l⁻¹ * ‖X ω‖ₑ ^ 2 +
          l * ‖Ys k ω - Y ω‖ₑ ^ 2) ∂μ :=
        lintegral_mono fun ω => enorm_mul_sub_mul_le _ _ _ _ hl0 hlt
    _ = l * ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ^ 2 ∂μ + l⁻¹ * ∫⁻ ω, ‖Ys k ω‖ₑ ^ 2 ∂μ +
          l⁻¹ * ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ + l * ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ :=
        lintegral_lam_four (((hXs k).sub hX).enorm.pow_const 2) ((hYs k).enorm.pow_const 2)
          (hX.enorm.pow_const 2) hl0 hlt
    _ ≤ l * ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ^ 2 ∂μ + l⁻¹ * (2 * ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ +
          2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ) + l⁻¹ * ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ +
          l * ∫⁻ ω, ‖Ys k ω - Y ω‖ₑ ^ 2 ∂μ := by gcongr
    _ = _ := by ring

/-- **`L²` convergence implies `L¹` convergence** (finite measure). -/
lemma tendsto_lintegral_enorm_of_sq [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
    (hZ : ∀ k, AEMeasurable (Z k) μ)
    (h : Tendsto (fun k => ∫⁻ ω, ‖Z k ω‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ‖Z k ω‖ₑ ∂μ) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_lam (b := fun _ => μ Set.univ) h tendsto_const_nhds
    (measure_ne_top μ _) fun l hl0 hlt => Eventually.of_forall fun k => ?_
  calc ∫⁻ ω, ‖Z k ω‖ₑ ∂μ ≤ ∫⁻ ω, (l * ‖Z k ω‖ₑ ^ 2 + l⁻¹ * 1) ∂μ := by
        refine lintegral_mono fun ω => ?_
        simpa using enorm_mul_le_lam (Z k ω) 1 hl0 hlt
    _ = l * ∫⁻ ω, ‖Z k ω‖ₑ ^ 2 ∂μ + l⁻¹ * μ Set.univ := by
        rw [lintegral_add_left' (((hZ k).enorm.pow_const 2).const_mul l),
          lintegral_const_mul' _ _ hlt, lintegral_const, mul_one]

/-- **Conditional expectations and `L¹` limits.** If `𝔼[X_k | 𝓖_r] = Z_k` almost surely,
`X_k → X` and `Z_k → Z` in `L¹`, then `𝔼[X | 𝓖_r] = Z` almost surely. -/
lemma condExp_ae_eq_of_tendsto [IsFiniteMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ} (r : ℝ≥0)
    {Xs Zs : ℕ → Ω → ℝ} {X Z : Ω → ℝ} (hXs : ∀ k, Integrable (Xs k) μ) (hX : Integrable X μ)
    (hZ : AEStronglyMeasurable Z μ) (hce : ∀ k, μ[Xs k | 𝓖 r] =ᵐ[μ] Zs k)
    (hXl : Tendsto (fun k => ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ∂μ) atTop (𝓝 0))
    (hZl : Tendsto (fun k => ∫⁻ ω, ‖Zs k ω - Z ω‖ₑ ∂μ) atTop (𝓝 0)) :
    μ[X | 𝓖 r] =ᵐ[μ] Z := by
  have hbound : ∀ k, ∫⁻ ω, ‖μ[X | 𝓖 r] ω - Z ω‖ₑ ∂μ ≤
      ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ∂μ + ∫⁻ ω, ‖Zs k ω - Z ω‖ₑ ∂μ := by
    intro k
    have h1 : ∫⁻ ω, ‖(μ[X | 𝓖 r] - μ[Xs k | 𝓖 r]) ω‖ₑ ∂μ ≤ ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ∂μ := by
      have hsub := condExp_sub hX (hXs k) (𝓖 r)
      calc ∫⁻ ω, ‖(μ[X | 𝓖 r] - μ[Xs k | 𝓖 r]) ω‖ₑ ∂μ = ∫⁻ ω, ‖μ[X - Xs k | 𝓖 r] ω‖ₑ ∂μ :=
            lintegral_congr_ae (hsub.mono fun ω h => by dsimp only; rw [h])
        _ = eLpNorm (μ[X - Xs k | 𝓖 r]) 1 μ :=
            (eLpNorm_one_eq_lintegral_enorm integrable_condExp.aestronglyMeasurable).symm
        _ ≤ eLpNorm (X - Xs k) 1 μ := eLpNorm_condExp_le_eLpNorm _ le_rfl
        _ = ∫⁻ ω, ‖X ω - Xs k ω‖ₑ ∂μ :=
            eLpNorm_one_eq_lintegral_enorm (hX.sub (hXs k)).aestronglyMeasurable
        _ = ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ∂μ := lintegral_congr fun ω => enorm_sub_rev _ _
    calc ∫⁻ ω, ‖μ[X | 𝓖 r] ω - Z ω‖ₑ ∂μ
        ≤ ∫⁻ ω, (‖(μ[X | 𝓖 r] - μ[Xs k | 𝓖 r]) ω‖ₑ + ‖Zs k ω - Z ω‖ₑ) ∂μ := by
          refine lintegral_mono_ae ((hce k).mono fun ω h => ?_)
          calc ‖μ[X | 𝓖 r] ω - Z ω‖ₑ = ‖(μ[X | 𝓖 r] - μ[Xs k | 𝓖 r]) ω + (Zs k ω - Z ω)‖ₑ := by
                rw [Pi.sub_apply, h]; ring_nf
            _ ≤ _ := enorm_add_le _ _
      _ = ∫⁻ ω, ‖(μ[X | 𝓖 r] - μ[Xs k | 𝓖 r]) ω‖ₑ ∂μ + ∫⁻ ω, ‖Zs k ω - Z ω‖ₑ ∂μ :=
          lintegral_add_left' ((integrable_condExp.sub
            integrable_condExp).aestronglyMeasurable.aemeasurable.enorm) _
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun k => ∫⁻ ω, ‖Xs k ω - X ω‖ₑ ∂μ + ∫⁻ ω, ‖Zs k ω - Z ω‖ₑ ∂μ)
      atTop (𝓝 0) := by simpa using hXl.add hZl
  have h0 : ∫⁻ ω, ‖μ[X | 𝓖 r] ω - Z ω‖ₑ ∂μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  have hm : AEMeasurable (fun ω => ‖μ[X | 𝓖 r] ω - Z ω‖ₑ) μ :=
    (integrable_condExp.aestronglyMeasurable.sub hZ).aemeasurable.enorm
  rw [lintegral_eq_zero_iff' hm] at h0
  filter_upwards [h0] with ω h
  simpa [sub_eq_zero] using h

/-- A random variable with `𝔼 ‖X‖² < ∞` is in `L²`. -/
lemma memLp_two_of_lintegral {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ)
    (h : ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ ≠ ∞) : MemLp X 2 μ := by
  rw [memLp_two_iff_integrable_sq hX]
  refine ⟨hX.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h.lt_top

/-- A random variable in `L²` has `𝔼 ‖X‖² < ∞`. -/
lemma lintegral_sq_ne_top {X : Ω → ℝ} (hX : MemLp X 2 μ) : ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ ≠ ∞ := by
  have := hX.integrable_sq.2
  rw [hasFiniteIntegral_iff_enorm] at this
  simpa [enorm_pow] using this.ne

/-! ### Indistinguishability -/

/-- Two processes with almost surely continuous paths that are versions of each other on
`[0, T]` are indistinguishable on `[0, T]`. -/
lemma ae_forall_le_eq_of_continuous {X Y : ℝ → Ω → ℝ} {T : ℝ}
    (hX : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => X t ω)
    (hY : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => Y t ω)
    (h : ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = Y t ω := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ae_of_all _ fun ω t ht => absurd ht (not_le.2 (hT.trans_le t.2))
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hle : ∀ t : ℝ≥0, (t : ℝ) ≤ T ↔ t ≤ T.toNNReal := fun t => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT]
  have hD : ∀ᵐ ω ∂μ, ∀ d ∈ D, X (min d T.toNNReal : ℝ≥0) ω = Y (min d T.toNNReal : ℝ≥0) ω := by
    rw [ae_ball_iff hDc]
    exact fun d _ => h _ ((hle _).2 (min_le_right _ _))
  filter_upwards [hX, hY, hD] with ω h1 h2 h3 t ht
  have hc : (fun t : ℝ≥0 => X (min t T.toNNReal : ℝ≥0) ω) =
      fun t : ℝ≥0 => Y (min t T.toNNReal : ℝ≥0) ω :=
    Continuous.ext_on hDd (h1.comp (continuous_id.min continuous_const))
      (h2.comp (continuous_id.min continuous_const)) fun d hd => h3 d hd
  have := congrFun hc t
  rwa [min_eq_left ((hle t).1 ht)] at this

/-- Two processes with almost surely continuous paths that are versions of each other are
indistinguishable on `[0, ∞)`. -/
lemma ae_forall_eq_of_continuous {X Y : ℝ → Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => X t ω)
    (hY : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => Y t ω) (h : ∀ t : ℝ≥0, X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, X t ω = Y t ω := by
  have := ae_all_iff.2 fun n : ℕ => ae_forall_le_eq_of_continuous (T := n) hX hY fun t _ => h t
  filter_upwards [this] with ω hω t
  exact hω ⌈(t : ℝ)⌉₊ t (Nat.le_ceil _)

end StochIntAux

end QSSEPtoKPZ
