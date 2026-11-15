/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.NoiseFiltration
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.WhiteNoise.ProjectionFiber
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Conditioning a Walsh integral on the noise (task G6)

Interface file of task I0″ (Stage 4); all statements proved by task G6 (13 November 2026), with
the fiberwise lemma of `ProjectionFiber.lean`. See `docs/stage4-design.md`, Sections 1.2 (h) and 3.3, and
`docs/stage4-interfaces.md`.

`𝔼[∫ h dξ | 𝒩_∞] = ∫ ĥ dξ`, the integral on the right being taken for the noise filtration,
where `ĥ = noiseProj S ν h` is the projection of the integrand onto `L²(𝒩_∞ ⊗ 𝓑(ℝ²))`.

**The projection.** A Walsh integrand is in `L²(ν ⊗ Leb²)`, an infinite measure, on which it
need not be integrable; Mathlib's `condExp` of a non-integrable function is `0`, and
σ-finiteness of the trimmed measure does not help (example: `h(s,y) = 𝟙_{(0,1]}(s)
𝟙_{[0,∞)}(y)/(1+y)`, deterministic, in `L²` but not in `L¹`). So the conditional expectation is
taken for the reference **probability** measure `ν ⊗ γ ⊗ γ` (`γ` the standard Gaussian,
`noiseRefMeasure`): it has the same null sets as `ν ⊗ Leb²`, every `h ∈ L²(ν ⊗ Leb²)` is
integrable for it (`∫ |h| g ≤ ‖h‖₂ ‖g‖₂`, `g` the Gaussian density), and since its density with
respect to `ν ⊗ Leb²` is a function of `(s,y)` only (measurable for `𝒩_∞ ⊗ 𝓑(ℝ²)`), the
conditional expectation is the same as the orthogonal projection of `L²(ν ⊗ Leb²)` onto the
`𝒩_∞ ⊗ 𝓑(ℝ²)`-measurable fields (equivalently, the conditional expectations on the unit cells
of space-time, glued). Proof of `condExp_noise`: induction on `IsWalshIntegral`; for a block
`c 𝟙_{(s,t] × (a,b]}`, `ĥ = 𝔼[c | 𝒩_∞] 𝟙_{(s,t] × (a,b]}` and `𝔼[c | 𝒩_∞] = 𝔼[c | 𝒩_s]`
(`IsWhiteNoise.condExp_noise_eq`); sums by linearity and `IsWalshIntegral.congr_ae`; limits by
the `L²(ν ⊗ Leb²)` contraction `noiseProj_memLp`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The reference probability measure `ν ⊗ γ ⊗ γ` on `Ω × ℝ × ℝ` (`γ` the standard Gaussian),
with the same null sets as `ν ⊗ Leb²` when `ν` is a probability measure. -/
def noiseRefMeasure (ν : Measure Ω) : Measure (Ω × ℝ × ℝ) :=
  ν.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- The σ-algebra `𝒩_∞ ⊗ 𝓑(ℝ²)` on `Ω × ℝ × ℝ` (`𝒩_∞ = ⨆_t 𝒩_t`, the noise with null sets). -/
@[instance_reducible] def noiseProdSigma (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) : MeasurableSpace (Ω × ℝ × ℝ) :=
  (⨆ t, noiseFiltration (mΩ := mΩ) S ν t).prod (borel (ℝ × ℝ))

/-- **The projection of a random field onto the noise**: `ĥ = 𝔼[h | 𝒩_∞ ⊗ 𝓑(ℝ²)]`, computed for
the reference probability measure `noiseRefMeasure ν` (see the module docstring); for
`h ∈ L²(ν ⊗ Leb²)` this is the orthogonal projection of `h` onto the `𝒩_∞ ⊗ 𝓑(ℝ²)`-measurable
fields of `L²(ν ⊗ Leb²)`. -/
def noiseProj (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) (h : ℝ → ℝ → Ω → ℝ) (s y : ℝ) (ω : Ω) : ℝ :=
  ((noiseRefMeasure ν)[uncurryField h | noiseProdSigma S ν]) (ω, s, y)

instance (ν : Measure Ω) [IsProbabilityMeasure ν] : IsProbabilityMeasure (noiseRefMeasure ν) := by
  unfold noiseRefMeasure; infer_instance

/-- `𝒩_∞ ⊗ 𝓑(ℝ²)` is contained in the product σ-algebra of `Ω × ℝ × ℝ`. -/
theorem noiseProdSigma_le (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    noiseProdSigma S ν ≤ (inferInstance : MeasurableSpace (Ω × ℝ × ℝ)) := by
  unfold noiseProdSigma
  rw [← (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace (ℝ × ℝ)) = borel (ℝ × ℝ))]
  exact sup_le_sup (MeasurableSpace.comap_mono (iSup_le fun t => (noiseFiltration S ν).le t))
    le_rfl

/-- The projection is `𝒩_∞ ⊗ 𝓑(ℝ²)`-strongly measurable. -/
theorem stronglyMeasurable_noiseProj (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω)
    (h : ℝ → ℝ → Ω → ℝ) :
    StronglyMeasurable[noiseProdSigma S ν] (uncurryField (noiseProj S ν h)) :=
  stronglyMeasurable_condExp


/-! ### Comparison of `ν ⊗ γ ⊗ γ` with `ν ⊗ Leb²`, and the fiberwise property -/

/-- The standard Gaussian density is at most `1`, so `γ ≤ Leb`. -/
private lemma noiseProj_gaussian_le : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  refine Measure.le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs]
  calc ∫⁻ x in s, gaussianPDF 0 1 x ≤ ∫⁻ _ in s, 1 := lintegral_mono fun x => ?_
    _ = volume s := by simp
  rw [gaussianPDF, ENNReal.ofReal_le_one, gaussianPDFReal_def]
  have h1 : (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    rw [NNReal.coe_one, mul_one, Real.one_le_sqrt]
    nlinarith [Real.two_le_pi]
  have h2 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (x - 0) ^ 2 := sq_nonneg _
    rw [NNReal.coe_one]
    linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 2 * 1), neg_div (2 * (1 : ℝ)) ((x - 0) ^ 2)]
  calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- `ν ⊗ γ ⊗ γ ≤ ν ⊗ Leb²`. -/
theorem noiseRefMeasure_le (ν : Measure Ω) [IsProbabilityMeasure ν] :
    noiseRefMeasure ν ≤ ν.prod volume :=
  Measure.prod_mono le_rfl (Measure.prod_mono noiseProj_gaussian_le noiseProj_gaussian_le)

/-- `Leb² ≪ γ ⊗ γ`. -/
private lemma noiseProj_vol_ac :
    (volume : Measure (ℝ × ℝ)) ≪ (gaussianReal 0 1).prod (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 one_ne_zero).prod
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero)

/-- `ν ⊗ Leb² ≪ ν ⊗ γ ⊗ γ`. -/
theorem noiseRefMeasure_absolutelyContinuous (ν : Measure Ω) [IsProbabilityMeasure ν] :
    ν.prod volume ≪ noiseRefMeasure ν :=
  Measure.AbsolutelyContinuous.rfl.prod noiseProj_vol_ac

/-- A field in `L²(ν ⊗ Leb²)` is integrable for `ν ⊗ γ ⊗ γ`. -/
theorem noiseProj_integrable {ν : Measure Ω} [IsProbabilityMeasure ν] {F : Ω × ℝ × ℝ → ℝ}
    (hF : MemLp F 2 (ν.prod volume)) : Integrable F (noiseRefMeasure ν) :=
  (hF.mono_measure (noiseRefMeasure_le ν)).integrable one_le_two

/-- `𝒩_∞ ⊗ 𝓑(ℝ²)`, written with the product instance on `ℝ × ℝ`. -/
theorem noiseProdSigma_eq (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    noiseProdSigma S ν = (⨆ t, noiseFiltration (mΩ := mΩ) S ν t).prod inferInstance := by
  unfold noiseProdSigma
  rw [← (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace (ℝ × ℝ)) = borel (ℝ × ℝ))]

/-- `𝒩_∞ ≤ 𝓕`. -/
theorem noiseProj_iSup_le (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    (⨆ t, noiseFiltration (mΩ := mΩ) S ν t) ≤ mΩ :=
  iSup_le fun t => (noiseFiltration S ν).le t

/-- The projection as a conditional expectation of `uncurryField h`. -/
theorem uncurryField_noiseProj (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) (h : ℝ → ℝ → Ω → ℝ) :
    uncurryField (noiseProj S ν h) = (noiseRefMeasure ν)[uncurryField h | noiseProdSigma S ν] :=
  rfl

/-- **Fiberwise property**: for `Leb²`-a.e. `(s, y)`, `ĥ(s, y) = 𝔼[h(s, y) | 𝒩_∞]`. -/
theorem noiseProj_ae_fiber {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {h : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume)) :
    ∀ᵐ q : ℝ × ℝ, (fun ω => noiseProj S ν h q.1 q.2 ω) =ᵐ[ν]
      ν[fun ω => h q.1 q.2 ω | ⨆ t, noiseFiltration S ν t] := by
  have := noiseFiber_condExp (τ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (𝒢 := ⨆ t, noiseFiltration S ν t) (noiseProj_iSup_le S ν) (noiseProj_integrable hh)
  refine noiseProj_vol_ac.ae_le ?_
  filter_upwards [this] with q hq
  unfold noiseProj
  rw [noiseProdSigma_eq]
  exact hq

/-- `‖f‖₂ ≤ ‖g‖₂` in terms of the integrals of the squares. -/
private lemma noiseProj_eLpNorm_le_iff {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm f 2 μ ≤ eLpNorm g 2 μ ↔
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow_iff (by norm_num)

/-- The projection is strongly measurable for the product σ-algebra. -/
private lemma noiseProj_stronglyMeasurable (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω)
    (h : ℝ → ℝ → Ω → ℝ) : StronglyMeasurable (uncurryField (noiseProj S ν h)) :=
  (stronglyMeasurable_noiseProj S ν h).mono (noiseProdSigma_le S ν)

/-- Sections of an `L²(μ ⊗ ν)` function in the second variable. -/
private lemma noiseProj_memLp_sect_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν' : Measure β} [SFinite μ] [SFinite ν'] {k : α × β → ℝ}
    (hk : MemLp k 2 (μ.prod ν')) : ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 ν' := by
  have hsq := (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  filter_upwards [hsq.prod_right_ae, hk.aestronglyMeasurable.prodMk_left] with x h1 h2
  exact (memLp_two_iff_integrable_sq h2).2 h1

/-- Sections of an `L²(μ ⊗ ν)` function in the first variable. -/
private lemma noiseProj_memLp_sect_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν' : Measure β} [SFinite μ] [SFinite ν'] {k : α × β → ℝ}
    (hk : MemLp k 2 (μ.prod ν')) : ∀ᵐ y ∂ν', MemLp (fun x => k (x, y)) 2 μ := by
  have hsq := (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  filter_upwards [hsq.prod_left_ae, hk.aestronglyMeasurable.prodMk_right] with y h1 h2
  exact (memLp_two_iff_integrable_sq h2).2 h1

/-- The rearrangement `(t, (ω, x)) ↦ (ω, (t, x))` preserves the measures. -/
private lemma noiseProj_rearrange (ν : Measure Ω) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun p : ℝ × Ω × ℝ => (p.2.1, p.1, p.2.2))
      ((volume : Measure ℝ).prod (ν.prod volume)) (ν.prod (volume : Measure (ℝ × ℝ))) := by
  have h1 := MeasurePreserving.symm _
    (measurePreserving_prodAssoc (volume : Measure ℝ) ν (volume : Measure ℝ))
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := ν)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h3 := measurePreserving_prodAssoc ν (volume : Measure ℝ) (volume : Measure ℝ)
  exact h3.comp (h2.comp h1)

/-- Parametric integrals of a strongly measurable function are strongly measurable. -/
private lemma noiseProj_integral_meas {α : Type*} [MeasurableSpace α] {G : α × ℝ × ℝ → ℝ}
    (hG : StronglyMeasurable G) (t : ℝ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun a => ∫ x, G (a, t, x) * f x :=
  StronglyMeasurable.integral_prod_right' (f := fun q : α × ℝ => G (q.1, t, q.2) * f q.2)
    ((hG.comp_measurable (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).mul
      (hf.comp_measurable measurable_snd))

/-- **`L²` contraction**: for `h ∈ L²(ν ⊗ Leb²)`, `ĥ ∈ L²(ν ⊗ Leb²)` and `‖ĥ‖₂ ≤ ‖h‖₂`. -/
theorem noiseProj_memLp {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {h : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume)) :
    MemLp (uncurryField (noiseProj S ν h)) 2 (ν.prod volume) ∧
      eLpNorm (uncurryField (noiseProj S ν h)) 2 (ν.prod volume) ≤
        eLpNorm (uncurryField h) 2 (ν.prod volume) := by
  have hmeas := (noiseProj_stronglyMeasurable S ν h).aestronglyMeasurable (μ := ν.prod volume)
  have hle : eLpNorm (uncurryField (noiseProj S ν h)) 2 (ν.prod volume) ≤
      eLpNorm (uncurryField h) 2 (ν.prod volume) := by
    rw [noiseProj_eLpNorm_le_iff hmeas hh.aestronglyMeasurable,
      lintegral_prod_symm _ (hmeas.enorm.pow_const _),
      lintegral_prod_symm _ (hh.aestronglyMeasurable.enorm.pow_const _)]
    refine lintegral_mono_ae ?_
    filter_upwards [noiseProj_ae_fiber S hh, hh.aestronglyMeasurable.prodMk_right] with q hq hqm
    have hq' : (fun ω => uncurryField (noiseProj S ν h) (ω, q)) =ᵐ[ν]
        ν[fun ω => uncurryField h (ω, q) | ⨆ t, noiseFiltration S ν t] := hq
    rw [lintegral_congr_ae (hq'.mono fun ω hω => by simp only at hω; rw [hω])]
    exact (noiseProj_eLpNorm_le_iff (stronglyMeasurable_condExp.mono
      (noiseProj_iSup_le S ν)).aestronglyMeasurable
      hqm).1
      (eLpNorm_condExp_le_eLpNorm _ one_le_two)
  refine ⟨?_, hle⟩
  exact lt_of_le_of_lt hle hh.eLpNorm_lt_top

/-- Fields that are already functions of the noise are fixed by the projection
(`ν ⊗ Leb²`-almost everywhere). -/
theorem noiseProj_ae_eq_self {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {h : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume))
    (hm : AEStronglyMeasurable[noiseProdSigma S ν] (uncurryField h) (ν.prod volume)) :
    uncurryField (noiseProj S ν h) =ᵐ[ν.prod volume] uncurryField h := by
  rw [uncurryField_noiseProj]
  exact (noiseRefMeasure_absolutelyContinuous ν).ae_le (condExp_of_aestronglyMeasurable' (noiseProdSigma_le S ν)
    (hm.mono_ac (Measure.absolutelyContinuous_of_le (noiseRefMeasure_le ν)))
    (noiseProj_integrable hh))

/-- **Linearity**: the projection of a sum is the sum of the projections. -/
theorem noiseProj_add {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {h h' : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume))
    (hh' : MemLp (uncurryField h') 2 (ν.prod volume)) :
    uncurryField (noiseProj S ν fun s y ω => h s y ω + h' s y ω) =ᵐ[ν.prod volume]
      uncurryField fun s y ω => noiseProj S ν h s y ω + noiseProj S ν h' s y ω := by
  exact (noiseRefMeasure_absolutelyContinuous ν).ae_le (condExp_add (noiseProj_integrable hh) (noiseProj_integrable hh')
    (noiseProdSigma S ν))

/-- **A deterministic bounded factor comes out of the projection**:
`(g h)^ = g ĥ`, `ν ⊗ Leb²`-almost everywhere. -/
theorem noiseProj_mul_left {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (hgb : ∃ C, ∀ s y, |g s y| ≤ C)
    {h : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume)) :
    uncurryField (noiseProj S ν fun s y ω => g s y * h s y ω) =ᵐ[ν.prod volume]
      uncurryField fun s y ω => g s y * noiseProj S ν h s y ω := by
  obtain ⟨C, hC⟩ := hgb
  have hsnd : Measurable[noiseProdSigma S ν, inferInstance] (Prod.snd : Ω × ℝ × ℝ → ℝ × ℝ) := by
    rw [noiseProdSigma_eq]
    exact measurable_iff_comap_le.2 le_sup_right
  have hG : StronglyMeasurable[noiseProdSigma S ν] fun p : Ω × ℝ × ℝ => g p.2.1 p.2.2 :=
    (hg.comp hsnd).stronglyMeasurable
  have hGb : ∀ p : Ω × ℝ × ℝ, ‖g p.2.1 p.2.2‖ ≤ C := fun p => hC _ _
  have hint : Integrable ((fun p : Ω × ℝ × ℝ => g p.2.1 p.2.2) * uncurryField h)
      (noiseRefMeasure ν) :=
    (noiseProj_integrable hh).bdd_mul (hG.mono (noiseProdSigma_le S ν)).aestronglyMeasurable
      (ae_of_all _ hGb)
  exact (noiseRefMeasure_absolutelyContinuous ν).ae_le
    (condExp_mul_of_stronglyMeasurable_left hG hint (noiseProj_integrable hh))

/-- **Conditional Fubini**: for `h ∈ L²(ν ⊗ Leb²)` and `f ∈ L²(ℝ)`, for almost every `t`,
`𝔼[∫ h(t,x) f(x) dx | 𝒩_∞] = ∫ ĥ(t,x) f(x) dx` almost surely. -/
theorem condExp_integral_noiseProj {ν : Measure Ω} [IsProbabilityMeasure ν]
    (S : ℝ → ℝ → Ω → ℝ) {h : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume))
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ∀ᵐ t, ν[fun ω => ∫ x, h t x ω * f x | ⨆ t, noiseFiltration (mΩ := mΩ) S ν t] =ᵐ[ν]
      fun ω => ∫ x, noiseProj S ν h t x ω * f x := by
  have h𝒢 := noiseProj_iSup_le (mΩ := mΩ) S ν
  obtain ⟨hhat, -⟩ := noiseProj_memLp S hh
  have hfs : MemLp (fun q : Ω × ℝ => f q.2) 2 (ν.prod volume) :=
    hf.comp_measurePreserving measurePreserving_snd
  have hfib := Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume) (noiseProj_ae_fiber S hh)
  filter_upwards [hfib,
    noiseProj_memLp_sect_left (hh.comp_measurePreserving (noiseProj_rearrange ν)),
    noiseProj_memLp_sect_left (hhat.comp_measurePreserving (noiseProj_rearrange ν))]
    with t hft hkt hkht
  have hkt' : MemLp (fun q : Ω × ℝ => h t q.2 q.1) 2 (ν.prod volume) := hkt
  have hkht' : MemLp (fun q : Ω × ℝ => noiseProj S ν h t q.2 q.1) 2 (ν.prod volume) := hkht
  have hK : Integrable (fun q : Ω × ℝ => h t q.2 q.1 * f q.2) (ν.prod volume) :=
    hkt'.integrable_mul hfs
  have hKh : Integrable (fun q : Ω × ℝ => noiseProj S ν h t q.2 q.1 * f q.2) (ν.prod volume) :=
    hkht'.integrable_mul hfs
  have hsec : ∀ᵐ x, Integrable (fun ω => h t x ω) ν :=
    (noiseProj_memLp_sect_right hkt').mono fun x hx => hx.integrable one_le_two
  have hG := stronglyMeasurable_noiseProj S ν h
  rw [noiseProdSigma_eq] at hG
  have hV : (fun ω => ∫ x, noiseProj S ν h t x ω * f x) =
      fun ω => ∫ x, noiseProj S ν h t x ω * hf.aestronglyMeasurable.mk f x :=
    funext fun ω => integral_congr_ae (hf.aestronglyMeasurable.ae_eq_mk.mono fun x hx => by
      simp only [hx])
  have hVm : StronglyMeasurable[⨆ t, noiseFiltration (mΩ := mΩ) S ν t]
      (fun ω => ∫ x, noiseProj S ν h t x ω * hf.aestronglyMeasurable.mk f x) :=
    @noiseProj_integral_meas Ω (⨆ t, noiseFiltration (mΩ := mΩ) S ν t) _ hG t _
      hf.aestronglyMeasurable.stronglyMeasurable_mk
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒢 hK.integral_prod_left
    (fun A _ _ => hKh.integral_prod_left.integrableOn) (fun A hA _ => ?_)
    (hV ▸ hVm.aestronglyMeasurable)).symm
  have hswap : ∀ {K : Ω × ℝ → ℝ}, Integrable K (ν.prod volume) →
      ∫ ω in A, ∫ x, K (ω, x) ∂volume ∂ν = ∫ x, ∫ ω in A, K (ω, x) ∂ν := fun hK' =>
    integral_integral_swap (hK'.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
  rw [hswap hKh, hswap hK]
  refine integral_congr_ae ?_
  filter_upwards [hft, hsec] with x hx hxi
  rw [integral_mul_const, integral_mul_const]
  congr 1
  rw [setIntegral_congr_ae (h𝒢 _ hA) (hx.mono fun ω hω _ => hω), setIntegral_condExp h𝒢 hxi hA]

/-- Linearity of the projection for differences. -/
theorem noiseProj_sub {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {h h' : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume))
    (hh' : MemLp (uncurryField h') 2 (ν.prod volume)) :
    uncurryField (noiseProj S ν fun s y ω => h s y ω - h' s y ω) =ᵐ[ν.prod volume]
      uncurryField (noiseProj S ν h) - uncurryField (noiseProj S ν h') :=
  (noiseRefMeasure_absolutelyContinuous ν).ae_le (condExp_sub (noiseProj_integrable hh) (noiseProj_integrable hh')
    (noiseProdSigma S ν))

/-- The projection of `c(ω) 𝟙_R(s, y)` is `𝔼[c | 𝒩_∞](ω) 𝟙_R(s, y)`. -/
theorem noiseProj_block {ν : Measure Ω} [IsProbabilityMeasure ν] (S : ℝ → ℝ → Ω → ℝ)
    {c : Ω → ℝ} (hc : Measurable c) {C : ℝ} (hC : ∀ ω, |c ω| ≤ C) (s t a b : ℝ) :
    uncurryField (noiseProj S ν
        fun r y ω => if s < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then c ω else 0) =ᵐ[ν.prod volume]
      uncurryField fun r y ω => if s < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then
        ν[c | ⨆ t, noiseFiltration (mΩ := mΩ) S ν t] ω else 0 := by
  let g : ℝ → ℝ → ℝ := fun r y => if s < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then 1 else 0
  have hgm : Measurable (Function.uncurry g) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    refine (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)))
  have hgb : ∃ C, ∀ r y, |g r y| ≤ C := ⟨1, fun r y => by
    simp only [g]; split_ifs <;> simp⟩
  have hci : Integrable c ν :=
    Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have e : (fun r y ω => if s < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then c ω else 0) =
      fun r y ω => g r y * c ω := by
    funext r y ω
    simp only [g]
    split_ifs <;> simp
  obtain ⟨C', hC'⟩ := hgb
  have hm := noiseProdSigma_le S ν
  have hsnd : Measurable[noiseProdSigma S ν, inferInstance] (Prod.snd : Ω × ℝ × ℝ → ℝ × ℝ) := by
    rw [noiseProdSigma_eq]
    exact measurable_iff_comap_le.2 le_sup_right
  have hG : StronglyMeasurable[noiseProdSigma S ν] fun p : Ω × ℝ × ℝ => g p.2.1 p.2.2 :=
    (hgm.comp hsnd).stronglyMeasurable
  have hcρ : Integrable (fun p : Ω × ℝ × ℝ => c p.1) (noiseRefMeasure ν) := hci.comp_fst _
  have hint : Integrable ((fun p : Ω × ℝ × ℝ => g p.2.1 p.2.2) * fun p => c p.1)
      (noiseRefMeasure ν) :=
    hcρ.bdd_mul (hG.mono hm).aestronglyMeasurable (ae_of_all _ fun p => hC' p.2.1 p.2.2)
  have h1 := condExp_mul_of_stronglyMeasurable_left hG hint hcρ
  have h2 : (noiseRefMeasure ν)[fun p => c p.1 | noiseProdSigma S ν] =ᵐ[noiseRefMeasure ν]
      fun p => ν[c | ⨆ t, noiseFiltration (mΩ := mΩ) S ν t] p.1 := by
    rw [noiseProdSigma_eq]
    exact noiseFiber_condExp_fst (noiseProj_iSup_le S ν) hci
  rw [uncurryField_noiseProj, e]
  refine (noiseRefMeasure_absolutelyContinuous ν).ae_le ?_
  filter_upwards [h1, h2] with p hp1 hp2
  have e2 : uncurryField (fun r y ω => g r y * c ω) =
      (fun p : Ω × ℝ × ℝ => g p.2.1 p.2.2) * fun p => c p.1 := rfl
  rw [e2, hp1, Pi.mul_apply, hp2]
  simp only [uncurryField, g]
  split_ifs <;> simp

/-- **Projection onto the noise**: `𝔼[∫ h dξ | 𝒩_∞] = ∫ ĥ dξ`, the integral on the right being
taken for the noise filtration `𝒩`. -/
theorem IsWalshIntegral.condExp_noise {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) :
    IsWalshIntegral (noiseFiltration S ν) S ν (noiseProj S ν h)
      (ν[X | ⨆ t, noiseFiltration S ν t]) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hS' := hS.noiseSheet
  have h𝒢 := noiseProj_iSup_le (mΩ := mΩ) S ν
  have hcongr : ∀ {h h' : ℝ → ℝ → Ω → ℝ} {X X' : Ω → ℝ},
      IsWalshIntegral (noiseFiltration S ν) S ν h X →
      uncurryField h =ᵐ[ν.prod volume] uncurryField h' → X =ᵐ[ν] X' →
      IsWalshIntegral (noiseFiltration S ν) S ν h' X' := fun hX hh hXX =>
    isWalshIntegral_noiseSheet_iff.1 ((isWalshIntegral_noiseSheet_iff.2 hX).congr_ae hS' hh hXX)
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    obtain ⟨C, hC⟩ := hbdd
    have hcm : Measurable c := hc.mono (𝓖.le s) le_rfl
    have hci : Integrable c ν :=
      Integrable.of_bound hcm.aestronglyMeasurable C (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hC ω)
    have hXi : Integrable (fun ω => c ω * rectMass S s t a b ω) ν :=
      ((IsWalshIntegral.isometry_lib hS (IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν)
        s t a b c hst hab hc ⟨C, hC⟩)).2.1).integrable one_le_two
    -- a bounded `𝒩_s`-measurable version of `𝔼[c | 𝒩_s]`
    set d : Ω → ℝ := ν[c | noiseFiltration S ν s] with hd
    let d' : Ω → ℝ := fun ω => max (-C) (min C (d ω))
    have hd'm : Measurable[noiseFiltration S ν s] d' :=
      (measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable))
    have hd'b : ∃ C' : ℝ, ∀ ω, |d' ω| ≤ C' := ⟨|C|, fun ω => by
      simp only [d', abs_le]
      constructor
      · exact (neg_le_neg (le_abs_self C)).trans (le_max_left _ _)
      · exact max_le (by linarith [neg_abs_le C, le_abs_self C])
          ((min_le_left _ _).trans (le_abs_self C))⟩
    have hdd' : d =ᵐ[ν] d' := by
      filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := noiseFiltration S ν s) (μ := ν)
        (ae_of_all _ hC)] with ω hω
      rw [abs_le] at hω
      simp only [d']
      rw [min_eq_right hω.2, max_eq_right hω.1]
    have hN : ν[c | ⨆ t, noiseFiltration S ν t] =ᵐ[ν] d' :=
      (hS.condExp_noise_eq hc hci).trans hdd'
    have hblock := IsWalshIntegral.block (𝓖 := noiseFiltration S ν) (S := S) (ν := ν)
      s t a b d' hst hab hd'm hd'b
    refine hcongr hblock ?_ ?_
    · refine EventuallyEq.trans ?_ (noiseProj_block S hcm hC s t a b).symm
      have := (Measure.quasiMeasurePreserving_fst (μ := ν)
        (ν := (volume : Measure (ℝ × ℝ)))).ae hN
      filter_upwards [this] with p hp
      simp only [uncurryField]
      rw [hp]
    · have hrm : StronglyMeasurable[⨆ t, noiseFiltration S ν t] (rectMass S s t a b) := by
        have h1 := hS'.measurable_rectMass_noise_le hst (le_refl t) a b
        have e : rectMass (noiseSheet S) s t a b = rectMass S s t a b :=
          funext (rectMass_noiseSheet S s t a b)
        rw [e] at h1
        exact (h1.mono (le_iSup (fun u => (noiseFiltration S ν u : MeasurableSpace Ω)) t)
          le_rfl).stronglyMeasurable
      have h1 := condExp_mul_of_stronglyMeasurable_right hrm hXi hci
      filter_upwards [h1, hN] with ω e1 e2
      rw [show (fun ω => c ω * rectMass S s t a b ω) = c * rectMass S s t a b from rfl, e1,
        Pi.mul_apply, e2]
  | add h h' X X' hX hX' ih ih' =>
    obtain ⟨hh, hX2, -⟩ := IsWalshIntegral.isometry_lib hS hX
    obtain ⟨hh', hX2', -⟩ := IsWalshIntegral.isometry_lib hS hX'
    refine hcongr (IsWalshIntegral.add _ _ _ _ ih ih') (noiseProj_add S hh hh').symm ?_
    exact (condExp_add (hX2.integrable one_le_two) (hX2'.integrable one_le_two) _).symm
  | limit h X hs Xs hXs hh hX hhs hXs' ih =>
    refine IsWalshIntegral.limit _ _ (fun k => noiseProj S ν (hs k))
      (fun k => ν[Xs k | ⨆ t, noiseFiltration S ν t]) ih (noiseProj_memLp S hh).1
      (hX.condExp one_le_two) ?_ ?_
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhs (fun _ => zero_le)
        fun k => ?_
      have hk := (IsWalshIntegral.isometry_lib hS (hXs k)).1
      rw [← eLpNorm_congr_ae (noiseProj_sub S hk hh)]
      exact (noiseProj_memLp S (h := fun s y ω => hs k s y ω - h s y ω) (hk.sub hh)).2
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hXs' (fun _ => zero_le)
        fun k => ?_
      have hk := ((IsWalshIntegral.isometry_lib hS (hXs k)).2.1).integrable one_le_two
      rw [← eLpNorm_congr_ae (condExp_sub hk (hX.integrable one_le_two) _)]
      exact eLpNorm_condExp_le_eLpNorm _ one_le_two

end QSSEPtoKPZ
