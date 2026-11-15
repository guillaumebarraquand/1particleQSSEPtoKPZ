/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.Defs
public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import QSSEPtoKPZ.WhiteNoise.TransferFactor

/-!
# Uniqueness in law for (7.13): auxiliary results (task K4)

* `noiseFun_condExp_integral`: conditional Fubini, `𝔼[∫ h(t,x) f(x) dx | 𝒩_∞] = ∫ ĥ(t,x) f(x) dx`
  with `ĥ = noiseProj S ν h`, for almost every `t` **and every** `f ∈ L²(ℝ)` (the null set of
  times does not depend on `f`; `condExp_integral_noiseProj` of `WhiteNoise/Projection.lean`
  has the quantifiers in the other order, which is not enough for (7.13), where the
  negligible set of times must serve all test functions at once).
* `noiseFun_exists_factor`: Doob–Dynkin for the projection, `ĥ = G(N, s, y)` a.e. with `G`
  measurable and `N = noiseMap S` the noise coordinates.
* Measure-theoretic bookkeeping on `Ω × [0,T] × ℝ` (`noiseFun_prod_restrict_eq`,
  `noiseFun_lintegral_eq`, `noiseFun_lintegral_transfer`) and the measurability of
  `(s, y) ↦ (g_{t-s} ⋆ f)(y)` (`noiseFun_measurable_heatConv`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### Measure-theoretic bookkeeping -/

/-- The rearrangement `(a, (b, c)) ↦ (b, (a, c))` preserves product measures. -/
theorem noiseFun_rearrange {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa]
    [SFinite μb] [SFinite μc] :
    MeasurePreserving (fun p : α × β × γ => (p.2.1, p.1, p.2.2))
      (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have h1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb μc)
  have h2 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod
    (MeasurePreserving.id μc)
  have h3 := measurePreserving_prodAssoc μb μa μc
  exact h3.comp (h2.comp h1)

/-- `ν ⊗ (Leb|_A ⊗ Leb) = (ν ⊗ Leb²)|_{Ω × A × ℝ}`. -/
theorem noiseFun_prod_restrict_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω)
    [SFinite ν] (A : Set ℝ) :
    ν.prod ((volume.restrict A).prod (volume : Measure ℝ)) =
      (ν.prod (volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ (A ×ˢ Set.univ)) := by
  calc ν.prod ((volume.restrict A).prod (volume : Measure ℝ))
      = (ν.restrict Set.univ).prod ((volume.restrict A).prod
          ((volume : Measure ℝ).restrict Set.univ)) := by
        simp only [Measure.restrict_univ]
    _ = _ := by
        rw [Measure.prod_restrict, Measure.prod_restrict, Measure.volume_eq_prod]

/-- Almost everywhere on `Ω × [0,T] × ℝ` gives almost everywhere on `Ω × ℝ × ℝ` off
`Ω × A × ℝ`. -/
theorem noiseFun_ae_of_ae_restrict {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    [SFinite ν] {A : Set ℝ} (hA : MeasurableSet A) {P : Ω × ℝ × ℝ → Prop}
    (h : ∀ᵐ p ∂(ν.prod ((volume.restrict A).prod volume)), P p) :
    ∀ᵐ p ∂(ν.prod (volume : Measure (ℝ × ℝ))), p.2.1 ∈ A → P p := by
  rw [noiseFun_prod_restrict_eq, ae_restrict_iff'
    (MeasurableSet.univ.prod (hA.prod MeasurableSet.univ))] at h
  filter_upwards [h] with p hp hpA
  exact hp ⟨Set.mem_univ _, hpA, Set.mem_univ _⟩

/-- Tonelli on `Ω × A × ℝ`: `∫ F d(ν ⊗ Leb|_A ⊗ Leb) = 𝔼 ∫_A ∫_ℝ F`. -/
theorem noiseFun_lintegral_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [SFinite ν]
    (A : Set ℝ) {F : Ω × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(ν.prod ((volume.restrict A).prod volume)) =
      ∫⁻ ω, (∫⁻ t in A, (∫⁻ x, F (ω, t, x))) ∂ν := by
  rw [lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact lintegral_prod _ (hF.comp (f := fun q : ℝ × ℝ => (ω, q)) (by fun_prop)).aemeasurable

/-- Change of variables `ω ↦ N(ω)` in a Lebesgue integral on `Ω × ℝ × ℝ`. -/
private lemma noiseFun_lintegral_map {Ω : Type*} {m : MeasurableSpace Ω} {ν : Measure Ω}
    [IsProbabilityMeasure ν] (μ : Measure (ℝ × ℝ)) [SFinite μ]
    {F : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) {N : Ω → ℝ≥0 × ℝ × ℝ → ℝ}
    (hN : Measurable N) :
    ∫⁻ p, F (N p.1, p.2) ∂(ν.prod μ) = ∫⁻ q, F q ∂((ν.map N).prod μ) := by
  rw [← Measure.map_id (μ := μ), Measure.map_prod_map _ _ hN measurable_id, Measure.map_id,
    lintegral_map hF (hN.prodMap measurable_id)]
  rfl

/-- Lebesgue integrals of functions of `(N, s, y)`, `N` the noise coordinates, are the same on
all spaces carrying a white noise. -/
theorem noiseFun_lintegral_transfer {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂}
    {S₁ : ℝ → ℝ → Ω₁ → ℝ} {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₁ : Measure Ω₁} {ν₂ : Measure Ω₂}
    (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂) (μ : Measure (ℝ × ℝ))
    [SFinite μ] {F : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (noiseMap S₂ p.1, p.2) ∂(ν₂.prod μ) = ∫⁻ p, F (noiseMap S₁ p.1, p.2) ∂(ν₁.prod μ) := by
  have : IsProbabilityMeasure ν₁ := h₁.isProbabilityMeasure
  have : IsProbabilityMeasure ν₂ := h₂.isProbabilityMeasure
  rw [noiseFun_lintegral_map μ hF h₂.measurable_noiseMap,
    noiseFun_lintegral_map μ hF h₁.measurable_noiseMap, h₁.map_noiseMap_eq h₂]

/-- Measurability of `(s, y) ↦ (g_{t-s} ⋆ f)(y)`. -/
theorem noiseFun_measurable_heatConv {f : ℝ → ℝ} (hf : Measurable f) (t : ℝ) :
    Measurable (fun q : ℝ × ℝ => heatConv (t - q.1) f q.2) := by
  have hm : Measurable (fun r : (ℝ × ℝ) × ℝ => heatKernel (t - r.1.1) (r.1.2 - r.2) * f r.2) := by
    refine Measurable.mul ?_ (hf.comp measurable_snd)
    unfold heatKernel; fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-! ### Conditional Fubini, uniformly in the test function -/

section CondFubini

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Sections of an `L²(μ ⊗ ν)` function in the second variable. -/
private lemma noiseFun_memLp_sect_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν' : Measure β} [SFinite μ] [SFinite ν'] {k : α × β → ℝ}
    (hk : MemLp k 2 (μ.prod ν')) : ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 ν' := by
  have hsq := (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  filter_upwards [hsq.prod_right_ae, hk.aestronglyMeasurable.prodMk_left] with x h1 h2
  exact (memLp_two_iff_integrable_sq h2).2 h1

/-- Sections of an `L²(μ ⊗ ν)` function in the first variable. -/
private lemma noiseFun_memLp_sect_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν' : Measure β} [SFinite μ] [SFinite ν'] {k : α × β → ℝ}
    (hk : MemLp k 2 (μ.prod ν')) : ∀ᵐ y ∂ν', MemLp (fun x => k (x, y)) 2 μ := by
  have hsq := (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  filter_upwards [hsq.prod_left_ae, hk.aestronglyMeasurable.prodMk_right] with y h1 h2
  exact (memLp_two_iff_integrable_sq h2).2 h1

/-- Parametric integrals of a strongly measurable function are strongly measurable. -/
private lemma noiseFun_integral_meas {α : Type*} [MeasurableSpace α] {G : α × ℝ × ℝ → ℝ}
    (hG : StronglyMeasurable G) (t : ℝ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun a => ∫ x, G (a, t, x) * f x :=
  StronglyMeasurable.integral_prod_right' (f := fun q : α × ℝ => G (q.1, t, q.2) * f q.2)
    ((hG.comp_measurable (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).mul
      (hf.comp_measurable measurable_snd))

/-- **Conditional Fubini, uniformly in the test function**: for `h ∈ L²(ν ⊗ Leb²)`, for almost
every `t`, for every `f ∈ L²(ℝ)`, `𝔼[∫ h(t,x) f(x) dx | 𝒩_∞] = ∫ ĥ(t,x) f(x) dx` almost surely
(`ĥ = noiseProj S ν h`). -/
theorem noiseFun_condExp_integral {ν : Measure Ω} [IsProbabilityMeasure ν]
    (S : ℝ → ℝ → Ω → ℝ) {h : ℝ → ℝ → Ω → ℝ} (hh : MemLp (uncurryField h) 2 (ν.prod volume)) :
    ∀ᵐ t, ∀ f : ℝ → ℝ, MemLp f 2 volume →
      ν[fun ω => ∫ x, h t x ω * f x | ⨆ t, noiseFiltration (mΩ := mΩ) S ν t] =ᵐ[ν]
        fun ω => ∫ x, noiseProj S ν h t x ω * f x := by
  have h𝒢 := noiseProj_iSup_le (mΩ := mΩ) S ν
  obtain ⟨hhat, -⟩ := noiseProj_memLp S hh
  have hre := noiseFun_rearrange (volume : Measure ℝ) ν (volume : Measure ℝ)
  rw [← Measure.volume_eq_prod] at hre
  have hfib := Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume) (noiseProj_ae_fiber S hh)
  filter_upwards [hfib,
    noiseFun_memLp_sect_left (hh.comp_measurePreserving hre),
    noiseFun_memLp_sect_left (hhat.comp_measurePreserving hre)]
    with t hft hkt hkht f hf
  have hfs : MemLp (fun q : Ω × ℝ => f q.2) 2 (ν.prod volume) :=
    hf.comp_measurePreserving measurePreserving_snd
  have hkt' : MemLp (fun q : Ω × ℝ => h t q.2 q.1) 2 (ν.prod volume) := hkt
  have hkht' : MemLp (fun q : Ω × ℝ => noiseProj S ν h t q.2 q.1) 2 (ν.prod volume) := hkht
  have hK : Integrable (fun q : Ω × ℝ => h t q.2 q.1 * f q.2) (ν.prod volume) :=
    hkt'.integrable_mul hfs
  have hKh : Integrable (fun q : Ω × ℝ => noiseProj S ν h t q.2 q.1 * f q.2) (ν.prod volume) :=
    hkht'.integrable_mul hfs
  have hsec : ∀ᵐ x, Integrable (fun ω => h t x ω) ν :=
    (noiseFun_memLp_sect_right hkt').mono fun x hx => hx.integrable one_le_two
  have hG := stronglyMeasurable_noiseProj S ν h
  rw [noiseProdSigma_eq] at hG
  have hV : (fun ω => ∫ x, noiseProj S ν h t x ω * f x) =
      fun ω => ∫ x, noiseProj S ν h t x ω * hf.aestronglyMeasurable.mk f x :=
    funext fun ω => integral_congr_ae (hf.aestronglyMeasurable.ae_eq_mk.mono fun x hx => by
      simp only [hx])
  have hVm : StronglyMeasurable[⨆ t, noiseFiltration (mΩ := mΩ) S ν t]
      (fun ω => ∫ x, noiseProj S ν h t x ω * hf.aestronglyMeasurable.mk f x) :=
    @noiseFun_integral_meas Ω (⨆ t, noiseFiltration (mΩ := mΩ) S ν t) _ hG t _
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

end CondFubini

/-! ### Doob–Dynkin for the projection onto the noise -/

section Factor

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- `𝒩_s ⊆ N⁻¹(noisePathSigma s) ∨ (null sets)`. -/
private lemma noiseFun_filtration_le_comap (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) (s : ℝ≥0) :
    noiseFiltration S ν s ≤
      MeasurableSpace.comap (noiseMap S) (noisePathSigma s) ⊔ nullSets ν := by
  refine sup_le_sup_right (inf_le_left.trans (iSup₂_le fun u hu => iSup₂_le fun a b => ?_)) _
  rw [show rectMass S 0 u a b = (fun w => w (u, a, b)) ∘ noiseMap S from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (le_iSup₂_of_le (f := fun (p : ℝ≥0 × ℝ × ℝ) (_ : p.1 ≤ s) =>
    MeasurableSpace.comap (fun w : ℝ≥0 × ℝ × ℝ → ℝ => w p) (borel ℝ)) (u, a, b) hu le_rfl)

/-- `𝒩_∞ ⊆ σ(N) ∨ (null sets)`. -/
private lemma noiseFun_iSup_le_comap (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    (⨆ t, noiseFiltration S ν t) ≤ MeasurableSpace.comap (noiseMap S) MeasurableSpace.pi ⊔
      nullSets ν :=
  iSup_le fun s => (noiseFun_filtration_le_comap S ν s).trans
    (sup_le_sup_right (MeasurableSpace.comap_mono (noisePathSigma_le s)) _)

/-- **Doob–Dynkin for the projection onto the noise**: for `h ∈ L²(ν ⊗ Leb²)`, the projection
`ĥ = noiseProj S ν h` is a.e. `G(N, s, y)`, with `G` measurable and `N = noiseMap S`. -/
theorem IsWhiteNoise.noiseFun_exists_factor (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ}
    (hh : MemLp (uncurryField h) 2 (ν.prod volume)) :
    ∃ G : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ, Measurable G ∧
      uncurryField (noiseProj S ν h) =ᵐ[ν.prod volume] fun p => G (noiseMap S p.1, p.2) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have h𝒢 := noiseProj_iSup_le (mΩ := mΩ) S ν
  have hNle : MeasurableSpace.comap (noiseMap S) MeasurableSpace.pi ≤ mΩ :=
    hS.noiseMap_comap_le_iSup.trans h𝒢
  set 𝒜 : MeasurableSpace (Ω × ℝ × ℝ) :=
    (MeasurableSpace.comap (noiseMap S) MeasurableSpace.pi).prod inferInstance with h𝒜
  have h1 : 𝒜 ≤ noiseProdSigma S ν := by
    rw [noiseProdSigma_eq]
    exact sup_le_sup (MeasurableSpace.comap_mono hS.noiseMap_comap_le_iSup) le_rfl
  have h2 : noiseProdSigma S ν ≤ noiseAugSets 𝒜 (noiseRefMeasure ν) := by
    rw [noiseProdSigma_eq]
    exact (sup_le_sup (MeasurableSpace.comap_mono (noiseFun_iSup_le_comap S ν)) le_rfl).trans
      (noiseAug_prod hNle)
  have eh := noiseAug_condExp_eq (P := noiseRefMeasure ν) (noiseProdSigma_le S ν) h1 h2
    (noiseProj_integrable hh)
  have h𝒜' : 𝒜 = MeasurableSpace.comap (Prod.map (noiseMap S) id)
      ((MeasurableSpace.pi : MeasurableSpace (ℝ≥0 × ℝ × ℝ → ℝ)).prod inferInstance) := by
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
  have hGm : StronglyMeasurable[MeasurableSpace.comap (Prod.map (noiseMap S) id)
      ((MeasurableSpace.pi : MeasurableSpace (ℝ≥0 × ℝ × ℝ → ℝ)).prod inferInstance)]
      ((noiseRefMeasure ν)[uncurryField h | 𝒜]) := by
    rw [← h𝒜']
    exact stronglyMeasurable_condExp
  obtain ⟨G, hG, hGe⟩ := StronglyMeasurable.exists_eq_measurable_comp hGm
  refine ⟨G, hG.measurable, (noiseRefMeasure_absolutelyContinuous ν).ae_le ?_⟩
  rw [uncurryField_noiseProj]
  exact eh.trans (EventuallyEq.of_eq hGe)

end Factor

end QSSEPtoKPZ
