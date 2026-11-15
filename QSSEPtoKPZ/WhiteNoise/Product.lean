/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshExists
public import QSSEPtoKPZ.WhiteNoise.ProductAux
public import QSSEPtoKPZ.Martingales.CovariationAlgebra

/-!
# Enlargement of the probability space by a product (task G9)

INTERFACE FILE (task I0″ of Stage 4): the definition is complete; the statements below are
interfaces, proved by task G9. See `docs/stage4-design.md`, Sections 1.2 (f) and 3.3, and
`docs/stage4-interfaces.md`.

"Possibly after enlarging the probability space" (Proposition 7.2, decision D7″): the product of
`(Ω₁, μ₁, 𝒢₁)` with a space `(Ω₂, μ₂, 𝒢₂)` carrying a white noise, with the filtration
`(𝒢₁_t ⊗ 𝒢₂_t) ∨ (null sets)`. Martingales and brackets of either factor lift; white noises of
the second factor lift; a martingale of the first factor has zero covariation with any Walsh
integral process against the lifted white noise (independence).

Proofs (task G9, auxiliary results in `WhiteNoise/ProductAux.lean`): conditional expectations of
functions of `ω₁` are computed on the rectangles `B × C` and extended by a Dynkin argument; the
lifted white noise is checked on rectangles too. For the orthogonality, the lifted noise is also
a white noise for the larger filtration `𝒦_t = (𝒢₁_∞ ⊗ 𝒢₂_t) ∨ 𝒩`, so that
`𝔼[X_t - X_s | 𝒦_s] = 0` (martingale property of the Walsh integral, `prodNoise_walsh_restrict`);
since `M_t - M_s` depends on `ω₁` only, it is `𝒦_s`-measurable, whence
`𝔼[(M_t - M_s)(X_t - X_s) | 𝒢_s] = 0`, and `M_t X_t - M_s X_s` is a martingale increment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- The product filtration `(𝒢₁_t ⊗ 𝒢₂_t) ∨ σ(P-null sets)` on `Ω₁ × Ω₂`. -/
def prodFiltration (𝒢₁ : Filtration ℝ≥0 m₁) (𝒢₂ : Filtration ℝ≥0 m₂) (P : Measure (Ω₁ × Ω₂)) :
    Filtration ℝ≥0 (m₁.prod m₂) :=
  nullAug P
    { seq := fun t => (𝒢₁ t).prod (𝒢₂ t)
      mono' := fun _ _ h => sup_le_sup (MeasurableSpace.comap_mono (𝒢₁.mono h))
        (MeasurableSpace.comap_mono (𝒢₂.mono h))
      le' := fun t => sup_le_sup (MeasurableSpace.comap_mono (𝒢₁.le t))
        (MeasurableSpace.comap_mono (𝒢₂.le t)) }

variable {𝒢₁ : Filtration ℝ≥0 m₁} {𝒢₂ : Filtration ℝ≥0 m₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
  {T : ℝ}

/-- The first factor's filtration is contained in the product filtration. -/
theorem comap_fst_le_prodFiltration (P : Measure (Ω₁ × Ω₂)) (t : ℝ≥0) :
    (𝒢₁ t).comap Prod.fst ≤ prodFiltration 𝒢₁ 𝒢₂ P t :=
  le_sup_left.trans le_sup_left

/-- The sets of the product filtration: `(𝒢₁_t ⊗ 𝒢₂_t) ∨ σ(P-null sets)`. -/
theorem prodFiltration_apply (P : Measure (Ω₁ × Ω₂)) (t : ℝ≥0) :
    prodFiltration 𝒢₁ 𝒢₂ P t = (𝒢₁ t).prod (𝒢₂ t) ⊔ nullSets P :=
  rfl

/-- The second factor's filtration is contained in the product filtration. -/
theorem comap_snd_le_prodFiltration (P : Measure (Ω₁ × Ω₂)) (t : ℝ≥0) :
    (𝒢₂ t).comap Prod.snd ≤ prodFiltration 𝒢₁ 𝒢₂ P t :=
  le_sup_right.trans le_sup_left

/-- Conditional expectations of functions of the first factor, for the product filtration. -/
theorem prodFiltration_condExp_fst [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℝ} (hX : Integrable X μ₁) (s : ℝ≥0) :
    (μ₁.prod μ₂)[fun ω => X ω.1 | prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s]
      =ᵐ[μ₁.prod μ₂] fun ω => μ₁[X | 𝒢₁ s] ω.1 :=
  prodNoise_condExp_fst (𝒢₁.le s) (𝒢₂.le s) hX

/-- Continuous square-integrable martingales of the first factor lift to the product. -/
theorem IsCL2Mart.prod_fst [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {M : ℝ → Ω₁ → ℝ} (h : IsCL2Mart T 𝒢₁ M μ₁) :
    IsCL2Mart T (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)) (fun t ω => M t ω.1) (μ₁.prod μ₂) where
  cont := prodNoise_ae_fst h.cont
  memLp t ht := (h.memLp t ht).comp_measurePreserving measurePreserving_fst
  condExp s t hst ht :=
    (prodFiltration_condExp_fst ((h.memLp t ht).integrable one_le_two) s).trans
      (prodNoise_ae_fst (h.condExp s t hst ht))

/-- Covariations of the first factor lift to the product. -/
theorem HasCovariation.prod_fst [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {M N A : ℝ → Ω₁ → ℝ} (h : HasCovariation T 𝒢₁ M N A μ₁) :
    HasCovariation T (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)) (fun t ω => M t ω.1)
      (fun t ω => N t ω.1) (fun t ω => A t ω.1) (μ₁.prod μ₂) where
  left := h.left.prod_fst
  right := h.right.prod_fst
  integrable_cov t ht := prodNoise_integrable_fst (h.integrable_cov t ht)
  zero := prodNoise_ae_fst h.zero
  cont_cov := prodNoise_ae_fst h.cont_cov
  bv := prodNoise_ae_fst h.bv
  condExp_mul s t hst ht :=
    (prodFiltration_condExp_fst (((h.left.memLp t ht).integrable_mul
      (h.right.memLp t ht)).sub (h.integrable_cov t ht)) s).trans
      (prodNoise_ae_fst (h.condExp_mul s t hst ht))

/-- Brackets of the first factor lift to the product. -/
theorem HasBracket.prod_fst [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {M A : ℝ → Ω₁ → ℝ} (h : HasBracket T 𝒢₁ M A μ₁) :
    HasBracket T (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)) (fun t ω => M t ω.1)
      (fun t ω => A t ω.1) (μ₁.prod μ₂) where
  toIsCL2Mart := h.toIsCL2Mart.prod_fst
  integrable_bracket t ht := prodNoise_integrable_fst (h.integrable_bracket t ht)
  zero := prodNoise_ae_fst h.zero
  mono := prodNoise_ae_fst h.mono
  cont_bracket := prodNoise_ae_fst h.cont_bracket
  condExp_sq s t hst ht :=
    (prodFiltration_condExp_fst ((h.memLp t ht).integrable_sq.sub
      (h.integrable_bracket t ht)) s).trans (prodNoise_ae_fst (h.condExp_sq s t hst ht))

/-- White noises of the second factor lift to the product. -/
theorem IsWhiteNoise.prod_snd [IsProbabilityMeasure μ₁] {S : ℝ → ℝ → Ω₂ → ℝ}
    (hS : IsWhiteNoise 𝒢₂ S μ₂) :
    IsWhiteNoise (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)) (fun t x ω => S t x ω.2) (μ₁.prod μ₂) := by
  have : IsProbabilityMeasure μ₂ := hS.isProbabilityMeasure
  have hmeas : ∀ s t : ℝ≥0, ∀ a b : ℝ, Measurable (rectMass S s t a b) := by
    intro s t a b
    have h1 : ∀ (u : ℝ≥0) x, Measurable (S u x) := fun u x => (hS.adapted u x).mono (𝒢₂.le u) le_rfl
    exact (((h1 t b).sub (h1 t a)).sub (h1 s b)).add (h1 s a)
  refine ⟨fun t x => ?_, fun s t a b hst hab => ?_, fun s t hst k a ha => ?_, fun s t hst => ?_⟩
  · exact ((hS.adapted t x).comp (@measurable_snd _ _ (𝒢₁ t) (𝒢₂ t))).mono le_sup_left le_rfl
  · exact (hS.gaussian s t a b hst hab).comp measurePreserving_snd.hasLaw
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro J sets hsets
    have e : ∀ i, (fun ω : Ω₁ × Ω₂ => rectMass (fun t x ω => S t x ω.2) s t (a i.castSucc)
        (a i.succ) ω) ⁻¹' sets i = Prod.snd ⁻¹' (rectMass S s t (a i.castSucc) (a i.succ) ⁻¹'
          sets i) := fun _ => rfl
    have hm : ∀ i ∈ J, MeasurableSet (rectMass S s t (a i.castSucc) (a i.succ) ⁻¹' sets i) :=
      fun i hi => hmeas _ _ _ _ (hsets i hi)
    have hpre : ∀ E, MeasurableSet E → (μ₁.prod μ₂) (Prod.snd ⁻¹' E) = μ₂ E :=
      fun E hE => measurePreserving_snd.measure_preimage hE.nullMeasurableSet
    simp_rw [e, ← Set.preimage_iInter₂]
    rw [hpre _ (Finset.measurableSet_biInter J hm), Finset.prod_congr rfl
      fun i hi => hpre _ (hm i hi)]
    exact (hS.indep s t hst k a ha).measure_inter_preimage_eq_mul J hsets
  · have hF : (⨆ (a : ℝ) (b : ℝ), MeasurableSpace.comap (rectMass S s t a b) inferInstance) ≤ m₂ :=
      iSup₂_le fun a b => (hmeas s t a b).comap_le
    have h := prodNoise_indep_comap_snd (μ₁ := μ₁) hF (𝒢₁.le s) (𝒢₂.le s) (hS.indep_past s t hst)
    refine indep_of_indep_of_le_left
      (prodNoise_indep_sup_nullSets (prodNoise_prod_le (𝒢₁.le s) (𝒢₂.le s)) h) ?_
    refine iSup₂_le fun a b => ?_
    rw [show rectMass (fun t x ω => S t x ω.2) s t a b = rectMass S s t a b ∘ Prod.snd from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (le_iSup₂ (f := fun a b => MeasurableSpace.comap (rectMass S s t a b) inferInstance) a b)

/-- Predictable fields of the first factor are predictable on the product. -/
theorem measurable_predictable_prod_fst (P : Measure (Ω₁ × Ω₂)) {h : ℝ → ℝ → Ω₁ → ℝ}
    (hh : Measurable[(𝒢₁.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω₁) × ℝ => h p.1.1 p.2 p.1.2) :
    Measurable[((prodFiltration 𝒢₁ 𝒢₂ P).predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × (Ω₁ × Ω₂)) × ℝ => h p.1.1 p.2 p.1.2.1 := by
  let ψ : ℝ≥0 × (Ω₁ × Ω₂) → ℝ≥0 × Ω₁ := fun q => (q.1, q.2.1)
  have hψ : Measurable[(prodFiltration 𝒢₁ 𝒢₂ P).predictable, 𝒢₁.predictable] ψ := by
    refine @measurable_generateFrom _ _ ((prodFiltration 𝒢₁ 𝒢₂ P).predictable) _ _ ?_
    rintro _ (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
    · have e : ψ ⁻¹' ({⊥} ×ˢ A) = {⊥} ×ˢ (Prod.fst ⁻¹' A) := by
        ext q
        simp [ψ]
      rw [e]
      exact MeasurableSpace.measurableSet_generateFrom
        (Or.inl ⟨_, comap_fst_le_prodFiltration P ⊥ _ ⟨A, hA, rfl⟩, rfl⟩)
    · have e : ψ ⁻¹' (Set.Ioi i ×ˢ A) = Set.Ioi i ×ˢ (Prod.fst ⁻¹' A) := by
        ext q
        simp [ψ]
      rw [e]
      exact MeasurableSpace.measurableSet_generateFrom
        (Or.inr ⟨i, _, comap_fst_le_prodFiltration P i _ ⟨A, hA, rfl⟩, rfl⟩)
  have hΦ : Measurable[((prodFiltration 𝒢₁ 𝒢₂ P).predictable).prod (borel ℝ),
      (𝒢₁.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × (Ω₁ × Ω₂)) × ℝ => (ψ p.1, p.2) :=
    Measurable.prodMk (m := ((prodFiltration 𝒢₁ 𝒢₂ P).predictable).prod (borel ℝ))
      (hψ.comp (@measurable_fst _ _ ((prodFiltration 𝒢₁ 𝒢₂ P).predictable) (borel ℝ)))
      (@measurable_snd _ _ ((prodFiltration 𝒢₁ 𝒢₂ P).predictable) (borel ℝ))
  exact hh.comp hΦ

/-- **Orthogonality**: a martingale of the first factor has zero covariation with a Walsh
integral process against the white noise of the second factor (lifted to the product). -/
theorem hasCovariation_prod_fst_walsh [IsProbabilityMeasure μ₁] {S : ℝ → ℝ → Ω₂ → ℝ}
    (hS : IsWhiteNoise 𝒢₂ S μ₂) {M : ℝ → Ω₁ → ℝ} (hM : IsCL2Mart T 𝒢₁ M μ₁)
    {k : ℝ → ℝ → Ω₁ × Ω₂ → ℝ} {X : ℝ → Ω₁ × Ω₂ → ℝ}
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T, IsWalshIntegral (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂))
      (fun t x ω => S t x ω.2) (μ₁.prod μ₂)
      (fun s y ω => if 0 < s ∧ s ≤ t then k s y ω else 0) (X t))
    (hXc : IsCL2Mart T (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)) X (μ₁.prod μ₂)) :
    HasCovariation T (prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)) (fun t ω => M t ω.1) X
      (fun _ _ => 0) (μ₁.prod μ₂) := by
  have : IsProbabilityMeasure μ₂ := hS.isProbabilityMeasure
  -- the larger filtration `𝒦_t = (𝒢₁_∞ ⊗ 𝒢₂_t) ∨ 𝒩`, for which the lifted noise is still white
  let K : Filtration ℝ≥0 (m₁.prod m₂) :=
    prodFiltration (Filtration.const ℝ≥0 m₁ le_rfl) 𝒢₂ (μ₁.prod μ₂)
  have hSK : IsWhiteNoise K (fun t x ω => S t x ω.2) (μ₁.prod μ₂) := hS.prod_snd
  have hGK : prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) ≤ K := fun t =>
    sup_le_sup_right (sup_le_sup_right (MeasurableSpace.comap_mono (𝒢₁.le t)) _) _
  have hMG := hM.prod_fst (𝒢₂ := 𝒢₂) (μ₂ := μ₂)
  refine ⟨hMG, hXc, fun _ _ => integrable_zero _ _ _, ae_of_all _ fun _ => rfl,
    ae_of_all _ fun _ => continuousOn_const, ae_of_all _ fun _ => ?_, fun s t hst ht => ?_⟩
  · rw [BoundedVariationOn, eVariationOn.constant_on]
    · exact ENNReal.zero_ne_top
    · exact (Set.subsingleton_singleton (a := (0 : ℝ))).anti (by rintro _ ⟨x, -, rfl⟩; rfl)
  have hsT : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hU := hMG.memLp t ht
  have hUs := hMG.memLp s hsT
  have hXt := hXc.memLp t ht
  have hXs := hXc.memLp s hsT
  have hYint : Integrable (fun ω => X t ω - X s ω) (μ₁.prod μ₂) :=
    (hXt.sub hXs).integrable one_le_two
  -- `𝔼[X_t - X_s | 𝒦_s] = 0`: martingale property of the Walsh integral for `𝒦`
  have hWt := (hX t ⟨t.2, ht⟩).mono_filtration hGK
  have hWs := (hX s ⟨s.2, hsT⟩).mono_filtration hGK
  obtain ⟨Y', hY', hYY'⟩ := prodNoise_walsh_restrict hSK (hWt.sub hWs) s
  have hY'0 : Y' =ᵐ[μ₁.prod μ₂] 0 := by
    refine hY'.ae_eq_lib hSK (IsWalshIntegral.zero _ _ _) (ae_of_all _ fun p => ?_)
    by_cases h1 : p.2.1 ≤ s
    · have h2 : p.2.1 ≤ t := h1.trans (by exact_mod_cast hst)
      simp [uncurryField, h1, h2]
    · simp [uncurryField, h1]
  have hint_set : ∀ E, MeasurableSet[K s] E →
      ∫ ω in E, (X t ω - X s ω) ∂(μ₁.prod μ₂) = 0 := by
    intro E hE
    have hEm : MeasurableSet E := K.le s E hE
    have h := hYY' (E.indicator fun _ => 1) (measurable_const.indicator hE)
      ⟨1, fun ω => by by_cases h : ω ∈ E <;> simp [h]⟩
    have e1 : ∀ V : Ω₁ × Ω₂ → ℝ,
        (fun ω => E.indicator (fun _ => (1 : ℝ)) ω * V ω) = E.indicator V := by
      intro V
      funext ω
      by_cases h : ω ∈ E <;> simp [h]
    rw [e1, e1, integral_indicator hEm, integral_indicator hEm] at h
    rw [h, integral_congr_ae (ae_restrict_of_ae hY'0)]
    simp
  have hcK : (μ₁.prod μ₂)[fun ω => X t ω - X s ω | K s] =ᵐ[μ₁.prod μ₂] 0 :=
    (ae_eq_condExp_of_forall_setIntegral_eq (K.le s) hYint (fun _ _ _ => integrableOn_zero)
      (fun E hE _ => by rw [hint_set E hE]; simp) aestronglyMeasurable_zero).symm
  -- `𝔼[(M_t - M_s)(X_t - X_s) | 𝒢_s] = 0`
  have hD : AEStronglyMeasurable[K s] (fun ω => M t ω.1 - M s ω.1) (μ₁.prod μ₂) := by
    have hle : m₁.comap Prod.fst ≤ K s := le_sup_left.trans le_sup_left
    exact ((prodNoise_aestronglyMeasurable_fst (hM.memLp t ht).aestronglyMeasurable).sub
      (prodNoise_aestronglyMeasurable_fst (hM.memLp s hsT).aestronglyMeasurable)).mono hle
  have hDY : ∀ A, MeasurableSet[prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s] A →
      ∫ ω in A, (M t ω.1 - M s ω.1) * (X t ω - X s ω) ∂(μ₁.prod μ₂) = 0 := by
    intro A hA
    have hAK : MeasurableSet[K s] A := hGK s A hA
    have hAm : MeasurableSet A := K.le s A hAK
    set V := A.indicator fun ω : Ω₁ × Ω₂ => M t ω.1 - M s ω.1 with hVdef
    have hV : AEStronglyMeasurable[K s] V (μ₁.prod μ₂) := by
      obtain ⟨g, hg, hfg⟩ := hD
      exact ⟨A.indicator g, hg.indicator hAK,
        hfg.mono fun ω hω => by by_cases h : ω ∈ A <;> simp [V, h, hω]⟩
    have hV2 : MemLp V 2 (μ₁.prod μ₂) := (hU.sub hUs).indicator hAm.nullMeasurableSet
    have hVY : Integrable (V * fun ω => X t ω - X s ω) (μ₁.prod μ₂) :=
      hV2.integrable_mul (hXt.sub hXs)
    have e : ∫ ω in A, (M t ω.1 - M s ω.1) * (X t ω - X s ω) ∂(μ₁.prod μ₂) =
        ∫ ω, (V * fun ω => X t ω - X s ω) ω ∂(μ₁.prod μ₂) := by
      rw [← integral_indicator hAm]
      congr 1
      funext ω
      by_cases h : ω ∈ A <;> simp [V, h]
    rw [e, ← integral_condExp (K.le s)]
    have h := condExp_mul_of_aestronglyMeasurable_left hV hVY hYint
    have h0 : (μ₁.prod μ₂)[V * fun ω => X t ω - X s ω | K s] =ᵐ[μ₁.prod μ₂] 0 := by
      filter_upwards [h, hcK] with ω h1 h2
      rw [h1, Pi.mul_apply, h2]
      simp
    rw [integral_congr_ae h0]
    simp
  have hi1 : Integrable (fun ω => (M t ω.1 - M s ω.1) * (X t ω - X s ω)) (μ₁.prod μ₂) :=
    (hU.sub hUs).integrable_mul (hXt.sub hXs)
  have hc1 : (μ₁.prod μ₂)[fun ω => (M t ω.1 - M s ω.1) * (X t ω - X s ω) |
      prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s] =ᵐ[μ₁.prod μ₂] 0 :=
    (ae_eq_condExp_of_forall_setIntegral_eq ((prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂)).le s) hi1
      (fun _ _ _ => integrableOn_zero) (fun A hA _ => by rw [hDY A hA]; simp)
      aestronglyMeasurable_zero).symm
  -- `𝔼[X_s (M_t - M_s) | 𝒢_s] = 0` and `𝔼[M_s X_t | 𝒢_s] = M_s X_s`
  have hXsG : AEStronglyMeasurable[prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s] (X s) (μ₁.prod μ₂) :=
    ⟨_, stronglyMeasurable_condExp, (hXc.condExp s s le_rfl hsT).symm⟩
  have hUsG : AEStronglyMeasurable[prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s] (fun ω => M s ω.1)
      (μ₁.prod μ₂) :=
    ⟨_, stronglyMeasurable_condExp, (hMG.condExp s s le_rfl hsT).symm⟩
  have hcD : (μ₁.prod μ₂)[fun ω => M t ω.1 - M s ω.1 | prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s]
      =ᵐ[μ₁.prod μ₂] 0 := by
    refine (condExp_sub (hU.integrable one_le_two) (hUs.integrable one_le_two) _).trans ?_
    filter_upwards [hMG.condExp s t hst ht, hMG.condExp s s le_rfl hsT] with ω h1 h2
    simp [h1, h2]
  have hi2 : Integrable (fun ω => X s ω * (M t ω.1 - M s ω.1)) (μ₁.prod μ₂) :=
    hXs.integrable_mul (hU.sub hUs)
  have hi3 : Integrable (fun ω => M s ω.1 * X t ω) (μ₁.prod μ₂) := hUs.integrable_mul hXt
  have hc2 : (μ₁.prod μ₂)[fun ω => X s ω * (M t ω.1 - M s ω.1) |
      prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s] =ᵐ[μ₁.prod μ₂] 0 :=
    (condExp_mul_of_aestronglyMeasurable_left hXsG hi2
      ((hU.sub hUs).integrable one_le_two)).trans (hcD.mono fun ω hω => by simp [hω])
  have hc3 : (μ₁.prod μ₂)[fun ω => M s ω.1 * X t ω | prodFiltration 𝒢₁ 𝒢₂ (μ₁.prod μ₂) s]
      =ᵐ[μ₁.prod μ₂] fun ω => M s ω.1 * X s ω :=
    (condExp_mul_of_aestronglyMeasurable_left hUsG hi3 (hXt.integrable one_le_two)).trans
      ((hXc.condExp s t hst ht).mono fun ω hω => by simp [hω])
  -- conclusion: `M_t X_t = (M_t - M_s)(X_t - X_s) + X_s (M_t - M_s) + M_s X_t`
  have e : (fun ω => M t ω.1 * X t ω - (fun _ _ => (0 : ℝ)) t ω) =
      (fun ω => (M t ω.1 - M s ω.1) * (X t ω - X s ω)) + (fun ω => X s ω * (M t ω.1 - M s ω.1))
        + (fun ω => M s ω.1 * X t ω) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [e]
  refine (condExp_add (hi1.add hi2) hi3 _).trans ?_
  refine ((condExp_add hi1 hi2 _).add EventuallyEq.rfl).trans ?_
  filter_upwards [hc1, hc2, hc3] with ω h1 h2 h3
  simp [h1, h2, h3]

end QSSEPtoKPZ
