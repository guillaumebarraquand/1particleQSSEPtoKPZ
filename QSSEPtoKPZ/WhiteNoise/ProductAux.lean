/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshExists
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Auxiliary results for the enlargement by a product (task G9)

Generic tools for `WhiteNoise/Product.lean`.

* Lifting along the first projection of `(Ω₁ × Ω₂, μ₁ ⊗ μ₂)`: almost sure statements,
  integrability, and conditional expectations: for `X ∈ L¹(μ₁)` and sub-σ-algebras `𝒜₁`, `𝒜₂`,
  `𝔼[X ∘ π₁ | (𝒜₁ ⊗ 𝒜₂) ∨ 𝒩] = 𝔼[X | 𝒜₁] ∘ π₁` (`prodNoise_condExp_fst`), by a Dynkin argument
  on the rectangles `B × C` (`prodNoise_setIntegral_eq_of_rect`).
* Independence: `σ(Y ∘ π₂)` is independent of `𝒜₁ ⊗ 𝒜₂` if `σ(Y)` is independent of `𝒜₂`
  (`prodNoise_indep_comap_snd`); independence survives the augmentation by null sets
  (`prodNoise_indep_sup_nullSets`).
* **Martingale property of the Walsh integral** (`prodNoise_walsh_restrict`): for every Walsh
  integral `X = ∫ h dξ` and every `s`, the integral `X' = ∫ 𝟙_{r ≤ s} h dξ` exists and
  `𝔼[W X] = 𝔼[W X']` for every bounded `𝒢_s`-measurable `W`. Proof by induction on the
  definition of `IsWalshIntegral` (the blocks straddling `s` are cut at `s`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### Lifting along the first projection -/

section Lift

variable {Ω₁ Ω₂ : Type*} {n₁ : MeasurableSpace Ω₁} {n₂ F : MeasurableSpace Ω₂}
  {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}

/-- Almost sure statements on `Ω₁` lift to `Ω₁ × Ω₂`. -/
theorem prodNoise_ae_fst [IsProbabilityMeasure μ₂] {p : Ω₁ → Prop} (h : ∀ᵐ ω ∂μ₁, p ω) :
    ∀ᵐ ω ∂(μ₁.prod μ₂), p ω.1 :=
  measurePreserving_fst.quasiMeasurePreserving.ae h

/-- Integrability lifts along the first projection. -/
theorem prodNoise_integrable_fst [IsProbabilityMeasure μ₂] {X : Ω₁ → ℝ} (hX : Integrable X μ₁) :
    Integrable (fun ω : Ω₁ × Ω₂ => X ω.1) (μ₁.prod μ₂) :=
  memLp_one_iff_integrable.1
    ((memLp_one_iff_integrable.2 hX).comp_measurePreserving measurePreserving_fst)

/-- An almost everywhere strongly measurable function of `ω₁` is, as a function on the product,
almost everywhere strongly measurable for `σ(π₁)`. -/
theorem prodNoise_aestronglyMeasurable_fst [IsProbabilityMeasure μ₂] {X : Ω₁ → ℝ}
    (hX : AEStronglyMeasurable X μ₁) :
    AEStronglyMeasurable[m₁.comap Prod.fst] (fun ω : Ω₁ × Ω₂ => X ω.1) (μ₁.prod μ₂) := by
  obtain ⟨g, hg, hXg⟩ := hX
  exact ⟨fun ω => g ω.1, hg.comp_measurable (comap_measurable Prod.fst), prodNoise_ae_fst hXg⟩

/-- The product of two sub-σ-algebras is a sub-σ-algebra of the product. -/
theorem prodNoise_prod_le (h₁ : n₁ ≤ m₁)
    (h₂ : n₂ ≤ m₂) : n₁.prod n₂ ≤ m₁.prod m₂ :=
  sup_le_sup (MeasurableSpace.comap_mono h₁) (MeasurableSpace.comap_mono h₂)

/-- **Dynkin argument on rectangles**: two integrable functions with the same integrals on the
rectangles `B × C`, `B ∈ 𝒜₁`, `C ∈ 𝒜₂`, have the same integrals on the sets of `𝒜₁ ⊗ 𝒜₂`. -/
theorem prodNoise_setIntegral_eq_of_rect
    (h₁ : n₁ ≤ m₁) (h₂ : n₂ ≤ m₂) {P : Measure (Ω₁ × Ω₂)} {f g : Ω₁ × Ω₂ → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hrect : ∀ B C, MeasurableSet[n₁] B → MeasurableSet[n₂] C →
      ∫ ω in B ×ˢ C, f ω ∂P = ∫ ω in B ×ˢ C, g ω ∂P) :
    ∀ A, MeasurableSet[n₁.prod n₂] A → ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P := by
  have hle := prodNoise_prod_le h₁ h₂
  have huniv : ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
    have := hrect Set.univ Set.univ (@MeasurableSet.univ _ n₁) (@MeasurableSet.univ _ n₂)
    simpa using this
  intro A hA
  refine @MeasurableSpace.induction_on_inter _ (n₁.prod n₂)
    (fun A _ => ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P) _
    (@generateFrom_prod Ω₁ Ω₂ n₁ n₂).symm (@isPiSystem_prod Ω₁ Ω₂ n₁ n₂) ?_ ?_ ?_ ?_ A hA
  · simp
  · rintro _ ⟨B, hB, C, hC, rfl⟩
    exact hrect B C hB hC
  · intro t htm ih
    have htm' := hle t htm
    rw [setIntegral_compl htm' hf, setIntegral_compl htm' hg, ih, huniv]
  · intro F hd hFm ih
    rw [integral_iUnion (fun i => hle _ (hFm i)) hd hf.integrableOn,
      integral_iUnion (fun i => hle _ (hFm i)) hd hg.integrableOn]
    exact tsum_congr ih

/-- **Conditional expectations lift along the first projection**: for `X ∈ L¹(μ₁)`,
`𝔼[X ∘ π₁ | (𝒜₁ ⊗ 𝒜₂) ∨ 𝒩] = 𝔼[X | 𝒜₁] ∘ π₁` almost surely on `(Ω₁ × Ω₂, μ₁ ⊗ μ₂)`. -/
theorem prodNoise_condExp_fst [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : n₁ ≤ m₁) (h₂ : n₂ ≤ m₂) {X : Ω₁ → ℝ} (hX : Integrable X μ₁) :
    (μ₁.prod μ₂)[fun ω => X ω.1 | n₁.prod n₂ ⊔ nullSets (μ₁.prod μ₂)]
      =ᵐ[μ₁.prod μ₂] fun ω => μ₁[X | n₁] ω.1 := by
  have hle := prodNoise_prod_le h₁ h₂
  refine (condExp_sup_nullSets hle _).trans ?_
  have hci : Integrable (fun ω : Ω₁ × Ω₂ => μ₁[X | n₁] ω.1) (μ₁.prod μ₂) :=
    prodNoise_integrable_fst integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle (prodNoise_integrable_fst hX)
    (fun _ _ _ => hci.integrableOn) ?_ ?_).symm
  · intro A hA _
    refine prodNoise_setIntegral_eq_of_rect h₁ h₂ hci (prodNoise_integrable_fst hX) ?_ A hA
    intro B C hB _
    have e1 := setIntegral_prod_mul (μ := μ₁) (ν := μ₂) (μ₁[X | n₁]) (fun _ => (1 : ℝ)) B C
    have e2 := setIntegral_prod_mul (μ := μ₁) (ν := μ₂) X (fun _ => (1 : ℝ)) B C
    simp only [mul_one] at e1 e2
    rw [e1, e2, setIntegral_condExp h₁ hX hB]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (@measurable_fst _ _ n₁ n₂)).aestronglyMeasurable

end Lift

/-! ### Independence on the product -/

section Indep

/-- Independence survives the augmentation of one of the σ-algebras by the null sets. -/
theorem prodNoise_indep_sup_nullSets {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {m m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ) (h : Indep m m' μ) :
    Indep m (m' ⊔ nullSets μ) μ := by
  rw [Indep_iff] at h ⊢
  intro t1 t2 h1 h2
  obtain ⟨-, F, hF, htF⟩ := (measurableSet_sup_nullSets_iff hm').1 h2
  rw [measure_congr (ae_eq_set_inter (EventuallyEq.refl _ t1) htF), measure_congr htF]
  exact h t1 F h1 hF

variable {Ω₁ Ω₂ : Type*} {n₁ : MeasurableSpace Ω₁} {n₂ F : MeasurableSpace Ω₂}
  {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}

/-- If `𝓕` is independent of `𝒜₂` under `μ₂`, then `π₂⁻¹ 𝓕` is independent of `𝒜₁ ⊗ 𝒜₂` under
`μ₁ ⊗ μ₂`. -/
theorem prodNoise_indep_comap_snd [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hF : F ≤ m₂) (h₁ : n₁ ≤ m₁)
    (h₂ : n₂ ≤ m₂) (h : Indep F n₂ μ₂) :
    Indep (F.comap Prod.snd) (n₁.prod n₂) (μ₁.prod μ₂) := by
  refine IndepSets.indep ((MeasurableSpace.comap_mono hF).trans le_sup_right)
    (prodNoise_prod_le h₁ h₂) (@MeasurableSpace.isPiSystem_measurableSet _ (F.comap Prod.snd))
    (@isPiSystem_prod Ω₁ Ω₂ n₁ n₂)
    (@MeasurableSpace.generateFrom_measurableSet _ (F.comap Prod.snd)).symm
    (@generateFrom_prod Ω₁ Ω₂ n₁ n₂).symm ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨E, hE, rfl⟩ ⟨B, hB, C, hC, rfl⟩
  have e1 : Prod.snd ⁻¹' E ∩ B ×ˢ C = B ×ˢ (E ∩ C) := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  have e2 : (Prod.snd ⁻¹' E : Set (Ω₁ × Ω₂)) = (Set.univ : Set Ω₁) ×ˢ E := by
    ext ⟨x, y⟩
    simp
  rw [e1, e2, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    (Indep_iff _ _ _).1 h E C hE hC, measure_univ]
  ring

end Indep

/-! ### The martingale property of the Walsh integral -/

section Walsh

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- The mass of a rectangle `(s,t] × (a,b]` is `𝒢_u`-measurable for `s, t ≤ u`. -/
theorem prodNoise_meas_rect (hS : IsWhiteNoise 𝓖 S ν) {s t u : ℝ≥0} (hs : s ≤ u)
    (ht : t ≤ u) (a b : ℝ) : Measurable[𝓖 u] (rectMass S s t a b) := by
  have h1 : ∀ x, Measurable[𝓖 u] (S t x) := fun x => (hS.adapted t x).mono (𝓖.mono ht) le_rfl
  have h0 : ∀ x, Measurable[𝓖 u] (S s x) := fun x => (hS.adapted s x).mono (𝓖.mono hs) le_rfl
  exact (((h1 b).sub (h1 a)).sub (h0 b)).add (h0 a)

/-- A `𝓖_u`-measurable variable is orthogonal to the mass of a rectangle `(u,v] × (a,b]`. -/
theorem prodNoise_integral_mul_rect (hS : IsWhiteNoise 𝓖 S ν) {u v : ℝ≥0} (huv : u ≤ v)
    {a b : ℝ} (hab : a ≤ b) {W : Ω → ℝ} (hW : Measurable[𝓖 u] W) :
    ∫ ω, W ω * rectMass S u v a b ω ∂ν = 0 := by
  have hind : IndepFun W (rectMass S u v a b) ν := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep_past u v huv)
      (le_iSup₂ (f := fun a b => MeasurableSpace.comap (rectMass S u v a b) inferInstance)
        a b)) hW.comap_le).symm
  have hm : Measurable (rectMass S u v a b) :=
    (prodNoise_meas_rect hS (le_max_left u v) (le_max_right u v) a b).mono (𝓖.le _) le_rfl
  rw [hind.integral_fun_mul_eq_mul_integral (hW.mono (𝓖.le u) le_rfl).aestronglyMeasurable
    hm.aestronglyMeasurable, (hS.gaussian u v a b huv hab).integral_eq, integral_id_gaussianReal,
    mul_zero]

/-- `W c ξ(R)` is integrable for `W c` bounded and measurable. -/
theorem prodNoise_integrable_bdd_rect (hS : IsWhiteNoise 𝓖 S ν) {u v : ℝ≥0} (huv : u ≤ v)
    {a b : ℝ} (hab : a ≤ b) {W : Ω → ℝ} (hW : Measurable W) (hWb : ∃ C, ∀ ω, |W ω| ≤ C) :
    Integrable (fun ω => W ω * rectMass S u v a b ω) ν := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  obtain ⟨C, hC⟩ := hWb
  exact ((hS.gaussian u v a b huv hab).hasGaussianLaw.memLp_two.integrable one_le_two).bdd_mul
    hW.aestronglyMeasurable (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)

/-- For `W` bounded, `𝔼[W Yₖ] → 𝔼[W Y]` when `Yₖ → Y` in `L²`. -/
theorem prodNoise_tendsto_integral_mul [IsProbabilityMeasure ν] {W : Ω → ℝ}
    (hWm : AEStronglyMeasurable W ν) {C : ℝ} (hC : ∀ ω, |W ω| ≤ C) {Y : ℕ → Ω → ℝ}
    {Z : Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 ν) (hZ : MemLp Z 2 ν)
    (hlim : Tendsto (fun k => eLpNorm (Y k - Z) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, W ω * Y k ω ∂ν) atTop (𝓝 (∫ ω, W ω * Z ω ∂ν)) := by
  have hb : ∀ᵐ ω ∂ν, ‖W ω‖ ≤ C := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω
  have hint : ∀ V : Ω → ℝ, MemLp V 2 ν → Integrable (fun ω => W ω * V ω) ν :=
    fun _ hV => (hV.integrable one_le_two).bdd_mul hWm hb
  refine tendsto_integral_of_L1' (μ := ν) (fun ω => W ω * Z ω)
    (Eventually.of_forall fun k => hint _ (hY k)) ?_
  have hbound : ∀ k, eLpNorm ((fun ω => W ω * Y k ω) - fun ω => W ω * Z ω) 1 ν ≤
      ENNReal.ofReal C * eLpNorm (Y k - Z) 2 ν := by
    intro k
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := Y k - Z) (c := C)
      ((hint _ (hY k)).sub (hint _ hZ)).aestronglyMeasurable ?_ 1).trans ?_
    · filter_upwards [hb] with ω hω
      simp only [Pi.sub_apply, ← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    · gcongr
      exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have h0 : Tendsto (fun k => ENNReal.ofReal C * eLpNorm (Y k - Z) 2 ν) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
    hbound

/-- **Martingale property of the Walsh integral**: if `X = ∫ h dξ`, then for every `s` the
integral `X' = ∫ 𝟙_{r ≤ s} h(r,y) ξ(dr dy)` exists, and `𝔼[W X] = 𝔼[W X']` for every bounded
`𝒢_s`-measurable `W`. In particular, if `h` vanishes for `r ≤ s`, then `𝔼[X | 𝒢_s] = 0`. -/
theorem prodNoise_walsh_restrict (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) (s : ℝ≥0) :
    ∃ X' : Ω → ℝ, IsWalshIntegral 𝓖 S ν (fun r y ω => if r ≤ s then h r y ω else 0) X' ∧
      ∀ W : Ω → ℝ, Measurable[𝓖 s] W → (∃ C, ∀ ω, |W ω| ≤ C) →
        ∫ ω, W ω * X ω ∂ν = ∫ ω, W ω * X' ω ∂ν := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hmem : ∀ {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}, IsWalshIntegral 𝓖 S ν h X → MemLp X 2 ν :=
    fun hX => (IsWalshIntegral.isometry_lib hS hX).2.1
  have hWint : ∀ {W V : Ω → ℝ}, Measurable[𝓖 s] W → (∃ C, ∀ ω, |W ω| ≤ C) → MemLp V 2 ν →
      Integrable (fun ω => W ω * V ω) ν := by
    intro W V hW hWb hV
    obtain ⟨C, hC⟩ := hWb
    exact (hV.integrable one_le_two).bdd_mul (hW.mono (𝓖.le s) le_rfl).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)
  induction hX with
  | block s₀ t₀ a b c hst hab hc hbdd =>
    -- `𝔼[W c ξ((u,v] × (a,b])] = 0` for `W` bounded `𝒢_u`-measurable, `s₀ ≤ u ≤ v`
    have key : ∀ u v : ℝ≥0, u ≤ v → s₀ ≤ u → ∀ W : Ω → ℝ, Measurable[𝓖 u] W →
        ∫ ω, W ω * (c ω * rectMass S u v a b ω) ∂ν = 0 := by
      intro u v huv hsu W hW
      have := prodNoise_integral_mul_rect hS huv hab (W := fun ω => W ω * c ω)
        (hW.mul (hc.mono (𝓖.mono hsu) le_rfl))
      simpa only [mul_assoc] using this
    rcases le_total s s₀ with hs | hs
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · convert IsWalshIntegral.zero 𝓖 S ν using 1
        funext r y ω
        have hs' : (s : ℝ) ≤ s₀ := by exact_mod_cast hs
        rw [ite_eq_right_iff]
        intro h1
        rw [ite_eq_right_iff]
        intro h2
        exfalso
        linarith [h2.1]
      · intro W hW _
        simp only [mul_zero, integral_zero]
        exact key s₀ t₀ hst le_rfl W (hW.mono (𝓖.mono hs) le_rfl)
    · refine ⟨fun ω => c ω * rectMass S s₀ ((min s t₀ : ℝ≥0) : ℝ) a b ω, ?_, ?_⟩
      · convert IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s₀ (min s t₀) a b c
          (le_min hs hst) hab hc hbdd using 1
        funext r y ω
        simp only [NNReal.coe_min, le_min_iff]
        split_ifs <;> first | rfl | (exfalso; tauto)
      · intro W hW hWb
        rcases le_total s t₀ with hst' | hts
        · have e : ∀ ω, W ω * (c ω * rectMass S s₀ t₀ a b ω) =
              W ω * (c ω * rectMass S s₀ ((min s t₀ : ℝ≥0) : ℝ) a b ω) +
                W ω * (c ω * rectMass S s t₀ a b ω) := by
            intro ω
            simp only [min_eq_left hst', rectMass]
            ring
          obtain ⟨C, hC⟩ := hWb
          obtain ⟨C', hC'⟩ := hbdd
          have hWc : ∀ u v : ℝ≥0, u ≤ v → Integrable
              (fun ω => W ω * (c ω * rectMass S u v a b ω)) ν := by
            intro u v huv
            have := prodNoise_integrable_bdd_rect hS huv hab (W := fun ω => W ω * c ω)
              ((hW.mono (𝓖.le s) le_rfl).mul (hc.mono (𝓖.le s₀) le_rfl))
              ⟨C * C', fun ω => by
                rw [abs_mul]
                exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _)
                  ((abs_nonneg _).trans (hC ω))⟩
            simpa only [mul_assoc] using this
          simp_rw [e]
          rw [integral_add (hWc _ _ (le_min hs hst)) (hWc _ _ hst'),
            key s t₀ hst' hs W hW, add_zero]
        · simp only [min_eq_right hts]
  | add h h' X X' hX hX' ih ih' =>
    obtain ⟨X₁, hX₁, e₁⟩ := ih
    obtain ⟨X₂, hX₂, e₂⟩ := ih'
    refine ⟨fun ω => X₁ ω + X₂ ω, ?_, ?_⟩
    · convert IsWalshIntegral.add _ _ _ _ hX₁ hX₂ using 1
      funext r y ω
      split_ifs <;> simp
    · intro W hW hWb
      simp only [mul_add]
      rw [integral_add (hWint hW hWb (hmem hX)) (hWint hW hWb (hmem hX')),
        integral_add (hWint hW hWb (hmem hX₁)) (hWint hW hWb (hmem hX₂)), e₁ W hW hWb,
        e₂ W hW hWb]
  | limit h X hs Xs hk h2 X2 hlim Xlim ih =>
    choose X' hX' e using ih
    have hr : ∀ g : ℝ → ℝ → Ω → ℝ, uncurryField (fun r y ω => if r ≤ s then g r y ω else 0) =
        {p : Ω × ℝ × ℝ | p.2.1 ≤ s}.indicator (uncurryField g) := by
      intro g
      funext p
      simp only [uncurryField, Set.indicator, Set.mem_ofPred_eq]
    have hmeas : MeasurableSet {p : Ω × ℝ × ℝ | p.2.1 ≤ s} :=
      measurableSet_le (measurable_fst.comp measurable_snd) measurable_const
    have hr2 : MemLp (uncurryField (fun r y ω => if r ≤ s then h r y ω else 0)) 2
        (ν.prod volume) := by
      rw [hr]
      exact h2.indicator hmeas.nullMeasurableSet
    have hlim' : Tendsto (fun k => eLpNorm
        (uncurryField (fun r y ω => if r ≤ s then hs k r y ω else 0) -
          uncurryField (fun r y ω => if r ≤ s then h r y ω else 0)) 2 (ν.prod volume))
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => zero_le) fun k =>
          eLpNorm_mono ((IsWalshIntegral.isometry_lib hS (hX' k)).1.sub hr2).aestronglyMeasurable fun p => ?_
      simp only [hr, Pi.sub_apply, Set.indicator]
      split_ifs <;> simp
    obtain ⟨Y, hY, hYlim⟩ := IsWalshIntegral.exists_limit hS hX' hr2 hlim'
    refine ⟨Y, hY, fun W hW hWb => ?_⟩
    obtain ⟨C, hC⟩ := hWb
    have hWm : AEStronglyMeasurable W ν := (hW.mono (𝓖.le s) le_rfl).aestronglyMeasurable
    have t1 := prodNoise_tendsto_integral_mul hWm hC (fun k => hmem (hk k)) X2 Xlim
    have t2 := prodNoise_tendsto_integral_mul hWm hC (fun k => hmem (hX' k)) (hmem hY) hYlim
    have e' : (fun k => ∫ ω, W ω * Xs k ω ∂ν) = fun k => ∫ ω, W ω * X' k ω ∂ν :=
      funext fun k => e k W hW ⟨C, hC⟩
    rw [e'] at t1
    exact tendsto_nhds_unique t1 t2

end Walsh

end QSSEPtoKPZ
