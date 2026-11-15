/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.NoiseLaw
public import QSSEPtoKPZ.WhiteNoise.WalshBasic
public import QSSEPtoKPZ.Martingales.Defs
public import QSSEPtoKPZ.Martingales.NullAug
public import Mathlib.Probability.ConditionalExpectation

/-!
# The natural filtration of the noise (task G5)

Interface statements of task I0″ of Stage 4, proved by task G5. See `docs/stage4-design.md`,
Sections 1.2 (h) and 3.3, and `docs/stage4-interfaces.md`.

Method: independence of the future by π-systems (finite intersections of rectangle events),
each finite family being a function of the cells of a grid starting at time `s`
(`IsWhiteNoise.indep_noiseCells`); the conditional expectation lemma from
`⨆ t, 𝒩_t = 𝒩_s ∨ (future increments)` and `𝔼[c | 𝒜 ∨ ℬ] = 𝔼[c | 𝒜]` when `σ(c) ∨ 𝒜` is
independent of `ℬ` (Dynkin's π-λ theorem on the sets `A ∩ B`).

`noiseFiltration S ν`: `𝒩_t = σ(ξ((0,s] × (a,b]) : s ≤ t, a, b)`, augmented by the null sets.
* `𝒩_t ⊆ 𝓖_t ∨ (null sets)` for a white noise for `𝓖`;
* the increments after `s` are jointly independent of `𝓖_s`;
* `𝔼[c | 𝒩_∞] = 𝔼[c | 𝒩_s]` for `c` `𝓖_s`-measurable;
* `noiseSheet S` is a white noise for `𝒩` (the axis values of `S` need not be `𝒩`-measurable,
  so `S` itself need not be);
* augmenting the filtration by the null sets preserves white noises.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The natural filtration of the noise, augmented by the null sets:
`𝒩_t = σ(rectMass S 0 s a b : s ≤ t, a, b ∈ ℝ) ∨ σ(null sets)`. -/
def noiseFiltration (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) : Filtration ℝ≥0 mΩ :=
  nullAug ν
    { seq := fun t => (⨆ (s : ℝ≥0) (_ : s ≤ t) (a : ℝ) (b : ℝ),
          MeasurableSpace.comap (rectMass S 0 s a b) (borel ℝ)) ⊓ mΩ
      mono' := fun _ _ h => inf_le_inf_right _ (iSup_mono fun _ => iSup_mono' fun hs =>
        ⟨hs.trans h, le_rfl⟩)
      le' := fun _ => inf_le_right }

variable {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}

/-! ### Auxiliary results -/

/-- Adding the null sets to the second σ-algebra preserves independence. -/
private theorem noise_indep_sup_nullSets {m₁ m₂ : MeasurableSpace Ω} (hm₂ : m₂ ≤ mΩ)
    (h : Indep m₁ m₂ ν) : Indep m₁ (m₂ ⊔ nullSets ν) ν := by
  rw [Indep_iff] at h ⊢
  intro t1 t2 ht1 ht2
  obtain ⟨-, F, hF, h2F⟩ := (measurableSet_sup_nullSets_iff hm₂).1 ht2
  rw [measure_congr h2F, measure_congr ((EventuallyEqSet.refl _ t1).inter h2F), h t1 F ht1 hF]

/-- The noise coordinates `ξ((0,u] × (a,b])`, `u ≤ t`, are measurable for `𝒩_t`. -/
private theorem IsWhiteNoise.measurable_noiseFiltration (hS : IsWhiteNoise 𝓖 S ν) {u t : ℝ≥0}
    (hu : u ≤ t) (a b : ℝ) : Measurable[noiseFiltration S ν t] (rectMass S 0 u a b) := by
  intro B hB
  refine le_nullAug ν _ t _ (MeasurableSpace.measurableSet_inf.2 ⟨?_, ?_⟩)
  · exact le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : s ≤ t) => ⨆ (a : ℝ) (b : ℝ),
      MeasurableSpace.comap (rectMass S 0 s a b) (borel ℝ)) u hu
      (le_iSup₂ (f := fun (a b : ℝ) => MeasurableSpace.comap (rectMass S 0 u a b) (borel ℝ)) a b)
      _ ⟨B, hB, rfl⟩
  · exact ((hS.measurable_noiseCoord_le le_rfl a b).mono (𝓖.le u) le_rfl) hB

/-- A Walsh integral depends on `S` only through the rectangle masses. -/
private theorem noise_isWalshIntegral_congr {S' : ℝ → ℝ → Ω → ℝ}
    (hSS' : ∀ s t a b ω, rectMass S s t a b ω = rectMass S' s t a b ω)
    {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    IsWalshIntegral 𝓖 S' ν h X := by
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    have e : (fun ω => c ω * rectMass S s t a b ω) = fun ω => c ω * rectMass S' s t a b ω := by
      funext ω; rw [hSS']
    rw [e]
    exact IsWalshIntegral.block s t a b c hst hab hc hbdd
  | add h h' X X' _ _ ih ih' => exact IsWalshIntegral.add _ _ _ _ ih ih'
  | limit h X hs Xs _ hh hX hlim hlimX ih => exact IsWalshIntegral.limit _ _ _ _ ih hh hX hlim hlimX

/-- For `f` measurable for `𝒞`, `A ∈ 𝒞`, `B ∈ ℬ`, with `𝒞` and `ℬ` independent:
`∫_{A ∩ B} f = ν(B) ∫_A f`. -/
private theorem noise_setIntegral_inter_of_indep [IsProbabilityMeasure ν]
    {𝒞 ℬ : MeasurableSpace Ω} (h𝒞 : 𝒞 ≤ mΩ) (hℬ : ℬ ≤ mΩ) (hind : Indep 𝒞 ℬ ν) {f : Ω → ℝ}
    (hf : StronglyMeasurable[𝒞] f) (hfi : Integrable f ν) {A B : Set Ω}
    (hA : MeasurableSet[𝒞] A) (hB : MeasurableSet[ℬ] B) :
    ∫ x in A ∩ B, f x ∂ν = ν.real B * ∫ x in A, f x ∂ν := by
  have hfA : StronglyMeasurable[𝒞] (A.indicator f) := hf.indicator hA
  have hfAi : Integrable (A.indicator f) ν := hfi.indicator (h𝒞 _ hA)
  have hce := condExp_indep_eq h𝒞 hℬ hfA hind
  rw [Set.inter_comm, ← setIntegral_indicator (h𝒞 _ hA), ← setIntegral_condExp hℬ hfAi hB,
    setIntegral_congr_ae (hℬ _ hB) (hce.mono fun x hx _ => hx), setIntegral_const,
    integral_indicator (h𝒞 _ hA), smul_eq_mul]

/-- **Conditioning and independence**: if `𝒜 ⊆ 𝒞`, `c` is `𝒞`-measurable and `𝒞` is independent
of `ℬ`, then `𝔼[c | 𝒜 ∨ ℬ] = 𝔼[c | 𝒜]`. -/
private theorem noise_condExp_sup_eq [IsProbabilityMeasure ν] {𝒜 ℬ 𝒞 : MeasurableSpace Ω}
    (h𝒜𝒞 : 𝒜 ≤ 𝒞) (h𝒞 : 𝒞 ≤ mΩ) (hℬ : ℬ ≤ mΩ) (hind : Indep 𝒞 ℬ ν) {c : Ω → ℝ}
    (hc : StronglyMeasurable[𝒞] c) (hci : Integrable c ν) :
    ν[c | 𝒜 ⊔ ℬ] =ᵐ[ν] ν[c | 𝒜] := by
  have h𝒜 : 𝒜 ≤ mΩ := h𝒜𝒞.trans h𝒞
  have h𝒜ℬ : 𝒜 ⊔ ℬ ≤ mΩ := sup_le h𝒜 hℬ
  set g := ν[c | 𝒜]
  have hgi : Integrable g ν := integrable_condExp
  have hgm : StronglyMeasurable[𝒞] g := stronglyMeasurable_condExp.mono h𝒜𝒞
  let p : Set (Set Ω) :=
    {E | ∃ A B, MeasurableSet[𝒜] A ∧ MeasurableSet[ℬ] B ∧ E = A ∩ B}
  have hp : IsPiSystem p := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ _
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by ext; simp only [Set.mem_inter_iff]; tauto⟩
  have hgen : 𝒜 ⊔ ℬ = MeasurableSpace.generateFrom p := by
    apply le_antisymm
    · refine sup_le (fun A hA => MeasurableSpace.measurableSet_generateFrom
        ⟨A, Set.univ, hA, MeasurableSet.univ, by simp⟩) (fun B hB =>
        MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, B, MeasurableSet.univ, hB, by simp⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨A, B, hA, hB, rfl⟩
      exact (le_sup_left (a := 𝒜) (b := ℬ) _ hA).inter (le_sup_right (a := 𝒜) (b := ℬ) _ hB)
  have key : ∀ E, MeasurableSet[𝒜 ⊔ ℬ] E → ∫ x in E, g x ∂ν = ∫ x in E, c x ∂ν := by
    intro E hE
    induction E, hE using MeasurableSpace.induction_on_inter hgen hp with
    | empty => simp
    | basic E hE =>
      obtain ⟨A, B, hA, hB, rfl⟩ := hE
      rw [noise_setIntegral_inter_of_indep h𝒞 hℬ hind hgm hgi (h𝒜𝒞 _ hA) hB,
        noise_setIntegral_inter_of_indep h𝒞 hℬ hind hc hci (h𝒜𝒞 _ hA) hB,
        setIntegral_condExp h𝒜 hci hA]
    | compl E hE ih =>
      rw [setIntegral_compl (h𝒜ℬ _ hE) hgi, setIntegral_compl (h𝒜ℬ _ hE) hci, ih,
        integral_condExp h𝒜]
    | iUnion f hdisj hf ih =>
      rw [integral_iUnion (fun n => h𝒜ℬ _ (hf n)) hdisj hgi.integrableOn,
        integral_iUnion (fun n => h𝒜ℬ _ (hf n)) hdisj hci.integrableOn]
      exact tsum_congr ih
  have hgm' : StronglyMeasurable[𝒜 ⊔ ℬ] g := stronglyMeasurable_condExp.mono le_sup_left
  exact (ae_eq_condExp_of_forall_setIntegral_eq h𝒜ℬ hci (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => key s hs) hgm'.aestronglyMeasurable).symm

/-! ### The noise filtration -/

/-- The noise filtration is contained in the augmented filtration of the white noise. -/
theorem IsWhiteNoise.noiseFiltration_le (hS : IsWhiteNoise 𝓖 S ν) (t : ℝ≥0) :
    noiseFiltration S ν t ≤ nullAug ν 𝓖 t := by
  refine sup_le_sup_right (inf_le_left.trans (iSup₂_le fun u hu => iSup₂_le fun a b => ?_)) _
  exact (hS.measurable_noiseCoord_le hu a b).comap_le

/-- Augmenting the filtration by the null sets preserves white noises. -/
theorem IsWhiteNoise.nullAug (hS : IsWhiteNoise 𝓖 S ν) : IsWhiteNoise (nullAug ν 𝓖) S ν :=
  ⟨fun t x => (hS.adapted t x).mono (le_nullAug ν 𝓖 t) le_rfl, hS.gaussian, hS.indep,
    fun s t hst => noise_indep_sup_nullSets (𝓖.le s) (hS.indep_past s t hst)⟩

/-- `noiseSheet S` is a white noise for the noise filtration. -/
theorem IsWhiteNoise.noiseSheet (hS : IsWhiteNoise 𝓖 S ν) :
    IsWhiteNoise (noiseFiltration S ν) (noiseSheet S) ν := by
  have e : ∀ s t a b, rectMass (QSSEPtoKPZ.noiseSheet S) s t a b = rectMass S s t a b :=
    fun s t a b => funext (rectMass_noiseSheet S s t a b)
  refine ⟨fun t x => hS.measurable_noiseFiltration le_rfl 0 x, fun s t a b hst hab => ?_,
    fun s t hst k a ha => ?_, fun s t hst => ?_⟩
  · rw [e]; exact hS.gaussian s t a b hst hab
  · simp only [e]; exact hS.indep s t hst k a ha
  · simp only [e]
    exact indep_of_indep_of_le_right (hS.nullAug.indep_past s t hst) (hS.noiseFiltration_le s)

/-- A Walsh integral against `S` is a Walsh integral against `noiseSheet S`, and conversely. -/
theorem isWalshIntegral_noiseSheet_iff {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} :
    IsWalshIntegral 𝓖 (noiseSheet S) ν h X ↔ IsWalshIntegral 𝓖 S ν h X :=
  ⟨noise_isWalshIntegral_congr fun s t a b ω => rectMass_noiseSheet S s t a b ω,
    noise_isWalshIntegral_congr fun s t a b ω => (rectMass_noiseSheet S s t a b ω).symm⟩

/-- **The future of the noise is independent of the past**: the masses of all rectangles in
`(s, ∞) × ℝ` are jointly independent of `𝓖_s`. -/
theorem IsWhiteNoise.indep_future (hS : IsWhiteNoise 𝓖 S ν) (s : ℝ≥0) :
    Indep (⨆ (u : ℝ≥0) (v : ℝ≥0) (_ : s ≤ u) (_ : u ≤ v) (a : ℝ) (b : ℝ),
      MeasurableSpace.comap (rectMass S u v a b) (borel ℝ)) (𝓖 s) ν := by
  classical
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  let ι := {q : ℝ≥0 × ℝ≥0 × ℝ × ℝ // s ≤ q.1 ∧ s ≤ q.2.1}
  let g : ι → Ω → ℝ := fun i => rectMass S i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2
  have hle : (⨆ (u : ℝ≥0) (v : ℝ≥0) (_ : s ≤ u) (_ : u ≤ v) (a : ℝ) (b : ℝ),
      MeasurableSpace.comap (rectMass S u v a b) (borel ℝ)) ≤
      ⨆ i : ι, MeasurableSpace.comap (g i) (borel ℝ) := by
    refine iSup_le fun u => iSup_le fun v => iSup_le fun hsu => iSup_le fun huv =>
      iSup_le fun a => iSup_le fun b => ?_
    exact le_iSup (fun i : ι => MeasurableSpace.comap (g i) (borel ℝ))
      ⟨(u, v, a, b), hsu, hsu.trans huv⟩
  refine indep_of_indep_of_le_left ?_ hle
  refine IndepSets.indep (iSup_le fun i => (hS.measurable_rectMass_noise _ _ _ _).comap_le) (𝓖.le s)
    (isPiSystem_piiUnionInter _ (fun i => @MeasurableSpace.isPiSystem_measurableSet Ω
      (MeasurableSpace.comap (g i) (borel ℝ))) Set.univ)
    (@MeasurableSpace.isPiSystem_measurableSet Ω (𝓖 s)) ?_
    (@MeasurableSpace.generateFrom_measurableSet Ω (𝓖 s)).symm ?_
  · rw [generateFrom_piiUnionInter_measurableSet (fun i => MeasurableSpace.comap (g i) (borel ℝ))]
    simp
  rw [IndepSets_iff]
  rintro _ G ⟨J, -, f, hf, rfl⟩ hG
  have hB : ∀ i, ∃ B : Set ℝ, MeasurableSet B ∧ (i ∈ J → g i ⁻¹' B = f i) := by
    intro i
    by_cases hi : i ∈ J
    · obtain ⟨B, hB, e⟩ := hf i hi
      exact ⟨B, hB, fun _ => e⟩
    · exact ⟨Set.univ, MeasurableSet.univ, fun h => absurd h hi⟩
  choose B hBm hBf using hB
  -- a grid containing all the corners, starting at time `s`
  set ts : Finset ℝ≥0 := insert s (J.image (fun i => i.1.1) ∪ J.image fun i => i.1.2.1)
  set xs : Finset ℝ := insert 0 (J.image (fun i => i.1.2.2.1) ∪ J.image fun i => i.1.2.2.2)
  obtain ⟨T, hT, hT0, hTs⟩ := noiseEnum_exists ts (Finset.insert_nonempty _ _)
  obtain ⟨X, hX, -, hXs⟩ := noiseEnum_exists xs (Finset.insert_nonempty _ _)
  have hT0' : T 0 = s := by
    rw [hT0]
    refine le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
      (Finset.le_min' _ _ _ fun y hy => ?_)
    simp only [ts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hy
    rcases hy with rfl | ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
    · exact le_rfl
    · exact i.2.1
    · exact i.2.2
  have hidx : ∀ i : ι, ∃ j₁ ≤ ts.card, ∃ j₂ ≤ ts.card, ∃ k ≤ xs.card, ∃ l ≤ xs.card,
      i ∈ J → T j₁ = i.1.1 ∧ T j₂ = i.1.2.1 ∧ X k = i.1.2.2.1 ∧ X l = i.1.2.2.2 := by
    intro i
    by_cases hi : i ∈ J
    · obtain ⟨j₁, hj₁, e₁⟩ := hTs i.1.1
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)))
      obtain ⟨j₂, hj₂, e₂⟩ := hTs i.1.2.1
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)))
      obtain ⟨k, hk, e₃⟩ := hXs i.1.2.2.1
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)))
      obtain ⟨l, hl, e₄⟩ := hXs i.1.2.2.2
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)))
      exact ⟨j₁, hj₁.le, j₂, hj₂.le, k, hk.le, l, hl.le, fun _ => ⟨e₁, e₂, e₃, e₄⟩⟩
    · exact ⟨0, Nat.zero_le _, 0, Nat.zero_le _, 0, Nat.zero_le _, 0, Nat.zero_le _,
        fun h => absurd h hi⟩
  choose j₁ hj₁ j₂ hj₂ k hk l hl he using hidx
  set A : Set (Fin ts.card × Fin xs.card → ℝ) :=
    ⋂ i ∈ J, (fun c => noiseGridRect c (j₁ i) (j₂ i) (k i) (l i)) ⁻¹' B i
  have hAm : MeasurableSet A := Finset.measurableSet_biInter _ fun i _ =>
    measurable_noiseGridRect _ _ _ _ _ _ (hBm i)
  have hset : ⋂ i ∈ J, f i = noiseCells S T X ts.card xs.card ⁻¹' A := by
    ext ω
    simp only [A, Set.mem_iInter, Set.mem_preimage]
    refine forall₂_congr fun i hi => ?_
    rw [← hBf i hi, Set.mem_preimage]
    obtain ⟨e₁, e₂, e₃, e₄⟩ := he i hi
    have := rectMass_eq_noiseGridRect S T X (hj₁ i) (hj₂ i) (hk i) (hl i) ω
    rw [e₁, e₂, e₃, e₄] at this
    simp only [g, this]
  rw [hset]
  have hind := hS.indep_noiseCells hT hX ts.card xs.card
  rw [hT0'] at hind
  exact (Indep_iff _ _ _).1 hind _ G ⟨A, hAm, rfl⟩ hG

/-- **Conditioning on the whole noise**: for `c` integrable and `𝓖_s`-measurable,
`𝔼[c | 𝒩_∞] = 𝔼[c | 𝒩_s]` almost surely. -/
theorem IsWhiteNoise.condExp_noise_eq (hS : IsWhiteNoise 𝓖 S ν) {s : ℝ≥0} {c : Ω → ℝ}
    (hc : Measurable[𝓖 s] c) (hci : Integrable c ν) :
    ν[c | ⨆ t, noiseFiltration S ν t] =ᵐ[ν] ν[c | noiseFiltration S ν s] := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  set ℬ := ⨆ (u : ℝ≥0) (v : ℝ≥0) (_ : s ≤ u) (_ : u ≤ v) (a : ℝ) (b : ℝ),
      MeasurableSpace.comap (rectMass S u v a b) (borel ℝ) with hℬdef
  have hℬmeas : ∀ {u v : ℝ≥0}, s ≤ u → u ≤ v → ∀ a b, Measurable[ℬ] (rectMass S u v a b) := by
    intro u v hsu huv a b
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le hsu (le_iSup_of_le huv
      (le_iSup_of_le a (le_iSup_of_le b le_rfl)))))
  have hℬle : ℬ ≤ mΩ := iSup_le fun u => iSup_le fun v => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun a => iSup_le fun b => (hS.measurable_rectMass_noise u v a b).comap_le
  have hsup : ⨆ t, noiseFiltration S ν t = noiseFiltration S ν s ⊔ ℬ := by
    refine le_antisymm (iSup_le fun t => ?_) (sup_le (le_iSup (noiseFiltration S ν) s) ?_)
    · refine sup_le (inf_le_left.trans (iSup₂_le fun u _ => iSup₂_le fun a b => ?_)) ?_
      · refine Measurable.comap_le ?_
        by_cases hus : u ≤ s
        · exact (hS.measurable_noiseFiltration hus a b).mono le_sup_left le_rfl
        · have e : rectMass S 0 u a b = fun ω => rectMass S 0 s a b ω + rectMass S s u a b ω := by
            funext ω; simp only [rectMass]; ring
          rw [e]
          exact ((hS.measurable_noiseFiltration le_rfl a b).mono le_sup_left le_rfl).add
            ((hℬmeas le_rfl (le_of_not_ge hus) a b).mono le_sup_right le_rfl)
      · exact (nullSets_le_nullAug s).trans le_sup_left
    · refine iSup_le fun u => iSup_le fun v => iSup_le fun _ => iSup_le fun huv =>
        iSup_le fun a => iSup_le fun b => Measurable.comap_le ?_
      have e : rectMass S u v a b = fun ω => rectMass S 0 v a b ω - rectMass S 0 u a b ω := by
        funext ω; simp only [rectMass]; ring
      rw [e]
      exact ((hS.measurable_noiseFiltration le_rfl a b).mono (le_iSup _ v) le_rfl).sub
        ((hS.measurable_noiseFiltration huv a b).mono (le_iSup _ v) le_rfl)
  rw [hsup]
  have hind : Indep (QSSEPtoKPZ.nullAug ν 𝓖 s) ℬ ν :=
    (noise_indep_sup_nullSets (𝓖.le s) (hS.indep_future s)).symm
  exact noise_condExp_sup_eq (hS.noiseFiltration_le s) ((QSSEPtoKPZ.nullAug ν 𝓖).le s) hℬle hind
    (hc.mono (le_nullAug ν 𝓖 s) le_rfl).stronglyMeasurable hci

end QSSEPtoKPZ
