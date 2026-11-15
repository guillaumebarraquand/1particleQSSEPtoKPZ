/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Defs

/-!
# The null augmentation of a filtration; versions; transfer lemmas (package B, task B1)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces, proved by
task B1. See `docs/stage2-design.md`, Section 1.2 (a), (b) and Section 2.1, and
`docs/stage2-interfaces.md`.

* Sets and conditional expectations of `𝓕ᵃ_t = 𝓕_t ∨ σ(null sets)`: `measurableSet_nullAug_iff`,
  `condExp_nullAug`, `aestronglyMeasurable_of_nullAug`, `stronglyMeasurable_nullAug_of_ae`.
* A Brownian family and a wave function for `𝓕` are also one for `𝓕ᵃ`.
* Versions with all paths continuous: `exists_continuous_version`, `IsWaveFunction.exists_good`,
  `IsCL2Mart.exists_version`.
* Transfer of `IsCL2Mart` and `HasBracket`: filtration `𝓕 ↔ 𝓕ᵃ`, indistinguishability,
  restriction of the horizon, time change, multiplication by a constant, sums; and the link with
  Mathlib's `Martingale`.

The description of the sets of `𝓕ᵃ_t` is first proved for `m ⊔ σ(null sets)`, `m` any
sub-σ-algebra (`measurableSet_sup_nullSets_iff`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Sets and functions of the augmented filtration -/

/-- A measurable `μ`-null set is measurable for `nullSets μ`. -/
lemma measurableSet_nullSets {s : Set Ω} (hs : MeasurableSet s) (h0 : μ s = 0) :
    MeasurableSet[nullSets μ] s :=
  MeasurableSpace.measurableSet_generateFrom ⟨hs, h0⟩

/-- The null sets are in every `𝓕ᵃ_t`. -/
lemma nullSets_le_nullAug (t : ℝ≥0) : nullSets μ ≤ nullAug μ 𝓕 t :=
  le_sup_right

/-- Sets of `m ∨ σ(null sets)`, for a sub-σ-algebra `m`: they are the measurable sets which are
almost everywhere equal to a set of `m`. -/
theorem measurableSet_sup_nullSets_iff {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {G : Set Ω} :
    MeasurableSet[m ⊔ nullSets μ] G ↔
      MeasurableSet[mΩ] G ∧ ∃ F, MeasurableSet[m] F ∧ G =ᵐ[μ] F := by
  constructor
  · intro hG
    let S : MeasurableSpace Ω :=
      { MeasurableSet' := fun G => MeasurableSet[mΩ] G ∧ ∃ F, MeasurableSet[m] F ∧ G =ᵐ[μ] F
        measurableSet_empty := ⟨@MeasurableSet.empty _ mΩ, ∅, @MeasurableSet.empty _ m, by rfl⟩
        measurableSet_compl := fun G ⟨hG, F, hF, h⟩ =>
          ⟨hG.compl, Fᶜ, hF.compl, EventuallyEqSet.compl h⟩
        measurableSet_iUnion := fun G hG => by
          choose hGm F hF h using hG
          exact ⟨MeasurableSet.iUnion hGm, ⋃ i, F i, MeasurableSet.iUnion hF,
            EventuallyEqSet.countable_iUnion h⟩ }
    have hle : m ⊔ nullSets μ ≤ S := sup_le (fun s hs => ⟨hm s hs, s, hs, by rfl⟩)
      (MeasurableSpace.generateFrom_le fun s hs =>
        ⟨hs.1, ∅, @MeasurableSet.empty _ m, ae_eq_empty.2 hs.2⟩)
    exact hle G hG
  · rintro ⟨hG, F, hF, h⟩
    have h1 : μ (F \ G) = 0 := (ae_eq_set.1 h).2
    have h2 : μ (G \ F) = 0 := (ae_eq_set.1 h).1
    have hFm : MeasurableSet[mΩ] F := hm F hF
    have hGeq : G = (F \ (F \ G)) ∪ (G \ F) := by
      ext ω; by_cases a : ω ∈ G <;> by_cases b : ω ∈ F <;> simp [a, b]
    rw [hGeq]
    refine MeasurableSet.union (MeasurableSet.diff ?_ ?_) ?_
    · exact (le_sup_left : m ≤ m ⊔ nullSets μ) F hF
    · exact (le_sup_right : nullSets μ ≤ m ⊔ nullSets μ) _
        (measurableSet_nullSets (hFm.diff hG) h1)
    · exact (le_sup_right : nullSets μ ≤ m ⊔ nullSets μ) _
        (measurableSet_nullSets (hG.diff hFm) h2)

/-- **Sets of the augmented filtration.** A set belongs to `𝓕ᵃ_t` if and only if it is
measurable and almost everywhere equal to a set of `𝓕_t`. -/
theorem measurableSet_nullAug_iff {t : ℝ≥0} {G : Set Ω} :
    MeasurableSet[nullAug μ 𝓕 t] G ↔
      MeasurableSet G ∧ ∃ F, MeasurableSet[𝓕 t] F ∧ G =ᵐ[μ] F :=
  measurableSet_sup_nullSets_iff (𝓕.le t)

/-- Adding the null sets to a sub-σ-algebra `m` does not change conditional expectations:
`𝔼[X | m ∨ σ(null sets)] = 𝔼[X | m]` almost surely (finite measure). -/
theorem condExp_sup_nullSets [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (X : Ω → ℝ) : μ[X | m ⊔ nullSets μ] =ᵐ[μ] μ[X | m] := by
  by_cases hX : Integrable X μ
  swap; · simp [condExp_of_not_integrable hX]
  have hm' : m ⊔ nullSets μ ≤ mΩ := sup_le hm (nullSets_le μ)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm' hX
    (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_).symm
  · intro s hs _
    obtain ⟨-, F, hF, hsF⟩ := (measurableSet_sup_nullSets_iff hm).1 hs
    rw [setIntegral_congr_set hsF, setIntegral_congr_set hsF, setIntegral_condExp hm hX hF]
  · exact (stronglyMeasurable_condExp.mono le_sup_left).aestronglyMeasurable

/-- `𝔼[X | 𝓕ᵃ_t] = 𝔼[X | 𝓕_t]` almost surely (finite measure). -/
theorem condExp_nullAug [IsFiniteMeasure μ] (X : Ω → ℝ) (t : ℝ≥0) :
    μ[X | nullAug μ 𝓕 t] =ᵐ[μ] μ[X | 𝓕 t] :=
  condExp_sup_nullSets (𝓕.le t) X

/-- A real function measurable for `𝓕ᵃ_t` is almost everywhere equal to an
`𝓕_t`-measurable function. -/
theorem aestronglyMeasurable_of_nullAug {t : ℝ≥0} {X : Ω → ℝ}
    (hX : StronglyMeasurable[nullAug μ 𝓕 t] X) : AEStronglyMeasurable[𝓕 t] X μ := by
  classical
  -- simple functions of `𝓕ᵃ_t` are a.e. equal to `𝓕_t`-measurable functions
  have hsimple : ∀ f : @SimpleFunc Ω (nullAug μ 𝓕 t) ℝ, AEStronglyMeasurable[𝓕 t] (⇑f) μ := by
    intro f
    refine @SimpleFunc.induction Ω ℝ (nullAug μ 𝓕 t) _
      (fun f => AEStronglyMeasurable[𝓕 t] (⇑f) μ) ?_ ?_ f
    · intro c s hs
      obtain ⟨-, F, hF, hsF⟩ := measurableSet_nullAug_iff.1 hs
      refine ⟨F.indicator fun _ => c, stronglyMeasurable_const.indicator hF, ?_⟩
      have e : s.piecewise (fun _ => c) (fun _ => (0 : ℝ)) = s.indicator fun _ => c := by
        ext ω; by_cases h : ω ∈ s <;> simp [h]
      change s.piecewise (fun _ => c) (fun _ => (0 : ℝ)) =ᵐ[μ] _
      rw [e]
      exact indicator_ae_eq_of_ae_eq_set hsF
    · intro f g _ hf hg
      exact hf.add hg
  -- pass to the limit along the approximating simple functions
  obtain ⟨fs, hfs⟩ := hX
  choose g hg hfg using fun n => hsimple (fs n)
  have hall : ∀ᵐ ω ∂μ, ∀ n, fs n ω = g n ω := ae_all_iff.2 hfg
  refine ⟨fun ω => limUnder atTop (fun n => g n ω),
    @StronglyMeasurable.limUnder ℕ Ω ℝ (𝓕 t) _ _ atTop _ g _ _ hg, ?_⟩
  filter_upwards [hall] with ω hω
  exact ((hfs ω).congr hω).limUnder_eq.symm

/-- Conversely, a measurable real function which is almost everywhere equal to an
`𝓕_t`-measurable function is measurable for `𝓕ᵃ_t`. -/
theorem stronglyMeasurable_nullAug_of_ae {t : ℝ≥0} {X : Ω → ℝ} (hX : StronglyMeasurable X)
    (hae : AEStronglyMeasurable[𝓕 t] X μ) : StronglyMeasurable[nullAug μ 𝓕 t] X := by
  obtain ⟨Y, hY, hXY⟩ := hae
  have hmeas : Measurable[nullAug μ 𝓕 t] X := fun B hB =>
    measurableSet_nullAug_iff.2
      ⟨hX.measurable hB, Y ⁻¹' B, hY.measurable hB, hXY.preimage B⟩
  exact hmeas.stronglyMeasurable

/-! ### Brownian family and wave function for the augmented filtration -/

/-- A Brownian family for `𝓕` is a Brownian family for the augmented filtration `𝓕ᵃ`
(the independence of the increments from the past survives the addition of null sets). -/
theorem IsBrownianFamily.nullAug {ι : Type*} {B : ι → ℝ → Ω → ℝ}
    (hB : IsBrownianFamily 𝓕 B μ) : IsBrownianFamily (nullAug μ 𝓕) B μ := by
  refine ⟨fun i t => (hB.adapted i t).mono (le_nullAug μ 𝓕 t) le_rfl, hB.continuous, hB.zero,
    hB.gaussian, hB.indep, fun s t hst => ?_⟩
  have h := hB.indep_past s t hst
  rw [Indep_iff] at h ⊢
  intro t1 t2 ht1 ht2
  obtain ⟨-, F, hF, h2F⟩ := measurableSet_nullAug_iff.1 ht2
  rw [measure_congr h2F, measure_congr ((EventuallyEqSet.refl _ t1).inter h2F), h t1 F ht1 hF]

/-- A wave function for `𝓕` is a wave function for the augmented filtration `𝓕ᵃ`. -/
theorem IsWaveFunction.nullAug {L : ℕ∞} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    IsWaveFunction L (nullAug μ 𝓕) B ψ μ :=
  ⟨fun t x => (hψ.adapted t x).mono (le_nullAug μ 𝓕 t) le_rfl, hψ.continuous, hψ.support,
    hψ.sde⟩

/-! ### Versions with all paths continuous -/

/-- **Continuous version.** If the filtration `𝓖` contains the null sets, a process adapted to
`𝓖` with almost surely continuous paths on `[0, ∞)` has a version, indistinguishable from it,
which is adapted to `𝓖` and has *all* its paths continuous on `[0, ∞)` (change it to a constant
on a measurable null set containing the bad paths). -/
theorem exists_continuous_version {E : Type*} [TopologicalSpace E] [Nonempty E]
    {𝓖 : Filtration ℝ≥0 mΩ} (h0 : nullSets μ ≤ 𝓖 0) {X : ℝ → Ω → E}
    (hX : ∀ t : ℝ≥0, StronglyMeasurable[𝓖 t] (X t))
    (hc : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => X t ω) :
    ∃ X' : ℝ → Ω → E, (∀ t : ℝ≥0, StronglyMeasurable[𝓖 t] (X' t)) ∧
      (∀ ω, Continuous fun t : ℝ≥0 => X' t ω) ∧ ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, X' t ω = X t ω := by
  classical
  set N := toMeasurable μ {ω | ¬ Continuous fun t : ℝ≥0 => X t ω} with hNdef
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hc
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNG : ∀ t, MeasurableSet[𝓖 t] N := fun t =>
    𝓖.mono (by simp) _ (h0 _ (measurableSet_nullSets hNm hN0))
  let c : E := Classical.arbitrary E
  refine ⟨fun t ω => if ω ∈ N then c else X t ω, fun t => ?_, fun ω => ?_, ?_⟩
  · exact StronglyMeasurable.ite (hNG t) stronglyMeasurable_const (hX t)
  · by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact continuous_const
    · simp only [hω, ite_false]
      by_contra h; exact hω (subset_toMeasurable _ _ h)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t
    simp [hω]

/-- **Good version of the wave function.** A wave function `ψ` for `𝓕` has a version `ψ'`,
indistinguishable from `ψ`, which is a wave function for `𝓕ᵃ`, has all its paths continuous
on `[0, ∞)`, and vanishes outside `Λ_L` for every `ω`. -/
theorem IsWaveFunction.exists_good {L : ℕ∞} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveFunction L (QSSEPtoKPZ.nullAug μ 𝓕) B ψ' μ ∧
      (∀ ω, Continuous fun t : ℝ≥0 => ψ' t ω) ∧
      (∀ ω, ∀ (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ' t ω x = 0) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω := by
  classical
  set N := toMeasurable μ {ω | ¬ ((Continuous fun t : ℝ≥0 => ψ t ω) ∧
    ∀ (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0)} with hNdef
  have hN0 : μ N = 0 := by
    rw [hNdef, measure_toMeasurable]; exact ae_iff.1 (hψ.continuous.and hψ.support)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω, ω ∉ N → (Continuous fun t : ℝ≥0 => ψ t ω) ∧
      ∀ (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0 := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  set ψ' : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω => if ω ∈ N then 0 else ψ t ω with hψ'
  have hψψ' : ∀ᵐ ω ∂μ, ∀ t, ψ' t ω = ψ t ω := by
    filter_upwards [hNa] with ω hω t; simp [ψ', hω]
  have hcont : ∀ ω, Continuous fun t : ℝ≥0 => ψ' t ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp only [ψ', hω, ite_true]; exact continuous_const
    · simp only [ψ', hω, ite_false]; exact (hgood ω hω).1
  have hsupp : ∀ ω, ∀ (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ' t ω x = 0 := fun ω t x hx => by
    by_cases hω : ω ∈ N
    · simp [ψ', hω]
    · simp only [ψ', hω, ite_false]; exact (hgood ω hω).2 t x hx
  refine ⟨ψ', ⟨fun t x => ?_, ae_of_all _ hcont, ae_of_all _ hsupp, fun t x hx => ?_⟩, hcont,
    hsupp, hψψ'.mono fun _ h t => h t⟩
  · have e : (fun ω => ψ' t ω x) = fun ω => if ω ∈ N then 0 else ψ t ω x := by
      ext ω; by_cases hω : ω ∈ N <;> simp [ψ', hω]
    rw [e]
    exact Measurable.ite (nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0))
      measurable_const ((hψ.adapted t x).mono (le_nullAug μ 𝓕 t) le_rfl)
  · refine (hψ.sde t x hx).congr (fun m => ?_) ?_
    · filter_upwards [hψψ'] with ω hω
      simp only [itoSum, hω]
    · filter_upwards [hψψ'] with ω hω
      simp only [hω]

/-! ### Transfer lemmas for `IsCL2Mart` and `HasBracket` -/

/-- `M` is a continuous `L²` martingale on `[0, T]` for `𝓕ᵃ` iff it is one for `𝓕`. -/
theorem isCL2Mart_nullAug_iff [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ} :
    IsCL2Mart T (nullAug μ 𝓕) M μ ↔ IsCL2Mart T 𝓕 M μ :=
  ⟨fun h => ⟨h.cont, h.memLp, fun s t hst ht =>
      (condExp_nullAug (𝓕 := 𝓕) (M t) s).symm.trans (h.condExp s t hst ht)⟩,
    fun h => ⟨h.cont, h.memLp, fun s t hst ht =>
      (condExp_nullAug (𝓕 := 𝓕) (M t) s).trans (h.condExp s t hst ht)⟩⟩

/-- `⟨M⟩ = A` on `[0, T]` for `𝓕ᵃ` iff for `𝓕`. -/
theorem hasBracket_nullAug_iff [IsFiniteMeasure μ] {T : ℝ} {M A : ℝ → Ω → ℝ} :
    HasBracket T (nullAug μ 𝓕) M A μ ↔ HasBracket T 𝓕 M A μ :=
  ⟨fun h => { toIsCL2Mart := isCL2Mart_nullAug_iff.1 h.toIsCL2Mart
              integrable_bracket := h.integrable_bracket
              zero := h.zero
              mono := h.mono
              cont_bracket := h.cont_bracket
              condExp_sq := fun s t hst ht =>
                (condExp_nullAug (𝓕 := 𝓕) _ s).symm.trans (h.condExp_sq s t hst ht) },
    fun h => { toIsCL2Mart := isCL2Mart_nullAug_iff.2 h.toIsCL2Mart
               integrable_bracket := h.integrable_bracket
               zero := h.zero
               mono := h.mono
               cont_bracket := h.cont_bracket
               condExp_sq := fun s t hst ht =>
                 (condExp_nullAug (𝓕 := 𝓕) _ s).trans (h.condExp_sq s t hst ht) }⟩

/-- `IsCL2Mart` is stable under indistinguishability on `[0, T]`. -/
theorem IsCL2Mart.congr {T : ℝ} {M M' : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M μ)
    (h : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, M t ω = M' t ω) : IsCL2Mart T 𝓕 M' μ := by
  have hae : ∀ t : ℝ≥0, (t : ℝ) ≤ T → M t =ᵐ[μ] M' t := fun t ht => by
    filter_upwards [h] with ω hω using hω t ⟨t.2, ht⟩
  refine ⟨?_, fun t ht => (hM.memLp t ht).ae_eq (hae t ht), fun s t hst ht => ?_⟩
  · filter_upwards [hM.cont, h] with ω hc hω
    exact hc.congr fun t ht => (hω t ht).symm
  · exact (condExp_congr_ae (hae t ht).symm).trans ((hM.condExp s t hst ht).trans
      (hae s (le_trans (NNReal.coe_le_coe.2 hst) ht)))

/-- `HasBracket` is stable under indistinguishability of `M` and of `A` on `[0, T]`
(`T ≥ 0` is needed for the condition `A 0 = 0`). -/
theorem HasBracket.congr {T : ℝ} (hT : 0 ≤ T) {M M' A A' : ℝ → Ω → ℝ}
    (h : HasBracket T 𝓕 M A μ) (hM : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, M t ω = M' t ω)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, A t ω = A' t ω) : HasBracket T 𝓕 M' A' μ := by
  have haeA : ∀ t : ℝ≥0, (t : ℝ) ≤ T → A t =ᵐ[μ] A' t := fun t ht => by
    filter_upwards [hA] with ω hω using hω t ⟨t.2, ht⟩
  have e : ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      (fun ω => M u ω ^ 2 - A u ω) =ᵐ[μ] fun ω => M' u ω ^ 2 - A' u ω := fun u hu => by
    filter_upwards [hM, hA] with ω h1 h2
    rw [h1 u ⟨u.2, hu⟩, h2 u ⟨u.2, hu⟩]
  refine { toIsCL2Mart := h.toIsCL2Mart.congr hM
           integrable_bracket := fun t ht => (h.integrable_bracket t ht).congr (haeA t ht)
           zero := ?_, mono := ?_, cont_bracket := ?_, condExp_sq := ?_ }
  · filter_upwards [h.zero, hA] with ω h0 hω
    rw [← hω 0 ⟨le_rfl, hT⟩]; exact h0
  · filter_upwards [h.mono, hA] with ω hm hω
    intro a ha b hb hab
    show A' a ω ≤ A' b ω
    rw [← hω a ha, ← hω b hb]; exact hm ha hb hab
  · filter_upwards [h.cont_bracket, hA] with ω hc hω
    exact hc.congr fun t ht => (hω t ht).symm
  · intro s t hst ht
    exact (condExp_congr_ae (e t ht).symm).trans ((h.condExp_sq s t hst ht).trans
      (e s (le_trans (NNReal.coe_le_coe.2 hst) ht)))

/-- Restriction of the horizon: a continuous `L²` martingale on `[0, T]` is one on `[0, S]`
for `S ≤ T`. -/
theorem IsCL2Mart.mono_horizon {S T : ℝ} {M : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M μ) (hST : S ≤ T) :
    IsCL2Mart S 𝓕 M μ :=
  ⟨hM.cont.mono fun _ h => h.mono (Set.Icc_subset_Icc_right hST),
    fun t ht => hM.memLp t (ht.trans hST), fun s t hst ht => hM.condExp s t hst (ht.trans hST)⟩

/-- Restriction of the horizon for `HasBracket`. -/
theorem HasBracket.mono_horizon {S T : ℝ} {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ)
    (hST : S ≤ T) : HasBracket S 𝓕 M A μ :=
  { toIsCL2Mart := h.toIsCL2Mart.mono_horizon hST
    integrable_bracket := fun t ht => h.integrable_bracket t (ht.trans hST)
    zero := h.zero
    mono := h.mono.mono fun _ h => h.mono (Set.Icc_subset_Icc_right hST)
    cont_bracket := h.cont_bracket.mono fun _ h => h.mono (Set.Icc_subset_Icc_right hST)
    condExp_sq := fun s t hst ht => h.condExp_sq s t hst (ht.trans hST) }

/-- The map `t ↦ c t` sends `[0, T]` into `[0, c T]`. -/
lemma mapsTo_mul_Icc (c : ℝ≥0) (T : ℝ) :
    Set.MapsTo (fun t : ℝ => (c : ℝ) * t) (Set.Icc 0 T) (Set.Icc 0 ((c : ℝ) * T)) :=
  fun _ ht => ⟨mul_nonneg c.2 ht.1, mul_le_mul_of_nonneg_left ht.2 c.2⟩

/-- Time change: if `M` is a continuous `L²` martingale on `[0, c T]` for `𝓕`, then
`t ↦ M_{c t}` is one on `[0, T]` for the filtration `t ↦ 𝓕_{c t}`. -/
theorem IsCL2Mart.timeChange {c : ℝ≥0} {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart ((c : ℝ) * T) 𝓕 M μ) :
    IsCL2Mart T (timeChange c 𝓕) (fun t => M ((c : ℝ) * t)) μ := by
  refine ⟨?_, fun t ht => ?_, fun s t hst ht => ?_⟩
  · filter_upwards [hM.cont] with ω hω
    exact hω.comp (continuousOn_const.mul continuousOn_id) (mapsTo_mul_Icc c T)
  · have := hM.memLp (c * t) (by push_cast; exact mul_le_mul_of_nonneg_left ht c.2)
    rw [NNReal.coe_mul] at this
    exact this
  · have := hM.condExp (c * s) (c * t) (mul_le_mul_of_nonneg_left hst c.2)
      (by push_cast; exact mul_le_mul_of_nonneg_left ht c.2)
    rw [NNReal.coe_mul, NNReal.coe_mul] at this
    exact this

/-- Time change for `HasBracket`: `⟨M⟩ = A` on `[0, c T]` for `𝓕` gives
`⟨M_{c ·}⟩ = A_{c ·}` on `[0, T]` for `t ↦ 𝓕_{c t}`. -/
theorem HasBracket.timeChange {c : ℝ≥0} {T : ℝ} {M A : ℝ → Ω → ℝ}
    (h : HasBracket ((c : ℝ) * T) 𝓕 M A μ) :
    HasBracket T (timeChange c 𝓕) (fun t => M ((c : ℝ) * t)) (fun t => A ((c : ℝ) * t)) μ := by
  refine { toIsCL2Mart := h.toIsCL2Mart.timeChange
           integrable_bracket := fun t ht => ?_
           zero := ?_, mono := ?_, cont_bracket := ?_, condExp_sq := fun s t hst ht => ?_ }
  · have := h.integrable_bracket (c * t) (by push_cast; exact mul_le_mul_of_nonneg_left ht c.2)
    rw [NNReal.coe_mul] at this
    exact this
  · simpa only [mul_zero] using h.zero
  · filter_upwards [h.mono] with ω hω
    intro a ha b hb hab
    exact hω (mapsTo_mul_Icc c T ha) (mapsTo_mul_Icc c T hb) (mul_le_mul_of_nonneg_left hab c.2)
  · filter_upwards [h.cont_bracket] with ω hω
    exact hω.comp (continuousOn_const.mul continuousOn_id) (mapsTo_mul_Icc c T)
  · have := h.condExp_sq (c * s) (c * t) (mul_le_mul_of_nonneg_left hst c.2)
      (by push_cast; exact mul_le_mul_of_nonneg_left ht c.2)
    rw [NNReal.coe_mul, NNReal.coe_mul] at this
    exact this

/-- A constant multiple of a continuous `L²` martingale is one. -/
theorem IsCL2Mart.const_mul {T : ℝ} {M : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M μ) (c : ℝ) :
    IsCL2Mart T 𝓕 (fun t ω => c * M t ω) μ := by
  refine ⟨hM.cont.mono fun _ h => continuousOn_const.mul h,
    fun t ht => (hM.memLp t ht).const_mul c, fun s t hst ht => ?_⟩
  have e : ∀ u : ℝ≥0, (fun ω => c * M u ω) = c • M u := fun u => rfl
  simp only [e]
  exact (condExp_smul c (M t) (𝓕 s)).trans
    ((hM.condExp s t hst ht).mono fun ω hω => by simp [hω])

/-- `⟨c M⟩ = c² ⟨M⟩`. -/
theorem HasBracket.const_mul {T : ℝ} {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ) (c : ℝ) :
    HasBracket T 𝓕 (fun t ω => c * M t ω) (fun t ω => c ^ 2 * A t ω) μ := by
  refine { toIsCL2Mart := h.toIsCL2Mart.const_mul c
           integrable_bracket := fun t ht => (h.integrable_bracket t ht).const_mul (c ^ 2)
           zero := ?_, mono := ?_, cont_bracket := ?_, condExp_sq := fun s t hst ht => ?_ }
  · filter_upwards [h.zero] with ω hω; simp [hω]
  · filter_upwards [h.mono] with ω hω
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (hω ha hb hab) (sq_nonneg c)
  · filter_upwards [h.cont_bracket] with ω hω
    exact continuousOn_const.mul hω
  · have e : ∀ u : ℝ≥0, (fun ω => (c * M u ω) ^ 2 - c ^ 2 * A u ω) =
        (c ^ 2) • fun ω => M u ω ^ 2 - A u ω := fun u => by
      ext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
    simp only [e]
    exact (condExp_smul (c ^ 2) _ (𝓕 s)).trans
      ((h.condExp_sq s t hst ht).mono fun ω hω => by simp [hω])

/-- The sum of two continuous `L²` martingales is one (finite measure). -/
theorem IsCL2Mart.add [IsFiniteMeasure μ] {T : ℝ} {M N : ℝ → Ω → ℝ} (hM : IsCL2Mart T 𝓕 M μ)
    (hN : IsCL2Mart T 𝓕 N μ) : IsCL2Mart T 𝓕 (fun t ω => M t ω + N t ω) μ := by
  refine ⟨?_, fun t ht => (hM.memLp t ht).add (hN.memLp t ht), fun s t hst ht => ?_⟩
  · filter_upwards [hM.cont, hN.cont] with ω h1 h2 using h1.add h2
  · exact (condExp_add ((hM.memLp t ht).integrable one_le_two)
      ((hN.memLp t ht).integrable one_le_two) _).trans
      ((hM.condExp s t hst ht).add (hN.condExp s t hst ht))

/-- A Mathlib martingale (indexed by `ℝ≥0`) with almost surely continuous paths on `[0, T]` and
square-integrable on `[0, T]` is a continuous `L²` martingale on `[0, T]`. -/
theorem isCL2Mart_of_martingale {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : Martingale (fun t : ℝ≥0 => M t) 𝓕 μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (hL2 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → MemLp (M t) 2 μ) : IsCL2Mart T 𝓕 M μ :=
  ⟨hc, hL2, fun s t hst _ => hM.2 s t hst⟩

/-- Conversely, a continuous `L²` martingale on `[0, T]` which is adapted (for every `ω`), once
frozen after time `T`, is a Mathlib martingale indexed by `ℝ≥0` (finite measure). -/
theorem IsCL2Mart.martingale_stopped [IsFiniteMeasure μ] {T : ℝ≥0} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) (hadapt : ∀ t : ℝ≥0, StronglyMeasurable[𝓕 t] (M t)) :
    Martingale (fun t : ℝ≥0 => M (min t T : ℝ≥0)) 𝓕 μ := by
  refine ⟨fun t => (hadapt (min t T)).mono (𝓕.mono (min_le_left t T)), fun s t hst => ?_⟩
  show μ[M ↑(min t T) | 𝓕 s] =ᵐ[μ] M ↑(min s T)
  rcases le_total s T with hsT | hTs
  · rw [min_eq_left hsT]
    exact hM.condExp s (min t T) (le_min hst hsT) (NNReal.coe_le_coe.2 (min_le_right t T))
  · rw [min_eq_right hTs, min_eq_right (hTs.trans hst),
      condExp_of_stronglyMeasurable (𝓕.le s) ((hadapt T).mono (𝓕.mono hTs))
        ((hM.memLp T le_rfl).integrable one_le_two)]

/-! ### Good version of a continuous `L²` martingale

Placed last because its proof uses `isCL2Mart_nullAug_iff` and `IsCL2Mart.congr`. -/

/-- The grid point `k / (n + 1)`, for `p = (k, n)`. -/
def ratGridPt (p : ℕ × ℕ) : ℝ≥0 := (p.1 : ℝ≥0) / ((p.2 : ℝ≥0) + 1)

/-- The approximation `⌊(n + 1) t⌋ / (n + 1)` of `t` from below, a grid point. -/
def gridBelow (t : ℝ≥0) (n : ℕ) : ℝ≥0 := ratGridPt (⌊((n : ℝ) + 1) * t⌋₊, n)

/-- `gridBelow t n` as a real number. -/
lemma coe_gridBelow (t : ℝ≥0) (n : ℕ) :
    (gridBelow t n : ℝ) = (⌊((n : ℝ) + 1) * t⌋₊ : ℝ) / ((n : ℝ) + 1) := by
  simp [gridBelow, ratGridPt]

/-- The grid approximation lies below `t`. -/
lemma gridBelow_le (t : ℝ≥0) (n : ℕ) : gridBelow t n ≤ t := by
  rw [← NNReal.coe_le_coe, coe_gridBelow, div_le_iff₀ (by positivity)]
  calc _ ≤ ((n : ℝ) + 1) * t := Nat.floor_le (by positivity)
    _ = _ := mul_comm _ _

/-- `⌊(n + 1) t⌋ / (n + 1) → t`. -/
lemma tendsto_gridBelow (t : ℝ≥0) :
    Tendsto (fun n => (gridBelow t n : ℝ)) atTop (𝓝 (t : ℝ)) := by
  have hlow : ∀ n : ℕ, (t : ℝ) - 1 / ((n : ℝ) + 1) ≤ gridBelow t n := fun n => by
    rw [coe_gridBelow, le_div_iff₀ (by positivity), sub_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
    have := Nat.lt_floor_add_one (((n : ℝ) + 1) * t)
    linarith [mul_comm ((n : ℝ) + 1) (t : ℝ)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow
    (fun n => NNReal.coe_le_coe.2 (gridBelow_le t n))
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := (t : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Good version of a continuous `L²` martingale.** A continuous square-integrable martingale
on `[0, T]` up to null sets has a version `M'`, indistinguishable from `M` on `[0, T]`, adapted
to `𝓕ᵃ`, with all its paths continuous on `[0, T]`; it is again a continuous `L²` martingale,
for `𝓕ᵃ` (hence also for `𝓕`, by `isCL2Mart_nullAug_iff`). -/
theorem IsCL2Mart.exists_version [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) :
    ∃ M' : ℝ → Ω → ℝ, (∀ t : ℝ≥0, StronglyMeasurable[nullAug μ 𝓕 t] (M' t)) ∧
      (∀ ω, ContinuousOn (fun t => M' t ω) (Set.Icc 0 T)) ∧
      (∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, M' t ω = M t ω) ∧ IsCL2Mart T (nullAug μ 𝓕) M' μ := by
  classical
  rcases lt_or_ge T 0 with hT | hT
  · refine ⟨fun _ _ => 0, fun _ => stronglyMeasurable_const, fun _ => continuousOn_const,
      ae_of_all _ fun ω t ht => absurd (ht.1.trans ht.2) (not_le.2 hT),
      ⟨ae_of_all _ fun _ => continuousOn_const, fun t ht => absurd (t.2.trans ht) (not_le.2 hT),
        fun s t _ ht => absurd (t.2.trans ht) (not_le.2 hT)⟩⟩
  -- `Y r` is an `𝓕_r`-measurable version of `M r`; outside a null set `N`, the path of `M` is
  -- continuous on `[0, T]` and `M = Y` at the grid points
  set Y : ℝ≥0 → Ω → ℝ := fun r => μ[M r | 𝓕 r] with hY
  have hgood : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T) ∧
      ∀ p : ℕ × ℕ, (ratGridPt p : ℝ) ≤ T → M (ratGridPt p) ω = Y (ratGridPt p) ω := by
    refine hM.cont.and (ae_all_iff.2 fun p => ?_)
    by_cases hp : (ratGridPt p : ℝ) ≤ T
    · filter_upwards [hM.condExp (ratGridPt p) (ratGridPt p) le_rfl hp] with ω hω _
      exact hω.symm
    · exact ae_of_all _ fun ω h => absurd h hp
  set N := toMeasurable μ {ω | ¬ (ContinuousOn (fun t => M t ω) (Set.Icc 0 T) ∧
      ∀ p : ℕ × ℕ, (ratGridPt p : ℝ) ≤ T → M (ratGridPt p) ω = Y (ratGridPt p) ω)} with hNdef
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hgood
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hNt : ∀ t : ℝ≥0, MeasurableSet[nullAug μ 𝓕 t] N := fun t =>
    nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0)
  have hok : ∀ ω, ω ∉ N → ContinuousOn (fun t => M t ω) (Set.Icc 0 T) ∧
      ∀ p : ℕ × ℕ, (ratGridPt p : ℝ) ≤ T → M (ratGridPt p) ω = Y (ratGridPt p) ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  -- the version: `0` on `N`, `M` frozen after `T` outside `N`
  set M' : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else M (min t T) ω with hM'
  have hM'eq : ∀ ω, ω ∉ N → ∀ t ∈ Set.Icc 0 T, M' t ω = M t ω := fun ω hω t ht => by
    simp [M', hω, min_eq_left ht.2]
  -- adaptedness for `t ≤ T`: limit of the versions at the grid points below `t`
  have hmeasT : ∀ t : ℝ≥0, (t : ℝ) ≤ T → StronglyMeasurable[nullAug μ 𝓕 t] (M' t) := by
    intro t ht
    have hseq : ∀ n, StronglyMeasurable[nullAug μ 𝓕 t]
        (fun ω => if ω ∈ N then 0 else Y (gridBelow t n) ω) := fun n =>
      StronglyMeasurable.ite (hNt t) stronglyMeasurable_const
        (stronglyMeasurable_condExp.mono
          ((𝓕.mono (gridBelow_le t n)).trans (le_nullAug μ 𝓕 t)))
    refine stronglyMeasurable_of_tendsto atTop hseq (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ N
    · simp only [M', hω, ite_true]; exact tendsto_const_nhds
    · have hle : ∀ n, (gridBelow t n : ℝ) ≤ T := fun n =>
        (NNReal.coe_le_coe.2 (gridBelow_le t n)).trans ht
      have e : ∀ n, (if ω ∈ N then 0 else Y (gridBelow t n) ω) = M (gridBelow t n) ω :=
        fun n => by
          simp only [hω, ite_false]
          exact ((hok ω hω).2 (⌊((n : ℝ) + 1) * t⌋₊, n) (hle n)).symm
      simp only [e, hM'eq ω hω t ⟨t.2, ht⟩]
      have hlim : Tendsto (fun n => (gridBelow t n : ℝ)) atTop (𝓝[Set.Icc 0 T] (t : ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_gridBelow t,
          Eventually.of_forall fun n => ⟨(gridBelow t n).2, hle n⟩⟩
      exact ((hok ω hω).1 t ⟨t.2, ht⟩).tendsto.comp hlim
  have hmeas : ∀ t : ℝ≥0, StronglyMeasurable[nullAug μ 𝓕 t] (M' t) := by
    intro t
    rcases le_total (t : ℝ) T with ht | ht
    · exact hmeasT t ht
    · have e : M' t = M' (⟨T, hT⟩ : ℝ≥0) := by
        ext ω; simp only [M', min_eq_right ht, min_self]
      rw [e]
      exact (hmeasT _ le_rfl).mono
        ((nullAug μ 𝓕).mono (NNReal.coe_le_coe.1 ht : (⟨T, hT⟩ : ℝ≥0) ≤ t))
  have hae : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, M' t ω = M t ω := by
    filter_upwards [hNa] with ω hω t ht using hM'eq ω hω t ht
  refine ⟨M', hmeas, fun ω => ?_, hae, isCL2Mart_nullAug_iff.2 (hM.congr ?_)⟩
  · by_cases hω : ω ∈ N
    · have : (fun t => M' t ω) = fun _ => 0 := by ext t; simp [M', hω]
      rw [this]; exact continuousOn_const
    · exact (hok ω hω).1.congr (hM'eq ω hω)
  · filter_upwards [hae] with ω hω t ht using (hω t ht).symm

end QSSEPtoKPZ
