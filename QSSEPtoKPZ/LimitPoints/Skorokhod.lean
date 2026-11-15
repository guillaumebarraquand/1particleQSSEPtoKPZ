/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.SkorokhodPartition
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.BorelCantelli

/-!
# Skorokhod's representation along a subsequence (task G1, decision D1″)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G1.
See `docs/stage4-design.md`, Sections 1.2 (a) and 3.2, and `docs/stage4-interfaces.md`.

The article (Section 7.1) uses Skorokhod's representation theorem on the Polish space
`C([0,T], ℳ₊)` (Billingsley, Theorem 6.7). Mathlib has neither this theorem nor the completeness
of `ℳ₊`. Only subsequences are ever used, and along a subsequence the representation holds on any
separable metrizable space, with an explicit coupling (partitions into continuity sets of small
diameter, `Measure.infinitePi`, Borel–Cantelli). No completeness is needed.

The space `S` has no metric instance: the proof uses
`TopologicalSpace.metrizableSpaceMetric S` locally.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- **Mixture decomposition.** Given a probability measure `Q`, weights `p i` summing to `1` and
measures `lam i` of mass at most `p i` with `∑ lam i ≤ Q`, there are probability measures `ν i`
with `∑ p i • ν i = Q` and `p i • ν i = lam i + (p i - lam i(univ)) • R` for one probability
measure `R` (the normalized remainder `Q - ∑ lam i`). -/
private lemma skoro_mixture {S : Type*} [MeasurableSpace S] {ι : Type*} [Fintype ι]
    (Q : Measure S) [IsProbabilityMeasure Q] (p : ι → ℝ≥0∞) (hp : ∑ i, p i = 1)
    (lam : ι → Measure S) (hlp : ∀ i, lam i Set.univ ≤ p i) (hlQ : ∑ i, lam i ≤ Q) :
    ∃ (R : Measure S) (ν : ι → Measure S), IsProbabilityMeasure R ∧
      (∀ i, IsProbabilityMeasure (ν i)) ∧
      (∀ i, p i • ν i = lam i + (p i - lam i Set.univ) • R) ∧ ∑ i, p i • ν i = Q := by
  classical
  set L : Measure S := ∑ i, lam i with hL
  have : IsFiniteMeasure L := isFiniteMeasure_of_le Q hlQ
  set rem : Measure S := Q - L with hrem_def
  have hrem : rem + L = Q := Measure.sub_add_cancel_of_le hlQ
  set a : ℝ≥0∞ := rem Set.univ with ha_def
  have hLuniv : L Set.univ = ∑ i, lam i Set.univ := by simp [hL]
  have hp_le : ∀ i, p i ≤ 1 := fun i => hp ▸ Finset.single_le_sum (fun j _ => zero_le)
    (Finset.mem_univ i)
  have ha : a = ∑ i, (p i - lam i Set.univ) := by
    have h1 : a + L Set.univ = 1 := by rw [ha_def, ← Measure.add_apply, hrem, measure_univ]
    have h2 : (∑ i, (p i - lam i Set.univ)) + L Set.univ = 1 := by
      rw [hLuniv, ← Finset.sum_add_distrib]
      simp only [tsub_add_cancel_of_le (hlp _), hp]
    exact (ENNReal.add_left_inj (measure_ne_top L _)).1 (h1.trans h2.symm)
  have ha_top : a ≠ ⊤ := measure_ne_top _ _
  set R : Measure S := if a = 0 then Q else a⁻¹ • rem with hR_def
  have haR : a • R = rem := by
    by_cases h0 : a = 0
    · simp only [hR_def, h0, ↓reduceIte, zero_smul]
      exact ((Measure.measure_univ_eq_zero).1 h0).symm
    · simp only [hR_def, h0, ↓reduceIte, smul_smul, ENNReal.mul_inv_cancel h0 ha_top, one_smul]
  have hRprob : IsProbabilityMeasure R := by
    by_cases h0 : a = 0
    · simp only [hR_def, h0, ↓reduceIte]; infer_instance
    · simp only [hR_def, h0, ↓reduceIte]
      constructor
      rw [Measure.smul_apply, smul_eq_mul, ← ha_def, ENNReal.inv_mul_cancel h0 ha_top]
  set ν : ι → Measure S := fun i =>
    if p i = 0 then Q else (p i)⁻¹ • (lam i + (p i - lam i Set.univ) • R) with hν_def
  have hpt : ∀ i, p i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hp_le i)
  have hν : ∀ i, p i • ν i = lam i + (p i - lam i Set.univ) • R := by
    intro i
    by_cases h0 : p i = 0
    · have hl : lam i = 0 := (Measure.measure_univ_eq_zero).1 (le_antisymm (h0 ▸ hlp i) zero_le)
      simp [hν_def, h0, hl]
    · simp only [hν_def, h0, ↓reduceIte, smul_smul, ENNReal.mul_inv_cancel h0 (hpt i), one_smul]
  refine ⟨R, ν, hRprob, fun i => ?_, hν, ?_⟩
  · by_cases h0 : p i = 0
    · simp only [hν_def, h0, ↓reduceIte]; infer_instance
    · constructor
      simp only [hν_def, h0, ↓reduceIte, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
        measure_univ, mul_one]
      rw [add_tsub_cancel_of_le (hlp i), ENNReal.inv_mul_cancel h0 (hpt i)]
  · simp only [hν, Finset.sum_add_distrib, ← Finset.sum_smul, ← ha, haR]
    rw [← hL, add_comm, hrem]

/-- The cells of one level: `none` is the uncovered remainder, `some i` the set `A i`. -/
private def skoroCellSet {S : Type*} {m : ℕ} (A : Fin m → Set S) : Option (Fin m) → Set S
  | none => (⋃ i, A i)ᶜ
  | some i => A i

open Classical in
/-- The index of the cell containing `x`. -/
private def skoroCell {S : Type*} {m : ℕ} (A : Fin m → Set S) (x : S) : Option (Fin m) :=
  if h : ∃ i, x ∈ A i then some h.choose else none

/-- The sets where the coupling may fail at one level: everything on the remainder,
the complement of the cell on a cell. -/
private def skoroBadSet {S : Type*} {m : ℕ} (A : Fin m → Set S) : Option (Fin m) → Set S
  | none => Set.univ
  | some i => (A i)ᶜ

/-- The sub-measures `λ_i = (c_i / Q(A_i)) Q|_{A_i}` with `c_i = min(Q(A_i), P(A_i))`. -/
private def skoroLam {S : Type*} [MeasurableSpace S] (Q Pl : Measure S) {m : ℕ}
    (A : Fin m → Set S) :
    Option (Fin m) → Measure S
  | none => 0
  | some i => (min (Q (A i)) (Pl (A i)) / Q (A i)) • Q.restrict (A i)

section cells

variable {S : Type*} {m : ℕ} {A : Fin m → Set S}

/-- `x` lies in cell `o` iff the cell index of `x` is `o` (the cells are disjoint). -/
private lemma skoroCell_eq_iff (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (x : S)
    (o : Option (Fin m)) : skoroCell A x = o ↔ x ∈ skoroCellSet A o := by
  classical
  unfold skoroCell
  split_ifs with h
  · cases o with
    | none => simpa [skoroCellSet] using h
    | some i =>
      simp only [Option.some.injEq, skoroCellSet]
      constructor
      · rintro rfl; exact h.choose_spec
      · intro hi
        by_contra hne
        exact Set.disjoint_left.1 (hA hne) h.choose_spec hi
  · push Not at h
    cases o with
    | none => simpa [skoroCellSet] using h
    | some i => simpa [skoroCellSet] using h i

/-- The cells of one level are pairwise disjoint. -/
private lemma skoroCellSet_disjoint (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Pairwise (fun o o' => Disjoint (skoroCellSet A o) (skoroCellSet A o')) := by
  intro o o' hne
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [← skoroCell_eq_iff hA] at h1 h2
  exact hne (h1.symm.trans h2)

/-- The failure sets are measurable. -/
private lemma skoroBadSet_measurable [MeasurableSpace S] (hA : ∀ i, MeasurableSet (A i))
    (o : Option (Fin m)) : MeasurableSet (skoroBadSet A o) := by
  cases o with
  | none => exact MeasurableSet.univ
  | some i => exact (hA i).compl

/-- The cells are measurable. -/
private lemma skoroCellSet_measurable [MeasurableSpace S] (hA : ∀ i, MeasurableSet (A i))
    (o : Option (Fin m)) : MeasurableSet (skoroCellSet A o) := by
  cases o with
  | none => exact (MeasurableSet.iUnion hA).compl
  | some i => exact hA i

end cells

section lam

variable {S : Type*} [MeasurableSpace S] {m : ℕ} {A : Fin m → Set S}

/-- The mass of `λ_i` is `c_i = min(Q(A_i), P(A_i))`. -/
private lemma skoroLam_univ (Q Pl : Measure S) [IsFiniteMeasure Q] (i : Fin m) :
    skoroLam Q Pl A (some i) Set.univ = min (Q (A i)) (Pl (A i)) := by
  simp only [skoroLam, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  by_cases h0 : Q (A i) = 0
  · simp [h0]
  · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _)

/-- `λ_i` does not charge the complement of `A_i`. -/
private lemma skoroLam_compl (Q Pl : Measure S) (hA : ∀ i, MeasurableSet (A i)) (i : Fin m) :
    skoroLam Q Pl A (some i) (A i)ᶜ = 0 := by
  simp [skoroLam, Measure.restrict_apply (hA i).compl]

/-- The mass of `λ_o` is at most the `P`-mass of the cell `o`. -/
private lemma skoroLam_univ_le (Q Pl : Measure S) [IsFiniteMeasure Q] (o : Option (Fin m)) :
    skoroLam Q Pl A o Set.univ ≤ Pl (skoroCellSet A o) := by
  cases o with
  | none => simp [skoroLam]
  | some i => rw [skoroLam_univ]; exact min_le_right _ _

/-- `∑_o λ_o ≤ Q`, since `λ_i ≤ Q|_{A_i}` and the `A_i` are disjoint. -/
private lemma skoroLam_sum_le (Q Pl : Measure S) (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ o, skoroLam Q Pl A o ≤ Q := by
  rw [Measure.le_iff]
  intro s hs
  rw [Fintype.sum_option]
  simp only [skoroLam, zero_add, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply hs]
  calc ∑ i, min (Q (A i)) (Pl (A i)) / Q (A i) * Q (s ∩ A i) ≤ ∑ i, Q (s ∩ A i) := by
        refine Finset.sum_le_sum fun i _ => mul_le_of_le_one_left zero_le ?_
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact min_le_left _ _)
    _ = Q (⋃ i, s ∩ A i) := by
        rw [measure_iUnion _ (fun i => hs.inter (hA i)), tsum_fintype]
        intro i j hij
        exact (hAd hij).mono Set.inter_subset_right Set.inter_subset_right
    _ ≤ Q s := measure_mono (Set.iUnion_subset fun i => Set.inter_subset_left)

/-- The `P`-masses of the cells add up to `1`. -/
private lemma skoroCellSet_sum (Pl : Measure S) [IsProbabilityMeasure Pl]
    (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ o, Pl (skoroCellSet A o) = 1 := by
  rw [Fintype.sum_option]
  simp only [skoroCellSet]
  rw [← tsum_fintype (L := .unconditional _), ← measure_iUnion hAd hA, add_comm,
    measure_add_measure_compl
    (MeasurableSet.iUnion hA), measure_univ]

end lam

/-- The measure of a measurable rectangle `B × {z | z k ∈ F}` under `μ ⊗ ⨂ᵢ ν i`. -/
private lemma skoro_prod_rect {S : Type*} [MeasurableSpace S] {ι : Type*} (μ : Measure S)
    [SFinite μ]
    (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)] (k : ι) {B F : Set S}
    (hF : MeasurableSet F) :
    (μ.prod (Measure.infinitePi ν)) (B ×ˢ {z | z k ∈ F}) = μ B * ν k F := by
  rw [Measure.prod_prod]
  congr 1
  rw [← Measure.infinitePi_map_eval ν k, Measure.map_apply (measurable_pi_apply k) hF]
  rfl

universe u

/-- **Skorokhod's representation, along a subsequence** (generic). If the laws `P k` converge
weakly to `Plim` on a separable metrizable space `S` (with its Borel σ-algebra), then for some
subsequence `φ` there are, on one probability space, random elements `X k` with law `P (φ k)` and
`Y` with law `Plim` such that `X k → Y` almost surely. The probability space lives in the same
universe as `S`. -/
theorem skorokhod_subseq {S : Type u} [TopologicalSpace S] [TopologicalSpace.MetrizableSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    {P : ℕ → ProbabilityMeasure S} {Plim : ProbabilityMeasure S}
    (h : Tendsto P atTop (𝓝 Plim)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Pr : Measure Ω)
      (_ : IsProbabilityMeasure Pr) (X : ℕ → Ω → S) (Y : Ω → S),
      (∀ k, Measurable (X k)) ∧ Measurable Y ∧
      (∀ k, Pr.map (X k) = (P (φ k) : Measure S)) ∧ Pr.map Y = (Plim : Measure S) ∧
      ∀ᵐ ω ∂Pr, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω)) := by
  classical
  let _ : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  set Pl : Measure S := (Plim : Measure S) with hPl
  set ε : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j with hε
  have hεpos : ∀ j, 0 < ε j := fun j => pow_pos (by norm_num) j
  -- level `j`: a partition into `Plim`-continuity sets of diameter `< ε j`
  have part := fun j => skoro_exists_partition Pl (hεpos j)
  choose m A hAm hAd hAdiam hAfr hAc using part
  -- along a subsequence, `∑ᵢ (Plim(Aᵢ) - min(P_k(Aᵢ), Plim(Aᵢ))) ≤ ε j` at level `j`
  have hconv : ∀ j, ∀ᶠ k in atTop, ∑ i, (Pl (A j i) - min ((P k : Measure S) (A j i)) (Pl (A j i)))
      ≤ ENNReal.ofReal (ε j) := by
    intro j
    have hq : ∀ i, Tendsto (fun k => (P k : Measure S) (A j i)) atTop (𝓝 (Pl (A j i))) :=
      fun i => ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h (hAfr j i)
    have hlim : Tendsto (fun k => ∑ i, (Pl (A j i) - min ((P k : Measure S) (A j i)) (Pl (A j i))))
        atTop (𝓝 (∑ i, (Pl (A j i) - min (Pl (A j i)) (Pl (A j i))))) :=
      tendsto_finsetSum _ fun i _ => ENNReal.Tendsto.sub tendsto_const_nhds
        ((hq i).min tendsto_const_nhds) (Or.inl (measure_ne_top _ _))
    simp only [min_self, tsub_self, Finset.sum_const_zero] at hlim
    exact ((tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 (hεpos j))).mono fun k hk => hk.le
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_eventually hconv
  -- level `j`: the mixture decomposition of `P (φ j)` along the cells
  have mix := fun j => skoro_mixture (P (φ j) : Measure S) (fun o => Pl (skoroCellSet (A j) o))
    (skoroCellSet_sum Pl (hAm j) (hAd j)) (skoroLam (P (φ j)) Pl (A j))
    (fun o => skoroLam_univ_le _ _ o) (skoroLam_sum_le _ _ (hAm j) (hAd j))
  choose R ν hRp hνp hνeq hνsum using mix
  -- the product space
  set νall : (Σ j : ℕ, Option (Fin (m j))) → Measure S := fun k => ν k.1 k.2 with hνall
  have hνall : ∀ k, IsProbabilityMeasure (νall k) := fun k => hνp k.1 k.2
  set Pr : Measure (S × ((Σ j : ℕ, Option (Fin (m j))) → S)) :=
    Pl.prod (Measure.infinitePi νall) with hPr
  set X : ℕ → S × ((Σ j : ℕ, Option (Fin (m j))) → S) → S :=
    fun j ω => ω.2 ⟨j, skoroCell (A j) ω.1⟩ with hX
  have hpre : ∀ j E, X j ⁻¹' E = ⋃ o, skoroCellSet (A j) o ×ˢ {z | z ⟨j, o⟩ ∈ E} := by
    intro j E
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq, hX]
    constructor
    · intro hω
      exact ⟨_, (skoroCell_eq_iff (hAd j) _ _).1 rfl, hω⟩
    · rintro ⟨o, h1, h2⟩
      rwa [(skoroCell_eq_iff (hAd j) _ _).2 h1]
  have hdisj : ∀ j (F : Option (Fin (m j)) → Set S), Pairwise (fun o o' => Disjoint
      (skoroCellSet (A j) o ×ˢ {z : (Σ j : ℕ, Option (Fin (m j))) → S | z ⟨j, o⟩ ∈ F o})
      (skoroCellSet (A j) o' ×ˢ {z : (Σ j : ℕ, Option (Fin (m j))) → S | z ⟨j, o'⟩ ∈ F o'})) :=
    fun j F o o' hne => Set.disjoint_prod.2 (Or.inl (skoroCellSet_disjoint (hAd j) hne))
  have hrect_meas : ∀ j (o : Option (Fin (m j))) {F : Set S}, MeasurableSet F →
      MeasurableSet (skoroCellSet (A j) o ×ˢ
        {z : (Σ j : ℕ, Option (Fin (m j))) → S | z ⟨j, o⟩ ∈ F}) :=
    fun j o F hF => (skoroCellSet_measurable (hAm j) o).prod (measurable_pi_apply _ hF)
  have hXm : ∀ j, Measurable (X j) := by
    intro j E hE
    rw [hpre]
    exact MeasurableSet.iUnion fun o => hrect_meas j o hE
  refine ⟨φ, hφ, S × ((Σ j : ℕ, Option (Fin (m j))) → S), inferInstance, Pr, inferInstance, X,
    Prod.fst, hXm, measurable_fst, ?_, ?_, ?_⟩
  · -- the law of `X j`
    intro j
    ext E hE
    rw [Measure.map_apply (hXm j) hE, hpre, measure_iUnion (hdisj j fun _ => E)
      (fun o => hrect_meas j o hE), tsum_fintype (L := .unconditional _), ← hνsum j]
    simp only [hPr, skoro_prod_rect _ νall _ hE, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.smul_apply, smul_eq_mul]
    rfl
  · -- the law of `Y`
    rw [hPr, Measure.map_fst_prod, measure_univ, one_smul]
  · -- almost sure convergence, by Borel–Cantelli
    set bad : ℕ → Set (S × ((Σ j : ℕ, Option (Fin (m j))) → S)) :=
      fun j => {ω | ε j ≤ dist (X j ω) ω.1} with hbad
    have hbad_sub : ∀ j, bad j ⊆
        ⋃ o, skoroCellSet (A j) o ×ˢ {z | z ⟨j, o⟩ ∈ skoroBadSet (A j) o} := by
      intro j ω hω
      obtain ⟨o, ho⟩ : ∃ o, skoroCell (A j) ω.1 = o := ⟨_, rfl⟩
      have h1 := (skoroCell_eq_iff (hAd j) _ _).1 ho
      refine Set.mem_iUnion.2 ⟨o, h1, ?_⟩
      cases o with
      | none => trivial
      | some i =>
        simp only [Set.mem_ofPred_eq, skoroBadSet, Set.mem_compl_iff]
        intro h2
        have hlt := hAdiam j i _ h2 _ h1
        simp only [hbad, Set.mem_ofPred_eq, hX, ho] at hω
        linarith
    have hbad_le : ∀ j, Pr (bad j) ≤ 2 * ENNReal.ofReal (ε j) := by
      intro j
      refine (measure_mono (hbad_sub j)).trans ((measure_iUnion_fintype_le _ _).trans ?_)
      have hrect : ∀ o, Pr (skoroCellSet (A j) o ×ˢ {z | z ⟨j, o⟩ ∈ skoroBadSet (A j) o}) =
          (Pl (skoroCellSet (A j) o) • ν j o) (skoroBadSet (A j) o) := fun o => by
        rw [hPr, skoro_prod_rect _ νall _ (skoroBadSet_measurable (hAm j) o), Measure.smul_apply,
          smul_eq_mul]
      simp only [hrect]
      rw [Fintype.sum_option]
      calc (Pl (skoroCellSet (A j) none) • ν j none) (skoroBadSet (A j) none) +
            ∑ i, (Pl (skoroCellSet (A j) (some i)) • ν j (some i)) (skoroBadSet (A j) (some i))
          ≤ ENNReal.ofReal (ε j) + ∑ i, (Pl (A j i) - min ((P (φ j) : Measure S) (A j i))
            (Pl (A j i))) := by
            refine add_le_add ?_ (Finset.sum_le_sum fun i _ => ?_)
            · simpa [skoroBadSet, skoroCellSet] using hAc j
            · rw [hνeq j (some i), Measure.add_apply, Measure.smul_apply]
              simp only [skoroBadSet, skoroCellSet]
              rw [skoroLam_compl _ _ (hAm j) i, skoroLam_univ, zero_add, smul_eq_mul]
              exact mul_le_of_le_one_right zero_le prob_le_one
        _ ≤ ENNReal.ofReal (ε j) + ENNReal.ofReal (ε j) := add_le_add le_rfl (hφP j)
        _ = 2 * ENNReal.ofReal (ε j) := (two_mul _).symm
    have hsum : (∑' j, Pr (bad j)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbad_le)
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun j => (hεpos j).le)
        summable_geometric_two]
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    refine tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun j => dist_nonneg) (hω.mono fun j hj => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)))
    simp only [hbad, Set.mem_ofPred_eq, not_le] at hj
    exact hj.le

end QSSEPtoKPZ
