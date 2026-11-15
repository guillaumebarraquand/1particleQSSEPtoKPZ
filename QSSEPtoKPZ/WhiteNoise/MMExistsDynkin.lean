/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.MMExistsDense

/-!
# Dynkin argument for martingale-measure integrals (task G8b, auxiliary)

For every `A ∈ 𝒫 ⊗ 𝓑(ℝ)` (`𝒫` the predictable σ-algebra of `𝒢`), the field
`(r, x, ω) ↦ 𝟙_A((r⁺, ω), x)` has an integral against `M` (`mmEx_indicator`):
`MeasurableSpace.induction_on_inter` from the rectangles `({0} × A₀) × (l, u]` (zero energy) and
`((i, ∞) × A₀) × (l, u]` (limits of blocks with the smooth bumps `mmExBump`), with complements
(`𝟙_{Aᶜ} = 1 - 𝟙_A`) and disjoint unions (dominated convergence of the partial sums).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {T : ℝ} {𝒢 : Filtration ℝ≥0 mΩ}
  {q : ℝ → ℝ → Ω → ℝ} {M : (ℝ → ℝ) → ℝ → Ω → ℝ}

/-- The indicator field of a `𝒫 ⊗ 𝓑(ℝ)`-set is predictable. -/
theorem mmEx_pred_ind {A : Set ((ℝ≥0 × Ω) × ℝ)}
    (hA : MeasurableSet[(𝒢.predictable).prod (borel ℝ)] A) : MMPred 𝒢 (mmExInd A) := by
  unfold MMPred mmExInd
  have e : (fun p : (ℝ≥0 × Ω) × ℝ =>
      A.indicator (fun _ => (1 : ℝ)) ((((p.1.1 : ℝ)).toNNReal, p.1.2), p.2)) =
      A.indicator (fun _ => (1 : ℝ)) := by
    funext p
    simp only [Real.toNNReal_coe]
  rw [e]
  exact measurable_const.indicator hA

/-- `|x y - x z| ≤ 2` for `|x|, |y|, |z| ≤ 1`. -/
private lemma mmEx_abs_aux {x y z : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |x * y - x * z| ≤ 2 := by
  have h := abs_sub_le y 0 z
  simp only [sub_zero, zero_sub, abs_neg] at h
  calc |x * y - x * z| = |x| * |y - z| := by rw [← mul_sub, abs_mul]
    _ ≤ 1 * 2 := mul_le_mul hx (by linarith) (abs_nonneg _) zero_le_one
    _ = 2 := one_mul 2

section Dynkin

variable [IsProbabilityMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
  (hq0 : ∀ r x ω, 0 ≤ q r x ω)
  (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
  (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
include hT hq hq0 hq1 hM

/-- The constant field `1`. -/
private lemma mmEx_one : MMExIntegrable T 𝒢 q M μ (fun _ _ _ => 1) := by
  obtain ⟨C, -, hC⟩ := isC13_bumpTestRaw 0
  refine (mmEx_block (q := q) (M := M) (μ := μ) hT 0 T.toNNReal zero_le
    (a := fun _ => 1) measurable_const ⟨1, by simp⟩ (hC T)).congr hT hq hq0 hq1 hM
    measurable_const fun r hr x ω => ?_
  simp [hr.1, hr.2, bumpTestRaw]

/-- The generators `((i, ∞) × A₀) × (l, u]`, `A₀ ∈ 𝒢_i`. -/
private lemma mmEx_gen_Ioi (i : ℝ≥0) {A₀ : Set Ω} (hA₀ : MeasurableSet[𝒢 i] A₀) (l u : ℝ)
    (hmeas : MeasurableSet[(𝒢.predictable).prod (borel ℝ)] ((Set.Ioi i ×ˢ A₀) ×ˢ Set.Ioc l u)) :
    MMExIntegrable T 𝒢 q M μ (mmExInd ((Set.Ioi i ×ˢ A₀) ×ˢ Set.Ioc l u)) := by
  classical
  set T' : ℝ≥0 := max i T.toNNReal with hT'
  set a : Ω → ℝ := A₀.indicator (fun _ => (1 : ℝ)) with hadef
  have ha : Measurable[𝒢 i] a := measurable_const.indicator hA₀
  have ha1 : ∀ ω, |a ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A₀ <;> simp [hadef, h]
  have hi1 : ∀ x, |(Set.Ioc l u).indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    by_cases h : x ∈ Set.Ioc l u <;> simp [h]
  set b : ℕ → ℝ → ℝ → Ω → ℝ := fun n r x ω =>
    if (i : ℝ) < r ∧ r ≤ T' then a ω * mmExBump n l u x else 0 with hbdef
  set g : ℝ → ℝ → Ω → ℝ := fun r x ω =>
    if (i : ℝ) < r ∧ r ≤ T' then a ω * (Set.Ioc l u).indicator (fun _ => (1 : ℝ)) x else 0
    with hgdef
  have hb : ∀ n, MMExIntegrable T 𝒢 q M μ (b n) := fun n =>
    mmEx_block hT i T' (le_max_left _ _) ha ⟨1, ha1⟩ (mmExBump_isC13 n l u T).choose_spec
  have hgp : MMPred 𝒢 g := mmEx_block_pred ha (measurable_const.indicator measurableSet_Ioc)
  have hg : MMExIntegrable T 𝒢 q M μ g := by
    refine MMExIntegrable.of_tendsto hT hq hq0 hq1 hM hb hgp
      (mmEx_tendsto_energy hq hq0 hq1 (fun n => (hb n).1) hgp (K := 2) (fun n r x ω => ?_)
        (fun r x ω => ?_))
    · by_cases hc : (i : ℝ) < r ∧ r ≤ T'
      · simp only [hbdef, hgdef, hc, and_self, ↓reduceIte]
        exact mmEx_abs_aux (ha1 ω) (mmExBump_abs_le n l u x) (hi1 x)
      · simp only [hbdef, hgdef, hc, ↓reduceIte, sub_zero, abs_zero]
        norm_num
    · by_cases hc : (i : ℝ) < r ∧ r ≤ T'
      · simp only [hbdef, hgdef, hc, and_self, ↓reduceIte]
        exact (mmExBump_tendsto l u x).const_mul (a ω)
      · simp only [hbdef, hgdef, hc, ↓reduceIte]
        exact tendsto_const_nhds
  refine hg.congr hT hq hq0 hq1 hM (mmEx_pred_ind hmeas) fun r hr x ω => ?_
  have hrT : r ≤ (T' : ℝ) := by
    rw [hT', NNReal.coe_max, Real.coe_toNNReal _ hT]
    exact hr.2.trans (le_max_right _ _)
  have key : ((r.toNNReal, ω), x) ∈ (Set.Ioi i ×ˢ A₀) ×ˢ Set.Ioc l u ↔
      ((i : ℝ) < r ∧ r ≤ T') ∧ ω ∈ A₀ ∧ x ∈ Set.Ioc l u := by
    simp only [Set.mem_prod, Set.mem_Ioi, Real.lt_toNNReal_iff_coe_lt, hrT, and_true, and_assoc]
  simp only [hgdef, mmExInd]
  by_cases h1 : (i : ℝ) < r ∧ r ≤ T'
  · by_cases hω : ω ∈ A₀
    · by_cases hx : x ∈ Set.Ioc l u
      · simp only [h1, and_self, ↓reduceIte]
        rw [Set.indicator_of_mem (key.2 ⟨h1, hω, hx⟩), hadef,
          Set.indicator_of_mem hω, Set.indicator_of_mem hx, one_mul]
      · simp only [h1, and_self, ↓reduceIte]
        rw [Set.indicator_of_notMem (fun h => hx (key.1 h).2.2),
          Set.indicator_of_notMem hx, mul_zero]
    · simp only [h1, and_self, ↓reduceIte]
      rw [Set.indicator_of_notMem (fun h => hω (key.1 h).2.1), hadef,
        Set.indicator_of_notMem hω, zero_mul]
  · simp only [h1, ↓reduceIte]
    rw [Set.indicator_of_notMem (fun h => h1 (key.1 h).1)]

/-- **Dynkin argument**: for every `A ∈ 𝒫 ⊗ 𝓑(ℝ)`, the field `(r, x, ω) ↦ 𝟙_A((r⁺, ω), x)` has
an integral against the martingale measure. -/
theorem mmEx_indicator {A : Set ((ℝ≥0 × Ω) × ℝ)}
    (hA : MeasurableSet[(𝒢.predictable).prod (borel ℝ)] A) :
    MMExIntegrable T 𝒢 q M μ (mmExInd A) := by
  set C : Set (Set (ℝ≥0 × Ω)) := {s | ∃ A, MeasurableSet[𝒢 ⊥] A ∧ s = {⊥} ×ˢ A} ∪
    {s | ∃ i A, MeasurableSet[𝒢 i] A ∧ s = Set.Ioi i ×ˢ A} with hCdef
  set D : Set (Set ℝ) := {S : Set ℝ | ∃ l u, l < u ∧ Set.Ioc l u = S} with hDdef
  have hpiC : IsPiSystem C := by
    rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩) t (⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩) hne
    · exact Or.inl ⟨A ∩ B, hA.inter hB, by rw [Set.prod_inter_prod, Set.inter_self]⟩
    · exfalso
      obtain ⟨⟨x, ω⟩, ⟨hx1, -⟩, hx2, -⟩ := hne
      simp only [Set.mem_singleton_iff] at hx1
      subst hx1
      exact not_lt_bot (show j < ⊥ from hx2)
    · exfalso
      obtain ⟨⟨x, ω⟩, ⟨hx1, -⟩, hx2, -⟩ := hne
      simp only [Set.mem_singleton_iff] at hx2
      subst hx2
      exact not_lt_bot (show i < ⊥ from hx1)
    · refine Or.inr ⟨max i j, A ∩ B, (𝒢.mono (le_max_left i j) _ hA).inter
        (𝒢.mono (le_max_right i j) _ hB), ?_⟩
      rw [Set.prod_inter_prod, Set.Ioi_inter_Ioi]
  have hspC : IsCountablySpanning C := by
    refine ⟨fun k => if k = 0 then {⊥} ×ˢ Set.univ else Set.Ioi ⊥ ×ˢ Set.univ, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact Or.inl ⟨Set.univ, MeasurableSet.univ, rfl⟩
      · exact Or.inr ⟨⊥, Set.univ, MeasurableSet.univ, rfl⟩
    · refine Set.eq_univ_of_forall fun ⟨x, ω⟩ => Set.mem_iUnion.2 ?_
      rcases eq_bot_or_bot_lt x with hx | hx
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simpa using hx⟩
  have hpiD : IsPiSystem D := isPiSystem_Ioc id id
  have hspD : IsCountablySpanning D := by
    refine ⟨fun k => Set.Ioc (-((k : ℝ) + 1)) ((k : ℝ) + 1), fun k => ⟨_, _, by linarith, rfl⟩,
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    refine ⟨k, ?_, ?_⟩ <;> linarith [abs_le.1 (le_refl |x|), neg_abs_le x, le_abs_self x]
  have hgen : (𝒢.predictable).prod (borel ℝ) = MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) C D) := by
    rw [borel_eq_generateFrom_Ioc ℝ]
    exact generateFrom_prod_eq hspC hspD
  refine MeasurableSpace.induction_on_inter (C := fun A _ => MMExIntegrable T 𝒢 q M μ (mmExInd A))
    hgen (hpiC.prod hpiD) ?_ ?_ ?_ ?_ A hA
  · convert mmEx_zero (q := q) (M := M) (μ := μ) hT hq hq0 hq1 hM using 1
    funext r x ω
    simp [mmExInd]
  · intro t ht
    have htm : MeasurableSet[(𝒢.predictable).prod (borel ℝ)] t := by
      rw [hgen]; exact MeasurableSpace.measurableSet_generateFrom ht
    obtain ⟨P, hP, B, ⟨l, u, hlu, rfl⟩, rfl⟩ := ht
    rcases hP with ⟨A₀, hA₀, rfl⟩ | ⟨i, A₀, hA₀, rfl⟩
    · refine (mmEx_zero (q := q) (M := M) (μ := μ) hT hq hq0 hq1 hM).congr hT hq hq0 hq1 hM
        (mmEx_pred_ind htm) fun r hr x ω => ?_
      symm
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨⟨h0, -⟩, -⟩
      simp only [Set.mem_singleton_iff, bot_eq_zero', Real.toNNReal_eq_zero] at h0
      linarith [hr.1]
    · exact mmEx_gen_Ioi hT hq hq0 hq1 hM i hA₀ l u htm
  · intro t htm ih
    convert (mmEx_one (q := q) (M := M) (μ := μ) hT hq hq0 hq1 hM).sub ih using 1
    funext r x ω
    simp only [mmExInd]
    by_cases h : ((r.toNNReal, ω), x) ∈ t
    · simp [h]
    · simp [h]
  · intro f hdisj hfm ih
    set S : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun N => ⋃ i ∈ Finset.range N, f i with hSdef
    have hS : ∀ N, MMExIntegrable T 𝒢 q M μ (mmExInd (S N)) := by
      intro N
      induction N with
      | zero =>
        convert mmEx_zero (q := q) (M := M) (μ := μ) hT hq hq0 hq1 hM using 1
        funext r x ω
        simp [mmExInd, hSdef]
      | succ N ihN =>
        have e : S (N + 1) = S N ∪ f N := by
          simp only [hSdef, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
        have hd : Disjoint (S N) (f N) := by
          simp only [hSdef, Set.disjoint_iUnion_left]
          intro i hi
          exact hdisj (by simp at hi; omega : i ≠ N)
        convert ihN.add (ih N) using 1
        funext r x ω
        simp only [mmExInd, e, Set.indicator_union_of_disjoint hd]
    have hUm : MeasurableSet[(𝒢.predictable).prod (borel ℝ)] (⋃ i, f i) := MeasurableSet.iUnion hfm
    have hSm : ∀ N, MeasurableSet[(𝒢.predictable).prod (borel ℝ)] (S N) := fun N =>
      Finset.measurableSet_biUnion _ fun i _ => hfm i
    refine MMExIntegrable.of_tendsto hT hq hq0 hq1 hM hS (mmEx_pred_ind hUm)
      (mmEx_tendsto_energy hq hq0 hq1 (fun N => mmEx_pred_ind (hSm N)) (mmEx_pred_ind hUm)
        (K := 1) (fun N r x ω => ?_) (fun r x ω => ?_))
    · simp only [mmExInd, Set.indicator]
      split_ifs <;> norm_num
    · set z : (ℝ≥0 × Ω) × ℝ := ((r.toNNReal, ω), x)
      simp only [mmExInd]
      by_cases hz : z ∈ ⋃ i, f i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
        rw [Set.indicator_of_mem hz]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop i] with N hN
        rw [Set.indicator_of_mem]
        simp only [hSdef, Set.mem_iUnion, Finset.mem_range, exists_prop]
        exact ⟨i, hN, hi⟩
      · rw [Set.indicator_of_notMem hz]
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
        dsimp only
        rw [Set.indicator_of_notMem]
        simp only [hSdef, Set.mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and]
        exact fun i _ hi => hz (Set.mem_iUnion.2 ⟨i, hi⟩)

end Dynkin

end QSSEPtoKPZ
