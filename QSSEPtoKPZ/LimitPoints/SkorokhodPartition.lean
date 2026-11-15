/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Partitions into continuity sets (task G1)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G1.
See `docs/stage4-design.md`, Section 1.2 (a) and 3.2, and `docs/stage4-interfaces.md`.

For a probability measure `P` on a separable metric space and `ε > 0`, there are finitely many
pairwise disjoint Borel sets of diameter `< ε` (balls cut by earlier balls, with radii avoiding
the countably many radii whose spheres carry mass), whose boundaries are `P`-null and which
cover all but `ε` of the mass. This is the first step of the coupling proof of Skorokhod's
representation along a subsequence (`skorokhod_subseq`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- **Partition into `P`-continuity sets of small diameter** (generic). -/
theorem skoro_exists_partition {S : Type*} [MetricSpace S] [TopologicalSpace.SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (P : Measure S) [IsProbabilityMeasure P] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (m : ℕ) (A : Fin m → Set S), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < ε) ∧
      (∀ i, P (frontier (A i)) = 0) ∧
      P (⋃ i, A i)ᶜ ≤ ENNReal.ofReal ε := by
  classical
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := P)
    simp [Set.univ_eq_empty_iff.2 h] at this
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  have hε4 : ε / 4 < ε / 2 := by linarith
  have hr : ∀ n, ∃ r ∈ Set.Ioo (ε / 4) (ε / 2), P (frontier (Metric.ball (u n) r)) = 0 := by
    intro n
    obtain ⟨r, hr, h0⟩ := exists_null_frontier_thickening P {u n} hε4
    exact ⟨r, hr, by rwa [Metric.thickening_singleton] at h0⟩
  choose r hrI hr0 using hr
  set U : ℕ → Set S := fun n => Metric.ball (u n) (r n) with hU
  have hUcov : ∀ x, ∃ n, x ∈ U n := by
    intro x
    obtain ⟨n, hn⟩ := hu.exists_dist_lt x (by linarith : 0 < ε / 4)
    exact ⟨n, by simpa [hU, Metric.mem_ball] using hn.trans (hrI n).1⟩
  have hUm : ∀ n, MeasurableSet (U n) := fun n => Metric.isOpen_ball.measurableSet
  -- the complements of the partial unions decrease to `∅`
  set s : ℕ → Set S := fun N => (⋃ n ∈ Finset.Iic N, U n)ᶜ with hs
  have hs_anti : Antitone s := by
    intro a b hab x hx
    simp only [hs, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx ⊢
    intro n hn
    exact hx n (Finset.mem_Iic.2 ((Finset.mem_Iic.1 hn).trans hab))
  have hs_inter : (⋂ N, s N) = ∅ := by
    ext x
    simp only [hs, Set.mem_iInter, Set.mem_compl_iff, Set.mem_iUnion, not_exists,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    obtain ⟨n, hn⟩ := hUcov x
    exact ⟨n, n, Finset.mem_Iic.2 le_rfl, hn⟩
  have hlim : Tendsto (P ∘ s) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P)
      (fun N =>
        (MeasurableSet.compl (Finset.measurableSet_biUnion _ fun n _ => hUm n)).nullMeasurableSet)
      hs_anti ⟨0, measure_ne_top _ _⟩
    rwa [hs_inter, measure_empty] at this
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 hε)).exists
  refine ⟨N + 1, fun i => disjointed U i, fun i => MeasurableSet.disjointed hUm _, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact disjoint_disjointed U (fun h => hij (Fin.ext h))
  · intro i x hx y hy
    have hx' := disjointed_subset U i hx
    have hy' := disjointed_subset U i hy
    simp only [hU, Metric.mem_ball] at hx' hy'
    calc dist x y ≤ dist x (u i) + dist y (u i) := dist_triangle_right _ _ _
      _ < r i + r i := add_lt_add hx' hy'
      _ < ε := by linarith [(hrI i).2]
  · intro i
    refine measure_mono_null ((congrArg frontier (disjointed_eq_inter_compl U i)).subset.trans
      (frontier_inter_subset _ _)) ?_
    refine measure_union_null (measure_mono_null Set.inter_subset_left (hr0 i))
      (measure_mono_null Set.inter_subset_right ?_)
    have heq : (⋂ j < (i : ℕ), (U j)ᶜ) = (⋃ j ∈ Finset.range i, U j)ᶜ := by
      simp [Set.compl_iUnion]
    rw [heq, frontier_compl]
    refine measure_mono_null (Finset.frontier_biUnion_subset _ _) ?_
    exact (measure_biUnion_null_iff (Finset.range (i : ℕ)).countable_toSet).2 fun j _ => hr0 j
  · have heq : (⋃ i : Fin (N + 1), disjointed U i) = ⋃ n ∈ Finset.Iic N, U n := by
      have h1 : (⋃ i : Fin (N + 1), disjointed U i) = ⋃ n ∈ Finset.Iic N, disjointed U n := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_Iic]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, Nat.lt_succ_iff.1 i.2, hi⟩
        · rintro ⟨n, hn, hx⟩
          exact ⟨⟨n, Nat.lt_succ_iff.2 hn⟩, hx⟩
      rw [h1, biUnion_Iic_disjointed, partialSups_eq_biSup]
      ext x
      simp
    rw [heq]
    exact (hN : P (s N) < _).le

end QSSEPtoKPZ
