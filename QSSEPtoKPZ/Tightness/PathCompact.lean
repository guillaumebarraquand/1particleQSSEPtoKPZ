/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.Tightness.FiniteMeasureEmbed
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact sets of paths: `C([0,T], ℳ₊(ℝ))` and `C([0,T], ℝ)` (task H4)

INTERFACE FILE (task I0' of Stage 3): the statements below are interfaces, proved by task H4.
See `docs/stage3-design.md`, Sections 1.2 (a), (e) and 2.4, and `docs/stage3-interfaces.md`.

* `pathCptTest j γ`: the real path `t ↦ ∫ f_j dγ(t)` of a path `γ` in `ℳ₊(ℝ)`.
* `isCompact_pathCptSet`: a set of paths `γ ∈ C([0,T], ℳ₊)` that take their values in a fixed
  compact set `K₀ ⊆ ℳ₊` and whose test paths `t ↦ ∫ f_j dγ(t)` lie in fixed compact sets
  `C_j ⊆ C([0,T], ℝ)` is compact. (Proof: through the embedding `tightEmb` of task H2,
  `C([0,T], ℳ₊)` embeds in `C([0,T], ℝ^ℕ) ≅ ∏_j C([0,T], ℝ)`; Tychonoff.)
* `isCompact_pathCptModulus`: the real paths bounded by `M` with a prescribed modulus of
  continuity (`|g(s) - g(t)| ≤ 1/(m+1)` when `|s - t| ≤ δ_m`, for all `m`) form a compact set
  (Arzelà–Ascoli).

`C(Set.Icc 0 T, ·)` carries the compact-open topology, which is the topology of uniform
convergence since `[0,T]` is compact. For `T < 0`, `[0,T]` is empty and all these sets are
compact trivially.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction UniformConvergence

noncomputable section

namespace QSSEPtoKPZ

/-- The real test path `t ↦ ∫ f_j dγ(t)` of a path `γ ∈ C([0,T], ℳ₊(ℝ))` (continuous since
`μ ↦ ∫ f_j dμ` is continuous for the weak topology). -/
def pathCptTest {T : ℝ} (j : ℕ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    C(Set.Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => ∫ x, bumpTest j x ∂(γ t : Measure ℝ),
    (FiniteMeasure.continuous_integral_boundedContinuousFunction (bumpTest j)).comp γ.continuous⟩

/-- `pathCptTest j γ t = ∫ f_j dγ(t)`. **(proved)** -/
@[simp] theorem pathCptTest_apply {T : ℝ} (j : ℕ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (t : Set.Icc (0 : ℝ) T) : pathCptTest j γ t = ∫ x, bumpTest j x ∂(γ t : Measure ℝ) := rfl

/-- The set of paths with values in `K₀` whose `j`-th test path lies in `C j` for every `j`. -/
def pathCptSet {T : ℝ} (K₀ : Set (FiniteMeasure ℝ)) (C : ℕ → Set C(Set.Icc (0 : ℝ) T, ℝ)) :
    Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  {γ | (∀ t, γ t ∈ K₀) ∧ ∀ j, pathCptTest j γ ∈ C j}

/-- **Compact sets of `C([0,T], ℳ₊(ℝ))`**: compact containment in `K₀` plus compactness of each
family of test paths. **(proved)** Proof: `γ ↦ (j ↦ ∫ f_j dγ(·))` is an inducing map into
`∏_j ([0,T] →ᵤ ℝ)` (`isInducing_postcomp` with `isEmbedding_tightEmb`, then
`UniformFun.uniformEquivPiComm`); the target set is compact (Tychonoff and closedness of
`{η | ∀ t, (η_j(t))_j ∈ tightEmb(K₀)}`) and lies in the range. -/
theorem isCompact_pathCptSet {T : ℝ} {K₀ : Set (FiniteMeasure ℝ)} (hK₀ : IsCompact K₀)
    {C : ℕ → Set C(Set.Icc (0 : ℝ) T, ℝ)} (hC : ∀ j, IsCompact (C j)) :
    IsCompact (pathCptSet K₀ C) := by
  -- `E = tightEmb` as a bundled continuous map, and `e : C(I, ℝ^ℕ) → ∏_j (I →ᵤ ℝ)`
  let E : C(FiniteMeasure ℝ, ℕ → ℝ) := ⟨tightEmb, isEmbedding_tightEmb.continuous⟩
  let e : C(Set.Icc (0 : ℝ) T, ℕ → ℝ) → (ℕ → Set.Icc (0 : ℝ) T →ᵤ ℝ) :=
    fun g => UniformFun.uniformEquivPiComm _ _ (UniformFun.ofFun g)
  have he : IsInducing e :=
    (UniformFun.uniformEquivPiComm _ _).isUniformEmbedding.isUniformInducing.isInducing.comp
      ContinuousMap.isUniformEmbedding_uniformFunOfFun.isUniformInducing.isInducing
  -- `Φ γ = (j ↦ t ↦ ∫ f_j dγ(t))` is a topological inducing map
  let Φ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → (ℕ → Set.Icc (0 : ℝ) T →ᵤ ℝ) :=
    fun γ => e (E.comp γ)
  have hΦ : IsInducing Φ :=
    he.comp (ContinuousMap.isInducing_postcomp E isEmbedding_tightEmb.isInducing)
  let ι : C(Set.Icc (0 : ℝ) T, ℝ) → (Set.Icc (0 : ℝ) T →ᵤ ℝ) := fun g => UniformFun.ofFun g
  have hι : IsUniformEmbedding ι := ContinuousMap.isUniformEmbedding_uniformFunOfFun
  have hΦι : ∀ γ j, Φ γ j = ι (pathCptTest j γ) := fun _ _ => rfl
  have hev : ∀ t : Set.Icc (0 : ℝ) T,
      Continuous fun g : Set.Icc (0 : ℝ) T →ᵤ ℝ => UniformFun.toFun g t :=
    fun t => (UniformFun.uniformContinuous_eval ℝ t).continuous
  -- the compact set `S` of `∏_j (I →ᵤ ℝ)` whose preimage is `pathCptSet K₀ C`
  let S : Set (ℕ → Set.Icc (0 : ℝ) T →ᵤ ℝ) :=
    (Set.univ.pi fun j => ι '' C j) ∩
      {η | ∀ t, (fun j => UniformFun.toFun (η j) t) ∈ tightEmb '' K₀}
  have hS : IsCompact S := by
    refine (isCompact_univ_pi fun j => (hC j).image hι.uniformContinuous.continuous).inter_right ?_
    have hK : IsClosed (tightEmb '' K₀) := (hK₀.image E.continuous).isClosed
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun t =>
      hK.preimage (continuous_pi fun j => (hev t).comp (continuous_apply j))
  have hSΦ : S ⊆ Set.range Φ := by
    rintro η ⟨hη₁, hη₂⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_image] at hη₁
    choose c hcC hc using hη₁
    choose μ hμK hμ using hη₂
    have hcont : Continuous μ := by
      refine isEmbedding_tightEmb.isInducing.continuous_iff.2 ?_
      have : tightEmb ∘ μ = fun t j => c j t := by
        funext t j
        rw [Function.comp_apply, hμ t]
        show UniformFun.toFun (η j) t = c j t
        rw [← hc j]
        rfl
      rw [this]
      exact continuous_pi fun j => (c j).continuous
    refine ⟨⟨μ, hcont⟩, funext fun j => ?_⟩
    rw [hΦι, ← hc j]
    refine congrArg UniformFun.ofFun (funext fun t => ?_)
    show tightEmb (μ t) j = c j t
    rw [hμ t]
    show UniformFun.toFun (η j) t = c j t
    rw [← hc j]
    rfl
  have hpre : pathCptSet K₀ C = Φ ⁻¹' S := by
    ext γ
    simp only [pathCptSet, S, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi,
      Set.mem_univ, true_implies, hΦι, hι.injective.mem_set_image]
    refine and_comm.trans (and_congr Iff.rfl (forall_congr' fun t => ?_))
    exact (isEmbedding_tightEmb.injective.mem_set_image (a := γ t) (s := K₀)).symm
  rw [hpre]
  exact (hΦ.isCompact_preimage_iff hSΦ).2 hS

/-- Real paths on `[0,T]` bounded by `M`, with modulus of continuity `δ`: `|g(s) - g(t)| ≤ 1/(m+1)`
whenever `|s - t| ≤ δ_m`, for every `m ∈ ℕ`. -/
def pathCptModulus (T M : ℝ) (δ : ℕ → ℝ) : Set C(Set.Icc (0 : ℝ) T, ℝ) :=
  {g | (∀ t, |g t| ≤ M) ∧ ∀ m : ℕ, ∀ s t : Set.Icc (0 : ℝ) T,
    |(s : ℝ) - t| ≤ δ m → |g s - g t| ≤ 1 / (m + 1)}

/-- **Arzelà–Ascoli**: bounded paths with a prescribed modulus of continuity (`δ_m > 0`) form a
compact subset of `C([0,T], ℝ)`. **(proved)** Through `ArzelaAscoli.isCompact_of_equicontinuous`:
the set is uniformly equicontinuous, and its image in `ℝ^{[0,T]}` is closed and contained in
`[-M, M]^{[0,T]}`. -/
theorem isCompact_pathCptModulus (T M : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    IsCompact (pathCptModulus T M δ) := by
  -- the same conditions on all functions `[0,T] → ℝ` (product topology)
  let D : Set (Set.Icc (0 : ℝ) T → ℝ) := {g | (∀ t, |g t| ≤ M) ∧ ∀ m : ℕ,
    ∀ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ m → |g s - g t| ≤ 1 / (m + 1)}
  have hD_closed : IsClosed D := by
    simp only [D, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_iInter fun t => isClosed_le (continuous_apply t).abs continuous_const).inter
      (isClosed_iInter fun m => isClosed_iInter fun s => isClosed_iInter fun t => ?_)
    exact isClosed_iInter fun _ => isClosed_le
      (f := fun g : Set.Icc (0 : ℝ) T → ℝ => |g s - g t|) (by fun_prop) continuous_const
  have hD : IsCompact D := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := -M) (b := M)).of_isClosed_subset
      hD_closed fun g hg t _ => ?_
    exact abs_le.1 (hg.1 t)
  -- a function with the modulus of continuity `δ` is continuous
  have himage : ContinuousMap.toFun '' pathCptModulus T M δ = D := by
    ext g
    refine ⟨fun ⟨g', hg', hg⟩ => hg ▸ hg', fun hg => ?_⟩
    refine ⟨⟨g, ?_⟩, hg, rfl⟩
    refine (Metric.uniformContinuous_iff.2 fun ε hε => ?_).continuous
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine ⟨δ m, hδ m, fun {a b} hab => ?_⟩
    rw [Real.dist_eq]
    exact (hg.2 m a b (by rw [Subtype.dist_eq, Real.dist_eq] at hab; exact hab.le)).trans_lt hm
  refine ArzelaAscoli.isCompact_of_equicontinuous _ (himage ▸ hD) ?_
  refine (Metric.uniformEquicontinuous_iff.2 fun ε hε => ?_).equicontinuous
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨δ m, hδ m, fun a b hab g => ?_⟩
  rw [Real.dist_eq]
  exact (g.2.2 m a b (by rw [Subtype.dist_eq, Real.dist_eq] at hab; exact hab.le)).trans_lt hm

end QSSEPtoKPZ
