/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Existence
public import QSSEPtoKPZ.WhiteNoise.WalshBrownian
public import QSSEPtoKPZ.WhiteNoise.NoiseLaw
public import QSSEPtoKPZ.WhiteNoise.ProductAux
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Existence of a Brownian family indexed by `ℤ × {0,1}` (task E1a)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proof is task E1a.
`docs/stage5-design.md`, Section 1.2 (h), decision D3‴.

`exists_isBrownianFamily`: on the space of a white noise `ξ` (`exists_isWhiteNoise_lib`), with
the unit intervals `I_{(x,j)} = (2x+j, 2x+j+1]`, `B_{(x,j)}(t)` is the continuous version of
`ξ((0,t] × I_{(x,j)})` (task G9's `walshProc_exists_cont_rect` on `[0,N]` for each `N`, glued),
for the filtration `nullAug ν 𝓖`; Gaussian increments, independence across `(x,j)` (disjoint
space intervals) and independence of the past (`indep_past`, null sets added on both sides).

Proved (task E1a). Let `W_{i,N}` be G9's version on `[0,N]` (continuous on `[0,N]` for every
`ω`, not stated to be measurable). Almost surely `W_{i,N}(q) = ξ((0,q] × I_i)` at all grid
points `q = k/(n+1) ≤ N` (countably many conditions); let `Z` be a *measurable* null set
containing the exceptional set (`toMeasurable`). Off `Z`, `W_{i,N}(u)` is the limit of
`ξ((0,q_n] × I_i)` along the grid approximations `q_n = ⌊(n+1)u⌋/(n+1) ↑ u` (`gridBelow`), so the
versions agree on `[0, min(N,M)]` and `B_i(t) = 𝟙_{Zᶜ} W_{i,⌈t⌉}(t)` is continuous in `t` for
every `ω`, and `𝓖ᵃ_t`-measurable (a pointwise limit of `𝓖_t`-measurable functions times
`𝟙_{Zᶜ}`). `B_i(t) = ξ((0,t] × I_i)` a.s. for each `t`, whence the Gaussian law and the
independence of the increments (`IsWhiteNoise.indep`, finitely many cells of a partition of
`(-K,K]`); the past: the increments are measurable for `σ(ξ) ∨ σ(null sets)`, and
`prodNoise_indep_sup_nullSets` adds the null sets on both sides.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

section Glue

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {S : ℝ → ℝ → Ω → ℝ}

/-- The left end `2x + j` of the unit interval `I_{(x,j)} = (2x+j, 2x+j+1]`. -/
def bmFamilyIdx (i : ℤ × Fin 2) : ℤ := 2 * i.1 + ((i.2 : ℕ) : ℤ)

/-- `(x, j) ↦ 2x + j` is injective. -/
private lemma bmFamilyIdx_injective : Function.Injective bmFamilyIdx := by
  rintro ⟨x, j⟩ ⟨y, k⟩ h
  simp only [bmFamilyIdx] at h
  have hj := j.2
  have hk := k.2
  have h1 : x = y := by omega
  have h2 : (j : ℕ) = k := by omega
  exact Prod.ext h1 (Fin.ext h2)

/-- `ξ((0,u] × I_i)`, with `I_i = (2x+j, 2x+j+1]` for `i = (x, j)`. -/
def bmFamilyRect (S : ℝ → ℝ → Ω → ℝ) (i : ℤ × Fin 2) (u : ℝ) (ω : Ω) : ℝ :=
  rectMass S 0 u (bmFamilyIdx i) ((bmFamilyIdx i : ℝ) + 1) ω

/-- The glued process `B_i(t) = 𝟙_{Zᶜ} W_{i,⌈t⌉}(t)`: `W_{i,⌈t⌉}(t)` off the set `Z`, `0` on `Z`. -/
def bmFamilyGlue (W : ℤ × Fin 2 → ℕ → ℝ → Ω → ℝ) (Z : Set Ω) (i : ℤ × Fin 2) (t : ℝ) (ω : Ω) :
    ℝ :=
  Zᶜ.indicator (fun ω => W i ⌈t⌉₊ t ω) ω

variable {W : ℤ × Fin 2 → ℕ → ℝ → Ω → ℝ} {Z : Set Ω}

/-- Off `Z`, `W_{i,N}(u) = lim_n ξ((0, q_n] × I_i)` for `u ≤ N`, `q_n = gridBelow u n`. -/
private lemma bmFamily_tendsto
    (hWc : ∀ i N ω, ContinuousOn (fun u => W i N u ω) (Set.Icc 0 (N : ℝ)))
    (hgood : ∀ ω ∉ Z, ∀ i (N : ℕ) p, (ratGridPt p : ℝ) ≤ N →
      W i N (ratGridPt p) ω = bmFamilyRect S i (ratGridPt p) ω)
    {ω : Ω} (hω : ω ∉ Z) (i : ℤ × Fin 2) {N : ℕ} {u : ℝ≥0} (hu : (u : ℝ) ≤ N) :
    Tendsto (fun n => bmFamilyRect S i (gridBelow u n) ω) atTop (𝓝 (W i N u ω)) := by
  have hle : ∀ n, ((gridBelow u n : ℝ≥0) : ℝ) ≤ N := fun n =>
    (NNReal.coe_le_coe.2 (gridBelow_le u n)).trans hu
  have heq : ∀ n, bmFamilyRect S i (gridBelow u n) ω = W i N (gridBelow u n) ω := fun n =>
    (hgood ω hω i N _ (hle n)).symm
  simp_rw [heq]
  have hc := (hWc i N ω) (u : ℝ) ⟨u.coe_nonneg, hu⟩
  refine hc.tendsto.comp ?_
  exact tendsto_nhdsWithin_iff.2 ⟨tendsto_gridBelow u,
    Eventually.of_forall fun n => ⟨(gridBelow u n).coe_nonneg, hle n⟩⟩

/-- Off `Z`, the glued process equals `W_{i,N}` on `[0, N]`. -/
private lemma bmFamilyGlue_eq
    (hWc : ∀ i N ω, ContinuousOn (fun u => W i N u ω) (Set.Icc 0 (N : ℝ)))
    (hgood : ∀ ω ∉ Z, ∀ i (N : ℕ) p, (ratGridPt p : ℝ) ≤ N →
      W i N (ratGridPt p) ω = bmFamilyRect S i (ratGridPt p) ω)
    {ω : Ω} (hω : ω ∉ Z) (i : ℤ × Fin 2) {N : ℕ} {u : ℝ≥0} (hu : (u : ℝ) ≤ N) :
    bmFamilyGlue W Z i u ω = W i N u ω := by
  rw [bmFamilyGlue, Set.indicator_of_mem (Set.mem_compl hω)]
  exact tendsto_nhds_unique (bmFamily_tendsto hWc hgood hω i (Nat.le_ceil (u : ℝ)))
    (bmFamily_tendsto hWc hgood hω i hu)

/-- Every path of the glued process is continuous on `[0, ∞)`. -/
private lemma bmFamilyGlue_continuous
    (hWc : ∀ i N ω, ContinuousOn (fun u => W i N u ω) (Set.Icc 0 (N : ℝ)))
    (hgood : ∀ ω ∉ Z, ∀ i (N : ℕ) p, (ratGridPt p : ℝ) ≤ N →
      W i N (ratGridPt p) ω = bmFamilyRect S i (ratGridPt p) ω)
    (i : ℤ × Fin 2) (ω : Ω) : Continuous fun t : ℝ≥0 => bmFamilyGlue W Z i t ω := by
  by_cases hω : ω ∈ Z
  · simp only [bmFamilyGlue, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro t0
  set M : ℕ := ⌈(t0 : ℝ)⌉₊ + 1
  have hlt : t0 < (M : ℝ≥0) := by
    rw [← NNReal.coe_lt_coe]
    push_cast [M]
    linarith [Nat.le_ceil (t0 : ℝ)]
  have hon : ContinuousOn (fun t : ℝ≥0 => bmFamilyGlue W Z i t ω) (Set.Iic (M : ℝ≥0)) := by
    have h1 : ContinuousOn (fun t : ℝ≥0 => W i M t ω) (Set.Iic (M : ℝ≥0)) :=
      (hWc i M ω).comp NNReal.continuous_coe.continuousOn fun t ht =>
        ⟨t.coe_nonneg, by simpa using NNReal.coe_le_coe.2 (Set.mem_Iic.1 ht)⟩
    refine h1.congr fun t ht => ?_
    exact bmFamilyGlue_eq hWc hgood hω i (by simpa using NNReal.coe_le_coe.2 (Set.mem_Iic.1 ht))
  exact hon.continuousAt (Iic_mem_nhds hlt)

/-- The glued process is adapted to any filtration for which `ξ((0,u] × I_i)` is
`𝓕_u`-measurable and which contains `Z`. -/
private lemma bmFamilyGlue_measurable {𝓕 : Filtration ℝ≥0 mΩ}
    (hWc : ∀ i N ω, ContinuousOn (fun u => W i N u ω) (Set.Icc 0 (N : ℝ)))
    (hgood : ∀ ω ∉ Z, ∀ i (N : ℕ) p, (ratGridPt p : ℝ) ≤ N →
      W i N (ratGridPt p) ω = bmFamilyRect S i (ratGridPt p) ω)
    (hR : ∀ i (u : ℝ≥0), Measurable[𝓕 u] (bmFamilyRect S i u))
    (hZ : ∀ t, MeasurableSet[𝓕 t] Z) (i : ℤ × Fin 2) (t : ℝ≥0) :
    Measurable[𝓕 t] (bmFamilyGlue W Z i t) := by
  refine @measurable_of_tendsto_metrizable Ω ℝ (𝓕 t) _ _ _ _
    (fun n => Zᶜ.indicator (bmFamilyRect S i (gridBelow t n))) _ (fun n => ?_) ?_
  · exact ((hR i _).mono (𝓕.mono (gridBelow_le t n)) le_rfl).indicator (hZ t).compl
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ Z
    · simp only [bmFamilyGlue, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
      exact tendsto_const_nhds
    · simp only [Set.indicator_of_mem (Set.mem_compl hω)]
      rw [bmFamilyGlue_eq hWc hgood hω i (Nat.le_ceil (t : ℝ))]
      exact bmFamily_tendsto hWc hgood hω i (Nat.le_ceil (t : ℝ))

/-- For each `t ≥ 0`, `B_i(t) = ξ((0,t] × I_i)` almost surely. -/
private lemma bmFamilyGlue_ae
    (hWae : ∀ i (N : ℕ), ∀ u ∈ Set.Icc (0 : ℝ) N, W i N u =ᵐ[ν] bmFamilyRect S i u)
    (hZ0 : ν Z = 0) (i : ℤ × Fin 2) (t : ℝ≥0) :
    bmFamilyGlue W Z i t =ᵐ[ν] bmFamilyRect S i t := by
  have hZ : ∀ᵐ ω ∂ν, ω ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  filter_upwards [hZ, hWae i ⌈(t : ℝ)⌉₊ t ⟨t.coe_nonneg, Nat.le_ceil _⟩] with ω hω h
  rw [bmFamilyGlue, Set.indicator_of_mem (Set.mem_compl hω)]
  exact h

/-- The masses `ξ((s,t] × I_i)` of the unit intervals `I_i`, `i ∈ ℤ × {0,1}`, are independent
(finitely many of them lie in a partition of some `(-K, K]` into unit intervals). -/
private lemma bmFamily_iIndep {𝓖 : Filtration ℝ≥0 mΩ} (hS : IsWhiteNoise 𝓖 S ν) {s t : ℝ≥0}
    (hst : s ≤ t) :
    iIndepFun (fun (i : ℤ × Fin 2) => rectMass S s t (bmFamilyIdx i) ((bmFamilyIdx i : ℝ) + 1))
      ν := by
  rw [iIndepFun_iff_finset]
  intro F
  set K : ℕ := F.sup (fun i => (bmFamilyIdx i).natAbs) + 1 with hK
  have hbd : ∀ i ∈ F, (bmFamilyIdx i).natAbs < K := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (bmFamilyIdx i).natAbs) hi)
  let a : Fin (2 * K + 1) → ℝ := fun k => ((k : ℕ) : ℝ) - K
  have ha : Monotone a := fun k l hkl => by
    have : ((k : ℕ) : ℝ) ≤ (l : ℕ) := by exact_mod_cast hkl
    simp only [a]
    linarith
  have h := hS.indep s t hst (2 * K) a ha
  let e : F → Fin (2 * K) := fun i =>
    ⟨(bmFamilyIdx i + K).toNat, by have := hbd i i.2; omega⟩
  have he : Function.Injective e := by
    intro i j hij
    have h1 := congrArg Fin.val hij
    simp only [e] at h1
    have := hbd i i.2
    have := hbd j j.2
    exact Subtype.ext (bmFamilyIdx_injective (by omega))
  have h2 := h.precomp he
  convert h2 using 1
  funext i ω
  have hc : (((bmFamilyIdx i + K).toNat : ℕ) : ℝ) = (bmFamilyIdx i : ℝ) + K := by
    have := hbd i i.2
    have h3 : (((bmFamilyIdx i + K).toNat : ℕ) : ℤ) = bmFamilyIdx i + K :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast h3
  simp only [Finset.restrict, a, e, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one,
    hc]
  congr 1 <;> ring

/-- A white noise yields a Brownian family indexed by `ℤ × {0,1}`, for the augmented filtration:
`B_i(t)` is the glued continuous version of `ξ((0,t] × I_i)`. -/
theorem bmFamily_exists_of_isWhiteNoise {𝓖 : Filtration ℝ≥0 mΩ} (hS : IsWhiteNoise 𝓖 S ν) :
    ∃ B : ℤ × Fin 2 → ℝ → Ω → ℝ, IsBrownianFamily (nullAug ν 𝓖) B ν := by
  have hex : ∀ (i : ℤ × Fin 2) (N : ℕ), ∃ W : ℝ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun u => W u ω) (Set.Icc 0 (N : ℝ))) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) N, W u =ᵐ[ν] bmFamilyRect S i u := fun i N =>
    walshProc_exists_cont_rect hS N _ _ (by linarith)
  choose W hWc hWae using hex
  set E : Set Ω := {ω | ¬ ∀ i (N : ℕ) p, (ratGridPt p : ℝ) ≤ N →
    W i N (ratGridPt p) ω = bmFamilyRect S i (ratGridPt p) ω} with hEdef
  have hE : ν E = 0 := by
    refine ae_iff.1 ?_
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro N
    rw [ae_all_iff]; intro p
    by_cases hp : (ratGridPt p : ℝ) ≤ N
    · filter_upwards [hWae i N _ ⟨(ratGridPt p).coe_nonneg, hp⟩] with ω h _
      exact h
    · exact ae_of_all _ fun ω h => absurd h hp
  set Z := toMeasurable ν E with hZdef
  have hZ0 : ν Z = 0 := by rw [hZdef, measure_toMeasurable]; exact hE
  have hZm : MeasurableSet Z := measurableSet_toMeasurable ν E
  have hgood : ∀ ω ∉ Z, ∀ i (N : ℕ) p, (ratGridPt p : ℝ) ≤ N →
      W i N (ratGridPt p) ω = bmFamilyRect S i (ratGridPt p) ω := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable ν E h)
  have hR : ∀ i (u : ℝ≥0), Measurable[nullAug ν 𝓖 u] (bmFamilyRect S i u) := fun i u =>
    (hS.measurable_noiseCoord_le le_rfl _ _).mono (le_nullAug ν 𝓖 u) le_rfl
  have hZt : ∀ t, MeasurableSet[nullAug ν 𝓖 t] Z := fun t =>
    nullSets_le_nullAug t _ (measurableSet_nullSets hZm hZ0)
  have hinc : ∀ i (s t : ℝ≥0), (fun ω => bmFamilyGlue W Z i t ω - bmFamilyGlue W Z i s ω) =ᵐ[ν]
      rectMass S s t (bmFamilyIdx i) ((bmFamilyIdx i : ℝ) + 1) := by
    intro i s t
    filter_upwards [bmFamilyGlue_ae hWae hZ0 i t, bmFamilyGlue_ae hWae hZ0 i s] with ω h1 h2
    rw [h1, h2]
    simp only [bmFamilyRect, rectMass]
    ring
  refine ⟨bmFamilyGlue W Z, ⟨fun i t => bmFamilyGlue_measurable hWc hgood hR hZt i t,
    fun i => ae_of_all _ (bmFamilyGlue_continuous hWc hgood i), fun i => ?_,
    fun i s t hst => ?_, fun s t hst => ?_, fun s t hst => ?_⟩⟩
  · have h0 := bmFamilyGlue_ae hWae hZ0 i 0
    simp only [NNReal.coe_zero] at h0
    filter_upwards [h0] with ω h
    rw [h]
    simp [bmFamilyRect, rectMass]
  · have h := hS.gaussian s t (bmFamilyIdx i) ((bmFamilyIdx i : ℝ) + 1) hst (by linarith)
    rw [show ((bmFamilyIdx i : ℝ) + 1 - bmFamilyIdx i).toNNReal = 1 by simp, mul_one] at h
    exact h.congr (hinc i s t)
  · exact (iIndepFun_congr fun i => (hinc i s t).symm).1 (bmFamily_iIndep hS hst)
  · set M := ⨆ (a : ℝ) (b : ℝ),
      MeasurableSpace.comap (rectMass S s t a b) (inferInstance : MeasurableSpace ℝ) with hMdef
    have hM : M ≤ mΩ := iSup₂_le fun a b => (hS.measurable_rectMass_noise s t a b).comap_le
    have h0 : Indep M (nullAug ν 𝓖 s) ν :=
      prodNoise_indep_sup_nullSets (𝓖.le s) (hS.indep_past s t hst)
    have h1 : Indep (M ⊔ nullSets ν) (nullAug ν 𝓖 s) ν :=
      (prodNoise_indep_sup_nullSets hM h0.symm).symm
    refine indep_of_indep_of_le_left h1 (iSup_le fun i => ?_)
    refine Measurable.comap_le ?_
    intro A hA
    have hmeas : Measurable[mΩ] fun ω => bmFamilyGlue W Z i t ω - bmFamilyGlue W Z i s ω :=
      ((bmFamilyGlue_measurable hWc hgood hR hZt i t).mono ((nullAug ν 𝓖).le t) le_rfl).sub
        ((bmFamilyGlue_measurable hWc hgood hR hZt i s).mono ((nullAug ν 𝓖).le s) le_rfl)
    refine (measurableSet_sup_nullSets_iff hM).2 ⟨hmeas hA,
      rectMass S s t (bmFamilyIdx i) ((bmFamilyIdx i : ℝ) + 1) ⁻¹' A, ?_, ?_⟩
    · exact le_iSup₂ (f := fun (a : ℝ) (b : ℝ) =>
        MeasurableSpace.comap (rectMass S s t a b) (inferInstance : MeasurableSpace ℝ))
        (bmFamilyIdx i : ℝ) ((bmFamilyIdx i : ℝ) + 1) _ ⟨A, hA, rfl⟩
    · filter_upwards [hinc i s t] with ω hω
      simp only [Set.mem_preimage, eq_iff_iff]
      rw [hω]

end Glue

/-- **A Brownian family indexed by `ℤ × {0,1}` exists** (on a probability space in `Type`). -/
theorem exists_isBrownianFamily :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (B : ℤ × Fin 2 → ℝ → Ω → ℝ), IsProbabilityMeasure μ ∧ IsBrownianFamily 𝓕 B μ := by
  obtain ⟨Ω, mΩ, ν, 𝓖, S, hν, hS⟩ := exists_isWhiteNoise_lib
  obtain ⟨B, hB⟩ := bmFamily_exists_of_isWhiteNoise hS
  exact ⟨Ω, mΩ, ν, nullAug ν 𝓖, B, hν, hB⟩

end QSSEPtoKPZ
