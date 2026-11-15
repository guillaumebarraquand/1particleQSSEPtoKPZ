/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71
public import QSSEPtoKPZ.WhiteNoise.Prop72
public import QSSEPtoKPZ.Uniqueness.SheVersion
public import QSSEPtoKPZ.Uniqueness.MildSolution
public import QSSEPtoKPZ.Uniqueness.WeakMildBridge
public import QSSEPtoKPZ.Uniqueness.Prop73Aux
public import QSSEPtoKPZ.Tightness.Prop51
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Proof of Theorem 1.2 for `L_n = ∞` (task Q5)

The proofs of the frozen statements `main_theorem_top` and
`IsMildSolution.nonneg_of_isWaveFunction` of `Uniqueness/Theorem12.lean`
(`docs/stage4-design.md`, Section 1.2 (h), last bullet, and the note on Q5).

* `thm12_subseq`: from any sequence of realizations (with `n_k → ∞`) and versions `Zv k` of
  `(𝖹_{n_k}(t))_{t ∈ [0,T]}`, a subsequence converging in distribution to a continuous version
  `𝒵` of `t ↦ sheMeasure Z t` on the given space `Ω'`; and `Z ≥ 0` on `(0,T] × ℝ` a.s. Chain:
  Proposition 5.1 (tightness) and Prokhorov's theorem give a subsequence whose laws converge to a
  law `P`; on the canonical space `(C([0,T], ℳ₊), P)` with `Y = id`, Proposition 7.1, then
  Proposition 7.2 (auxiliary noise: the given `(Ω', S)`), the bridge `isWeakMild_prod_of_eq_7_8`
  and `exists_sheVersion_map_eq` on `C([0,T], ℳ₊) × Ω'` (tightness of `P` by the portmanteau
  inequality for open sets).
* `thm12_main_top`: the statement of `main_theorem_top`. The limit law does not depend on the
  subsequence (two continuous versions of `sheMeasure` agree a.s.), hence the whole sequence of
  tilted versions converges; then `𝒵_n(t) = ϱ_n(t) 𝖹_n(t)` (3.8) with `ϱ_n → 1` uniformly on
  `[0,T]` (3.9), and the continuous map `(γ, c) ↦ (t ↦ c(t) γ(t))` with the continuity of products
  of laws.
* `thm12_nonneg`: the statement of `IsMildSolution.nonneg_of_isWaveFunction`, from
  `thm12_subseq` with a constant sequence of realizations, for every `T ∈ ℕ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- `(γ, c) ↦ (t ↦ c(t) γ(t))`, from `C([0,T], ℳ₊) × C([0,T], ℝ≥0)` to `C([0,T], ℳ₊)`. -/
def thm12Scale {T : ℝ}
    (p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × C(Set.Icc (0 : ℝ) T, ℝ≥0)) :
    C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  ⟨fun t => p.2 t • p.1 t, by fun_prop⟩

/-- `(γ, c) ↦ (t ↦ c(t) γ(t))` is continuous (compact-open topologies). -/
theorem thm12Scale_continuous {T : ℝ} : Continuous (thm12Scale (T := T)) := by
  have h : Continuous fun q : (C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) ×
      C(Set.Icc (0 : ℝ) T, ℝ≥0)) × Set.Icc (0 : ℝ) T => q.1.2 q.2 • q.1.1 q.2 := by fun_prop
  exact (ContinuousMap.curry ⟨_, h⟩).continuous

/-- `t ↦ 1 · γ(t)` is `γ`. -/
private lemma thm12Scale_one {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    thm12Scale (γ, 1) = γ := by
  ext1 t
  simp [thm12Scale]

/-- **Convergence in distribution is preserved by a deterministic rescaling `c_k → 1`**: if
`X_k → Y` in distribution in `C([0,T], ℳ₊)` and `c_k → 1` in `C([0,T], ℝ≥0)` (uniformly), then
`t ↦ c_k(t) X_k(t)` converges in distribution to `Y`. -/
theorem thm12_tendstoInDistribution_scale {T : ℝ} {Ω : ℕ → Type*}
    {mΩ : ∀ k, MeasurableSpace (Ω k)} {μ : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (μ k)]
    {X : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hX : ∀ k, Measurable (X k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Y : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    (h : TendstoInDistribution X atTop Y μ ν)
    {c : ℕ → C(Set.Icc (0 : ℝ) T, ℝ≥0)} (hc : Tendsto c atTop (𝓝 1)) :
    TendstoInDistribution (fun k ω => thm12Scale (X k ω, c k)) atTop Y μ ν := by
  have hG := thm12Scale_continuous (T := T)
  have hXc : ∀ k, Measurable fun ω => (X k ω, c k) := fun k => (hX k).prodMk measurable_const
  refine ⟨fun k => (hG.measurable.comp (hXc k)).aemeasurable, hY.aemeasurable, ?_⟩
  have h1 := (ProbabilityMeasure.continuous_prod.tendsto _).comp
    (h.tendsto.prodMk_nhds ((continuous_diracProba.tendsto 1).comp hc))
  have h2 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h1 hG
  have e1 : ∀ k, (ProbabilityMeasure.prod (⟨(μ k).map (X k), inferInstance⟩ :
        ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
        (diracProba (c k))).map thm12Scale =
      ⟨(μ k).map (fun ω => thm12Scale (X k ω, c k)), inferInstance⟩ := by
    intro k
    apply Subtype.ext
    simp only [diracProba]
    change Measure.map _ (((μ k).map (X k)).prod (Measure.dirac (c k))) = _
    rw [Measure.prod_dirac, Measure.map_map hG.measurable measurable_prodMk_right,
      Measure.map_map (hG.measurable.comp measurable_prodMk_right) (hX k)]
    rfl
  have e2 : (ProbabilityMeasure.prod (⟨ν.map Y, inferInstance⟩ :
        ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
        (diracProba (1 : C(Set.Icc (0 : ℝ) T, ℝ≥0)))).map thm12Scale =
      ⟨ν.map Y, inferInstance⟩ := by
    apply Subtype.ext
    simp only [diracProba]
    change Measure.map _ ((ν.map Y).prod (Measure.dirac 1)) = _
    rw [Measure.prod_dirac, Measure.map_map hG.measurable measurable_prodMk_right,
      Measure.map_map (hG.measurable.comp measurable_prodMk_right) hY]
    congr 1
    funext ω
    exact thm12Scale_one (Y ω)
  exact (e2 ▸ h2).congr e1

/-- **Every sequence of limit points has a subsequence converging to the SHE** (end of
Section 7, for one subsequence): let `n_k → ∞`, `n_k ≥ 1`, for each `k` a realization of the
one-particle QSSEP on `ℤ` and a measurable version `Zv k` of `(𝖹_{n_k}(t))_{t ∈ [0,T]}`; on `Ω'`
a white noise `S` and a solution `Z` of (1.13). Then for some subsequence `σ`, there is a
measurable `𝒵 : Ω' → C([0,T], ℳ₊)`, almost surely equal to `t ↦ sheMeasure Z t` for all
`t ∈ [0,T]`, with `Zv (σ j) → 𝒵` in distribution; and almost surely `Z ≥ 0` on `(0,T] × ℝ`. -/
theorem thm12_subseq {T : ℝ} (hT : 0 < T)
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (Zv : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (hZm : ∀ k, Measurable (Zv k))
    (hZv : ∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
      (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ') (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν) :
    ∃ (σ : ℕ → ℕ) (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)), StrictMono σ ∧
      Measurable 𝒵 ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      (∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → t ≤ T → 0 ≤ Z t x ω) ∧
      TendstoInDistribution (fun j => Zv (σ j)) atTop 𝒵 (fun j => μ (σ j)) ν := by
  -- the laws, tight by Proposition 5.1; Prokhorov and sequential compactness
  let P : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) := fun k =>
    ⟨(μ k).map (Zv k), inferInstance⟩
  have htight := prop_5_1_isTight hT n hn₁ μ 𝓕 B hB ψ hψ Zv (fun k => (hZm k).aemeasurable) hZv
  have hset : {x | ∃ p ∈ Set.range P, (p : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) = x} =
      Set.range fun k => (μ k).map (Zv k) := by
    ext m
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨P k, ⟨k, rfl⟩, rfl⟩
  rw [← hset] at htight
  obtain ⟨Plim, -, σ, hσ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
      (fun k => subset_closure ⟨k, rfl⟩)
  -- the canonical space `(C([0,T], ℳ₊), Plim)` with `Y = id`
  set Pr : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) := Plim.toMeasure with hPr
  have hconv : TendstoInDistribution (fun j => Zv (σ j)) atTop
      (id : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → _) (fun j => μ (σ j)) Pr := by
    refine ⟨fun j => (hZm (σ j)).aemeasurable, measurable_id.aemeasurable, ?_⟩
    have e : (⟨Pr.map id, inferInstance⟩ :
        ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) = Plim :=
      Subtype.ext (by exact Measure.map_id)
    have h := hlim
    rw [← e] at h
    exact h
  -- Proposition 7.1
  obtain ⟨ρ, hρ⟩ := prop73_exists_mollifier
  obtain ⟨hY0, ⟨hpred, hZ0, hZ2, hdens⟩, hmart⟩ :=
    prop_7_1 hρ hT (fun j => n (σ j)) (fun j => hn₁ (σ j)) (hn.comp hσ.tendsto_atTop)
      (fun j => μ (σ j)) (fun j => 𝓕 (σ j)) (fun j => B (σ j)) (fun j => hB (σ j))
      (fun j => ψ (σ j)) (fun j => hψ (σ j)) (fun j => Zv (σ j)) (fun j => hZv (σ j))
      measurable_id hconv
  -- Proposition 7.2, with the given `(Ω', S)` as auxiliary noise
  have hZp : Measurable[((nullAug Pr (pathFiltration (mΩ := borel _)
      (id : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → _))).predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) × ℝ =>
        limField ρ id p.1.1 p.2 p.1.2 :=
    hpred.mono (sup_le_sup_right (MeasurableSpace.comap_mono
      (predictable_mono (le_nullAug _ _))) _) le_rfl
  obtain ⟨𝒢b, S₁, -, hS₁, h78⟩ := prop_7_2 hT measurable_id hY0 hZp hZ0 hZ2 hdens hmart hS
  -- the bridge (7.8) → (7.13) on `C([0,T], ℳ₊) × Ω'`
  have hW := isWeakMild_prod_of_eq_7_8 hT measurable_id (measurable_limDensity_pathAt hρ) hZ0 hZ2
    hdens hS₁ h78
  -- the SHE side: `exists_sheVersion_map_eq` on `Ω₁ = C([0,T], ℳ₊) × Ω'`
  have hfst : MeasurePreserving Prod.fst (Pr.prod ν) Pr := measurePreserving_fst
  have htight₁ : ∀ ε : ℝ, 0 < ε → ∃ K : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ),
      IsCompact K ∧ (Pr.prod ν) ((fun ω => ω.1) ⁻¹' Kᶜ) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨𝒦, h𝒦, hb⟩ := prop_5_1 hT hε
    refine ⟨𝒦, h𝒦, ?_⟩
    have hmeas : MeasurableSet 𝒦ᶜ := h𝒦.isClosed.measurableSet.compl
    rw [show (fun ω : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × Ω' => ω.1) = Prod.fst from rfl,
      hfst.measure_preimage hmeas.nullMeasurableSet]
    refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      h𝒦.isClosed.isOpen_compl).trans ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun j => ?_)
    change (μ (σ j)).map (Zv (σ j)) 𝒦ᶜ ≤ _
    rw [Measure.map_apply (hZm (σ j)) hmeas]
    exact hb (hB (σ j)) (hψ (σ j)) (hn₁ (σ j)) (Zv (σ j)) (hZv (σ j))
  obtain ⟨𝒵, h𝒵m, h𝒵, hmap, hpos⟩ := exists_sheVersion_map_eq hS₁ hT measurable_fst htight₁
    (hfst.quasiMeasurePreserving.ae hY0) hW (fun t x ω => hZ0 t x ω.1)
    (hfst.quasiMeasurePreserving.ae hdens) hS hZ
  refine ⟨σ, 𝒵, hσ, h𝒵m, h𝒵, hpos, fun j => (hZm (σ j)).aemeasurable, h𝒵m.aemeasurable, ?_⟩
  have e : (⟨ν.map 𝒵, inferInstance⟩ :
      ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) = Plim :=
    Subtype.ext (by
      change ν.map 𝒵 = Pr
      rw [hmap]
      exact hfst.map_eq)
  have h := hlim
  rw [← e] at h
  exact h

/-- Two continuous versions of `t ↦ sheMeasure Z t` on `[0,T]` agree almost surely. -/
private lemma thm12_version_ae_eq {T : ℝ} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {ν : Measure Ω'} {Z : ℝ → ℝ → Ω' → ℝ} {𝒵 𝒵' : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (h : ∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
      (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t)
    (h' : ∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
      (𝒵' ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) :
    𝒵' =ᵐ[ν] 𝒵 := by
  filter_upwards [h, h'] with ω hω hω'
  ext1 t
  exact FiniteMeasure.toMeasure_injective ((hω' t).trans (hω t).symm)

/-- `ϱ_{n_k} → 1` uniformly on `[0,T]` when `n_k → ∞` ((3.9)). -/
private lemma thm12_tendsto_varrho {T : ℝ} (hT : 0 ≤ T) (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k)
    (hn : Tendsto n atTop atTop) (c : ℕ → C(Set.Icc (0 : ℝ) T, ℝ≥0))
    (hc : ∀ k t, c k t = (varrhoN (n k) t).toNNReal) :
    Tendsto c atTop (𝓝 1) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : Tendsto (fun k => Real.exp (T * n k ^ (-1 / 2 : ℝ)) - 1) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k => n k ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hn
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
      exact this
    have h1 : Tendsto (fun k => T * n k ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
      simpa using h0.const_mul T
    have := ((Real.continuous_exp.tendsto 0).comp h1).sub_const 1
    simpa using this
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hb
  have hpos : 0 ≤ n k ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans (hn₁ k)) _
  have hb0 : 0 ≤ Real.exp (T * n k ^ (-1 / 2 : ℝ)) - 1 := by
    have := Real.add_one_le_exp (T * n k ^ (-1 / 2 : ℝ))
    nlinarith [mul_nonneg hT hpos]
  refine (ContinuousMap.dist_le hb0).2 fun t => ?_
  obtain ⟨h1, h2⟩ := varrhoN_bounds (hn₁ k) t.2.1
  rw [hc, ContinuousMap.one_apply, NNReal.dist_eq, NNReal.coe_one,
    Real.coe_toNNReal _ (zero_le_one.trans h1), abs_of_nonneg (by linarith)]
  have : Real.exp ((t : ℝ) * n k ^ (-1 / 2 : ℝ)) ≤ Real.exp (T * n k ^ (-1 / 2 : ℝ)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right t.2.2 hpos)
  linarith

/-- **Theorem 1.2 when `L_n = ∞` for all `n`**: the statement of `main_theorem_top`
(`Uniqueness/Theorem12.lean`), proved here. -/
theorem thm12_main_top
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ')
    (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝒵n : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
      (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵n k ω t : Measure ℝ) = rescaledMeasure ⊤ (n k) (density (ψ k) ω) t) ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν := by
  -- versions of `𝖹_{n_k}` (Proposition 5.1)
  have hver := fun k => exists_tiltedPath_version_bcf (hB k) (hψ k) (hn₁ k) T
  choose Zt hZtm _ hZt using hver
  -- one limit point, a version `𝒵` of `t ↦ sheMeasure Z t`
  obtain ⟨-, 𝒵, -, h𝒵m, h𝒵, -, -⟩ :=
    thm12_subseq hT n hn₁ hn μ 𝓕 B hB ψ hψ Zt hZtm hZt ν 𝓖 S hS Z hZ
  -- every subsequence has a further subsequence converging to the law of `𝒵`
  have hconv : TendstoInDistribution Zt atTop 𝒵 μ ν := by
    refine ⟨fun k => (hZtm k).aemeasurable, h𝒵m.aemeasurable, ?_⟩
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨σ, 𝒵', -, -, h𝒵', -, hc'⟩ := thm12_subseq hT (fun k => n (ns k))
      (fun k => hn₁ (ns k)) (hn.comp hns) (fun k => μ (ns k)) (fun k => 𝓕 (ns k))
      (fun k => B (ns k)) (fun k => hB (ns k)) (fun k => ψ (ns k)) (fun k => hψ (ns k))
      (fun k => Zt (ns k)) (fun k => hZtm (ns k)) (fun k => hZt (ns k)) ν 𝓖 S hS Z hZ
    refine ⟨σ, ?_⟩
    have e : (⟨ν.map 𝒵', inferInstance⟩ :
        ProbabilityMeasure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) = ⟨ν.map 𝒵, inferInstance⟩ :=
      Subtype.ext (Measure.map_congr (thm12_version_ae_eq h𝒵 h𝒵'))
    have h := hc'.tendsto
    rw [e] at h
    exact h
  -- `𝒵_n(t) = ϱ_n(t) 𝖹_n(t)` (3.8), with `ϱ_n → 1` uniformly on `[0,T]` (3.9)
  let c : ℕ → C(Set.Icc (0 : ℝ) T, ℝ≥0) := fun k =>
    ⟨fun t => (varrhoN (n k) t).toNNReal, by unfold varrhoN; fun_prop⟩
  have hc : Tendsto c atTop (𝓝 1) := thm12_tendsto_varrho hT.le n hn₁ hn c fun _ _ => rfl
  refine ⟨fun k ω => thm12Scale (Zt k ω, c k), 𝒵, fun k => ?_, h𝒵,
    thm12_tendstoInDistribution_scale hZtm h𝒵m hconv hc⟩
  filter_upwards [hZt k] with ω hω t
  simp only [thm12Scale, ContinuousMap.coe_mk, FiniteMeasure.toMeasure_smul]
  rw [rescaledMeasure_eq (hn₁ k), hω t]
  rfl

/-- **Nonnegativity of the solution of the SHE, conditionally on the existence of the QSSEP on
`ℤ`**: the statement of `IsMildSolution.nonneg_of_isWaveFunction`
(`Uniqueness/Theorem12.lean`), proved here, from `thm12_subseq` with the constant sequence of
realizations `(Ω₀, ψ₀)` and `n_k = k + 1`, on `(0, m + 1]` for every `m ∈ ℕ`. -/
theorem thm12_nonneg
    (hE : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀) (μ₀ : Measure Ω₀)
      (𝓕₀ : Filtration ℝ≥0 m₀) (B₀ : ℤ × Fin 2 → ℝ → Ω₀ → ℝ) (ψ₀ : ℝ → Ω₀ → ℓ²(ℤ, ℂ)),
      IsProbabilityMeasure μ₀ ∧ IsBrownianFamily 𝓕₀ B₀ μ₀ ∧ IsWaveFunction ⊤ 𝓕₀ B₀ ψ₀ μ₀)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → 0 ≤ Z t x ω := by
  obtain ⟨Ω₀, m₀, μ₀, 𝓕₀, B₀, ψ₀, hμ₀, hB₀, hψ₀⟩ := hE
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hn₁ : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := k.cast_nonneg (α := ℝ); linarith
  have hn : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hm : ∀ m : ℕ, ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → t ≤ (m : ℝ) + 1 → 0 ≤ Z t x ω := by
    intro m
    have hT : (0 : ℝ) < (m : ℝ) + 1 := zero_lt_one.trans_le (hn₁ m)
    have hver := fun k : ℕ => prop_5_1_version hB₀ hψ₀ (hn₁ k) ((m : ℝ) + 1)
    choose Zv hZvm hZv using hver
    obtain ⟨-, -, -, -, -, hpos, -⟩ := thm12_subseq hT (fun k : ℕ => (k : ℝ) + 1) hn₁ hn
      (fun _ => μ₀) (fun _ => 𝓕₀) (fun _ => B₀) (fun _ => hB₀) (fun _ => ψ₀) (fun _ => hψ₀)
      Zv hZvm hZv ν 𝓖 S hS Z hZ
    exact hpos
  filter_upwards [ae_all_iff.2 hm] with ω hω t x ht
  obtain ⟨m, hm⟩ := exists_nat_ge t
  exact hω m t x ht (by linarith)

end QSSEPtoKPZ
