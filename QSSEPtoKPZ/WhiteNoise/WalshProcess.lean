/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshExists
public import QSSEPtoKPZ.Martingales.CovariationAlgebra
public import QSSEPtoKPZ.WhiteNoise.WalshCont
public import QSSEPtoKPZ.WhiteNoise.WalshBracket
public import QSSEPtoKPZ.WhiteNoise.WalshPred

/-!
# The Walsh integral as a process (task G9)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G9.
See `docs/stage4-interfaces.md`.

Section 7.2 of the article: "for `h ∈ ℋ_T`, the stochastic integral `∫_0^t ∫ h(s,y) ξ(ds dy)`
is a continuous square-integrable martingale with quadratic variation `∫_0^t ∫ h(s,y)² dy ds`".
Used in Step 2 of the proof of Proposition 7.2 (the part `∫∫ 𝟙_{Z=0} ξ'` of the new noise).

Proofs (task G9): the martingale property and the conditional isometry come from
`WhiteNoise/WalshMart.lean`, the continuous version from `WhiteNoise/WalshCont.lean` (the frozen
`IsWhiteNoise` has no continuity clause: continuity is obtained from Kolmogorov's argument for
`t ↦ ξ((0,t] × (a,b])` and Doob's inequality, `WhiteNoise/WalshBrownian.lean`), the properties of
the bracket `∫_0^t ∫ h h'` from `WhiteNoise/WalshBracket.lean`, and its adaptedness from
`WhiteNoise/WalshPred.lean` (a Walsh integrand is almost everywhere predictable).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω} {T : ℝ}

/-- `𝔼[𝟙_B M_s (N_t - N_s)] = 0` for continuous `L²` martingales `M`, `N` and `B ∈ 𝒢_s`. -/
private lemma walshProc_setIntegral_mul_incr [IsProbabilityMeasure ν] {M N : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓖 M ν) (hN : IsCL2Mart T 𝓖 N ν) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : (t : ℝ) ≤ T) {B : Set Ω} (hB : MeasurableSet[𝓖 s] B) :
    ∫ ω in B, M s ω * (N t ω - N s ω) ∂ν = 0 := by
  have hsT : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hBm : MeasurableSet B := 𝓖.le s B hB
  have hMs : AEStronglyMeasurable[𝓖 s] (M s) ν :=
    ⟨_, stronglyMeasurable_condExp, (hM.condExp s s le_rfl hsT).symm⟩
  set V := B.indicator (M s) with hVdef
  have hV : AEStronglyMeasurable[𝓖 s] V ν := by
    obtain ⟨g, hg, hfg⟩ := hMs
    exact ⟨B.indicator g, hg.indicator hB,
      hfg.mono fun ω hω => by by_cases h : ω ∈ B <;> simp [V, h, hω]⟩
  have hV2 : MemLp V 2 ν := (hM.memLp s hsT).indicator hBm.nullMeasurableSet
  have hD2 : MemLp (fun ω => N t ω - N s ω) 2 ν := (hN.memLp t ht).sub (hN.memLp s hsT)
  have hVD : Integrable (V * fun ω => N t ω - N s ω) ν := hV2.integrable_mul hD2
  have hcD : ν[fun ω => N t ω - N s ω | 𝓖 s] =ᵐ[ν] 0 := by
    refine (condExp_sub ((hN.memLp t ht).integrable one_le_two)
      ((hN.memLp s hsT).integrable one_le_two) _).trans ?_
    filter_upwards [hN.condExp s t hst ht, hN.condExp s s le_rfl hsT] with ω h1 h2
    simp [h1, h2]
  have e : ∫ ω in B, M s ω * (N t ω - N s ω) ∂ν = ∫ ω, (V * fun ω => N t ω - N s ω) ω ∂ν := by
    rw [← integral_indicator hBm]
    congr 1
    funext ω
    by_cases h : ω ∈ B <;> simp [V, h]
  rw [e, ← integral_condExp (𝓖.le s)]
  have h := condExp_mul_of_aestronglyMeasurable_left hV hVD (hD2.integrable one_le_two)
  have h0 : ν[V * fun ω => N t ω - N s ω | 𝓖 s] =ᵐ[ν] 0 := by
    filter_upwards [h, hcD] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  rw [integral_congr_ae h0]
  simp

/-- **Core of the covariation**: for continuous `L²` martingales `X`, `X'` which are Walsh
integral processes of `h`, `h'`, with `∫_0^s ∫ h h'` almost surely `𝒢_s`-measurable,
`⟨X, X'⟩ = ∫_0^· ∫ h h'`. -/
private lemma walshProc_hasCovariation_core (hS : IsWhiteNoise 𝓖 S ν) {h h' : ℝ → ℝ → Ω → ℝ}
    {X X' : ℝ → Ω → ℝ}
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h s y ω else 0) (X t))
    (hX' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h' s y ω else 0) (X' t))
    (hXc : IsCL2Mart T 𝓖 X ν) (hXc' : IsCL2Mart T 𝓖 X' ν)
    (hA : ∀ s : ℝ≥0, (s : ℝ) ≤ T → AEStronglyMeasurable[𝓖 s]
      (fun ω => ∫ r in (0 : ℝ)..s, ∫ y, h r y ω * h' r y ω) ν) :
    HasCovariation T 𝓖 X X' (fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, h s y ω * h' s y ω) ν := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  rcases lt_or_ge T 0 with hT | hT
  · have hI : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.2 hT)
    refine ⟨hXc, hXc', fun t ht => absurd (t.2.trans ht) (not_le.2 hT),
      ae_of_all _ fun ω => by simp, ae_of_all _ fun ω => by rw [hI]; exact continuousOn_empty _,
      ae_of_all _ fun ω => by rw [hI]; exact BoundedVariationOn.of_subsingleton Set.subsingleton_empty,
      fun s t _ ht => absurd (t.2.trans ht) (not_le.2 hT)⟩
  have hg := (IsWalshIntegral.isometry_lib hS (hX T ⟨hT, le_rfl⟩)).1
  have hg' := (IsWalshIntegral.isometry_lib hS (hX' T ⟨hT, le_rfl⟩)).1
  obtain ⟨hae, hint, hset⟩ := walshProc_bracket hg hg'
  refine ⟨hXc, hXc', fun t ht => hint t ⟨t.2, ht⟩, ae_of_all _ fun ω => by simp,
    hae.mono fun ω h => h.1, hae.mono fun ω h => h.2.1, fun s t hst ht => ?_⟩
  have hsT : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  set A : ℝ → Ω → ℝ := fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, h s y ω * h' s y ω with hAdef
  have hmem : ∀ u : ℝ≥0, (u : ℝ) ≤ T → MemLp (X u) 2 ν ∧ MemLp (X' u) 2 ν :=
    fun u hu => ⟨hXc.memLp u hu, hXc'.memLp u hu⟩
  have hint2 : ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      Integrable (fun ω => X u ω * X' u ω - A u ω) ν := fun u hu =>
    ((hmem u hu).1.integrable_mul (hmem u hu).2).sub (hint u ⟨u.2, hu⟩)
  have hXs : AEStronglyMeasurable[𝓖 s] (X s) ν :=
    ⟨_, stronglyMeasurable_condExp, (hXc.condExp s s le_rfl hsT).symm⟩
  have hXs' : AEStronglyMeasurable[𝓖 s] (X' s) ν :=
    ⟨_, stronglyMeasurable_condExp, (hXc'.condExp s s le_rfl hsT).symm⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) (hint2 t ht)
    (fun _ _ _ => (hint2 s hsT).integrableOn) (fun B hB _ => ?_)
    ((hXs.mul hXs').sub (hA s hsT))).symm
  have hBm : MeasurableSet B := 𝓖.le s B hB
  have h1 := walshProc_setIntegral_mul hS hst (hX s ⟨s.2, hsT⟩) (hX t ⟨t.2, ht⟩)
    (hX' s ⟨s.2, hsT⟩) (hX' t ⟨t.2, ht⟩) hB
  have h2 := hset s t s.2 hst' ht B hBm
  have h3 := walshProc_setIntegral_mul_incr hXc hXc' hst ht hB
  have h4 := walshProc_setIntegral_mul_incr hXc' hXc hst ht hB
  have e : ∀ ω, X t ω * X' t ω - A t ω = (X s ω * X' s ω - A s ω) +
      ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω)) +
      X s ω * (X' t ω - X' s ω) + X' s ω * (X t ω - X s ω) := fun ω => by ring
  simp_rw [e]
  have i1 : IntegrableOn (fun ω => X s ω * X' s ω - A s ω) B ν := (hint2 s hsT).integrableOn
  have i2 : IntegrableOn (fun ω => (X t ω - X s ω) * (X' t ω - X' s ω)) B ν :=
    (((hmem t ht).1.sub (hmem s hsT).1).integrable_mul
      ((hmem t ht).2.sub (hmem s hsT).2)).integrableOn
  have i3 : IntegrableOn (fun ω => A t ω - A s ω) B ν :=
    ((hint t ⟨t.2, ht⟩).sub (hint s ⟨s.2, hsT⟩)).integrableOn
  have i4 : IntegrableOn (fun ω => X s ω * (X' t ω - X' s ω)) B ν :=
    ((hmem s hsT).1.integrable_mul ((hmem t ht).2.sub (hmem s hsT).2)).integrableOn
  have i5 : IntegrableOn (fun ω => X' s ω * (X t ω - X s ω)) B ν :=
    ((hmem s hsT).2.integrable_mul ((hmem t ht).1.sub (hmem s hsT).1)).integrableOn
  have j1 : ∫ ω in B, ((X s ω * X' s ω - A s ω) +
      ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω)) +
      X s ω * (X' t ω - X' s ω) + X' s ω * (X t ω - X s ω)) ∂ν =
      ∫ ω in B, ((X s ω * X' s ω - A s ω) +
        ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω)) +
        X s ω * (X' t ω - X' s ω)) ∂ν + ∫ ω in B, X' s ω * (X t ω - X s ω) ∂ν :=
    integral_add ((i1.add (i2.sub i3)).add i4) i5
  have j2 : ∫ ω in B, ((X s ω * X' s ω - A s ω) +
      ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω)) +
      X s ω * (X' t ω - X' s ω)) ∂ν =
      ∫ ω in B, ((X s ω * X' s ω - A s ω) +
        ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω))) ∂ν +
        ∫ ω in B, X s ω * (X' t ω - X' s ω) ∂ν :=
    integral_add (i1.add (i2.sub i3)) i4
  have j3 : ∫ ω in B, ((X s ω * X' s ω - A s ω) +
      ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω))) ∂ν =
      ∫ ω in B, (X s ω * X' s ω - A s ω) ∂ν +
        ∫ ω in B, ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω)) ∂ν :=
    integral_add i1 (i2.sub i3)
  have j4 : ∫ ω in B, ((X t ω - X s ω) * (X' t ω - X' s ω) - (A t ω - A s ω)) ∂ν =
      ∫ ω in B, (X t ω - X s ω) * (X' t ω - X' s ω) ∂ν - ∫ ω in B, (A t ω - A s ω) ∂ν :=
    integral_sub i2 i3
  rw [j1, j2, j3, j4, h3, h4, h1]
  simp only [hAdef] at h2 ⊢
  rw [h2]
  ring

/-- **The Walsh integral process**: for a predictable field `h` with `𝔼 ∫_0^T ∫ h² < ∞`, the
integrals `X_t = ∫_0^t ∫ h dξ`, `t ∈ [0,T]`, have a version which is a continuous
square-integrable martingale with bracket `∫_0^t ∫ h²`. -/
theorem exists_walshProcess (hS : IsWhiteNoise 𝓖 S ν) (hT : 0 ≤ T) {h : ℝ → ℝ → Ω → ℝ}
    (hp : Measurable[(𝓖.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2)
    (h2 : ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ y, ENNReal.ofReal (h s y ω ^ 2)) ∂ν < ⊤) :
    ∃ X : ℝ → Ω → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h s y ω else 0) (X t)) ∧
      HasBracket T 𝓖 X (fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, h s y ω ^ 2) ν := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  -- measurability of the truncated fields
  have hpred_le : 𝓖.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro - (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
    · exact (measurableSet_singleton _).prod (𝓖.le _ _ hA)
    · exact measurableSet_Ioi.prod (𝓖.le _ _ hA)
  have hpm : Measurable[inferInstance, (𝓖.predictable).prod (borel ℝ)]
      (fun p : Ω × ℝ × ℝ => ((p.2.1.toNNReal, p.1), p.2.2)) := by
    have h : Measurable (fun p : Ω × ℝ × ℝ => ((p.2.1.toNNReal, p.1), p.2.2)) := by fun_prop
    refine h.mono le_rfl ?_
    exact sup_le_sup (MeasurableSpace.comap_mono hpred_le)
      (MeasurableSpace.comap_mono BorelSpace.measurable_eq.ge)
  have htp : ∀ t : ℝ, 0 ≤ t → Measurable[(𝓖.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => (if 0 < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) ≤ t then h p.1.1 p.2 p.1.2
        else 0) := by
    intro t ht
    refine Measurable.ite ?_ hp measurable_const
    have e : {p : (ℝ≥0 × Ω) × ℝ | 0 < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) ≤ t} =
        Prod.fst ⁻¹' (Set.Ioc 0 t.toNNReal ×ˢ Set.univ) := by
      ext p
      simp [Real.le_toNNReal_iff_coe_le ht]
    rw [e]
    exact (@measurable_fst _ _ 𝓖.predictable (borel ℝ))
      (measurableSet_predictable_Ioc_prod 0 _ MeasurableSet.univ)
  have hue : ∀ t : ℝ, uncurryField (fun r y ω => if 0 < r ∧ r ≤ t then h r y ω else 0) =
      (fun q : (ℝ≥0 × Ω) × ℝ => if 0 < (q.1.1 : ℝ) ∧ (q.1.1 : ℝ) ≤ t then h q.1.1 q.2 q.1.2
        else 0) ∘ (fun p : Ω × ℝ × ℝ => ((p.2.1.toNNReal, p.1), p.2.2)) := by
    intro t
    funext p
    simp only [uncurryField, Function.comp]
    by_cases hr : 0 < p.2.1
    · rw [Real.coe_toNNReal _ hr.le]
    · simp [hr]
  have hum : ∀ t : ℝ, 0 ≤ t →
      Measurable (uncurryField (fun r y ω => if 0 < r ∧ r ≤ t then h r y ω else 0)) := by
    intro t ht
    rw [hue t]
    exact (htp t ht).comp hpm
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) T,
      MemLp (uncurryField (fun r y ω => if 0 < r ∧ r ≤ t then h r y ω else 0)) 2
        (ν.prod volume) := by
    intro t ht
    have hm := hum t ht.1
    rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
    refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg _)]
    refine lt_of_le_of_lt ?_ h2
    rw [lintegral_prod _ (hm.pow_const 2).ennreal_ofReal.aemeasurable]
    refine lintegral_mono fun ω => ?_
    have hsec : Measurable fun q : ℝ × ℝ => ENNReal.ofReal
        (uncurryField (fun r y ω => if 0 < r ∧ r ≤ t then h r y ω else 0) (ω, q) ^ 2) :=
      ((hm.comp measurable_prodMk_left).pow_const 2).ennreal_ofReal
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      lintegral_prod _ hsec.aemeasurable, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_mono fun r => ?_
    simp only [uncurryField]
    by_cases hr : 0 < r ∧ r ≤ t
    · rw [Set.indicator_of_mem (show r ∈ Set.Icc (0 : ℝ) T from ⟨hr.1.le, hr.2.trans ht.2⟩)]
      simp [hr]
    · simp [hr]
  -- the Walsh integrals and their continuous version
  have hex : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ Z : Ω → ℝ,
      IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h s y ω else 0) Z :=
    fun t ht => exists_isWalshIntegral hS (htp t ht.1)
      (fun s y ω hs => by simp [not_lt.2 hs]) (hmem t ht)
  choose! Z hZ using hex
  obtain ⟨X, hXc, hXe⟩ := walshProc_exists_cont_version hS hT hZ
  have hXw : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h s y ω else 0) (X t) :=
    fun t ht => (hZ t ht).congr_ae hS EventuallyEq.rfl (hXe t ht).symm
  have hXm : IsCL2Mart T 𝓖 X ν := by
    refine ⟨ae_of_all _ hXc, fun t ht => (IsWalshIntegral.isometry_lib hS
      (hXw t ⟨t.2, ht⟩)).2.1, fun s t hst ht => ?_⟩
    have hsT : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
    exact walshProc_condExp hS hst (hXw s ⟨s.2, hsT⟩) (hXw t ⟨t.2, ht⟩)
  have hcov := walshProc_hasCovariation_core hS hXw hXw hXm hXm fun s _ =>
    (⟨_, walshProc_bracket_stronglyMeasurable hp hp s, EventuallyEq.rfl⟩ :
      AEStronglyMeasurable[𝓖 s] (fun ω => ∫ r in (0 : ℝ)..s, ∫ y, h r y ω * h r y ω) ν)
  have hmono := walshProc_bracket_mono (hmem T ⟨hT, le_rfl⟩)
  have hsq : (fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, h s y ω ^ 2) =
      fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, h s y ω * h s y ω := by
    simp_rw [sq]
  refine ⟨X, hXw, ?_⟩
  rw [hsq]
  exact ⟨hXm, hcov.integrable_cov, hcov.zero, hmono, hcov.cont_cov,
    fun s t hst ht => by simpa only [sq] using hcov.condExp_mul s t hst ht⟩

/-- **Covariation of two Walsh integral processes**: `⟨∫ h dξ, ∫ h' dξ⟩_t = ∫_0^t ∫ h h'`. -/
theorem walshProcess_hasCovariation (hS : IsWhiteNoise 𝓖 S ν) {h h' : ℝ → ℝ → Ω → ℝ}
    {X X' : ℝ → Ω → ℝ}
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h s y ω else 0) (X t))
    (hX' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsWalshIntegral 𝓖 S ν (fun s y ω => if 0 < s ∧ s ≤ t then h' s y ω else 0) (X' t))
    (hXc : IsCL2Mart T 𝓖 X ν) (hXc' : IsCL2Mart T 𝓖 X' ν) :
    HasCovariation T 𝓖 X X' (fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, h s y ω * h' s y ω) ν := by
  refine walshProc_hasCovariation_core hS hX hX' hXc hXc' fun s hs => ?_
  have hT : 0 ≤ T := s.2.trans hs
  obtain ⟨G, hG, hGe⟩ := walshProc_exists_predictable hS (hX T ⟨hT, le_rfl⟩)
  obtain ⟨G', hG', hGe'⟩ := walshProc_exists_predictable hS (hX' T ⟨hT, le_rfl⟩)
  set k : ℝ → ℝ → Ω → ℝ := fun r y ω => G ((r.toNNReal, ω), y) with hk
  set k' : ℝ → ℝ → Ω → ℝ := fun r y ω => G' ((r.toNNReal, ω), y) with hk'
  have hkm : Measurable[(𝓖.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => k p.1.1 p.2 p.1.2 := by
    have : (fun p : (ℝ≥0 × Ω) × ℝ => k p.1.1 p.2 p.1.2) = G := by
      funext p
      simp [hk]
    rw [this]
    exact hG
  have hkm' : Measurable[(𝓖.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => k' p.1.1 p.2 p.1.2 := by
    have : (fun p : (ℝ≥0 × Ω) × ℝ => k' p.1.1 p.2 p.1.2) = G' := by
      funext p
      simp [hk']
    rw [this]
    exact hG'
  refine ⟨_, walshProc_bracket_stronglyMeasurable hkm hkm' s, ?_⟩
  have hsec : ∀ g : ℝ → ℝ → Ω → ℝ, ∀ F : (ℝ≥0 × Ω) × ℝ → ℝ,
      uncurryField (fun r y ω => if 0 < r ∧ r ≤ T then g r y ω else 0) =ᵐ[ν.prod volume]
        (fun p => F ((p.2.1.toNNReal, p.1), p.2.2)) →
      ∀ᵐ ω ∂ν, ∀ᵐ r, ∀ᵐ y, (if 0 < r ∧ r ≤ T then g r y ω else 0) = F ((r.toNNReal, ω), y) := by
    intro g F hgF
    filter_upwards [Measure.ae_ae_of_ae_prod hgF] with ω hω
    exact Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) hω
  filter_upwards [hsec h G hGe, hsec h' G' hGe'] with ω h1 h2
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h1, h2] with r hr hr' hrI
  rw [Set.uIoc_of_le s.coe_nonneg] at hrI
  have hc : 0 < r ∧ r ≤ T := ⟨hrI.1, hrI.2.trans hs⟩
  refine integral_congr_ae ?_
  filter_upwards [hr, hr'] with y hy hy'
  simp only [hc, and_self, ite_true] at hy hy'
  rw [hy, hy']

end QSSEPtoKPZ
