/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Martingales on the path space and their transfer (task G2)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G2.
See `docs/stage4-design.md`, Sections 1.2 (b) and 3.2, and `docs/stage4-interfaces.md`.

* `hasBracket_map_iff`, `isCL2Mart_map_iff`: a process which is a functional `m(t, X)` of a
  path-valued random variable `X` is a martingale (with bracket `a(t, X)`) for the natural
  filtration of `X` augmented by the null sets iff `m` is one (with bracket `a`) on the canonical
  space `C([0,T], ℳ₊)` under the law of `X`, for the augmented canonical filtration. Applied
  twice, this transfers martingale properties between two path-valued random variables with the
  same law. The functionals are required to be measurable for `t ∈ [0,T]` (the values outside
  `[0,T]` play no role in `HasBracket T`) and continuous in `t` (and `a` nondecreasing) for
  **every** path, so that the almost sure path properties are events of the path space (modify
  `a` off a measurable set of full measure when needed, then use `HasBracket.congr`).
* `pathCan_condExp_eq_zero`: the martingale property is tested on the products
  `∏ᵢ gᵢ(γ(uᵢ)(fᵢ))`, `uᵢ ≤ s` (the article's random variables `Θ`, Section 7.1).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Conditional expectations under an image measure -/

/-- `𝔼_μ[g ∘ X | X⁻¹ m] = 𝔼_{X_*μ}[g | m] ∘ X` almost surely, for a measurable `X` and a
sub-σ-algebra `m` of the target. -/
private lemma pathMap_condExp_comp {Ω' : Type*} {m m' : MeasurableSpace Ω'} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → Ω'} (hX : Measurable X) (hm : m ≤ m')
    {g : Ω' → ℝ} (hg : AEStronglyMeasurable g (μ.map X)) :
    μ[fun ω => g (X ω) | m.comap X] =ᵐ[μ] fun ω => (μ.map X)[g | m] (X ω) := by
  by_cases hgi : Integrable g (μ.map X)
  swap
  · have : ¬ Integrable (fun ω => g (X ω)) μ := fun h =>
      hgi ((integrable_map_measure hg hX.aemeasurable).2 h)
    rw [condExp_of_not_integrable hgi, condExp_of_not_integrable this]
    rfl
  have hcm : m.comap X ≤ mΩ := (MeasurableSpace.comap_mono hm).trans hX.comap_le
  have hXm : Measurable[m.comap X, m] X := measurable_iff_comap_le.2 le_rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hcm
    ((integrable_map_measure hg hX.aemeasurable).1 hgi) (fun s _ _ => ?_) ?_ ?_).symm
  · exact ((integrable_map_measure (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
      hX.aemeasurable).1 integrable_condExp).integrableOn
  · rintro s ⟨A, hA, rfl⟩ _
    rw [← setIntegral_map (hm A hA) (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
      hX.aemeasurable, setIntegral_condExp hm hgi hA,
      setIntegral_map (hm A hA) hg hX.aemeasurable]
    rfl
  · exact (stronglyMeasurable_condExp.comp_measurable hXm).aestronglyMeasurable

/-- The martingale identity transfers between `X` and the canonical space. -/
private lemma pathMap_condExp_iff {μ : Measure Ω} [IsFiniteMeasure μ] {T : ℝ}
    {X : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hX : Measurable X) (s : ℝ≥0)
    {g h : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ} (hg : Measurable g) (hh : Measurable h) :
    μ[fun ω => g (X ω) | pathFiltration (mΩ := mΩ) X s] =ᵐ[μ] (fun ω => h (X ω)) ↔
      (μ.map X)[g | pathFiltrationCan T s] =ᵐ[μ.map X] h := by
  rw [pathFiltration_eq_comap hX]
  have e := pathMap_condExp_comp hX ((pathFiltrationCan T).le s) hg.aestronglyMeasurable
    (μ := μ)
  have hmeas : MeasurableSet {γ | (μ.map X)[g | pathFiltrationCan T s] γ = h γ} :=
    measurableSet_eq_fun ((stronglyMeasurable_condExp.mono
      ((pathFiltrationCan T).le s)).measurable) hh
  simp only [EventuallyEq]
  rw [ae_map_iff hX.aemeasurable hmeas]
  exact ⟨fun h1 => e.symm.trans h1, fun h2 => e.trans h2⟩

/-- Measurability of `f t` at the times `t ∈ ℝ≥0` with `t ≤ T`. -/
private lemma pathMart_measurable {T : ℝ} {f : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (f t)) {t : ℝ≥0} (ht : (t : ℝ) ≤ T) :
    Measurable (f t) :=
  hf t ⟨t.2, ht⟩

/-- `f 0` is measurable (if `T < 0`, the path space is a singleton). -/
private lemma pathMart_measurable_zero {T : ℝ} {f : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (f t)) : Measurable (f 0) := by
  by_cases hT : 0 ≤ T
  · exact hf 0 ⟨le_rfl, hT⟩
  · have : Subsingleton C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
      ⟨fun γ γ' => ContinuousMap.ext fun x => absurd (x.2.1.trans x.2.2) hT⟩
    exact Subsingleton.measurable

/-- The transfer for `IsCL2Mart`, without the null sets. -/
private lemma pathMart_isCL2Mart_iff {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℝ}
    {X : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hX : Measurable X)
    {m : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (m t))
    (hmc : ∀ γ, ContinuousOn (fun t => m t γ) (Set.Icc 0 T)) :
    IsCL2Mart T (pathFiltration X) (fun t ω => m t (X ω)) μ ↔
      IsCL2Mart T (pathFiltrationCan T) m (μ.map X) := by
  constructor
  · intro h
    exact ⟨ae_of_all _ hmc, fun t ht => (memLp_map_measure_iff
      (pathMart_measurable hm ht).aestronglyMeasurable hX.aemeasurable).2 (h.memLp t ht),
      fun s t hst ht => (pathMap_condExp_iff hX s (pathMart_measurable hm ht)
        (pathMart_measurable hm ((NNReal.coe_le_coe.2 hst).trans ht))).1 (h.condExp s t hst ht)⟩
  · intro h
    exact ⟨ae_of_all _ fun ω => hmc (X ω), fun t ht => (memLp_map_measure_iff
      (pathMart_measurable hm ht).aestronglyMeasurable hX.aemeasurable).1 (h.memLp t ht),
      fun s t hst ht => (pathMap_condExp_iff hX s (pathMart_measurable hm ht)
        (pathMart_measurable hm ((NNReal.coe_le_coe.2 hst).trans ht))).2 (h.condExp s t hst ht)⟩

/-- **Transfer of a bracket to the canonical space.** -/
theorem hasBracket_map_iff {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℝ}
    {X : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hX : Measurable X)
    {m a : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (m t))
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (a t))
    (hmc : ∀ γ, ContinuousOn (fun t => m t γ) (Set.Icc 0 T))
    (hac : ∀ γ, ContinuousOn (fun t => a t γ) (Set.Icc 0 T))
    (ham : ∀ γ, MonotoneOn (fun t => a t γ) (Set.Icc 0 T)) :
    HasBracket T (nullAug μ (pathFiltration X)) (fun t ω => m t (X ω)) (fun t ω => a t (X ω)) μ ↔
      HasBracket T (nullAug (μ.map X) (pathFiltrationCan T)) m a (μ.map X) := by
  rw [hasBracket_nullAug_iff, hasBracket_nullAug_iff]
  have hsq : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable fun γ => m t γ ^ 2 - a t γ := fun t ht =>
    ((pathMart_measurable hm ht).pow_const 2).sub (pathMart_measurable ha ht)
  have hzero : MeasurableSet {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) | a 0 γ = 0} :=
    measurableSet_eq_fun (pathMart_measurable_zero ha) measurable_const
  constructor
  · intro h
    exact { toIsCL2Mart := (pathMart_isCL2Mart_iff hX hm hmc).1 h.toIsCL2Mart
            integrable_bracket := fun t ht => (integrable_map_measure
              (pathMart_measurable ha ht).aestronglyMeasurable hX.aemeasurable).2
              (h.integrable_bracket t ht)
            zero := (ae_map_iff hX.aemeasurable hzero).2 h.zero
            mono := ae_of_all _ ham
            cont_bracket := ae_of_all _ hac
            condExp_sq := fun s t hst ht => (pathMap_condExp_iff hX s (hsq t ht)
              (hsq s ((NNReal.coe_le_coe.2 hst).trans ht))).1 (h.condExp_sq s t hst ht) }
  · intro h
    exact { toIsCL2Mart := (pathMart_isCL2Mart_iff hX hm hmc).2 h.toIsCL2Mart
            integrable_bracket := fun t ht => (integrable_map_measure
              (pathMart_measurable ha ht).aestronglyMeasurable hX.aemeasurable).1
              (h.integrable_bracket t ht)
            zero := (ae_map_iff hX.aemeasurable hzero).1 h.zero
            mono := ae_of_all _ fun ω => ham (X ω)
            cont_bracket := ae_of_all _ fun ω => hac (X ω)
            condExp_sq := fun s t hst ht => (pathMap_condExp_iff hX s (hsq t ht)
              (hsq s ((NNReal.coe_le_coe.2 hst).trans ht))).2 (h.condExp_sq s t hst ht) }

/-- **Transfer of a martingale to the canonical space.** -/
theorem isCL2Mart_map_iff {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℝ}
    {X : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hX : Measurable X)
    {m : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (m t))
    (hmc : ∀ γ, ContinuousOn (fun t => m t γ) (Set.Icc 0 T)) :
    IsCL2Mart T (nullAug μ (pathFiltration X)) (fun t ω => m t (X ω)) μ ↔
      IsCL2Mart T (nullAug (μ.map X) (pathFiltrationCan T)) m (μ.map X) := by
  rw [isCL2Mart_nullAug_iff, isCL2Mart_nullAug_iff]
  exact pathMart_isCL2Mart_iff hX hm hmc

/-! ### The canonical filtration is generated by finite-dimensional cylinders -/

/-- The cylinder sets `{γ : γ(uᵢ)(fᵢ) < cᵢ, i < k}` with `uᵢ ≤ s`, `fᵢ` bounded continuous. -/
private def pathCylSets (T : ℝ) (s : ℝ≥0) : Set (Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :=
  {A | ∃ (k : ℕ) (u : Fin k → ℝ) (f : Fin k → ℝ →ᵇ ℝ) (c : Fin k → ℝ), (∀ i, u i ≤ s) ∧
    A = {γ | ∀ i, pairFM (pathAt γ (u i)) (f i) < c i}}

/-- The cylinders form a π-system (concatenate the finite families). -/
private lemma isPiSystem_pathCylSets (T : ℝ) (s : ℝ≥0) : IsPiSystem (pathCylSets T s) := by
  rintro _ ⟨k, u, f, c, hu, rfl⟩ _ ⟨k', u', f', c', hu', rfl⟩ -
  refine ⟨k + k', Fin.append u u', Fin.append f f', Fin.append c c', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa [Fin.append_left] using hu i
    · simpa [Fin.append_right] using hu' i
  · ext γ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.forall_fin_add, Fin.append_left,
      Fin.append_right]

/-- The canonical filtration at time `s` is generated by the cylinders `pathCylSets T s`. -/
private lemma pathFiltrationCan_eq_generateFrom (T : ℝ) (s : ℝ≥0) :
    pathFiltrationCan T s = MeasurableSpace.generateFrom (pathCylSets T s) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine inf_le_left.trans (iSup₂_le fun u hu => ?_)
    have hmeas : ∀ j : ℕ, Measurable[MeasurableSpace.generateFrom (pathCylSets T s)]
        fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => ∫ x, bumpTest j x ∂(γ u : Measure ℝ) := by
      intro j
      let _ : MeasurableSpace C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
        MeasurableSpace.generateFrom (pathCylSets T s)
      refine measurable_of_Iio fun c => MeasurableSpace.measurableSet_generateFrom
        ⟨1, fun _ => u, fun _ => bumpTest j, fun _ => c, fun _ => hu, ?_⟩
      ext γ
      simp [pathAt_of_mem γ u.2, pairFM]
    exact measurable_iff_comap_le.1
      ((@measurable_finiteMeasure_iff_tightEmb _ (MeasurableSpace.generateFrom (pathCylSets T s))
        (fun γ => γ u)).2 hmeas)
  · rintro _ ⟨k, u, f, c, hu, rfl⟩
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurable_pairFM_pathFiltrationCan (hu i) (f i) measurableSet_Iio

/-- The ramp `x ↦ max 0 (min 1 ((n+1)(c - x)))`, a continuous approximation of `𝟙_{x < c}`. -/
private def pathRamp (n : ℕ) (c : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (min 1 (((n : ℝ) + 1) * (c - x)))) (by fun_prop) 1 fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _)

/-- The ramp is nonnegative. -/
private lemma pathRamp_nonneg (n : ℕ) (c x : ℝ) : 0 ≤ pathRamp n c x := le_max_left _ _

/-- The ramp is at most `1`. -/
private lemma pathRamp_le_one (n : ℕ) (c x : ℝ) : pathRamp n c x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The ramps converge pointwise to `𝟙_{x < c}`. -/
private lemma tendsto_pathRamp (c x : ℝ) :
    Tendsto (fun n => pathRamp n c x) atTop (𝓝 (if x < c then 1 else 0)) := by
  split_ifs with h
  · obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : 1 ≤ ((n : ℝ) + 1) * (c - x) := by
      have hN' : 1 / ((n : ℝ) + 1) < c - x :=
        lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.succ_le_succ hn)) hN
      rw [div_lt_iff₀ (by positivity)] at hN'
      linarith
    change 1 = max 0 (min 1 (((n : ℝ) + 1) * (c - x)))
    rw [min_eq_left h1, max_eq_right zero_le_one]
  · refine tendsto_const_nhds.congr fun n => ?_
    change 0 = max 0 (min 1 (((n : ℝ) + 1) * (c - x)))
    have : ((n : ℝ) + 1) * (c - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [not_lt.1 h])
    rw [max_eq_left ((min_le_right _ _).trans this)]

/-- **The martingale property tested on functionals of the past** (Section 7.1, the random
variables `Θ`). If `D` is integrable and `𝔼[D ∏ᵢ gᵢ(γ(uᵢ)(fᵢ))] = 0` for all finite families with
`uᵢ ≤ s`, `fᵢ, gᵢ` bounded continuous, then `𝔼[D | 𝒢_s] = 0` for the canonical filtration
augmented by the null sets. -/
theorem pathCan_condExp_eq_zero {T : ℝ} {P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    [IsProbabilityMeasure P] {D : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hD : Integrable D P) {s : ℝ≥0}
    (h : ∀ (k : ℕ) (u : Fin k → ℝ) (f g : Fin k → ℝ →ᵇ ℝ), (∀ i, u i ≤ s) →
      ∫ γ, (∏ i, g i (pairFM (pathAt γ (u i)) (f i))) * D γ ∂P = 0) :
    P[D | nullAug P (pathFiltrationCan T) s] =ᵐ[P] 0 := by
  have hle := (pathFiltrationCan T).le s
  have hpm : ∀ {u : ℝ}, u ≤ s → ∀ f : ℝ →ᵇ ℝ,
      Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => pairFM (pathAt γ u) f :=
    fun hu f => (measurable_pairFM_pathFiltrationCan hu f).mono hle le_rfl
  have hint0 : ∫ γ, D γ ∂P = 0 := by
    simpa using h 0 Fin.elim0 Fin.elim0 Fin.elim0 fun i => i.elim0
  -- the cylinders have zero integral
  have hcyl : ∀ A ∈ pathCylSets T s, ∫ γ in A, D γ ∂P = 0 := by
    rintro _ ⟨k, u, f, c, hu, rfl⟩
    set A := {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) | ∀ i, pairFM (pathAt γ (u i)) (f i) < c i}
    have hA : MeasurableSet A := by
      simp only [A, Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => hpm (hu i) (f i) measurableSet_Iio
    rw [← integral_indicator hA]
    have hlim : Tendsto (fun n => ∫ γ, (∏ i, pathRamp n (c i) (pairFM (pathAt γ (u i)) (f i))) *
        D γ ∂P) atTop (𝓝 (∫ γ, A.indicator D γ ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun γ => ‖D γ‖) (fun n => ?_) hD.norm
        (fun n => ae_of_all _ fun γ => ?_) (ae_of_all _ fun γ => ?_)
      · exact (Finset.measurable_prod _ fun i _ => (pathRamp n (c i)).continuous.measurable.comp
          (hpm (hu i) (f i))).aestronglyMeasurable.mul hD.1
      · rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => pathRamp_nonneg _ _ _)]
        exact Finset.prod_le_one₀ (fun i _ => pathRamp_nonneg _ _ _)
          fun i _ => pathRamp_le_one _ _ _
      · have := (tendsto_finsetProd Finset.univ fun i _ =>
          tendsto_pathRamp (c i) (pairFM (pathAt γ (u i)) (f i))).mul_const (D γ)
        convert this using 2
        by_cases hγ : γ ∈ A
        · rw [Set.indicator_of_mem hγ, Finset.prod_eq_one fun i _ => by simp [hγ i], one_mul]
        · rw [Set.indicator_of_notMem hγ]
          simp only [A, Set.mem_ofPred_eq, not_forall, not_lt] at hγ
          obtain ⟨i, hi⟩ := hγ
          rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [not_lt.2 hi]), zero_mul]
    exact tendsto_nhds_unique hlim (by simp only [h _ u _ _ hu, tendsto_const_nhds])
  -- by the π-λ theorem, all sets of `𝒢_s` have zero integral
  have hall : ∀ A, MeasurableSet[pathFiltrationCan T s] A → ∫ γ in A, D γ ∂P = 0 := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter
      (pathFiltrationCan_eq_generateFrom T s) (isPiSystem_pathCylSets T s) with
    | empty => simp
    | basic A hA => exact hcyl A hA
    | compl A hA ih => rw [setIntegral_compl (hle A hA) hD, ih, hint0, sub_zero]
    | iUnion F hdis hF ih =>
      rw [integral_iUnion (fun i => hle _ (hF i)) hdis hD.integrableOn]
      simp [ih]
  refine (condExp_nullAug (𝓕 := pathFiltrationCan T) D s).trans
    (ae_eq_condExp_of_forall_setIntegral_eq hle hD (fun _ _ _ => integrableOn_zero)
      (fun A hA _ => ?_) aestronglyMeasurable_zero).symm
  rw [hall A hA]
  simp

end QSSEPtoKPZ
