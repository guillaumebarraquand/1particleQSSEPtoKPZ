/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Defs
public import QSSEPtoKPZ.Tightness.FiniteMeasureEmbed
public import QSSEPtoKPZ.Martingales.Defs
public import Mathlib.Probability.Process.Predictable

/-!
# The path space `C([0,T], ℳ₊)`: evaluations, pairings, adaptedness, predictability (task G2)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G2.
See `docs/stage4-design.md`, Sections 1.2 (b) and 3.2, and `docs/stage4-interfaces.md`.

`C([0,T], ℳ₊)` has the compact-open topology and its Borel σ-algebra (Mathlib's instance); by
Stage 3 (`Tightness/FiniteMeasureEmbed.lean`) it is metrizable and second countable, so the
Borel σ-algebra of a product with `ℝ` is the product σ-algebra. `ℳ₊` carries
`borel (FiniteMeasure ℝ)`, never Mathlib's Giry instance.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

/-- On `[0,T]`, `pathAt γ t` is the value of `γ` at `t`. -/
theorem pathAt_of_mem {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : pathAt γ t = γ ⟨t, ht⟩ := by
  simp only [pathAt, ht.1.trans ht.2, ↓reduceDIte, Set.projIcc_of_mem _ ht]

/-- `(γ, t) ↦ γ(t)` is jointly continuous on `C([0,T], ℳ₊) × ℝ`. -/
theorem continuous_pathAt_prod {T : ℝ} :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => pathAt p.1 p.2 := by
  by_cases hT : 0 ≤ T
  · simp only [pathAt, hT, ↓reduceDIte]
    exact continuous_eval.comp
      (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
  · simp only [pathAt, hT, ↓reduceDIte]
    exact continuous_const

/-- `μ ↦ μ(f)` is continuous on `ℳ₊` for `f` bounded and continuous. -/
theorem continuous_pairFM {f : ℝ → ℝ} (hf : Continuous f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    Continuous fun μ : FiniteMeasure ℝ => pairFM μ f := by
  obtain ⟨C, hC⟩ := hb
  exact FiniteMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf C fun x => by
      simpa [Real.norm_eq_abs] using hC x)

/-- The cutoff `x ↦ min 1 (max 0 (|x| - R))`: `0` on `[-R, R]`, `1` outside `(-R-1, R+1)`. -/
private def pathCutoff (R : ℝ) (x : ℝ) : ℝ := min 1 (max 0 (|x| - R))

/-- The cutoff is continuous. -/
private lemma continuous_pathCutoff (R : ℝ) : Continuous (pathCutoff R) := by
  unfold pathCutoff; fun_prop

/-- The cutoff is nonnegative. -/
private lemma pathCutoff_nonneg (R x : ℝ) : 0 ≤ pathCutoff R x :=
  le_min zero_le_one (le_max_left _ _)

/-- The cutoff is at most `1`. -/
private lemma pathCutoff_le_one (R x : ℝ) : pathCutoff R x ≤ 1 := min_le_left _ _

/-- The cutoff vanishes on `[-R, R]`. -/
private lemma pathCutoff_eq_zero {R x : ℝ} (h : |x| ≤ R) : pathCutoff R x = 0 := by
  unfold pathCutoff
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

/-- The cutoff is `1` outside `(-R-1, R+1)`. -/
private lemma pathCutoff_eq_one {R x : ℝ} (h : R + 1 ≤ |x|) : pathCutoff R x = 1 := by
  unfold pathCutoff
  rw [max_eq_right (by linarith)]
  exact min_eq_left (by linarith)

/-- **Weak convergence against locally uniformly converging integrands.** If `μᵢ → μ` weakly in
`ℳ₊`, and `fᵢ` are continuous, uniformly bounded, and converge to the bounded continuous `f`
uniformly on every interval `[-R, R]`, then `∫ fᵢ dμᵢ → ∫ f dμ`. (The masses of `μᵢ` far away are
controlled by the cutoffs `pathCutoff`, whose integrals converge.) -/
private lemma pathFM_tendsto_integral {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs L (𝓝 μ))
    {fs : ι → ℝ → ℝ} (f : ℝ →ᵇ ℝ) {C : ℝ} (hfc : ∀ i, Continuous (fs i))
    (hb : ∀ i x, |fs i x| ≤ C)
    (hu : ∀ R : ℝ, TendstoUniformlyOn fs f L (Set.Icc (-R) R)) :
    Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure ℝ)) L (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  set D : ℝ := |C| + ‖f‖ with hD
  have hD0 : 0 ≤ D := by positivity
  have hgb : ∀ (n : ℕ) (x : ℝ), ‖1 / ((n : ℝ) + 1) + D * pathCutoff n x‖ ≤ 1 + D := by
    intro n x
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h2 := pathCutoff_nonneg n x
    have h3 := pathCutoff_le_one n x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  let g : ℕ → ℝ →ᵇ ℝ := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => 1 / ((n : ℝ) + 1) + D * pathCutoff n x)
    (continuous_const.add (continuous_const.mul (continuous_pathCutoff _))) (1 + D) (hgb n)
  have hg0 : Tendsto (fun n => ∫ x, g n x ∂(μ : Measure ℝ)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := (μ : Measure ℝ))
      (F := fun n x => g n x) (f := fun _ => (0 : ℝ)) (fun _ => 1 + D)
      (fun n => (g n).continuous.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ (hgb n)) (ae_of_all _ fun x => ?_)
    · simpa using h
    have hz : ∀ᶠ n : ℕ in atTop, D * pathCutoff n x = 0 := by
      filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with n hn
      rw [pathCutoff_eq_zero ((Nat.le_ceil _).trans (by exact_mod_cast hn)), mul_zero]
    have := tendsto_one_div_add_atTop_nhds_zero_nat.add
      (tendsto_const_nhds.congr' (EventuallyEq.symm hz))
    rw [add_zero] at this
    exact this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n, ∫ x, g n x ∂(μ : Measure ℝ) < ε / 3 :=
    (hg0.eventually (gt_mem_nhds (by positivity))).exists
  have h1 := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hμ (g n)).eventually
    (gt_mem_nhds hn)
  have h2 := Metric.tendsto_nhds.1 (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hμ f)
    (ε / 3) (by positivity)
  have h3 := Metric.tendstoUniformlyOn_iff.1 (hu ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1))
    (by positivity)
  filter_upwards [h1, h2, h3] with i hi1 hi2 hi3
  have hint : Integrable (fs i) (μs i : Measure ℝ) :=
    Integrable.of_bound (hfc i).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb i x)
  have hpt : ∀ x, ‖fs i x - f x‖ ≤ g n x := by
    intro x
    change _ ≤ 1 / ((n : ℝ) + 1) + D * pathCutoff n x
    have hc0 := pathCutoff_nonneg n x
    by_cases hx : |x| ≤ (n : ℝ) + 1
    · have := hi3 x (abs_le.1 hx)
      rw [dist_comm, dist_eq_norm] at this
      nlinarith
    · rw [pathCutoff_eq_one (by linarith), mul_one]
      have hf := f.norm_coe_le_norm x
      rw [Real.norm_eq_abs] at hf ⊢
      have := hb i x
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      calc |fs i x - f x| ≤ |fs i x| + |f x| := abs_sub _ _
        _ ≤ |C| + ‖f‖ := add_le_add ((hb i x).trans (le_abs_self C)) hf
        _ ≤ _ := by linarith
  have hA : |∫ x, fs i x ∂(μs i : Measure ℝ) - ∫ x, f x ∂(μs i : Measure ℝ)| ≤
      ∫ x, g n x ∂(μs i : Measure ℝ) := by
    rw [← integral_sub hint (f.integrable _)]
    exact norm_integral_le_of_norm_le ((g n).integrable _) (ae_of_all _ hpt)
  rw [Real.dist_eq] at hi2 ⊢
  calc _ ≤ |∫ x, fs i x ∂(μs i : Measure ℝ) - ∫ x, f x ∂(μs i : Measure ℝ)| +
        |∫ x, f x ∂(μs i : Measure ℝ) - ∫ x, f x ∂(μ : Measure ℝ)| := abs_sub_le _ _ _
    _ < ε / 3 + ε / 3 := add_lt_add_of_le_of_lt (hA.trans hi1.le) hi2
    _ < ε := by linarith

/-- `(γ, t) ↦ γ(t)(φ_t)` is continuous on `C([0,T], ℳ₊) × [0,T]` when `φ` is continuous and
bounded on `[0,T] × ℝ`. -/
theorem continuousOn_pairFM_pathAt {T : ℝ} {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∃ C, ∀ t ∈ Set.Icc 0 T, ∀ x, |φ t x| ≤ C) :
    ContinuousOn (fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => pairFM (pathAt p.1 p.2)
      (φ p.2)) (Set.univ ×ˢ Set.Icc 0 T) := by
  obtain ⟨C, hC⟩ := hb
  by_cases hT : 0 ≤ T
  swap
  · exact fun p hp => absurd (hp.2.1.trans hp.2.2) hT
  -- extend `φ` continuously to `ℝ × ℝ` through the projection on `[0,T]`
  set ψ : ℝ → ℝ → ℝ := fun t x => φ (Set.projIcc 0 T hT t) x with hψ
  have hψc : Continuous (Function.uncurry ψ) :=
    hφ.comp_continuous (((continuous_subtype_val.comp (continuous_projIcc (h := hT))).comp
      continuous_fst).prodMk continuous_snd) fun p => ⟨(Set.projIcc 0 T hT p.1).2, trivial⟩
  have hψb : ∀ t x, |ψ t x| ≤ C := fun t x => hC _ (Set.projIcc 0 T hT t).2 x
  have hψ_eq : ∀ t ∈ Set.Icc 0 T, ψ t = φ t := fun t ht => by
    funext x; simp [hψ, Set.projIcc_of_mem _ ht]
  let Ψ : C(ℝ × ℝ, ℝ) := ⟨Function.uncurry ψ, hψc⟩
  have key : Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      pairFM (pathAt p.1 p.2) (ψ p.2) := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hcur : Tendsto (fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => Ψ.curry p.2)
        (𝓝 p₀) (𝓝 (Ψ.curry p₀.2)) :=
      (Ψ.curry.continuous.comp continuous_snd).continuousAt
    exact pathFM_tendsto_integral (continuous_pathAt_prod.tendsto p₀)
      (BoundedContinuousFunction.ofNormedAddCommGroup (ψ p₀.2) (Ψ.curry p₀.2).continuous C
        fun x => by simpa [Real.norm_eq_abs] using hψb p₀.2 x)
      (fun p => (Ψ.curry p.2).continuous) (fun p x => hψb p.2 x)
      (fun R => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hcur _
        isCompact_Icc)
  refine key.continuousOn.congr fun p hp => ?_
  simp only [hψ_eq p.2 hp.2]

/-- Adaptedness of the evaluations to the canonical filtration: for `s ≤ t`, `γ ↦ γ(s)` is
measurable from `(C([0,T], ℳ₊), 𝒢_t)` to `(ℳ₊, borel)`. -/
theorem measurable_pathAt_pathFiltrationCan {T : ℝ} {s : ℝ} {t : ℝ≥0} (hst : s ≤ t) :
    @Measurable _ _ (pathFiltrationCan T t) (borel (FiniteMeasure ℝ))
      fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => pathAt γ s := by
  by_cases hT : 0 ≤ T
  · simp only [pathAt, hT, ↓reduceDIte]
    have hs' : ((Set.projIcc 0 T hT s : Set.Icc (0 : ℝ) T) : ℝ) ≤ t := by
      rw [Set.coe_projIcc]
      exact max_le t.2 ((min_le_right _ _).trans hst)
    rw [measurable_iff_comap_le]
    refine le_inf (le_iSup₂_of_le (f := fun (u : Set.Icc (0 : ℝ) T) (_ : (u : ℝ) ≤ t) =>
      (borel (FiniteMeasure ℝ)).comap fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ u)
      _ hs' le_rfl) ?_
    let : MeasurableSpace (FiniteMeasure ℝ) := borel _
    have : BorelSpace (FiniteMeasure ℝ) := ⟨rfl⟩
    exact (continuous_eval_const _).measurable.comap_le
  · simp only [pathAt, hT, ↓reduceDIte]
    exact measurable_const

/-- The canonical filtration is generated by the pairings `γ ↦ γ(s)(f)`, `s ≤ t`, `f` bounded
continuous: a real functional of the path is `𝒢_t`-measurable as soon as it is a measurable
function of finitely many of them (in particular each pairing is `𝒢_t`-measurable). -/
theorem measurable_pairFM_pathFiltrationCan {T : ℝ} {s : ℝ} {t : ℝ≥0} (hst : s ≤ t)
    (f : ℝ →ᵇ ℝ) :
    Measurable[pathFiltrationCan T t]
      fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => pairFM (pathAt γ s) f := by
  let : MeasurableSpace (FiniteMeasure ℝ) := borel _
  have : BorelSpace (FiniteMeasure ℝ) := ⟨rfl⟩
  exact (FiniteMeasure.continuous_integral_boundedContinuousFunction f).measurable.comp
    (measurable_pathAt_pathFiltrationCan hst)

/-! ### Predictability of continuous adapted processes -/

/-- The index `⌈t 2ⁿ⌉₊` of the dyadic interval `((j-1)/2ⁿ, j/2ⁿ]` containing `t > 0` (`0` for
`t = 0`). -/
private def pathPredIdx (n : ℕ) (t : ℝ≥0) : ℕ := ⌈t * 2 ^ n⌉₊

/-- The left end `(j-1)/2ⁿ` of the `j`-th dyadic interval (`0` for `j = 0`). -/
private def pathPredPt (n j : ℕ) : ℝ≥0 := ((j - 1 : ℕ) : ℝ≥0) / 2 ^ n

/-- The left dyadic point of `t` is at most `t`. -/
private lemma pathPredPt_le (n : ℕ) (t : ℝ≥0) : pathPredPt n (pathPredIdx n t) ≤ t := by
  unfold pathPredPt pathPredIdx
  rw [div_le_iff₀ (by positivity)]
  rcases Nat.eq_zero_or_pos ⌈t * 2 ^ n⌉₊ with h | h
  · rw [h]; simp
  · have := (Nat.ceil_eq_iff h.ne').1 rfl
    exact this.1.le

/-- The left dyadic point of `t` is at least `t - 2⁻ⁿ`. -/
private lemma pathPredPt_ge (n : ℕ) (t : ℝ≥0) :
    (t : ℝ) - 1 / 2 ^ n ≤ (pathPredPt n (pathPredIdx n t) : ℝ) := by
  unfold pathPredPt pathPredIdx
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, le_div_iff₀ h2, sub_mul,
    div_mul_cancel₀ _ h2.ne']
  have hc : (t : ℝ) * 2 ^ n ≤ (⌈t * 2 ^ n⌉₊ : ℝ) := by
    have := Nat.le_ceil (t * 2 ^ n)
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos ⌈t * 2 ^ n⌉₊ with h | h
  · rw [h] at hc ⊢; simp only [Nat.cast_zero] at hc; simp; linarith
  · rw [NNReal.coe_natCast, Nat.cast_sub h, Nat.cast_one]
    linarith

/-- The left dyadic points of `t` converge to `t`. -/
private lemma tendsto_pathPredPt (t : ℝ≥0) :
    Tendsto (fun n => pathPredPt n (pathPredIdx n t)) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have h0 : Tendsto (fun n : ℕ => (t : ℝ) - 1 / 2 ^ n) atTop (𝓝 t) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [div_pow] using (tendsto_const_nhds (x := (t : ℝ))).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds
    (fun n => pathPredPt_ge n t) fun n => NNReal.coe_le_coe.2 (pathPredPt_le n t)

/-- The fibre `{t : ⌈t 2ⁿ⌉₊ = j}` (`{0}` or `((j-1)/2ⁿ, j/2ⁿ]`) times a set of
`𝓕_{(j-1)/2ⁿ}` is predictable. -/
private lemma measurableSet_pathPred_fiber {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (n j : ℕ) {A : Set Ω} (hA : MeasurableSet[𝓕 (pathPredPt n j)] A) :
    MeasurableSet[𝓕.predictable] ({t | pathPredIdx n t = j} ×ˢ A) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have e : {t | pathPredIdx n t = 0} = {⊥} := by
      ext t
      simp only [pathPredIdx, Set.mem_ofPred_eq, Nat.ceil_eq_zero, Set.mem_singleton_iff,
        bot_eq_zero']
      constructor
      · intro h
        exact (mul_eq_zero.1 (le_antisymm h zero_le)).resolve_right (by positivity)
      · rintro rfl; simp
    rw [e]
    refine measurableSet_predictable_singleton_bot_prod ?_
    have : pathPredPt n 0 = ⊥ := by simp [pathPredPt]
    rwa [this] at hA
  · have e : {t | pathPredIdx n t = j} = Set.Ioc (pathPredPt n j) ((j : ℝ≥0) / 2 ^ n) := by
      ext t
      simp only [pathPredIdx, pathPredPt, Set.mem_ofPred_eq, Set.mem_Ioc, Nat.ceil_eq_iff hj.ne',
        div_lt_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n), le_div_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)]
    rw [e]
    exact measurableSet_predictable_Ioc_prod _ _ hA

/-- A real process with continuous paths, adapted to `𝓕`, is predictable (its left dyadic
discretizations are predictable step processes, and converge pointwise). -/
private lemma measurable_predictable_of_continuous_process {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => X t ω)
    (ha : ∀ t, Measurable[𝓕 t] (X t)) :
    Measurable[𝓕.predictable] fun p : ℝ≥0 × Ω => X p.1 p.2 := by
  have hn : ∀ n, Measurable[𝓕.predictable]
      fun p : ℝ≥0 × Ω => X (pathPredPt n (pathPredIdx n p.1)) p.2 := by
    intro n B hB
    have e : (fun p : ℝ≥0 × Ω => X (pathPredPt n (pathPredIdx n p.1)) p.2) ⁻¹' B =
        ⋃ j : ℕ, {t | pathPredIdx n t = j} ×ˢ (X (pathPredPt n j) ⁻¹' B) := by
      ext ⟨t, ω⟩; simp
    rw [e]
    exact MeasurableSet.iUnion fun j => measurableSet_pathPred_fiber n j (ha _ hB)
  exact @measurable_of_tendsto_metrizable _ _ 𝓕.predictable _ _ _ _ _ _ hn
    (tendsto_pi_nhds.2 fun p => ((hc p.2).tendsto p.1).comp (tendsto_pathPredPt p.1))

/-- **Continuous adapted fields are predictable** (generic). If `F(t, x, ω)` is jointly
continuous in `(t, x) ∈ ℝ≥0 × ℝ` for every `ω`, and `F(t, x, ·)` is `𝓕_t`-measurable, then
`((t, ω), x) ↦ F(t, x, ω)` is measurable for the predictable σ-algebra of `𝓕` times the Borel
σ-algebra of `ℝ`. -/
theorem measurable_predictable_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {F : ℝ≥0 → ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun p : ℝ≥0 × ℝ => F p.1 p.2 ω)
    (ha : ∀ t x, Measurable[𝓕 t] (F t x)) :
    Measurable[(𝓕.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => F p.1.1 p.2 p.1.2 := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have h1 : Measurable (Function.uncurry fun (x : ℝ) (p : ℝ≥0 × Ω) => F p.1 x p.2) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun p => (hc p.2).comp (continuous_const.prodMk continuous_id))
      (fun x => measurable_predictable_of_continuous_process
        (fun ω => (hc ω).comp (continuous_id.prodMk continuous_const)) (fun t => ha t x))
  exact h1.comp measurable_swap

/-- The predictable σ-algebra is monotone in the filtration. -/
theorem predictable_mono {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 𝓕' : Filtration ℝ≥0 mΩ}
    (h : 𝓕 ≤ 𝓕') : 𝓕.predictable ≤ 𝓕'.predictable := by
  refine MeasurableSpace.generateFrom_mono ?_
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact Or.inl ⟨A, h ⊥ A hA, rfl⟩
  · exact Or.inr ⟨i, A, h i A hA, rfl⟩

/-- For a measurable `Y`, the natural filtration of `Y` is the inverse image of the canonical
filtration (the intersection with `mΩ` in `pathFiltration` is harmless). -/
theorem pathFiltration_eq_comap {Ω : Type*} {mΩ : MeasurableSpace Ω} {T : ℝ}
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y) (t : ℝ≥0) :
    pathFiltration (mΩ := mΩ) Y t = (pathFiltrationCan T t).comap Y :=
  inf_eq_left.2 ((MeasurableSpace.comap_mono ((pathFiltrationCan T).le t)).trans hY.comap_le)

end QSSEPtoKPZ
