/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.HeatKernel
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry

/-!
# A jointly measurable version of a mild solution; centred Walsh integrals (task K2)

* `secondMom_walsh_integral_eq_zero`: a Walsh integral is centred, `𝔼 ∫ h dξ = 0` (elementary
  integrals by `indep_past`, then `L²` limits).
* `secondMom_memLp`: for a mild solution `Z` and `t > 0`, `Z(t,x) ∈ L²(ν)` (from **W**).
* `secondMom_eqOn_of_rat`: two functions continuous on `(0,∞) × ℝ` that agree at the rational
  points agree on `(0,∞) × ℝ`.
* `secondMom_exists_version`: a mild solution has a version `Z'` which is jointly measurable on
  `Ω × ℝ × ℝ`, continuous on `(0,∞) × ℝ` for every `ω`, and again a mild solution. Construction:
  outside a measurable null set `N` (where continuity fails or `Z` differs, at some rational point,
  from a measurable modification), `Z' = Z` on `(0,∞) × ℝ`; `Z' = 0` elsewhere. Joint
  measurability: Carathéodory (`measurable_uncurry_of_continuous_of_measurable`) in the
  coordinates `(log t, x)`; measurability of each `Z'(t,x)` as a pointwise limit along rational
  points.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- **Walsh integrals are centred**: if `X = ∫ h dξ`, then `𝔼 X = 0`. -/
theorem secondMom_walsh_integral_eq_zero (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ}
    {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) : ∫ ω, X ω ∂ν = 0 := by
  have := hS.isProbabilityMeasure
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    have hind : IndepFun c (rectMass S s t a b) ν := by
      rw [IndepFun_iff_Indep]
      exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep_past s t hst)
        (le_iSup₂ (f := fun a b => MeasurableSpace.comap (rectMass S s t a b) inferInstance)
          a b)) hc.comap_le).symm
    rw [hind.integral_fun_mul_eq_mul_integral (hc.mono (𝓖.le s) le_rfl).aestronglyMeasurable
      (hS.gaussian s t a b hst hab).aemeasurable.aestronglyMeasurable,
      (hS.gaussian s t a b hst hab).integral_eq, integral_id_gaussianReal, mul_zero]
  | add h h' X X' hX hX' ih ih' =>
    rw [integral_add ((IsWalshIntegral.isometry_lib hS hX).2.1.integrable one_le_two)
      ((IsWalshIntegral.isometry_lib hS hX').2.1.integrable one_le_two), ih, ih', add_zero]
  | limit h X hs Xs hk hh hX2 _ hlim ih =>
    have hconv := tendsto_integral_of_L1' (μ := ν) X (F := Xs) (l := atTop)
      (Eventually.of_forall fun k =>
        (IsWalshIntegral.isometry_lib hS (hk k)).2.1.integrable one_le_two)
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le)
        (fun k => eLpNorm_le_eLpNorm_of_exponent_le one_le_two))
    simp_rw [ih] at hconv
    exact tendsto_nhds_unique hconv tendsto_const_nhds

/-- For a mild solution and `t > 0`, `Z(t,x) - g_t(x) = ∫ … dξ` is square integrable, hence so
is `Z(t,x)`. -/
theorem secondMom_memLp (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) {t : ℝ} (ht : 0 < t) (x : ℝ) : MemLp (Z t x) 2 ν := by
  have := hS.isProbabilityMeasure
  have h := ((IsWalshIntegral.isometry_lib hS (hZ.mild t x ht)).2.1).add
    (memLp_const (heatKernel t x))
  exact h.ae_eq (ae_of_all _ fun ω => by simp)

/-- Rational points `q` with `q.1 > 0` approximate every point of `(0,∞) × ℝ`. -/
theorem secondMom_exists_seq_rat {p : ℝ × ℝ} (hp : 0 < p.1) :
    ∃ q : ℕ → ℚ × ℚ, (∀ n, 0 < ((q n).1 : ℝ)) ∧
      Tendsto (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) atTop (𝓝 p) := by
  have hd : Dense (Set.range (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem := hd.open_subset_closure_inter hU (show p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ from
    ⟨hp, trivial⟩)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose q hq using fun n => (hu n).2
  have e : (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) = u := funext fun n => hq n
  refine ⟨q, fun n => ?_, e ▸ hlim⟩
  have := (hu n).1.1
  rw [← hq n] at this
  exact this

/-- Points of `(0,∞) × ℝ` are limits, within `(0,∞) × ℝ`, of rational points. -/
private lemma secondMom_tendsto_within {p : ℝ × ℝ} {q : ℕ → ℚ × ℚ} (hq : ∀ n, 0 < ((q n).1 : ℝ))
    (hlim : Tendsto (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) atTop (𝓝 p)) :
    Tendsto (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) atTop
      (𝓝[Set.Ioi (0 : ℝ) ×ˢ Set.univ] p) :=
  tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => ⟨hq n, trivial⟩⟩

/-- Two functions continuous on `(0,∞) × ℝ` which agree at the rational points of `(0,∞) × ℝ`
agree on `(0,∞) × ℝ`. -/
theorem secondMom_eqOn_of_rat {f g : ℝ × ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0 ×ˢ Set.univ))
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.univ))
    (h : ∀ q : ℚ × ℚ, 0 < (q.1 : ℝ) → f ((q.1 : ℝ), (q.2 : ℝ)) = g ((q.1 : ℝ), (q.2 : ℝ))) :
    Set.EqOn f g (Set.Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨q, hq, hlim⟩ := secondMom_exists_seq_rat (p := p) hp.1
  have hw := secondMom_tendsto_within hq hlim
  have h1 := (hf p hp).tendsto.comp hw
  have h2 := (hg p hp).tendsto.comp hw
  have e : f ∘ (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) =
      g ∘ (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) := funext fun n => h (q n) (hq n)
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

open Classical in
/-- Measurability of `ω ↦ 𝟙_G(ω) Z(t,x,ω)`, when on the measurable set `G` the field is
continuous on `(0,∞) × ℝ` and agrees at rational points with measurable variables `Y q`. -/
private lemma secondMom_measurable_slice {Z : ℝ → ℝ → Ω → ℝ} {G : Set Ω} (hG : MeasurableSet G)
    {Y : ℚ × ℚ → Ω → ℝ} (hY : ∀ q, Measurable (Y q))
    (hP : ∀ ω ∈ G, ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∀ q : ℚ × ℚ, 0 < (q.1 : ℝ) → Z q.1 q.2 ω = Y q ω)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    Measurable fun ω => if ω ∈ G then Z p.1 p.2 ω else 0 := by
  obtain ⟨q, hq, hlim⟩ := secondMom_exists_seq_rat hp
  have hw := secondMom_tendsto_within hq hlim
  refine measurable_of_tendsto_metrizable (f := fun n ω => if ω ∈ G then Y (q n) ω else 0)
    (fun n => Measurable.ite hG (hY _) measurable_const) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ G
  · simp only [hω, ↓reduceIte]
    have h1 := ((hP ω hω).1 p ⟨hp, trivial⟩).tendsto.comp hw
    have e : (fun p : ℝ × ℝ => Z p.1 p.2 ω) ∘ (fun n => (((q n).1 : ℝ), ((q n).2 : ℝ))) =
        fun n => Y (q n) ω := funext fun n => (hP ω hω).2 (q n) (hq n)
    rw [e] at h1
    exact h1
  · simp only [hω, ↓reduceIte]
    exact tendsto_const_nhds

/-- **A jointly measurable version** of a mild solution, continuous on `(0,∞) × ℝ` for every
`ω`, and again a mild solution. -/
theorem secondMom_exists_version (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) :
    ∃ Z' : ℝ → ℝ → Ω → ℝ, (∀ᵐ ω ∂ν, ∀ t x, 0 < t → Z' t x ω = Z t x ω) ∧
      Measurable (uncurryField Z') ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℝ => Z' p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ)) ∧
      IsMildSolution 𝓖 S Z' ν := by
  have haem : ∀ t x, 0 < t → AEMeasurable (Z t x) ν := fun t x ht =>
    (secondMom_memLp hS hZ ht x).aestronglyMeasurable.aemeasurable
  classical
  set Y : ℚ × ℚ → Ω → ℝ := fun q =>
    if hq : 0 < (q.1 : ℝ) then (haem _ _ hq).mk _ else 0 with hYdef
  have hY : ∀ q, Measurable (Y q) := by
    intro q
    by_cases hq : 0 < (q.1 : ℝ)
    · simp only [hYdef, hq, ↓reduceDIte]
      exact (haem _ _ hq).measurable_mk
    · simp only [hYdef, hq, ↓reduceDIte]
      exact measurable_const
  set P : Ω → Prop := fun ω =>
    ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∀ q : ℚ × ℚ, 0 < (q.1 : ℝ) → Z q.1 q.2 ω = Y q ω with hPdef
  have hgood : ∀ᵐ ω ∂ν, P ω := by
    refine hZ.continuous.and (ae_all_iff.2 fun q => ?_)
    by_cases hq : 0 < (q.1 : ℝ)
    · filter_upwards [(haem _ _ hq).ae_eq_mk] with ω hω
      intro _
      simp only [hYdef, hq, ↓reduceDIte]
      exact hω
    · exact ae_of_all _ fun ω h => absurd h hq
  set G : Set Ω := (toMeasurable ν {ω | ¬ P ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGP : ∀ ω ∈ G, P ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hGae : ∀ᵐ ω ∂ν, ω ∈ G := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ G} = toMeasurable ν {ω | ¬ P ω} := by
      ext ω; simp [hGdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hgood
  -- the version
  set Z' : ℝ → ℝ → Ω → ℝ := fun t x ω => if 0 < t ∧ ω ∈ G then Z t x ω else 0 with hZ'def
  have hZ'eq : ∀ ω ∈ G, ∀ t x, 0 < t → Z' t x ω = Z t x ω := fun ω hω t x ht => by
    simp [hZ'def, ht, hω]
  -- joint measurability
  set u : ℝ × ℝ → Ω → ℝ := fun i ω => if ω ∈ G then Z (Real.exp i.1) i.2 ω else 0 with hudef
  have hu_cont : ∀ ω, Continuous fun i => u i ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hudef, hω, ↓reduceIte]
      exact (hGP ω hω).1.comp_continuous (f := fun i : ℝ × ℝ => (Real.exp i.1, i.2))
        (by fun_prop) (fun i => ⟨Real.exp_pos _, trivial⟩)
    · simp only [hudef, hω, ↓reduceIte]
      exact continuous_const
  have hu_meas : ∀ i, Measurable (u i) := fun i => by
    convert secondMom_measurable_slice (p := (Real.exp i.1, i.2)) hGm hY hGP (Real.exp_pos _)
      using 1
    funext ω
    simp only [hudef]
  have hu := measurable_uncurry_of_continuous_of_measurable hu_cont hu_meas
  have hZ'm : Measurable (uncurryField Z') := by
    have e : uncurryField Z' = fun p : Ω × ℝ × ℝ =>
        if 0 < p.2.1 then Function.uncurry u ((Real.log p.2.1, p.2.2), p.1) else 0 := by
      funext p
      simp only [uncurryField, hZ'def, Function.uncurry_apply_pair, hudef]
      by_cases ht : 0 < p.2.1
      · simp [ht, Real.exp_log ht]
      · simp [ht]
    rw [e]
    refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) ?_ measurable_const
    exact hu.comp (by fun_prop)
  refine ⟨Z', hGae.mono fun ω hω => hZ'eq ω hω, hZ'm, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ G
    · exact (hGP ω hω).1.congr fun p hp => hZ'eq ω hω p.1 p.2 hp.1
    · have : (fun p : ℝ × ℝ => Z' p.1 p.2 ω) = fun _ => 0 := by
        funext p; simp [hZ'def, hω]
      rw [this]
      exact continuousOn_const
  · have hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Z' p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ) := by
      intro ω
      by_cases hω : ω ∈ G
      · exact (hGP ω hω).1.congr fun p hp => hZ'eq ω hω p.1 p.2 hp.1
      · have : (fun p : ℝ × ℝ => Z' p.1 p.2 ω) = fun _ => 0 := by
          funext p; simp [hZ'def, hω]
        rw [this]
        exact continuousOn_const
    refine ⟨ae_of_all _ hcont, fun t x ht => ?_⟩
    refine (hZ.mild t x ht).congr_ae hS ?_ ?_
    · have hprod : ∀ᵐ p ∂(ν.prod (volume : Measure (ℝ × ℝ))), p.1 ∈ G :=
        QuasiMeasurePreserving.ae
          (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := (volume : Measure (ℝ × ℝ)))) hGae
      filter_upwards [hprod] with p hp
      simp only [uncurryField]
      by_cases hs : 0 < p.2.1 ∧ p.2.1 < t
      · simp only [hs, and_self, ↓reduceIte]
        rw [hZ'eq p.1 hp _ _ hs.1]
      · simp only [hs, ↓reduceIte]
    · filter_upwards [hGae] with ω hω
      rw [hZ'eq ω hω t x ht]

end QSSEPtoKPZ
