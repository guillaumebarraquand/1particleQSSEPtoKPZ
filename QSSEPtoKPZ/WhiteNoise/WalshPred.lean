/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshMart
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Predictable integrands and adaptedness of the bracket (task G9)

Auxiliary results for `WhiteNoise/WalshProcess.lean`.

* `walshProc_bracket_stronglyMeasurable`: for predictable fields `g`, `g'`, the random variable
  `∫_0^s ∫ g g' dy dr` is `𝒢_s`-measurable.
* `walshProc_exists_predictable`: every Walsh integrand `h` is `ν ⊗ dr ⊗ dy`-almost everywhere
  equal to `G((r⁺, ω), y)` for a function `G` measurable for the predictable σ-algebra times
  the Borel σ-algebra (it is an `L²` limit of elementary integrands, which are of this form).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- Iterated integrals of a strongly measurable function are strongly measurable. -/
private lemma walshProc_sm_integral {α : Type*} [MeasurableSpace α] {F : (α × ℝ) × ℝ → ℝ}
    (hF : StronglyMeasurable F) : StronglyMeasurable (fun x => ∫ r, ∫ y, F ((x, r), y)) :=
  (hF.integral_prod_right' (ν := volume)).integral_prod_right' (ν := volume)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- The map `(ω, r) ↦ (min(r⁺, s), ω)` is measurable from `𝒢_s ⊗ 𝓑(ℝ)` to the predictable
σ-algebra. -/
private lemma walshProc_measurable_clip (s : ℝ≥0) :
    Measurable[(𝓖 s).prod (borel ℝ), 𝓖.predictable]
      (fun q : Ω × ℝ => (min q.2.toNNReal s, q.1)) := by
  have hm : Measurable fun r : ℝ => min r.toNNReal s :=
    measurable_real_toNNReal.min measurable_const
  rw [@measurable_iff_comap_le _ _ ((𝓖 s).prod (borel ℝ)) 𝓖.predictable]
  refine MeasurableSpace.comap_le_iff_le_map.2
    (measurableSpace_le_predictable_of_measurableSet (fun A hA => ?_) fun i A hA => ?_)
  · have e : (fun q : Ω × ℝ => (min q.2.toNNReal s, q.1)) ⁻¹' ({⊥} ×ˢ A) =
        A ×ˢ ((fun r : ℝ => min r.toNNReal s) ⁻¹' {⊥}) := by
      ext ⟨ω, r⟩
      simp [and_comm]
    change MeasurableSet[(𝓖 s).prod (borel ℝ)] _
    rw [e]
    exact @MeasurableSet.prod Ω ℝ (𝓖 s) (borel ℝ) _ _ (𝓖.mono bot_le A hA)
      (hm (measurableSet_singleton _))
  · have e : (fun q : Ω × ℝ => (min q.2.toNNReal s, q.1)) ⁻¹' (Set.Ioi i ×ˢ A) =
        A ×ˢ ((fun r : ℝ => min r.toNNReal s) ⁻¹' Set.Ioi i) := by
      ext ⟨ω, r⟩
      simp [and_comm]
    change MeasurableSet[(𝓖 s).prod (borel ℝ)] _
    rw [e]
    by_cases his : i < s
    · exact @MeasurableSet.prod Ω ℝ (𝓖 s) (borel ℝ) _ _ (𝓖.mono his.le A hA)
        (hm measurableSet_Ioi)
    · have : (fun r : ℝ => min r.toNNReal s) ⁻¹' Set.Ioi i = ∅ := by
        ext r
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (min_le_right _ _).trans (not_lt.1 his)
      rw [this, Set.prod_empty]
      exact @MeasurableSet.empty _ ((𝓖 s).prod (borel ℝ))

/-- **Adaptedness of the bracket**: for predictable `g`, `g'`, the random variable
`∫_0^s ∫ g(r,y) g'(r,y) dy dr` is `𝒢_s`-measurable. -/
theorem walshProc_bracket_stronglyMeasurable {g g' : ℝ → ℝ → Ω → ℝ}
    (hg : Measurable[(𝓖.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => g p.1.1 p.2 p.1.2)
    (hg' : Measurable[(𝓖.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => g' p.1.1 p.2 p.1.2) (s : ℝ≥0) :
    StronglyMeasurable[𝓖 s] fun ω => ∫ r in (0 : ℝ)..s, ∫ y, g r y ω * g' r y ω := by
  set Φ : (Ω × ℝ) × ℝ → ℝ := fun p => if p.1.2 ∈ Set.Ioc (0 : ℝ) s then
    g (min p.1.2.toNNReal s) p.2 p.1.1 * g' (min p.1.2.toNNReal s) p.2 p.1.1 else 0 with hΦ
  have hΨ : Measurable[((𝓖 s).prod (borel ℝ)).prod (borel ℝ), (𝓖.predictable).prod (borel ℝ)]
      fun p : (Ω × ℝ) × ℝ => ((min p.1.2.toNNReal s, p.1.1), p.2) :=
    Measurable.prodMk (m := ((𝓖 s).prod (borel ℝ)).prod (borel ℝ))
      ((walshProc_measurable_clip s).comp
        (@measurable_fst _ _ ((𝓖 s).prod (borel ℝ)) (borel ℝ)))
      (@measurable_snd _ _ ((𝓖 s).prod (borel ℝ)) (borel ℝ))
  have hΦm : Measurable[((𝓖 s).prod (borel ℝ)).prod (borel ℝ)] Φ := by
    refine Measurable.ite (m := ((𝓖 s).prod (borel ℝ)).prod (borel ℝ)) ?_
      ((hg.comp hΨ).mul (hg'.comp hΨ)) measurable_const
    exact (@measurable_snd _ _ (𝓖 s) (borel ℝ)).comp
      (@measurable_fst _ _ ((𝓖 s).prod (borel ℝ)) (borel ℝ)) measurableSet_Ioc
  have key := @walshProc_sm_integral Ω (𝓖 s) Φ hΦm.stronglyMeasurable
  have heq : ∀ ω, (∫ r in (0 : ℝ)..s, ∫ y, g r y ω * g' r y ω) = ∫ r, ∫ y, Φ ((ω, r), y) := by
    intro ω
    rw [intervalIntegral.integral_of_le s.coe_nonneg, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext r
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) s
    · have hm : max r 0 = r := max_eq_left hr.1.le
      simp [hΦ, hm, hr.1, hr.2]
    · have hr' : ¬ (0 < r ∧ r ≤ s) := hr
      simp [hΦ, hr']
  rw [show (fun ω => ∫ r in (0 : ℝ)..s, ∫ y, g r y ω * g' r y ω) =
    fun ω => ∫ r, ∫ y, Φ ((ω, r), y) from funext heq]
  exact key

/-! ### Walsh integrands are almost everywhere predictable -/

/-- `(r, ω) ↦ c(ω) 𝟙_{r > u}` is predictable for `c` `𝒢_u`-measurable. -/
private lemma walshProc_measurable_after {u : ℝ≥0} {c : Ω → ℝ} (hc : Measurable[𝓖 u] c) :
    Measurable[𝓖.predictable] fun q : ℝ≥0 × Ω => if u < q.1 then c q.2 else 0 := by
  intro B hB
  have e : (fun q : ℝ≥0 × Ω => if u < q.1 then c q.2 else 0) ⁻¹' B =
      (Set.Ioi u ×ˢ (c ⁻¹' B)) ∪ ((Set.Ioi u ×ˢ Set.univ)ᶜ ∩ {_q | (0 : ℝ) ∈ B}) := by
    ext ⟨r, ω⟩
    by_cases h : u < r <;> simp [h]
  rw [e]
  exact (measurableSet_predictable_Ioi_prod (hc hB)).union
    ((measurableSet_predictable_Ioi_prod MeasurableSet.univ).compl.inter (MeasurableSet.const _))

/-- An adapted elementary integrand is of the form `G((r⁺, ω), y)` with `G` predictable. -/
private lemma walshProc_elem_predictable {e : WalshElem Ω} (he : e.IsAdapted 𝓖) :
    Measurable[(𝓖.predictable).prod (borel ℝ)]
      (fun q : (ℝ≥0 × Ω) × ℝ => e.field q.1.1 q.2 q.1.2) ∧
    uncurryField e.field = fun p => e.field (p.2.1.toNNReal : ℝ) p.2.2 p.1 := by
  constructor
  · have hblock : ∀ i, Measurable[(𝓖.predictable).prod (borel ℝ)]
        (fun q : (ℝ≥0 × Ω) × ℝ =>
          ((if e.s i < q.1.1 then e.c i q.1.2 else 0) - (if e.t i < q.1.1 then e.c i q.1.2 else 0))
            * (Set.Ioc (e.a i) (e.b i)).indicator (fun _ => (1 : ℝ)) q.2) := by
      intro i
      have h1 := walshProc_measurable_after (𝓖 := 𝓖) (he.meas i)
      have h2 := walshProc_measurable_after (𝓖 := 𝓖) ((he.meas i).mono (𝓖.mono (he.le_t i)) le_rfl)
      exact ((h1.comp (@measurable_fst _ _ 𝓖.predictable (borel ℝ))).sub
        (h2.comp (@measurable_fst _ _ 𝓖.predictable (borel ℝ)))).mul
        ((measurable_const.indicator measurableSet_Ioc).comp
          (@measurable_snd _ _ 𝓖.predictable (borel ℝ)))
    convert Finset.measurable_sum (m := (𝓖.predictable).prod (borel ℝ)) Finset.univ
      fun i _ => hblock i using 1
    funext q
    simp only [WalshElem.field]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hst := he.le_t i
    by_cases h1 : e.s i < q.1.1
    · by_cases h2 : e.t i < q.1.1
      · have : ¬ (q.1.1 : ℝ) ≤ e.t i := not_le.2 (by exact_mod_cast h2)
        simp [h1, h2, this]
      · have h2' : (q.1.1 : ℝ) ≤ e.t i := by exact_mod_cast not_lt.1 h2
        have h1' : (e.s i : ℝ) < q.1.1 := by exact_mod_cast h1
        by_cases h3 : e.a i < q.2 ∧ q.2 ≤ e.b i
        · simp [h1, h2, h1', h2', h3, Set.indicator, Set.mem_Ioc]
        · simp [h1, h2, h1', h2', h3, Set.indicator, Set.mem_Ioc]
    · have h1' : ¬ (e.s i : ℝ) < q.1.1 := by exact_mod_cast h1
      have h2 : ¬ e.t i < q.1.1 := fun h => h1 (lt_of_le_of_lt hst h)
      simp [h1, h1', h2]
  · funext p
    simp only [uncurryField, WalshElem.field]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hr : 0 ≤ p.2.1
    · rw [Real.coe_toNNReal _ hr]
    · have h1 : ¬ (e.s i : ℝ) < p.2.1 := fun h => hr ((e.s i).2.trans h.le)
      have h2 : ¬ (e.s i : ℝ) < (p.2.1.toNNReal : ℝ) := by
        rw [Real.toNNReal_of_nonpos (le_of_not_ge hr)]
        simp
      simp [h1]

/-- **Walsh integrands are almost everywhere predictable**: if `X = ∫ h dξ`, there is `G`,
measurable for the predictable σ-algebra times the Borel σ-algebra, with
`h(r, y, ω) = G((r⁺, ω), y)` for `ν ⊗ dr ⊗ dy`-almost every `(ω, r, y)`. -/
theorem walshProc_exists_predictable (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ}
    {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    ∃ G : (ℝ≥0 × Ω) × ℝ → ℝ, Measurable[(𝓖.predictable).prod (borel ℝ)] G ∧
      uncurryField h =ᵐ[ν.prod volume] fun p => G ((p.2.1.toNNReal, p.1), p.2.2) := by
  set pm : Ω × ℝ × ℝ → (ℝ≥0 × Ω) × ℝ := fun p => ((p.2.1.toNNReal, p.1), p.2.2) with hpm
  obtain ⟨e, he, hlim, -⟩ := hX.exists_elem_tendsto hS
  have helem : ∀ j, AEStronglyMeasurable[MeasurableSpace.comap pm
      ((𝓖.predictable).prod (borel ℝ))] (uncurryField (e j).field) (ν.prod volume) := by
    intro j
    obtain ⟨hGj, hej⟩ := walshProc_elem_predictable (he j)
    refine ⟨_, (hGj.comp (comap_measurable pm)).stronglyMeasurable, ?_⟩
    rw [hej]
    rfl
  obtain ⟨f, hf, hhf⟩ := walshProc_aesm_of_tendsto_L2 helem hlim
  obtain ⟨G, hG, hfG⟩ := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) := (𝓖.predictable).prod (borel ℝ)
    exact Measurable.exists_eq_measurable_comp hf.measurable
  refine ⟨G, hG, hhf.trans ?_⟩
  rw [hfG]
  rfl

end QSSEPtoKPZ
