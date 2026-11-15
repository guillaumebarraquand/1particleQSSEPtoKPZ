/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshMart
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The bracket of a Walsh integral process (task G9)

Auxiliary results for `WhiteNoise/WalshProcess.lean`, on the process
`A_t(ω) = ∫_0^t ∫ g(r,y,ω) g'(r,y,ω) dy dr`:

* `walshProc_bracket`: if `𝟙_{(0,T]} g`, `𝟙_{(0,T]} g' ∈ L²(ν ⊗ dr ⊗ dy)`, then almost surely
  `A` is continuous and of bounded variation on `[0, T]`, `A_t` is integrable, and
  `𝔼[𝟙_B (A_t - A_s)] = 𝔼 ∫∫ 𝟙_B 𝟙_{s < r ≤ t} g g'` (Fubini); `walshProc_bracket_mono`:
  for `g = g'`, `A` is almost surely nondecreasing.
* `walshProc_bracket_stronglyMeasurable`: for predictable `g`, `g'`, `A_s` is
  `𝒢_s`-measurable.
* `walshProc_exists_predictable`: every Walsh integrand is almost everywhere equal to a
  predictable field (it is an `L²` limit of elementary integrands).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### Analytic properties -/

/-- `eVariationOn (f - g) ≤ eVariationOn f + eVariationOn g`. -/
private lemma walshProc_eVariationOn_sub_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (f - g) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, us⟩ := p
  calc ∑ i ∈ Finset.range n, edist ((f - g) (u (i + 1))) ((f - g) (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [Real.dist_eq, Pi.sub_apply]
        rw [show f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i)) =
          (f (u (i + 1)) - f (u i)) + -(g (u (i + 1)) - g (u i)) by ring]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le (f := f) (n := n) hu us)
          (eVariationOn.sum_le (f := g) (n := n) hu us)

/-- A primitive of an integrable function is of bounded variation on `[0, T]`. -/
private lemma walshProc_bv_primitive {φ : ℝ → ℝ} (hφ : Integrable φ) (T : ℝ) :
    BoundedVariationOn (fun t => ∫ r in (0 : ℝ)..t, φ r) (Set.Icc 0 T) := by
  have hP := hφ.pos_part
  have hN := hφ.neg_part
  have hmono : ∀ {ψ : ℝ → ℝ}, Integrable ψ → (∀ r, 0 ≤ ψ r) →
      BoundedVariationOn (fun t => ∫ r in (0 : ℝ)..t, ψ r) (Set.Icc 0 T) := by
    intro ψ hψ hψ0
    have hc : Continuous fun t => ∫ r in (0 : ℝ)..t, ψ r :=
      intervalIntegral.continuous_primitive (fun _ _ => hψ.intervalIntegrable) 0
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (f := fun t => ∫ r in (0 : ℝ)..t, ψ r) hc.continuousOn
    refine MonotoneOn.boundedVariationOn (C := C) (fun a _ b _ hab => ?_) fun x hx => by
      simpa [Real.norm_eq_abs] using hC x hx
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := a) (c := b)
      hψ.intervalIntegrable hψ.intervalIntegrable]
    simp only [le_add_iff_nonneg_right]
    exact intervalIntegral.integral_nonneg hab fun r _ => hψ0 r
  have e : (fun t => ∫ r in (0 : ℝ)..t, φ r) = (fun t => ∫ r in (0 : ℝ)..t, max (φ r) 0) -
      fun t => ∫ r in (0 : ℝ)..t, max (-φ r) 0 := by
    funext t
    rw [Pi.sub_apply, ← intervalIntegral.integral_sub hP.intervalIntegrable hN.intervalIntegrable]
    congr 1
    funext r
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [e]
  have h1 := hmono hP fun r => le_max_right _ _
  have h2 := hmono hN fun r => le_max_right _ _
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h1, h2⟩)
    (walshProc_eVariationOn_sub_le _ _ _)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}

/-- **The bracket functional**: continuity, bounded variation, integrability, and the identity
`𝔼[𝟙_B (A_t - A_s)] = 𝔼 ∫∫ 𝟙_B 𝟙_{s < r ≤ t} g g'`. -/
theorem walshProc_bracket [IsProbabilityMeasure ν] {T : ℝ} {g g' : ℝ → ℝ → Ω → ℝ}
    (hg : MemLp (uncurryField fun r y ω => if 0 < r ∧ r ≤ T then g r y ω else 0) 2
      (ν.prod volume))
    (hg' : MemLp (uncurryField fun r y ω => if 0 < r ∧ r ≤ T then g' r y ω else 0) 2
      (ν.prod volume)) :
    (∀ᵐ ω ∂ν, ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω)
        (Set.Icc 0 T) ∧
      BoundedVariationOn (fun t => ∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω) (Set.Icc 0 T) ∧
      (g = g' → MonotoneOn (fun t => ∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω)
        (Set.Icc 0 T))) ∧
    (∀ t ∈ Set.Icc 0 T, Integrable (fun ω => ∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω) ν) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ B : Set Ω, MeasurableSet B →
      ∫ ω in B, ((∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω) -
        ∫ r in (0 : ℝ)..s, ∫ y, g r y ω * g' r y ω) ∂ν =
      ∫ p : Ω × ℝ × ℝ, B.indicator (fun _ => (1 : ℝ)) p.1 *
        (if s < p.2.1 ∧ p.2.1 ≤ t then g p.2.1 p.2.2 p.1 * g' p.2.1 p.2.2 p.1 else 0)
        ∂(ν.prod volume)) := by
  set F : Ω × ℝ × ℝ → ℝ := fun p =>
    uncurryField (fun r y ω => if 0 < r ∧ r ≤ T then g r y ω else 0) p *
      uncurryField (fun r y ω => if 0 < r ∧ r ≤ T then g' r y ω else 0) p with hFdef
  have hF : Integrable F (ν.prod volume) := hg.integrable_mul hg'
  -- the truncation at time `t`
  set Ft : ℝ → Ω × ℝ × ℝ → ℝ := fun t p => if 0 < p.2.1 ∧ p.2.1 ≤ t then F p else 0 with hFt
  have hFti : ∀ t, Integrable (Ft t) (ν.prod volume) := by
    intro t
    have : Ft t = {p : Ω × ℝ × ℝ | 0 < p.2.1 ∧ p.2.1 ≤ t}.indicator F := by
      funext p
      by_cases h : 0 < p.2.1 ∧ p.2.1 ≤ t <;> simp [hFt, Set.indicator, h]
    rw [this]
    exact hF.indicator ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const))
  -- the good `ω`: integrable sections
  have hgood : ∀ᵐ ω ∂ν, Integrable (fun q : ℝ × ℝ => F (ω, q)) (volume : Measure (ℝ × ℝ)) :=
    hF.prod_right_ae
  -- on a good `ω`, `A_t = ∫_0^t φ` with `φ r = ∫ F(ω, r, ·)` integrable
  have hA : ∀ ω, Integrable (fun q : ℝ × ℝ => F (ω, q)) (volume : Measure (ℝ × ℝ)) →
      Integrable (fun r => ∫ y, F (ω, r, y)) ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        (∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω) = ∫ r in (0 : ℝ)..t, ∫ y, F (ω, r, y) := by
    intro ω hω
    refine ⟨hω.integral_prod_left, fun t ht => ?_⟩
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [Set.uIoc_of_le ht.1] at hr
    have hc : 0 < r ∧ r ≤ T := ⟨hr.1, hr.2.trans ht.2⟩
    simp [hFdef, uncurryField, hc]
  -- the value at `t` as a product integral
  have hAt : ∀ ω, Integrable (fun q : ℝ × ℝ => F (ω, q)) (volume : Measure (ℝ × ℝ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, (∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g' r y ω) =
        ∫ q, Ft t (ω, q) ∂(volume : Measure (ℝ × ℝ)) := by
    intro ω hω t ht
    have hsec : Integrable (fun q : ℝ × ℝ => Ft t (ω, q)) (volume : Measure (ℝ × ℝ)) := by
      have : (fun q : ℝ × ℝ => Ft t (ω, q)) =
          {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ t}.indicator fun q => F (ω, q) := by
        funext q
        by_cases h : 0 < q.1 ∧ q.1 ≤ t <;> simp [hFt, Set.indicator, h]
      rw [this]
      exact hω.indicator ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
    rw [(hA ω hω).2 t ht, show ∫ q, Ft t (ω, q) ∂(volume : Measure (ℝ × ℝ)) =
      ∫ r, ∫ y, Ft t (ω, r, y) from integral_prod _ hsec, intervalIntegral.integral_of_le ht.1,
      ← integral_indicator measurableSet_Ioc]
    congr 1
    funext r
    by_cases hr : 0 < r ∧ r ≤ t
    · simp [Set.indicator, hFt, hr, Set.mem_Ioc]
    · have : r ∉ Set.Ioc 0 t := fun h => hr h
      simp [hFt, hr]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    obtain ⟨hφ, he⟩ := hA ω hω
    have hc : Continuous fun t => ∫ r in (0 : ℝ)..t, ∫ y, F (ω, r, y) :=
      intervalIntegral.continuous_primitive (fun _ _ => hφ.intervalIntegrable) 0
    refine ⟨hc.continuousOn.congr fun t ht => he t ht, ?_, fun hgg => ?_⟩
    · have hbv := walshProc_bv_primitive hφ T
      unfold BoundedVariationOn at hbv ⊢
      rwa [eVariationOn.eq_of_eqOn fun t ht => he t ht]
    · intro a ha b hb hab
      beta_reduce
      rw [he a ha, he b hb, ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := a)
        (c := b) hφ.intervalIntegrable hφ.intervalIntegrable]
      simp only [le_add_iff_nonneg_right]
      refine intervalIntegral.integral_nonneg hab fun r _ => integral_nonneg fun y => ?_
      simp only [hFdef, uncurryField, hgg]
      exact mul_self_nonneg _
  · intro t ht
    refine (hFti t).integral_prod_left.congr ?_
    filter_upwards [hgood] with ω hω
    exact (hAt ω hω t ht).symm
  · intro s t hs hst htT B hB
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs, hst.trans htT⟩
    have htT' : t ∈ Set.Icc (0 : ℝ) T := ⟨hs.trans hst, htT⟩
    have hint : Integrable (fun p : Ω × ℝ × ℝ => B.indicator (fun _ => (1 : ℝ)) p.1 *
        (Ft t p - Ft s p)) (ν.prod volume) := by
      refine ((hFti t).sub (hFti s)).bdd_mul (c := 1)
        ((measurable_const.indicator hB).comp measurable_fst).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      by_cases h : p.1 ∈ B <;> simp [Set.indicator, h]
    have e1 : (fun p : Ω × ℝ × ℝ => B.indicator (fun _ => (1 : ℝ)) p.1 *
        (if s < p.2.1 ∧ p.2.1 ≤ t then g p.2.1 p.2.2 p.1 * g' p.2.1 p.2.2 p.1 else 0)) =
        fun p => B.indicator (fun _ => (1 : ℝ)) p.1 * (Ft t p - Ft s p) := by
      funext p
      congr 1
      by_cases h1 : s < p.2.1
      · have h0 : 0 < p.2.1 := lt_of_le_of_lt hs h1
        by_cases h2 : p.2.1 ≤ t
        · have h3 : p.2.1 ≤ T := h2.trans htT
          simp [hFt, hFdef, uncurryField, h1, h2, h0, h3, not_le.2 h1]
        · have h4 : ¬ p.2.1 ≤ s := fun h => h2 (h.trans hst)
          simp [hFt, h1, h2, h4]
      · have h2 : p.2.1 ≤ s := not_lt.1 h1
        have h3 : p.2.1 ≤ t := h2.trans hst
        simp [hFt, h1, h2, h3]
    rw [e1, integral_prod _ hint, ← integral_indicator hB]
    · refine integral_congr_ae ?_
      filter_upwards [hgood] with ω hω
      have hsec : ∀ u : ℝ, Integrable (fun q : ℝ × ℝ => Ft u (ω, q)) (volume : Measure (ℝ × ℝ)) := by
        intro u
        have : (fun q : ℝ × ℝ => Ft u (ω, q)) =
            {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ u}.indicator fun q => F (ω, q) := by
          funext q
          by_cases h : 0 < q.1 ∧ q.1 ≤ u <;> simp [hFt, Set.indicator, h]
        rw [this]
        exact hω.indicator ((measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_le measurable_fst measurable_const))
      have hsub := integral_sub (hsec t) (hsec s)
      beta_reduce at hsub
      rw [integral_const_mul, hsub, ← hAt ω hω t htT',
        ← hAt ω hω s hsT]
      by_cases h : ω ∈ B <;> simp [Set.indicator, h]

/-- For `g = g'`, the bracket functional is almost surely nondecreasing on `[0, T]`. -/
theorem walshProc_bracket_mono [IsProbabilityMeasure ν] {T : ℝ} {g : ℝ → ℝ → Ω → ℝ}
    (hg : MemLp (uncurryField fun r y ω => if 0 < r ∧ r ≤ T then g r y ω else 0) 2
      (ν.prod volume)) :
    ∀ᵐ ω ∂ν, MonotoneOn (fun t => ∫ r in (0 : ℝ)..t, ∫ y, g r y ω * g r y ω) (Set.Icc 0 T) := by
  filter_upwards [(walshProc_bracket hg hg).1] with ω hω
  exact hω.2.2 rfl

end QSSEPtoKPZ
