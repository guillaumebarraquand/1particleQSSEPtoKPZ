/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Defs
public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.Uniqueness.Defs
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry

/-!
# From (7.8) to the weak mild equation (7.13) on the enlarged space (task Q5a)

Interface added after the audit of Stage 4 (remark R6 of `docs/stage4-audit.md`), proved by
task Q5a. See `docs/stage4-interfaces.md`.

Between `prop_7_2` and `exists_sheVersion_map_eq` the proof of `main_theorem_top` (task Q5) needs
`IsWeakMild` for the lifted field `Z₁(t,x,(ω,ω'')) = Z(t,x,ω)` on `Ω × Ω''`. The conclusion (7.8)
of `prop_7_2` has the value `𝒵(t;f) - ∫ g_t f` for every `t ∈ (0,T]`, while `IsWeakMild` has
`∫ Z(t,x) f(x) dx - ∫ g_t f` for almost every `t`, with one negligible set of times for all
`f`. Proof: the set of `(ω,t)` where `𝒵(t) = Z(t,x) dx` is measurable (it is cut out by countably
many equations: equal total masses, and `∫ f_j d𝒵(t) = ∫ Z(t,x) f_j(x) dx` for the test
functions `f_j = bumpTest j` of Stage 3, which separate finite measures (`isEmbedding_tightEmb`);
both sides are measurable in `(ω,t)`: `pathAt` is continuous in `(γ,t)`, `Z` is jointly
measurable); by `hdens` and Fubini its complement is
`Pr ⊗ Leb`-null, so for almost every `t` it holds for `Pr`-almost every `ω`; at such `t`,
`𝒵(t;f) = ∫ Z(t,x) f(x) dx` almost surely for **every** `f` (using `Z ≥ 0`: `hdens` only sees
`max(Z,0)`), and `IsWalshIntegral.congr_ae` changes the value on a `Pr ⊗ ν''`-null set.
Measurability and (7.1) on the product follow from those on `Ω` (Tonelli, `ν''` a probability
measure).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- For a nonnegative measurable `z`, `∫ g d(z dx) = ∫ z(x) g(x) dx`. -/
private lemma wmBridge_integral_withDensity {z : ℝ → ℝ} (hz : Measurable z) (hz0 : ∀ x, 0 ≤ z x)
    (g : ℝ → ℝ) :
    (∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (z x))) = ∫ x, z x * g x := by
  rw [integral_withDensity_eq_integral_toReal_smul hz.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hz0 _), smul_eq_mul]

/-- **The density relation as countably many equations.** For a finite measure `μ` on `ℝ` and a
nonnegative measurable `z`, `μ = z(x) dx` iff `∫ z = μ(ℝ)` and `∫ f_j dμ = ∫ z f_j` for the
test functions `f_j = bumpTest j` that separate finite measures (`isEmbedding_tightEmb`). -/
private lemma wmBridge_eq_withDensity_iff (μ : FiniteMeasure ℝ) {z : ℝ → ℝ} (hz : Measurable z)
    (hz0 : ∀ x, 0 ≤ z x) :
    (μ : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (z x)) ↔
      ((∫⁻ x, ENNReal.ofReal (z x)) = (μ.mass : ℝ≥0∞) ∧
        ∀ j : ℕ, (∫ x, bumpTest j x ∂(μ : Measure ℝ)) = ∫ x, z x * bumpTest j x) := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · rw [FiniteMeasure.ennreal_mass, h, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
    · rw [h, wmBridge_integral_withDensity hz hz0]
  · rintro ⟨hm, hj⟩
    set ν := volume.withDensity (fun x => ENNReal.ofReal (z x)) with hν
    have hfin : IsFiniteMeasure ν := ⟨by
      rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hm]
      exact ENNReal.coe_lt_top⟩
    let νF : FiniteMeasure ℝ := ⟨ν, hfin⟩
    have he : tightEmb μ = tightEmb νF := by
      funext j
      change (∫ x, bumpTest j x ∂(μ : Measure ℝ)) = ∫ x, bumpTest j x ∂ν
      rw [hj j, hν, wmBridge_integral_withDensity hz hz0]
    exact congrArg (fun m : FiniteMeasure ℝ => (m : Measure ℝ)) (isEmbedding_tightEmb.injective he)

/-- The map `(ω, t, x) ↦ (ω, (t, x))` from `(Ω × ℝ) × ℝ`, used to read a field as a function
of `((ω, t), x)`. -/
private lemma wmBridge_measurable_reassoc :
    Measurable fun q : (Ω × ℝ) × ℝ => (q.1.1, q.1.2, q.2) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

/-- **The set of `(ω, t)` where `Y(ω)(t) = Z(t,x,ω) dx` is measurable**: it is cut out by
countably many equations between measurable functions of `(ω, t)`. -/
private lemma wmBridge_measurableSet_dens {T : ℝ} {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hY : Measurable Y) {Z : ℝ → ℝ → Ω → ℝ} (hZm : Measurable (uncurryField Z))
    (hZ0 : ∀ t x ω, 0 ≤ Z t x ω) :
    MeasurableSet {p : Ω × ℝ | (pathAt (Y p.1) p.2 : Measure ℝ) =
      volume.withDensity fun x => ENNReal.ofReal (Z p.2 x p.1)} := by
  have hzx : ∀ (ω : Ω) (t : ℝ), Measurable fun x => Z t x ω := fun ω t =>
    hZm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hset : {p : Ω × ℝ | (pathAt (Y p.1) p.2 : Measure ℝ) =
      volume.withDensity fun x => ENNReal.ofReal (Z p.2 x p.1)} =
      {p : Ω × ℝ | (∫⁻ x, ENNReal.ofReal (Z p.2 x p.1)) = ((pathAt (Y p.1) p.2).mass : ℝ≥0∞)} ∩
        ⋂ j : ℕ, {p : Ω × ℝ | (∫ x, bumpTest j x ∂(pathAt (Y p.1) p.2 : Measure ℝ)) =
          ∫ x, Z p.2 x p.1 * bumpTest j x} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact wmBridge_eq_withDensity_iff _ (hzx p.1 p.2) (hZ0 p.2 · p.1)
  rw [hset]
  have hYp : Measurable fun p : Ω × ℝ => (Y p.1, p.2) := hY.prodMap measurable_id
  have hZq : Measurable fun q : (Ω × ℝ) × ℝ => Z q.1.2 q.2 q.1.1 :=
    hZm.comp wmBridge_measurable_reassoc
  refine MeasurableSet.inter (measurableSet_eq_fun ?_ ?_) (MeasurableSet.iInter fun j =>
    measurableSet_eq_fun ?_ ?_)
  · exact (ENNReal.measurable_ofReal.comp hZq).lintegral_prod_right'
  · exact ((FiniteMeasure.continuous_mass.comp continuous_pathAt_prod).measurable.comp
      hYp).coe_nnreal_ennreal
  · exact ((continuous_tightEmb_apply j).comp continuous_pathAt_prod).measurable.comp hYp
  · exact (hZq.mul ((bumpTest j).continuous.measurable.comp measurable_snd)).stronglyMeasurable
      |>.integral_prod_right' |>.measurable

/-- **(7.8) gives (7.13) for the lifted density.** Let `Y` be a random path in `C([0,T], ℳ₊)`
on `Ω` with a jointly measurable density `Z ≥ 0` satisfying (7.1) (`Y(t)(dx) = Z(t,x) dx`
almost surely for almost every `t ∈ [0,T]`), and let `S` be a white noise for a filtration `𝒢̄`
on `Ω × Ω''` (product measure) for which (7.8) holds for every `f ∈ C_c^∞(ℝ)` and `t ∈ (0,T]`
(the conclusion of `prop_7_2`). Then `Z₁(t,x,(ω,ω'')) = Z(t,x,ω)` satisfies `IsWeakMild` on
`Ω × Ω''`. -/
theorem isWeakMild_prod_of_eq_7_8 {Pr : Measure Ω} [IsProbabilityMeasure Pr] {T : ℝ}
    (hT : 0 < T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    {Z : ℝ → ℝ → Ω → ℝ} (hZm : Measurable (uncurryField Z)) (hZ0 : ∀ t x ω, 0 ≤ Z t x ω)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z t x ω))
    {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
    {𝒢b : Filtration ℝ≥0 (mΩ.prod m'')} {S : ℝ → ℝ → Ω × Ω'' → ℝ}
    (hS : IsWhiteNoise 𝒢b S (Pr.prod ν''))
    (h78 : ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ t ∈ Set.Ioc (0 : ℝ) T,
      IsWalshIntegral 𝒢b S (Pr.prod ν'')
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω.1 else 0)
        (fun ω => pairFM (pathAt (Y ω.1) t) f - ∫ x, heatKernel t x * f x)) :
    IsWeakMild T 𝒢b S (fun t x ω => Z t x ω.1) (Pr.prod ν'') := by
  have _ : 0 < T := hT -- `0 < T` is not needed
  -- Fubini: "a.s., for a.e. `t`" becomes "for a.e. `t`, a.s." (the set is measurable)
  have hswap : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂Pr,
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z t x ω) :=
    (Measure.ae_ae_comm (wmBridge_measurableSet_dens hY hZm hZ0)).1 hdens
  have hswap' := ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hswap
  have hZq : Measurable fun q : (Ω × ℝ) × ℝ => Z q.1.2 q.2 q.1.1 :=
    hZm.comp wmBridge_measurable_reassoc
  refine ⟨?_, ?_, ?_⟩
  · exact hZm.comp (measurable_fst.fst.prodMk measurable_snd)
  · -- (7.1) on the product: the integrand depends on the first coordinate only
    have hG : Measurable fun p : Ω × ℝ => ∫⁻ x, ENNReal.ofReal (Z p.2 x p.1 ^ 2) :=
      (ENNReal.measurable_ofReal.comp (hZq.pow_const 2)).lintegral_prod_right'
    have hF : Measurable fun ω : Ω =>
        ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2) :=
      hG.lintegral_prod_right'
    refine lt_of_eq_of_lt ((lintegral_prod _ (hF.comp measurable_fst).aemeasurable).trans ?_) hZ2
    simp only [Function.comp_apply, lintegral_const, measure_univ, mul_one]
  · filter_upwards [hswap', ae_restrict_mem measurableSet_Ioc] with t ht htI f hf hfc
    refine IsWalshIntegral.congr_ae hS (h78 f hf hfc t htI) (ae_of_all _ fun _ => rfl) ?_
    refine Measure.quasiMeasurePreserving_fst.ae (p := fun ω : Ω =>
      pairFM (pathAt (Y ω) t) f - (∫ x, heatKernel t x * f x) =
        (∫ x, Z t x ω * f x) - ∫ x, heatKernel t x * f x) ?_
    filter_upwards [ht] with ω hω
    have hzx : Measurable fun x => Z t x ω :=
      hZm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [pairFM, hω, wmBridge_integral_withDensity hzx (hZ0 t · ω)]

end QSSEPtoKPZ
