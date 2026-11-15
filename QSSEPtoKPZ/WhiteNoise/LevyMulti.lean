/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Levy
public import QSSEPtoKPZ.Martingales.Covariation
public import QSSEPtoKPZ.WhiteNoise.LevyMultiBracket
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# White noises from families of martingales (task G7b)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G7b.
See `docs/stage4-design.md`, Sections 1.2 (f) and 3.3, and `docs/stage4-interfaces.md`.

Step 2 of the proof of Proposition 7.2 ("By Lévy's characterization of Brownian motion, `ξ` is a
white noise"): if the processes `t ↦ S(t,b) - S(t,a)` are continuous square-integrable
martingales with covariations `t |(a,b] ∩ (a',b']|` (on every horizon), then `S` is the
distribution function of a white noise in the sense of the frozen `IsWhiteNoise`. Proof:
Cramér–Wold (linear combinations have bracket `∑ λᵢ² cᵢ t` by bilinearity of
`HasCovariation`) and `levy_setIntegral`, conditionally on `A ∈ 𝓖_s`; characteristic functions
(`Measure.ext_of_charFun`, `indepFun_iff_charFun_prod`).

Proof (task G7b). The conditional characteristic function
`∫_A exp(i ∑ᵢ uᵢ ξ((s,t] × (aᵢ,bᵢ])) dℙ = exp(-Q(u)(t-s)/2) ℙ(A)`, `A ∈ 𝓖_s`, is
`levyMulti_setIntegral` (`LevyMultiBracket.lean`). Here: with one interval it identifies the law
`N(0, (t-s)(b-a))` (`Measure.ext_of_charFun`); for the cells of a subdivision `Q(u)` is diagonal
and the joint characteristic function is the product of the marginal ones
(`iIndepFun_iff_charFunDual_pi`); and for any finite family of intervals, the conditional
characteristic function on `A ∈ 𝓖_s` being `φ(u) ℙ(A)` gives `ℙ(A ∩ {X ∈ B}) = ℙ(A) ℙ(X ∈ B)`
(`Measure.ext_of_charFunDual` applied to `(ℙ|_A) ∘ X⁻¹` and `ℙ(A) ℙ ∘ X⁻¹`), and the σ-algebra of
all rectangle masses is a directed supremum of these (`indep_iSup_of_directed_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A continuous linear form on `ℝ^ι` is `L x = ∑ᵢ L(eᵢ) xᵢ`. -/
private lemma levyMulti_dual_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) : L x = ∑ i, L (Pi.single i 1) * x i := by
  rw [← ContinuousLinearMap.sum_comp_single (L := L) (v := x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : ι → ℝ) = x i • Pi.single i 1 := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, this, map_smul,
    smul_eq_mul, mul_comm]

/-- **Independence from a deterministic conditional characteristic function.** If
`∫_A exp(i L(X)) dℙ = φ(L) ℙ(A)` for all `A ∈ 𝓕_r` and all linear forms `L`, then `X` is
independent of `𝓕_r`. -/
private lemma levyMulti_indep_of_setIntegral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ} {r : ℝ≥0} {ι : Type*} [Fintype ι] {X : Ω → ι → ℝ}
    (hX : Measurable X) (φ : StrongDual ℝ (ι → ℝ) → ℂ)
    (h : ∀ A, MeasurableSet[𝓕 r] A → ∀ L : StrongDual ℝ (ι → ℝ),
      ∫ ω in A, Complex.exp ((L (X ω) : ℂ) * Complex.I) ∂μ = φ L * (μ.real A : ℂ)) :
    Indep (MeasurableSpace.comap X inferInstance) (𝓕 r) μ := by
  rw [Indep_iff]
  rintro _ A ⟨B, hB, rfl⟩ hA
  have : IsFiniteMeasure (μ A • μ.map X) :=
    ⟨by simp⟩
  have key : (μ.restrict A).map X = μ A • μ.map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply, integral_map hX.aemeasurable (by fun_prop),
      integral_smul_measure, integral_map hX.aemeasurable (by fun_prop), h A hA L,
      ← setIntegral_univ, h Set.univ MeasurableSet.univ L]
    rw [probReal_univ, Complex.ofReal_one, mul_one, Complex.real_smul, measureReal_def,
      mul_comm]
  have := congrArg (fun ν : Measure (ι → ℝ) => ν B) key
  rw [Measure.map_apply hX hB, Measure.restrict_apply (hX hB), Measure.smul_apply,
    Measure.map_apply hX hB, smul_eq_mul] at this
  rw [this, mul_comm]

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
  {S : ℝ → ℝ → Ω → ℝ}

/-- One interval: `∫_A exp(i v ξ((s,t] × (a,b])) dℙ = exp(-v² (b-a)(t-s)/2) ℙ(A)`. -/
private lemma levyMulti_setIntegral_one (h0 : ∀ x ω, S 0 x ω = 0)
    (hcov : ∀ (T : ℝ) (a b a' b' : ℝ), a ≤ b → a' ≤ b' →
      HasCovariation T 𝓖 (fun t ω => S t b ω - S t a ω) (fun t ω => S t b' ω - S t a' ω)
        (fun t _ => t * (volume (Set.Ioc a b ∩ Set.Ioc a' b')).toReal) μ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Complex.exp ((v : ℂ) * (rectMass S s t a b ω : ℂ) * Complex.I) ∂μ =
      (Real.exp (-(v ^ 2 * (b - a) * ((t : ℝ) - s) / 2)) : ℂ) * (μ.real A : ℂ) := by
  have h := levyMulti_setIntegral (ι := Unit) (a := fun _ => a) (b := fun _ => b)
    h0 hcov (fun _ => hab) (fun _ => v) hst hA
  have hQ : levyMultiQ (fun _ : Unit => a) (fun _ => b) (fun _ => v) = v ^ 2 * (b - a) := by
    simp only [levyMultiQ, levyMultiCov, Set.inter_self, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.2 hab), Finset.univ_unique, Finset.sum_singleton]
    ring
  simpa [hQ] using h

end

/-- A family of continuous martingales indexed by intervals `(a, b]`, with the covariations of
a white noise, is a white noise. -/
theorem isWhiteNoise_of_martingales {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    (hS : ∀ t x, Measurable[𝓖 t.toNNReal] (S t x))
    (h0 : ∀ x ω, S 0 x ω = 0)
    (hcov : ∀ (T : ℝ) (a b a' b' : ℝ), a ≤ b → a' ≤ b' →
      HasCovariation T 𝓖 (fun t ω => S t b ω - S t a ω) (fun t ω => S t b' ω - S t a' ω)
        (fun t _ => t * (volume (Set.Ioc a b ∩ Set.Ioc a' b')).toReal) μ) :
    IsWhiteNoise 𝓖 S μ := by
  classical
  have hmeas : ∀ t x, Measurable (S t x) := fun t x => (hS t x).mono (𝓖.le _) le_rfl
  have hrect : ∀ s t a b, Measurable (rectMass S s t a b) := fun s t a b =>
    (((hmeas t b).sub (hmeas t a)).sub (hmeas s b)).add (hmeas s a)
  refine ⟨fun t x => by have h := hS t x; rw [Real.toNNReal_coe] at h; exact h, ?_, ?_, ?_⟩
  · -- the law of one rectangle mass
    intro s t a b hst hab
    refine ⟨(hrect _ _ _ _).aemeasurable, ?_⟩
    refine Measure.ext_of_charFun (funext fun v => ?_)
    rw [charFun_apply_real, integral_map (hrect _ _ _ _).aemeasurable (by fun_prop),
      charFun_gaussianReal, ← setIntegral_univ,
      levyMulti_setIntegral_one h0 hcov hab v hst MeasurableSet.univ]
    rw [NNReal.coe_mul, NNReal.coe_sub hst, Real.coe_toNNReal _ (sub_nonneg.2 hab)]
    simp only [probReal_univ, Complex.ofReal_one, mul_one, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · -- independence of the cells of a subdivision
    intro s t hst k a ha
    have hcell : ∀ i : Fin k, a i.castSucc ≤ a i.succ := fun i => ha (Fin.castSucc_le_succ i)
    rw [iIndepFun_iff_charFunDual_pi (E := fun _ => ℝ) (fun i => (hrect _ _ _ _).aemeasurable)]
    intro L
    set u : Fin k → ℝ := fun i => L (Pi.single i 1) with hu
    have hfac : ∀ i : Fin k, charFunDual (μ.map (rectMass S s t (a i.castSucc) (a i.succ)))
        (L.comp (.single ℝ (fun _ => ℝ) i)) =
        (Real.exp (-(u i ^ 2 * (a i.succ - a i.castSucc) * ((t : ℝ) - s) / 2)) : ℂ) := by
      intro i
      rw [charFunDual_apply, integral_map (hrect _ _ _ _).aemeasurable (by fun_prop)]
      have hL : ∀ x : ℝ, (L.comp (.single ℝ (fun _ => ℝ) i)) x = u i * x := by
        intro x
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
          levyMulti_dual_apply]
        simp [Pi.single_apply, hu]
      simp_rw [hL, Complex.ofReal_mul]
      rw [← setIntegral_univ, levyMulti_setIntegral_one h0 hcov (hcell i) _ hst
        MeasurableSet.univ]
      simp
    rw [Finset.prod_congr rfl fun i _ => hfac i, charFunDual_apply,
      integral_map (Measurable.of_eval fun i => hrect _ _ _ _).aemeasurable (by fun_prop)]
    have hL : ∀ ω, L (fun i => rectMass S s t (a i.castSucc) (a i.succ) ω) =
        ∑ i, u i * rectMass S s t (a i.castSucc) (a i.succ) ω := fun ω =>
      levyMulti_dual_apply L _
    simp_rw [hL]
    rw [← setIntegral_univ, levyMulti_setIntegral h0 hcov hcell u hst MeasurableSet.univ]
    have hQ : levyMultiQ (fun i : Fin k => a i.castSucc) (fun i => a i.succ) u =
        ∑ i, u i ^ 2 * (a i.succ - a i.castSucc) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp [levyMultiCov, Real.volume_Ioc, hcell i, sq]
      · intro j _ hji
        have hempty : Set.Ioc (a i.castSucc) (a i.succ) ∩ Set.Ioc (a j.castSucc) (a j.succ) =
            ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false,
            not_and, not_le]
          intro h1 h2
          rcases lt_or_gt_of_ne hji with h | h
          · have := ha (Fin.succ_le_castSucc_iff.2 h)
            linarith [h1.1]
          · have := ha (Fin.succ_le_castSucc_iff.2 h)
            linarith [h1.2]
        simp [levyMultiCov, hempty]
      · simp
    rw [hQ, probReal_univ, Complex.ofReal_one, mul_one, ← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_neg_distrib]
  · -- independence of the past
    intro s t hst
    set Z : (F : Finset (ℝ × ℝ)) → Ω → (F → ℝ) := fun F ω p =>
      rectMass S s t (min p.1.1 p.1.2) (max p.1.1 p.1.2) ω with hZdef
    have hZ : ∀ F, Measurable (Z F) := fun F => Measurable.of_eval fun p => hrect _ _ _ _
    have hind : ∀ F : Finset (ℝ × ℝ),
        Indep (MeasurableSpace.comap (Z F) inferInstance) (𝓖 s) μ := by
      intro F
      refine levyMulti_indep_of_setIntegral (hZ F) (fun L => (Real.exp (-(levyMultiQ
        (fun p : F => min p.1.1 p.1.2) (fun p => max p.1.1 p.1.2)
        (fun p => L (Pi.single p 1)) * ((t : ℝ) - s) / 2)) : ℂ)) ?_
      intro A hA L
      have hL : ∀ ω, L (Z F ω) = ∑ p, L (Pi.single p 1) * Z F ω p := fun ω =>
        levyMulti_dual_apply L _
      simp_rw [hL]
      exact levyMulti_setIntegral h0 hcov (fun p => min_le_max) _ hst hA
    have hle : ∀ F G : Finset (ℝ × ℝ), F ⊆ G → MeasurableSpace.comap (Z F) inferInstance ≤
        MeasurableSpace.comap (Z G) inferInstance := by
      intro F G hFG
      have : Measurable[MeasurableSpace.comap (Z G) inferInstance] (Z F) := by
        change Measurable[MeasurableSpace.comap (Z G) inferInstance]
          ((fun (z : G → ℝ) (p : F) => z ⟨p.1, hFG p.2⟩) ∘ Z G)
        exact (Measurable.of_eval fun p : F =>
          measurable_pi_apply (⟨p.1, hFG p.2⟩ : G)).comp
          (comap_measurable (Z G))
      exact this.comap_le
    have hdir : Directed (· ≤ ·) fun F : Finset (ℝ × ℝ) =>
        MeasurableSpace.comap (Z F) inferInstance := fun F G =>
      ⟨F ∪ G, hle _ _ Finset.subset_union_left, hle _ _ Finset.subset_union_right⟩
    refine indep_of_indep_of_le_left (indep_iSup_of_directed_le hind
      (fun F => (hZ F).comap_le) (𝓖.le s) hdir) ?_
    refine iSup₂_le fun x y => le_iSup_of_le {(x, y)} ?_
    set p : ↥({(x, y)} : Finset (ℝ × ℝ)) := ⟨(x, y), Finset.mem_singleton_self _⟩
    have hp : Measurable[MeasurableSpace.comap (Z {(x, y)}) inferInstance]
        fun ω => Z {(x, y)} ω p :=
      (measurable_pi_apply p).comp (comap_measurable (Z _))
    have : Measurable[MeasurableSpace.comap (Z {(x, y)}) inferInstance]
        (rectMass S s t x y) := by
      rcases le_total x y with h | h
      · convert hp using 1
        ext ω
        show _ = rectMass S s t (min x y) (max x y) ω
        rw [min_eq_left h, max_eq_right h]
      · convert hp.neg using 1
        ext ω
        show _ = -rectMass S s t (min x y) (max x y) ω
        rw [min_eq_right h, max_eq_left h]
        simp only [rectMass]; ring
    exact this.comap_le

end QSSEPtoKPZ
