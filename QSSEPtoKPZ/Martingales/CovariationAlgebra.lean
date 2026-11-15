/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Covariation
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Algebra of covariations (task G8a)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G8a.
See `docs/stage4-interfaces.md`.

Bilinearity and symmetry of `HasCovariation`, and polarization from brackets: used for (7.9)
(`⟨M^{φ₁}, M^{φ₂}⟩` from the brackets of Proposition 7.1 (3)), for (7.10) and in Step 2 of the
proof of Proposition 7.2.

Auxiliary results (task G8a): the variation of a linear combination
(`mmEVariationOn_lincomb_le`, `mmBoundedVariationOn_lincomb`), and the invariance of
`HasCovariation` under a change of the covariation process on a null set
(`HasCovariation.mmCongrCov`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The variation of `a f + b g` is at most `|a| Var f + |b| Var g`. -/
theorem mmEVariationOn_lincomb_le {α : Type*} [LinearOrder α] (f g : α → ℝ) (s : Set α)
    (a b : ℝ) :
    eVariationOn (fun t => a * f t + b * g t) s ≤
      ‖a‖ₑ * eVariationOn f s + ‖b‖ₑ * eVariationOn g s := by
  refine iSup_le fun p => ?_
  have hpt : ∀ i, edist (a * f (p.2.1 (i + 1)) + b * g (p.2.1 (i + 1)))
      (a * f (p.2.1 i) + b * g (p.2.1 i)) ≤
      ‖a‖ₑ * edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
        ‖b‖ₑ * edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) := by
    intro i
    rw [edist_eq_enorm_sub, edist_eq_enorm_sub, edist_eq_enorm_sub, ← enorm_mul, ← enorm_mul]
    refine le_trans (le_of_eq ?_) (enorm_add_le _ _)
    congr 1; ring
  calc ∑ i ∈ Finset.range p.1, edist (a * f (p.2.1 (i + 1)) + b * g (p.2.1 (i + 1)))
        (a * f (p.2.1 i) + b * g (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, (‖a‖ₑ * edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          ‖b‖ₑ * edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = ‖a‖ₑ * ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          ‖b‖ₑ * ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add
        (mul_le_mul_right (eVariationOn.sum_le p.2.2.1 p.2.2.2) _)
        (mul_le_mul_right (eVariationOn.sum_le p.2.2.1 p.2.2.2) _)

/-- A linear combination of functions of bounded variation has bounded variation. -/
theorem mmBoundedVariationOn_lincomb {α : Type*} [LinearOrder α] {f g : α → ℝ} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) (a b : ℝ) :
    BoundedVariationOn (fun t => a * f t + b * g t) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top enorm_ne_top hf,
    ENNReal.mul_ne_top enorm_ne_top hg⟩) (mmEVariationOn_lincomb_le f g s a b)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {T : ℝ}

/-- `HasCovariation` is unchanged when the covariation process is modified on a null set of
paths, on `[0, T]` (`T ≥ 0` is needed for the condition at time `0`). -/
theorem HasCovariation.mmCongrCov (hT : 0 ≤ T) {M N A A' : ℝ → Ω → ℝ}
    (h : HasCovariation T 𝓕 M N A μ) (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, A t ω = A' t ω) :
    HasCovariation T 𝓕 M N A' μ := by
  have haeA : ∀ t : ℝ≥0, (t : ℝ) ≤ T → A t =ᵐ[μ] A' t := fun t ht => by
    filter_upwards [hA] with ω hω using hω t ⟨t.2, ht⟩
  refine ⟨h.left, h.right, fun t ht => (h.integrable_cov t ht).congr (haeA t ht), ?_, ?_, ?_,
    fun s t hst ht => ?_⟩
  · filter_upwards [h.zero, hA] with ω h0 hω
    rw [← hω 0 ⟨le_rfl, hT⟩]; exact h0
  · filter_upwards [h.cont_cov, hA] with ω hc hω
    exact hc.congr fun t ht => (hω t ht).symm
  · filter_upwards [h.bv, hA] with ω hc hω
    unfold BoundedVariationOn at hc ⊢
    rwa [eVariationOn.eq_of_eqOn (f := fun t => A' t ω) (f' := fun t => A t ω)
      fun t ht => (hω t ht).symm]
  · have e : ∀ u : ℝ≥0, (u : ℝ) ≤ T →
        (fun ω => M u ω * N u ω - A u ω) =ᵐ[μ] fun ω => M u ω * N u ω - A' u ω := fun u hu => by
      filter_upwards [haeA u hu] with ω h1
      rw [h1]
    exact (condExp_congr_ae (e t ht).symm).trans ((h.condExp_mul s t hst ht).trans
      (e s (le_trans (NNReal.coe_le_coe.2 hst) ht)))

/-- A bracket is a covariation of the martingale with itself. -/
theorem HasBracket.hasCovariation {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ) :
    HasCovariation T 𝓕 M M A μ := by
  refine ⟨h.toIsCL2Mart, h.toIsCL2Mart, h.integrable_bracket, h.zero, h.cont_bracket, ?_,
    fun s t hst ht => ?_⟩
  · filter_upwards [h.mono] with ω hω
    rcases lt_or_ge T 0 with hT | hT
    · exact BoundedVariationOn.of_subsingleton
        (by rw [Set.Icc_eq_empty (not_le.2 hT)]; exact Set.subsingleton_empty)
    · have := hω.locallyBoundedVariationOn 0 T ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩
      rwa [Set.inter_self] at this
  · simpa only [← sq] using h.condExp_sq s t hst ht

/-- Symmetry of the covariation. -/
theorem HasCovariation.symm {M N A : ℝ → Ω → ℝ} (h : HasCovariation T 𝓕 M N A μ) :
    HasCovariation T 𝓕 N M A μ := by
  refine ⟨h.right, h.left, h.integrable_cov, h.zero, h.cont_cov, h.bv, fun s t hst ht => ?_⟩
  simpa only [mul_comm (N _ _)] using h.condExp_mul s t hst ht

/-- Additivity of the covariation in the first argument. -/
theorem HasCovariation.add_left [IsFiniteMeasure μ] {M M' N A A' : ℝ → Ω → ℝ}
    (h : HasCovariation T 𝓕 M N A μ) (h' : HasCovariation T 𝓕 M' N A' μ) :
    HasCovariation T 𝓕 (fun t ω => M t ω + M' t ω) N (fun t ω => A t ω + A' t ω) μ := by
  refine ⟨h.left.add h'.left, h.right, fun t ht => (h.integrable_cov t ht).add
    (h'.integrable_cov t ht), ?_, ?_, ?_, fun s t hst ht => ?_⟩
  · filter_upwards [h.zero, h'.zero] with ω h1 h2; simp [h1, h2]
  · filter_upwards [h.cont_cov, h'.cont_cov] with ω h1 h2 using h1.add h2
  · filter_upwards [h.bv, h'.bv] with ω h1 h2
    simpa using mmBoundedVariationOn_lincomb h1 h2 1 1
  · have hi : ∀ (P : ℝ → Ω → ℝ) (B : ℝ → Ω → ℝ), HasCovariation T 𝓕 P N B μ →
        Integrable (fun ω => P t ω * N t ω - B t ω) μ := fun P B hP =>
      ((hP.left.memLp t ht).integrable_mul (hP.right.memLp t ht)).sub (hP.integrable_cov t ht)
    have e : (fun ω => (M t ω + M' t ω) * N t ω - (A t ω + A' t ω)) =
        (fun ω => M t ω * N t ω - A t ω) + fun ω => M' t ω * N t ω - A' t ω := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [e]
    refine (condExp_add (hi M A h) (hi M' A' h') _).trans ?_
    filter_upwards [h.condExp_mul s t hst ht, h'.condExp_mul s t hst ht] with ω h1 h2
    simp only [Pi.add_apply, h1, h2]; ring

/-- Homogeneity of the covariation in the first argument. -/
theorem HasCovariation.const_mul_left {M N A : ℝ → Ω → ℝ} (h : HasCovariation T 𝓕 M N A μ)
    (c : ℝ) :
    HasCovariation T 𝓕 (fun t ω => c * M t ω) N (fun t ω => c * A t ω) μ := by
  refine ⟨h.left.const_mul c, h.right, fun t ht => (h.integrable_cov t ht).const_mul c, ?_, ?_,
    ?_, fun s t hst ht => ?_⟩
  · filter_upwards [h.zero] with ω h1; simp [h1]
  · filter_upwards [h.cont_cov] with ω h1 using continuousOn_const.mul h1
  · filter_upwards [h.bv] with ω h1
    simpa using mmBoundedVariationOn_lincomb h1 h1 c 0
  · have e : ∀ u : ℝ≥0, (fun ω => c * M u ω * N u ω - c * A u ω) =
        c • fun ω => M u ω * N u ω - A u ω := fun u => by
      funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, e]
    exact (condExp_smul c _ _).trans ((h.condExp_mul s t hst ht).mono fun ω hω => by
      simp only [Pi.smul_apply, hω])

/-- **Polarization**: from the brackets of `M`, `N` and `M + N`,
`⟨M, N⟩ = (⟨M + N⟩ - ⟨M⟩ - ⟨N⟩) / 2`. -/
theorem HasCovariation.of_hasBracket_add [IsFiniteMeasure μ] {M N A B C : ℝ → Ω → ℝ}
    (hM : HasBracket T 𝓕 M A μ) (hN : HasBracket T 𝓕 N B μ)
    (hMN : HasBracket T 𝓕 (fun t ω => M t ω + N t ω) C μ) :
    HasCovariation T 𝓕 M N (fun t ω => (C t ω - A t ω - B t ω) / 2) μ := by
  refine ⟨hM.toIsCL2Mart, hN.toIsCL2Mart, fun t ht => ?_, ?_, ?_, ?_, fun s t hst ht => ?_⟩
  · exact (((hMN.integrable_bracket t ht).sub (hM.integrable_bracket t ht)).sub
      (hN.integrable_bracket t ht)).div_const 2
  · filter_upwards [hM.zero, hN.zero, hMN.zero] with ω h1 h2 h3; simp [h1, h2, h3]
  · filter_upwards [hM.cont_bracket, hN.cont_bracket, hMN.cont_bracket] with ω h1 h2 h3
    exact ((h3.sub h1).sub h2).div_const 2
  · filter_upwards [hM.hasCovariation.bv, hN.hasCovariation.bv, hMN.hasCovariation.bv]
      with ω h1 h2 h3
    have := mmBoundedVariationOn_lincomb
      (mmBoundedVariationOn_lincomb h3 h1 1 (-1)) h2 (1 / 2) (-1 / 2)
    unfold BoundedVariationOn at this ⊢
    convert this using 2
    funext t; ring
  · have hi : ∀ (P : ℝ → Ω → ℝ) (D : ℝ → Ω → ℝ), HasBracket T 𝓕 P D μ →
        Integrable (fun ω => P t ω ^ 2 - D t ω) μ := fun P D hP =>
      ((hP.memLp t ht).integrable_sq).sub (hP.integrable_bracket t ht)
    have e : ∀ u : ℝ≥0, (fun ω => M u ω * N u ω - (C u ω - A u ω - B u ω) / 2) =
        (1 / 2 : ℝ) • ((fun ω => (M u ω + N u ω) ^ 2 - C u ω) -
          (fun ω => M u ω ^ 2 - A u ω) - fun ω => N u ω ^ 2 - B u ω) := fun u => by
      funext ω; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [e, e]
    refine (condExp_smul _ _ _).trans ?_
    have h1 := condExp_sub ((hi _ _ hMN).sub (hi _ _ hM)) (hi _ _ hN) (𝓕 s)
    have h2 := condExp_sub (hi _ _ hMN) (hi _ _ hM) (𝓕 s)
    have h3 := hMN.condExp_sq s t hst ht
    have h4 := hM.condExp_sq s t hst ht
    have h5 := hN.condExp_sq s t hst ht
    beta_reduce at h3
    filter_upwards [h1, h2, h3, h4, h5] with ω e1 e2 e3 e4 e5
    rw [Pi.smul_apply, e1, Pi.sub_apply, e2, Pi.sub_apply, e3, e4, e5]
    rfl

/-- A covariation `⟨M, M⟩ = A` with `A` almost surely nondecreasing is a bracket. -/
theorem HasCovariation.hasBracket {M A : ℝ → Ω → ℝ} (h : HasCovariation T 𝓕 M M A μ)
    (hmono : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Set.Icc 0 T)) :
    HasBracket T 𝓕 M A μ :=
  { toIsCL2Mart := h.left
    integrable_bracket := h.integrable_cov
    zero := h.zero
    mono := hmono
    cont_bracket := h.cont_cov
    condExp_sq := fun s t hst ht => by simpa only [sq] using h.condExp_mul s t hst ht }

end QSSEPtoKPZ
