/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71BracketAux

/-!
# Proposition 7.1 (3): the stopped prelimit identity (task Q4)

The localization of decision D3″ (`docs/stage4-design.md`, Section 1.2 (d)): the level process
`V_n = max(Q_n, (M_n^φ)²)` (`limBrPreV`, time clamped to `[0,T]`), its hitting time
`σ_n^L = hitTime V_n L T`, and the identity of the proof of Proposition 7.1 (3)
`𝔼[(M_n^φ(t∧σ)² - Q_n(t∧σ) - M_n^φ(s∧σ)² + Q_n(s∧σ)) Θ] = 0` for `Θ` measurable for the
canonical filtration at time `s` (`limBr_prelim_integral`), under a prelimit law. The stopped
increment is `limBrInc`; `limBrLimV` is the level process of the limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Interval

noncomputable section

namespace QSSEPtoKPZ

universe u

variable {T : ℝ}

/-- The level process `V_n(u) = max(⟨M_n^φ⟩_u, M_n^φ(u)²)`, with `u` clamped to `[0,T]`. -/
def limBrPreV (n : ℝ) (φ φt : ℝ → ℝ → ℝ) (u : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ℝ :=
  max (QNpath n φ (pathFunClamp T u) γ) (MNpath n φ φt (pathFunClamp T u) γ ^ 2)

/-- The level process `V(u) = max(Q(u), M^φ(u)²)` of the limit (with the modified bracket
`limBrMod`), with `u` clamped to `[0,T]`. -/
def limBrLimV (ρ : ℝ → ℝ) (φ φt : ℝ → ℝ → ℝ) (u : ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : ℝ :=
  max (limBrMod ρ φ (pathFunClamp T u) γ)
    (limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt (pathFunClamp T u) γ ^ 2)

/-- The stopped increment `(M(t∧σ)² - A(t∧σ)) - (M(s∧σ)² - A(s∧σ))`. -/
def limBrInc (M A : ℝ → ℝ) (s t σ : ℝ) : ℝ :=
  (M (min t σ) ^ 2 - A (min t σ)) - (M (min s σ) ^ 2 - A (min s σ))

/-- For a bracket `⟨M⟩ = A` and a bounded `𝓕_s`-measurable `Θ`,
`𝔼[Θ ((M_t² - A_t) - (M_s² - A_s))] = 0` (the identity of the proof of Proposition 7.1 (3)). -/
private lemma limBr_integral_mul_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ → Ω → ℝ}
    (h : HasBracket T 𝓕 M A P) {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ) ≤ T) {Θ : Ω → ℝ}
    (hΘ : StronglyMeasurable[𝓕 s] Θ) {B : ℝ} (hB : ∀ ω, |Θ ω| ≤ B) :
    Integrable (fun ω => Θ ω * ((M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω))) P ∧
      ∫ ω, Θ ω * ((M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω)) ∂P = 0 := by
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hYt : Integrable (fun ω => M t ω ^ 2 - A t ω) P :=
    (h.memLp t ht).integrable_sq.sub (h.integrable_bracket t ht)
  have hYs : Integrable (fun ω => M s ω ^ 2 - A s ω) P :=
    (h.memLp s hs).integrable_sq.sub (h.integrable_bracket s hs)
  have hdiff := hYt.sub hYs
  have hprod : Integrable (Θ * fun ω => (M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω)) P :=
    hdiff.bdd_mul (hΘ.mono (𝓕.le s)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)
  refine ⟨hprod, ?_⟩
  have h1 : P[fun ω => (M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω) | 𝓕 s] =ᵐ[P] 0 := by
    refine (condExp_sub hYt hYs _).trans ?_
    filter_upwards [h.condExp_sq s t hst ht, h.condExp_sq s s le_rfl hs] with ω h1 h2
    simp [h1, h2]
  have h2 := condExp_mul_of_stronglyMeasurable_left hΘ hprod hdiff
  calc ∫ ω, Θ ω * ((M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω)) ∂P
      = ∫ ω, (Θ * fun ω => (M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω)) ω ∂P := rfl
    _ = ∫ ω, (P[Θ * fun ω => (M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω) | 𝓕 s]) ω ∂P :=
        (integral_condExp (𝓕.le s)).symm
    _ = ∫ ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h2, h1] with ω h2 h1
        rw [h2, Pi.mul_apply, h1]
        simp
    _ = 0 := by simp

variable {n C : ℝ} {φ φt : ℝ → ℝ → ℝ}

/-- `M_n^φ(u)` is measurable for the canonical filtration at any time `t ≥ u`. -/
theorem limBr_measurable_MNpath_can (hn : 1 ≤ n) (hφ : IsC13 T φ φt C) {u : ℝ}
    (hu : u ∈ Icc 0 T) {t : ℝ≥0} (hut : u ≤ t) :
    Measurable[pathFiltrationCan T t] (MNpath n φ φt u) := by
  have e : MNpath n φ φt u = MNpath n φ φt u ∘ prelimStop (T := T) u := by
    funext γ
    simp only [Function.comp_apply, MNpath]
    rw [pathAt_prelimStop hu.1 le_rfl]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    simp only [pathAt_prelimStop hu.1 hs.2]
  rw [e]
  exact (measurable_MNpath hn hφ hu).comp ((measurable_prelimStop (T := T) ⟨u, hu.1⟩).mono
    ((pathFiltrationCan T).mono (show (⟨u, hu.1⟩ : ℝ≥0) ≤ t from hut)) le_rfl)

/-- `⟨M_n^φ⟩_u` is measurable for the canonical filtration at any time `t ≥ u`. -/
theorem limBr_measurable_QNpath_can (hn : 1 ≤ n) (hφ : IsC13 T φ φt C) {u : ℝ}
    (hu : u ∈ Icc 0 T) {t : ℝ≥0} (hut : u ≤ t) :
    Measurable[pathFiltrationCan T t] (QNpath n φ u) := by
  have e : QNpath n φ u = QNpath n φ u ∘ prelimStop (T := T) u := by
    funext γ
    simp only [Function.comp_apply, QNpath]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    simp only [QNdensPath, atomPath, pathAt_prelimStop hu.1 hs.2]
  rw [e]
  exact (measurable_QNpath hn hφ hu).comp ((measurable_prelimStop (T := T) ⟨u, hu.1⟩).mono
    ((pathFiltrationCan T).mono (show (⟨u, hu.1⟩ : ℝ≥0) ≤ t from hut)) le_rfl)

theorem limBr_clamp_le {T : ℝ} (u : ℝ≥0) : pathFunClamp T u ≤ u :=
  max_le u.2 (min_le_right _ _)

/-- The level process `V_n` is adapted to the canonical filtration. -/
theorem limBr_measurable_preV (hT : 0 ≤ T) (hn : 1 ≤ n) (hφ : IsC13 T φ φt C) (u : ℝ≥0) :
    Measurable[pathFiltrationCan T u] (limBrPreV (T := T) n φ φt u) :=
  (limBr_measurable_QNpath_can hn hφ (pathFunClamp_mem hT u) (limBr_clamp_le u)).max
    ((limBr_measurable_MNpath_can hn hφ (pathFunClamp_mem hT u) (limBr_clamp_le u)).pow_const 2)

/-- Every path of the level process `V_n` is continuous. -/
theorem limBr_continuous_preV (hT : 0 ≤ T) (hn : 1 ≤ n) (hφ : IsC13 T φ φt C)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    Continuous fun u : ℝ≥0 => limBrPreV (T := T) n φ φt u γ := by
  have hc : Continuous fun u : ℝ≥0 => pathFunClamp T u :=
    (continuous_pathFunClamp T).comp NNReal.continuous_coe
  have h1 := (continuousOn_monotoneOn_QNpath hn hφ γ).1.comp_continuous hc
    fun u => pathFunClamp_mem hT u
  have h2 := (continuousOn_MNpath hn hφ γ).comp_continuous hc fun u => pathFunClamp_mem hT u
  exact h1.max (h2.pow 2)

/-- **The stopped prelimit identity**: under a prelimit law, for `σ = hitTime V_n L T` and a
bounded `Θ` measurable for the canonical filtration at time `s ≤ t ≤ T`,
`𝔼[Θ ((M_n^φ(t∧σ)² - Q_n(t∧σ)) - (M_n^φ(s∧σ)² - Q_n(s∧σ)))] = 0` (`σ` is a stopping time and
`HasBracket.stopped`). -/
theorem limBr_prelim_integral {P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hP : IsPathPrelimLaw.{u} T n P) (hn : 1 ≤ n) (hT : 0 < T) (hφ : IsC13 T φ φt C) (L : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ) ≤ T)
    {Θ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ} (hΘ : Measurable[pathFiltrationCan T s] Θ)
    {B : ℝ} (hB : ∀ γ, |Θ γ| ≤ B) :
    Integrable (fun γ => Θ γ * limBrInc (fun u => MNpath n φ φt u γ) (fun u => QNpath n φ u γ)
      s t (hitTime (limBrPreV n φ φt) L ⟨T, hT.le⟩ γ)) P ∧
    ∫ γ, Θ γ * limBrInc (fun u => MNpath n φ φt u γ) (fun u => QNpath n φ u γ)
      s t (hitTime (limBrPreV n φ φt) L ⟨T, hT.le⟩ γ) ∂P = 0 := by
  have := hP.isProbabilityMeasure
  have hBr := hP.hasBracket hn hT hφ
  have hτ0 := isStoppingTime_hitTime (𝓕 := pathFiltrationCan T)
    (limBr_measurable_preV hT.le hn hφ) (limBr_continuous_preV hT.le hn hφ) L ⟨T, hT.le⟩
  have hτ : IsStoppingTime (nullAug P (nullAug P (pathFiltrationCan T)))
      (fun γ => (hitTime (limBrPreV n φ φt) L ⟨T, hT.le⟩ γ : WithTop ℝ≥0)) := fun i =>
    (le_nullAug P (nullAug P (pathFiltrationCan T)) i) _
      ((le_nullAug P (pathFiltrationCan T) i) _ (hτ0 i))
  have hS := hBr.stopped hτ fun γ => NNReal.coe_le_coe.2 (hitTime_le _ _ _ γ)
  exact limBr_integral_mul_sub hS hst ht
    ((hΘ.mono (le_nullAug P (pathFiltrationCan T) s) le_rfl).stronglyMeasurable) hB

end QSSEPtoKPZ
