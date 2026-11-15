/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.NullAug
public import QSSEPtoKPZ.Martingales.StoppingAux
public import QSSEPtoKPZ.Martingales.Doob

/-!
# Stopping times and optional sampling in continuous time (package B, task B3)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces, proved by
task B3. See `docs/stage2-design.md`, Section 2.1 (design decision B-4), and
`docs/stage2-interfaces.md`.

Stopping times are `ℝ≥0`-valued and bounded, coerced to `WithTop ℝ≥0` for Mathlib's
`IsStoppingTime`. No right-continuity of the filtration is assumed: optional sampling is proved
by approximating a bounded stopping time from above by stopping times with finitely many
values (dyadic grids), and passing to the limit with path continuity and uniform
integrability.

* `hitTime X K T`: the first time `X ≥ K`, capped at `T`; `isStoppingTime_hitTime` (all paths
  continuous, raw filtration), and its elementary properties.
* `condExp_stopped_of_forall`: if `𝔼[V_t | 𝓕_t] = Y_t` for all deterministic `t ≤ T`, then
  `𝔼[V_τ | 𝓕_τ] = Y_τ` for every stopping time `τ ≤ T` of `𝓕ᵃ`.
* `IsCL2Mart.condExp_stopped`: optional sampling `𝔼[M_τ | 𝓕_σ] = M_σ` for `σ ≤ τ ≤ T`.
* `IsCL2Mart.stopped`, `HasBracket.stopped`: stopped martingales and stopped brackets.

All are proved (task B3); the auxiliary results on discretization and stopped values are in
`Martingales/StoppingAux.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Hitting times -/

/-- The first time `t ≥ 0` at which `X_t ≥ K`, capped at `T` (equal to `T` if there is no such
time before `T`). -/
def hitTime (X : ℝ → Ω → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf ({t : ℝ≥0 | K ≤ X t ω} ∪ {T}) ⊓ T

/-- The hitting time is at most `T`. -/
lemma hitTime_le (X : ℝ → Ω → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) : hitTime X K T ω ≤ T :=
  inf_le_right

/-- Before the hitting time, `X < K`. -/
lemma lt_of_lt_hitTime {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω} {t : ℝ≥0}
    (ht : t < hitTime X K T ω) : X t ω < K := by
  by_contra h
  have hmem : t ∈ ({t : ℝ≥0 | K ≤ X t ω} ∪ {T}) := Or.inl (not_lt.1 h)
  have : sInf ({t : ℝ≥0 | K ≤ X t ω} ∪ {T}) ≤ t := csInf_le (OrderBot.bddBelow _) hmem
  exact absurd (ht.trans_le inf_le_left) (not_lt.2 this)

/-- For `t < T` and a continuous path, `hitTime ≤ t` iff the path reaches `K` on `[0, t]` (the
set `{s : X_s ≥ K} ∪ {T}` is closed, so its infimum belongs to it). -/
private lemma hitTime_le_iff_of_lt {X : ℝ → Ω → ℝ} {K : ℝ} {T t : ℝ≥0} {ω : Ω}
    (hc : Continuous fun s : ℝ≥0 => X s ω) (htT : t < T) :
    hitTime X K T ω ≤ t ↔ ∃ s : ℝ≥0, s ≤ t ∧ K ≤ X s ω := by
  unfold hitTime
  constructor
  · intro h
    have hS : IsClosed ({s : ℝ≥0 | K ≤ X s ω} ∪ {T}) :=
      (isClosed_le continuous_const hc).union isClosed_singleton
    have hmem := hS.csInf_mem ⟨T, Or.inr rfl⟩ (OrderBot.bddBelow _)
    have hle : sInf ({s : ℝ≥0 | K ≤ X s ω} ∪ {T}) ≤ t := by
      rcases inf_le_iff.1 h with h' | h'
      · exact h'
      · exact absurd h' (not_le.2 htT)
    rcases hmem with hK | hT
    · exact ⟨_, hle, hK⟩
    · rw [Set.mem_singleton_iff.1 hT] at hle
      exact absurd hle (not_le.2 htT)
  · rintro ⟨s, hst, hK⟩
    exact (inf_le_left.trans (csInf_le (OrderBot.bddBelow _)
      (show s ∈ {s : ℝ≥0 | K ≤ X s ω} ∪ {T} from Or.inl hK))).trans hst

/-- A continuous path reaches `K` on `[0, t]` iff for every `n` it exceeds `K - 1/(n+1)` at some
dyadic grid point `gridPt t j k` of `[0, t]` (the maximum over `[0, t]` is attained). -/
private lemma exists_le_iff_forall_grid {X : ℝ → Ω → ℝ} {K : ℝ} {t : ℝ≥0} {ω : Ω}
    (hc : Continuous fun s : ℝ≥0 => X s ω) :
    (∃ s : ℝ≥0, s ≤ t ∧ K ≤ X s ω) ↔
      ∀ n : ℕ, ∃ p : ℕ × ℕ, K - 1 / ((n : ℝ) + 1) < X (gridPt t p.1 p.2) ω := by
  constructor
  · rintro ⟨s, hst, hK⟩ n
    obtain ⟨-, hlim⟩ := tendsto_gridPt (T := (t : ℝ)) (t := (s : ℝ)) t.2
      ⟨s.2, NNReal.coe_le_coe.2 hst⟩
    rw [Real.toNNReal_coe] at hlim
    have hlim' : Tendsto (fun j : ℕ => gridPt t j ⌊2 ^ j * (s : ℝ) / t⌋₊) atTop (𝓝 s) :=
      NNReal.tendsto_coe.1 hlim
    have hlt : K - 1 / ((n : ℝ) + 1) < X s ω := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨j, hj⟩ := (((hc.tendsto s).comp hlim').eventually (lt_mem_nhds hlt)).exists
    exact ⟨(j, _), hj⟩
  · intro h
    obtain ⟨s, hs, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) t)).exists_isMaxOn
      ⟨0, le_rfl, zero_le⟩ hc.continuousOn
    refine ⟨s, hs.2, le_of_forall_pos_lt_add fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨p, hp⟩ := h n
    have hq : X (gridPt t p.1 p.2) ω ≤ X s ω :=
      isMaxOn_iff.1 hmax _ ⟨zero_le, gridPt_le t p.1 p.2⟩
    linarith

/-- **Hitting times are stopping times.** If `X` is adapted to `𝓕` and all its paths are
continuous on `[0, ∞)`, then `hitTime X K T` is a stopping time of `𝓕` (no right-continuity of
the filtration is needed). -/
theorem isStoppingTime_hitTime {X : ℝ → Ω → ℝ} (hX : ∀ t : ℝ≥0, Measurable[𝓕 t] (X t))
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (K : ℝ) (T : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => (hitTime X K T ω : WithTop ℝ≥0)) := by
  intro t
  show MeasurableSet[𝓕 t] {ω | (hitTime X K T ω : WithTop ℝ≥0) ≤ t}
  simp only [WithTop.coe_le_coe]
  rcases le_or_gt T t with hTt | htT
  · have e : {ω | hitTime X K T ω ≤ t} = Set.univ :=
      Set.eq_univ_of_forall fun ω => (hitTime_le X K T ω).trans hTt
    rw [e]; exact MeasurableSet.univ
  have key : {ω | hitTime X K T ω ≤ t} =
      ⋂ n : ℕ, ⋃ p : ℕ × ℕ, {ω | K - 1 / ((n : ℝ) + 1) < X (gridPt t p.1 p.2) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [hitTime_le_iff_of_lt (hc ω) htT, exists_le_iff_forall_grid (hc ω)]
  rw [key]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun p =>
    𝓕.mono (gridPt_le t p.1 p.2) _ (hX _ measurableSet_Ioi)

/-- Up to the hitting time (included), `X ≤ K`, if the path is continuous and `X_0 ≤ K`. -/
theorem le_of_le_hitTime {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => X t ω) (h0 : X 0 ω ≤ K) {t : ℝ≥0}
    (ht : t ≤ hitTime X K T ω) : X t ω ≤ K := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ hitTime X K T ω) with h | hpos
  · have : t = 0 := le_antisymm (h ▸ ht) zero_le
    subst this
    simpa using h0
  · have hsub : Set.Iio (hitTime X K T ω) ⊆ {s : ℝ≥0 | X s ω ≤ K} :=
      fun s hs => (lt_of_lt_hitTime hs).le
    have hcl : IsClosed {s : ℝ≥0 | X s ω ≤ K} := isClosed_le hc continuous_const
    have hIic := closure_minimal hsub hcl
    rw [closure_Iio' (a := hitTime X K T ω) ⟨0, hpos⟩] at hIic
    exact hIic ht

/-- If `X < K` on `[0, T)`, the hitting time is `T`. -/
lemma hitTime_eq_of_forall_lt {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω}
    (h : ∀ t : ℝ≥0, t < T → X t ω < K) : hitTime X K T ω = T := by
  refine le_antisymm (hitTime_le X K T ω) (le_inf (le_csInf ⟨T, Or.inr rfl⟩ ?_) le_rfl)
  rintro t (ht | ht)
  · by_contra hlt
    exact absurd (h t (not_le.1 hlt)) (not_lt.2 ht)
  · exact le_of_eq ht.symm

/-! ### Conditional expectations at stopping times -/

/-- **Conditional expectation at a bounded stopping time.** Let `T ≥ 0`, let `V` and `Y` have
almost surely continuous paths on `[0, T]`, let `V_t` be almost everywhere strongly measurable
for `t ≤ T`, let `𝔼[sup_{t ∈ [0, T]} (|V_t| + |Y_t|)] < ∞`, and assume `𝔼[V_t | 𝓕_t] = Y_t`
almost surely for every deterministic `t ∈ [0, T]`. Then `𝔼[V_τ | 𝓕_τ] = Y_τ` almost surely for
every stopping time `τ ≤ T` of the augmented filtration `𝓕ᵃ`.

(With `V_t = M_T`, `Y_t = M_t` this is optional sampling; with `V_t = 𝒲(t+s)²` it is the
stopping-time form of (4.7); with `V_t = M_{t+s}² - A_{t+s}`, `Y_t = M_t² - A_t` it gives the
increments of a bracket after a stopping time.) -/
theorem condExp_stopped_of_forall [IsFiniteMeasure μ] {V Y : ℝ → Ω → ℝ} {T : ℝ}
    (hV : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T))
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hVm : ∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable (V t) μ)
    (hdom : ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (|V t ω| + |Y t ω|) ∂μ ≠ ∞)
    (h : ∀ t : ℝ≥0, (t : ℝ) ≤ T → μ[V t | 𝓕 t] =ᵐ[μ] Y t)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    μ[fun ω => V (τ ω) ω | hτ.measurableSpace] =ᵐ[μ] fun ω => Y (τ ω) ω := by
  classical
  rcases lt_or_ge T 0 with hT | hT
  · exact ae_of_all _ fun ω => absurd ((τ ω).2.trans (hτT ω)) (not_le.2 hT)
  set T' : ℝ≥0 := ⟨T, hT⟩ with hT'
  set D : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (|V t ω| + |Y t ω|)
    with hD
  have hDV : ∀ ω (t : ℝ), t ∈ Set.Icc 0 T → ‖V t ω‖ₑ ≤ D ω := fun ω t ht => by
    rw [Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (abs_nonneg _))).trans
      (le_iSup₂ (f := fun t _ => ENNReal.ofReal (|V t ω| + |Y t ω|)) t ht)
  have hDY : ∀ ω (t : ℝ), t ∈ Set.Icc 0 T → ‖Y t ω‖ₑ ≤ D ω := fun ω t ht => by
    rw [Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (abs_nonneg _))).trans
      (le_iSup₂ (f := fun t _ => ENNReal.ofReal (|V t ω| + |Y t ω|)) t ht)
  have hYm : ∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable[𝓕 t] (Y t) μ := fun t ht =>
    ⟨_, stronglyMeasurable_condExp, (h t ht).symm⟩
  have hVi : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (V t) μ := fun t ht =>
    integrable_of_enorm_le_lintegral (hVm t ht) hdom (ae_of_all _ fun ω => hDV ω t ⟨t.2, ht⟩)
  have hYi : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (Y t) μ := fun t ht =>
    integrable_of_enorm_le_lintegral ((hYm t ht).mono (𝓕.le t)) hdom
      (ae_of_all _ fun ω => hDY ω t ⟨t.2, ht⟩)
  -- the hypothesis, for sets of `𝓕ᵃ_t`
  have hdet : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ B, MeasurableSet[nullAug μ 𝓕 t] B →
      ∫ ω in B, V t ω ∂μ = ∫ ω in B, Y t ω ∂μ := fun t ht B hB => by
    rw [← setIntegral_condExp ((nullAug μ 𝓕).le t) (hVi t ht) hB]
    exact integral_congr_ae (ae_restrict_of_ae ((condExp_nullAug (V t) t).trans (h t ht)))
  -- the dyadic approximations `τ_j ↓ τ`
  set τj : ℕ → Ω → ℝ≥0 := fun j ω => dyadicUpper T' j (τ ω) with hτjdef
  have hτj : ∀ j, IsStoppingTime (nullAug μ 𝓕) (fun ω => (τj j ω : WithTop ℝ≥0)) := fun j =>
    isStoppingTime_comp_of_monotone hτ (dyadicUpper_mono T' j) (le_dyadicUpper T' j)
  have hτT' : ∀ ω, τ ω ≤ T' := fun ω => NNReal.coe_le_coe.1 (hτT ω)
  have hτjT : ∀ j ω, (τj j ω : ℝ) ≤ T := fun j ω =>
    NNReal.coe_le_coe.2 (dyadicUpper_le T' j (hτT' ω))
  have hrange : ∀ j, ∃ S : Finset ℝ≥0, (∀ ω, τj j ω ∈ S) ∧ ∀ s ∈ S, (s : ℝ) ≤ T := fun j =>
    ⟨_, fun ω => Finset.mem_filter.2 ⟨dyadicUpper_mem T' j (hτT' ω), hτjT j ω⟩,
      fun s hs => (Finset.mem_filter.1 hs).2⟩
  choose S hS hST using hrange
  -- the identity at the discretized times, on sets of `𝓕ᵃ_τ ⊆ 𝓕ᵃ_{τ_j}`
  have hj : ∀ j A, MeasurableSet[hτ.measurableSpace] A →
      ∫ ω in A, V (τj j ω) ω ∂μ = ∫ ω in A, Y (τj j ω) ω ∂μ := fun j A hA =>
    setIntegral_stoppedAt_finite (hτj j) (S j) (hS j) (fun s hs => hVi s (hST j s hs))
      (fun s hs => hYi s (hST j s hs)) (fun s hs => hdet s (hST j s hs))
      (hτ.measurableSpace_mono (hτj j) (fun ω => WithTop.coe_le_coe.2 (le_dyadicUpper T' j (τ ω)))
        _ hA)
  -- passage to the limit `j → ∞` (path continuity, domination by `D`)
  have hconv : ∀ W : ℝ → Ω → ℝ, (∀ᵐ ω ∂μ, ContinuousOn (fun t => W t ω) (Set.Icc 0 T)) →
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable (W t) μ) →
      (∀ ω (t : ℝ), t ∈ Set.Icc 0 T → ‖W t ω‖ₑ ≤ D ω) →
      Integrable (fun ω => W (τ ω) ω) μ ∧ ∀ A : Set Ω,
        Tendsto (fun j => ∫ ω in A, W (τj j ω) ω ∂μ) atTop (𝓝 (∫ ω in A, W (τ ω) ω ∂μ)) := by
    intro W hWc hWm hWD
    have hmem : ∀ ω, (τ ω : ℝ) ∈ Set.Icc 0 T := fun ω => ⟨(τ ω).2, hτT ω⟩
    have hmemj : ∀ j ω, (τj j ω : ℝ) ∈ Set.Icc 0 T := fun j ω => ⟨(τj j ω).2, hτjT j ω⟩
    have hlim : ∀ᵐ ω ∂μ, Tendsto (fun j => W (τj j ω) ω) atTop (𝓝 (W (τ ω) ω)) := by
      filter_upwards [hWc] with ω hω
      have h1 : Tendsto (fun j => (τj j ω : ℝ)) atTop (𝓝[Set.Icc 0 T] (τ ω : ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨NNReal.tendsto_coe.2 (tendsto_dyadicUpper T' (τ ω)),
          Eventually.of_forall fun j => hmemj j ω⟩
      exact (hω _ (hmem ω)).tendsto.comp h1
    have hFm : ∀ j, AEStronglyMeasurable (fun ω => W (τj j ω) ω) μ := fun j =>
      aestronglyMeasurable_stoppedAt_finite (hτj j) (S j) (hS j) fun s hs => hWm s (hST j s hs)
    have hfm : AEStronglyMeasurable (fun ω => W (τ ω) ω) μ :=
      aestronglyMeasurable_of_tendsto_ae atTop hFm hlim
    have hFi : ∀ j, Integrable (fun ω => W (τj j ω) ω) μ := fun j =>
      integrable_of_enorm_le_lintegral (hFm j) hdom (ae_of_all _ fun ω => hWD ω _ (hmemj j ω))
    refine ⟨integrable_of_enorm_le_lintegral hfm hdom (ae_of_all _ fun ω => hWD ω _ (hmem ω)),
      fun A => tendsto_setIntegral_of_L1 _ hfm (Eventually.of_forall hFi) ?_ A⟩
    have h2 := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
      (fun ω => 2 * D ω) (fun j => ((hFm j).sub hfm).enorm)
      (fun j => ae_of_all _ fun ω => ?_) ?_ ?_
    · simpa using h2
    · calc ‖W (τj j ω) ω - W (τ ω) ω‖ₑ ≤ ‖W (τj j ω) ω‖ₑ + ‖W (τ ω) ω‖ₑ := enorm_sub_le
        _ ≤ D ω + D ω := add_le_add (hWD ω _ (hmemj j ω)) (hWD ω _ (hmem ω))
        _ = 2 * D ω := (two_mul _).symm
    · rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) hdom
    · filter_upwards [hlim] with ω hω
      simpa using (hω.sub_const (W (τ ω) ω)).enorm
  obtain ⟨hVτi, hVlim⟩ := hconv V hV hVm hDV
  obtain ⟨hYτi, hYlim⟩ := hconv Y hY (fun t ht => (hYm t ht).mono (𝓕.le t)) hDY
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hVτi
    (fun s _ _ => hYτi.integrableOn) (fun A hA _ => ?_)
    (aestronglyMeasurable_stoppedAt hY hYm hτ hτT)).symm
  exact tendsto_nhds_unique (hYlim A) ((hVlim A).congr fun j => hj j A hA)

/-! ### Optional sampling and stopping for processes with the martingale property -/

/-- **Optional sampling** for a process `X` with `𝔼[X_t | 𝓕_s] = X_s` (`s ≤ t ≤ T`), a.s.
continuous paths on `[0, T]` and `𝔼 sup_{[0,T]} |X| < ∞`: `𝔼[X_τ | 𝓕ᵃ_σ] = X_σ` for stopping times
`σ ≤ τ ≤ T` of `𝓕ᵃ` (from `condExp_stopped_of_forall` with `V_t = X_T`, and the tower
property). -/
private lemma condExp_stopped_aux [IsFiniteMeasure μ] {T : ℝ} {X : ℝ → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hdom : ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |X t ω| ∂μ ≠ ∞)
    (hX : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T → μ[X t | 𝓕 s] =ᵐ[μ] X s)
    {σ τ : Ω → ℝ≥0} (hσ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : σ ≤ τ) (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    μ[fun ω => X (τ ω) ω | hσ.measurableSpace] =ᵐ[μ] fun ω => X (σ ω) ω := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ae_of_all _ fun ω => absurd ((τ ω).2.trans (hτT ω)) (not_le.2 hT)
  set T' : ℝ≥0 := ⟨T, hT⟩ with hT'
  have hσT : ∀ ω, (σ ω : ℝ) ≤ T := fun ω => (NNReal.coe_le_coe.2 (hστ ω)).trans (hτT ω)
  have hXT : AEStronglyMeasurable (X T) μ :=
    ((stronglyMeasurable_condExp.mono (𝓕.le T')).aestronglyMeasurable).congr
      (hX T' T' le_rfl le_rfl)
  have hdom' : ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (|X T ω| + |X t ω|) ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (?_ : ∫⁻ ω, 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal |X t ω| ∂μ ≠ ∞) (lintegral_mono fun ω => ?_)
    · rw [lintegral_const_mul' _ _ (by simp)]; exact ENNReal.mul_ne_top (by simp) hdom
    · refine iSup₂_le fun t ht => ?_
      rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), two_mul]
      exact add_le_add (le_iSup₂ (f := fun t _ => ENNReal.ofReal |X t ω|) T ⟨hT, le_rfl⟩)
        (le_iSup₂ (f := fun t _ => ENNReal.ofReal |X t ω|) t ht)
  have key : ∀ {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (ρ ω : WithTop ℝ≥0))),
      (∀ ω, (ρ ω : ℝ) ≤ T) → μ[X T | hρ.measurableSpace] =ᵐ[μ] fun ω => X (ρ ω) ω :=
    fun hρ hρT => condExp_stopped_of_forall (V := fun _ => X T) (Y := X)
      (ae_of_all _ fun _ => continuousOn_const) hc (fun _ _ => hXT) hdom'
      (fun t ht => hX t T' (NNReal.coe_le_coe.1 ht) le_rfl) hρ hρT
  have hστ' : hσ.measurableSpace ≤ hτ.measurableSpace :=
    hσ.measurableSpace_mono hτ fun ω => WithTop.coe_le_coe.2 (hστ ω)
  calc μ[fun ω => X (τ ω) ω | hσ.measurableSpace]
      =ᵐ[μ] μ[μ[X T | hτ.measurableSpace] | hσ.measurableSpace] :=
        condExp_congr_ae (key hτ hτT).symm
    _ =ᵐ[μ] μ[X T | hσ.measurableSpace] := condExp_condExp_of_le hστ' hτ.measurableSpace_le
    _ =ᵐ[μ] fun ω => X (σ ω) ω := key hσ hσT

/-- **Stopped process.** For `X` as in `condExp_stopped_aux` and a stopping time `τ ≤ T` of `𝓕ᵃ`,
`𝔼[X_{t ∧ τ} | 𝓕_s] = X_{s ∧ τ}` for `s ≤ t ≤ T`: on `{τ ≤ s}` both sides are `X_τ`, and
`A ∩ {τ > s} ∈ 𝓕ᵃ_{s ∧ τ}` for `A ∈ 𝓕ᵃ_s`, so optional sampling applies there. -/
private lemma condExp_stopped_min_aux [IsFiniteMeasure μ] {T : ℝ} {X : ℝ → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hdom : ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |X t ω| ∂μ ≠ ∞)
    (hX : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T → μ[X t | 𝓕 s] =ᵐ[μ] X s)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (s t : ℝ≥0) (hst : s ≤ t) (ht : (t : ℝ) ≤ T) :
    μ[fun ω => X (min (t : ℝ) (τ ω)) ω | 𝓕 s] =ᵐ[μ] fun ω => X (min (s : ℝ) (τ ω)) ω := by
  have ecoe : ∀ (r : ℝ≥0) ω, min (r : ℝ) (τ ω : ℝ) = ((min r (τ ω) : ℝ≥0) : ℝ) :=
    fun r ω => (NNReal.coe_min r (τ ω)).symm
  simp only [ecoe]
  have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
  have hρT : ∀ r : ℝ≥0, (r : ℝ) ≤ T → ∀ ω, ((min r (τ ω) : ℝ≥0) : ℝ) ≤ T :=
    fun r hr ω => (NNReal.coe_le_coe.2 (min_le_left _ _)).trans hr
  have hXm : ∀ r : ℝ≥0, (r : ℝ) ≤ T → AEStronglyMeasurable[𝓕 r] (X r) μ :=
    fun r hr => aestronglyMeasurable_of_condExp_eq_self (hX r r le_rfl hr)
  have hint : ∀ r : ℝ≥0, (r : ℝ) ≤ T → Integrable (fun ω => X ((min r (τ ω) : ℝ≥0) : ℝ) ω) μ := by
    intro r hr
    refine integrable_of_enorm_le_lintegral (((aestronglyMeasurable_stoppedAt hc hXm
      (isStoppingTime_nnreal_min hτ r) (hρT r hr))).mono
      (isStoppingTime_nnreal_min hτ r).measurableSpace_le) hdom (ae_of_all _ fun ω => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact le_iSup₂ (f := fun t _ => ENNReal.ofReal |X t ω|) _
      ⟨(min r (τ ω)).2, hρT r hr ω⟩
  have hos := condExp_stopped_aux hc hdom hX (isStoppingTime_nnreal_min hτ s)
    (isStoppingTime_nnreal_min hτ t) (fun ω => min_le_min_right _ hst) (hρT t ht)
  have hsm : AEStronglyMeasurable[nullAug μ 𝓕 s] (fun ω => X ((min s (τ ω) : ℝ≥0) : ℝ) ω) μ :=
    (aestronglyMeasurable_stoppedAt hc hXm (isStoppingTime_nnreal_min hτ s) (hρT s hs)).mono
      ((isStoppingTime_nnreal_min hτ s).measurableSpace_le_of_le_const
        fun ω => WithTop.coe_le_coe.2 (min_le_left s (τ ω)))
  refine (condExp_nullAug _ s).symm.trans (ae_eq_condExp_of_forall_setIntegral_eq
    ((nullAug μ 𝓕).le s) (hint t ht) (fun _ _ _ => (hint s hs).integrableOn)
    (fun A hA _ => ?_) hsm).symm
  have hle : MeasurableSet[nullAug μ 𝓕 s] {ω | τ ω ≤ s} := by
    simpa only [WithTop.coe_le_coe] using hτ s
  have hle' := (nullAug μ 𝓕).le s _ hle
  rw [← integral_inter_add_sdiff hle' ((hint s hs).integrableOn : IntegrableOn _ A μ),
    ← integral_inter_add_sdiff hle' ((hint t ht).integrableOn : IntegrableOn _ A μ)]
  congr 1
  · refine setIntegral_congr_fun (((nullAug μ 𝓕).le s _ hA).inter hle') fun ω hω => ?_
    have h : τ ω ≤ s := hω.2
    rw [min_eq_right h, min_eq_right (h.trans hst)]
  · -- `A \ {τ ≤ s}` is a set of `𝓕ᵃ_{s ∧ τ}`
    have hB𝓖 : MeasurableSet[nullAug μ 𝓕 s] (A \ {ω | τ ω ≤ s}) := hA.diff hle
    have hB : MeasurableSet[(isStoppingTime_nnreal_min hτ s).measurableSpace]
        (A \ {ω | τ ω ≤ s}) := by
      refine ⟨le_iSup (nullAug μ 𝓕) s _ hB𝓖, fun r => ?_⟩
      rcases le_or_gt s r with hsr | hrs
      · have e : (A \ {ω | τ ω ≤ s}) ∩ {ω | ((min s (τ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
            A \ {ω | τ ω ≤ s} :=
          Set.inter_eq_left.2 fun ω _ => WithTop.coe_le_coe.2 ((min_le_left _ _).trans hsr)
        rw [e]; exact (nullAug μ 𝓕).mono hsr _ hB𝓖
      · have e : (A \ {ω | τ ω ≤ s}) ∩ {ω | ((min s (τ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ r} = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
          have h1 : ¬ τ ω ≤ s := hω.1.2
          have h2 : min s (τ ω) ≤ r := WithTop.coe_le_coe.1 hω.2
          rcases min_le_iff.1 h2 with h3 | h3
          · exact absurd h3 (not_le.2 hrs)
          · exact h1 (h3.trans hrs.le)
        rw [e]; exact @MeasurableSet.empty _ (nullAug μ 𝓕 r)
    rw [← setIntegral_condExp (isStoppingTime_nnreal_min hτ s).measurableSpace_le (hint t ht) hB]
    exact setIntegral_congr_ae ((nullAug μ 𝓕).le s _ hB𝓖)
      (by filter_upwards [hos] with ω hω _ using hω.symm)

/-- `𝔼 sup_{[0,T]} M² < ∞` for a continuous `L²` martingale (Doob's `L²` inequality). -/
private lemma IsCL2Mart.lintegral_iSup_sq_ne_top [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) :
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) ∂μ ≠ ∞ := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Set.Icc_eq_empty (not_le.2 hT)]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) ?_) hM.lintegral_iSup_sq_le.2
  have hL2 := hM.memLp ⟨T, hT⟩ le_rfl
  exact ((memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2).lintegral_lt_top.ne

/-- `𝔼 sup_{[0,T]} |M| < ∞` for a continuous `L²` martingale. -/
private lemma IsCL2Mart.lintegral_iSup_abs_ne_top [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) :
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |M t ω| ∂μ ≠ ∞ := by
  have h1 : ∀ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |M t ω| ≤
      1 + ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) := fun ω =>
    iSup₂_le fun t ht => by
      calc ENNReal.ofReal |M t ω| ≤ ENNReal.ofReal (1 + M t ω ^ 2) :=
            ENNReal.ofReal_le_ofReal (by
              nlinarith [sq_nonneg (abs (M t ω) - 1), sq_abs (M t ω), abs_nonneg (M t ω)])
        _ = 1 + ENNReal.ofReal (M t ω ^ 2) := by
            rw [ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one]
        _ ≤ _ := add_le_add le_rfl
            (le_iSup₂ (f := fun t _ => ENNReal.ofReal (M t ω ^ 2)) t ht)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono h1)
  rw [lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const]
  exact ENNReal.add_ne_top.2 ⟨by simp, hM.lintegral_iSup_sq_ne_top⟩

/-- **Optional sampling** for a continuous `L²` martingale on `[0, T]` and two stopping times
`σ ≤ τ ≤ T` of the augmented filtration: `𝔼[M_τ | 𝓕_σ] = M_σ` almost surely. -/
theorem IsCL2Mart.condExp_stopped [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : σ ≤ τ) (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    μ[fun ω => M (τ ω) ω | hσ.measurableSpace] =ᵐ[μ] fun ω => M (σ ω) ω :=
  condExp_stopped_aux hM.cont hM.lintegral_iSup_abs_ne_top hM.condExp hσ hτ hστ hτT

set_option linter.unusedVariables false in
/-- **Stopped martingale.** If `M` is a continuous `L²` martingale on `[0, T]` and `τ ≤ T` is a
stopping time of the augmented filtration, then `t ↦ M_{t ∧ τ}` is a continuous `L²` martingale
on `[0, T]` (for the original filtration `𝓕`). -/
theorem IsCL2Mart.stopped [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    IsCL2Mart T 𝓕 (fun t ω => M (min t (τ ω)) ω) μ := by
  refine ⟨?_, fun t ht => ?_, fun s t hst ht =>
    condExp_stopped_min_aux hM.cont hM.lintegral_iSup_abs_ne_top hM.condExp hτ s t hst ht⟩
  · filter_upwards [hM.cont] with ω hω
    exact hω.comp (continuous_id.min continuous_const).continuousOn
      fun t ht => ⟨le_min ht.1 (τ ω).2, (min_le_left _ _).trans ht.2⟩
  · have ecoe : ∀ ω, min (t : ℝ) (τ ω : ℝ) = ((min t (τ ω) : ℝ≥0) : ℝ) :=
      fun ω => (NNReal.coe_min t (τ ω)).symm
    simp only [ecoe]
    have hρT : ∀ ω, ((min t (τ ω) : ℝ≥0) : ℝ) ≤ T :=
      fun ω => (NNReal.coe_le_coe.2 (min_le_left _ _)).trans ht
    have hm : AEStronglyMeasurable (fun ω => M ((min t (τ ω) : ℝ≥0) : ℝ) ω) μ :=
      (aestronglyMeasurable_stoppedAt hM.cont
        (fun r hr => aestronglyMeasurable_of_condExp_eq_self (hM.condExp r r le_rfl hr))
        (isStoppingTime_nnreal_min hτ t) hρT).mono
        (isStoppingTime_nnreal_min hτ t).measurableSpace_le
    rw [memLp_two_iff_integrable_sq hm]
    refine integrable_of_enorm_le_lintegral (hm.pow 2) hM.lintegral_iSup_sq_ne_top
      (ae_of_all _ fun ω => ?_)
    rw [Real.enorm_eq_ofReal (sq_nonneg _)]
    exact le_iSup₂ (f := fun t _ => ENNReal.ofReal (M t ω ^ 2)) _
      ⟨(min t (τ ω)).2, hρT ω⟩

/-- **Stopped bracket.** If `⟨M⟩ = A` on `[0, T]` and `τ ≤ T` is a stopping time of the
augmented filtration, then `⟨M_{· ∧ τ}⟩ = A_{· ∧ τ}` on `[0, T]` (for the original filtration
`𝓕`). -/
theorem HasBracket.stopped [IsFiniteMeasure μ] {T : ℝ} {M A : ℝ → Ω → ℝ}
    (h : HasBracket T 𝓕 M A μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    HasBracket T 𝓕 (fun t ω => M (min t (τ ω)) ω) (fun t ω => A (min t (τ ω)) ω) μ := by
  have hM := h.toIsCL2Mart
  -- `0 ≤ A_t ≤ A_T` on `[0, T]`
  have hA : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ A t ω ∧ A t ω ≤ A T ω := by
    filter_upwards [h.zero, h.mono] with ω h0 hmono t ht
    exact ⟨h0.symm.trans_le (hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1),
      hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2⟩
  -- `X = M² - A` has the martingale property and `𝔼 sup_{[0,T]} |X| < ∞`
  set X : ℝ → Ω → ℝ := fun r ω => M r ω ^ 2 - A r ω with hXdef
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T) := by
    filter_upwards [hM.cont, h.cont_bracket] with ω h1 h2 using (h1.pow 2).sub h2
  have hXdom : ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal |X t ω| ∂μ ≠ ∞ := by
    rcases lt_or_ge T 0 with hT | hT
    · simp [Set.Icc_eq_empty (not_le.2 hT)]
    have hAT : Integrable (A T) μ := h.integrable_bracket ⟨T, hT⟩ le_rfl
    refine ne_top_of_le_ne_top (?_ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (M t ω ^ 2)) + ENNReal.ofReal (A T ω) ∂μ ≠ ∞) (lintegral_mono_ae ?_)
    · rw [lintegral_add_right' _ hAT.aemeasurable.ennreal_ofReal]
      exact ENNReal.add_ne_top.2 ⟨hM.lintegral_iSup_sq_ne_top, hAT.lintegral_lt_top.ne⟩
    · filter_upwards [hA] with ω hω
      refine iSup₂_le fun t ht => ?_
      calc ENNReal.ofReal |X t ω| ≤ ENNReal.ofReal (M t ω ^ 2 + A T ω) := by
            refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩) <;>
              nlinarith [sq_nonneg (M t ω), (hω t ht).1, (hω t ht).2]
        _ = ENNReal.ofReal (M t ω ^ 2) + ENNReal.ofReal (A T ω) :=
            ENNReal.ofReal_add (sq_nonneg _) ((hω t ht).1.trans (hω t ht).2)
        _ ≤ _ := add_le_add (le_iSup₂ (f := fun t _ => ENNReal.ofReal (M t ω ^ 2)) t ht) le_rfl
  have hXm : ∀ r : ℝ≥0, (r : ℝ) ≤ T → AEStronglyMeasurable[𝓕 r] (X r) μ :=
    fun r hr => aestronglyMeasurable_of_condExp_eq_self (h.condExp_sq r r le_rfl hr)
  have hMm : ∀ r : ℝ≥0, (r : ℝ) ≤ T → AEStronglyMeasurable[𝓕 r] (M r) μ :=
    fun r hr => aestronglyMeasurable_of_condExp_eq_self (hM.condExp r r le_rfl hr)
  refine
    { toIsCL2Mart := hM.stopped hτ hτT
      integrable_bracket := fun t ht => ?_
      zero := ?_
      mono := ?_
      cont_bracket := ?_
      condExp_sq := fun s t hst ht =>
        condExp_stopped_min_aux hXc hXdom h.condExp_sq hτ s t hst ht }
  · rcases lt_or_ge T 0 with hT | hT
    · exact absurd (t.2.trans ht) (not_le.2 hT)
    have ecoe : ∀ ω, min (t : ℝ) (τ ω : ℝ) = ((min t (τ ω) : ℝ≥0) : ℝ) :=
      fun ω => (NNReal.coe_min t (τ ω)).symm
    simp only [ecoe]
    have hρT : ∀ ω, ((min t (τ ω) : ℝ≥0) : ℝ) ≤ T :=
      fun ω => (NNReal.coe_le_coe.2 (min_le_left _ _)).trans ht
    have hρ := isStoppingTime_nnreal_min hτ t
    have h1 := (aestronglyMeasurable_stoppedAt hM.cont hMm hρ hρT).mono hρ.measurableSpace_le
    have h2 := (aestronglyMeasurable_stoppedAt hXc hXm hρ hρT).mono hρ.measurableSpace_le
    have hm : AEStronglyMeasurable (fun ω => A ((min t (τ ω) : ℝ≥0) : ℝ) ω) μ :=
      ((h1.pow 2).sub h2).congr (ae_of_all _ fun ω => by simp [X])
    refine (h.integrable_bracket ⟨T, hT⟩ le_rfl).mono' hm ?_
    filter_upwards [hA] with ω hω
    have hmem : ((min t (τ ω) : ℝ≥0) : ℝ) ∈ Set.Icc 0 T := ⟨(min t (τ ω)).2, hρT ω⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hω _ hmem).1]
    exact (hω _ hmem).2
  · filter_upwards [h.zero] with ω h0
    convert h0 using 2
    exact min_eq_left (τ ω).2
  · filter_upwards [h.mono] with ω hω a ha b hb hab
    exact hω ⟨le_min ha.1 (τ ω).2, (min_le_left _ _).trans ha.2⟩
      ⟨le_min hb.1 (τ ω).2, (min_le_left _ _).trans hb.2⟩ (min_le_min_right _ hab)
  · filter_upwards [h.cont_bracket] with ω hω
    exact hω.comp (continuous_id.min continuous_const).continuousOn
      fun t ht => ⟨le_min ht.1 (τ ω).2, (min_le_left _ _).trans ht.2⟩

end QSSEPtoKPZ
