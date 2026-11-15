/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Integrands
public import QSSEPtoKPZ.Martingales.Stopping

/-!
# Stopping the Itô integral; pulling out known factors (package C, task C5)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces, proved by
task C5. See `docs/stage2-design.md`, Section 2.2 ("Stopping"), and
`docs/stage2-interfaces.md`.

* `stochInt_indicator_stoppingTime`: `I_t(h 𝟙_{[0,τ]}) = I_{t ∧ τ}(h)`.
* `stochInt_mul_indicator_gt`: `I_t(ξ 𝟙_{(u,∞)} h) = ξ (I_t(h) - I_{t ∧ u}(h))` for `ξ` bounded
  and `𝓖_u`-measurable.

Both are proved at a fixed time `t`, then for all `t` at once by continuity of the paths
(`IsItoIntegrable.indicator_stoppingTime`, `IsItoIntegrable.mul_indicator_gt` give the
integrability).

* Stopping, with `σ = t ∧ τ` and `g = h 𝟙_{s > τ}` (so `I(h) = I(h 𝟙_{s ≤ τ}) + I(g)`): optional
  sampling for the martingale `I(f)² - ⟨I(f)⟩` (`HasBracket.stopped`) gives
  `𝔼 I_σ(f)² = 𝔼 ∫_0^σ ∑ᵢ fᵢ²`. With `f = g` the right side is `0`, so `I_σ(g) = 0`. With
  `f = h 𝟙_{s ≤ τ}`, `𝔼 I_σ(f)² = 𝔼 I_t(f)²`, and `𝔼[I_t(f) | 𝓖_σ] = I_σ(f)` (optional
  sampling), so `𝔼 (I_t(f) - I_σ(f))² = 0`.
* Known factor: for an elementary `e`, `ξ 𝟙_{s > u} e` is elementary (blocks cut at `u`), and
  its elementary integral is `ξ (I_t(e) - I_{t ∧ u}(e))` for every `ω`; pass to the `L²` limit
  along an approximating sequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-! ### Generic facts -/

omit [IsProbabilityMeasure μ] in
/-- Two processes with almost surely continuous paths on `[0, ∞)` that are almost surely equal at
each fixed time are almost surely equal at all times (equality on a countable dense set). -/
private lemma stopInt_ae_forall_of_continuous {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, Continuous fun t => X t ω) (hY : ∀ᵐ ω ∂μ, Continuous fun t => Y t ω)
    (h : ∀ t, X t =ᵐ[μ] Y t) : ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD : ∀ᵐ ω ∂μ, ∀ t ∈ D, X t ω = Y t ω := (ae_ball_iff hDc).2 fun t _ => h t
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω t
  exact congrFun (Continuous.ext_on hDd hXω hYω hDω) t

/-- **Orthogonality.** If `a, b ∈ L²`, `𝔼[a | 𝓜] = b` and `𝔼[a²] = 𝔼[b²]`, then `a = b` almost
surely (since `𝔼[(a - b)²] = 𝔼[a²] - 𝔼[b²]`). -/
private lemma stopInt_ae_eq_of_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {a b : Ω → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hab : μ[a | m] =ᵐ[μ] b)
    (hsq : ∫ ω, a ω ^ 2 ∂μ = ∫ ω, b ω ^ 2 ∂μ) : a =ᵐ[μ] b := by
  have hbm : AEStronglyMeasurable[m] b μ := ⟨_, stronglyMeasurable_condExp, hab.symm⟩
  have hint : Integrable (a * b) μ := ha.integrable_mul hb
  have hcross : ∫ ω, a ω * b ω ∂μ = ∫ ω, b ω ^ 2 ∂μ := by
    have h1 := condExp_mul_of_aestronglyMeasurable_right hbm hint (ha.integrable one_le_two)
    calc ∫ ω, a ω * b ω ∂μ = ∫ ω, (μ[a * b | m]) ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, (μ[a | m] * b) ω ∂μ := integral_congr_ae h1
      _ = ∫ ω, b ω ^ 2 ∂μ := integral_congr_ae (by
          filter_upwards [hab] with ω hω
          simp [hω, sq])
  have ha2 := ha.integrable_sq
  have hb2 := hb.integrable_sq
  have hzero : ∫ ω, (a ω - b ω) ^ 2 ∂μ = 0 := by
    have e : (fun ω => (a ω - b ω) ^ 2) = fun ω => (a ω ^ 2 + b ω ^ 2) - 2 * (a ω * b ω) := by
      funext ω; ring
    have hint' : Integrable (fun ω => 2 * (a ω * b ω)) μ := hint.const_mul 2
    rw [e, integral_sub (f := fun ω => a ω ^ 2 + b ω ^ 2) (ha2.add hb2) hint',
      integral_add ha2 hb2, integral_const_mul, hcross, hsq]
    ring
  have hint2 : Integrable (fun ω => (a ω - b ω) ^ 2) μ := (ha.sub hb).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (a ω - b ω)) hint2).1 hzero
  filter_upwards [h0] with ω hω
  have : (a ω - b ω) ^ 2 = 0 := hω
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- **Itô isometry at a bounded stopping time.** For an Itô-integrable `f` and a stopping time
`σ ≤ t`: `I_σ(f) ∈ L²` and `𝔼[I_σ(f)²] = 𝔼 ∫_0^σ ∑ᵢ fᵢ(s)² ds` (optional sampling for the
martingale `I(f)² - ⟨I(f)⟩`, via `HasBracket.stopped`). -/
private lemma stopInt_stopped_sq (hB : IsBrownianFamily 𝓖 B μ) {f : ι → ℝ → Ω → ℝ}
    (hf : IsItoIntegrable 𝓖 μ f) {t : ℝ≥0} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓖 (fun ω => (σ ω : WithTop ℝ≥0))) (hσt : ∀ ω, σ ω ≤ t) :
    MemLp (fun ω => stochInt 𝓖 μ B f (σ ω) ω) 2 μ ∧
      ∫ ω, stochInt 𝓖 μ B f (σ ω) ω ^ 2 ∂μ =
        ∫ ω, (∫ s in (0 : ℝ)..(σ ω), ∑' i, f i s ω ^ 2) ∂μ := by
  have hσN : IsStoppingTime (nullAug μ 𝓖) (fun ω => (σ ω : WithTop ℝ≥0)) :=
    fun r => le_nullAug μ 𝓖 r _ (hσ r)
  have hS := (hasBracket_stochInt hB hf t).stopped hσN (fun ω => NNReal.coe_le_coe.2 (hσt ω))
  have e : ∀ ω, min (t : ℝ) (σ ω : ℝ) = σ ω := fun ω =>
    min_eq_right (NNReal.coe_le_coe.2 (hσt ω))
  have e0 : ∀ ω, min ((0 : ℝ≥0) : ℝ) (σ ω : ℝ) = 0 := fun ω => by simp
  have h1 := hS.memLp t le_rfl
  have h2 := hS.integrable_bracket t le_rfl
  have h3 := hS.condExp_sq 0 t zero_le le_rfl
  simp only [e, e0] at h1 h2 h3
  refine ⟨h1, ?_⟩
  have h4 := integral_congr_ae h3
  rw [integral_condExp (𝓖.le 0)] at h4
  simp only [stochInt_of_nonpos B f le_rfl, intervalIntegral.integral_same] at h4
  rw [integral_sub h1.integrable_sq h2] at h4
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self,
    integral_zero] at h4
  linarith

/-! ### Stopping -/

/-- **Stopping.** If `h` is Itô-integrable and `τ` is a stopping time of `𝓖`, then almost
surely, for all `t ≥ 0`, `I_t(h 𝟙_{s ≤ τ}) = I_{t ∧ τ}(h)`. -/
theorem stochInt_indicator_stoppingTime (hB : IsBrownianFamily 𝓖 B μ)
    {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then h i s ω else 0) t ω =
        stochInt 𝓖 μ B h ((min t (τ ω) : ℝ≥0) : ℝ) ω := by
  have hY : IsItoIntegrable 𝓖 μ (fun i s ω => if s ≤ τ ω then h i s ω else 0) :=
    hh.indicator_stoppingTime hτ
  -- the complementary integrand `g = h 𝟙_{s > τ}`
  obtain ⟨g, hgdef⟩ : ∃ g : ι → ℝ → Ω → ℝ, g = fun i (s : ℝ) ω => if s ≤ τ ω then 0 else h i s ω :=
    ⟨_, rfl⟩
  have hg : IsItoIntegrable 𝓖 μ g := by
    have e : g = fun i (s : ℝ) ω => h i s ω + -1 * (if s ≤ τ ω then h i s ω else 0) := by
      rw [hgdef]; funext i s ω; split_ifs <;> ring
    rw [e]
    exact hh.add (hY.const_mul (-1))
  have hsum : (fun i (s : ℝ) ω => (if s ≤ τ ω then h i s ω else 0) + g i s ω) = h := by
    rw [hgdef]; funext i s ω; by_cases hs : s ≤ τ ω <;> simp [hs]
  have hadd := stochInt_add hB hY hg
  rw [hsum] at hadd
  have hfix : ∀ t : ℝ≥0,
      (fun ω => stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then h i s ω else 0) t ω) =ᵐ[μ]
        fun ω => stochInt 𝓖 μ B h ((min t (τ ω) : ℝ≥0) : ℝ) ω := by
    intro t
    set σ : Ω → ℝ≥0 := fun ω => min t (τ ω) with hσdef
    have hσ : IsStoppingTime 𝓖 (fun ω => (σ ω : WithTop ℝ≥0)) := isStoppingTime_nnreal_min hτ t
    have hσt : ∀ ω, σ ω ≤ t := fun ω => min_le_left _ _
    have hστ : ∀ ω, (σ ω : ℝ) ≤ τ ω := fun ω => NNReal.coe_le_coe.2 (min_le_right _ _)
    -- `I_σ(g) = 0`: its bracket vanishes up to `σ ≤ τ`
    have hD : ∀ᵐ ω ∂μ, stochInt 𝓖 μ B g (σ ω) ω = 0 := by
      obtain ⟨hm, heq⟩ := stopInt_stopped_sq hB hg hσ hσt
      have hz : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ∑' i, g i s ω ^ 2 = 0 := by
        intro ω
        refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_).trans
          intervalIntegral.integral_zero
        rw [Set.uIcc_of_le (NNReal.coe_nonneg _)] at hs
        have : s ≤ τ ω := hs.2.trans (hστ ω)
        simp [hgdef, this]
      simp only [hz, integral_zero] at heq
      have h0 := (integral_eq_zero_iff_of_nonneg
        (fun ω => sq_nonneg (stochInt 𝓖 μ B g (σ ω) ω)) hm.integrable_sq).1 heq
      filter_upwards [h0] with ω hω
      have : stochInt 𝓖 μ B g (σ ω) ω ^ 2 = 0 := hω
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    -- `I_t(h 𝟙_{s ≤ τ}) = I_σ(h 𝟙_{s ≤ τ})`: optional sampling and equal brackets
    have hYt : (fun ω => stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then h i s ω else 0) t ω)
        =ᵐ[μ] fun ω =>
          stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then h i s ω else 0) (σ ω) ω := by
      obtain ⟨hma, hia⟩ := stopInt_stopped_sq hB hY (σ := fun _ => t)
        (isStoppingTime_const 𝓖 t) (fun _ => le_rfl)
      obtain ⟨hmb, hib⟩ := stopInt_stopped_sq hB hY hσ hσt
      have hσN : IsStoppingTime (nullAug μ 𝓖) (fun ω => (σ ω : WithTop ℝ≥0)) :=
        fun r => le_nullAug μ 𝓖 r _ (hσ r)
      have htN : IsStoppingTime (nullAug μ 𝓖)
          (fun ω => (((fun _ => t) ω : ℝ≥0) : WithTop ℝ≥0)) :=
        isStoppingTime_const _ t
      have hc := (hasBracket_stochInt hB hY t).toIsCL2Mart.condExp_stopped hσN htN
        (fun ω => hσt ω) (fun _ => le_rfl)
      refine stopInt_ae_eq_of_condExp hσN.measurableSpace_le hma hmb hc ?_
      rw [hia, hib]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
        intervalIntegral.integral_of_le (NNReal.coe_nonneg (σ ω))]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
        (Set.Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (hσt ω))) fun s hs => ?_
      have hsτ : ¬ s ≤ τ ω := by
        intro hsτ
        refine hs.2 ⟨hs.1.1, ?_⟩
        rw [hσdef, NNReal.coe_min]
        exact le_min hs.1.2 hsτ
      simp [hsτ]
    filter_upwards [hD, hYt, hadd] with ω h1 h2 h3
    rw [h2, h3 (σ ω), h1, add_zero]
  refine stopInt_ae_forall_of_continuous
    (X := fun t ω => stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then h i s ω else 0) t ω)
    (Y := fun t ω => stochInt 𝓖 μ B h ((min t (τ ω) : ℝ≥0) : ℝ) ω)
    (stochInt_continuous hB hY) ?_ hfix
  filter_upwards [stochInt_continuous hB hh] with ω hω
  exact hω.comp (continuous_id.min continuous_const)

/-! ### Pulling out a known factor -/

/-- The block `η 𝟙_{(a,b]} eᵢ` cut at time `u` and multiplied by `c`:
`c η 𝟙_{(a ∨ u, b ∨ u]} eᵢ`, i.e. `c 𝟙_{s > u} η 𝟙_{(a,b]}(s) eᵢ`. -/
private def stopIntBlockAfter (u : ℝ≥0) (c : Ω → ℝ) (hc : Measurable[𝓖 u] c)
    (hcb : ∃ C, ∀ ω, |c ω| ≤ C) (bl : ElemBlock 𝓖 ι) : ElemBlock 𝓖 ι where
  a := max bl.a u
  b := max bl.b u
  le := max_le_max bl.le le_rfl
  i := bl.i
  ξ := fun ω => c ω * bl.ξ ω
  meas := (hc.mono (𝓖.mono (le_max_right _ _)) le_rfl).mul
    (bl.meas.mono (𝓖.mono (le_max_left _ _)) le_rfl)
  bdd := by
    obtain ⟨C, hC⟩ := hcb
    obtain ⟨C', hC'⟩ := bl.bdd
    exact ⟨C * C', fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))⟩

omit [Countable ι] [IsProbabilityMeasure μ] in
open Classical in
/-- The family represented by the cut blocks is `c 𝟙_{s > u} e`. -/
private lemma stopInt_toFun_after (u : ℝ≥0) (c : Ω → ℝ) (hc : Measurable[𝓖 u] c)
    (hcb : ∃ C, ∀ ω, |c ω| ≤ C) (e : ElemIntegrand 𝓖 ι) (i : ι) (s : ℝ) (ω : Ω) :
    ElemIntegrand.toFun (e.map (stopIntBlockAfter u c hc hcb)) i s ω =
      if (u : ℝ) < s then c ω * e.toFun i s ω else 0 := by
  unfold ElemIntegrand.toFun
  rw [List.map_map]
  split_ifs with hs
  · rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun bl _ => ?_
    simp only [Function.comp_apply, stopIntBlockAfter, NNReal.coe_max, max_lt_iff, le_max_iff]
    by_cases h1 : bl.i = i <;> by_cases h2 : (bl.a : ℝ) < s <;> by_cases h3 : s ≤ bl.b <;>
      simp [h1, h2, h3, hs, not_le.2 hs]
  · have : ∀ bl ∈ e, ((fun bl : ElemBlock 𝓖 ι =>
        if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0) ∘
          stopIntBlockAfter u c hc hcb) bl = 0 := fun bl _ => by
      have : ¬ ((max bl.a u : ℝ≥0) : ℝ) < s := by
        rw [NNReal.coe_max]
        exact fun h => hs ((le_max_right _ _).trans_lt h)
      simp [Function.comp_apply, stopIntBlockAfter, hs]
    rw [List.map_congr_left this]
    simp

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- The elementary integral of the cut blocks is `c (I_t(e) - I_{t ∧ u}(e))`, for every `ω`. -/
private lemma stopInt_integral_after (u : ℝ≥0) (c : Ω → ℝ) (hc : Measurable[𝓖 u] c)
    (hcb : ∃ C, ∀ ω, |c ω| ≤ C) (e : ElemIntegrand 𝓖 ι) (t : ℝ) (ω : Ω) :
    ElemIntegrand.integral (e.map (stopIntBlockAfter u c hc hcb)) B t ω =
      c ω * (e.integral B t ω - e.integral B (min t u) ω) := by
  induction e with
  | nil => simp [ElemIntegrand.integral]
  | cons bl e ih =>
    simp only [ElemIntegrand.integral, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have key : ∀ x : ℝ≥0, B bl.i (min t ((max x u : ℝ≥0) : ℝ)) ω =
        B bl.i (min t x) ω + B bl.i (min t u) ω - B bl.i (min (min t u) x) ω := by
      intro x
      rw [NNReal.coe_max]
      rcases le_total (x : ℝ) u with hx | hx
      · rw [max_eq_right hx, min_assoc, min_eq_right hx]; ring
      · rw [max_eq_left hx, min_eq_left ((min_le_right t u).trans hx)]; ring
    simp only [stopIntBlockAfter]
    rw [key bl.b, key bl.a]
    ring

/-- `L²` convergence at a fixed time `r ∈ [0, T]`, from the uniform one. -/
private lemma stopInt_tendsto_fixed (hB : IsBrownianFamily 𝓖 B μ) {f : ℕ → ι → ℝ → Ω → ℝ}
    {g : ι → ℝ → Ω → ℝ} (hf : ∀ n, IsItoIntegrable 𝓖 μ (f n)) (hg : IsItoIntegrable 𝓖 μ g)
    {T : ℝ} (hlim : Tendsto (fun n => energy μ (fun i s ω => f n i s ω - g i s ω) T) atTop (𝓝 0))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
      ((stochInt 𝓖 μ B (f n) r ω - stochInt 𝓖 μ B g r ω) ^ 2) ∂μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_lintegral_iSup_stochInt_sub hB hf hg hlim) (fun _ => zero_le) fun n =>
      lintegral_mono fun ω => le_iSup₂ (f := fun r' (_ : r' ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal ((stochInt 𝓖 μ B (f n) r' ω - stochInt 𝓖 μ B g r' ω) ^ 2)) r hr

/-- **Pulling out a known factor.** If `h` is Itô-integrable and `ξ` is bounded and
`𝓖_u`-measurable, then almost surely, for all `t ≥ 0`,
`I_t(ξ 𝟙_{s > u} h) = ξ (I_t(h) - I_{t ∧ u}(h))`. -/
theorem stochInt_mul_indicator_gt (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) {u : ℝ≥0} {ξ : Ω → ℝ} (hξ : Measurable[𝓖 u] ξ)
    (hξb : ∃ C, ∀ ω, |ξ ω| ≤ C) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      stochInt 𝓖 μ B (fun i s ω => if (u : ℝ) < s then ξ ω * h i s ω else 0) t ω =
        ξ ω * (stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h ((min t u : ℝ≥0) : ℝ) ω) := by
  obtain ⟨C, hC⟩ := hξb
  have hξ2 : ∀ ω, ξ ω ^ 2 ≤ C ^ 2 := fun ω => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2
  obtain ⟨k, hkdef⟩ : ∃ k : ι → ℝ → Ω → ℝ,
      k = fun i s ω => if (u : ℝ) < s then ξ ω * h i s ω else 0 := ⟨_, rfl⟩
  rw [← hkdef]
  have hk : IsItoIntegrable 𝓖 μ k := hkdef ▸ hh.mul_indicator_gt hξ ⟨C, hC⟩
  obtain ⟨E, hE⟩ := hh.approx
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ElemIntegrand 𝓖 ι,
      F = fun n => (E n).map (stopIntBlockAfter u ξ hξ ⟨C, hC⟩) := ⟨_, rfl⟩
  -- `F n = ξ 𝟙_{s > u} E n → k` for the energy
  have hFk : ∀ T, Tendsto (fun n => energy μ (fun i s ω => (F n).toFun i s ω - k i s ω) T)
      atTop (𝓝 0) := by
    intro T
    have hle : ∀ n, energy μ (fun i s ω => (F n).toFun i s ω - k i s ω) T ≤
        ENNReal.ofReal (C ^ 2) * energy μ (fun i s ω => (E n).toFun i s ω - h i s ω) T :=
      fun n => itoEnergy_le_mul ENNReal.ofReal_ne_top fun ω s _ _ => by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [hFdef, hkdef]
        simp only
        rw [stopInt_toFun_after, itoEnergy_enorm_sq, itoEnergy_enorm_sq,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        split_ifs
        · rw [← mul_sub, mul_pow]
          exact mul_le_mul_of_nonneg_right (hξ2 ω) (sq_nonneg _)
        · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
          positivity
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (C ^ 2)) (hE T)
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) hle
  have hm : ∀ (f : ι → ℝ → Ω → ℝ) (r : ℝ≥0), Measurable (stochInt 𝓖 μ B f r) :=
    fun f r => (stochInt_adapted hB f r).mono (𝓖.le r) le_rfl
  have hmq : ∀ a b : Ω → ℝ, Measurable a → Measurable b →
      Measurable fun ω => ENNReal.ofReal ((a ω - b ω) ^ 2) :=
    fun a b ha hb => ENNReal.measurable_ofReal.comp ((ha.sub hb).pow_const 2)
  have hfix : ∀ t : ℝ≥0, (fun ω => stochInt 𝓖 μ B k t ω) =ᵐ[μ]
      fun ω => ξ ω * (stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h ((min t u : ℝ≥0) : ℝ) ω) := by
    intro t
    set tu : ℝ≥0 := min t u with htu_def
    have htt : (t : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨NNReal.coe_nonneg _, le_rfl⟩
    have htu : (tu : ℝ) ∈ Set.Icc (0 : ℝ) t :=
      ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_left _ _)⟩
    have hA := stopInt_tendsto_fixed (B := B) hB (f := fun n => (F n).toFun)
      (fun n => isItoIntegrable_elem (F n)) hk (hFk t) htt
    have hB1 := stopInt_tendsto_fixed (B := B) hB (f := fun n => (E n).toFun)
      (fun n => isItoIntegrable_elem (E n)) hh (hE t) htt
    have hB2 := stopInt_tendsto_fixed (B := B) hB (f := fun n => (E n).toFun)
      (fun n => isItoIntegrable_elem (E n)) hh (hE t) htu
    set c3 : ℝ≥0∞ := ENNReal.ofReal (3 * C ^ 2) with hc3
    set Q := ∫⁻ ω, ENNReal.ofReal ((stochInt 𝓖 μ B k t ω -
      ξ ω * (stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h tu ω)) ^ 2) ∂μ with hQ
    have hbound : ∀ n, Q ≤
        ENNReal.ofReal 3 * ∫⁻ ω, ENNReal.ofReal
          ((stochInt 𝓖 μ B (F n).toFun t ω - stochInt 𝓖 μ B k t ω) ^ 2) ∂μ +
        c3 * ∫⁻ ω, ENNReal.ofReal
          ((stochInt 𝓖 μ B (E n).toFun t ω - stochInt 𝓖 μ B h t ω) ^ 2) ∂μ +
        c3 * ∫⁻ ω, ENNReal.ofReal
          ((stochInt 𝓖 μ B (E n).toFun tu ω - stochInt 𝓖 μ B h tu ω) ^ 2) ∂μ := by
      intro n
      rw [← lintegral_const_mul _ (hmq _ _ (hm _ _) (hm _ _)),
        ← lintegral_const_mul _ (hmq _ _ (hm _ _) (hm _ _)),
        ← lintegral_const_mul _ (hmq _ _ (hm _ _) (hm _ _)),
        ← lintegral_add_left (((hmq _ _ (hm _ _) (hm _ _))).const_mul _),
        ← lintegral_add_right _ (((hmq _ _ (hm _ _) (hm _ _))).const_mul _)]
      refine lintegral_mono_ae ?_
      filter_upwards [stochInt_elem hB (F n), stochInt_elem hB (E n)] with ω h1 h2
      have e1 : stochInt 𝓖 μ B (F n).toFun t ω = ξ ω * (stochInt 𝓖 μ B (E n).toFun t ω -
          stochInt 𝓖 μ B (E n).toFun tu ω) := by
        rw [h1 t, h2 t, h2 tu, hFdef]
        simp only
        rw [stopInt_integral_after, htu_def, NNReal.coe_min]
      rw [e1]
      set X := stochInt 𝓖 μ B k t ω
      set p1 := stochInt 𝓖 μ B (E n).toFun t ω
      set p2 := stochInt 𝓖 μ B (E n).toFun tu ω
      set q1 := stochInt 𝓖 μ B h t ω
      set q2 := stochInt 𝓖 μ B h tu ω
      have hd1 : (ξ ω * (p1 - q1)) ^ 2 ≤ C ^ 2 * (p1 - q1) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hξ2 ω) (sq_nonneg _)
      have hd2 : (ξ ω * (p2 - q2)) ^ 2 ≤ C ^ 2 * (p2 - q2) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hξ2 ω) (sq_nonneg _)
      have hsq : (X - ξ ω * (q1 - q2)) ^ 2 ≤ 3 * (ξ ω * (p1 - p2) - X) ^ 2 +
          3 * C ^ 2 * (p1 - q1) ^ 2 + 3 * C ^ 2 * (p2 - q2) ^ 2 := by
        set a := ξ ω * (p1 - p2) - X
        set d1 := ξ ω * (p1 - q1)
        set d2 := ξ ω * (p2 - q2)
        have e : X - ξ ω * (q1 - q2) = d1 - d2 - a := by
          simp only [a, d1, d2]; ring
        rw [e]
        nlinarith [sq_nonneg (d1 + d2), sq_nonneg (d1 + a), sq_nonneg (a - d2)]
      rw [hc3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal (hsq.trans (le_of_eq ?_))
      ring
    have hlim : Tendsto (fun n =>
        ENNReal.ofReal 3 * ∫⁻ ω, ENNReal.ofReal
          ((stochInt 𝓖 μ B (F n).toFun t ω - stochInt 𝓖 μ B k t ω) ^ 2) ∂μ +
        c3 * ∫⁻ ω, ENNReal.ofReal
          ((stochInt 𝓖 μ B (E n).toFun t ω - stochInt 𝓖 μ B h t ω) ^ 2) ∂μ +
        c3 * ∫⁻ ω, ENNReal.ofReal
          ((stochInt 𝓖 μ B (E n).toFun tu ω - stochInt 𝓖 μ B h tu ω) ^ 2) ∂μ)
        atTop (𝓝 0) := by
      have := ((ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 3) hA
        (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.const_mul (a := c3) hB1 (Or.inr ENNReal.ofReal_ne_top))).add
        (ENNReal.Tendsto.const_mul (a := c3) hB2 (Or.inr ENNReal.ofReal_ne_top))
      simpa using this
    have hQ0 : Q = 0 := le_antisymm (ge_of_tendsto' hlim hbound) zero_le
    have hmY : Measurable fun ω =>
        ξ ω * (stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h tu ω) :=
      (hξ.mono (𝓖.le u) le_rfl).mul ((hm _ _).sub (hm _ _))
    rw [hQ, lintegral_eq_zero_iff (hmq _ _ (hm _ _) hmY)] at hQ0
    filter_upwards [hQ0] with ω hω
    have h1 : (stochInt 𝓖 μ B k t ω -
        ξ ω * (stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h tu ω)) ^ 2 ≤ 0 :=
      ENNReal.ofReal_eq_zero.1 hω
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h1 (sq_nonneg _)))
  refine stopInt_ae_forall_of_continuous (X := fun t ω => stochInt 𝓖 μ B k t ω)
    (Y := fun t ω =>
      ξ ω * (stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B h ((min t u : ℝ≥0) : ℝ) ω))
    (stochInt_continuous hB hk) ?_ hfix
  filter_upwards [stochInt_continuous hB hh] with ω hω
  exact continuous_const.mul (hω.sub (hω.comp (continuous_id.min continuous_const)))

end QSSEPtoKPZ
