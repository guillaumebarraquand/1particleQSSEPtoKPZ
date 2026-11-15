/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.ConvQ
public import QSSEPtoKPZ.LimitPoints.HitLevel

/-!
# Proposition 7.1 (3): the bracket functional on the path space (task Q4)

Auxiliary results for `IsLimCoupling.hasBracket` (`Prop71Bracket.lean`), on the path space
`C([0,T], ℳ₊)`:
* `limBrGood ρ T`: the measurable set of paths `γ` with `∫_0^T ∫ Z(t,x)² dx dt < ∞`, where
  `Z(t,·) = limDensity ρ (γ(t))`; on it, `Q(t) = ∫_0^t ∫ Z(s,x)² φ_s(x)² dx ds` (the process
  (7.3), `limBracket`) is continuous and nondecreasing on `[0,T]`
  (`limBr_continuousOn_monotoneOn`);
* `limBrMod ρ φ`: `Q` modified to `0` off `limBrGood ρ T`, continuous and nondecreasing for every
  path, which is what `hasBracket_map_iff` needs;
* `limBr_hasBracket_map_iff`: transfer of the bracket (7.3) between a random path `Y` and the
  canonical space, when `Y ∈ limBrGood ρ T` almost surely;
* `limBr_measurable_can`: `Q(t)` is measurable for the canonical filtration at time `t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Interval

noncomputable section

namespace QSSEPtoKPZ

variable {T : ℝ}

/-- The paths `γ` with `∫_0^T ∫ Z(t,x)² dx dt < ∞`, `Z(t,·) = limDensity ρ (γ(t))` (the set where
(7.1) holds pathwise). -/
def limBrGood (ρ : ℝ → ℝ) (T : ℝ) : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  {γ | ∫⁻ t in Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ t) x ^ 2) < ⊤}

/-- The process (7.3) on the path space, modified to be `0` off `limBrGood ρ T`. -/
def limBrMod (ρ : ℝ → ℝ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ℝ :=
  (limBrGood ρ T).indicator
    (limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t) γ

variable {C : ℝ} {φ φt : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ}

theorem limBr_measurableSet_good (hρ : IsMollifier ρ) : MeasurableSet (limBrGood ρ T) :=
  measurableSet_lt (measurable_convQ_lintegral_sq hρ) measurable_const

/-- Almost surely a limit point is in `limBrGood ρ T`, by (7.1). -/
theorem limBr_ae_good {Ω : Type*} {mΩ : MeasurableSpace Ω} {Pr : Measure Ω}
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y) (hρ : IsMollifier ρ)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal (limField ρ Y t x ω ^ 2)) ∂Pr < ⊤) :
    ∀ᵐ ω ∂Pr, Y ω ∈ limBrGood ρ T :=
  ae_lt_top (f := fun ω => ∫⁻ t in Icc (0 : ℝ) T, ∫⁻ x,
    ENNReal.ofReal (limDensity ρ (pathAt (Y ω) t) x ^ 2))
    ((measurable_convQ_lintegral_sq hρ).comp hY) hZ2.ne

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for a nonnegative `f` (no integrability needed). -/
private lemma limBr_ofReal_integral_le {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ‖∫ x, f x ∂μ‖ₑ := Real.ofReal_le_enorm _
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := lintegral_congr fun x => Real.enorm_eq_ofReal (hf x)

/-- On `[0,T]`, `Q(t) = ∫_0^t q(γ, s) ds` with the jointly measurable `q = convQDens`. -/
theorem limBr_eq_convQDens (hT : 0 ≤ T) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ =
      ∫ s in (0 : ℝ)..t, convQDens hT ρ φ γ s := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  exact (convQDens_of_mem hT ρ φ γ ⟨hs.1, hs.2.trans ht.2⟩).symm

/-- `Q(t) ≥ 0` for `t ≥ 0`. -/
theorem limBr_bracket_nonneg (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ :=
  intervalIntegral.integral_nonneg ht fun _ _ => integral_nonneg fun _ => by positivity

/-- `γ ↦ Q(t)` is measurable for `t ∈ [0,T]`. -/
theorem limBr_measurable_bracket (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have e : (fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ) =
      fun γ => ∫ s in (0 : ℝ)..t, convQDens hT ρ φ γ s :=
    funext fun γ => limBr_eq_convQDens hT γ ht
  rw [e]
  exact prelimAux_measurable_intervalIntegral (measurable_convQDens hT hφ hρ) ht.1
    fun _ _ _ => rfl

/-- `ofReal q(γ, s) ≤ c² ∫ Z(s,x)² dx` on `[0,T]`, with `c` a bound for `|φ|`. -/
private lemma limBr_ofReal_convQDens_le (hT : 0 ≤ T) {c : ℝ}
    (hc : ∀ s ∈ Icc 0 T, ∀ y, |φ s y| ≤ c) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    ENNReal.ofReal (convQDens hT ρ φ γ s) ≤
      ENNReal.ofReal (c ^ 2) * ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) := by
  rw [convQDens_of_mem hT ρ φ γ hs, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (limBr_ofReal_integral_le fun x => by positivity).trans (lintegral_mono fun x => ?_)
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : φ s x ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hc s hs x) 2
  nlinarith [sq_nonneg (limDensity ρ (pathAt γ s) x)]

/-- **The bound behind the integrability of (7.3)**: for `t ∈ [0,T]`,
`Q(t) ≤ c² ∫_0^T ∫ Z(s,x)² dx ds` (in `[0, ∞]`), for every path. -/
theorem limBr_ofReal_le (hφ : IsC13 T φ φt C) :
    ∃ c : ℝ, ∀ (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)), ∀ t ∈ Icc (0 : ℝ) T,
      ENNReal.ofReal
        (limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ) ≤
      ENNReal.ofReal c * ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ x,
        ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) := by
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  refine ⟨c ^ 2, fun γ t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  rw [limBr_eq_convQDens hT γ ht, intervalIntegral.integral_of_le ht.1,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (limBr_ofReal_integral_le fun s => integral_nonneg fun _ => by positivity).trans ?_
  calc ∫⁻ s in Ioc 0 t, ENNReal.ofReal (convQDens hT ρ φ γ s)
      ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal (convQDens hT ρ φ γ s) :=
        lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2))
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc fun s hs =>
        limBr_ofReal_convQDens_le hT hc γ hs

/-- On a good path, `q(γ, ·)` is integrable on `[0,T]`. -/
private lemma limBr_integrableOn (hT : 0 ≤ T) (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ)
    {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hγ : γ ∈ limBrGood ρ T) :
    IntegrableOn (convQDens hT ρ φ γ) (Icc 0 T) := by
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  have hm : Measurable (convQDens hT ρ φ γ) :=
    ((measurable_convQDens hT hφ hρ).comp (f := fun s : ℝ => (γ, s)) (by fun_prop) :)
  refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun s => integral_nonneg fun _ => by positivity)).2 ?_⟩
  calc ∫⁻ s in Icc 0 T, ENNReal.ofReal (convQDens hT ρ φ γ s)
      ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal (c ^ 2) *
          ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) :=
        setLIntegral_mono' measurableSet_Icc fun s hs => limBr_ofReal_convQDens_le hT hc γ hs
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγ

/-- On a good path, `t ↦ Q(t)` is continuous and nondecreasing on `[0,T]`. -/
theorem limBr_continuousOn_monotoneOn (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ)
    {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hγ : γ ∈ limBrGood ρ T) :
    ContinuousOn (fun t =>
        limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ)
        (Icc 0 T) ∧
      MonotoneOn (fun t =>
        limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ)
        (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp only [Icc_eq_empty (not_le.2 hT)]
    exact ⟨continuousOn_empty _, fun _ h => h.elim⟩
  have hi := limBr_integrableOn hT hφ hρ hγ
  refine ⟨?_, fun a ha b hb hab => ?_⟩
  · have h2 := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := convQDens hT ρ φ γ) (by rwa [uIcc_of_le hT])
    rw [uIcc_of_le hT] at h2
    exact h2.congr fun t ht => limBr_eq_convQDens hT γ ht
  · simp only
    rw [limBr_eq_convQDens hT γ ha, limBr_eq_convQDens hT γ hb]
    refine intervalIntegral.integral_mono_interval le_rfl ha.1 hab
      (ae_of_all _ fun s => integral_nonneg fun _ => by positivity) ?_
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb.1).2
      (hi.mono_set (Icc_subset_Icc le_rfl hb.2))

/-- Properties of the modified bracket `limBrMod` (every path). -/
theorem limBrMod_props (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ContinuousOn (fun t => limBrMod ρ φ t γ) (Icc 0 T) ∧
      MonotoneOn (fun t => limBrMod ρ φ t γ) (Icc 0 T) ∧ limBrMod ρ φ 0 γ = 0 ∧
      ∀ t, 0 ≤ t → 0 ≤ limBrMod ρ φ t γ := by
  by_cases hγ : γ ∈ limBrGood ρ T
  · simp only [limBrMod, indicator_of_mem hγ]
    exact ⟨(limBr_continuousOn_monotoneOn hφ hρ hγ).1, (limBr_continuousOn_monotoneOn hφ hρ hγ).2,
      by simp [limBracket], fun t ht => limBr_bracket_nonneg γ ht⟩
  · simp only [limBrMod, indicator_of_notMem hγ]
    exact ⟨continuousOn_const, monotoneOn_const, by simp, fun _ _ => le_rfl⟩

theorem limBr_measurable_mod (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Measurable (limBrMod (T := T) ρ φ t) :=
  (limBr_measurable_bracket hφ hρ ht).indicator (limBr_measurableSet_good hρ)

/-- **Transfer of the bracket (7.3)** between a random path `Y` (almost surely good) and the
canonical space with the law of `Y`. -/
theorem limBr_hasBracket_map_iff {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hT : 0 ≤ T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hY : Measurable Y) (hρ : IsMollifier ρ) (hφ : IsC13 T φ φt C)
    (hG : ∀ᵐ ω ∂μ, Y ω ∈ limBrGood ρ T) :
    HasBracket T (nullAug μ (pathFiltration Y)) (limMart Y φ φt) (limBracket (limField ρ Y) φ) μ ↔
      HasBracket T (nullAug (μ.map Y) (pathFiltrationCan T))
        (limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt)
        (limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ)
        (μ.map Y) := by
  have hGm : ∀ᵐ γ ∂(μ.map Y), γ ∈ limBrGood ρ T :=
    (ae_map_iff hY.aemeasurable (limBr_measurableSet_good hρ)).2 hG
  have key := hasBracket_map_iff (μ := μ) hY
    (m := limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt)
    (a := limBrMod ρ φ) (fun t ht => limMart_measurable hφ ht)
    (fun t ht => limBr_measurable_mod hφ hρ ht) (limMart_continuousOn hφ)
    (fun γ => (limBrMod_props hφ hρ γ).1) (fun γ => (limBrMod_props hφ hρ γ).2.1)
  constructor
  · intro h
    refine (key.1 (h.congr hT (ae_of_all _ fun _ _ _ => rfl) ?_)).congr hT
      (ae_of_all _ fun _ _ _ => rfl) ?_
    · filter_upwards [hG] with ω hω t _
      simp only [limBrMod, indicator_of_mem hω]
      rfl
    · filter_upwards [hGm] with γ hγ t _
      simp only [limBrMod, indicator_of_mem hγ]
  · intro h
    refine (key.2 (h.congr hT (ae_of_all _ fun _ _ _ => rfl) ?_)).congr hT
      (ae_of_all _ fun _ _ _ => rfl) ?_
    · filter_upwards [hGm] with γ hγ t _
      simp only [limBrMod, indicator_of_mem hγ]
    · filter_upwards [hG] with ω hω t _
      simp only [limBrMod, indicator_of_mem hω]
      rfl

/-- **Adaptedness of (7.3)**: `Q(t)` is measurable for the canonical filtration at time `t`. -/
theorem limBr_measurable_can (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ T) :
    Measurable[pathFiltrationCan T t] fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ := by
  have hm := (limBr_measurable_bracket (ρ := ρ) hφ hρ ⟨t.2, ht⟩).comp (measurable_prelimStop t)
  have e : (fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ) =
      (fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      limBracket (limField ρ fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ t γ) ∘
        prelimStop (T := T) t := by
    funext γ
    simp only [Function.comp_apply, limBracket, limField]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
    simp only [pathAt_prelimStop (NNReal.coe_nonneg t) hs.2]
  rw [e]
  exact hm

end QSSEPtoKPZ
