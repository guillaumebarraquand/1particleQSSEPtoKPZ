/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Auxiliary results for stopping times (package B, task B3)

Used by `Martingales/Stopping.lean` (optional sampling by discretization from above, design
decision B-4 of `docs/stage2-design.md`, Section 2.1).

* `isStoppingTime_comp_of_monotone`: `F(τ)` is a stopping time if `F` is monotone and `F ≥ id`.
* `dyadicUpper T j`: the dyadic approximation from above `x ↦ min(⌈2^j x⌉ 2^{-j}, T)` on
  `[0, T]`, with finitely many values, converging to `x`.
* Stopped values `V_ρ` at finitely-valued stopping times: decomposition
  `V_ρ = ∑_s 𝟙_{ρ = s} V_s`, measurability, and optional sampling
  (`setIntegral_stoppedAt_finite`).
* `exists_adapted_continuous_version`, `aestronglyMeasurable_stoppedAt`: `Y_τ` is
  `𝓕ᵃ_τ`-measurable up to a null set if `Y` is a.s. continuous on `[0, T]` and adapted up to
  null sets (no right-continuity of the filtration).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Discretization of stopping times from above -/

/-- A monotone function `F ≥ id` of a stopping time is a stopping time: `{F(τ) ≤ t}` is
`{τ ≤ a}` or `{τ < a}` for `a = sup {x : F x ≤ t} ≤ t`. -/
lemma isStoppingTime_comp_of_monotone {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) {F : ℝ≥0 → ℝ≥0}
    (hF : Monotone F) (hle : ∀ x, x ≤ F x) :
    IsStoppingTime 𝓖 (fun ω => (F (τ ω) : WithTop ℝ≥0)) := by
  intro t
  show MeasurableSet[𝓖 t] {ω | (F (τ ω) : WithTop ℝ≥0) ≤ t}
  simp only [WithTop.coe_le_coe]
  by_cases hS : ({x | F x ≤ t} : Set ℝ≥0).Nonempty
  swap
  · have e : {ω | F (τ ω) ≤ t} = ∅ := Set.eq_empty_of_forall_notMem fun ω h => hS ⟨_, h⟩
    rw [e]; exact @MeasurableSet.empty _ (𝓖 t)
  have hSb : BddAbove ({x | F x ≤ t} : Set ℝ≥0) := ⟨t, fun x hx => (hle x).trans hx⟩
  have hat : sSup {x | F x ≤ t} ≤ t := csSup_le hS fun x hx => (hle x).trans hx
  by_cases ha : sSup {x | F x ≤ t} ∈ ({x | F x ≤ t} : Set ℝ≥0)
  · have e : {ω | F (τ ω) ≤ t} =
        {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((sSup {x | F x ≤ t} : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
      exact ⟨fun h => le_csSup hSb h, fun h => (hF h).trans ha⟩
    rw [e]; exact 𝓖.mono hat _ (hτ _)
  · have e : {ω | F (τ ω) ≤ t} =
        {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) < ((sSup {x | F x ≤ t} : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_lt_coe]
      refine ⟨fun h => lt_of_le_of_ne (le_csSup hSb h) fun e => ha (e ▸ h), fun h => ?_⟩
      obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup hS h
      exact (hF hxy.le).trans hy
    rw [e]; exact 𝓖.mono hat _ (hτ.measurableSet_lt _)

/-- The dyadic approximation from above at level `j`, capped at `T`:
`x ↦ max(x, min(⌈2^j x⌉ 2^{-j}, T))` (equal to `min(⌈2^j x⌉ 2^{-j}, T)` for `x ≤ T`). -/
def dyadicUpper (T : ℝ≥0) (j : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  max x (min ((⌈(2 : ℝ≥0) ^ j * x⌉₊ : ℝ≥0) / 2 ^ j) T)

/-- `dyadicUpper T j` is monotone. -/
lemma dyadicUpper_mono (T : ℝ≥0) (j : ℕ) : Monotone (dyadicUpper T j) := fun x y h => by
  unfold dyadicUpper
  gcongr

/-- `x ≤ dyadicUpper T j x`. -/
lemma le_dyadicUpper (T : ℝ≥0) (j : ℕ) (x : ℝ≥0) : x ≤ dyadicUpper T j x := le_max_left _ _

/-- `dyadicUpper T j x ≤ T` for `x ≤ T`. -/
lemma dyadicUpper_le (T : ℝ≥0) (j : ℕ) {x : ℝ≥0} (hx : x ≤ T) : dyadicUpper T j x ≤ T :=
  max_le hx (min_le_right _ _)

/-- `dyadicUpper T j x ≤ x + 2^{-j}`. -/
lemma dyadicUpper_le_add (T : ℝ≥0) (j : ℕ) (x : ℝ≥0) : dyadicUpper T j x ≤ x + 1 / 2 ^ j := by
  refine max_le le_self_add ((min_le_left _ _).trans ?_)
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity), mul_comm]
  exact (Nat.ceil_lt_add_one zero_le).le

/-- `dyadicUpper T j x → x` as `j → ∞`. -/
lemma tendsto_dyadicUpper (T x : ℝ≥0) :
    Tendsto (fun j => dyadicUpper T j x) atTop (𝓝 x) := by
  have h : Tendsto (fun j : ℕ => (1 : ℝ≥0) / 2 ^ j) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have h' : Tendsto (fun j : ℕ => x + (1 : ℝ≥0) / 2 ^ j) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (le_dyadicUpper T · x)
    (dyadicUpper_le_add T · x)

/-- On `[0, T]`, `dyadicUpper T j` takes finitely many values. -/
lemma dyadicUpper_mem (T : ℝ≥0) (j : ℕ) {x : ℝ≥0} (hx : x ≤ T) :
    dyadicUpper T j x ∈ insert T ((Finset.range (⌈(2 : ℝ≥0) ^ j * T⌉₊ + 1)).image
      fun k : ℕ => (k : ℝ≥0) / 2 ^ j) := by
  have hxle : x ≤ (⌈(2 : ℝ≥0) ^ j * x⌉₊ : ℝ≥0) / 2 ^ j := by
    rw [le_div_iff₀ (by positivity), mul_comm]; exact Nat.le_ceil _
  unfold dyadicUpper
  rw [max_eq_right (le_min hxle hx)]
  rcases min_choice ((⌈(2 : ℝ≥0) ^ j * x⌉₊ : ℝ≥0) / 2 ^ j) T with h | h <;> rw [h]
  · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, Finset.mem_range.2
      (Nat.lt_succ_of_le (Nat.ceil_mono (by gcongr))), rfl⟩)
  · exact Finset.mem_insert_self _ _

/-! ### Auxiliary results on stopped values -/

/-- A function dominated by `D` with `∫⁻ D < ∞` is integrable (no measurability of `D` is
needed, `∫⁻` being the lower integral). -/
lemma integrable_of_enorm_le_lintegral {f : Ω → ℝ} {D : Ω → ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hD : ∫⁻ ω, D ω ∂μ ≠ ∞) (hle : ∀ᵐ ω ∂μ, ‖f ω‖ₑ ≤ D ω) : Integrable f μ :=
  ⟨hf, (lintegral_mono_ae hle).trans_lt hD.lt_top⟩

/-- `{ρ = s}` is `𝓖_s`-measurable for a stopping time `ρ`. -/
lemma measurableSet_eq_of_isStoppingTime {𝓖 : Filtration ℝ≥0 mΩ} {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0))) (s : ℝ≥0) :
    MeasurableSet[𝓖 s] {ω | ρ ω = s} := by
  simpa only [WithTop.coe_inj] using hρ.measurableSet_eq s

/-- `V_ρ = ∑_{s ∈ S} 𝟙_{ρ = s} V_s` if `ρ` takes its values in the finite set `S`. -/
lemma stoppedAt_eq_sum (V : ℝ → Ω → ℝ) (ρ : Ω → ℝ≥0) (S : Finset ℝ≥0)
    (hS : ∀ ω, ρ ω ∈ S) :
    (fun ω => V (ρ ω) ω) = fun ω => ∑ s ∈ S, {ω | ρ ω = s}.indicator (V s) ω := by
  ext ω
  rw [Finset.sum_eq_single (ρ ω)]
  · exact (Set.indicator_of_mem (show ω ∈ {ω' | ρ ω' = ρ ω} from rfl) _).symm
  · intro s _ hs
    exact Set.indicator_of_notMem (fun h => hs h.symm) _
  · intro h; exact absurd (hS ω) h

/-- If `ρ` is a stopping time with values in a finite set `S` and each `V_s`, `s ∈ S`, is
a.e. strongly measurable, then so is `V_ρ`. -/
lemma aestronglyMeasurable_stoppedAt_finite {𝓖 : Filtration ℝ≥0 mΩ} {V : ℝ → Ω → ℝ}
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0))) (S : Finset ℝ≥0)
    (hS : ∀ ω, ρ ω ∈ S) (hV : ∀ s ∈ S, AEStronglyMeasurable (V s) μ) :
    AEStronglyMeasurable (fun ω => V (ρ ω) ω) μ := by
  rw [stoppedAt_eq_sum V ρ S hS]
  exact Finset.aestronglyMeasurable_fun_sum S fun s hs =>
    (hV s hs).indicator (𝓖.le s _ (measurableSet_eq_of_isStoppingTime hρ s))

/-- **Optional sampling for finitely-valued stopping times.** If `ρ` takes its values in a
finite set `S` and `∫_B V_s = ∫_B Y_s` for `s ∈ S` and `B ∈ 𝓖_s`, then `∫_A V_ρ = ∫_A Y_ρ` for
`A ∈ 𝓖_ρ`. -/
lemma setIntegral_stoppedAt_finite {𝓖 : Filtration ℝ≥0 mΩ} {V Y : ℝ → Ω → ℝ}
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0))) (S : Finset ℝ≥0)
    (hS : ∀ ω, ρ ω ∈ S) (hVi : ∀ s ∈ S, Integrable (V s) μ) (hYi : ∀ s ∈ S, Integrable (Y s) μ)
    (h : ∀ s ∈ S, ∀ B, MeasurableSet[𝓖 s] B → ∫ ω in B, V s ω ∂μ = ∫ ω in B, Y s ω ∂μ)
    {A : Set Ω} (hA : MeasurableSet[hρ.measurableSpace] A) :
    ∫ ω in A, V (ρ ω) ω ∂μ = ∫ ω in A, Y (ρ ω) ω ∂μ := by
  have hm : ∀ s, MeasurableSet {ω | ρ ω = s} :=
    fun s => 𝓖.le s _ (measurableSet_eq_of_isStoppingTime hρ s)
  rw [stoppedAt_eq_sum V ρ S hS, stoppedAt_eq_sum Y ρ S hS,
    integral_finsetSum S fun s hs => ((hVi s hs).indicator (hm s)).integrableOn,
    integral_finsetSum S fun s hs => ((hYi s hs).indicator (hm s)).integrableOn]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [setIntegral_indicator (hm s), setIntegral_indicator (hm s)]
  have hset : {ω | ((ρ ω : ℝ≥0) : WithTop ℝ≥0) = (s : WithTop ℝ≥0)} = {ω | ρ ω = s} := by
    ext ω; exact WithTop.coe_inj
  have hA' : MeasurableSet[hρ.measurableSpace] (A ∩ {ω | ((ρ ω : ℝ≥0) : WithTop ℝ≥0) = s}) :=
    hA.inter (hρ.measurableSet_eq' s)
  rw [hρ.measurableSet_inter_eq_iff, hset] at hA'
  exact h s hs _ hA'

/-- **Adapted continuous version.** If `Y` has a.s. continuous paths on `[0, T]` (`T ≥ 0`) and
each `Y_t`, `t ≤ T`, is a.e. equal to an `𝓕_t`-measurable function, then there is a process `Y'`
adapted to `𝓕ᵃ`, with all paths continuous on `[0, ∞)` (frozen after `T`), with `Y'_t = Y_t` for
all `t ≤ T`, almost surely. `Y'_t` is the limit of versions of `Y` at grid points below `t`. -/
lemma exists_adapted_continuous_version {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hm : ∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable[𝓕 t] (Y t) μ) :
    ∃ Y' : ℝ≥0 → Ω → ℝ, (∀ t, StronglyMeasurable[nullAug μ 𝓕 t] (Y' t)) ∧
      (∀ ω, Continuous fun t => Y' t ω) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ) ≤ T → Y' t ω = Y t ω := by
  classical
  set T' : ℝ≥0 := ⟨T, hT⟩ with hT'
  set Z : ℝ≥0 → Ω → ℝ := fun r => if hr : (r : ℝ) ≤ T then (hm r hr).mk (Y r) else 0 with hZ
  have hZm : ∀ r, StronglyMeasurable[𝓕 r] (Z r) := fun r => by
    by_cases hr : (r : ℝ) ≤ T
    · simp only [Z, hr, dite_true]; exact (hm r hr).stronglyMeasurable_mk
    · simp only [Z, hr, dite_false]; exact stronglyMeasurable_const
  have hgood : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) ∧
      ∀ p : ℕ × ℕ, (ratGridPt p : ℝ) ≤ T → Y (ratGridPt p) ω = Z (ratGridPt p) ω := by
    refine hc.and (ae_all_iff.2 fun p => ?_)
    by_cases hp : (ratGridPt p : ℝ) ≤ T
    · filter_upwards [(hm _ hp).ae_eq_mk] with ω hω _
      simp only [Z, hp, dite_true]; exact hω
    · exact ae_of_all _ fun ω h => absurd h hp
  set N := toMeasurable μ {ω | ¬ (ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) ∧
      ∀ p : ℕ × ℕ, (ratGridPt p : ℝ) ≤ T → Y (ratGridPt p) ω = Z (ratGridPt p) ω)} with hNdef
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hgood
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hNt : ∀ t : ℝ≥0, MeasurableSet[nullAug μ 𝓕 t] N := fun t =>
    nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0)
  have hok : ∀ ω, ω ∉ N → ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) ∧
      ∀ p : ℕ × ℕ, (ratGridPt p : ℝ) ≤ T → Y (ratGridPt p) ω = Z (ratGridPt p) ω :=
    fun ω hω => by by_contra h; exact hω (subset_toMeasurable _ _ h)
  set Y' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N then 0 else Y (min t T' : ℝ≥0) ω with hY'
  have hY'eq : ∀ ω, ω ∉ N → ∀ t : ℝ≥0, (t : ℝ) ≤ T → Y' t ω = Y t ω := fun ω hω t ht => by
    simp only [Y', hω, ite_false]
    rw [min_eq_left (show t ≤ T' from NNReal.coe_le_coe.1 ht)]
  have hmeasT : ∀ t : ℝ≥0, (t : ℝ) ≤ T → StronglyMeasurable[nullAug μ 𝓕 t] (Y' t) := by
    intro t ht
    have hseq : ∀ n, StronglyMeasurable[nullAug μ 𝓕 t]
        (fun ω => if ω ∈ N then 0 else Z (gridBelow t n) ω) := fun n =>
      StronglyMeasurable.ite (hNt t) stronglyMeasurable_const
        ((hZm _).mono ((𝓕.mono (gridBelow_le t n)).trans (le_nullAug μ 𝓕 t)))
    refine stronglyMeasurable_of_tendsto atTop hseq (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ N
    · simp only [Y', hω, ite_true]; exact tendsto_const_nhds
    · have hle : ∀ n, (gridBelow t n : ℝ) ≤ T := fun n =>
        (NNReal.coe_le_coe.2 (gridBelow_le t n)).trans ht
      have e : ∀ n, (if ω ∈ N then 0 else Z (gridBelow t n) ω) = Y (gridBelow t n) ω :=
        fun n => by
          simp only [hω, ite_false]
          exact ((hok ω hω).2 (⌊((n : ℝ) + 1) * t⌋₊, n) (hle n)).symm
      simp only [e, hY'eq ω hω t ht]
      have hlim : Tendsto (fun n => (gridBelow t n : ℝ)) atTop (𝓝[Set.Icc 0 T] (t : ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_gridBelow t,
          Eventually.of_forall fun n => ⟨(gridBelow t n).2, hle n⟩⟩
      exact ((hok ω hω).1 t ⟨t.2, ht⟩).tendsto.comp hlim
  have hmeas : ∀ t : ℝ≥0, StronglyMeasurable[nullAug μ 𝓕 t] (Y' t) := by
    intro t
    rcases le_total (t : ℝ) T with ht | ht
    · exact hmeasT t ht
    · have hTt : T' ≤ t := NNReal.coe_le_coe.1 ht
      have e : Y' t = Y' T' := by
        ext ω; simp only [Y', min_eq_right hTt, min_self]
      rw [e]
      exact (hmeasT _ le_rfl).mono ((nullAug μ 𝓕).mono hTt)
  refine ⟨Y', hmeas, fun ω => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [Y', hω, ite_true]; exact continuous_const
    · simp only [Y', hω, ite_false]
      exact (hok ω hω).1.comp_continuous
        (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
        fun t => ⟨(min t T').2, NNReal.coe_le_coe.2 (min_le_right t T')⟩
  · filter_upwards [hNa] with ω hω t ht using hY'eq ω hω t ht

/-- At a stopping time `τ ≤ T` of `𝓕ᵃ`, `Y_τ` is a.e. strongly measurable for `𝓕ᵃ_τ`, if `Y` has
a.s. continuous paths on `[0, T]` and is adapted to `𝓕` up to null sets (through the adapted
continuous version, which is progressively measurable). -/
lemma aestronglyMeasurable_stoppedAt {T : ℝ} {Y : ℝ → Ω → ℝ}
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hm : ∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable[𝓕 t] (Y t) μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    AEStronglyMeasurable[hτ.measurableSpace] (fun ω => Y (τ ω) ω) μ := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨fun _ => 0, stronglyMeasurable_const,
      ae_of_all _ fun ω => absurd ((τ ω).2.trans (hτT ω)) (not_le.2 hT)⟩
  obtain ⟨Y', hY'm, hY'c, hY'eq⟩ := exists_adapted_continuous_version hT hc hm
  have hprog : IsStronglyProgressive (nullAug μ 𝓕) Y' :=
    StronglyAdapted.isStronglyProgressive_of_continuous hY'm hY'c
  refine ⟨stoppedValue Y' (fun ω => (τ ω : WithTop ℝ≥0)),
    (measurable_stoppedValue hprog hτ).stronglyMeasurable, ?_⟩
  filter_upwards [hY'eq] with ω hω
  simp only [stoppedValue]
  exact (hω (τ ω) (hτT ω)).symm

/-! ### Small facts on stopping times and conditional expectations -/

/-- `r ∧ τ` is a stopping time, written with the minimum in `ℝ≥0`. -/
lemma isStoppingTime_nnreal_min {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) (r : ℝ≥0) :
    IsStoppingTime 𝓖 (fun ω => ((min r (τ ω) : ℝ≥0) : WithTop ℝ≥0)) := by
  have e : (fun ω => ((min r (τ ω) : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min ((τ ω : ℝ≥0) : WithTop ℝ≥0) r := by
    ext1 ω; rw [WithTop.coe_min, min_comm]
  rw [e]; exact hτ.min_const r

/-- If `𝔼[X_s | 𝓕_s] = X_s`, then `X_s` is a.e. equal to an `𝓕_s`-measurable function. -/
lemma aestronglyMeasurable_of_condExp_eq_self {X : Ω → ℝ} {s : ℝ≥0}
    (h : μ[X | 𝓕 s] =ᵐ[μ] X) : AEStronglyMeasurable[𝓕 s] X μ :=
  ⟨_, stronglyMeasurable_condExp, h.symm⟩

end QSSEPtoKPZ
