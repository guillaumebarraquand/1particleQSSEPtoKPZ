/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Stopping

/-!
# Aldous' trick (task H5a)

INTERFACE FILE (task I0' of Stage 3): the statement below is an interface, proved by task H5a.
See `docs/stage3-design.md`, Sections 1.2 (e) and 2.5, and `docs/stage3-interfaces.md`.

Let `X` be a real process with all paths continuous on `[0, ∞)`, adapted to a filtration `𝓖`
(no right-continuity, no completeness assumed). Suppose that
`ℙ(|X_{ρ+s} - X_ρ| ≥ η) ≤ a` for every stopping time `ρ ≤ T + 1` and every deterministic
`s ∈ [0, 2δ]`. Then for stopping times `τ ≤ σ ≤ τ + δ` with `τ ≤ T` (and `δ ≤ 1`),
`ℙ(|X_σ - X_τ| ≥ 2η) ≤ 3a`.

Proof: for `s ∈ [δ, 2δ]`, `|X_σ - X_τ| ≤ |X_{τ+s} - X_τ| + |X_{σ+u} - X_σ|` with
`u = τ + s - σ ∈ [0, 2δ]`; average over `s ∈ [δ, 2δ]` and use Tonelli on `[δ, 2δ] × Ω`
(the map `(s, ω) ↦ X_{ρ(ω)+s}(ω)` is jointly measurable by continuity of the paths). The first
term gives `a`, the second `2a` (after the change of variable `u = τ + s - σ`, the `u`-interval
has length `δ` inside `[0, 2δ]`).

Probabilities are outer measures of the events (their measurability is not claimed).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- The set of `(s, ω) ∈ ℝ × Ω` with `η ≤ |X_{ρ(ω) + s⁺}(ω) - X_{ρ(ω)}(ω)|`, where `s⁺ = max s 0`
(for `s ≥ 0` the increment of `X` on `[ρ, ρ + s]`). -/
private def trickSet (X : ℝ → Ω → ℝ) (η : ℝ) (ρ : Ω → ℝ≥0) : Set (ℝ × Ω) :=
  {p | η ≤ |X ((ρ p.2 + p.1.toNNReal : ℝ≥0) : ℝ) p.2 - X (ρ p.2) p.2|}

/-- Joint measurability: for a process with continuous paths on `[0, ∞)` and measurable
marginals, and a measurable random time `ρ`, the set `trickSet X η ρ` is measurable. -/
private lemma measurableSet_trickSet {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXm : ∀ t : ℝ≥0, Measurable (X t))
    (η : ℝ) {ρ : Ω → ℝ≥0} (hρ : Measurable ρ) : MeasurableSet (trickSet X η ρ) := by
  have hY : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => X t ω) :=
    measurable_uncurry_of_continuous_of_measurable hXc hXm
  have h1 : Measurable fun p : ℝ × Ω => X ((ρ p.2 + p.1.toNNReal : ℝ≥0) : ℝ) p.2 :=
    hY.comp (((hρ.comp measurable_snd).add (measurable_real_toNNReal.comp measurable_fst)).prodMk
      measurable_snd)
  have h2 : Measurable fun p : ℝ × Ω => X (ρ p.2) p.2 :=
    hY.comp ((hρ.comp measurable_snd).prodMk measurable_snd)
  exact measurableSet_le measurable_const (continuous_abs.measurable.comp (h1.sub h2))

/-- A random time `ρ` that is a stopping time (seen in `WithTop ℝ≥0`) is measurable. -/
private lemma measurable_of_isStoppingTime_coe {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0))) : Measurable ρ := by
  refine measurable_of_Iic fun t => ?_
  have h := 𝓖.le t _ (hρ.measurableSet_le t)
  convert h using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq, WithTop.coe_le_coe]

/-- Tonelli step: for a stopping time `ρ ≤ T + 1` and a measurable `S ⊆ [0, 2δ]`,
`∫ ∫_S 1{η ≤ |X_{ρ+s} - X_ρ|} ds dℙ ≤ |S| a`. -/
private lemma lintegral_setLIntegral_trickSet_le [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXm : ∀ t : ℝ≥0, Measurable (X t))
    {T δ η a : ℝ}
    (hA : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ),
        μ {ω | η ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρT : ∀ ω, (ρ ω : ℝ) ≤ T + 1) {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc 0 (2 * δ)) :
    ∫⁻ ω, (∫⁻ s in S, (trickSet X η ρ).indicator 1 (s, ω)) ∂μ
      ≤ volume S * ENNReal.ofReal a := by
  have hG := measurableSet_trickSet hXc hXm η (measurable_of_isStoppingTime_coe hρ)
  have hm : AEMeasurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (trickSet X η ρ).indicator (1 : ℝ × Ω → ℝ≥0∞) (s, ω)) (μ.prod (volume.restrict S)) :=
    ((measurable_one.indicator hG).comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hm]
  calc ∫⁻ s in S, ∫⁻ ω, (trickSet X η ρ).indicator 1 (s, ω) ∂μ
      ≤ ∫⁻ _ in S, ENNReal.ofReal a := by
        refine setLIntegral_mono' hS fun s hs => ?_
        have hs0 : 0 ≤ s := (hSsub hs).1
        have he : (fun ω => (trickSet X η ρ).indicator 1 (s, ω))
            = (Prod.mk s ⁻¹' trickSet X η ρ).indicator (1 : Ω → ℝ≥0∞) := by
          ext ω
          rfl
        rw [he, lintegral_indicator_one (hG.preimage measurable_prodMk_left)]
        refine le_trans (measure_mono fun ω hω => ?_) (hA ρ hρ hρT s (hSsub hs))
        simp only [Set.mem_preimage, trickSet, Set.mem_ofPred_eq, NNReal.coe_add,
          Real.coe_toNNReal _ hs0] at hω
        exact hω
    _ = volume S * ENNReal.ofReal a := by rw [setLIntegral_const, mul_comm]

/-- Change of variable: if `c ∈ [-δ, 0]`, then `∫_{[δ, 2δ]} h(s + c) ds ≤ ∫_{[0, 2δ]} h(u) du`. -/
private lemma setLIntegral_Icc_add_le {δ c : ℝ} (hc1 : -δ ≤ c) (hc2 : c ≤ 0) (h : ℝ → ℝ≥0∞) :
    ∫⁻ s in Set.Icc δ (2 * δ), h (s + c) ≤ ∫⁻ u in Set.Icc 0 (2 * δ), h u := by
  calc ∫⁻ s in Set.Icc δ (2 * δ), h (s + c)
      ≤ ∫⁻ s in Set.Icc δ (2 * δ), (Set.Icc 0 (2 * δ)).indicator h (s + c) := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        rw [Set.indicator_of_mem]
        constructor <;> linarith [hs.1, hs.2]
    _ ≤ ∫⁻ s, (Set.Icc 0 (2 * δ)).indicator h (s + c) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ s, (Set.Icc 0 (2 * δ)).indicator h s := lintegral_add_right_eq_self _ c
    _ = ∫⁻ u in Set.Icc 0 (2 * δ), h u := lintegral_indicator measurableSet_Icc _

/-- Pointwise step of Aldous' trick: if `2η ≤ |X_σ - X_τ|` with `τ ≤ σ ≤ τ + δ`, then
`δ ≤ ∫_{[δ, 2δ]} 1{η ≤ |X_{τ+s} - X_τ|} ds + ∫_{[0, 2δ]} 1{η ≤ |X_{σ+u} - X_σ|} du`
(for `s ∈ [δ, 2δ]` put `u = τ + s - σ ∈ [0, 2δ]` and use the triangle inequality). -/
private lemma ofReal_le_add_of_two_mul_le {X : ℝ → Ω → ℝ} {δ η : ℝ} {τ σ : Ω → ℝ≥0} {ω : Ω}
    (hτσ : τ ω ≤ σ ω) (hσδ : (σ ω : ℝ) ≤ τ ω + δ)
    (hω : 2 * η ≤ |X (σ ω) ω - X (τ ω) ω|) (hτm : Measurable fun s : ℝ =>
      (trickSet X η τ).indicator (1 : ℝ × Ω → ℝ≥0∞) (s, ω)) :
    ENNReal.ofReal δ ≤ (∫⁻ s in Set.Icc δ (2 * δ), (trickSet X η τ).indicator 1 (s, ω))
      + ∫⁻ u in Set.Icc 0 (2 * δ), (trickSet X η σ).indicator 1 (u, ω) := by
  set c : ℝ := (τ ω : ℝ) - σ ω with hc
  have hτσ' : (τ ω : ℝ) ≤ σ ω := hτσ
  have hc1 : -δ ≤ c := by linarith
  have hc2 : c ≤ 0 := by linarith
  have key : ∀ s ∈ Set.Icc δ (2 * δ), (1 : ℝ≥0∞) ≤ (trickSet X η τ).indicator 1 (s, ω)
      + (trickSet X η σ).indicator 1 (s + c, ω) := by
    intro s hs
    have hδ0 : 0 ≤ δ := by linarith [hs.1, hs.2]
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hsc0 : 0 ≤ s + c := by linarith [hs.1]
    by_contra hlt
    push Not at hlt
    have h1 : (s, ω) ∉ trickSet X η τ := fun hm => by
      rw [Set.indicator_of_mem hm] at hlt
      exact absurd hlt (not_lt.2 le_self_add)
    have h2 : (s + c, ω) ∉ trickSet X η σ := fun hm => by
      rw [Set.indicator_of_mem hm] at hlt
      exact absurd hlt (not_lt.2 le_add_self)
    simp only [trickSet, Set.mem_ofPred_eq, not_le, NNReal.coe_add,
      Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ hsc0] at h1 h2
    have he : (σ ω : ℝ) + (s + c) = τ ω + s := by rw [hc]; ring
    rw [he, abs_sub_comm] at h2
    have := abs_sub_le (X (σ ω) ω) (X (τ ω + s) ω) (X (τ ω) ω)
    linarith
  calc ENNReal.ofReal δ = ∫⁻ _ in Set.Icc δ (2 * δ), 1 := by
        rw [setLIntegral_const, Real.volume_Icc, one_mul]
        congr 1
        ring
    _ ≤ ∫⁻ s in Set.Icc δ (2 * δ), ((trickSet X η τ).indicator 1 (s, ω)
        + (trickSet X η σ).indicator 1 (s + c, ω)) := setLIntegral_mono' measurableSet_Icc key
    _ = (∫⁻ s in Set.Icc δ (2 * δ), (trickSet X η τ).indicator 1 (s, ω))
        + ∫⁻ s in Set.Icc δ (2 * δ), (trickSet X η σ).indicator 1 (s + c, ω) :=
        lintegral_add_left hτm _
    _ ≤ _ := add_le_add le_rfl
        (setLIntegral_Icc_add_le hc1 hc2 fun u => (trickSet X η σ).indicator 1 (u, ω))


/-- **Aldous' trick**: from deterministic shifts after stopping times to a stopping time `σ` with
`τ ≤ σ ≤ τ + δ`. If `ℙ(|X_{ρ+s} - X_ρ| ≥ η) ≤ a` for all stopping times `ρ ≤ T + 1` and all
`s ∈ [0, 2δ]`, then `ℙ(|X_σ - X_τ| ≥ 2η) ≤ 3a`. -/
theorem aldous_trick [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    {T δ η a : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ),
        μ {ω | η ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a)
    {τ σ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hσ : IsStoppingTime 𝓖 (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) (hτσ : τ ≤ σ) (hσδ : ∀ ω, (σ ω : ℝ) ≤ τ ω + δ) :
    μ {ω | 2 * η ≤ |X (σ ω) ω - X (τ ω) ω|} ≤ ENNReal.ofReal (3 * a) := by
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hXa t).mono (𝓖.le t) le_rfl
  have hτm := measurable_of_isStoppingTime_coe hτ
  have hσm := measurable_of_isStoppingTime_coe hσ
  have hGτ := measurableSet_trickSet hXc hXm η hτm
  have hGσ := measurableSet_trickSet hXc hXm η hσm
  have hστ : ∀ ω, (σ ω : ℝ) ≤ T + 1 := fun ω => by linarith [hσδ ω, hτT ω]
  have hτT1 : ∀ ω, (τ ω : ℝ) ≤ T + 1 := fun ω => by linarith [hτT ω]
  set F : Ω → ℝ≥0∞ := fun ω => (∫⁻ s in Set.Icc δ (2 * δ), (trickSet X η τ).indicator 1 (s, ω))
    + ∫⁻ u in Set.Icc 0 (2 * δ), (trickSet X η σ).indicator 1 (u, ω) with hF
  have hF1 : Measurable fun ω =>
      ∫⁻ s in Set.Icc δ (2 * δ), (trickSet X η τ).indicator (1 : ℝ × Ω → ℝ≥0∞) (s, ω) :=
    Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => (trickSet X η τ).indicator 1 p.swap)
      ((measurable_one.indicator hGτ).comp measurable_swap)
  have hF2 : Measurable fun ω =>
      ∫⁻ u in Set.Icc 0 (2 * δ), (trickSet X η σ).indicator (1 : ℝ × Ω → ℝ≥0∞) (u, ω) :=
    Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => (trickSet X η σ).indicator 1 p.swap)
      ((measurable_one.indicator hGσ).comp measurable_swap)
  have hsub : {ω | 2 * η ≤ |X (σ ω) ω - X (τ ω) ω|} ⊆ {ω | ENNReal.ofReal δ ≤ F ω} :=
    fun ω hω => ofReal_le_add_of_two_mul_le (hτσ ω) (hσδ ω) hω
      ((measurable_one.indicator hGτ).comp measurable_prodMk_right)
  have hint : ∫⁻ ω, F ω ∂μ ≤ ENNReal.ofReal δ * (3 * ENNReal.ofReal a) := by
    rw [hF, lintegral_add_left hF1]
    calc _ ≤ volume (Set.Icc δ (2 * δ)) * ENNReal.ofReal a
          + volume (Set.Icc (0 : ℝ) (2 * δ)) * ENNReal.ofReal a :=
          add_le_add
            (lintegral_setLIntegral_trickSet_le hXc hXm hA hτ hτT1 measurableSet_Icc
              (Set.Icc_subset_Icc_left hδ.le))
            (lintegral_setLIntegral_trickSet_le hXc hXm hA hσ hστ measurableSet_Icc le_rfl)
      _ = ENNReal.ofReal δ * (3 * ENNReal.ofReal a) := by
          rw [Real.volume_Icc, Real.volume_Icc, show 2 * δ - δ = δ by ring, sub_zero,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          ring
  have hmark := (mul_meas_ge_le_lintegral₀ (hF1.add hF2).aemeasurable (ENNReal.ofReal δ)).trans
    hint
  have hδ0 : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  have hle := (ENNReal.mul_le_mul_iff_right hδ0 ENNReal.ofReal_ne_top).1 hmark
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
  exact (measure_mono hsub).trans hle

end QSSEPtoKPZ
