/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import Mathlib.MeasureTheory.Measure.Tight
public import QSSEPtoKPZ.Tightness.Version
public import QSSEPtoKPZ.Tightness.Assembly

/-!
# Proposition 5.1: continuity and tightness of `t ↦ 𝖹_n(t)`

Statements: Stage 3, task T0' (`docs/stage3-design.md`, Section 3.4, decisions D3', D6');
proofs: tasks Q3 (continuity, version; from `Tightness/Version.lean`) and Q4 (tightness).

`ℳ₊(ℝ)` is Mathlib's `FiniteMeasure ℝ` with the topology of weak convergence, as in the frozen
statement of Theorem 1.2; `C([0,T], ℳ₊(ℝ))` is `C(Set.Icc 0 T, FiniteMeasure ℝ)`, with the
compact-open topology (the topology of uniform convergence, `[0,T]` being compact) and its
Borel σ-algebra (Mathlib's instance on `C(X, Y)`, the one used by the frozen statement). The
`MeasurableSpace` instance of `FiniteMeasure ℝ` itself (the Giry σ-algebra) is not used.

* `prop_5_1_continuous`: almost surely, `t ↦ 𝖹_n(t)` is continuous from `[0, ∞)` to `ℳ₊(ℝ)`.
* `prop_5_1_version`: a version of `(𝖹_n(t))_{t ∈ [0,T]}` which is a random variable with values
  in `C([0,T], ℳ₊(ℝ))`.
* `prop_5_1`: tightness in `C([0,T], ℳ₊(ℝ))`, uniformly over all realizations of the model, all
  `n ≥ 1` and all versions.
* `prop_5_1_isTight`: for a sequence of realizations, the family of laws is tight in the sense of
  Mathlib (`IsTightMeasureSet`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

universe u

section Continuity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **Proposition 5.1**, continuity of the trajectories: for `n ≥ 1`, almost surely there is a
continuous map `γ : [0, ∞) → ℳ₊(ℝ)` (weak topology) with `γ(t) = 𝖹_n(t)` for every `t ≥ 0`,
where `𝖹_n(t)` is the measure (3.5). -/
theorem prop_5_1_continuous (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n : ℝ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, ∃ γ : C(ℝ≥0, FiniteMeasure ℝ), ∀ t : ℝ≥0,
      (γ t : Measure ℝ) = tiltedMeasure n ψ ω t :=
  tiltVer_ae_continuous hB hψ hn

/-- **Proposition 5.1**, the process `(𝖹_n(t))_{t ∈ [0,T]}` as a random variable in
`C([0,T], ℳ₊(ℝ))`: for `n ≥ 1` and every `T`, there is a map `Zv : Ω → C([0,T], ℳ₊(ℝ))`,
measurable for the Borel σ-algebra of the topology of uniform convergence (as in the frozen
statement of Theorem 1.2), such that almost surely `Zv(ω)(t) = 𝖹_n(t)` for all `t ∈ [0,T]`. -/
theorem prop_5_1_version (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable Zv ∧
      ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t := by
  obtain ⟨Zv, hm, -, he⟩ := exists_tiltedPath_version hB hψ hn T
  exact ⟨Zv, hm, he⟩

end Continuity

/-- **Proposition 5.1**, tightness (decision D3'): for `T > 0` and `ε > 0` there is a compact set
`𝒦` of `C([0,T], ℳ₊(ℝ))` such that, for every probability space, Brownian family and wave
function, every `n ≥ 1` and every version `Zv` of `(𝖹_n(t))_{t ∈ [0,T]}` (a map
`Ω → C([0,T], ℳ₊(ℝ))` with, almost surely, `Zv(ω)(t) = 𝖹_n(t)` for all `t ∈ [0,T]`),
`ℙ(Zv ∉ 𝒦) ≤ ε` (outer probability if `Zv` is not measurable). -/
theorem prop_5_1 {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ 𝒦 : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), IsCompact 𝒦 ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
        IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ → ∀ {n : ℝ}, 1 ≤ n →
        ∀ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ),
          (∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t) →
          μ (Zv ⁻¹' 𝒦ᶜ) ≤ ENNReal.ofReal ε :=
  tightAsm_prop_5_1 hT hε

/-- **Proposition 5.1**, tightness of the laws, for a sequence of realizations: let `T > 0`, and
for each `k` let `n_k ≥ 1`, a probability space with a Brownian family and a wave function, and
an (almost everywhere measurable) version `Zv_k` of `(𝖹_{n_k}(t))_{t ∈ [0,T]}` with values in
`C([0,T], ℳ₊(ℝ))`. Then the family of the laws of the `Zv_k` is tight (Mathlib's
`IsTightMeasureSet`: for every `ε > 0` there is a compact `𝒦` with `ℙ(Zv_k ∉ 𝒦) ≤ ε` for all
`k`). -/
theorem prop_5_1_isTight {T : ℝ} (hT : 0 < T) (n : ℕ → ℝ) (hn : ∀ k, 1 ≤ n k)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (Zv : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (hZm : ∀ k, AEMeasurable (Zv k) (μ k))
    (hZ : ∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
      (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t) :
    IsTightMeasureSet (Set.range fun k => (μ k).map (Zv k)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun ν _ => by simp [hεtop]⟩
  obtain ⟨𝒦, h𝒦, hb⟩ := prop_5_1 hT (ENNReal.toReal_pos hε.ne' hεtop)
  refine ⟨𝒦, h𝒦, ?_⟩
  rintro _ ⟨k, rfl⟩
  rw [Measure.map_apply_of_aemeasurable (hZm k) h𝒦.isClosed.measurableSet.compl]
  exact (hb (hB k) (hψ k) (hn k) (Zv k) (hZ k)).trans (ENNReal.ofReal_toReal hεtop).le

end QSSEPtoKPZ
