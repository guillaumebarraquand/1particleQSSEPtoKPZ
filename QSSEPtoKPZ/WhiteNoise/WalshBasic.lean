/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Checks

/-!
# Algebra of the Itô–Walsh integral (task G4a)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G4a
(except `IsWhiteNoise.isProbabilityMeasure`, proved here). See `docs/stage4-design.md`,
Section 3.3, and `docs/stage4-interfaces.md`.

Linearity of the frozen relation `IsWalshIntegral` and monotonicity in the filtration. These
hold without assuming that `S` is a white noise (they are inductions on the definition).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- A space carrying a white noise is a probability space. -/
theorem IsWhiteNoise.isProbabilityMeasure (hS : IsWhiteNoise 𝓖 S ν) : IsProbabilityMeasure ν :=
  (hS.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure

/-- The integral of `0` is `0`. -/
theorem IsWalshIntegral.zero (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) :
    IsWalshIntegral 𝓖 S ν (fun _ _ _ => 0) (fun _ => 0) := by
  have h := IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) 0 0 0 0 (fun _ => 0) le_rfl le_rfl
    measurable_const ⟨0, by simp⟩
  convert h using 1
  · funext r y ω
    split_ifs <;> rfl
  · funext ω
    simp

/-- Scalar multiples of Walsh integrals. -/
theorem IsWalshIntegral.const_mul {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) (c : ℝ) :
    IsWalshIntegral 𝓖 S ν (fun s y ω => c * h s y ω) (fun ω => c * X ω) := by
  induction hX with
  | block s t a b c' hst hab hc hbdd =>
    obtain ⟨C, hC⟩ := hbdd
    have h := IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s t a b (fun ω => c * c' ω) hst
      hab (measurable_const.mul hc) ⟨|c| * C, fun ω => by rw [abs_mul]; gcongr; exact hC ω⟩
    convert h using 1
    · funext r y ω
      simp only [mul_ite, mul_zero]
    · funext ω
      ring
  | add h h' X X' _ _ ih ih' =>
    convert IsWalshIntegral.add _ _ _ _ ih ih' using 1
    · funext r y ω
      ring
    · funext ω
      ring
  | limit h X hs Xs _ hh hX hhs hXs ih =>
    refine IsWalshIntegral.limit _ _ _ _ ih ?_ ?_ ?_ ?_
    · exact hh.const_mul c
    · exact hX.const_mul c
    · have e : ∀ k, uncurryField (fun s y ω => c * hs k s y ω) - uncurryField
          (fun s y ω => c * h s y ω) = c • (uncurryField (hs k) - uncurryField h) := by
        intro k
        funext p
        simp [uncurryField, mul_sub]
      simp_rw [e, eLpNorm_const_smul]
      rw [show (0 : ℝ≥0∞) = ‖c‖ₑ * 0 by simp]
      exact ENNReal.Tendsto.const_mul hhs (Or.inr enorm_ne_top)
    · have e : ∀ k, (fun ω => c * Xs k ω) - (fun ω => c * X ω) = c • (Xs k - X) := by
        intro k
        funext ω
        simp [mul_sub]
      simp_rw [e, eLpNorm_const_smul]
      rw [show (0 : ℝ≥0∞) = ‖c‖ₑ * 0 by simp]
      exact ENNReal.Tendsto.const_mul hXs (Or.inr enorm_ne_top)

/-- Differences of Walsh integrals. -/
theorem IsWalshIntegral.sub {h h' : ℝ → ℝ → Ω → ℝ} {X X' : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) (hX' : IsWalshIntegral 𝓖 S ν h' X') :
    IsWalshIntegral 𝓖 S ν (fun s y ω => h s y ω - h' s y ω) (fun ω => X ω - X' ω) := by
  convert IsWalshIntegral.add _ _ _ _ hX (hX'.const_mul (-1)) using 1
  · funext r y ω
    ring
  · funext ω
    ring

/-- Finite sums of Walsh integrals. -/
theorem IsWalshIntegral.finset_sum {ι : Type*} (I : Finset ι) {h : ι → ℝ → ℝ → Ω → ℝ}
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ I, IsWalshIntegral 𝓖 S ν (h i) (X i)) :
    IsWalshIntegral 𝓖 S ν (fun s y ω => ∑ i ∈ I, h i s y ω) (fun ω => ∑ i ∈ I, X i ω) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using IsWalshIntegral.zero 𝓖 S ν
  | insert i I hi ih =>
    have h := IsWalshIntegral.add _ _ _ _ (hX i (Finset.mem_insert_self i I))
      (ih fun j hj => hX j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using h

/-- A Walsh integral for a filtration is a Walsh integral for any larger filtration. -/
theorem IsWalshIntegral.mono_filtration {𝓖' : Filtration ℝ≥0 mΩ} (h𝓖 : 𝓖 ≤ 𝓖')
    {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    IsWalshIntegral 𝓖' S ν h X := by
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    exact IsWalshIntegral.block s t a b c hst hab (hc.mono (h𝓖 s) le_rfl) hbdd
  | add h h' X X' _ _ ih ih' => exact IsWalshIntegral.add _ _ _ _ ih ih'
  | limit h X hs Xs _ hh hX hhs hXs ih => exact IsWalshIntegral.limit _ _ _ _ ih hh hX hhs hXs

/-- A Walsh integral depends on `S` only through the masses of rectangles. -/
theorem IsWalshIntegral.congr_rectMass {S' : ℝ → ℝ → Ω → ℝ}
    (hSS' : ∀ s t a b ω, rectMass S s t a b ω = rectMass S' s t a b ω)
    {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    IsWalshIntegral 𝓖 S' ν h X := by
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    have h := IsWalshIntegral.block (𝓖 := 𝓖) (S := S') (ν := ν) s t a b c hst hab hc hbdd
    simp_rw [hSS']
    exact h
  | add h h' X X' _ _ ih ih' => exact IsWalshIntegral.add _ _ _ _ ih ih'
  | limit h X hs Xs _ hh hX hhs hXs ih => exact IsWalshIntegral.limit _ _ _ _ ih hh hX hhs hXs

end QSSEPtoKPZ
