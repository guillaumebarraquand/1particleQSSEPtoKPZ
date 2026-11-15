/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.QuadEnergy

/-!
# Quadratic functionals of `P` are Itô processes (task D6)

For the unit-norm version `ψ'` and a symmetric weight `f_t(x₁,x₂)`, `C¹` in `t ∈ [0,N]` with
`|f_t|, |∂ₜf_t| ≤ C e^{a(|x₁|+|x₂|)}`:

* `IsUnitWave.isItoProcessUpTo_quad`: `∑_{x₁,x₂} f_t(x₁,x₂) P(t,x₁) P(t,x₂)` is an Itô process up
  to `N` with drift `∑_{x₁,x₂} (∂ₜf + 𝒬f) P P` and diffusion `quadLimDiff` (the boxes
  `[-K,K]²` and `K → ∞`, `IsItoProcessUpTo.of_tendsto_const`);
* `IsUnitWave.hasBracket_quad`: the remainder of (2.8) is a continuous `L²` martingale on
  `[0,N]` with bracket `∫_0^t ∑ₓ 2 (2 D_s(x))² P(s,x) P(s,x+1) ds`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

namespace IsUnitWave

/-- **The quadratic functional is an Itô process up to `N`.** -/
theorem isItoProcessUpTo_quad [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) {f f' : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc (0 : ℝ) N,
      HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 N) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 N))
    (hfb : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    (hfb' : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f' t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ, f t x₁ x₂ * density ψ' ω t x₁ * density ψ' ω t x₂)
      (fun s ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ,
        (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ' ω s x₁ * density ψ' ω s x₂)
      (quadLimDiff ψ' a N f) := by
  have hbox := fun K : ℕ => hu.isItoProcessUpTo_quad_finset hB hf hf' (quadBox K)
  have hc : ∀ x₁ x₂, ContinuousOn (f · x₁ x₂) (Set.Icc 0 N) := fun x₁ x₂ t ht =>
    (hf x₁ x₂ t ht).continuousWithinAt
  obtain ⟨hm, hint⟩ := hu.quadSup_moment hB hψ ha N
  have hae := hu.ae_quadSup_ne_top hB hψ ha N
  have hdm := fun i => hu.measurable_quadLimDiff ha hC hc hfb hm i
  -- pathwise drift facts
  have hdrift : ∀ ω, quadSup ψ' a N ω ≠ ⊤ →
      IntervalIntegrable (fun s => ∑' x₁ : ℤ, ∑' x₂ : ℤ,
        (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ' ω s x₁ * density ψ' ω s x₂)
        volume 0 N ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ N → Tendsto (fun K => ∫ s in (0 : ℝ)..t,
        ∑ p ∈ quadBox K, quadDriftTerm (f s) (f' s) (density ψ' ω s) p.1 p.2) atTop
        (𝓝 (∫ s in (0 : ℝ)..t, ∑' x₁ : ℤ, ∑' x₂ : ℤ,
          (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ' ω s x₁ * density ψ' ω s x₂)) :=
    fun ω hω => quad_path_integral_drift (M := quadDriftBound a C (quadSup ψ' a N ω).toReal)
      N.2 (fun K => continuousOn_finsetSum _ fun p _ =>
        hu.continuousOn_quadDriftTerm hc hf' ω p.1 p.2)
      (fun s hs => (quad_path_drift ha hC (quadDecay_of_quadSup hω hs) (hfb s hs)
        (hfb' s hs)).1)
      (fun s hs => (quad_path_drift ha hC (quadDecay_of_quadSup hω hs) (hfb s hs)
        (hfb' s hs)).2)
  refine IsItoProcessUpTo.of_tendsto_const hB.nullAug hbox hdm
    (hu.tendsto_energy_quadBoxDiff ha hC hsymm hfb hm hint (fun K => (hbox K).integrable.meas)
      hdm) (hae.mono fun ω hω => (hdrift ω hω).1) ?_ (hae.mono fun ω hω => (hdrift ω hω).2)
  filter_upwards [hae] with ω hω t ht0 htN
  have hD := quadDecay_of_quadSup hω ⟨ht0, htN⟩
  have hl := fun x => le_quadP3 hD.nonneg x
  have hs : Summable fun p : ℤ × ℤ => f t p.1 p.2 * density ψ' ω t p.1 * density ψ' ω t p.2 :=
    hD.summable_of_le ha hC fun p => hD.abs_mul_le (hfb t ⟨ht0, htN⟩ _ _) (hl _).2.1 (hl _).2.1
  rw [← hs.tsum_prod]
  exact quad_tendsto_box_sum hs

/-- `P(0,x) = 𝟙_{x=0}` for the unit-norm version. -/
lemma density_zero (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    density ψ' ω 0 x = if x = 0 then 1 else 0 := by
  rw [density, hu.init_apply ω x]
  split_ifs <;> simp

/-- The bracket density on `{N_N < ∞}`: for `s ∈ [0,N]`,
`∑ᵢ (quadLimDiff)ᵢ² = ∑ₓ 2 (2 D_s(x))² P(s,x) P(s,x+1)`, and the latter converges. -/
lemma tsum_quadLimDiff_sq (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N a C : ℝ} (ha : 0 ≤ a)
    (hC : 0 ≤ C) {f : ℝ → ℤ → ℤ → ℝ}
    (hfb : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    {ω : Ω} (hω : quadSup ψ' a N ω ≠ ⊤) {s : ℝ} (hs : s ∈ Set.Icc 0 N) :
    Summable (fun x => 2 * (2 * quadD ψ' f s ω x) ^ 2 * density ψ' ω s x *
      density ψ' ω s (x + 1)) ∧
    ∑' i, quadLimDiff ψ' a N f i s ω ^ 2 = ∑' x : ℤ,
      2 * (2 * quadD ψ' f s ω x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1) := by
  have hD := quadDecay_of_quadSup hω hs
  set R := (quadSup ψ' a N ω).toReal
  have hvb : ∀ y, |2 * quadRow (f s) (density ψ' ω s) y| ≤
      (2 * C * R * quadSigma) * quadW a y := fun y => by
    rw [abs_mul, abs_two]
    have := hD.abs_row_le ha hC (hfb s hs) y
    linarith
  obtain ⟨h1, -⟩ := quad_tsum_diff_sq_le hD.nonneg (fun x => hu.density_le_one ω hs.1 x)
    (hD.summable_sq_mul hvb)
  have e : ∀ x, (2 * quadRow (f s) (density ψ' ω s) (x + 1) -
      2 * quadRow (f s) (density ψ' ω s) x) ^ 2 *
      (2 * density ψ' ω s x * density ψ' ω s (x + 1)) =
      2 * (2 * quadD ψ' f s ω x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1) :=
    fun x => by
    rw [quadD, hD.tsum_row_sub ha hC (hfb s hs) x]
    ring
  refine ⟨h1.congr e, ?_⟩
  simp only [quadLimDiff_eq ha hC hω hs (hfb s hs)]
  rw [(hasSum_weightCurrent_sq ψ' (fun _ x => 2 * quadRow (f s) (density ψ' ω s) x) s ω
    h1).tsum_eq]
  exact tsum_congr e

/-- **Lemma 2.3 (2) for the unit-norm version `ψ'`.** The remainder of (2.8) is a continuous
`L²` martingale on `[0,N]` for `𝓕` with bracket `∫_0^t ∑ₓ 2 (2 D_s(x))² P(s,x) P(s,x+1) ds`. -/
theorem hasBracket_quad [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) {f f' : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc (0 : ℝ) N,
      HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 N) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 N))
    (hfb : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    (hfb' : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f' t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂) :
    HasBracket N 𝓕
      (fun t ω => (∑' x₁ : ℤ, ∑' x₂ : ℤ, f t x₁ x₂ * density ψ' ω t x₁ * density ψ' ω t x₂) -
        f 0 0 0 - ∫ s in (0 : ℝ)..t, ∑' x₁ : ℤ, ∑' x₂ : ℤ,
          (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ' ω s x₁ * density ψ' ω s x₂)
      (fun t ω => ∫ s in (0 : ℝ)..t, ∑' x : ℤ,
        2 * (2 * quadD ψ' f s ω x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1)) μ := by
  have hX := hu.isItoProcessUpTo_quad hB hψ ha hC hsymm hf hf' hfb hfb'
  have hbr := hasBracket_stochInt hB.nullAug hX.integrable N
  have hae := hu.ae_quadSup_ne_top hB hψ ha N
  refine hasBracket_nullAug_iff.1 (hbr.congr (NNReal.coe_nonneg N) ?_ ?_)
  · filter_upwards [hX.eq] with ω hω t ht
    have e := hω ⟨t, ht.1⟩
    have hm : min (⟨t, ht.1⟩ : ℝ≥0) N = ⟨t, ht.1⟩ := min_eq_left ht.2
    erw [hm] at e
    have h0 : ∑' x₁ : ℤ, ∑' x₂ : ℤ, f 0 x₁ x₂ * density ψ' ω 0 x₁ * density ψ' ω 0 x₂ =
        f 0 0 0 := by
      simp only [hu.density_zero ω, mul_ite, mul_one, mul_zero, tsum_ite_eq]
    change (∑' x₁ : ℤ, ∑' x₂ : ℤ, f t x₁ x₂ * density ψ' ω t x₁ * density ψ' ω t x₂) =
      ((∑' x₁ : ℤ, ∑' x₂ : ℤ, f 0 x₁ x₂ * density ψ' ω 0 x₁ * density ψ' ω 0 x₂) +
      ∫ s in (0 : ℝ)..t, ∑' x₁ : ℤ, ∑' x₂ : ℤ,
        (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ' ω s x₁ * density ψ' ω s x₂) +
      stochInt (nullAug μ 𝓕) μ B (fun i s ω => if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω
        else 0) t ω at e
    rw [e, h0]
    ring
  · filter_upwards [hae] with ω hω t ht
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    have hsN : s ≤ (N : ℝ) := hs.2.trans ht.2
    simp only [hsN, ite_true]
    exact (hu.tsum_quadLimDiff_sq ha hC hfb hω ⟨hs.1, hsN⟩).2

end IsUnitWave

end QSSEPtoKPZ
