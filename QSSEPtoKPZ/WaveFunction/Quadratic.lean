/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Defs
public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.Martingales.Defs
public import QSSEPtoKPZ.WaveFunction.QuadIto
public import QSSEPtoKPZ.WaveFunction.EquationPAux

/-!
# Lemma 2.3 (2): quadratic functionals of `P`

Statement: Stage 2, task T0; proof: task D6, following the article (`docs/stage2-design.md`,
1.2 (h)). Replace `ψ` by a unit-norm version `ψ'`. On the boxes `[-K,K]²`, the product rule
gives the Itô decomposition of `∑ f P(x₁) P(x₂)` (`QuadBox.lean`); the drift summed over `ℤ²` is
`∑ (∂ₜf + 𝒬f) P P` by two summations by parts and (2.5) (`QuadDrift.lean`); as `K → ∞` the
processes and drifts converge pathwise on `{N_T < ∞}`, `N_T = sup_{t ≤ T} ‖ψ_t‖²_{2a+1}`
(`QuadPath.lean`), and the diffusions converge in energy, by (2.2) with `k = 3`
(`QuadEnergy.lean`). The limit is an Itô process (`QuadIto.lean`), whose martingale part has the
stated bracket.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The quantity `D_s(x) = ∑_{x' ∈ ℤ} (f_s(x+1,x') - f_s(x,x')) P(s,x')` of the last term of
(2.8). -/
def quadDiff (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (f : ℝ → ℤ → ℤ → ℝ) (s : ℝ) (ω : Ω) (x : ℤ) : ℝ :=
  ∑' x' : ℤ, (f s (x + 1) x' - f s x x') * density ψ ω s x'

/-- **Lemma 2.3 (2), equation (2.8)**, `L = ∞`. Let `T > 0`, `a ≥ 0`, and let `f_t(x₁,x₂)` be
symmetric in `(x₁,x₂)`, `C¹` in `t ∈ [0,T]` (derivative `f'`, continuous in `t`, one-sided at `0`
and `T`), with `|f_t(x₁,x₂)| + |∂ₜf_t(x₁,x₂)| ≤ C e^{a(|x₁| + |x₂|)}`. Then almost surely, for
`t ∈ [0,T]`, the double series `∑ f_t P P` and `∑ (∂ₜf_t + 𝒬 f_t) P P` converge absolutely, the
series `D_t(x) = ∑_{x'} (f_t(x+1,x') - f_t(x,x')) P(t,x')` converge absolutely, the series
`∑ₓ (2 D_t(x))² P(t,x) P(t,x+1)` converges, the drift and the bracket density below are
integrable on `[0,T]`, and
`M_t = ∑_{x₁,x₂} f_t(x₁,x₂) P(t,x₁) P(t,x₂) - f_0(0,0) - ∫_0^t ∑_{x₁,x₂} (∂ₛf_s + 𝒬 f_s)(x₁,x₂) P(s,x₁) P(s,x₂) ds`
(the last term of (2.8), `2 ∫_0^t ∑ₓ D_s(x) dJ_s(x)`) is a continuous square-integrable
martingale on `[0,T]` with bracket `⟨M⟩_t = ∫_0^t ∑ₓ 2 (2 D_s(x))² P(s,x) P(s,x+1) ds` (by (2.5)). -/
theorem lemma_2_3_quadratic (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {T a C : ℝ} (hT : 0 < T) (ha : 0 ≤ a) {f f' : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 T) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 T))
    (hbd : ∀ x₁ x₂, ∀ t ∈ Set.Icc 0 T,
      |f t x₁ x₂| + |f' t x₁ x₂| ≤ C * Real.exp (a * (|(x₁ : ℝ)| + |(x₂ : ℝ)|))) :
    (∀ᵐ ω ∂μ, (∀ t ∈ Set.Icc 0 T,
        Summable (fun p : ℤ × ℤ => |f t p.1 p.2| * density ψ ω t p.1 * density ψ ω t p.2) ∧
        Summable (fun p : ℤ × ℤ => |f' t p.1 p.2 + inclGen (f t) p.1 p.2| *
          density ψ ω t p.1 * density ψ ω t p.2) ∧
        (∀ x, Summable (fun x' => |f t (x + 1) x' - f t x x'| * density ψ ω t x')) ∧
        Summable (fun x => (2 * quadDiff ψ f t ω x) ^ 2 * density ψ ω t x * density ψ ω t (x + 1))) ∧
      IntervalIntegrable (fun s => ∑' x₁ : ℤ, ∑' x₂ : ℤ,
        (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ ω s x₁ * density ψ ω s x₂) volume 0 T ∧
      IntervalIntegrable (fun s => ∑' x : ℤ,
        2 * (2 * quadDiff ψ f s ω x) ^ 2 * density ψ ω s x * density ψ ω s (x + 1)) volume 0 T) ∧
    HasBracket T 𝓕
      (fun t ω => (∑' x₁ : ℤ, ∑' x₂ : ℤ, f t x₁ x₂ * density ψ ω t x₁ * density ψ ω t x₂) -
        f 0 0 0 - ∫ s in (0 : ℝ)..t, ∑' x₁ : ℤ, ∑' x₂ : ℤ,
          (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ ω s x₁ * density ψ ω s x₂)
      (fun t ω => ∫ s in (0 : ℝ)..t, ∑' x : ℤ,
        2 * (2 * quadDiff ψ f s ω x) ^ 2 * density ψ ω s x * density ψ ω s (x + 1)) μ := by
  -- the bounds `|f|, |∂ₜf| ≤ C W(x₁) W(x₂)`
  have hC : 0 ≤ C := by
    have h1 := hbd 0 0 0 ⟨le_rfl, hT.le⟩
    have h2 : 0 < Real.exp (a * (|((0 : ℤ) : ℝ)| + |((0 : ℤ) : ℝ)|)) := Real.exp_pos _
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h h2
    linarith [abs_nonneg (f 0 0 0), abs_nonneg (f' 0 0 0)]
  have hfb : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂ :=
    fun t ht x₁ x₂ => by
    have := hbd x₁ x₂ t ht
    rw [quadW_mul, ← mul_assoc] at this
    linarith [abs_nonneg (f' t x₁ x₂)]
  have hfb' : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, |f' t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂ :=
    fun t ht x₁ x₂ => by
    have := hbd x₁ x₂ t ht
    rw [quadW_mul, ← mul_assoc] at this
    linarith [abs_nonneg (f t x₁ x₂)]
  have hc : ∀ x₁ x₂, ContinuousOn (f · x₁ x₂) (Set.Icc 0 T) := fun x₁ x₂ t ht =>
    (hf x₁ x₂ t ht).continuousWithinAt
  -- the unit-norm version and `N = T`
  set N : ℝ≥0 := ⟨T, hT.le⟩ with hN
  obtain ⟨ψ', hu⟩ := hψ.exists_isUnitWave hB
  have hX := hu.isItoProcessUpTo_quad hB hψ (N := N) ha hC hsymm hf hf' hfb hfb'
  have hbr := hu.hasBracket_quad hB hψ (N := N) ha hC hsymm hf hf' hfb hfb'
  have hae := hu.ae_quadSup_ne_top hB hψ ha N
  -- `ψ = ψ'` on `[0, ∞)`
  have hq : ∀ ω, (∀ t : ℝ≥0, ψ' t ω = ψ t ω) → ∀ s, 0 ≤ s →
      density ψ ω s = density ψ' ω s ∧ quadDiff ψ f s ω = quadD ψ' f s ω := fun ω h s hs => by
    have hd := IsUnitWave.eqP_density_eq h hs
    refine ⟨hd, funext fun x => ?_⟩
    simp only [quadDiff, quadD, hd]
  refine ⟨?_, hbr.congr hT.le ?_ ?_⟩
  · filter_upwards [hu.ae_eq, hae, hX.drift] with ω h1 hω hdr
    refine ⟨fun t ht => ?_, ?_, ?_⟩
    · obtain ⟨hd, hq'⟩ := hq ω h1 t ht.1
      rw [hq', hd]
      have hD := quadDecay_of_quadSup hω (T := (N : ℝ)) ht
      have hl := fun x => le_quadP3 hD.nonneg x
      refine ⟨?_, ?_, fun x => hD.summable_abs_row_sub ha hC (hfb t ht) x, ?_⟩
      · exact hD.summable_of_le ha hC fun p =>
          hD.abs_mul_le (F := |f t p.1 p.2|) (by rw [abs_abs]; exact hfb t ht _ _)
            (hl _).2.1 (hl _).2.1
      · have hK : 0 ≤ (1 + 12 * Real.exp a) * C := by positivity
        refine hD.summable_of_le ha hK fun p => hD.abs_mul_le (by
          rw [abs_abs]
          have h1 := hfb' t ht p.1 p.2
          have h2 := quad_abs_lap_fst_le ha (hfb t ht) p.1 p.2
          have h3 := quad_abs_lap_snd_le ha (hfb t ht) p.1 p.2
          have h4 := quad_abs_jump_le ha (hfb t ht) p.1 p.2
          have e : inclGen (f t) p.1 p.2 = lap (fun y => f t y p.2) p.1 + lap (f t p.1) p.2 +
              (if |p.1 - p.2| = 1 then f t p.1 p.1 + f t p.2 p.2 - 2 * f t p.1 p.2 else 0) := rfl
          rw [e]
          have k1 := abs_add_le (f' t p.1 p.2) (lap (fun y => f t y p.2) p.1 +
            lap (f t p.1) p.2 +
            (if |p.1 - p.2| = 1 then f t p.1 p.1 + f t p.2 p.2 - 2 * f t p.1 p.2 else 0))
          have k2 := abs_add_le (lap (fun y => f t y p.2) p.1 + lap (f t p.1) p.2)
            (if |p.1 - p.2| = 1 then f t p.1 p.1 + f t p.2 p.2 - 2 * f t p.1 p.2 else 0)
          have k3 := abs_add_le (lap (fun y => f t y p.2) p.1) (lap (f t p.1) p.2)
          linarith) (hl _).2.1 (hl _).2.1
      · have h := (hu.tsum_quadLimDiff_sq ha hC (N := (N : ℝ)) hfb hω ht).1
        exact (h.mul_left (1 / 2)).congr fun x => by ring
    · refine hdr.congr fun s hs => ?_
      rw [Set.uIoc_of_le hT.le] at hs
      simp only [(hq ω h1 s hs.1.le).1]
    · have hcont := hu.quad_path_continuousOn_bracket ha hC (N := (N : ℝ))
        (fun s hs => quadDecay_of_quadSup hω hs) hfb hc
      refine (hcont.intervalIntegrable_of_Icc hT.le).congr fun s hs => ?_
      rw [Set.uIoc_of_le hT.le] at hs
      obtain ⟨hd, hq'⟩ := hq ω h1 s hs.1.le
      simp only [hd, hq']
  · filter_upwards [hu.ae_eq] with ω h1 t ht
    obtain ⟨hd, -⟩ := hq ω h1 t ht.1
    have hI : (∫ s in (0 : ℝ)..t, ∑' x₁ : ℤ, ∑' x₂ : ℤ,
        (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ' ω s x₁ * density ψ' ω s x₂) =
        ∫ s in (0 : ℝ)..t, ∑' x₁ : ℤ, ∑' x₂ : ℤ,
          (f' s x₁ x₂ + inclGen (f s) x₁ x₂) * density ψ ω s x₁ * density ψ ω s x₂ :=
      intervalIntegral.integral_congr fun s hs => by
        rw [Set.uIcc_of_le ht.1] at hs
        simp only [(hq ω h1 s hs.1).1]
    simp only [hd, hI]
  · filter_upwards [hu.ae_eq] with ω h1 t ht
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    obtain ⟨hd, hq'⟩ := hq ω h1 s hs.1
    simp only [hd, hq']

end QSSEPtoKPZ
