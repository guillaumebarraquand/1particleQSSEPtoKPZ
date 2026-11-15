/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.Prop73
public import QSSEPtoKPZ.WhiteNoise.Transfer
public import QSSEPtoKPZ.Uniqueness.NoiseFunctionalSol

/-!
# Uniqueness in law for the weak mild equation (task K4)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task K4
(13 November 2026), with `NoiseFunctionalAux.lean` and `NoiseFunctionalSol.lean`.
See `docs/stage4-design.md`, Section 1.2 (h) (second item), decision D4″, and
`docs/stage4-interfaces.md`.

A solution of (7.13) in `ℋ_T` is almost everywhere a fixed measurable function `H` of the noise
coordinates, the same on every probability space carrying a white noise. Proof: the projection
`Ẑ = noiseProj S ν Z_T` of `Z_T = Z 𝟙_{[0,T]}(t)` (in `L²(ν ⊗ Leb²)` by (7.1); `Z` itself need
not be integrable on `Ω × [0,T] × ℝ`, so Mathlib's `condExp` for `ν ⊗ Leb²` must not be used,
see `WhiteNoise/Projection.lean`) solves (7.13): apply `IsWalshIntegral.condExp_noise` to the
integrand `𝟙_{0<s<t} (g_{t-s} ⋆ f)(y) Z(s,y)`, take the bounded deterministic factor out by
`noiseProj_mul_left`, and identify the value by `condExp_integral_noiseProj` (for almost every
`t`) and `𝔼[∫ g_t f | 𝒩_∞] = ∫ g_t f`; `Ẑ ∈ ℋ_T` by `noiseProj_memLp` and
`stronglyMeasurable_noiseProj` (use `noiseSheet` and `IsWhiteNoise.noiseSheet` to have a white
noise for the noise filtration, and `IsWalshIntegral.mono_filtration` to compare with
`nullAug ν 𝓖`); so `Z = Ẑ` by Proposition 7.3; Doob–Dynkin gives `H`; `IsWalshIntegral.transfer` and Proposition 7.3 on the
other space conclude. The universe `u` of the other spaces is a separate universe variable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

universe u

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Uniqueness in law for (7.13)**: `Z = H(noise)` almost everywhere on `Ω × [0,T] × ℝ`, and
every solution of (7.13) on any space carrying a white noise is `H` of its noise. -/
theorem IsWeakMild.exists_noise_functional {T : ℝ} (hT : 0 < T) {𝓖 : Filtration ℝ≥0 mΩ}
    {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsWeakMild T 𝓖 S Z ν) :
    ∃ H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ,
      Measurable (fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2) ∧
      (∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
        Z p.2.1 p.2.2 p.1 = H (noiseMap S p.1) p.2.1 p.2.2) ∧
      ∀ {Ω₂ : Type u} {m₂ : MeasurableSpace Ω₂} {𝓖₂ : Filtration ℝ≥0 m₂}
        {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₂ : Measure Ω₂} {Z₂ : ℝ → ℝ → Ω₂ → ℝ},
        IsWhiteNoise 𝓖₂ S₂ ν₂ → IsWeakMild T 𝓖₂ S₂ Z₂ ν₂ →
        ∀ᵐ p ∂(ν₂.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
          Z₂ p.2.1 p.2.2 p.1 = H (noiseMap S₂ p.1) p.2.1 p.2.2 := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  -- `Ẑ`, the projection of `Z 𝟙_{[0,T]}` onto the noise, solves (7.13), so `Z = Ẑ` (Prop 7.3)
  have hL2 := hZ.noiseFun_memLp
  have heq := prop_7_3 hS.nullAug hT (hZ.noiseFun_mono (le_nullAug ν 𝓖)) (hZ.noiseFun_proj hS)
  -- Doob–Dynkin: `Ẑ = G(N, t, x)`
  obtain ⟨G, hG, hGe⟩ := hS.noiseFun_exists_factor hL2
  have hle : ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume) ≤
      ν.prod (volume : Measure (ℝ × ℝ)) := by
    rw [noiseFun_prod_restrict_eq]
    exact Measure.restrict_le_self
  have hZH : ∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
      Z p.2.1 p.2.2 p.1 = G (noiseMap S p.1, p.2) := by
    filter_upwards [heq, (Measure.absolutelyContinuous_of_le hle).ae_le hGe] with p h1 h2
    exact h1.trans h2
  refine ⟨fun w s y => G (w, s, y), hG, hZH, ?_⟩
  intro Ω₂ m₂ 𝓖₂ S₂ ν₂ Z₂ hS₂ hZ₂
  -- `G(N, t, x)` solves (7.13) on `Ω`, hence `G(N₂, t, x)` on `Ω₂`; Prop 7.3 on `Ω₂`
  have hY : IsWeakMild T 𝓖 S (fun s y ω => G (noiseMap S ω, s, y)) ν :=
    hZ.noiseFun_congr hS (hG.comp (hS.measurable_noiseMap.prodMap measurable_id)) hZH
  exact prop_7_3 hS₂ hT hZ₂ (hY.noiseFun_transfer hS hS₂ hG)

end QSSEPtoKPZ
