/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Prop72Noise
public import QSSEPtoKPZ.Uniqueness.HeatTest
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.WhiteNoise.Prop72Step3

/-!
# Proposition 7.2: representation with a white noise

STATEMENT FILE (task T0″ of Stage 4, `docs/stage4-statements.md`); the proof is task J2, in this
file (Steps 3 and 4 of the article, from Steps 1–2 = `prop72_noise`, task J1).

"Let `𝒵` and `Z` be as in Proposition 7.1" is rendered by hypotheses equal to the conclusions
(1)–(3) of `prop_7_1`, for an arbitrary filtration `𝒢` (decision D7″); the hypothesis
`𝒵(0) = δ₀` (1) is used in Step 3 (it gives `M^φ(0) = 0`; without it the statement is false:
`𝒵 ≡ 0`, `Z ≡ 0`, `docs/stage4-audit.md`, E1); "possibly after enlarging the
probability space" by the product with an arbitrary probability space carrying a white noise
`S''`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Proposition 7.2**, with (7.8). Let `Y` be a random path in `C([0,T], ℳ₊)` (the process
`𝒵`) with `𝒵(0) = δ₀` almost surely (Proposition 7.1 (1)), `𝒢` a filtration, and `Z` a
nonnegative random field, predictable for `𝒢`, with (7.1),
such that almost surely `Y(t)(dx) = Z(t,x) dx` for almost every `t ∈ [0,T]`, and such that for
every `φ ∈ C_b^{1,3}([0,T] × ℝ)` the process `M^φ` of (7.2) is a continuous square-integrable
`𝒢`-martingale with bracket (7.3). Let `S''` be a white noise on another probability space
`Ω''`. Then on `Ω × Ω''` (product measure) there are a filtration `𝒢̄` containing `𝒢` and a white
noise `ξ` for `𝒢̄` (distribution function `S`, on all of `ℝ₊ × ℝ`) such that for every
`f ∈ C_c^∞(ℝ)` and every `t ∈ (0,T]`, almost surely,
`𝒵(t;f) = ∫ g_t(x) f(x) dx + ∫_0^t ∫_ℝ (g_{t-s} ⋆ f)(y) Z(s,y) ξ(ds dy)` (7.8),
the stochastic integral being the frozen `IsWalshIntegral` (which asserts that it exists). -/
theorem prop_7_2 {Pr : Measure Ω} [IsProbabilityMeasure Pr] {𝒢 : Filtration ℝ≥0 mΩ}
    {T : ℝ} (hT : 0 < T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    (hY0 : ∀ᵐ ω ∂Pr, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0)
    {Z : ℝ → ℝ → Ω → ℝ}
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (hZ0 : ∀ t x ω, 0 ≤ Z t x ω)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z t x ω))
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
    {𝓖'' : Filtration ℝ≥0 m''} {S'' : ℝ → ℝ → Ω'' → ℝ} (hS'' : IsWhiteNoise 𝓖'' S'' ν'') :
    ∃ (𝒢b : Filtration ℝ≥0 (mΩ.prod m'')) (S : ℝ → ℝ → Ω × Ω'' → ℝ),
      (∀ t, (𝒢 t).comap Prod.fst ≤ 𝒢b t) ∧ IsWhiteNoise 𝒢b S (Pr.prod ν'') ∧
      ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ t ∈ Set.Ioc (0 : ℝ) T,
        IsWalshIntegral 𝒢b S (Pr.prod ν'')
          (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω.1 else 0)
          (fun ω => pairFM (pathAt (Y ω.1) t) f - ∫ x, heatKernel t x * f x) := by
  -- Steps 1–2 (task J1): the white noise and (7.11) for simple integrands
  obtain ⟨𝒢b, S, hle, hS, hsimple⟩ := prop72_noise hT hY hZp hZ0 hZ2 hdens hmart hS''
  refine ⟨𝒢b, S, hle, hS, fun f hf hfc t ht => ?_⟩
  -- Step 4: the test function `φ_s = g_{t-s} ⋆ f` (`heatTest`), and Step 3 (7.12) for it
  obtain ⟨C, hC⟩ := isC13_heatTest hf hfc ht.1 T
  have h3 := prop72_walsh_timeDep hZ2 hmart hS hsimple hC ht.1.le ht.2
  refine h3.congr_ae hS ?_ ?_
  · -- the integrands differ only on the null set `{s = t}`
    have hnull : ((Pr.prod ν'').prod volume)
        (Set.univ ×ˢ ({t} ×ˢ Set.univ) : Set ((Ω × Ω'') × ℝ × ℝ)) = 0 := by
      rw [Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
    obtain ⟨ω, s, y⟩ := p
    have hst : s ≠ t := fun h => hp ⟨Set.mem_univ _, h, Set.mem_univ _⟩
    simp only [uncurryField]
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · simp only [hlt, hlt.le, and_true, heatTest, ↓reduceIte]
    · simp only [not_le.2 hgt, not_lt.2 hgt.le, and_false, ↓reduceIte]
  · -- the values: `M^φ(0) = 0` (since `𝒵(0) = δ₀`) and `M^φ(t) = 𝒵(t;f) - ∫ g_t f`
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hY0] with ω hω
    have h0 : limMart Y (heatTest t f) (heatTestDeriv t f) 0 ω.1 = 0 := by
      simp only [limMart, pairFM, hω, integral_dirac, intervalIntegral.integral_same,
        sub_self]
    have ht' : limMart Y (heatTest t f) (heatTestDeriv t f) t ω.1 =
        pairFM (pathAt (Y ω.1) t) f - ∫ x, heatKernel t x * f x := by
      have hint : ∫ s in (0 : ℝ)..t, pairFM (pathAt (Y ω.1) s)
          (fun x => heatTestDeriv t f s x + iteratedDeriv 2 (heatTest t f s) x / 2) = 0 := by
        have hz : Set.EqOn (fun s => pairFM (pathAt (Y ω.1) s)
            (fun x => heatTestDeriv t f s x + iteratedDeriv 2 (heatTest t f s) x / 2))
            (fun _ => (0 : ℝ)) (Set.uIcc 0 t) := by
          intro s hs
          rw [Set.uIcc_of_le ht.1.le] at hs
          simp only [heatTest_pde hf hfc ht.1 hs, pairFM, integral_zero]
        rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
      rw [limMart, hint, heatTest_self, heatTest_zero_zero ht.1, sub_zero]
    rw [ht', h0, sub_zero]

end QSSEPtoKPZ
