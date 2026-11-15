/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Defs
public import QSSEPtoKPZ.FiniteSystems.WaveIto
public import QSSEPtoKPZ.WaveFunction.EquationP
public import QSSEPtoKPZ.WaveFunction.Linear
public import QSSEPtoKPZ.Tightness.ExpMomentsAux

/-!
# The law of the random walk: mass, exponential moments, tails (task L7)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L7.
`docs/stage5-design.md`, Sections 1.2 (e), 3.4 (L7).

`p_s = rwKernel s` is defined analytically (Stage 2, `p_s = e^{sΔ} δ₀`). Its probabilistic
properties are obtained here from a realization of the wave function on `ℤ` (hypotheses `hB`,
`hψ`; every use in Section 8 has one): `𝔼 P(s,x) = p_s(x)` (Proposition 2.2), `∑ₓ P(s,x) = 1`
(Lemma 2.3) and, for the exponential moment, Lemma 2.3 (1) with
`α_t(x) = e^{r x - 2t(cosh r - 1)}` (`∂_t α + Δα = 0`).

* `rwKernel_nonneg`, `hasSum_rwKernel`: `p_s ≥ 0`, `∑ₓ p_s(x) = 1` (`s ≥ 0`).
* `hasSum_exp_mul_rwKernel`: `∑ₓ e^{r x} p_s(x) = e^{2s(cosh r - 1)}`.
* `summable_rwTail`, `rwTail_nonneg`, `intervalIntegrable_rwTail`, `rwTail_le` (Chernoff:
  `𝖯(|X_s| ≥ L) ≤ 2 e^{-rL + 2s(cosh r - 1)}`, `r ≥ 0`), `cosh_sub_one_le`
  (`cosh r - 1 ≤ (2/3) r²` on `[0,1]`).

Proof of the exponential moments: with `α_s(x) = e^{r x - 2s(cosh r - 1)}` (Stage 3's
`expMomAlpha 1 (r - θ_1)`), `N(s) = ∑ₓ α_s(x) P(s,x)` has `𝔼 N(s) = 1` (`expMom_isCL2Mart`), the
series converges almost surely (domination (2.2), `tilt_ae_dom`), and Tonelli's theorem with
`𝔼 P(s,x) = p_s(x)` gives `∑ₓ α_s(x) p_s(x) = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- A Brownian family lives on a probability space (the law of `B i 0 - B i 0` is `N(0,0)`). -/
private lemma rwTail_isProb (hB : IsBrownianFamily 𝓕 B μ) : IsProbabilityMeasure μ :=
  (hB.gaussian (0, 0) 0 0 le_rfl).isProbabilityMeasure

/-- `P(s,x)` is integrable and `𝔼 P(s,x) = p_s(x)` for `s ≥ 0` (Proposition 2.2). -/
private lemma rwTail_integral_density (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {s : ℝ} (hs : 0 ≤ s) (x : ℤ) :
    Integrable (fun ω => density ψ ω s x) μ ∧ ∫ ω, density ψ ω s x ∂μ = rwKernel s x := by
  have := rwTail_isProb hB
  obtain ⟨-, -, -, -, -, h⟩ := prop_2_2 hB hψ
  simpa [Real.coe_toNNReal _ hs] using h s.toNNReal x

/-- `p_s(x) ≥ 0` for `s ≥ 0` (`p_s(x) = 𝔼 P(s,x)`). -/
theorem rwKernel_nonneg (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {s : ℝ} (hs : 0 ≤ s) (x : ℤ) : 0 ≤ rwKernel s x := by
  rw [← (rwTail_integral_density hB hψ hs x).2]
  exact integral_nonneg fun ω => tilt_density_nonneg ω s x

/-- `α_s(x) = e^{r x - 2s(cosh r - 1)}` is Stage 3's `expMomAlpha 1 (r - θ_1)`. -/
private lemma rwTail_alpha_eq (r s : ℝ) (x : ℤ) :
    expMomAlpha 1 (r - thetaN 1) s x =
      Real.exp (r * x) * Real.exp (-(2 * s * (Real.cosh r - 1))) := by
  have h : expMomTheta 1 (r - thetaN 1) = r := by simp [expMomTheta]
  rw [expMomAlpha, h, ← Real.exp_add]
  ring_nf

/-- **Core of the exponential moments**: `∑ₓ α_s(x) p_s(x) = 1` for
`α_s(x) = e^{r x - 2s(cosh r - 1)}`, `s ≥ 0`: `𝔼 ∑ₓ α_s(x) P(s,x) = 1` (Lemma 2.3 (1), Stage 3's
`expMom_isCL2Mart`), almost sure convergence of the series (domination (2.2)), Tonelli. -/
private lemma rwTail_hasSum_alpha (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (r : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun x : ℤ => expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x) 1 := by
  have := rwTail_isProb hB
  have hα0 : ∀ x, 0 ≤ expMomAlpha 1 (r - thetaN 1) s x := fun x => (Real.exp_pos _).le
  have hP := rwTail_integral_density hB hψ hs
  -- `𝔼 N(s) = 1`
  obtain ⟨-, hE⟩ := expMom_isCL2Mart hB hψ 1 (r - thetaN 1) (T := s + 1) (by linarith)
  have hE1 : ∫ ω, expMomN 1 (r - thetaN 1) ψ s ω ∂μ = 1 := hE s ⟨hs, by linarith⟩
  have hNi : Integrable (fun ω => expMomN 1 (r - thetaN 1) ψ s ω) μ :=
    Integrable.of_integral_ne_zero (by rw [hE1]; exact one_ne_zero)
  -- almost sure summability
  have hsum : ∀ᵐ ω ∂μ, Summable fun x => expMomAlpha 1 (r - thetaN 1) s x * density ψ ω s x := by
    filter_upwards [tilt_ae_dom hB hψ (a := |r| + 1) (by positivity)] with ω hω
    obtain ⟨K, hK⟩ := hω ⌈s⌉₊
    refine Summable.of_nonneg_of_le (fun x => mul_nonneg (hα0 x) (tilt_density_nonneg ω s x))
      (fun x => ?_) (tilt_summable_exp_neg_abs.mul_left K)
    have h1 := hK s ⟨hs, Nat.le_ceil s⟩ x
    have h2 : expMomAlpha 1 (r - thetaN 1) s x ≤ Real.exp (|r| * |(x : ℝ)|) := by
      have := expMom_alpha_le 1 (r - thetaN 1) hs x
      simpa [expMomTheta] using this
    have hd := tilt_density_nonneg (ψ := ψ) ω s x
    calc expMomAlpha 1 (r - thetaN 1) s x * density ψ ω s x
        ≤ Real.exp (|r| * |(x : ℝ)|) * density ψ ω s x := by gcongr
      _ = Real.exp ((|r| + 1) * |(x : ℝ)|) * density ψ ω s x * Real.exp (-|(x : ℝ)|) := by
          rw [show (|r| + 1) * |(x : ℝ)| = |r| * |(x : ℝ)| + |(x : ℝ)| by ring, Real.exp_add,
            Real.exp_neg]
          field_simp
      _ ≤ K * Real.exp (-|(x : ℝ)|) := by gcongr
  -- Tonelli
  have hint : ∀ x, Integrable (fun ω => expMomAlpha 1 (r - thetaN 1) s x * density ψ ω s x) μ :=
    fun x => (hP x).1.const_mul _
  have hlin : ∀ x, ∫⁻ ω, ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * density ψ ω s x) ∂μ
      = ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x) := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hint x)
      (ae_of_all _ fun ω => mul_nonneg (hα0 x) (tilt_density_nonneg ω s x)),
      integral_const_mul, (hP x).2]
  have key : ∑' x, ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x) = 1 := by
    calc ∑' x, ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x)
        = ∑' x, ∫⁻ ω, ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * density ψ ω s x) ∂μ :=
          tsum_congr fun x => (hlin x).symm
      _ = ∫⁻ ω, ∑' x, ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * density ψ ω s x) ∂μ :=
          (lintegral_tsum fun x => (hint x).aemeasurable.ennreal_ofReal).symm
      _ = ∫⁻ ω, ENNReal.ofReal (expMomN 1 (r - thetaN 1) ψ s ω) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsum] with ω hω
          rw [expMomN, ENNReal.ofReal_tsum_of_nonneg
            (fun x => mul_nonneg (hα0 x) (tilt_density_nonneg ω s x)) hω]
      _ = ENNReal.ofReal (∫ ω, expMomN 1 (r - thetaN 1) ψ s ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hNi
            (ae_of_all _ fun ω => expMomN_nonneg _ _ _ _)).symm
      _ = 1 := by rw [hE1, ENNReal.ofReal_one]
  have hnn : ∀ x, 0 ≤ expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x :=
    fun x => mul_nonneg (hα0 x) (rwKernel_nonneg hB hψ hs x)
  have hS : Summable fun x => expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x := by
    have := ENNReal.summable_toReal
      (f := fun x => ENNReal.ofReal (expMomAlpha 1 (r - thetaN 1) s x * rwKernel s x))
      (by rw [key]; exact ENNReal.one_ne_top)
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  have h1 := ENNReal.ofReal_tsum_of_nonneg hnn hS
  rw [key, ENNReal.ofReal_eq_one] at h1
  have h2 := hS.hasSum
  rwa [h1] at h2

/-- `∑ₓ p_s(x) = 1` for `s ≥ 0`. -/
theorem hasSum_rwKernel (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {s : ℝ} (hs : 0 ≤ s) : HasSum (rwKernel s) 1 := by
  have h := rwTail_hasSum_alpha hB hψ 0 hs
  simp only [rwTail_alpha_eq] at h
  simpa using h

/-- **Exponential moments of the random walk**: `∑ₓ e^{r x} p_s(x) = e^{2s(cosh r - 1)}` for
`s ≥ 0` and `r ∈ ℝ`. -/
theorem hasSum_exp_mul_rwKernel (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    (r : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun x : ℤ => Real.exp (r * x) * rwKernel s x)
      (Real.exp (2 * s * (Real.cosh r - 1))) := by
  convert (rwTail_hasSum_alpha hB hψ r hs).mul_right (Real.exp (2 * s * (Real.cosh r - 1)))
    using 1
  · funext x
    rw [rwTail_alpha_eq, Real.exp_neg]
    field_simp
  · ring

/-- The series `𝖯(|X_s| ≥ L) = ∑_{|x| ≥ L} p_s(x)` converges (`s ≥ 0`). -/
theorem summable_rwTail (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {s : ℝ} (hs : 0 ≤ s) (L : ℕ) :
    Summable fun x : ℤ => if (L : ℤ) ≤ |x| then rwKernel s x else 0 := by
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) (hasSum_rwKernel hB hψ hs).summable
  · split_ifs
    exacts [rwKernel_nonneg hB hψ hs x, le_rfl]
  · split_ifs
    exacts [le_rfl, rwKernel_nonneg hB hψ hs x]

/-- `𝖯(|X_s| ≥ L) ≥ 0` (`s ≥ 0`). -/
theorem rwTail_nonneg (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {s : ℝ} (hs : 0 ≤ s) (L : ℕ) : 0 ≤ rwTail s L := by
  refine tsum_nonneg fun x => ?_
  split_ifs
  exacts [rwKernel_nonneg hB hψ hs x, le_rfl]

/-- `s ↦ 𝖯(|X_s| ≥ L)` is integrable on `[0, S]`. -/
theorem intervalIntegrable_rwTail (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (L : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    IntervalIntegrable (fun s => rwTail s L) volume 0 S := by
  -- on `[0, S]`, `𝖯(|X_s| ≥ L) = 1 - ∑_{|x| < L} p_s(x)`, a continuous function of `s`
  have key : ∀ s : ℝ, 0 ≤ s →
      rwTail s L = 1 - ∑ x ∈ Finset.Ioo (-(L : ℤ)) L, rwKernel s x := by
    intro s hs
    have h1 := hasSum_rwKernel hB hψ hs
    have h2 : HasSum (fun x : ℤ => if (L : ℤ) ≤ |x| then 0 else rwKernel s x)
        (∑ x ∈ Finset.Ioo (-(L : ℤ)) L, rwKernel s x) := by
      have hz : ∀ x ∉ Finset.Ioo (-(L : ℤ)) L,
          (if (L : ℤ) ≤ |x| then 0 else rwKernel s x) = 0 := fun x hx => by
        rw [Finset.mem_Ioo, ← abs_lt, not_lt] at hx
        simp [hx]
      convert hasSum_sum_of_ne_finset_zero hz using 1
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_Ioo, ← abs_lt] at hx
      simp [not_le.2 hx]
      infer_instance
    have h3 := ((summable_rwTail hB hψ hs L).hasSum).add h2
    have e : (fun x : ℤ => (if (L : ℤ) ≤ |x| then rwKernel s x else 0) +
        (if (L : ℤ) ≤ |x| then 0 else rwKernel s x)) = rwKernel s := by
      funext x; split_ifs <;> simp
    rw [e] at h3
    have := h3.unique h1
    rw [rwTail]
    linarith
  have hc : Continuous fun s => 1 - ∑ x ∈ Finset.Ioo (-(L : ℤ)) L, rwKernel s x :=
    continuous_const.sub (continuous_finsetSum _ fun x _ => continuous_rwKernel x)
  refine (hc.intervalIntegrable 0 S).congr_ae ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => ?_)
  rw [Set.uIoc_of_le hS] at hs
  exact (key s hs.1.le).symm

/-- **Chernoff bound**: for `s ≥ 0`, `r ≥ 0`, `𝖯(|X_s| ≥ L) ≤ 2 e^{-rL + 2s(cosh r - 1)}`. -/
theorem rwTail_le (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (L : ℕ) :
    rwTail s L ≤ 2 * Real.exp (-r * L + 2 * s * (Real.cosh r - 1)) := by
  have hp := rwKernel_nonneg hB hψ hs
  have h1 := hasSum_exp_mul_rwKernel hB hψ r hs
  have h2 := hasSum_exp_mul_rwKernel hB hψ (-r) hs
  rw [Real.cosh_neg] at h2
  have h3 := (h1.add h2).mul_left (Real.exp (-r * L))
  have hle := hasSum_le (fun x => ?_) (summable_rwTail hB hψ hs L).hasSum h3
  · calc rwTail s L ≤ _ := hle
      _ = 2 * Real.exp (-r * L + 2 * s * (Real.cosh r - 1)) := by rw [Real.exp_add]; ring
  · split_ifs with hx
    · have hxL : (L : ℝ) ≤ |(x : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hx
      have hm : Real.exp (r * |(x : ℝ)|) ≤ Real.exp (r * x) + Real.exp (-r * x) := by
        rcases abs_cases (x : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]; linarith [Real.exp_pos (-r * x)]
        · rw [h, show r * -(x : ℝ) = -r * x by ring]; linarith [Real.exp_pos (r * x)]
      have he : 1 ≤ Real.exp (-r * L) * Real.exp (r * |(x : ℝ)|) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      have h4 : 1 ≤ Real.exp (-r * L) * (Real.exp (r * x) + Real.exp (-r * x)) :=
        he.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
      calc rwKernel s x ≤ Real.exp (-r * L) * (Real.exp (r * x) + Real.exp (-r * x)) *
            rwKernel s x := le_mul_of_one_le_left (hp x) h4
        _ = _ := by ring
    · have := hp x
      positivity

/-- `cosh r - 1 ≤ (2/3) r²` for `r ∈ [0, 1]`. -/
theorem cosh_sub_one_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Real.cosh r - 1 ≤ 2 / 3 * r ^ 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => 2 / 3 * x ^ 2 - Real.cosh x)
      (4 / 3 * x - Real.sinh x) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_mul (2 / 3 : ℝ)).sub (Real.hasDerivAt_cosh x)
    convert this using 1
    push_cast
    ring
  have hc1 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have := Real.exp_one_lt_d9
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    linarith
  have hmono : MonotoneOn (fun x => 2 / 3 * x ^ 2 - Real.cosh x) (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
      fun x hx => ?_
    rw [interior_Icc] at hx
    have hx0 := hx.1.le
    have hx1 := hx.2.le
    obtain ⟨-, h2⟩ := sinh_sub_self_bounds hx0
    have hcx : Real.cosh x ≤ 2 := le_trans
      (Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hx0, abs_one]; exact hx1)) hc1
    have h3 : x ^ 3 ≤ x := by
      simpa using pow_le_pow_of_le_one hx0 hx1 (by norm_num : 1 ≤ 3)
    have h4 : x ^ 3 / 6 * Real.cosh x ≤ x / 3 := by nlinarith [pow_nonneg hx0 3]
    linarith
  have := hmono ⟨le_rfl, zero_le_one⟩ ⟨h0, h1⟩ h0
  norm_num at this
  linarith

end QSSEPtoKPZ
