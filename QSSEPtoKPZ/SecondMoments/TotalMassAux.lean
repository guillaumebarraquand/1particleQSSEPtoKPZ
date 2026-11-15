/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Quadratic
public import QSSEPtoKPZ.TiltedField.Martingales
public import QSSEPtoKPZ.TiltedField.Identities
public import QSSEPtoKPZ.SecondMoments.FeynmanKac
public import QSSEPtoKPZ.Martingales.Stopping
public import QSSEPtoKPZ.Martingales.Doob
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Auxiliary results for Proposition 4.3 (task F1)

* Double series `∑_{x₁,x₂} z(x₁) z(x₂) g(x₂ - x₁)` for a summable `z ≥ 0` and a bounded `g`:
  summability on `ℤ²`, monotonicity in `g`, the case of a constant `g`.
* `totalMass_isCL2Mart_rev`: the martingale of the proof of Proposition 4.3 (1): for `t₀ ≥ 0`,
  `u ↦ 𝒵_n^{⊗2}(u; u_n(t₀ - u, x₂ - x₁))` is a continuous `L²` martingale on `[0, t₀ + 1]`
  (Lemma 3.2 applied to `f_u(x₁,x₂) = u_n(t₀ - u, x₂ - x₁)`, whose drift vanishes by (3.23) and
  (4.5)).
* `totalMass_continuousOn_pairZ2`: continuity of `t ↦ 𝒵_n^{⊗2}(t; g(x₂ - x₁))` (Lemma 3.2 with a
  function constant in time).
* Doob's `L²` bound in the form `𝔼 sup M² < ∞`, measurability at the time `τ + s`, and the
  adaptedness and the bounds `0 ≤ A_t ≤ A_T` of a bracket.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-! ### The tilted field is nonnegative -/

/-- `𝔷_n(t,x) ≥ 0`. -/
lemma totalMass_zN_nonneg (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) :
    0 ≤ zN n ψ ω t x := by
  unfold zN density; positivity

/-- `𝒲_n(t) = ∑ₓ 𝔷_n(t,x)`. -/
lemma totalMass_WN_eq (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (t : ℝ) (ω : Ω) :
    WN n ψ t ω = ∑' x, zN n ψ ω t x := by
  simp [WN, pairZ]

/-! ### Double series -/

/-- For a summable `z ≥ 0` and `|g| ≤ C`, `(x₁,x₂) ↦ z(x₁) z(x₂) g(x₂ - x₁)` is summable on
`ℤ²`. -/
lemma totalMass_summable_prod {z : ℤ → ℝ} (hz : Summable z) (hz0 : ∀ x, 0 ≤ z x) {g : ℤ → ℝ}
    {C : ℝ} (hg : ∀ r, |g r| ≤ C) :
    Summable (fun p : ℤ × ℤ => z p.1 * z p.2 * g (p.2 - p.1)) := by
  have h := (hz.mul_of_nonneg hz (fun x => hz0 x) (fun x => hz0 x)).mul_left C
  refine Summable.of_norm_bounded h fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hz0 _) (hz0 _)), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hg _) (mul_nonneg (hz0 _) (hz0 _))

/-- The double series is the sum over `ℤ²`. -/
lemma totalMass_tsum_eq {z : ℤ → ℝ} (hz : Summable z) (hz0 : ∀ x, 0 ≤ z x) {g : ℤ → ℝ}
    {C : ℝ} (hg : ∀ r, |g r| ≤ C) :
    ∑' x₁ : ℤ, ∑' x₂ : ℤ, z x₁ * z x₂ * g (x₂ - x₁) =
      ∑' p : ℤ × ℤ, z p.1 * z p.2 * g (p.2 - p.1) :=
  ((totalMass_summable_prod hz hz0 hg).tsum_prod).symm

/-- Monotonicity of `g ↦ ∑_{x₁,x₂} z(x₁) z(x₂) g(x₂ - x₁)`. -/
lemma totalMass_tsum_le {z : ℤ → ℝ} (hz : Summable z) (hz0 : ∀ x, 0 ≤ z x) {g h : ℤ → ℝ}
    {C : ℝ} (hg : ∀ r, |g r| ≤ C) (hh : ∀ r, |h r| ≤ C) (hgh : ∀ r, g r ≤ h r) :
    ∑' x₁ : ℤ, ∑' x₂ : ℤ, z x₁ * z x₂ * g (x₂ - x₁) ≤
      ∑' x₁ : ℤ, ∑' x₂ : ℤ, z x₁ * z x₂ * h (x₂ - x₁) := by
  rw [totalMass_tsum_eq hz hz0 hg, totalMass_tsum_eq hz hz0 hh]
  exact (totalMass_summable_prod hz hz0 hg).tsum_le_tsum
    (fun p => mul_le_mul_of_nonneg_left (hgh _) (mul_nonneg (hz0 _) (hz0 _)))
    (totalMass_summable_prod hz hz0 hh)

/-- `∑_{x₁,x₂} z(x₁) z(x₂) c = c (∑ₓ z(x))²`. -/
lemma totalMass_tsum_const (z : ℤ → ℝ) (c : ℝ) :
    ∑' x₁ : ℤ, ∑' x₂ : ℤ, z x₁ * z x₂ * c = c * (∑' x, z x) ^ 2 := by
  simp_rw [mul_assoc, tsum_mul_left, tsum_mul_right]
  ring

/-- `0 ≤ ∑_{x₁,x₂} z z g ≤ C (∑ z)²` for `0 ≤ g ≤ C`. -/
lemma totalMass_tsum_bounds {z : ℤ → ℝ} (hz : Summable z) (hz0 : ∀ x, 0 ≤ z x) {g : ℤ → ℝ}
    {C : ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgC : ∀ r, g r ≤ C) :
    0 ≤ ∑' x₁ : ℤ, ∑' x₂ : ℤ, z x₁ * z x₂ * g (x₂ - x₁) ∧
      ∑' x₁ : ℤ, ∑' x₂ : ℤ, z x₁ * z x₂ * g (x₂ - x₁) ≤ C * (∑' x, z x) ^ 2 := by
  have hC : 0 ≤ C := (hg0 0).trans (hgC 0)
  have hg : ∀ r, |g r| ≤ C := fun r => by rw [abs_of_nonneg (hg0 r)]; exact hgC r
  have h0 : ∀ r, |(fun _ : ℤ => (0 : ℝ)) r| ≤ C := fun r => by simpa using hC
  have hc : ∀ r, |(fun _ : ℤ => C) r| ≤ C := fun r => by simp [abs_of_nonneg hC]
  constructor
  · have := totalMass_tsum_le hz hz0 h0 hg hg0
    simpa using this
  · have := totalMass_tsum_le hz hz0 hg hc hgC
    rwa [totalMass_tsum_const] at this

/-! ### The martingale of the proof of Proposition 4.3 (1) -/

/-- The bounds `|u_n(t₀ - u, r)| ≤ C` and `|∂_t u_n(t₀ - u, r)| ≤ C` for `u ∈ [0, T]`. -/
private lemma uN_rev_bound (n t0 T : ℝ) :
    ∃ C : ℝ, ∀ u ∈ Set.Icc 0 T, ∀ r : ℤ,
      |uN n (t0 - u) r| ≤ C ∧ |generatorU n (uN n (t0 - u)) r| ≤ C := by
  have hc : Continuous (uN n) := (uN_regularity n).1.continuous
  have h1 : Continuous fun u => uN n (t0 - u) := hc.comp (continuous_const.sub continuous_id)
  have h2 : Continuous fun u => generatorU n (uN n (t0 - u)) := (generatorU n).continuous.comp h1
  obtain ⟨C1, hC1⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    h1.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    h2.continuousOn
  refine ⟨max C1 C2, fun u hu r => ⟨?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]
    exact ((lp.norm_apply_le_norm ENNReal.top_ne_zero _ r).trans (hC1 u hu)).trans
      (le_max_left _ _)
  · rw [← Real.norm_eq_abs]
    exact ((lp.norm_apply_le_norm ENNReal.top_ne_zero _ r).trans (hC2 u hu)).trans
      (le_max_right _ _)

/-- `∂_u u_n(t₀ - u, r) = -(A_n u_n(t₀ - u, ·))(r)`. -/
private lemma hasDerivAt_uN_rev (n t0 : ℝ) (r : ℤ) (t : ℝ) :
    HasDerivAt (fun u => uN n (t0 - u) r) (-(generatorU n (uN n (t0 - t)) r)) t := by
  have h1 : HasDerivAt (fun u => uN n (t0 - u)) ((-1 : ℝ) • generatorU n (uN n (t0 - t))) t :=
    ((uN_regularity n).2.1 (t0 - t)).scomp t ((hasDerivAt_id t).const_sub t0)
  have h2 := (coord r).hasFDerivAt.comp_hasDerivAt t h1
  simpa [Function.comp_def] using h2

/-- The drift of Lemma 3.2 vanishes for `f_u(x₁,x₂) = u_n(t₀ - u, x₂ - x₁)`: by (3.23),
`𝒬^{θ_n} f_u = c_n 𝓡 u_n(t₀ - u, ·)(x₂ - x₁)`, and (4.5). -/
private lemma drift_uN_rev (n t0 s : ℝ) (x₁ x₂ : ℤ) :
    -(generatorU n (uN n (t0 - s)) (x₂ - x₁)) +
      n / 2 * tiltedInclGen (thetaN n) (fun y₁ y₂ => uN n (t0 - s) (y₂ - y₁)) x₁ x₂ +
      n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then uN n (t0 - s) (x₂ - x₁) else 0) = 0 := by
  rw [tiltedInclGen_diff (thetaN n) (g := ⇑(uN n (t0 - s))) (fun r => uN_neg n _ r),
    generatorU_eq, genOp_apply, abs_sub_comm x₁ x₂]
  unfold cN
  split_ifs <;> ring

/-- **The martingale of the proof of Proposition 4.3 (1).** For `n ≥ 1` and `t₀ ≥ 0`, almost
surely `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`, and
`u ↦ 𝒵_n^{⊗2}(u; u_n(t₀ - u, x₂ - x₁)) - u_n(t₀, 0)` is a continuous `L²` `(𝓕ⁿ_t)`-martingale on
`[0, t₀ + 1]`: Lemma 3.2 applied to `f_u(x₁,x₂) = u_n(t₀ - u, x₂ - x₁)` (symmetric by evenness of
`u_n`), whose drift vanishes identically by (3.23) and (4.5). -/
theorem totalMass_isCL2Mart_rev [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {t0 : ℝ} (ht0 : 0 ≤ t0) :
    (∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
    IsCL2Mart (t0 + 1) (filtN n 𝓕)
      (fun t ω => pairZ2 n ψ ω t (fun x₁ x₂ => uN n (t0 - t) (x₂ - x₁)) - uN n t0 0) μ := by
  obtain ⟨C, hC⟩ := uN_rev_bound n t0 (t0 + 1)
  have key := lemma_3_2 hB hψ (T := t0 + 1) (C := C) hn (by linarith)
    (f := fun u x₁ x₂ => uN n (t0 - u) (x₂ - x₁))
    (f' := fun u x₁ x₂ => -(generatorU n (uN n (t0 - u)) (x₂ - x₁)))
    (fun t _ x₁ x₂ => by simp only; rw [← neg_sub x₂ x₁, uN_neg])
    (fun x₁ x₂ t _ => (hasDerivAt_uN_rev n t0 (x₂ - x₁) t).hasDerivWithinAt)
    (fun x₁ x₂ => (((coord (x₂ - x₁)).continuous.comp ((generatorU n).continuous.comp
      ((uN_regularity n).1.continuous.comp (continuous_const.sub continuous_id)))).neg
      ).continuousOn)
    (fun t ht x₁ x₂ => ⟨(hC t ht _).1, by rw [abs_neg]; exact (hC t ht _).2⟩)
  refine ⟨key.1.mono fun ω h => h.1, key.2.toIsCL2Mart.congr (ae_of_all _ fun ω t _ => ?_)⟩
  simp only [pairZ2, drift_uN_rev, mul_zero, tsum_zero, intervalIntegral.integral_zero, sub_zero]

/-- **Continuity of `t ↦ 𝒵_n^{⊗2}(t; g(x₂ - x₁))`** for an even bounded `g`, almost surely on
`[0, T]` (Lemma 3.2 with the function `f_t(x₁,x₂) = g(x₂ - x₁)`, constant in time: the
martingale and the integral of the drift are continuous). -/
theorem totalMass_continuousOn_pairZ2 [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T) {g : ℤ → ℝ}
    (hg : ∀ r, g (-r) = g r) {C : ℝ} (hgC : ∀ r, |g r| ≤ C) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t => pairZ2 n ψ ω t (fun x₁ x₂ => g (x₂ - x₁))) (Set.Icc 0 T) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have key := lemma_3_2 hB hψ (T := T) (C := C) hn hT
    (f := fun _ x₁ x₂ => g (x₂ - x₁)) (f' := fun _ _ _ => 0)
    (fun t _ x₁ x₂ => by rw [← neg_sub x₂ x₁, hg])
    (fun x₁ x₂ t _ => hasDerivWithinAt_const _ _ _)
    (fun x₁ x₂ => continuousOn_const)
    (fun t _ x₁ x₂ => ⟨hgC _, by simpa using hC⟩)
  filter_upwards [key.1, key.2.cont] with ω h1 h2
  have hprim := intervalIntegral.continuousOn_primitive_interval
    ((intervalIntegrable_iff' (μ := volume)).1 h1.2.1)
  rw [Set.uIcc_of_le hT.le] at hprim
  refine ((h2.add (continuousOn_const (c := g (0 - 0)))).add hprim).congr fun t _ => ?_
  simp only [Pi.add_apply]
  ring

/-! ### Measure-theoretic tools -/

/-- **Doob's `L²` inequality, consequence:** `𝔼[sup_{[0,T]} M²] < ∞` for a continuous `L²`
martingale on `[0, T]`, `T ≥ 0`. -/
theorem totalMass_lintegral_iSup_sq_ne_top [IsFiniteMeasure μ] {T : ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsCL2Mart T 𝓕 M μ) (hT : 0 ≤ T) :
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) ∂μ ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) ?_) hM.lintegral_iSup_sq_le.2
  have hL2 := hM.memLp ⟨T, hT⟩ le_rfl
  exact ((memLp_two_iff_integrable_sq hL2.aestronglyMeasurable).1 hL2).lintegral_lt_top.ne

/-- **Measurability at `τ + s`.** If `P` has almost surely continuous paths on `[0, T + s]` and is
adapted (up to null sets) to `𝓕`, and `τ ≤ T` is a stopping time of `𝓕ᵃ`, then `ω ↦ P_{τ+s}(ω)` is
almost everywhere strongly measurable. -/
theorem totalMass_aesm_stopped_add {P : ℝ → Ω → ℝ} {T s : ℝ} (hs : 0 ≤ s)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => P t ω) (Set.Icc 0 (T + s)))
    (hm : ∀ t : ℝ≥0, (t : ℝ) ≤ T + s → AEStronglyMeasurable[𝓕 t] (P t) μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    AEStronglyMeasurable (fun ω => P (τ ω + s) ω) μ := by
  have hρ := isStoppingTime_comp_of_monotone hτ (F := fun x => x + s.toNNReal)
    (fun a b h => add_le_add_left h _) (fun x => le_self_add)
  have hρT : ∀ ω, ((τ ω + s.toNNReal : ℝ≥0) : ℝ) ≤ T + s := fun ω => by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs]; linarith [hτT ω]
  have h := (aestronglyMeasurable_stoppedAt hc hm hρ hρT).mono hρ.measurableSpace_le
  have e : (fun ω => P ((τ ω + s.toNNReal : ℝ≥0) : ℝ) ω) = fun ω => P (τ ω + s) ω := by
    funext ω; rw [NNReal.coe_add, Real.coe_toNNReal _ hs]
  rwa [e] at h

/-- **Adaptedness of a bracket:** if `⟨M⟩ = A` on `[0, T]`, then `A_t` is `𝓕_t`-measurable up to
a null set (`A_t = M_t² - (M_t² - A_t)`). -/
theorem totalMass_bracket_adapted {T : ℝ} {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) : AEStronglyMeasurable[𝓕 t] (A t) μ := by
  have hM := aestronglyMeasurable_of_condExp_eq_self (h.condExp t t le_rfl ht)
  have hX := aestronglyMeasurable_of_condExp_eq_self (h.condExp_sq t t le_rfl ht)
  have e : A t = fun ω => M t ω ^ 2 - (M t ω ^ 2 - A t ω) := by funext ω; ring
  rw [e]
  exact (hM.pow 2).sub hX

/-- **Bounds on a bracket:** almost surely `0 ≤ A_t ≤ A_T` for `t ∈ [0, T]`. -/
theorem totalMass_bracket_bounds {T : ℝ} {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ)
    (hT : 0 ≤ T) : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ A t ω ∧ A t ω ≤ A T ω := by
  filter_upwards [h.zero, h.mono] with ω h0 hmono t ht
  have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  exact ⟨h0 ▸ hmono h0T ht ht.1, hmono ht hTT ht.2⟩

end QSSEPtoKPZ
