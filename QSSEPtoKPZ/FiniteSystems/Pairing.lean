/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.PairingCore
public import QSSEPtoKPZ.FiniteSystems.Identification
public import QSSEPtoKPZ.ItoIntegral.ComplexIto
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The pairing identity on a box (task L4)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L4.
`docs/stage5-design.md`, Sections 1.2 (c), 3.4.

* `IsWaveIto.isCItoProcessUpTo`: the coordinates of an Itô solution are complex Itô processes.
* `IsWaveIto.inner_eq` (finite `L`): two Itô solutions on `Λ_L` driven by the same Brownian
  family keep their inner product: `⟨a_t, b_t⟩ = ⟨a_0, b_0⟩` for all `t`, almost surely.
* `IsWaveIto.inner_restrict_eq` (finite `L ≥ 1`): the Duhamel formula (8.2) read
  coordinatewise. For an Itô solution `a` on `Λ_L` and an Itô solution `ψ` on `ℤ` (both of norm
  `≤ 1`),
  `∑_{x ∈ Λ_L} \bar a_t(x) ψ_t(x) = ∑_{x ∈ Λ_L} \bar a_0(x) ψ_0(x)
     - (1/2) ∫_0^t (\bar a_s(L) ψ_s(L) + \bar a_s(-L) ψ_s(-L)) ds
     + ∫_0^t \bar a_s(L) i ψ_s(L+1) dW⁽ᴸ⁾_s + ∫_0^t \bar a_s(-L) i ψ_s(-L-1) d\bar W⁽⁻ᴸ⁻¹⁾_s`,
  the last two terms written with real Itô integrals of the real and imaginary parts of
  `pairingBoundaryCoef`.
(Proof: localize at `τ_R ∧ N` (`isStoppingTime_waveStop_of_continuous`, `IsItoProcessUpTo.mono`),
`IsCItoProcessUpTo.conj_mul` per site, `finset_sum`, `PairingAlgebra.lean`, then `R → ∞`.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate InnerProductSpace

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-! ### Auxiliary lemmas -/

/-- On a finite box, `⟪f, g⟫ = ∑_{x ∈ Λ_L} \bar f(x) g(x)` if `f` vanishes outside `Λ_L`. -/
theorem pairing_inner_eq_sum {L : ℕ} (f g : ℓ²(ℤ, ℂ)) (hf : ∀ x, x ∉ box L → f x = 0) :
    ⟪f, g⟫_ℂ = ∑ x ∈ Finset.Icc (-(L : ℤ)) L, conj (f x) * g x := by
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply']
  exact tsum_eq_sum fun x hx => by
    rw [hf x fun h => hx (pairing_mem_box_iff.1 h), map_zero, zero_mul]

/-- `D_L(x,x) ≤ 2`. -/
theorem pairing_degree_le (L : ℕ∞) (x : ℤ) : degree L x ≤ 2 := by
  unfold degree
  have h : ∀ y, (box L).indicator (1 : ℤ → ℕ) y ≤ 1 := fun y => by
    by_cases hy : y ∈ box L
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have := h (x + 1)
  have := h (x - 1)
  omega

/-- A path continuous on `[0, ∞)` is continuous at every `s > 0` as a function of `s ∈ ℝ`. -/
private lemma pairing_continuousAt {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) {s : ℝ} (hs : 0 < s) : ContinuousAt f s := by
  refine (hf.comp continuous_real_toNNReal).continuousAt.congr ?_
  filter_upwards [lt_mem_nhds hs] with r hr
  simp [Real.coe_toNNReal _ hr.le]

/-- A path continuous on `[0, ∞)` is continuous on `[0, ∞) ⊆ ℝ`. -/
private lemma pairing_continuousOn {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) : ContinuousOn f (Set.Ici 0) :=
  (hf.comp continuous_real_toNNReal).continuousOn.congr fun r hr => by
    simp [Real.coe_toNNReal _ (Set.mem_Ici.1 hr)]

/-- `|\bar z w / √2| ≤ 1` if `|z|, |w| ≤ 1`. -/
private lemma pairing_norm_le_one {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖z * w / (Real.sqrt 2 : ℂ)‖ ≤ 1 := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_mul]
  rw [div_le_one (by positivity)]
  nlinarith [norm_nonneg z, norm_nonneg w]

/-- The boundary coefficients are bounded by `1` when the coordinates are. -/
private lemma pairing_boundaryCoef_norm_le (L : ℕ) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω)
    (ha : ∀ y, ‖a s ω y‖ ≤ 1) (hψ : ∀ y, ‖ψ s ω y‖ ≤ 1) (i : ℤ × Fin 2) :
    ‖pairingBoundaryCoef L a ψ i s ω‖ ≤ 1 := by
  have hc : ∀ y, ‖conj (a s ω y)‖ ≤ 1 := fun y => by rw [Complex.norm_conj]; exact ha y
  have hI : ∀ y, ‖Complex.I * ψ s ω y‖ ≤ 1 := fun y => by
    rw [norm_mul, Complex.norm_I, one_mul]; exact hψ y
  have hn : ∀ y, ‖-ψ s ω y‖ ≤ 1 := fun y => by rw [norm_neg]; exact hψ y
  unfold pairingBoundaryCoef
  split_ifs
  · exact pairing_norm_le_one (hc _) (hI _)
  · exact pairing_norm_le_one (hc _) (hn _)
  · exact pairing_norm_le_one (hc _) (hI _)
  · exact pairing_norm_le_one (hc _) (hψ _)
  · simp

/-- The boundary coefficients vanish outside four indices. -/
private lemma pairing_boundaryCoef_eq_zero (L : ℕ) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω)
    {i : ℤ × Fin 2} (hi : i ∉ ({((L : ℤ), 0), ((L : ℤ), 1), (-(L : ℤ) - 1, 0),
      (-(L : ℤ) - 1, 1)} : Finset (ℤ × Fin 2))) : pairingBoundaryCoef L a ψ i s ω = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp [pairingBoundaryCoef, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

/-- **Itô-integrability of the boundary coefficients** (real or imaginary parts, `f = Re, Im`):
they are bounded, adapted, continuous at positive times. -/
private lemma pairing_boundaryCoef_isItoIntegrable [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ} {L : ℕ}
    {a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {f : ℂ → ℝ} (hf : Continuous f) (hfb : ∀ z, |f z| ≤ ‖z‖)
    (haa : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => a t ω x)
    (hψa : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hac : ∀ ω, Continuous fun t : ℝ≥0 => a t ω) (hψc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω)
    (hbd : ∀ ω (t : ℝ≥0), ‖a t ω‖ ≤ 1 ∧ ‖ψ t ω‖ ≤ 1) :
    IsItoIntegrable 𝓖 μ (fun i s ω => f (pairingBoundaryCoef L a ψ i s ω)) := by
  set T : Finset (ℤ × Fin 2) := {((L : ℤ), 0), ((L : ℤ), 1), (-(L : ℤ) - 1, 0),
    (-(L : ℤ) - 1, 1)} with hT
  have hf0 : f 0 = 0 := by simpa using hfb 0
  have hz : ∀ i ∉ T, ∀ s ω, f (pairingBoundaryCoef L a ψ i s ω) ^ 2 = 0 := fun i hi s ω => by
    rw [pairing_boundaryCoef_eq_zero L a ψ s ω hi, hf0]; norm_num
  refine isItoIntegrable_of_leftContinuous (K := (T.card : ℝ)) (fun ω s hs => ?_) (fun i t => ?_)
    (fun i ω s hs => ?_)
  · have hle : ∀ i, f (pairingBoundaryCoef L a ψ i s ω) ^ 2 ≤ 1 := fun i => by
      have h1 := pairing_boundaryCoef_norm_le L a ψ s ω
        (fun y => (lp.norm_apply_le_norm two_ne_zero _ y).trans (hbd ω ⟨s, hs.le⟩).1)
        (fun y => (lp.norm_apply_le_norm two_ne_zero _ y).trans (hbd ω ⟨s, hs.le⟩).2) i
      have h2 := (hfb (pairingBoundaryCoef L a ψ i s ω)).trans h1
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) h2
    refine ⟨summable_of_ne_finset_zero (s := T) fun i hi => hz i hi s ω, ?_⟩
    rw [tsum_eq_sum (s := T) fun i hi => hz i hi s ω]
    calc ∑ i ∈ T, f (pairingBoundaryCoef L a ψ i s ω) ^ 2 ≤ ∑ _i ∈ T, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = T.card := by simp
  · have hm : ∀ y, Measurable[𝓖 t] fun ω => conj (a t ω y) := fun y =>
      Complex.continuous_conj.measurable.comp (haa t y)
    have hc : Measurable[𝓖 t] fun ω => pairingBoundaryCoef L a ψ i t ω := by
      unfold pairingBoundaryCoef
      split_ifs
      · exact ((hm _).mul (measurable_const.mul (hψa t _))).div_const _
      · exact ((hm _).mul (hψa t _).neg).div_const _
      · exact ((hm _).mul (measurable_const.mul (hψa t _))).div_const _
      · exact ((hm _).mul (hψa t _)).div_const _
      · exact measurable_const
    exact hf.measurable.comp hc
  · have hA : ∀ y, ContinuousAt (fun r => conj (a r ω y)) s := fun y =>
      Complex.continuous_conj.continuousAt.comp (pairing_continuousAt
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 y).continuous.comp (hac ω)) hs)
    have hP : ∀ y, ContinuousAt (fun r => ψ r ω y) s := fun y =>
      pairing_continuousAt ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 y).continuous.comp (hψc ω)) hs
    have hc : ContinuousAt (fun r => pairingBoundaryCoef L a ψ i r ω) s := by
      unfold pairingBoundaryCoef
      split_ifs
      · exact ((hA _).mul (continuousAt_const.mul (hP _))).div_const _
      · exact ((hA _).mul (hP _).neg).div_const _
      · exact ((hA _).mul (continuousAt_const.mul (hP _))).div_const _
      · exact ((hA _).mul (hP _)).div_const _
      · exact continuousAt_const
    exact (hf.continuousAt.comp hc).continuousWithinAt

/-- The coordinate `ψ(x)`, `x ∈ Λ_L`, of an Itô solution is a complex Itô process up to every
deterministic time `N`, with drift `-(D_L(x,x)/2) ψ(x)` and coefficients `waveDiffC ψ x`. -/
theorem IsWaveIto.isCItoProcessUpTo {𝓖 : Filtration ℝ≥0 mΩ} {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (h : IsWaveIto L 𝓖 B ψ0 ψ μ) {x : ℤ} (hx : x ∈ box L) (N : ℝ≥0) :
    IsCItoProcessUpTo 𝓖 μ B (fun _ => N) (fun t ω => ψ t ω x)
      (fun s ω => -((degree L x : ℂ) / 2) * ψ s ω x) (waveDiffC ψ x) := by
  have e1 : (fun s ω => (-((degree L x : ℂ) / 2) * ψ s ω x).re) =
      fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).re := by
    funext s ω
    simp [Complex.mul_re]
  have e2 : (fun s ω => (-((degree L x : ℂ) / 2) * ψ s ω x).im) =
      fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).im := by
    funext s ω
    simp [Complex.mul_im]
  have e3 : (fun i s ω => (waveDiffC ψ x i s ω).re) = waveDiffRe ψ x := by
    funext i s ω; simp
  have e4 : (fun i s ω => (waveDiffC ψ x i s ω).im) = waveDiffIm ψ x := by
    funext i s ω; simp
  unfold IsCItoProcessUpTo
  rw [e1, e2, e3, e4]
  exact ⟨h.re x hx N, h.im x hx N⟩

/-- **Conservation of inner products on a finite box.** Two Itô solutions `a`, `b` of the wave
equation on `Λ_L` (`L` finite), driven by the same Brownian family for the same filtration, with
initial conditions `a0`, `b0`: almost surely, `⟨a_t, b_t⟩ = ⟨a0, b0⟩` for all `t ≥ 0`. -/
theorem IsWaveIto.inner_eq [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ} {a0 b0 : ℓ²(ℤ, ℂ)} {a b : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (ha : IsWaveIto L 𝓖 B a0 a μ) (hb : IsWaveIto L 𝓖 B b0 b μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ⟪a t ω, b t ω⟫_ℂ = ⟪a0, b0⟫_ℂ := by
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have hsupp : ∀ {ψ0' : ℓ²(ℤ, ℂ)} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}, IsWaveIto L 𝓖 B ψ0' ψ μ →
      ∀ ω (s : ℝ), 0 ≤ s → ∀ x, x ∉ box L → ψ s ω x = 0 :=
    fun h ω s hs x hx => h.support ω ⟨s, hs⟩ x hx
  -- the pairing is constant up to `τ = τ_{n+1}(a) ∧ τ_{n+1}(b) ∧ N`
  have key : ∀ N n : ℕ, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (∑ x ∈ S, conj (a (min t (min (waveStop a ((n : ℝ) + 1) N ω)
        (waveStop b ((n : ℝ) + 1) N ω)) : ℝ≥0) ω x) *
        b (min t (min (waveStop a ((n : ℝ) + 1) N ω) (waveStop b ((n : ℝ) + 1) N ω)) : ℝ≥0) ω x)
        = ∑ x ∈ S, conj (a 0 ω x) * b 0 ω x := by
    intro N n
    set τ : Ω → ℝ≥0 := fun ω => min (waveStop a ((n : ℝ) + 1) N ω)
      (waveStop b ((n : ℝ) + 1) N ω) with hτdef
    have hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0)) := by
      have := (isStoppingTime_waveStop_of_continuous ha.adapted ha.continuous ((n : ℝ) + 1) N).min
        (isStoppingTime_waveStop_of_continuous hb.adapted hb.continuous ((n : ℝ) + 1) N)
      simpa only [hτdef, WithTop.coe_min] using this
    have hτN : ∀ ω, τ ω ≤ (N : ℝ≥0) := fun ω => (min_le_left _ _).trans (waveStop_le _ _ _ _)
    have hmono : ∀ {ψ0' : ℓ²(ℤ, ℂ)} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}, IsWaveIto L 𝓖 B ψ0' ψ μ →
        ∀ x ∈ S, IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => ψ t ω x)
          (fun s ω => -((degree L x : ℂ) / 2) * ψ s ω x) (waveDiffC ψ x) := by
      intro ψ0' ψ h x hx
      have h1 := h.isCItoProcessUpTo (pairing_mem_box_iff.2 hx) N
      exact ⟨h1.1.mono hB hτ hτN, h1.2.mono hB hτ hτN⟩
    set M : ℝ := max ((n : ℝ) + 1) (max ‖a0‖ ‖b0‖) with hM
    have hbd : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω → ‖a s ω‖ ≤ M ∧ ‖b s ω‖ ≤ M := by
      intro ω s hs0 hs
      have h1 := pairing_norm_le_of_le_waveStop ha.continuous hs0
        (hs.trans (NNReal.coe_le_coe.2 (min_le_left _ _)))
      have h2 := pairing_norm_le_of_le_waveStop hb.continuous hs0
        (hs.trans (NNReal.coe_le_coe.2 (min_le_right _ _)))
      rw [ha.init] at h1
      rw [hb.init] at h2
      exact ⟨h1.trans (max_le_max le_rfl (le_max_left _ _)),
        h2.trans (max_le_max le_rfl (le_max_right _ _))⟩
    have hP := pairing_isCIto_sum hB hτ ⟨N, hτN⟩ S (pairing_degree_le L) (pairing_degree_le L)
      (hmono ha) (hmono hb) ha.continuous hb.continuous ha.adapted hb.adapted hbd
    have hP0 := hP.congr_pos hB (a' := fun _ _ => 0) (b' := fun _ _ _ => 0)
      (fun ω s hs0 _ => (pairing_drift_sum_box L a b s ω (hsupp ha ω s hs0)
        (hsupp hb ω s hs0)).symm)
      (fun i s ω hs => (pairing_coef_sum_box L a b s ω (hsupp ha ω s hs.le)
        (hsupp hb ω s hs.le) i).symm)
    exact pairing_eq_of_zero hB hP0
  have key' := ae_all_iff.2 fun N : ℕ => ae_all_iff.2 fun n : ℕ => key N n
  filter_upwards [key'] with ω hω t
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨n1, hn1⟩ := pairing_waveStop_eventually (ha.continuous ω) N
  obtain ⟨n2, hn2⟩ := pairing_waveStop_eventually (hb.continuous ω) N
  have e := hω N (max n1 n2) t
  rw [hn1 _ (le_max_left _ _), hn2 _ (le_max_right _ _), min_self,
    min_eq_left (show t ≤ (N : ℝ≥0) from by exact_mod_cast hN)] at e
  rw [pairing_inner_eq_sum _ _ (ha.support ω t), pairing_inner_eq_sum _ _
    (fun x hx => by rw [← ha.init ω]; exact ha.support ω 0 x hx), e, ha.init ω, hb.init ω]

/-- **Duhamel identity for the restriction to `Λ_L` of the wave function on `ℤ`** (the
coordinates of (8.2): `(U_t^* φ_t)(y) = ⟨U_t e_y, φ_t⟩`). Let `L ≥ 1`, `a` an Itô solution on
`Λ_L` and `ψ` an Itô solution on `ℤ`, driven by the same Brownian family for the same filtration,
with `‖a_t‖ ≤ 1` and `‖ψ_t‖ ≤ 1` for all `t`, `ω`. Then the real and imaginary parts of the
boundary coefficients are Itô-integrable and, almost surely, for all `t ≥ 0`,
`∑_{x ∈ Λ_L} \bar a_t(x) ψ_t(x) = ∑_{x ∈ Λ_L} \bar a0(x) ψ0(x)
   - (1/2) ∫_0^t (\bar a_s(L) ψ_s(L) + \bar a_s(-L) ψ_s(-L)) ds
   + (I_t(Re c) + i I_t(Im c))`, `c = pairingBoundaryCoef L a ψ`. -/
theorem IsWaveIto.inner_restrict_eq [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ} (hL : 1 ≤ L) {a0 ψ0 : ℓ²(ℤ, ℂ)}
    {a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (ha : IsWaveIto L 𝓖 B a0 a μ) (hψ : IsWaveIto ⊤ 𝓖 B ψ0 ψ μ)
    (hbd : ∀ ω (t : ℝ≥0), ‖a t ω‖ ≤ 1 ∧ ‖ψ t ω‖ ≤ 1) :
    IsItoIntegrable 𝓖 μ (fun i s ω => (pairingBoundaryCoef L a ψ i s ω).re) ∧
    IsItoIntegrable 𝓖 μ (fun i s ω => (pairingBoundaryCoef L a ψ i s ω).im) ∧
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (∑ x ∈ Finset.Icc (-(L : ℤ)) L, conj (a t ω x) * ψ t ω x) =
        (∑ x ∈ Finset.Icc (-(L : ℤ)) L, conj (a0 x) * ψ0 x)
        - (1 / 2 : ℂ) * (∫ s in (0 : ℝ)..t,
            (conj (a s ω L) * ψ s ω L + conj (a s ω (-L)) * ψ s ω (-L)))
        + ((stochInt 𝓖 μ B (fun i s ω => (pairingBoundaryCoef L a ψ i s ω).re) t ω : ℂ)
          + Complex.I *
            (stochInt 𝓖 μ B (fun i s ω => (pairingBoundaryCoef L a ψ i s ω).im) t ω : ℂ)) := by
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  set c := pairingBoundaryCoef L a ψ with hcdef
  have hcre : IsItoIntegrable 𝓖 μ (fun i s ω => (c i s ω).re) :=
    pairing_boundaryCoef_isItoIntegrable Complex.continuous_re Complex.abs_re_le_norm ha.adapted
      hψ.adapted ha.continuous hψ.continuous hbd
  have hcim : IsItoIntegrable 𝓖 μ (fun i s ω => (c i s ω).im) :=
    pairing_boundaryCoef_isItoIntegrable Complex.continuous_im Complex.abs_im_le_norm ha.adapted
      hψ.adapted ha.continuous hψ.continuous hbd
  refine ⟨hcre, hcim, ?_⟩
  have hsupp : ∀ ω (s : ℝ), 0 ≤ s → ∀ x, x ∉ box L → a s ω x = 0 :=
    fun ω s hs x hx => ha.support ω ⟨s, hs⟩ x hx
  set g : ℝ → Ω → ℂ := fun s ω =>
    conj (a s ω L) * ψ s ω L + conj (a s ω (-L)) * ψ s ω (-L) with hgdef
  -- the identity up to every deterministic time `N`
  have key : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ) ≤ N →
      (∑ x ∈ S, conj (a t ω x) * ψ t ω x) = (∑ x ∈ S, conj (a 0 ω x) * ψ 0 ω x)
        + (∫ s in (0 : ℝ)..t, (-(1 / 2 : ℂ) * g s ω))
        + ((stochInt 𝓖 μ B (fun i s ω => (c i s ω).re) t ω : ℂ)
          + Complex.I * (stochInt 𝓖 μ B (fun i s ω => (c i s ω).im) t ω : ℂ)) := by
    intro N
    have hτ : IsStoppingTime 𝓖 (fun ω => (((fun _ : Ω => (N : ℝ≥0)) ω : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓖 (N : ℝ≥0)
    have hA : ∀ x ∈ S, IsCItoProcessUpTo 𝓖 μ B (fun _ => (N : ℝ≥0)) (fun t ω => a t ω x)
        (fun s ω => -((degree L x : ℂ) / 2) * a s ω x) (waveDiffC a x) :=
      fun x hx => ha.isCItoProcessUpTo (pairing_mem_box_iff.2 hx) N
    have hΨ : ∀ x ∈ S, IsCItoProcessUpTo 𝓖 μ B (fun _ => (N : ℝ≥0)) (fun t ω => ψ t ω x)
        (fun s ω => -((degree ⊤ x : ℂ) / 2) * ψ s ω x) (waveDiffC ψ x) :=
      fun x _ => hψ.isCItoProcessUpTo (waveBox_top_mem x) N
    have hM : ∀ ω (s : ℝ), 0 ≤ s → s ≤ ((fun _ : Ω => (N : ℝ≥0)) ω : ℝ) →
        ‖a s ω‖ ≤ 1 ∧ ‖ψ s ω‖ ≤ 1 := fun ω s hs0 _ => hbd ω ⟨s, hs0⟩
    have hP := pairing_isCIto_sum hB hτ ⟨N, fun _ => le_rfl⟩ S (pairing_degree_le L)
      (pairing_degree_le ⊤) hA hΨ ha.continuous hψ.continuous ha.adapted hψ.adapted hM
    have hP1 := hP.congr_pos hB (a' := fun s ω => -(1 / 2 : ℂ) * g s ω) (b' := c)
      (fun ω s hs0 _ => (pairing_drift_sum_restrict hL a ψ s ω (hsupp ω s hs0)).symm)
      (fun i s ω hs => (pairing_coef_sum_restrict L a ψ s ω (hsupp ω s hs.le) i).symm)
    -- the stopped and unstopped Itô integrals agree on `[0, N]`
    have hcut : ∀ {f : ℂ → ℝ}, IsItoIntegrable 𝓖 μ (fun i s ω => f (c i s ω)) →
        IsItoIntegrable 𝓖 μ (fun i s ω => if s ≤ ((N : ℝ≥0) : ℝ) then f (c i s ω) else 0) →
        ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ) ≤ N →
          stochInt 𝓖 μ B (fun i s ω => if s ≤ ((N : ℝ≥0) : ℝ) then f (c i s ω) else 0) t ω =
            stochInt 𝓖 μ B (fun i s ω => f (c i s ω)) t ω := by
      intro f h1 h2
      refine stochInt_congr hB h2 h1 ?_
      have h0 : ∀ ω, pathEnergy (fun i s ω => (if s ≤ ((N : ℝ≥0) : ℝ) then f (c i s ω) else 0)
          - f (c i s ω)) (N : ℝ) ω = 0 := by
        intro ω
        unfold pathEnergy
        rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) fun s hs => by
          have hsN : s ≤ ((N : ℝ≥0) : ℝ) := by rw [NNReal.coe_natCast]; exact hs.2
          simp only [hsN, ↓reduceIte, sub_self, enorm_zero]
          simp]
        simp
      unfold energy
      simp only [h0, lintegral_zero]
    filter_upwards [hP1.1.eq, hP1.2.eq, hcut hcre hP1.1.integrable, hcut hcim hP1.2.integrable]
      with ω h1 h2 h3 h4 t ht
    have htN : t ≤ (N : ℝ≥0) := by exact_mod_cast ht
    have e1 := h1 t
    have e2 := h2 t
    rw [min_eq_left htN, h3 t ht] at e1
    rw [min_eq_left htN, h4 t ht] at e2
    have hint : IntervalIntegrable (fun s => -(1 / 2 : ℂ) * g s ω) volume 0 t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le t.coe_nonneg]
      have hA : ∀ y, ContinuousOn (fun s => conj (a s ω y)) (Set.Ici 0) := fun y =>
        Complex.continuous_conj.comp_continuousOn (pairing_continuousOn
          ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 y).continuous.comp (ha.continuous ω)))
      have hP : ∀ y, ContinuousOn (fun s => ψ s ω y) (Set.Ici 0) := fun y =>
        pairing_continuousOn ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 y).continuous.comp
          (hψ.continuous ω))
      exact (continuousOn_const.mul (((hA _).mul (hP _)).add ((hA _).mul (hP _)))).mono
        Set.Icc_subset_Ici_self
    have hre := (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    have him := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
    apply Complex.ext
    · simp only [Complex.add_re, hre, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im,
        neg_zero, add_zero]
      exact e1
    · simp only [Complex.add_im, him, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re,
        zero_add]
      exact e2
  have key' := ae_all_iff.2 key
  filter_upwards [key'] with ω hω t
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  rw [hω N t hN, intervalIntegral.integral_const_mul]
  simp only [ha.init ω, hψ.init ω]
  ring

end QSSEPtoKPZ
