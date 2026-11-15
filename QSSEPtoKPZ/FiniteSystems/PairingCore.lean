/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.PairingAlgebra
public import QSSEPtoKPZ.ItoIntegral.ComplexIto

/-!
# Tools for the pairing identity (task L4)

`docs/stage5-design.md`, Section 1.2 (c).

* `IsItoProcessUpTo.congr_pos`, `IsCItoProcessUpTo.congr_pos`: only the values of the drift on
  `[0, τ]` and of the diffusion coefficients at times `s > 0` matter (the solutions of the wave
  equation are only known to vanish outside `Λ_L` at times `t ≥ 0`).
* `IsItoProcessUpTo.congr_null`: an Itô process may be changed on a measurable null set of `ω`
  (used for the unit-norm versions).
* `pairing_tsum_norm_sq`, `pairing_summable_norm_sq`: `∑ᵢ |c^ψ_{x,i}|² = |ψ(x+1)|² + |ψ(x-1)|²`.
* `pairing_isCIto_sum`: the product rule for `\bar a(x) b(x)` (`IsCItoProcessUpTo.conj_mul`),
  summed over a finite set of sites, for two processes whose coordinates are complex Itô
  processes with the coefficients of the wave equation.
* `pairing_eq_of_zero`: a complex Itô process without drift nor noise is constant.
* `pairing_norm_le_of_le_waveStop`, `pairing_waveStop_eventually`: the localizing times
  `τ_R ∧ N` of a process with continuous `ℓ²` paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-! ### Congruence lemmas -/

/-- **Congruence at positive times.** An Itô process up to `τ` stays one if its drift is changed
outside `[0, τ]` and its diffusion coefficients at times `s ≤ 0`. -/
theorem IsItoProcessUpTo.congr_pos (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {X a a' : ℝ → Ω → ℝ} {b b' : ι → ℝ → Ω → ℝ} (h : IsItoProcessUpTo 𝓖 μ B τ X a b)
    (ha : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω → a' s ω = a s ω)
    (hb : ∀ i (s : ℝ) ω, 0 < s → b' i s ω = b i s ω) :
    IsItoProcessUpTo 𝓖 μ B τ X a' b' := by
  set c : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ ω then b i s ω else 0 with hc
  set c' : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ ω then b' i s ω else 0 with hc'
  have hcc : ∀ i (s : ℝ) ω, 0 < s → c' i s ω = c i s ω := by
    intro i s ω hs
    simp only [hc, hc', hb i s ω hs]
  have hmeas : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then c' i p.1 p.2 else 0 := by
    intro i
    have e : (fun p : ℝ × Ω => if 0 < p.1 then c' i p.1 p.2 else 0) =
        fun p => if 0 < p.1 then c i p.1 p.2 else 0 := by
      funext p
      split_ifs with hp
      · exact hcc i _ _ hp
      · rfl
    rw [e]
    exact h.integrable.meas i
  have hE : ∀ T : ℝ, energy μ (fun i s ω => c i s ω - c' i s ω) T = 0 := by
    intro T
    rw [StochIntAux.energy_congr (g := fun _ _ _ => (0 : ℝ)) T fun i s ω hs => by simp [hcc i s ω hs]]
    simp [energy, pathEnergy]
  have hint : IsItoIntegrable 𝓖 μ c' := h.integrable.congr hmeas hE
  have hst : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B c t ω = stochInt 𝓖 μ B c' t ω := by
    have := fun n : ℕ => stochInt_congr hB h.integrable hint (T := n) (hE n)
    filter_upwards [ae_all_iff.2 this] with ω hω t
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    exact hω n t hn
  refine ⟨hint, ?_, ?_⟩
  · filter_upwards [h.drift] with ω hω
    refine hω.congr_ae (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_)
    rw [Set.uIoc_of_le (NNReal.coe_nonneg _)] at hs
    exact (ha ω s hs.1.le hs.2).symm
  · filter_upwards [h.eq, hst] with ω h1 h2 t
    rw [h1 t, h2 t]
    congr 2
    have hm0 : (0 : ℝ) ≤ ((min t (τ ω) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hm0] at hs
    exact (ha ω s hs.1 (hs.2.trans (NNReal.coe_le_coe.2 (min_le_right _ _)))).symm

/-- **Congruence at positive times** for complex Itô processes. -/
theorem IsCItoProcessUpTo.congr_pos (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {Z a a' : ℝ → Ω → ℂ} {b b' : ι → ℝ → Ω → ℂ} (h : IsCItoProcessUpTo 𝓖 μ B τ Z a b)
    (ha : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω → a' s ω = a s ω)
    (hb : ∀ i (s : ℝ) ω, 0 < s → b' i s ω = b i s ω) :
    IsCItoProcessUpTo 𝓖 μ B τ Z a' b' :=
  ⟨h.1.congr_pos hB (fun ω s h0 h1 => by rw [ha ω s h0 h1])
      (fun i s ω hs => by rw [hb i s ω hs]),
    h.2.congr_pos hB (fun ω s h0 h1 => by rw [ha ω s h0 h1])
      (fun i s ω hs => by rw [hb i s ω hs])⟩

/-- **Change on a null set.** An Itô process up to `τ` stays one (up to `τ'`) if the process,
the drift, the diffusion coefficients and the stopping time are changed on a measurable null set
of `ω`, provided the new stopped coefficients are jointly measurable. -/
theorem IsItoProcessUpTo.congr_null (hB : IsBrownianFamily 𝓖 B μ) {τ τ' : Ω → ℝ≥0}
    {X X' a a' : ℝ → Ω → ℝ} {b b' : ι → ℝ → Ω → ℝ} (h : IsItoProcessUpTo 𝓖 μ B τ X a b)
    {N : Set Ω} (hN0 : μ N = 0) (hτ : ∀ ω, ω ∉ N → τ' ω = τ ω)
    (hX : ∀ ω, ω ∉ N → ∀ t, X' t ω = X t ω) (ha : ∀ ω, ω ∉ N → ∀ s, a' s ω = a s ω)
    (hb : ∀ ω, ω ∉ N → ∀ i s, b' i s ω = b i s ω)
    (hmeas : ∀ i, Measurable fun p : ℝ × Ω =>
      if 0 < p.1 then (if p.1 ≤ τ' p.2 then b' i p.1 p.2 else 0) else 0) :
    IsItoProcessUpTo 𝓖 μ B τ' X' a' b' := by
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  set c : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ ω then b i s ω else 0 with hc
  set c' : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ' ω then b' i s ω else 0 with hc'
  have hcc : ∀ ω, ω ∉ N → ∀ i s, c' i s ω = c i s ω := by
    intro ω hω i s
    simp only [hc, hc', hτ ω hω, hb ω hω i s]
  have hE : ∀ T : ℝ, energy μ (fun i s ω => c i s ω - c' i s ω) T = 0 := by
    intro T
    refine (lintegral_congr_ae ?_).trans (lintegral_zero (μ := μ))
    filter_upwards [hNa] with ω hω
    simp [pathEnergy, hcc ω hω]
  have hint : IsItoIntegrable 𝓖 μ c' := h.integrable.congr hmeas hE
  have hst : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B c t ω = stochInt 𝓖 μ B c' t ω := by
    have := fun n : ℕ => stochInt_congr hB h.integrable hint (T := n) (hE n)
    filter_upwards [ae_all_iff.2 this] with ω hω t
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    exact hω n t hn
  refine ⟨hint, ?_, ?_⟩
  · filter_upwards [h.drift, hNa] with ω h1 hω
    rw [hτ ω hω]
    exact h1.congr (fun s _ => (ha ω hω s).symm)
  · filter_upwards [h.eq, hst, hNa] with ω h1 h2 hω t
    rw [hX ω hω, hX ω hω, hτ ω hω, h1 t, h2 t]
    congr 2
    exact intervalIntegral.integral_congr fun s _ => (ha ω hω s).symm

/-! ### The diffusion coefficients of the wave equation -/

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- The complex coefficients `c^ψ_{x,i}` vanish outside `waveSites x`. -/
theorem pairing_waveDiffC_of_notMem (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x : ℤ} {i : ℤ × Fin 2}
    (hi : i ∉ waveSites x) (s : ℝ) (ω : Ω) : waveDiffC ψ x i s ω = 0 := by
  simp [waveDiffC, waveDiffRe_of_notMem ψ hi, waveDiffIm_of_notMem ψ hi]

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- `∑ᵢ |c^ψ_{x,i}|²` converges (finitely many nonzero terms). -/
theorem pairing_summable_norm_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    Summable fun i => ‖waveDiffC ψ x i s ω‖ ^ 2 :=
  summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
    rw [pairing_waveDiffC_of_notMem ψ hi, norm_zero]
    norm_num

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- `∑ᵢ |c^ψ_{x,i}|² = |ψ(x+1)|² + |ψ(x-1)|²`. -/
theorem pairing_tsum_norm_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, ‖waveDiffC ψ x i s ω‖ ^ 2 = ‖ψ s ω (x + 1)‖ ^ 2 + ‖ψ s ω (x - 1)‖ ^ 2 := by
  have hre : Summable fun i => waveDiffRe ψ x i s ω ^ 2 :=
    summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffRe_of_notMem ψ hi]; norm_num
  have him : Summable fun i => waveDiffIm ψ x i s ω ^ 2 :=
    summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffIm_of_notMem ψ hi]; norm_num
  have e : ∀ i, ‖waveDiffC ψ x i s ω‖ ^ 2 = waveDiffRe ψ x i s ω ^ 2 + waveDiffIm ψ x i s ω ^ 2 :=
    fun i => by rw [Complex.sq_norm, Complex.normSq_apply, waveDiffC_re, waveDiffC_im]; ring
  simp only [e]
  rw [hre.tsum_add him, tsum_waveDiffRe_sq, tsum_waveDiffIm_sq]
  ring

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- The bounds required by the product rule, from `‖ψ_s‖ ≤ M`, for a drift coefficient
`D ≤ 2`. -/
theorem pairing_coef_bounds (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {D : ℕ} (hD : D ≤ 2) (x : ℤ) (s : ℝ)
    (ω : Ω) {M : ℝ} (hM : ‖ψ s ω‖ ≤ M) :
    ‖ψ s ω x‖ ≤ M + 2 * M ^ 2 ∧ ‖-((D : ℂ) / 2) * ψ s ω x‖ ≤ M + 2 * M ^ 2 ∧
      (∑' i, ‖waveDiffC ψ x i s ω‖ ^ 2) ≤ M + 2 * M ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hle : ∀ y, ‖ψ s ω y‖ ≤ M := fun y => (lp.norm_apply_le_norm two_ne_zero _ y).trans hM
  have h2M : 0 ≤ 2 * M ^ 2 := by positivity
  have hx := hle x
  refine ⟨by linarith, ?_, ?_⟩
  · have hD' : ‖-((D : ℂ) / 2)‖ ≤ 1 := by
      rw [norm_neg, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
      have : (D : ℝ) ≤ 2 := by exact_mod_cast hD
      linarith
    rw [norm_mul]
    nlinarith [norm_nonneg (-((D : ℂ) / 2)), norm_nonneg (ψ s ω x)]
  · rw [pairing_tsum_norm_sq]
    have h1 := hle (x + 1)
    have h2 := hle (x - 1)
    have := norm_nonneg (ψ s ω (x + 1))
    have := norm_nonneg (ψ s ω (x - 1))
    nlinarith

/-! ### The product rule summed over sites -/

/-- **The product rule for `∑_{x ∈ S} \bar a(x) b(x)`.** Let `τ` be a bounded stopping time and
`a`, `b` processes with continuous `ℓ²` paths and adapted coordinates, such that for every
`x ∈ S` the coordinates `a(x)`, `b(x)` are complex Itô processes up to `τ` with drifts
`-(D_a(x)/2) a(x)`, `-(D_b(x)/2) b(x)` (`D ≤ 2`) and the coefficients `waveDiffC` of the wave
equation, and `‖a_s‖, ‖b_s‖ ≤ M` on `[0, τ]`. Then `∑_{x ∈ S} \bar a(x) b(x)` is a complex Itô
process up to `τ`, with the drift and coefficients of the product rule summed over `S`. -/
theorem pairing_isCIto_sum {B : ℤ × Fin 2 → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓖 B μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T) (S : Finset ℤ) {Da Db : ℤ → ℕ} (hDa : ∀ x, Da x ≤ 2)
    (hDb : ∀ x, Db x ≤ 2) {a b : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (ha : ∀ x ∈ S, IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => a t ω x)
      (fun s ω => -((Da x : ℂ) / 2) * a s ω x) (waveDiffC a x))
    (hb : ∀ x ∈ S, IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => b t ω x)
      (fun s ω => -((Db x : ℂ) / 2) * b s ω x) (waveDiffC b x))
    (hac : ∀ ω, Continuous fun t : ℝ≥0 => a t ω) (hbc : ∀ ω, Continuous fun t : ℝ≥0 => b t ω)
    (haa : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => a t ω x)
    (hba : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => b t ω x) {M : ℝ}
    (hM : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω → ‖a s ω‖ ≤ M ∧ ‖b s ω‖ ≤ M) :
    IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => ∑ x ∈ S, conj (a t ω x) * b t ω x)
      (fun s ω => ∑ x ∈ S, (conj (a s ω x) * (-((Db x : ℂ) / 2) * b s ω x)
        + b s ω x * conj (-((Da x : ℂ) / 2) * a s ω x)
        + ∑' i, conj (waveDiffC a x i s ω) * waveDiffC b x i s ω))
      (fun i s ω => ∑ x ∈ S,
        (conj (a s ω x) * waveDiffC b x i s ω + b s ω x * conj (waveDiffC a x i s ω))) := by
  refine IsCItoProcessUpTo.finset_sum hB S fun x hx => ?_
  have hca : ∀ ω, Continuous fun t : ℝ≥0 => a t ω x := fun ω =>
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hac ω)
  have hcb : ∀ ω, Continuous fun t : ℝ≥0 => b t ω x := fun ω =>
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hbc ω)
  refine (ha x hx).conj_mul hB hτ hτb (hb x hx) hca hcb (fun t => haa t x) (fun t => hba t x)
    (fun ω s => pairing_summable_norm_sq a x s ω) (fun ω s => pairing_summable_norm_sq b x s ω)
    (K := M + 2 * M ^ 2) fun ω s hs0 hs => ?_
  obtain ⟨h1, h2⟩ := hM ω s hs0 hs
  obtain ⟨a1, a2, a3⟩ := pairing_coef_bounds a (hDa x) x s ω h1
  obtain ⟨b1, b2, b3⟩ := pairing_coef_bounds b (hDb x) x s ω h2
  exact ⟨a1, b1, a2, b2, a3, b3⟩

/-- **A complex Itô process without drift nor noise is constant**: almost surely,
`Z_{t∧τ} = Z_0` for all `t ≥ 0`. -/
theorem pairing_eq_of_zero (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0} {Z : ℝ → Ω → ℂ}
    (h : IsCItoProcessUpTo 𝓖 μ B τ Z (fun _ _ => 0) (fun _ _ _ => 0)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, Z (min t (τ ω) : ℝ≥0) ω = Z 0 ω := by
  filter_upwards [h.1.eq, h.2.eq, stochInt_zero (𝓖 := 𝓖) hB] with ω h1 h2 h0 t
  have e1 := h1 t
  have e2 := h2 t
  simp only [Complex.zero_re, Complex.zero_im, ite_self, intervalIntegral.integral_zero,
    add_zero] at e1 e2
  rw [show (fun (i : ι) (s : ℝ) (ω : Ω) => (0 : ℝ)) = 0 from rfl, h0 t, add_zero] at e1 e2
  exact Complex.ext e1 e2

/-! ### Localizing times -/

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- Before `τ_R ∧ N`, `‖ψ_s‖ ≤ max R ‖ψ_0‖`, for a process with continuous `ℓ²` paths. -/
theorem pairing_norm_le_of_le_waveStop {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) {R : ℝ} {N : ℝ≥0} {ω : Ω} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ waveStop ψ R N ω) : ‖ψ s ω‖ ≤ max R ‖ψ 0 ω‖ := by
  set s' : ℝ≥0 := ⟨s, hs0⟩ with hs'
  have hss : (s' : ℝ) = s := rfl
  have hle : s' ≤ waveStop ψ R N ω := by rw [← NNReal.coe_le_coe, hss]; exact hs
  rcases le_or_gt ‖ψ 0 ω‖ R with hR | hR
  · have := le_of_le_hitTime (X := fun t ω => ‖ψ t ω‖) (hc ω).norm
      (by simpa using hR) hle
    rw [hss] at this
    exact this.trans (le_max_left _ _)
  · have h0 : waveStop ψ R N ω ≤ 0 := inf_le_left.trans (csInf_le (OrderBot.bddBelow _)
      (Or.inl (show R ≤ ‖ψ ((0 : ℝ≥0) : ℝ) ω‖ by simpa using hR.le)))
    have : s = 0 := le_antisymm (by exact_mod_cast hs.trans (NNReal.coe_le_coe.2 h0)) hs0
    rw [this]
    exact le_max_right _ _

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- For a continuous path, `τ_{m+1} ∧ N = N` for all `m` large enough. -/
theorem pairing_waveStop_eventually {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => ψ t ω) (N : ℝ≥0) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → waveStop ψ ((m : ℝ) + 1) N ω = N := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := N)).exists_bound_of_continuousOn
    hc.norm.continuousOn
  obtain ⟨n0, hn0⟩ := exists_nat_ge M
  refine ⟨n0, fun m hm => hitTime_eq_of_forall_lt fun t ht => ?_⟩
  have h1 := hM t ⟨zero_le, ht.le⟩
  rw [Real.norm_eq_abs, abs_norm] at h1
  have h2 : (n0 : ℝ) ≤ m := by exact_mod_cast hm
  show ‖ψ t ω‖ < (m : ℝ) + 1
  linarith

end QSSEPtoKPZ
