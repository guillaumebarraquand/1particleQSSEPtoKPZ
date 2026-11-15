/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Identification
public import QSSEPtoKPZ.WaveFunction.Defs

/-!
# The density `P(x) = |ψ(x)|²` as an Itô process up to `τ_R ∧ N`; sums over boxes (task D2)

See `docs/stage2-design.md`, Section 1.2 (e), (f). Let `ψ̃` be a good version of the wave
function on `ℤ` (`IsGoodWave`) and `τ = τ_R ∧ N` (`waveStop`). Writing `ψ̃(y) = u_y + i v_y`,
the product rule (`IsItoProcessUpTo.mul`, task C6) applied to `u_x² + v_x²` gives:

* `IsGoodWave.isItoProcessUpTo_density`: `P(x) = |ψ̃(x)|²` is an Itô process up to `τ`, with drift
  `ΔP(x)` and diffusion coefficients `c_{x-1} - c_x`, where
  `c_x = waveCurrent ψ̃ x` are the coefficients of the current
  `J(x) = 2 ∫ Im(conj(ψ(x)) ψ(x+1) dW⁽ˣ⁾) = √2 ∫ (Im(conj ψ(x) ψ(x+1)) dB_{x,0} + Re(conj ψ(x) ψ(x+1)) dB_{x,1})`;
* `IsGoodWave.isItoProcessUpTo_boxMass`: summing over the box `|x| ≤ K`, the drift and the
  diffusion telescope: `∑_{|x| ≤ K} P(x)` has drift `P(K+1) - P(K) + P(-K-1) - P(-K)` (the flux
  through the boundary) and diffusion `c_{-K-1} - c_K`.

Algebraic facts on the currents: `∑ᵢ (c_x)ᵢ² = 2 P(x) P(x+1)` (`tsum_waveCurrent_sq`),
`∑ᵢ (c_x)ᵢ (c_y)ᵢ = 0` for `x ≠ y` (`tsum_waveCurrent_mul_waveCurrent`), and
`∑ᵢ (c_x - c_y)ᵢ² = 2 P(x) P(x+1) + 2 P(y) P(y+1)` for `x ≠ y` (`tsum_waveCurrent_sub_sq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The coefficients of the currents -/

/-- The diffusion coefficients of the current `J(x)`:
`dJ(x) = √2 (Im(conj ψ(x) ψ(x+1)) dB_{x,0} + Re(conj ψ(x) ψ(x+1)) dB_{x,1})`, that is
`dJ(x) = 2 Im(conj ψ(x) ψ(x+1) dW⁽ˣ⁾)` with `W⁽ˣ⁾ = (B_{x,0} + i B_{x,1})/√2` ((2.3)). -/
def waveCurrent (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) : ℝ :=
  if i = (x, 0) then Real.sqrt 2 * (conj (ψ s ω x) * ψ s ω (x + 1)).im
  else if i = (x, 1) then Real.sqrt 2 * (conj (ψ s ω x) * ψ s ω (x + 1)).re
  else 0

/-- The coefficients of `J(x)` vanish outside the two indices `(x,0)`, `(x,1)`. -/
lemma waveCurrent_of_ne (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x : ℤ} {i : ℤ × Fin 2} (h0 : i ≠ (x, 0))
    (h1 : i ≠ (x, 1)) (s : ℝ) (ω : Ω) : waveCurrent ψ x i s ω = 0 := by
  simp [waveCurrent, h0, h1]

/-- The coefficient of `J(x)` at `(x,0)`. -/
lemma waveCurrent_zero (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    waveCurrent ψ x (x, 0) s ω = Real.sqrt 2 * (conj (ψ s ω x) * ψ s ω (x + 1)).im := by
  simp [waveCurrent]

/-- The coefficient of `J(x)` at `(x,1)`. -/
lemma waveCurrent_one (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    waveCurrent ψ x (x, 1) s ω = Real.sqrt 2 * (conj (ψ s ω x) * ψ s ω (x + 1)).re := by
  simp [waveCurrent]

/-- The family `i ↦ (c_x)ᵢ gᵢ` is summable (finite support). -/
lemma summable_waveCurrent_mul (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (g : ℤ × Fin 2 → ℝ) (s : ℝ)
    (ω : Ω) : Summable fun i => waveCurrent ψ x i s ω * g i := by
  refine summable_of_ne_finset_zero (s := {(x, 0), (x, 1)}) fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  rw [waveCurrent_of_ne ψ hi.1 hi.2, zero_mul]

/-- `∑ᵢ (c_x)ᵢ gᵢ = (c_x)_{(x,0)} g_{(x,0)} + (c_x)_{(x,1)} g_{(x,1)}`. -/
lemma tsum_waveCurrent_mul (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (g : ℤ × Fin 2 → ℝ) (s : ℝ)
    (ω : Ω) : ∑' i, waveCurrent ψ x i s ω * g i =
      waveCurrent ψ x (x, 0) s ω * g (x, 0) + waveCurrent ψ x (x, 1) s ω * g (x, 1) := by
  rw [tsum_eq_sum (s := {(x, 0), (x, 1)}) fun i hi => ?_]
  · rw [Finset.sum_pair (by simp)]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [waveCurrent_of_ne ψ hi.1 hi.2, zero_mul]

/-- **Bracket density of a current**: `∑ᵢ (c_x)ᵢ² = 2 P(x) P(x+1)`, so that
`⟨J(x)⟩_t = 2 ∫_0^t P(s,x) P(s,x+1) ds` ((2.5)). -/
lemma tsum_waveCurrent_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, waveCurrent ψ x i s ω ^ 2 = 2 * density ψ ω s x * density ψ ω s (x + 1) := by
  have e := tsum_waveCurrent_mul ψ x (fun i => waveCurrent ψ x i s ω) s ω
  simp only [← sq] at e
  rw [e, waveCurrent_zero, waveCurrent_one, mul_pow, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), density, density, Complex.sq_norm,
    Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **Orthogonality of the currents**: `∑ᵢ (c_x)ᵢ (c_y)ᵢ = 0` for `x ≠ y`, so that
`⟨J(x), J(y)⟩ = 0` ((2.5)). -/
lemma tsum_waveCurrent_mul_waveCurrent (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x y : ℤ} (hxy : x ≠ y) (s : ℝ)
    (ω : Ω) : ∑' i, waveCurrent ψ x i s ω * waveCurrent ψ y i s ω = 0 := by
  rw [tsum_waveCurrent_mul, waveCurrent_of_ne ψ (x := y) (i := (x, 0)) (by simp [hxy]) (by simp),
    waveCurrent_of_ne ψ (x := y) (i := (x, 1)) (by simp) (by simp [hxy])]
  ring

/-- `∑ᵢ (c_x - c_y)ᵢ² = 2 P(x) P(x+1) + 2 P(y) P(y+1)` for `x ≠ y`. -/
lemma tsum_waveCurrent_sub_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x y : ℤ} (hxy : x ≠ y) (s : ℝ)
    (ω : Ω) : ∑' i, (waveCurrent ψ x i s ω - waveCurrent ψ y i s ω) ^ 2 =
      2 * density ψ ω s x * density ψ ω s (x + 1) +
        2 * density ψ ω s y * density ψ ω s (y + 1) := by
  have hx := summable_waveCurrent_mul ψ x (fun i => waveCurrent ψ x i s ω) s ω
  have hy := summable_waveCurrent_mul ψ y (fun i => waveCurrent ψ y i s ω) s ω
  have hxy' := summable_waveCurrent_mul ψ x (fun i => waveCurrent ψ y i s ω) s ω
  have e : (fun i => (waveCurrent ψ x i s ω - waveCurrent ψ y i s ω) ^ 2) = fun i =>
      waveCurrent ψ x i s ω * waveCurrent ψ x i s ω +
        waveCurrent ψ y i s ω * waveCurrent ψ y i s ω -
          2 * (waveCurrent ψ x i s ω * waveCurrent ψ y i s ω) := by
    funext i; ring
  rw [e, (hx.add hy).tsum_sub (hxy'.mul_left 2), hx.tsum_add hy, tsum_mul_left,
    tsum_waveCurrent_mul_waveCurrent ψ hxy]
  simp only [← sq, tsum_waveCurrent_sq]
  ring

/-- The diffusion of `P(x)`: `∑ᵢ (c_{x-1} - c_x)ᵢ² = 2 P(x-1) P(x) + 2 P(x) P(x+1)`. -/
lemma tsum_waveCurrent_sub_succ_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, (waveCurrent ψ (x - 1) i s ω - waveCurrent ψ x i s ω) ^ 2 =
      2 * density ψ ω s (x - 1) * density ψ ω s x +
        2 * density ψ ω s x * density ψ ω s (x + 1) := by
  rw [tsum_waveCurrent_sub_sq ψ (by omega : x - 1 ≠ x), sub_add_cancel]

/-! ### Algebra of `P(x) = u_x² + v_x²` -/

/-- The drift of `u_x² + v_x²` given by the product rule is `ΔP(x)`. -/
lemma localP_drift_eq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    (ψ s ω x).re * -(ψ s ω x).re + (ψ s ω x).re * -(ψ s ω x).re +
        ∑' i, waveDiffRe ψ x i s ω * waveDiffRe ψ x i s ω +
      ((ψ s ω x).im * -(ψ s ω x).im + (ψ s ω x).im * -(ψ s ω x).im +
        ∑' i, waveDiffIm ψ x i s ω * waveDiffIm ψ x i s ω) = lap (density ψ ω s) x := by
  simp only [← sq, tsum_waveDiffRe_sq, tsum_waveDiffIm_sq, lap, density]
  rw [Complex.sq_norm (ψ s ω x), Complex.normSq_apply]
  ring

/-- The diffusion of `u_x² + v_x²` given by the product rule is `c_{x-1} - c_x`. -/
lemma localP_diff_eq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    (ψ s ω x).re * waveDiffRe ψ x i s ω + (ψ s ω x).re * waveDiffRe ψ x i s ω +
      ((ψ s ω x).im * waveDiffIm ψ x i s ω + (ψ s ω x).im * waveDiffIm ψ x i s ω) =
        waveCurrent ψ (x - 1) i s ω - waveCurrent ψ x i s ω := by
  have h1 : x - 1 ≠ x := by omega
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_div_self', one_div]
  by_cases hi : i ∈ waveSites x
  · rcases mem_waveSites.1 hi with rfl | rfl | rfl | rfl <;>
      simp [waveDiffRe, waveDiffIm, waveCurrent, h1, h1.symm, div_eq_mul_inv, hinv,
        Complex.mul_im, Complex.mul_re] <;> ring
  · have h0 : i ≠ (x - 1, 0) := fun h => hi (mem_waveSites.2 (by tauto))
    have h1' : i ≠ (x - 1, 1) := fun h => hi (mem_waveSites.2 (by tauto))
    have h2 : i ≠ (x, 0) := fun h => hi (mem_waveSites.2 (by tauto))
    have h3 : i ≠ (x, 1) := fun h => hi (mem_waveSites.2 (by tauto))
    rw [waveDiffRe_of_notMem ψ hi, waveDiffIm_of_notMem ψ hi, waveCurrent_of_ne ψ h0 h1',
      waveCurrent_of_ne ψ h2 h3]
    ring

/-- Telescoping over the box `[-K, K]`: `∑_{|x| ≤ K} (f(x-1) - f(x)) = f(-K-1) - f(K)`. -/
lemma localP_sum_Icc_telescope {M : Type*} [AddCommGroup M] (f : ℤ → M) (K : ℕ) :
    ∑ x ∈ Finset.Icc (-(K : ℤ)) K, (f (x - 1) - f x) = f (-K - 1) - f K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
        {-(K : ℤ) - 1, (K : ℤ) + 1} ∪ Finset.Icc (-(K : ℤ)) K := by
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
      push_cast
      omega
    have hd : Disjoint ({-(K : ℤ) - 1, (K : ℤ) + 1} : Finset ℤ) (Finset.Icc (-(K : ℤ)) K) := by
      rw [Finset.disjoint_left]
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      simp only [Finset.mem_Icc]
      omega
    rw [e, Finset.sum_union hd, Finset.sum_pair (by omega), ih]
    have e1 : (K : ℤ) + 1 - 1 = K := by ring
    have e2 : -((K + 1 : ℕ) : ℤ) - 1 = -(K : ℤ) - 1 - 1 := by push_cast; ring
    rw [e1, e2]
    push_cast
    abel

/-- Summation by parts over the box: `∑_{|x| ≤ K} Δg(x) = g(K+1) - g(K) + (g(-K-1) - g(-K))`. -/
lemma localP_sum_Icc_lap (g : ℤ → ℝ) (K : ℕ) :
    ∑ x ∈ Finset.Icc (-(K : ℤ)) K, lap g x = g (K + 1) - g K + (g (-K - 1) - g (-K)) := by
  have e : ∀ x : ℤ, lap g x = -((g (x - 1 + 1) - g (x - 1)) - (g (x + 1) - g x)) := fun x => by
    rw [sub_add_cancel, lap]; ring
  simp only [e, Finset.sum_neg_distrib]
  rw [localP_sum_Icc_telescope (fun y => g (y + 1) - g y) K]
  have e3 : -(K : ℤ) - 1 + 1 = -K := by ring
  rw [e3]
  ring

/-! ### `P(x)` up to `τ_R ∧ N` -/

variable {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

omit [IsProbabilityMeasure μ] in
/-- `P(s,x) = |ψ'_s(x)|² ≤ (max R 1)²` for `0 ≤ s ≤ τ_R ∧ N`. -/
lemma IsGoodWave.density_le_of_le_waveStop (hg : IsGoodWave 𝓕 B ψ ψ' μ) {R : ℝ} {N : ℝ≥0}
    {ω : Ω} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ waveStop ψ' R N ω) (x : ℤ) :
    density ψ' ω s x ≤ max R 1 ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (hg.norm_apply_le_of_le_waveStop hs0 hs x) 2

/-- **The density as an Itô process up to `τ_R ∧ N`.** For every `x ∈ ℤ`,
`P(x) = |ψ'(x)|²` is an Itô process up to `τ = τ_R ∧ N` for `𝓕ᵃ`, with drift `ΔP(x)` and
diffusion coefficients `c_{x-1} - c_x` (`c_y = waveCurrent ψ' y`): before `τ`,
`dP(x) = ΔP(x) dt + dJ(x-1) - dJ(x)`. (Product rule for `u_x² + v_x²`.) -/
theorem IsGoodWave.isItoProcessUpTo_density (hB : IsBrownianFamily 𝓕 B μ)
    (hg : IsGoodWave 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (waveStop ψ' R N) (fun t ω => density ψ' ω t x)
      (fun s ω => lap (density ψ' ω s) x)
      (fun i s ω => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) := by
  set M := max R 1 with hMdef
  have hM : 1 ≤ M := le_max_right _ _
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hτ := hg.isStoppingTime_waveStop R N
  have hτb : ∃ T : ℝ≥0, ∀ ω, waveStop ψ' R N ω ≤ T := ⟨N, waveStop_le ψ' R N⟩
  have hb : ∀ ω (s : ℝ), 0 ≤ s → s ≤ waveStop ψ' R N ω → ∀ y, ‖ψ' s ω y‖ ≤ M :=
    fun ω s hs0 hs y => hg.norm_apply_le_of_le_waveStop hs0 hs y
  have hsq : ∀ ω (s : ℝ), 0 ≤ s → s ≤ waveStop ψ' R N ω →
      (‖ψ' s ω (x + 1)‖ ^ 2 + ‖ψ' s ω (x - 1)‖ ^ 2) / 2 ≤ M ^ 2 := by
    intro ω s hs0 hs
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hb ω s hs0 hs (x + 1)) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hb ω s hs0 hs (x - 1)) 2
    linarith
  have hbre : ∀ ω (s : ℝ), 0 ≤ s → s ≤ waveStop ψ' R N ω →
      |(ψ' s ω x).re| ≤ M ^ 2 ∧ |(ψ' s ω x).re| ≤ M ^ 2 ∧ |-(ψ' s ω x).re| ≤ M ^ 2 ∧
        |-(ψ' s ω x).re| ≤ M ^ 2 ∧ ∑' i, waveDiffRe ψ' x i s ω ^ 2 ≤ M ^ 2 ∧
          ∑' i, waveDiffRe ψ' x i s ω ^ 2 ≤ M ^ 2 := by
    intro ω s hs0 hs
    have h := ((Complex.abs_re_le_norm _).trans (hb ω s hs0 hs x)).trans hMM
    rw [abs_neg, tsum_waveDiffRe_sq]
    exact ⟨h, h, h, h, hsq ω s hs0 hs, hsq ω s hs0 hs⟩
  have hbim : ∀ ω (s : ℝ), 0 ≤ s → s ≤ waveStop ψ' R N ω →
      |(ψ' s ω x).im| ≤ M ^ 2 ∧ |(ψ' s ω x).im| ≤ M ^ 2 ∧ |-(ψ' s ω x).im| ≤ M ^ 2 ∧
        |-(ψ' s ω x).im| ≤ M ^ 2 ∧ ∑' i, waveDiffIm ψ' x i s ω ^ 2 ≤ M ^ 2 ∧
          ∑' i, waveDiffIm ψ' x i s ω ^ 2 ≤ M ^ 2 := by
    intro ω s hs0 hs
    have h := ((Complex.abs_im_le_norm _).trans (hb ω s hs0 hs x)).trans hMM
    rw [abs_neg, tsum_waveDiffIm_sq]
    exact ⟨h, h, h, h, hsq ω s hs0 hs, hsq ω s hs0 hs⟩
  have hre := hg.isItoProcessUpTo_re hB R N x
  have him := hg.isItoProcessUpTo_im hB R N x
  have huu := hre.mul hB.nullAug hτ hτb hre (fun ω => hg.continuous_re ω x)
    (fun ω => hg.continuous_re ω x) (fun t => hg.measurable_re t x)
    (fun t => hg.measurable_re t x) hbre
  have hvv := him.mul hB.nullAug hτ hτb him (fun ω => hg.continuous_im ω x)
    (fun ω => hg.continuous_im ω x) (fun t => hg.measurable_im t x)
    (fun t => hg.measurable_im t x) hbim
  have hP := huu.add hB.nullAug hvv
  convert hP using 1
  · funext t ω
    simp only [density, Complex.sq_norm, Complex.normSq_apply]
  · funext s ω
    exact (localP_drift_eq ψ' x s ω).symm
  · funext i s ω
    exact (localP_diff_eq ψ' x i s ω).symm

/-- **Mass in a box, up to `τ_R ∧ N`.** For every `K ∈ ℕ`, `∑_{|x| ≤ K} P(x)` is an Itô process
up to `τ = τ_R ∧ N`, with drift the boundary flux `P(K+1) - P(K) + (P(-K-1) - P(-K))` and
diffusion `c_{-K-1} - c_K`: `d ∑_{|x| ≤ K} P(x) = (flux) dt + dJ(-K-1) - dJ(K)`. -/
theorem IsGoodWave.isItoProcessUpTo_boxMass (hB : IsBrownianFamily 𝓕 B μ)
    (hg : IsGoodWave 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0) (K : ℕ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (waveStop ψ' R N)
      (fun t ω => ∑ x ∈ Finset.Icc (-(K : ℤ)) K, density ψ' ω t x)
      (fun s ω => density ψ' ω s (K + 1) - density ψ' ω s K +
        (density ψ' ω s (-K - 1) - density ψ' ω s (-K)))
      (fun i s ω => waveCurrent ψ' (-K - 1) i s ω - waveCurrent ψ' K i s ω) := by
  have h := IsItoProcessUpTo.finset_sum hB.nullAug (Finset.Icc (-(K : ℤ)) K)
    (fun x _ => hg.isItoProcessUpTo_density hB R N x)
  convert h using 1
  · funext s ω
    exact (localP_sum_Icc_lap (density ψ' ω s) K).symm
  · funext i s ω
    exact (localP_sum_Icc_telescope (fun y => waveCurrent ψ' y i s ω) K).symm

end QSSEPtoKPZ
