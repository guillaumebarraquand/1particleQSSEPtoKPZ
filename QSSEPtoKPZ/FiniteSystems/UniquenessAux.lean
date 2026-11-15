/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Frame
public import QSSEPtoKPZ.ItoIntegral.ProductRiemann
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Auxiliary lemmas for the uniqueness of the wave function (task L5)

`docs/stage5-design.md`, Section 1.2 (i), decision D8‴.

* Deterministic inequalities in `[0, ∞]`: `‖a + b‖ₑ² ≤ 2‖a‖ₑ² + 2‖b‖ₑ²`, the Cauchy–Schwarz
  inequality `(∫_{(0,t]} f)² ≤ t ∫_{(0,t]} f²`, `∑ₓ ∫ fₓ ≤ ∫ ∑ₓ fₓ`, and `∑ₓ |v(x)|² = ‖v‖²`
  on `ℓ²(ℤ)`.
* `waveUniq_comp_bound`: if `X`, `X'` are real Itô processes up to `N` with drifts `-c X`, `-c X'`
  (`|c| ≤ 1`) and the same initial value, then almost surely, for `t ≤ N`,
  `|X_t - X'_t|² ≤ 2 t ∫_0^t |X_s - X'_s|² ds + 2 |I_t(b 𝟙_{[0,N]} - b' 𝟙_{[0,N]})|²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-! ### Deterministic inequalities -/

/-- `‖a‖ₑ² = a²` for a real number `a` (as an element of `[0, ∞]`). -/
theorem waveUniq_enorm_sq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs]

/-- `‖a + b‖ₑ² ≤ 2 ‖a‖ₑ² + 2 ‖b‖ₑ²` for real numbers. -/
theorem waveUniq_enorm_sq_add_le (a b : ℝ) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [waveUniq_enorm_sq, waveUniq_enorm_sq, waveUniq_enorm_sq]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - b)])

/-- `|z|² = (Re z)² + (Im z)²` in `[0, ∞]`. -/
theorem waveUniq_enorm_sq_complex (z : ℂ) : ‖z‖ₑ ^ 2 = ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2 := by
  rw [waveUniq_enorm_sq, waveUniq_enorm_sq, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.sq_norm,
    Complex.normSq_apply]
  ring_nf

/-- `∑ₓ |v(x)|² = ‖v‖²` on `ℓ²(ℤ)`, in `[0, ∞]`. -/
theorem waveUniq_tsum_enorm_sq (v : ℓ²(ℤ, ℂ)) :
    ∑' x, ‖v x‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  have hs : Summable fun x => ‖v x‖ ^ 2 := by
    have h := (lp.memℓp v).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa [Real.rpow_two] using h
  rw [lp2_norm_eq_sqrt_tsum, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
  refine tsum_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- `∑ₓ ∫ fₓ ≤ ∫ ∑ₓ fₓ` (no measurability needed in this direction). -/
theorem waveUniq_tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] (ν : Measure α)
    (f : ι → α → ℝ≥0∞) : ∑' x, ∫⁻ a, f x a ∂ν ≤ ∫⁻ a, (∑' x, f x a) ∂ν := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hfin : ∑ x ∈ s, ∫⁻ a, f x a ∂ν ≤ ∫⁻ a, (∑ x ∈ s, f x a) ∂ν := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert y s hy ih =>
      rw [Finset.sum_insert hy]
      calc (∫⁻ a, f y a ∂ν) + ∑ x ∈ s, ∫⁻ a, f x a ∂ν
          ≤ (∫⁻ a, f y a ∂ν) + ∫⁻ a, (∑ x ∈ s, f x a) ∂ν := by gcongr
        _ ≤ ∫⁻ a, (f y a + ∑ x ∈ s, f x a) ∂ν := le_lintegral_add _ _
        _ = ∫⁻ a, (∑ x ∈ insert y s, f x a) ∂ν := by
          simp only [Finset.sum_insert hy]
  exact hfin.trans (lintegral_mono fun a => ENNReal.sum_le_tsum s)

/-- **Cauchy–Schwarz on `(0, t]`**: `(∫_{(0,t]} f)² ≤ t ∫_{(0,t]} f²`. -/
theorem waveUniq_sq_lintegral_le {f : ℝ → ℝ≥0∞} {t : ℝ}
    (hf : AEMeasurable f (volume.restrict (Set.Ioc 0 t))) :
    (∫⁻ s in Set.Ioc 0 t, f s) ^ 2 ≤ ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 t, f s ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc 0 t))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply,
    MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero, one_mul] at h
  set A := ∫⁻ s in Set.Ioc 0 t, f s ^ (2 : ℝ)
  have hA : A = ∫⁻ s in Set.Ioc 0 t, f s ^ 2 := by
    simp only [A]
    congr 1
    funext s
    exact ENNReal.rpow_two (f s)
  calc (∫⁻ s in Set.Ioc 0 t, f s) ^ 2
      ≤ (A ^ (1 / 2 : ℝ) * ENNReal.ofReal t ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = A * ENNReal.ofReal t := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
    _ = ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 t, f s ^ 2 := by rw [hA, mul_comm]

/-- `D_L(x,x) ≤ 2`. -/
theorem waveUniq_degree_le (L : ℕ∞) (x : ℤ) : degree L x ≤ 2 := by
  unfold degree
  have h1 : ∀ y, (box L).indicator (1 : ℤ → ℕ) y ≤ 1 := fun y => by
    by_cases hy : y ∈ box L <;> simp [hy]
  have := h1 (x + 1)
  have := h1 (x - 1)
  omega

/-! ### Difference of two Itô processes with linear drift -/

/-- A process `t ↦ f(t)` continuous on `[0, ∞)` is a.e.-measurable on `(0, t]`. -/
theorem waveUniq_aemeasurable_Ioc {f : ℝ → ℝ} (hf : Continuous fun t : ℝ≥0 => f t) (t : ℝ) :
    AEMeasurable f (volume.restrict (Set.Ioc 0 t)) := by
  have hc : Continuous fun s : ℝ => f (s.toNNReal : ℝ) := hf.comp continuous_real_toNNReal
  refine hc.measurable.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.coe_toNNReal s hs.1.le]

/-- **Difference of two Itô processes with drifts `-c X`, `-c X'`** (`|c| ≤ 1`), the same initial
value and continuous paths: almost surely, for `t ≤ N`,
`|X_t - X'_t|² ≤ 2 (t ∫_0^t |X_s - X'_s|² ds) + 2 |I_t(b 𝟙_{[0,N]} - b' 𝟙_{[0,N]})|²`
(the drift by Cauchy–Schwarz). -/
theorem waveUniq_comp_bound {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Countable ι]
    {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}
    (hB : IsBrownianFamily 𝓖 B μ) {N : ℝ≥0} {X X' : ℝ → Ω → ℝ} {c : ℝ} (hc : |c| ≤ 1)
    {b b' : ι → ℝ → Ω → ℝ}
    (hX : IsItoProcessUpTo 𝓖 μ B (fun _ => N) X (fun s ω => -c * X s ω) b)
    (hX' : IsItoProcessUpTo 𝓖 μ B (fun _ => N) X' (fun s ω => -c * X' s ω) b')
    (h0 : ∀ ω, X 0 ω = X' 0 ω) (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω)
    (hXc' : ∀ ω, Continuous fun t : ℝ≥0 => X' t ω) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ N → ‖X t ω - X' t ω‖ₑ ^ 2 ≤
      2 * (ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ), ‖X s ω - X' s ω‖ₑ ^ 2) +
        2 * ‖stochInt 𝓖 μ B (fun i s ω => (if s ≤ N then b i s ω else 0) -
          (if s ≤ N then b' i s ω else 0)) t ω‖ₑ ^ 2 := by
  filter_upwards [hX.eq, hX'.eq, hX.drift, hX'.drift,
    itoProd_stochInt_sub hB hX.integrable hX'.integrable] with ω e1 e2 d1 d2 e3 t ht
  have hmin : min t N = t := min_eq_left ht
  have E1 := e1 t
  have E2 := e2 t
  simp only [hmin] at E1 E2
  have htN : ((t : ℝ)) ≤ N := by exact_mod_cast ht
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 (N : ℝ) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨NNReal.coe_nonneg t, htN⟩))
  have hi1 : IntervalIntegrable (fun s => -c * X s ω) volume 0 t := d1.mono_set hsub
  have hi2 : IntervalIntegrable (fun s => -c * X' s ω) volume 0 t := d2.mono_set hsub
  have key : X t ω - X' t ω = (∫ s in (0 : ℝ)..t, (-c * X s ω - -c * X' s ω)) +
      stochInt 𝓖 μ B (fun i s ω => (if s ≤ N then b i s ω else 0) -
        (if s ≤ N then b' i s ω else 0)) t ω := by
    rw [E1, E2, h0 ω, intervalIntegral.integral_sub hi1 hi2, e3 t]
    ring
  rw [key]
  refine (waveUniq_enorm_sq_add_le _ _).trans ?_
  gcongr
  have hm : AEMeasurable (fun s => ‖X s ω - X' s ω‖ₑ) (volume.restrict (Set.Ioc 0 (t : ℝ))) :=
    (waveUniq_aemeasurable_Ioc (f := fun s => X s ω - X' s ω) ((hXc ω).sub (hXc' ω)) t).enorm
  calc ‖∫ s in (0 : ℝ)..t, (-c * X s ω - -c * X' s ω)‖ₑ ^ 2
      ≤ (∫⁻ s in Set.Ioc 0 (t : ℝ), ‖X s ω - X' s ω‖ₑ) ^ 2 := by
        gcongr
        rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
        refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun s => ?_)
        rw [show -c * X s ω - -c * X' s ω = (-c) * (X s ω - X' s ω) by ring, enorm_mul]
        have : ‖-c‖ₑ ≤ 1 := by
          rw [enorm_neg, Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_one.2 hc
        calc ‖-c‖ₑ * ‖X s ω - X' s ω‖ₑ ≤ 1 * ‖X s ω - X' s ω‖ₑ := by gcongr
          _ = _ := one_mul _
    _ ≤ ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ), ‖X s ω - X' s ω‖ₑ ^ 2 :=
        waveUniq_sq_lintegral_le hm

/-! ### The Gronwall inequality for two Itô solutions of the wave equation -/

section Gronwall

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {φ φ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `F(s) = 𝔼 ‖φ_s - φ'_s‖² = 𝔼 ∑ₓ |φ_s(x) - φ'_s(x)|²`, in `[0, ∞]`. -/
def waveUniqF (μ : Measure Ω) (φ φ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∑' x, ‖φ s ω x - φ' s ω x‖ₑ ^ 2) ∂μ

/-- `∑ᵢ (waveDiffRe ψ x)ᵢ² + ∑ᵢ (waveDiffIm ψ x)ᵢ² = |ψ(x+1)|² + |ψ(x-1)|²`, in `[0, ∞]`. -/
theorem waveUniq_tsum_enorm_waveDiff (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    (∑' i, ‖waveDiffRe ψ x i s ω‖ₑ ^ 2) + ∑' i, ‖waveDiffIm ψ x i s ω‖ₑ ^ 2 =
      ‖ψ s ω (x + 1)‖ₑ ^ 2 + ‖ψ s ω (x - 1)‖ₑ ^ 2 := by
  have hre : Summable fun i => waveDiffRe ψ x i s ω ^ 2 :=
    summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffRe_of_notMem ψ hi]; norm_num
  have him : Summable fun i => waveDiffIm ψ x i s ω ^ 2 :=
    summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffIm_of_notMem ψ hi]; norm_num
  simp only [waveUniq_enorm_sq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hre,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) him, tsum_waveDiffRe_sq,
    tsum_waveDiffIm_sq, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The energy integrand of the difference of the cut-off coefficients of two solutions, at
`s ≤ N`: `|φ_s(x+1) - φ'_s(x+1)|² + |φ_s(x-1) - φ'_s(x-1)|²`. -/
theorem waveUniq_energy_integrand (φ φ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) {N s : ℝ} (hs : s ≤ N)
    (ω : Ω) :
    (∑' i, ‖(if s ≤ N then waveDiffRe φ x i s ω else 0) -
        (if s ≤ N then waveDiffRe φ' x i s ω else 0)‖ₑ ^ 2) +
      ∑' i, ‖(if s ≤ N then waveDiffIm φ x i s ω else 0) -
        (if s ≤ N then waveDiffIm φ' x i s ω else 0)‖ₑ ^ 2 =
      ‖φ s ω (x + 1) - φ' s ω (x + 1)‖ₑ ^ 2 + ‖φ s ω (x - 1) - φ' s ω (x - 1)‖ₑ ^ 2 := by
  simp only [hs, ↓reduceIte, ← waveDiffRe_sub, ← waveDiffIm_sub]
  rw [waveUniq_tsum_enorm_waveDiff]
  simp only [lp.coeFn_sub, Pi.sub_apply]

/-- Joint measurability of `(s, ω) ↦ ∑ₓ |φ_{s⁺}(x) - φ'_{s⁺}(x)|²` (`s⁺ = max s 0`), from the
continuity of the paths and the adaptedness. -/
theorem waveUniq_measurable (hφ : IsWaveIto L 𝓖 B ψ0 φ μ) (hφ' : IsWaveIto L 𝓖 B ψ0 φ' μ) :
    Measurable fun p : ℝ × Ω =>
      ∑' x, ‖φ (p.1.toNNReal : ℝ) p.2 x - φ' (p.1.toNNReal : ℝ) p.2 x‖ₑ ^ 2 := by
  refine Measurable.tsum fun x => ?_
  have h : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) =>
      φ (s.toNNReal : ℝ) ω x - φ' (s.toNNReal : ℝ) ω x) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun s => ?_)
    · have h1 : Continuous fun t : ℝ≥0 => φ t ω x :=
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hφ.continuous ω)
      have h2 : Continuous fun t : ℝ≥0 => φ' t ω x :=
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hφ'.continuous ω)
      exact (h1.sub h2).comp continuous_real_toNNReal
    · exact ((hφ.adapted _ x).sub (hφ'.adapted _ x)).mono (𝓖.le _) le_rfl
  exact h.enorm.pow_const 2

/-- Tonelli for `F`: `𝔼 ∫_{(0,t]} ‖φ_s - φ'_s‖² ds = ∫_{(0,t]} F(s) ds`. -/
theorem waveUniq_swap [SFinite μ] (hφ : IsWaveIto L 𝓖 B ψ0 φ μ)
    (hφ' : IsWaveIto L 𝓖 B ψ0 φ' μ) (t : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Ioc 0 t, ∑' x, ‖φ s ω x - φ' s ω x‖ₑ ^ 2) ∂μ =
      ∫⁻ s in Set.Ioc 0 t, waveUniqF μ φ φ' s := by
  have e1 : ∀ ω, (∫⁻ s in Set.Ioc 0 t, ∑' x, ‖φ s ω x - φ' s ω x‖ₑ ^ 2) =
      ∫⁻ s in Set.Ioc 0 t, ∑' x, ‖φ (s.toNNReal : ℝ) ω x - φ' (s.toNNReal : ℝ) ω x‖ₑ ^ 2 :=
    fun ω => setLIntegral_congr_fun measurableSet_Ioc fun s hs => by
      simp only [Real.coe_toNNReal s hs.1.le]
  have e2 : (∫⁻ s in Set.Ioc 0 t, waveUniqF μ φ φ' s) =
      ∫⁻ s in Set.Ioc 0 t, ∫⁻ ω,
        (∑' x, ‖φ (s.toNNReal : ℝ) ω x - φ' (s.toNNReal : ℝ) ω x‖ₑ ^ 2) ∂μ :=
    setLIntegral_congr_fun measurableSet_Ioc fun s hs => by
      simp only [waveUniqF, Real.coe_toNNReal s hs.1.le]
  simp only [e1, e2]
  exact lintegral_lintegral_swap
    (((waveUniq_measurable hφ hφ').comp measurable_swap).aemeasurable)

/-- **The Gronwall inequality** (`docs/stage5-design.md`, 1.2 (i)): for two Itô solutions of the
wave equation on `Λ_L` with the same initial value, and `t ≤ N`,
`F(t) ≤ (4 + 2N) ∫_0^t F(s) ds`, where `F(s) = 𝔼 ‖φ_s - φ'_s‖²` (Itô's isometry for the noise,
Cauchy–Schwarz for the drift, and `∑ₓ (|δ(x+1)|² + |δ(x-1)|²) = 2 ‖δ‖²`). -/
theorem waveUniq_gronwall [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓖 B μ)
    (hφ : IsWaveIto L 𝓖 B ψ0 φ μ) (hφ' : IsWaveIto L 𝓖 B ψ0 φ' μ) {N t : ℝ≥0} (ht : t ≤ N) :
    waveUniqF μ φ φ' t ≤
      ENNReal.ofReal (4 + 2 * N) * ∫⁻ s in Set.Ioc 0 (t : ℝ), waveUniqF μ φ φ' s := by
  classical
  set Ire : ℤ → Ω → ℝ := fun x ω => stochInt 𝓖 μ B
    (fun i s ω => (if s ≤ N then waveDiffRe φ x i s ω else 0) -
      (if s ≤ N then waveDiffRe φ' x i s ω else 0)) t ω with hIre
  set Iim : ℤ → Ω → ℝ := fun x ω => stochInt 𝓖 μ B
    (fun i s ω => (if s ≤ N then waveDiffIm φ x i s ω else 0) -
      (if s ≤ N then waveDiffIm φ' x i s ω else 0)) t ω with hIim
  set J : ℤ → Ω → ℝ≥0∞ := fun x ω =>
    if x ∈ box L then ‖Ire x ω‖ₑ ^ 2 + ‖Iim x ω‖ₑ ^ 2 else 0 with hJ
  set e : ℝ → Ω → ℤ → ℝ≥0∞ := fun s ω x => ‖φ s ω x - φ' s ω x‖ₑ ^ 2 with he
  set I := ∫⁻ s in Set.Ioc 0 (t : ℝ), waveUniqF μ φ φ' s with hI
  have htN : (t : ℝ) ≤ N := by exact_mod_cast ht
  -- Step A: the pointwise bound, coordinate by coordinate
  have hA : ∀ᵐ ω ∂μ, ∀ x, e t ω x ≤
      2 * (ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ), e s ω x) + 2 * J x ω := by
    rw [ae_all_iff]
    intro x
    by_cases hx : x ∈ box L
    · have hdeg : |((degree L x : ℝ) / 2)| ≤ 1 := by
        have := waveUniq_degree_le L x
        rw [abs_of_nonneg (by positivity)]
        have h2 : (degree L x : ℝ) ≤ 2 := by exact_mod_cast this
        linarith
      have c1 : ∀ ω, Continuous fun t : ℝ≥0 => φ t ω x := fun ω =>
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hφ.continuous ω)
      have c2 : ∀ ω, Continuous fun t : ℝ≥0 => φ' t ω x := fun ω =>
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hφ'.continuous ω)
      have hre := waveUniq_comp_bound hB hdeg (hφ.re x hx N) (hφ'.re x hx N)
        (fun ω => by simp only [hφ.init, hφ'.init])
        (fun ω => Complex.continuous_re.comp (c1 ω)) (fun ω => Complex.continuous_re.comp (c2 ω))
      have him := waveUniq_comp_bound hB hdeg (hφ.im x hx N) (hφ'.im x hx N)
        (fun ω => by simp only [hφ.init, hφ'.init])
        (fun ω => Complex.continuous_im.comp (c1 ω)) (fun ω => Complex.continuous_im.comp (c2 ω))
      filter_upwards [hre, him] with ω h1 h2
      have h1 := h1 t ht
      have h2 := h2 t ht
      have hsplit : ∀ s, e s ω x = ‖(φ s ω x).re - (φ' s ω x).re‖ₑ ^ 2 +
          ‖(φ s ω x).im - (φ' s ω x).im‖ₑ ^ 2 := fun s => by
        simp only [he, waveUniq_enorm_sq_complex, Complex.sub_re, Complex.sub_im]
      simp only [hJ, hx, ↓reduceIte]
      rw [hsplit]
      calc ‖(φ t ω x).re - (φ' t ω x).re‖ₑ ^ 2 + ‖(φ t ω x).im - (φ' t ω x).im‖ₑ ^ 2
          ≤ (2 * (ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ),
                ‖(φ s ω x).re - (φ' s ω x).re‖ₑ ^ 2) + 2 * ‖Ire x ω‖ₑ ^ 2) +
              (2 * (ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ),
                ‖(φ s ω x).im - (φ' s ω x).im‖ₑ ^ 2) + 2 * ‖Iim x ω‖ₑ ^ 2) :=
            add_le_add h1 h2
        _ = 2 * (ENNReal.ofReal t * ((∫⁻ s in Set.Ioc 0 (t : ℝ),
                ‖(φ s ω x).re - (φ' s ω x).re‖ₑ ^ 2) + ∫⁻ s in Set.Ioc 0 (t : ℝ),
                ‖(φ s ω x).im - (φ' s ω x).im‖ₑ ^ 2)) +
              2 * (‖Ire x ω‖ₑ ^ 2 + ‖Iim x ω‖ₑ ^ 2) := by ring
        _ ≤ 2 * (ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ), e s ω x) +
              2 * (‖Ire x ω‖ₑ ^ 2 + ‖Iim x ω‖ₑ ^ 2) := by
            gcongr
            simp only [hsplit]
            exact le_lintegral_add _ _
    · filter_upwards with ω
      simp [he, hφ.support ω t x hx, hφ'.support ω t x hx]
  -- measurability of the noise terms
  have hIrem : ∀ x, Measurable (Ire x) := fun x => (stochInt_adapted hB _ t).mono (𝓖.le t) le_rfl
  have hIimm : ∀ x, Measurable (Iim x) := fun x => (stochInt_adapted hB _ t).mono (𝓖.le t) le_rfl
  have hJm : ∀ x, Measurable (J x) := by
    intro x
    by_cases hx : x ∈ box L
    · simp only [hJ, hx, ↓reduceIte]
      exact ((hIrem x).enorm.pow_const 2).add ((hIimm x).enorm.pow_const 2)
    · simp only [hJ, hx, ↓reduceIte]
      exact measurable_const
  -- Step B: sum over `x`
  have hB1 : waveUniqF μ φ φ' t ≤ ∫⁻ ω, ((2 * ENNReal.ofReal t *
      (∫⁻ s in Set.Ioc 0 (t : ℝ), ∑' x, e s ω x)) + 2 * (∑' x, J x ω)) ∂μ := by
    unfold waveUniqF
    refine lintegral_mono_ae ?_
    filter_upwards [hA] with ω hω
    calc (∑' x, e t ω x)
        ≤ ∑' x, (2 * (ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 (t : ℝ), e s ω x) + 2 * J x ω) :=
          ENNReal.tsum_le_tsum hω
      _ = 2 * ENNReal.ofReal t * (∑' x, ∫⁻ s in Set.Ioc 0 (t : ℝ), e s ω x) +
            2 * (∑' x, J x ω) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left]
          ring
      _ ≤ _ := by
          gcongr
          exact waveUniq_tsum_lintegral_le _ _
  -- Step C: Tonelli
  have hC : ∫⁻ ω, ((2 * ENNReal.ofReal t *
      (∫⁻ s in Set.Ioc 0 (t : ℝ), ∑' x, e s ω x)) + 2 * (∑' x, J x ω)) ∂μ =
      2 * ENNReal.ofReal t * I + 2 * (∑' x, ∫⁻ ω, J x ω ∂μ) := by
    rw [lintegral_add_right _ ((Measurable.tsum hJm).const_mul 2),
      lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by norm_num),
      lintegral_tsum fun x => (hJm x).aemeasurable, hI, ← waveUniq_swap hφ hφ']
  -- Step D: Itô's isometry, coordinate by coordinate
  have hD : ∀ x, ∫⁻ ω, J x ω ∂μ ≤
      ∫⁻ ω, (∫⁻ s in Set.Ioc 0 (t : ℝ), (e s ω (x + 1) + e s ω (x - 1))) ∂μ := by
    intro x
    by_cases hx : x ∈ box L
    · have hre := itoProd_isItoIntegrable_sub (hφ.re x hx N).integrable
        (hφ'.re x hx N).integrable
      have him := itoProd_isItoIntegrable_sub (hφ.im x hx N).integrable
        (hφ'.im x hx N).integrable
      simp only [hJ, hx, ↓reduceIte]
      rw [lintegral_add_left ((hIrem x).enorm.pow_const 2)]
      have e1 : ∫⁻ ω, ‖Ire x ω‖ₑ ^ 2 ∂μ = energy μ (fun i s ω =>
          (if s ≤ N then waveDiffRe φ x i s ω else 0) -
            (if s ≤ N then waveDiffRe φ' x i s ω else 0)) t := by
        rw [← lintegral_stochInt_sq hB hre]
        simp only [hIre, waveUniq_enorm_sq]
      have e2 : ∫⁻ ω, ‖Iim x ω‖ₑ ^ 2 ∂μ = energy μ (fun i s ω =>
          (if s ≤ N then waveDiffIm φ x i s ω else 0) -
            (if s ≤ N then waveDiffIm φ' x i s ω else 0)) t := by
        rw [← lintegral_stochInt_sq hB him]
        simp only [hIim, waveUniq_enorm_sq]
      rw [e1, e2]
      simp only [energy, pathEnergy]
      refine (le_lintegral_add _ _).trans (lintegral_mono fun ω => ?_)
      refine (le_lintegral_add _ _).trans
        (le_of_eq (setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_))
      exact waveUniq_energy_integrand φ φ' x (hs.2.trans htN) ω
    · simp [hJ, hx]
  -- Step E: `∑ₓ (|δ(x+1)|² + |δ(x-1)|²) = 2 ‖δ‖²`
  have hE : (∑' x, ∫⁻ ω, J x ω ∂μ) ≤ 2 * I := by
    have hshift : ∀ s ω, (∑' x, (e s ω (x + 1) + e s ω (x - 1))) = 2 * ∑' x, e s ω x := by
      intro s ω
      have a1 := (Equiv.addRight (1 : ℤ)).tsum_eq (e s ω)
      have a2 := (Equiv.subRight (1 : ℤ)).tsum_eq (e s ω)
      simp only [Equiv.coe_addRight, Equiv.subRight_apply] at a1 a2
      rw [ENNReal.tsum_add, a1, a2]
      ring
    have hc : ∀ ω, (∫⁻ s in Set.Ioc 0 (t : ℝ), 2 * ∑' x, e s ω x) =
        2 * ∫⁻ s in Set.Ioc 0 (t : ℝ), ∑' x, e s ω x := fun ω =>
      lintegral_const_mul' _ _ (by norm_num)
    calc (∑' x, ∫⁻ ω, J x ω ∂μ)
        ≤ ∑' x, ∫⁻ ω, (∫⁻ s in Set.Ioc 0 (t : ℝ), (e s ω (x + 1) + e s ω (x - 1))) ∂μ :=
          ENNReal.tsum_le_tsum hD
      _ ≤ ∫⁻ ω, (∑' x, ∫⁻ s in Set.Ioc 0 (t : ℝ), (e s ω (x + 1) + e s ω (x - 1))) ∂μ :=
          waveUniq_tsum_lintegral_le _ _
      _ ≤ ∫⁻ ω, (∫⁻ s in Set.Ioc 0 (t : ℝ), ∑' x, (e s ω (x + 1) + e s ω (x - 1))) ∂μ :=
          lintegral_mono fun ω => waveUniq_tsum_lintegral_le _ _
      _ = 2 * I := by
          simp only [hshift, hc]
          rw [lintegral_const_mul' _ _ (by norm_num), hI, ← waveUniq_swap hφ hφ']
  -- conclusion
  have hcoef : 2 * ENNReal.ofReal t + 4 ≤ ENNReal.ofReal (4 + 2 * N) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num),
      add_comm]
    simp only [ENNReal.ofReal_ofNat]
    gcongr
  calc waveUniqF μ φ φ' t ≤ _ := hB1
    _ = 2 * ENNReal.ofReal t * I + 2 * (∑' x, ∫⁻ ω, J x ω ∂μ) := hC
    _ ≤ 2 * ENNReal.ofReal t * I + 2 * (2 * I) := by gcongr
    _ = (2 * ENNReal.ofReal t + 4) * I := by ring
    _ ≤ ENNReal.ofReal (4 + 2 * N) * I := by gcongr

end Gronwall

end QSSEPtoKPZ
