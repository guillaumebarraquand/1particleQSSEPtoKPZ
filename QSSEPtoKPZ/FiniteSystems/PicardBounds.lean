/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.WaveIto
public import QSSEPtoKPZ.FiniteSystems.PicardAux
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pointwise bounds for the Picard iteration (task L2a)

Auxiliary results for `FiniteSystems/PicardIter.lean`, for `ℓ²(ℤ)`-valued processes `ψ`:

* sums of squares of the coefficients: `∑ᵢ (waveDiffRe ψ x)ᵢ² = (|ψ(x+1)|² + |ψ(x-1)|²)/2`, hence
  `energy (waveDiffRe ψ x) T ≤ 𝔼 ∫_0^T ‖ψ_u‖² du` (`picardBd_energy_re_le`, `…_im_le`);
* continuity of the coordinates and of the drift `t ↦ ∫_0^t ψ_s(x) ds`;
* joint measurability of `(u, ω) ↦ ‖ψ_u(ω)‖²`, measurability of `ω ↦ ∫_0^T ‖ψ_u(ω)‖² du`, and
  Tonelli: `𝔼 ∫_0^t ‖ψ_u‖² du ≤ ∫_0^t 𝔼 sup_{v ≤ u} ‖ψ_v‖² du` (`picardBd_swap_le`);
* `|z + (a + i b) - (D/2) w|² ≤ 3|z|² + 3(a² + b²) + 3|w|²` and the variant without `z`
  (`D = D_L(x,x) ≤ 2`);
* continuity in `ℓ²` of a path whose coordinates are continuous and dominated by a summable
  sequence on bounded intervals (dominated convergence for series, `picardBd_continuous_lp`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### coefficients and energies -/

/-- `‖r‖ₑ² = (r²)⁺` for a real `r`. -/
theorem picardBd_enorm_sq (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- `∑ᵢ |(waveDiffRe ψ x)ᵢ|² = (|ψ(x+1)|² + |ψ(x-1)|²)/2`, in `[0, ∞]`. -/
theorem picardBd_tsum_enorm_re (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, ‖waveDiffRe ψ x i s ω‖ₑ ^ 2 =
      ENNReal.ofReal ((‖ψ s ω (x + 1)‖ ^ 2 + ‖ψ s ω (x - 1)‖ ^ 2) / 2) := by
  simp_rw [picardBd_enorm_sq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    (summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffRe_of_notMem ψ hi]; norm_num), tsum_waveDiffRe_sq]

/-- `∑ᵢ |(waveDiffIm ψ x)ᵢ|² = (|ψ(x+1)|² + |ψ(x-1)|²)/2`, in `[0, ∞]`. -/
theorem picardBd_tsum_enorm_im (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, ‖waveDiffIm ψ x i s ω‖ₑ ^ 2 =
      ENNReal.ofReal ((‖ψ s ω (x + 1)‖ ^ 2 + ‖ψ s ω (x - 1)‖ ^ 2) / 2) := by
  simp_rw [picardBd_enorm_sq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    (summable_of_ne_finset_zero (s := waveSites x) fun i hi => by
      rw [waveDiffIm_of_notMem ψ hi]; norm_num), tsum_waveDiffIm_sq]

/-- `(|v(x+1)|² + |v(x-1)|²)/2 ≤ ‖v‖²`. -/
theorem picardBd_half_le (v : ℓ²(ℤ, ℂ)) (x : ℤ) :
    (‖v (x + 1)‖ ^ 2 + ‖v (x - 1)‖ ^ 2) / 2 ≤ ‖v‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm two_ne_zero v (x + 1)) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm two_ne_zero v (x - 1)) 2
  linarith

/-- `energy (waveDiffRe ψ x) T ≤ 𝔼 ∫_0^T ‖ψ_u‖² du`. -/
theorem picardBd_energy_re_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (T : ℝ) :
    energy μ (waveDiffRe ψ x) T ≤
      ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ := by
  unfold energy pathEnergy
  refine lintegral_mono fun ω => lintegral_mono fun u => ?_
  rw [picardBd_tsum_enorm_re]
  exact ENNReal.ofReal_le_ofReal (picardBd_half_le _ x)

/-- `energy (waveDiffIm ψ x) T ≤ 𝔼 ∫_0^T ‖ψ_u‖² du`. -/
theorem picardBd_energy_im_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (T : ℝ) :
    energy μ (waveDiffIm ψ x) T ≤
      ∫⁻ ω, (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ := by
  unfold energy pathEnergy
  refine lintegral_mono fun ω => lintegral_mono fun u => ?_
  rw [picardBd_tsum_enorm_im]
  exact ENNReal.ofReal_le_ofReal (picardBd_half_le _ x)

/-- `∫_0^T ‖ψ_u‖² du ≤ T sup_{[0,T]} ‖ψ‖²`. -/
theorem picardBd_setLIntegral_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (T : ℝ) :
    ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2) ≤
      ENNReal.ofReal T * ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖ψ t ω‖ ^ 2) := by
  calc ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2)
      ≤ ∫⁻ u in Set.Ioc 0 T, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖ψ t ω‖ ^ 2) :=
        setLIntegral_mono measurable_const fun u hu =>
          le_iSup₂_of_le (f := fun t _ => ENNReal.ofReal (‖ψ t ω‖ ^ 2)) u ⟨hu.1.le, hu.2⟩ le_rfl
    _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]

/-- The coordinates of a process with continuous `ℓ²` paths are continuous. -/
theorem picardBd_continuous_coord {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => ψ t ω) (x : ℤ) : Continuous fun t : ℝ≥0 => ψ t ω x :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp hc

/-- `s ↦ ψ_s(ω)(x)` is continuous on `[0, ∞)` (as a function of a real time). -/
theorem picardBd_continuousOn {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => ψ t ω) (x : ℤ) :
    ContinuousOn (fun s => ψ s ω x) (Set.Ici 0) := by
  have h : Continuous fun r : ℝ => ψ (r.toNNReal : ℝ) ω x :=
    (picardBd_continuous_coord hc x).comp continuous_real_toNNReal
  exact h.continuousOn.congr fun s hs => by
    simp only [Real.coe_toNNReal _ (Set.mem_Ici.1 hs)]

/-- The drift `t ↦ ∫_0^t ψ_s(ω)(x) ds` is continuous on `[0, ∞)`. -/
theorem picardBd_continuous_drift {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => ψ t ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, ψ s ω x := by
  have h : Continuous fun r : ℝ => ψ (r.toNNReal : ℝ) ω x :=
    (picardBd_continuous_coord hc x).comp continuous_real_toNNReal
  have hF := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => h.intervalIntegrable a b) 0
  refine (hF.comp NNReal.continuous_coe).congr fun t => ?_
  simp only [Function.comp]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le t.coe_nonneg] at hs
  simp only [Real.coe_toNNReal _ hs.1]

/-- The coordinates of an adapted process with continuous paths are interval integrable. -/
theorem picardBd_intervalIntegrable {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => ψ t ω) (x : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => ψ s ω x) volume 0 t :=
  ((picardBd_continuousOn hc x).mono (by
    rw [Set.uIcc_of_le ht]; exact Set.Icc_subset_Ici_self)).intervalIntegrable

/-- `∑ₓ ∫_0^T |ψ_u(x)|² du ≤ ∫_0^T ‖ψ_u‖² du`. -/
theorem picardBd_tsum_J_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (T : ℝ) :
    ∑' x, ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω x‖ ^ 2) ≤
      ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2) :=
  (picardAux_tsum_lintegral_le _).trans_eq (by simp_rw [← picardAux_ofReal_norm_sq])

/-! ### measurability in `(t, ω)` -/

/-- `(u, ω) ↦ ‖ψ_{u⁺}(ω)‖²` is measurable. -/
theorem picardBd_measurable_F {𝓖 : Filtration ℝ≥0 mΩ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) :
    Measurable fun p : ℝ × Ω => ENNReal.ofReal (‖ψ (p.1.toNNReal : ℝ) p.2‖ ^ 2) := by
  have hX := picardAux_measurable_uncurry (X := fun u ω => ‖ψ u ω‖)
    (fun t => (measurable_norm_of_adapted hadapt t).mono (𝓖.le t) le_rfl)
    (fun ω => (hc ω).norm)
  exact ENNReal.measurable_ofReal.comp (hX.pow_const 2)

/-- `ω ↦ ∫_0^T ‖ψ_u(ω)‖² du` is measurable. -/
theorem picardBd_measurable_J {𝓖 : Filtration ℝ≥0 mΩ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) (T : ℝ) :
    Measurable fun ω => ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (‖ψ u ω‖ ^ 2) := by
  have hF := (picardBd_measurable_F hadapt hc).lintegral_prod_left'
    (μ := volume.restrict (Set.Ioc 0 T))
  convert hF using 1
  funext ω
  refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp only [Real.coe_toNNReal _ hu.1.le]

/-- **Tonelli**: `𝔼 ∫_0^t ‖ψ_u‖² du ≤ ∫_0^t 𝔼 sup_{v ≤ u} ‖ψ_v‖² du`. -/
theorem picardBd_swap_le [SFinite μ] {𝓖 : Filtration ℝ≥0 mΩ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) (t : ℝ) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ ≤
      ∫⁻ s in Set.Icc (0 : ℝ) t,
        ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ) s, ENNReal.ofReal (‖ψ u ω‖ ^ 2)) ∂μ := by
  have hF := picardBd_measurable_F hadapt hc
  set F : ℝ × Ω → ℝ≥0∞ := fun p => ENNReal.ofReal (‖ψ (p.1.toNNReal : ℝ) p.2‖ ^ 2) with hFdef
  have e : ∀ ω, ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖ψ u ω‖ ^ 2) =
      ∫⁻ u in Set.Ioc 0 t, F (u, ω) := fun ω =>
    setLIntegral_congr_fun measurableSet_Ioc fun u hu => by
      simp only [hFdef, Real.coe_toNNReal _ hu.1.le]
  simp_rw [e]
  rw [lintegral_lintegral_swap (f := fun ω u => F (u, ω))
    (hF.comp measurable_swap).aemeasurable]
  refine (lintegral_mono_ae ?_).trans (lintegral_mono_set Set.Ioc_subset_Icc_self)
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu => ?_)
  refine lintegral_mono fun ω => ?_
  simp only [hFdef, Real.coe_toNNReal _ hu.1.le]
  exact le_iSup₂_of_le (f := fun v _ => ENNReal.ofReal (‖ψ v ω‖ ^ 2)) u ⟨hu.1.le, le_rfl⟩ le_rfl

/-! ### pointwise bounds -/

/-- Monotonicity of multiplication by a constant in `[0, ∞]`. -/
theorem picardBd_mul_le {a b : ℝ≥0∞} (h : a ≤ b) (c : ℝ≥0∞) : c * a ≤ c * b :=
  mul_le_mul' le_rfl h

/-- `D_L(x,x) ≤ 2`. -/
theorem picardBd_degree_le (L : ℕ∞) (x : ℤ) : degree L x ≤ 2 := by
  unfold degree Set.indicator
  split_ifs <;> simp

/-- `|D_L(x,x)/2 · w| ≤ |w|`. -/
theorem picardBd_norm_drift_le (L : ℕ∞) (x : ℤ) (w : ℂ) :
    ‖(degree L x : ℂ) / 2 * w‖ ≤ ‖w‖ := by
  have hd : ‖(degree L x : ℂ) / 2‖ ≤ 1 := by
    have := picardBd_degree_le L x
    rw [norm_div, Complex.norm_natCast, Complex.norm_two, div_le_one (by norm_num)]
    exact_mod_cast this
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans_eq (one_mul _)

/-- `|a + i b|² = a² + b²`. -/
theorem picardBd_norm_mart (a b : ℝ) :
    ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `|z + (a + i b) - (D/2) w|² ≤ 3|z|² + 3(a² + b²) + 3|w|²`. -/
theorem picardBd_coord_le3 (z w : ℂ) (a b : ℝ) (L : ℕ∞) (x : ℤ) :
    ENNReal.ofReal (‖z + ((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w‖ ^ 2) ≤
      3 * ENNReal.ofReal (‖z‖ ^ 2) + 3 * (ENNReal.ofReal (a ^ 2) + ENNReal.ofReal (b ^ 2)) +
        3 * ENNReal.ofReal (‖w‖ ^ 2) := by
  have h1 := norm_sub_le (z + ((a : ℂ) + Complex.I * (b : ℂ))) ((degree L x : ℂ) / 2 * w)
  have h2 := norm_add_le z ((a : ℂ) + Complex.I * (b : ℂ))
  have h3 := picardBd_norm_drift_le L x w
  have h4 := picardBd_norm_mart a b
  have hq := norm_nonneg ((a : ℂ) + Complex.I * (b : ℂ))
  have hN := norm_nonneg (z + ((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w)
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have key : ‖z + ((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w‖ ^ 2 ≤
      3 * ‖z‖ ^ 2 + 3 * (a ^ 2 + b ^ 2) + 3 * ‖w‖ ^ 2 := by
    rw [← h4]
    have hs : ‖z + ((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w‖ ≤
        ‖z‖ + ‖(a : ℂ) + Complex.I * (b : ℂ)‖ + ‖w‖ := by linarith
    nlinarith [sq_nonneg (‖z‖ - ‖(a : ℂ) + Complex.I * (b : ℂ)‖), sq_nonneg (‖z‖ - ‖w‖),
      sq_nonneg (‖(a : ℂ) + Complex.I * (b : ℂ)‖ - ‖w‖)]
  refine (ENNReal.ofReal_le_ofReal key).trans_eq ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

/-- `|(a + i b) - (D/2) w|² ≤ 2(a² + b²) + 2|w|²`. -/
theorem picardBd_coord_le2 (w : ℂ) (a b : ℝ) (L : ℕ∞) (x : ℤ) :
    ENNReal.ofReal (‖((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w‖ ^ 2) ≤
      2 * (ENNReal.ofReal (a ^ 2) + ENNReal.ofReal (b ^ 2)) + 2 * ENNReal.ofReal (‖w‖ ^ 2) := by
  have h1 := norm_sub_le ((a : ℂ) + Complex.I * (b : ℂ)) ((degree L x : ℂ) / 2 * w)
  have h3 := picardBd_norm_drift_le L x w
  have h4 := picardBd_norm_mart a b
  have hq := norm_nonneg ((a : ℂ) + Complex.I * (b : ℂ))
  have hN := norm_nonneg (((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w)
  have hw := norm_nonneg w
  have key : ‖((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w‖ ^ 2 ≤
      2 * (a ^ 2 + b ^ 2) + 2 * ‖w‖ ^ 2 := by
    rw [← h4]
    have hs : ‖((a : ℂ) + Complex.I * (b : ℂ)) - (degree L x : ℂ) / 2 * w‖ ≤
        ‖(a : ℂ) + Complex.I * (b : ℂ)‖ + ‖w‖ := by linarith
    nlinarith [sq_nonneg (‖(a : ℂ) + Complex.I * (b : ℂ)‖ - ‖w‖)]
  refine (ENNReal.ofReal_le_ofReal key).trans_eq ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

/-! ### `ℓ²` paths -/

/-- **Continuity in `ℓ²`** (dominated convergence for series): coordinates continuous and
dominated on `[0, n]` by a summable sequence, for every `n`. -/
theorem picardBd_continuous_lp {c : ℝ≥0 → ℤ → ℂ} (hm : ∀ t, Memℓp (c t) 2)
    (hc : ∀ x, Continuous fun t => c t x)
    (hb : ∀ n : ℕ, ∃ g : ℤ → ℝ, Summable g ∧ ∀ t : ℝ≥0, t ≤ n → ∀ x, ‖c t x‖ ^ 2 ≤ g x) :
    Continuous fun t => (⟨c t, hm t⟩ : ℓ²(ℤ, ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro t0
  obtain ⟨n, hn⟩ := exists_nat_gt (t0 : ℝ)
  obtain ⟨g, hg, hgb⟩ := hb n
  have hn' : t0 < (n : ℝ≥0) := by exact_mod_cast hn
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hT : Tendsto (fun t => ∑' x, ‖c t x - c t0 x‖ ^ 2) (𝓝 t0) (𝓝 (∑' _ : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => 4 * g x) (hg.mul_left 4)
      (fun x => ?_) ?_
    · have := ((((hc x).tendsto t0).sub_const (c t0 x)).norm).pow 2
      simpa using this
    · filter_upwards [eventually_le_nhds hn'] with t ht x
      have h1 := hgb t ht x
      have h2 := hgb t0 hn'.le x
      have h3 := norm_sub_le (c t x) (c t0 x)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (c t x), norm_nonneg (c t0 x), norm_nonneg (c t x - c t0 x),
        sq_nonneg (‖c t x‖ - ‖c t0 x‖)]
  rw [tsum_zero] at hT
  have hs := (Real.continuous_sqrt.tendsto 0).comp hT
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun t => ?_
  simp only [Function.comp, lp2_norm_eq_sqrt_tsum, lp.coeFn_sub, Pi.sub_apply]

/-- A summable bound on `[0, n]` from the finiteness of `∑ₓ sup_{[0,n]} |c(x)|²`. -/
theorem picardBd_bound_of_lt_top {c : ℝ → ℤ → ℂ} {n : ℝ}
    (h : ∑' x, (⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖c t x‖ ^ 2)) < ⊤) :
    ∃ g : ℤ → ℝ, Summable g ∧ ∀ t ∈ Set.Icc (0 : ℝ) n, ∀ x, ‖c t x‖ ^ 2 ≤ g x := by
  refine ⟨fun x => (⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖c t x‖ ^ 2)).toReal,
    ENNReal.summable_toReal h.ne, fun t ht x => ?_⟩
  have hx : (⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖c t x‖ ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top h.ne
      (ENNReal.le_tsum (f := fun x => ⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖c t x‖ ^ 2)) x)
  exact (ENNReal.ofReal_le_iff_le_toReal hx).1
    (le_iSup₂_of_le (f := fun t _ => ENNReal.ofReal (‖c t x‖ ^ 2)) t ht le_rfl)

/-- A continuous path is bounded on `[0, T]`. -/
theorem picardBd_iSup_lt_top {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => ψ t ω) (T : ℝ) :
    (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖ψ t ω‖ ^ 2)) < ⊤ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T.toNNReal)).exists_bound_of_continuousOn
    hc.continuousOn
  refine lt_of_le_of_lt (iSup₂_le fun t ht => ?_) (ENNReal.ofReal_lt_top (r := M ^ 2))
  have h1 := hM t.toNNReal ⟨zero_le, Real.toNNReal_le_toNNReal ht.2⟩
  simp only [Real.coe_toNNReal _ ht.1] at h1
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)

end QSSEPtoKPZ
