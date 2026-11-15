/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.StochFubiniRiemann

/-!
# Stochastic Fubini, part 2: convergence of the deterministic error (task K3)

For `f` continuous, vanishing outside `[-R, R]`, `|f| ≤ M`, the error of the Riemann sum
`D_n(s,y) = ∑_k Δ f(a_k) g_{t-s}(a_k - y) - (g_{t-s} ⋆ f)(y)` (`stochFubErr`) satisfies

  `∫_0^t ∫_ℝ D_n(s,y)² C g_s(y)² dy ds → 0`   (`stochFub_err_tendsto`).

With `𝔼 Z(s,y)² ≤ C g_s(y)²` this is the `L²(Ω × ℝ₊ × ℝ)` convergence of the integrands in the
proof of (7.13). Dominated convergence in `y` for each `s ∈ (0,t)` (`|D_n| ≤ c (t-s)^{-1/2}`,
`∫ g_s² < ∞`), then in `s`, with the bound
* `c s^{-1/2}` for `s ≤ t/2` (`D_n` uniformly bounded, `∫ g_s² = (4πs)^{-1/2}`);
* `c ((t-s)^{-1/2} + 1)` for `s > t/2` (`g_s² ≤ (πt)^{-1}` and the `L²(dy)` bound
  `∫ D_n(s,y)² dy ≤ 2(2RM)²(4π(t-s))^{-1/2} + 2‖f‖₂²`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The error `D_n(s,y) = ∑_k Δ f(a_k) g_{t-s}(a_k - y) - (g_{t-s} ⋆ f)(y)` of the Riemann sum. -/
def stochFubErr (f : ℝ → ℝ) (R t : ℝ) (n : ℕ) (s y : ℝ) : ℝ :=
  stochFubSum f R (t - s) n y - heatConv (t - s) f y

/-- `(s, y) ↦ D_n(s,y)` is measurable. -/
theorem stochFub_measurable_err {f : ℝ → ℝ} (hf : Measurable f) (R t : ℝ) (n : ℕ) :
    Measurable (fun q : ℝ × ℝ => stochFubErr f R t n q.1 q.2) :=
  (stochFub_measurable_sum R t n).sub (stochFub_measurable_heatConv hf t)

/-- `1/√s` is integrable on `(0,t)`. -/
theorem stochFub_integrableOn_inv_sqrt {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s => 1 / Real.sqrt s) (Set.Ioo 0 t) := by
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 / 2)) ht).2 (by norm_num)
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioo
  show s ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt s
  rw [Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow, one_div]

/-- `1/√(t-s)` is integrable on `(0,t)`. -/
private lemma stochFub_integrableOn_inv_sqrt_sub {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s => 1 / Real.sqrt (t - s)) (Set.Ioo 0 t) := by
  have h := stochFub_integrableOn_inv_sqrt ht
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le] at h ⊢
  have := h.comp_sub_left t
  rw [sub_zero, sub_self] at this
  exact this.symm

/-- **Convergence of the deterministic error**:
`∫_0^t ∫_ℝ D_n(s,y)² C g_s(y)² dy ds → 0`. -/
theorem stochFub_err_tendsto {f : ℝ → ℝ} (hf : Continuous f) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ x, R ≤ |x| → f x = 0) {M : ℝ} (hM : ∀ x, |f x| ≤ M) {t C : ℝ} (ht : 0 < t)
    (hC : 0 ≤ C) :
    Tendsto (fun n : ℕ => ∫⁻ s in Set.Ioo 0 t, ∫⁻ y,
        ENNReal.ofReal (stochFubErr f R t n s y ^ 2) * ENNReal.ofReal (C * heatKernel s y ^ 2))
      atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hf2 : MemLp f 2 volume := hf.memLp_of_hasCompactSupport (stochFub_hasCompactSupport hsupp)
  set Q := ∫ x, f x ^ 2 with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  set K : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n q =>
    ENNReal.ofReal (stochFubErr f R t n q.1 q.2 ^ 2) * ENNReal.ofReal (C * heatKernel q.1 q.2 ^ 2)
    with hK
  have hKm : ∀ n, Measurable (K n) := fun n =>
    ((stochFub_measurable_err hf.measurable R t n).pow_const 2).ennreal_ofReal.mul
      ((measurable_const.mul (stochFub_measurable_heatKernel.pow_const 2)).ennreal_ofReal)
  -- the error is bounded by `2RM (2π(t-s))^{-1/2} + M`
  have habs : ∀ n s y, s < t → |stochFubErr f R t n s y| ≤
      2 * R * M / Real.sqrt (2 * Real.pi * (t - s)) + M := fun n s y hs =>
    (abs_sub _ _).trans (add_le_add (stochFubSum_abs_le hM hR n y)
      (abs_heatConv_le (sub_pos.2 hs) hf.measurable hM y))
  -- the dominating function in `s`
  set B := 2 * R * M / Real.sqrt (Real.pi * t) + M with hB
  set A₁ := B ^ 2 * C / Real.sqrt (4 * Real.pi) with hA₁
  set A₂ := C / (Real.pi * t) * 2 * (2 * R * M) ^ 2 / Real.sqrt (4 * Real.pi) with hA₂
  set A₃ := C / (Real.pi * t) * 2 * Q with hA₃
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hA₃0 : 0 ≤ A₃ := by positivity
  set g : ℝ → ℝ := fun s => A₁ * (1 / Real.sqrt s) + A₂ * (1 / Real.sqrt (t - s)) + A₃ with hg
  have hgi : IntegrableOn g (Set.Ioo 0 t) :=
    (((stochFub_integrableOn_inv_sqrt ht).const_mul A₁).add
      ((stochFub_integrableOn_inv_sqrt_sub ht).const_mul A₂)).add
      (integrableOn_const (by simp))
  have hbound : ∀ n, ∀ s ∈ Set.Ioo 0 t, ∫⁻ y, K n (s, y) ≤ ENNReal.ofReal (g s) := by
    intro n s hs
    have hr : 0 < t - s := sub_pos.2 hs.2
    have hs0 := hs.1
    have e4 : ∀ u, 0 ≤ u → Real.sqrt (4 * Real.pi * u) = Real.sqrt (4 * Real.pi) * Real.sqrt u :=
      fun u hu => Real.sqrt_mul (by positivity) u
    rcases le_or_gt s (t / 2) with hs2 | hs2
    · -- `s ≤ t/2`: `D_n` is bounded by `B`
      have hBy : ∀ y, stochFubErr f R t n s y ^ 2 ≤ B ^ 2 := by
        intro y
        have h1 := habs n s y hs.2
        have h2 : 2 * R * M / Real.sqrt (2 * Real.pi * (t - s)) ≤
            2 * R * M / Real.sqrt (Real.pi * t) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
      calc ∫⁻ y, K n (s, y)
          ≤ ∫⁻ y, ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (C * heatKernel s y ^ 2) :=
            lintegral_mono fun y => by
              simp only [hK]
              gcongr ?_ * _
              exact ENNReal.ofReal_le_ofReal (hBy y)
        _ = ENNReal.ofReal (B ^ 2 * (C / Real.sqrt (4 * Real.pi * s))) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              stochFub_lintegral_heatKernel_sq hs0 hC, ENNReal.ofReal_mul (sq_nonneg _)]
        _ ≤ ENNReal.ofReal (g s) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have e : B ^ 2 * (C / Real.sqrt (4 * Real.pi * s)) = A₁ * (1 / Real.sqrt s) := by
              rw [e4 s hs0.le, hA₁]; ring
            rw [e, hg]
            have : 0 ≤ A₂ * (1 / Real.sqrt (t - s)) := by positivity
            linarith
    · -- `s > t/2`: `C g_s² ≤ C/(πt)` and the `L²(dy)` bound on `D_n`
      have hgy : ∀ y, C * heatKernel s y ^ 2 ≤ C / (Real.pi * t) := by
        intro y
        have h1 := stochFub_heatKernel_le s y
        have h0 := heatKernel_nonneg s y
        have h2 : heatKernel s y ^ 2 ≤ 1 / (2 * Real.pi * s) := by
          calc heatKernel s y ^ 2 ≤ (1 / Real.sqrt (2 * Real.pi * s)) ^ 2 :=
                pow_le_pow_left₀ h0 h1 2
            _ = 1 / (2 * Real.pi * s) := by
                rw [div_pow, Real.sq_sqrt (by positivity), one_pow]
        have h3 : 1 / (2 * Real.pi * s) ≤ 1 / (Real.pi * t) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith [Real.pi_pos])
        calc C * heatKernel s y ^ 2 ≤ C * (1 / (Real.pi * t)) :=
              mul_le_mul_of_nonneg_left (h2.trans h3) hC
          _ = C / (Real.pi * t) := by ring
      have hL2 : ∫⁻ y, ENNReal.ofReal (stochFubErr f R t n s y ^ 2) ≤
          ENNReal.ofReal (2 * ((2 * R * M) ^ 2 / Real.sqrt (4 * Real.pi * (t - s))) + 2 * Q) := by
        obtain ⟨hSi, hSle⟩ := stochFubSum_sq_integral_le (f := f) hM hR hr n
        obtain ⟨hHi, hHle⟩ := heatConv_sq_integral_le hr hf2
        have hi : Integrable (fun y => 2 * stochFubSum f R (t - s) n y ^ 2 +
            2 * heatConv (t - s) f y ^ 2) := (hSi.const_mul 2).add (hHi.const_mul 2)
        calc ∫⁻ y, ENNReal.ofReal (stochFubErr f R t n s y ^ 2)
            ≤ ∫⁻ y, ENNReal.ofReal (2 * stochFubSum f R (t - s) n y ^ 2 +
                2 * heatConv (t - s) f y ^ 2) := lintegral_mono fun y => by
              refine ENNReal.ofReal_le_ofReal ?_
              simp only [stochFubErr]
              nlinarith [sq_nonneg (stochFubSum f R (t - s) n y + heatConv (t - s) f y)]
          _ = ENNReal.ofReal (∫ y, (2 * stochFubSum f R (t - s) n y ^ 2 +
                2 * heatConv (t - s) f y ^ 2)) :=
              (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => by positivity)).symm
          _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [integral_add (hSi.const_mul 2) (hHi.const_mul 2), integral_const_mul,
                integral_const_mul]
              linarith
      calc ∫⁻ y, K n (s, y)
          ≤ ∫⁻ y, ENNReal.ofReal (stochFubErr f R t n s y ^ 2) *
              ENNReal.ofReal (C / (Real.pi * t)) :=
            lintegral_mono fun y => by
              simp only [hK]
              gcongr _ * ?_
              exact ENNReal.ofReal_le_ofReal (hgy y)
        _ = (∫⁻ y, ENNReal.ofReal (stochFubErr f R t n s y ^ 2)) *
              ENNReal.ofReal (C / (Real.pi * t)) :=
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (2 * ((2 * R * M) ^ 2 / Real.sqrt (4 * Real.pi * (t - s))) + 2 * Q) *
              ENNReal.ofReal (C / (Real.pi * t)) := by gcongr
        _ = ENNReal.ofReal ((2 * ((2 * R * M) ^ 2 / Real.sqrt (4 * Real.pi * (t - s))) + 2 * Q) *
              (C / (Real.pi * t))) := (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (g s) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have e : (2 * ((2 * R * M) ^ 2 / Real.sqrt (4 * Real.pi * (t - s))) + 2 * Q) *
                (C / (Real.pi * t)) = A₂ * (1 / Real.sqrt (t - s)) + A₃ := by
              rw [e4 (t - s) hr.le, hA₂, hA₃]; ring
            rw [e, hg]
            have : 0 ≤ A₁ * (1 / Real.sqrt s) := by positivity
            linarith
  have hlim : ∀ s ∈ Set.Ioo 0 t, Tendsto (fun n => ∫⁻ y, K n (s, y)) atTop (𝓝 0) := by
    intro s hs
    set B' := 2 * R * M / Real.sqrt (2 * Real.pi * (t - s)) + M
    have hfin : ∫⁻ y, ENNReal.ofReal (B' ^ 2) * ENNReal.ofReal (C * heatKernel s y ^ 2) ≠ ∞ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, stochFub_lintegral_heatKernel_sq hs.1 hC]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hdom : ∀ n, (fun y => K n (s, y)) ≤ᵐ[volume]
        fun y => ENNReal.ofReal (B' ^ 2) * ENNReal.ofReal (C * heatKernel s y ^ 2) := by
      intro n
      refine ae_of_all _ fun y => ?_
      simp only [hK]
      gcongr ?_ * _
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs n s y hs.2) 2
    have hpt : ∀ y, Tendsto (fun n => K n (s, y)) atTop (𝓝 0) := by
      intro y
      have h1 : Tendsto (fun n => stochFubErr f R t n s y) atTop (𝓝 0) := by
        have := (stochFubSum_tendsto hf hR hsupp (t - s) y).sub_const (heatConv (t - s) f y)
        rw [sub_self] at this
        exact this
      have h2 : Tendsto (fun n => ENNReal.ofReal (stochFubErr f R t n s y ^ 2)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (h1.pow 2)
        simpa using this
      have := ENNReal.Tendsto.mul_const h2 (Or.inr (ENNReal.ofReal_ne_top
        (r := C * heatKernel s y ^ 2)))
      simpa using this
    have := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun n y => K n (s, y)) (f := fun _ => 0) _
      (fun n => (hKm n).comp measurable_prodMk_left) hdom hfin (ae_of_all _ hpt)
    simpa using this
  have hΦm : ∀ n, Measurable (fun s => ∫⁻ y, K n (s, y)) := fun n =>
    (hKm n).lintegral_prod_right'
  have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Ioo 0 t))
    (F := fun n s => ∫⁻ y, K n (s, y)) (f := fun _ => 0) (fun s => ENNReal.ofReal (g s)) hΦm
    (fun n => (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ (hbound n)))
    hgi.lintegral_lt_top.ne
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ hlim))
  simpa using this

end QSSEPtoKPZ
