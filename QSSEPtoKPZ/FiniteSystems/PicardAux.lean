/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Good

/-!
# Auxiliary results for the Picard iteration (task L2a)

Measure-theoretic and `ℓ²` lemmas used in `FiniteSystems/PicardIter.lean`:

* `picardAux_tsum_lintegral_le`: `∑ᵢ ∫⁻ fᵢ ≤ ∫⁻ ∑ᵢ fᵢ` (no measurability needed);
* `picardAux_measurable_uncurry`, `picardAux_measurable_intervalIntegral`: joint measurability of a
  process with continuous paths and measurable values, and measurability of `ω ↦ ∫_0^t f_s(ω) ds`;
* `picardAux_sq_integral_le`: Cauchy–Schwarz, `|∫_0^t f|² ≤ t ∫_0^t |f|²`;
* `picardAux_ofReal_norm_sq`, `picardAux_tsum_shift`: `‖v‖² = ∑ₓ |v(x)|²` and
  `∑ₓ (|v(x+1)|² + |v(x-1)|²) = 2 ‖v‖²` in `[0, ∞]`;
* `picardAux_ofReal_sq_le_iSup_rat`, `picardAux_iSup_rat_le`: the supremum over `[0, n]` of a
  path continuous on `[0, ∞)` is the supremum over the rationals (clamped to `[0, n]`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- `∑ᵢ ∫⁻ fᵢ ≤ ∫⁻ ∑ᵢ fᵢ` for any countable family of functions with values in `[0, ∞]` (the
lower integral is superadditive; no measurability is needed). -/
theorem picardAux_tsum_lintegral_le {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α}
    (f : ι → α → ℝ≥0∞) : ∑' i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑' i, f i a ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  have hS : ∑ i ∈ S, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ S, f i a ∂μ := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.sum_insert hj]
      refine (add_le_add le_rfl ih).trans ?_
      refine (le_lintegral_add _ _).trans (lintegral_mono fun a => ?_)
      rw [Finset.sum_insert hj]
  exact hS.trans (lintegral_mono fun a => ENNReal.sum_le_tsum S)

/-- **Joint measurability.** If `X_t` is measurable for every `t ≥ 0` and `t ↦ X_t(ω)` is
continuous on `[0, ∞)` for every `ω`, then `(t, ω) ↦ X_{t⁺}(ω)` is measurable on `ℝ × Ω`. -/
theorem picardAux_measurable_uncurry {Ω β : Type*} [MeasurableSpace Ω] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {X : ℝ → Ω → β} (hm : ∀ t : ℝ≥0, Measurable (X t))
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) :
    Measurable fun p : ℝ × Ω => X (p.1.toNNReal : ℝ) p.2 := by
  have hu : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => X t ω) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  exact hu.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

/-- **Measurability of a time integral.** If `f_s` is measurable for `0 ≤ s ≤ t` and every path
`s ↦ f_s(ω)` is continuous on `[0, ∞)`, then `ω ↦ ∫_0^t f_s(ω) ds` is measurable. (Applied with
the σ-algebra `𝓖_t`: the drift of an adapted continuous process is adapted.) -/
theorem picardAux_measurable_intervalIntegral {Ω : Type*} [MeasurableSpace Ω] {f : ℝ → Ω → ℂ}
    (t : ℝ≥0) (hm : ∀ s : ℝ≥0, s ≤ t → Measurable (f s))
    (hc : ∀ ω, Continuous fun s : ℝ≥0 => f s ω) :
    Measurable fun ω => ∫ s in (0 : ℝ)..t, f s ω := by
  set u : ℝ≥0 → Ω → ℂ := fun r ω => f (min r t : ℝ≥0) ω with hu
  have hum : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hc ω).comp (continuous_id.min continuous_const))
      (fun r => hm _ (min_le_right _ _))
  have hG : Measurable fun p : Ω × ℝ => u p.2.toNNReal p.1 :=
    hum.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hI := (hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) t)))
  convert hI.measurable using 1
  funext ω
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 ≤ s := hs.1.le
  simp [hu, Real.coe_toNNReal _ hs0, min_eq_left hs.2]

/-- **Cauchy–Schwarz for a time integral:** `|∫_0^t f|² ≤ t ∫_0^t |f|²`, in `[0, ∞]`. -/
theorem picardAux_sq_integral_le {f : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Set.Icc 0 t)) :
    ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, f s‖ ^ 2) ≤
      ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (‖f s‖ ^ 2) := by
  have h1 : ENNReal.ofReal ‖∫ s in (0 : ℝ)..t, f s‖ ≤ ∫⁻ s in Set.Ioc 0 t, ‖f s‖ₑ := by
    rw [intervalIntegral.integral_of_le ht, ofReal_norm]
    exact enorm_integral_le_lintegral_enorm _
  have hm : AEMeasurable (fun s => ‖f s‖ₑ) (volume.restrict (Set.Ioc 0 t)) :=
    ((hf.mono Set.Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc).enorm
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc 0 t))
    Real.HolderConjugate.two_two (f := fun _ => 1) (g := fun s => ‖f s‖ₑ) aemeasurable_const hm
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply,
    MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero] at h2
  have e2 : ∀ s, ‖f s‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f s‖ ^ 2) := fun s => by
    rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [e2] at h2
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    have := ENNReal.rpow_inv_natCast_pow (n := 2) (by norm_num) x
    simpa [one_div] using this
  calc ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, f s‖ ^ 2)
      = ENNReal.ofReal ‖∫ s in (0 : ℝ)..t, f s‖ ^ 2 := ENNReal.ofReal_pow (norm_nonneg _) 2
    _ ≤ (ENNReal.ofReal t ^ (1 / 2 : ℝ) *
          (∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (‖f s‖ ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans h2) 2
    _ = ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (‖f s‖ ^ 2) := by
        rw [mul_pow, hsq, hsq]

/-- `‖v‖² = ∑ₓ |v(x)|²` in `[0, ∞]`, for `v ∈ ℓ²(ℤ)`. -/
theorem picardAux_ofReal_norm_sq (v : ℓ²(ℤ, ℂ)) :
    ENNReal.ofReal (‖v‖ ^ 2) = ∑' x, ENNReal.ofReal (‖v x‖ ^ 2) := by
  have hs : Summable fun x => ‖v x‖ ^ 2 := by
    have := (lp.memℓp v).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa using this
  rw [lp2_norm_eq_sqrt_tsum, Real.sq_sqrt (tsum_nonneg fun _ => by positivity),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs]

/-- `∑ₓ (|v(x+1)|² + |v(x-1)|²) = 2 ‖v‖²` in `[0, ∞]`, for `v ∈ ℓ²(ℤ)`. -/
theorem picardAux_tsum_shift (v : ℓ²(ℤ, ℂ)) :
    ∑' x : ℤ, ENNReal.ofReal (‖v (x + 1)‖ ^ 2 + ‖v (x - 1)‖ ^ 2) =
      2 * ENNReal.ofReal (‖v‖ ^ 2) := by
  simp_rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have h1 : ∑' x : ℤ, ENNReal.ofReal (‖v (x + 1)‖ ^ 2) = ∑' x : ℤ, ENNReal.ofReal (‖v x‖ ^ 2) :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun y => ENNReal.ofReal (‖v y‖ ^ 2))
  have h2 : ∑' x : ℤ, ENNReal.ofReal (‖v (x - 1)‖ ^ 2) = ∑' x : ℤ, ENNReal.ofReal (‖v x‖ ^ 2) :=
    (Equiv.subRight (1 : ℤ)).tsum_eq (fun y => ENNReal.ofReal (‖v y‖ ^ 2))
  rw [ENNReal.tsum_add, picardAux_ofReal_norm_sq, h1, h2, two_mul]

/-- The value at `t ∈ [0, n]` of a path continuous on `[0, ∞)` is bounded by the supremum over
the rationals `q`, clamped to `[0, n]`. -/
theorem picardAux_ofReal_sq_le_iSup_rat {X : ℝ → ℝ} (hX : Continuous fun t : ℝ≥0 => X t)
    {n t : ℝ} (ht : t ∈ Set.Icc 0 n) :
    ENNReal.ofReal (X t ^ 2) ≤ ⨆ q : ℚ, ENNReal.ofReal (X (max 0 (min (q : ℝ) n)) ^ 2) := by
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (X (max 0 (min r n)) ^ 2) with hg
  have hgc : Continuous g := by
    have h1 : Continuous fun r : ℝ => (⟨max 0 (min r n), le_max_left _ _⟩ : ℝ≥0) :=
      (continuous_const.max (continuous_id.min continuous_const)).subtype_mk _
    exact ENNReal.continuous_ofReal.comp ((hX.comp h1).pow 2)
  have hS : IsClosed {r | g r ≤ ⨆ q : ℚ, g q} := isClosed_le hgc continuous_const
  have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {r | g r ≤ ⨆ q : ℚ, g q} := by
    rintro _ ⟨q, rfl⟩
    exact le_iSup (fun q : ℚ => g q) q
  have hmem : t ∈ {r | g r ≤ ⨆ q : ℚ, g q} := by
    have := hS.closure_subset_iff.2 hsub
    rw [Rat.denseRange_cast.closure_range] at this
    exact this (Set.mem_univ t)
  have ht' : max 0 (min t n) = t := by rw [min_eq_left ht.2, max_eq_right ht.1]
  simpa [hg, ht'] using hmem

/-- The supremum over the clamped rationals is at most the supremum over `[0, n]`. -/
theorem picardAux_iSup_rat_le {X : ℝ → ℝ} {n : ℝ} (hn : 0 ≤ n) :
    (⨆ q : ℚ, ENNReal.ofReal (X (max 0 (min (q : ℝ) n)) ^ 2)) ≤
      ⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (X t ^ 2) :=
  iSup_le fun q => le_iSup₂_of_le (f := fun t _ => ENNReal.ofReal (X t ^ 2))
    (max 0 (min (q : ℝ) n)) ⟨le_max_left _ _, max_le hn (min_le_right _ _)⟩ le_rfl

end QSSEPtoKPZ
