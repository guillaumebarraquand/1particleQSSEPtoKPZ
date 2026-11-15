/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.WhiteNoise.LevyAux
public import QSSEPtoKPZ.TiltedField.Defs

/-!
# Proposition 7.2, Step 3: calculus for the test functions and the martingales `M^φ` (task J2)

Auxiliary facts used in Step 3 of the proof of Proposition 7.2:
* `C_b^{1,3}([0,T] × ℝ)` is stable under differences (`IsC13.prop72Sub`), contains the
  time-independent slices `φ_{s₀}` (`IsC13.prop72Slice`), and its elements are Lipschitz in time
  (`IsC13.prop72_abs_sub_le`);
* the process `M^φ` of (7.2) is linear in `φ` (`prop72_limMart_sub`);
* for a martingale with bracket `A`: `𝔼 (M_b - M_a)² = 𝔼 (A_b - A_a)`
  (`prop72_integral_sq_incr`), and the increment of the bracket (7.3) is bounded by a lower
  integral (`prop72_ofReal_limBracket_sub_le`), without any measurability assumption.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {T C C' : ℝ} {φ φt ψ ψt : ℝ → ℝ → ℝ}

/-! ### The class `C_b^{1,3}` -/

/-- `φ, ψ ∈ C_b^{1,3}([0,T] × ℝ)` implies `φ - ψ ∈ C_b^{1,3}([0,T] × ℝ)`, with time derivative
`∂ₜφ - ∂ₜψ`. -/
theorem IsC13.prop72Sub (hφ : IsC13 T φ φt C) (hψ : IsC13 T ψ ψt C') :
    IsC13 T (fun s x => φ s x - ψ s x) (fun s x => φt s x - ψt s x) (C + C') := by
  obtain ⟨c, hcC, hc⟩ := hφ.bound
  obtain ⟨c', hcC', hc'⟩ := hψ.bound
  have hid : ∀ k ≤ 3, ∀ s ∈ Set.Icc 0 T, ∀ x, iteratedDeriv k (fun x => φ s x - ψ s x) x =
      iteratedDeriv k (φ s) x - iteratedDeriv k (ψ s) x := by
    intro k hk s hs x
    exact iteratedDeriv_fun_sub
      (((hφ.contDiff s hs).of_le (by exact_mod_cast hk)).contDiffAt)
      (((hψ.contDiff s hs).of_le (by exact_mod_cast hk)).contDiffAt)
  refine ⟨fun s hs => (hφ.contDiff s hs).sub (hψ.contDiff s hs),
    fun x s hs => (hφ.hasDerivWithinAt x s hs).sub (hψ.hasDerivWithinAt x s hs),
    ⟨hφ.continuousOn.1.sub hψ.continuousOn.1, fun k hk => ?_⟩,
    ⟨fun i => c i + c' i, ?_, fun s hs x => ?_⟩⟩
  · refine ((hφ.continuousOn.2 k hk).sub (hψ.continuousOn.2 k hk)).congr fun p hp => ?_
    exact hid k hk p.1 hp.1 p.2
  · rw [Finset.sum_add_distrib]
    linarith
  · obtain ⟨a0, a1, a2, a3, a4⟩ := hc s hs x
    obtain ⟨b0, b1, b2, b3, b4⟩ := hc' s hs x
    rw [hid 1 (by norm_num) s hs x, hid 2 (by norm_num) s hs x, hid 3 (by norm_num) s hs x]
    exact ⟨(abs_sub _ _).trans (add_le_add a0 b0), (abs_sub _ _).trans (add_le_add a1 b1),
      (abs_sub _ _).trans (add_le_add a2 b2), (abs_sub _ _).trans (add_le_add a3 b3),
      (abs_sub _ _).trans (add_le_add a4 b4)⟩

/-- The slice `φ_{s₀}` (`s₀ ∈ [0,T]`) of `φ ∈ C_b^{1,3}([0,T] × ℝ)`, as a time-independent test
function, is in `C_b^{1,3}([0,T] × ℝ)` (with time derivative `0`). -/
theorem IsC13.prop72Slice (hφ : IsC13 T φ φt C) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 T) :
    IsC13 T (fun _ => φ s₀) (fun _ _ => 0) C := by
  obtain ⟨c, hcC, hc⟩ := hφ.bound
  have hc1 : 0 ≤ c 1 := (abs_nonneg _).trans (hc s₀ hs₀ 0).2.1
  refine ⟨fun _ _ => hφ.contDiff s₀ hs₀, fun x s _ => hasDerivWithinAt_const _ _ _,
    ⟨continuous_const.continuousOn, fun k hk => ?_⟩, ⟨![c 0, 0, c 2, c 3, c 4], ?_, fun s _ x => ?_⟩⟩
  · exact ((hφ.continuousOn.2 k hk).comp_continuous
      (continuous_const.prodMk continuous_snd : Continuous fun p : ℝ × ℝ => (s₀, p.2))
      (fun p => ⟨hs₀, trivial⟩)).continuousOn
  · simp only [Fin.sum_univ_five] at hcC ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    linarith
  · obtain ⟨a0, -, a2, a3, a4⟩ := hc s₀ hs₀ x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue, abs_zero,
      le_refl, true_and]
    exact ⟨a0, a2, a3, a4⟩

/-- Elements of `C_b^{1,3}([0,T] × ℝ)` are Lipschitz in time:
`|φ_s(x) - φ_{s'}(x)| ≤ L |s - s'|` if `|∂ₜφ| ≤ L` on `[0,T] × ℝ`. -/
theorem IsC13.prop72_abs_sub_le (hφ : IsC13 T φ φt C) {L : ℝ}
    (hL : ∀ s ∈ Set.Icc 0 T, ∀ x, |φt s x| ≤ L) {s s' : ℝ} (hs : s ∈ Set.Icc 0 T)
    (hs' : s' ∈ Set.Icc 0 T) (x : ℝ) : |φ s x - φ s' x| ≤ L * |s - s'| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun r => φ r x)
    (f' := fun r => φt r x) (fun r hr => hφ.hasDerivWithinAt x r hr)
    (fun r hr => by rw [Real.norm_eq_abs]; exact hL r hr x) (convex_Icc (0 : ℝ) T) hs' hs
  simpa only [Real.norm_eq_abs] using this

/-- The generator part `∂ₛφ_s + ½ ∂ₓ²φ_s` of (7.2) is continuous on `[0,T] × ℝ`. -/
private lemma IsC13.prop72_gen_cont (hφ : IsC13 T φ φt C) :
    ContinuousOn (Function.uncurry fun s x => φt s x + iteratedDeriv 2 (φ s) x / 2)
      (Set.Icc 0 T ×ˢ Set.univ) :=
  hφ.continuousOn.1.add ((hφ.continuousOn.2 2 (by norm_num)).div_const 2)

/-- The generator part `∂ₛφ_s + ½ ∂ₓ²φ_s` of (7.2) is bounded on `[0,T] × ℝ`. -/
private lemma IsC13.prop72_gen_bdd (hφ : IsC13 T φ φt C) :
    ∃ K, ∀ s ∈ Set.Icc 0 T, ∀ x, |φt s x + iteratedDeriv 2 (φ s) x / 2| ≤ K := by
  obtain ⟨c, -, hc⟩ := hφ.bound
  refine ⟨c 1 + c 3 / 2, fun s hs x => ?_⟩
  obtain ⟨-, a1, -, a3, -⟩ := hc s hs x
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_two]
  linarith

/-- A bounded continuous function is integrable for a finite measure. -/
private lemma prop72_integrable_of_bdd (μ : FiniteMeasure ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    {K : ℝ} (hK : ∀ x, |g x| ≤ K) : Integrable g (μ : Measure ℝ) :=
  Integrable.of_bound hg.aestronglyMeasurable K
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hK x)

/-- The slices of `C_b^{1,3}` functions are integrable for finite measures. -/
private lemma IsC13.prop72_integrable (hφ : IsC13 T φ φt C) (μ : FiniteMeasure ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) : Integrable (φ s) (μ : Measure ℝ) := by
  obtain ⟨c, -, hc⟩ := hφ.bound
  exact prop72_integrable_of_bdd μ (hφ.contDiff s hs).continuous fun x => (hc s hs x).1

/-- The generator parts are integrable for finite measures. -/
private lemma IsC13.prop72_integrable_gen (hφ : IsC13 T φ φt C) (μ : FiniteMeasure ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) :
    Integrable (fun x => φt s x + iteratedDeriv 2 (φ s) x / 2) (μ : Measure ℝ) := by
  obtain ⟨K, hK⟩ := hφ.prop72_gen_bdd
  refine prop72_integrable_of_bdd μ ?_ (hK s hs)
  exact hφ.prop72_gen_cont.comp_continuous (continuous_const.prodMk continuous_id)
    (fun x => ⟨hs, trivial⟩)

/-- `s ↦ 𝒵(s; ∂ₛφ_s + ½ ∂ₓ²φ_s)` is interval integrable on `[0, r]`, `r ∈ [0,T]`. -/
private lemma IsC13.prop72_intervalIntegrable (hφ : IsC13 T φ φt C)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IntervalIntegrable (fun s => pairFM (pathAt γ s)
      (fun x => φt s x + iteratedDeriv 2 (φ s) x / 2)) volume 0 r := by
  have h := continuousOn_pairFM_pathAt hφ.prop72_gen_cont hφ.prop72_gen_bdd
  have h' : ContinuousOn (fun s => pairFM (pathAt γ s)
      (fun x => φt s x + iteratedDeriv 2 (φ s) x / 2)) (Set.Icc 0 T) :=
    h.comp (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨trivial, hs⟩
  exact (h'.mono (Set.Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1

/-! ### Linearity of `M^φ` -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Linearity of (7.2)**: `M^{φ - ψ}(r) = M^φ(r) - M^ψ(r)` for `r ∈ [0,T]` and
`φ, ψ ∈ C_b^{1,3}([0,T] × ℝ)`, for every `ω`. -/
theorem prop72_limMart_sub (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (hφ : IsC13 T φ φt C) (hψ : IsC13 T ψ ψt C') {r : ℝ} (hr : r ∈ Set.Icc 0 T) (ω : Ω) :
    limMart Y (fun s x => φ s x - ψ s x) (fun s x => φt s x - ψt s x) r ω =
      limMart Y φ φt r ω - limMart Y ψ ψt r ω := by
  unfold limMart
  have e1 : pairFM (pathAt (Y ω) r) (fun x => φ r x - ψ r x) =
      pairFM (pathAt (Y ω) r) (φ r) - pairFM (pathAt (Y ω) r) (ψ r) :=
    integral_sub (hφ.prop72_integrable _ hr) (hψ.prop72_integrable _ hr)
  have e2 : ∫ s in (0 : ℝ)..r, pairFM (pathAt (Y ω) s)
        (fun x => (φt s x - ψt s x) + iteratedDeriv 2 (fun x => φ s x - ψ s x) x / 2) =
      (∫ s in (0 : ℝ)..r, pairFM (pathAt (Y ω) s)
        (fun x => φt s x + iteratedDeriv 2 (φ s) x / 2)) -
      ∫ s in (0 : ℝ)..r, pairFM (pathAt (Y ω) s)
        (fun x => ψt s x + iteratedDeriv 2 (ψ s) x / 2) := by
    rw [← intervalIntegral.integral_sub (hφ.prop72_intervalIntegrable (Y ω) hr)
      (hψ.prop72_intervalIntegrable (Y ω) hr)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hr.1] at hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hr.2⟩
    rw [pairFM, pairFM, pairFM, ← integral_sub (hφ.prop72_integrable_gen _ hsT)
      (hψ.prop72_integrable_gen _ hsT)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [iteratedDeriv_fun_sub ((hφ.contDiff s hsT).of_le (by norm_num)).contDiffAt
      ((hψ.contDiff s hsT).of_le (by norm_num)).contDiffAt]
    ring
  simp only at e2 ⊢
  rw [e1, e2]
  ring

/-! ### Increments of martingales and of the bracket (7.3) -/

/-- For a continuous square-integrable martingale with bracket `A` and `0 ≤ a ≤ b ≤ T`:
`𝔼 (M_b - M_a)² = 𝔼 (A_b - A_a)`. -/
theorem prop72_integral_sq_incr {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
    {M A : ℝ → Ω → ℝ} (h : HasBracket T 𝓕 M A μ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) :
    ∫ ω, (M b ω - M a ω) ^ 2 ∂μ = ∫ ω, (A b ω - A a ω) ∂μ := by
  have hb : 0 ≤ b := ha.trans hab
  have h0 := h.levy_integral_mul_incr_sq (r := ⟨a, ha⟩) (r' := ⟨b, hb⟩) hab hbT
    (ξ := fun _ => 1) aestronglyMeasurable_const (K := 1) (fun _ => by simp)
  change ∫ ω, 1 * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω)) ∂μ = 0 at h0
  simp only [one_mul] at h0
  have hMa : MemLp (M a) 2 μ := h.memLp ⟨a, ha⟩ (hab.trans hbT)
  have hMb : MemLp (M b) 2 μ := h.memLp ⟨b, hb⟩ hbT
  have hAa : Integrable (A a) μ := h.integrable_bracket ⟨a, ha⟩ (hab.trans hbT)
  have hAb : Integrable (A b) μ := h.integrable_bracket ⟨b, hb⟩ hbT
  rw [integral_sub (f := fun ω => (M b ω - M a ω) ^ 2) (g := fun ω => A b ω - A a ω)
    (hMb.sub hMa).integrable_sq (hAb.sub hAa)] at h0
  linarith

/-- The increment of the bracket (7.3) is bounded by a lower integral, for every `ω` (no
integrability or measurability assumption): for `0 ≤ a ≤ b`,
`(∫_0^b ∫ Z² ψ² - ∫_0^a ∫ Z² ψ²)⁺ ≤ ∫⁻_{(a,b]} ∫⁻ |Z² ψ²|`. -/
theorem prop72_ofReal_limBracket_sub_le (Z : ℝ → ℝ → Ω → ℝ) (ψ : ℝ → ℝ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
    ENNReal.ofReal (limBracket Z ψ b ω - limBracket Z ψ a ω) ≤
      ∫⁻ s in Set.Ioc a b, ∫⁻ x, ‖Z s x ω ^ 2 * ψ s x ^ 2‖ₑ := by
  set F : ℝ → ℝ := fun s => ∫ x, Z s x ω ^ 2 * ψ s x ^ 2 with hFdef
  have hF0 : ∀ s, 0 ≤ F s := fun s => integral_nonneg fun x => by positivity
  have e : ∀ c, limBracket Z ψ c ω = ∫ s in (0 : ℝ)..c, F s := fun c => rfl
  rw [e, e]
  by_cases hi : IntervalIntegrable F volume 0 b
  · have hia : IntervalIntegrable F volume 0 a :=
      hi.mono_set (by
        rw [Set.uIcc_of_le ha, Set.uIcc_of_le (ha.trans hab)]
        exact Set.Icc_subset_Icc_right hab)
    rw [intervalIntegral.integral_interval_sub_left hi hia, intervalIntegral.integral_of_le hab]
    calc ENNReal.ofReal (∫ s in Set.Ioc a b, F s)
        ≤ ‖∫ s in Set.Ioc a b, F s‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ s in Set.Ioc a b, ‖F s‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono fun s => enorm_integral_le_lintegral_enorm _
  · rw [intervalIntegral.integral_undef hi, zero_sub,
      ENNReal.ofReal_of_nonpos (neg_nonpos.2 (intervalIntegral.integral_nonneg ha
        fun s _ => hF0 s))]
    exact bot_le

end QSSEPtoKPZ
