/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.ProductPathwise
public import QSSEPtoKPZ.ItoIntegral.Stopping

/-!
# Product rule: Riemann sums against an Itô integral (package C, task C6)

Auxiliary material for `ItoIntegral/Product.lean`.

* `itoProd_isItoIntegrable_sub`, `itoProd_stochInt_sub`: `I(h - g) = I(h) - I(g)`.
* `itoProd_tendsto_riemann`: if `Z` is bounded, adapted and left-continuous and `h` is
  Itô-integrable, then `∑_{k < m} Z(t_k) (I_{t_{k+1}}(h) - I_{t_k}(h)) → I_t(Z h)` in `L²`
  (`t_k = k t / m`). Proof: `Z(t_k) (I_{t_{k+1}}(h) - I_{t_k}(h)) = I_t(Z(t_k) 𝟙_{(t_k, t_{k+1}]} h)`
  (`stochInt_mul_indicator_gt`), so the difference is `I_t((Z^{(m)} - Z) h)` with `Z^{(m)}` the
  left-point step process; isometry and dominated convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-- The difference of two Itô-integrable families is Itô-integrable. -/
theorem itoProd_isItoIntegrable_sub {h g : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    (hg : IsItoIntegrable 𝓖 μ g) : IsItoIntegrable 𝓖 μ (fun i s ω => h i s ω - g i s ω) := by
  have e : (fun i s ω => h i s ω - g i s ω) = fun i s ω => h i s ω + (-1) * g i s ω := by
    funext i s ω
    ring
  rw [e]
  exact hh.add (hg.const_mul (-1))

/-- `I(h - g) = I(h) - I(g)`, for all `t`, almost surely. -/
theorem itoProd_stochInt_sub (hB : IsBrownianFamily 𝓖 B μ) {h g : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (hg : IsItoIntegrable 𝓖 μ g) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (fun i s ω => h i s ω - g i s ω) t ω =
      stochInt 𝓖 μ B h t ω - stochInt 𝓖 μ B g t ω := by
  have e : (fun i s ω => h i s ω - g i s ω) = fun i s ω => h i s ω + (-1) * g i s ω := by
    funext i s ω
    ring
  filter_upwards [stochInt_add hB hh (hg.const_mul (-1)), stochInt_const_mul hB hg (-1)]
    with ω h1 h2 t
  rw [e, h1 t, h2 t]
  ring

/-- **Dominated convergence for the energy of `F_n h`.** If `h` is Itô-integrable, the `F_n` are
jointly measurable on `(0, ∞) × Ω`, bounded by `C` on `(0, T]` and tend to `0` pointwise on
`(0, T]`, then `energy (F_n h) T → 0` (dominator `C² ∑ᵢ hᵢ²`, integrable since the energy of `h`
is finite). -/
private lemma energy_mul_tendsto {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    {F : ℕ → ℝ → Ω → ℝ} {C T : ℝ}
    (hFm : ∀ n, Measurable fun p : ℝ × Ω => if 0 < p.1 then F n p.1 p.2 else 0)
    (hFb : ∀ n ω (s : ℝ), 0 < s → s ≤ T → |F n s ω| ≤ C)
    (hFlim : ∀ ω (s : ℝ), 0 < s → s ≤ T → Tendsto (fun n => F n s ω) atTop (𝓝 0)) :
    Tendsto (fun n => energy μ (fun i s ω => F n s ω * h i s ω) T) atTop (𝓝 0) := by
  set Ψ : ℝ × Ω → ℝ≥0∞ := fun p => ∑' i, ‖(if 0 < p.1 then h i p.1 p.2 else 0)‖ₑ ^ 2 with hΨ
  have hΨm : Measurable Ψ := itoEnergy_measurable_tsum hh.meas
  set Φ : ℕ → ℝ × Ω → ℝ≥0∞ :=
    fun n p => ‖(if 0 < p.1 then F n p.1 p.2 else 0)‖ₑ ^ 2 * Ψ p with hΦ
  have hΦm : ∀ n, Measurable (Φ n) := fun n => ((hFm n).enorm.pow_const 2).mul hΨm
  have hΦs : ∀ n ω s, s ∈ Set.Ioc 0 T → ∑' i, ‖F n s ω * h i s ω‖ₑ ^ 2 = Φ n (s, ω) := by
    intro n ω s hs
    simp only [hΦ, hΨ, hs.1, ↓reduceIte]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [enorm_mul, mul_pow]
  have hE : ∀ n, energy μ (fun i s ω => F n s ω * h i s ω) T =
      ∫⁻ ω, (∫⁻ s in Set.Ioc 0 T, Φ n (s, ω)) ∂μ := fun n =>
    lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Ioc fun s hs => hΦs n ω s hs
  set c : ℝ≥0∞ := ENNReal.ofReal (C ^ 2) with hc
  have hbound : ∀ n ω s, s ∈ Set.Ioc 0 T → Φ n (s, ω) ≤ c * Ψ (s, ω) := by
    intro n ω s hs
    simp only [hΦ, hs.1, ↓reduceIte]
    gcongr
    rw [itoEnergy_enorm_sq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hFb n ω s hs.1 hs.2) 2
  have hPE : ∀ ω, pathEnergy h T ω = ∫⁻ s in Set.Ioc 0 T, Ψ (s, ω) := fun ω =>
    itoEnergy_pathEnergy_eq_pos h T ω
  have hin : ∀ ω, pathEnergy h T ω ≠ ∞ →
      Tendsto (fun n => ∫⁻ s in Set.Ioc 0 T, Φ n (s, ω)) atTop (𝓝 0) := by
    intro ω hω
    rw [hPE] at hω
    have hfin : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 T)), Ψ (s, ω) < ∞ :=
      ae_lt_top (hΨm.comp measurable_prodMk_right) hω
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Ioc 0 T))
      (F := fun n s => Φ n (s, ω)) (f := fun _ => 0) (fun s => c * Ψ (s, ω))
      (fun n => (hΦm n).comp measurable_prodMk_right)
      (fun n => ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => hbound n ω s hs)
      (by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)
      (by
        filter_upwards [hfin, ae_restrict_mem measurableSet_Ioc] with s hs hsI
        have h1 : Tendsto (fun n => ‖F n s ω‖ₑ ^ 2) atTop (𝓝 0) := by
          have := (ENNReal.continuous_ofReal.tendsto _).comp ((hFlim ω s hsI.1 hsI.2).pow 2)
          simpa [Function.comp_def, itoEnergy_enorm_sq] using this
        have h2 := ENNReal.Tendsto.mul_const h1 (b := Ψ (s, ω)) (Or.inr hs.ne)
        simp only [zero_mul] at h2
        simpa [hΦ, hsI.1] using h2)
    simpa using this
  have hgood : ∀ᵐ ω ∂μ, pathEnergy h T ω ≠ ∞ := by
    have := ae_lt_top (itoEnergy_measurable_pathEnergy hh.meas T) (hh.energy_lt_top T).ne
    filter_upwards [this] with ω hω using hω.ne
  simp_rw [hE]
  have := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun n ω => ∫⁻ s in Set.Ioc 0 T, Φ n (s, ω)) (f := fun _ => 0)
    (fun ω => c * pathEnergy h T ω) (fun n => (hΦm n).lintegral_prod_left')
    (fun n => ae_of_all _ fun ω => by
      refine (setLIntegral_mono' measurableSet_Ioc fun s hs => hbound n ω s hs).trans_eq ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      show _ = c * pathEnergy h T ω
      rw [hPE])
    (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hh.energy_lt_top T).ne)
    (by filter_upwards [hgood] with ω hω using hin ω hω)
  simpa using this

/-- `(𝟙_{a < s} - 𝟙_{b < s}) x y = 𝟙_{a < s ≤ b} x y` for `a ≤ b`. -/
private lemma ite_sub_ite_mul {a b s x y : ℝ} (hab : a ≤ b) :
    ((if a < s then x * y else 0) - if b < s then x * y else 0) =
      (if a < s ∧ s ≤ b then x else 0) * y := by
  by_cases h1 : a < s <;> by_cases h2 : b < s
  · have : ¬ (s ≤ b) := not_le.2 h2
    simp [h1, h2, this]
  · simp [h1, h2, not_lt.1 h2]
  · exact absurd (hab.trans_lt h2) h1
  · simp [h1, h2]

/-- The family `ξ 𝟙_{s > v} h` with `ξ = Z(u)` (used with `u = t_k`, `v ∈ {t_k, t_{k+1}}`). -/
private def rsH (Z : ℝ → Ω → ℝ) (h : ι → ℝ → Ω → ℝ) (u v : ℝ≥0) : ι → ℝ → Ω → ℝ :=
  fun i s ω => if (v : ℝ) < s then Z u ω * h i s ω else 0

/-- **Riemann sums against an Itô integral.** Let `h` be Itô-integrable and let `Z` be a real
process, bounded by `C` at times `s ≥ 0`, adapted, with left-continuous paths at every `s > 0`.
Then `𝔼[(∑_{k < m} Z(t_k) (I_{t_{k+1}}(h) - I_{t_k}(h)) - I_t(Z h))²] → 0`, `t_k = k t / m`. -/
theorem itoProd_tendsto_riemann (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) {Z : ℝ → Ω → ℝ} {C : ℝ}
    (hZ : ∀ ω (s : ℝ), 0 ≤ s → |Z s ω| ≤ C) (hZa : ∀ t : ℝ≥0, Measurable[𝓖 t] (Z t))
    (hZlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => Z r ω) (Set.Iic s) s)
    (t : ℝ≥0) :
    Tendsto (fun m : ℕ => ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range m,
        Z (itoProdGrid t m k) ω * (stochInt 𝓖 μ B h (itoProdGrid t m (k + 1)) ω -
          stochInt 𝓖 μ B h (itoProdGrid t m k) ω) -
        stochInt 𝓖 μ B (fun i s ω => Z s ω * h i s ω) t ω) ^ 2) ∂μ) atTop (𝓝 0) := by
  classical
  have hZ' : ∀ ω (s : ℝ), 0 < s → |Z s ω| ≤ C := fun ω s hs => hZ ω s hs.le
  have hZh : IsItoIntegrable 𝓖 μ (fun i s ω => Z s ω * h i s ω) :=
    hh.mul_leftContinuous hZ' hZa hZlc
  set g : ℕ → ℕ → ℝ≥0 := fun m k => itoProdGrid t m k with hg
  have hξb : ∀ m k, ∃ C', ∀ ω, |Z (g m k) ω| ≤ C' := fun m k =>
    ⟨C, fun ω => hZ ω _ (NNReal.coe_nonneg _)⟩
  have hHint : ∀ m k j, k ≤ j → IsItoIntegrable 𝓖 μ (rsH Z h (g m k) (g m j)) :=
    fun m k j hkj => hh.mul_indicator_gt
      ((hZa (g m k)).mono (𝓖.mono (itoProdGrid_mono t m hkj)) le_rfl) (hξb m k)
  have hstoch : ∀ m k j, k ≤ j → ∀ᵐ ω ∂μ, ∀ t' : ℝ≥0,
      stochInt 𝓖 μ B (rsH Z h (g m k) (g m j)) t' ω =
        Z (g m k) ω * (stochInt 𝓖 μ B h t' ω -
          stochInt 𝓖 μ B h ((min t' (g m j) : ℝ≥0) : ℝ) ω) :=
    fun m k j hkj => stochInt_mul_indicator_gt hB hh
      ((hZa (g m k)).mono (𝓖.mono (itoProdGrid_mono t m hkj)) le_rfl) (hξb m k)
  have hD : ∀ m k, IsItoIntegrable 𝓖 μ
      (fun i s ω => rsH Z h (g m k) (g m k) i s ω - rsH Z h (g m k) (g m (k + 1)) i s ω) :=
    fun m k => itoProd_isItoIntegrable_sub (hHint m k k le_rfl) (hHint m k (k + 1) k.le_succ)
  have hS : ∀ m, IsItoIntegrable 𝓖 μ (fun i s ω => ∑ k ∈ Finset.range m,
      (rsH Z h (g m k) (g m k) i s ω - rsH Z h (g m k) (g m (k + 1)) i s ω)) :=
    fun m => IsItoIntegrable.finset_sum _ fun k _ => hD m k
  have hG : ∀ m, IsItoIntegrable 𝓖 μ (fun i s ω => ∑ k ∈ Finset.range m,
      (rsH Z h (g m k) (g m k) i s ω - rsH Z h (g m k) (g m (k + 1)) i s ω) -
        Z s ω * h i s ω) :=
    fun m => itoProd_isItoIntegrable_sub (hS m) hZh
  -- the Riemann sum minus the integral is the integral of `G_m`
  have hae : ∀ m : ℕ, ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range m,
      Z (itoProdGrid t m k) ω * (stochInt 𝓖 μ B h (itoProdGrid t m (k + 1)) ω -
        stochInt 𝓖 μ B h (itoProdGrid t m k) ω) -
      stochInt 𝓖 μ B (fun i s ω => Z s ω * h i s ω) t ω) =
      stochInt 𝓖 μ B (fun i s ω => ∑ k ∈ Finset.range m,
        (rsH Z h (g m k) (g m k) i s ω - rsH Z h (g m k) (g m (k + 1)) i s ω) -
          Z s ω * h i s ω) t ω := by
    intro m
    have h1 := ae_all_iff.2 fun k => hstoch m k k le_rfl
    have h2 := ae_all_iff.2 fun k => hstoch m k (k + 1) k.le_succ
    have h3 := ae_all_iff.2 fun k =>
      itoProd_stochInt_sub hB (hHint m k k le_rfl) (hHint m k (k + 1) k.le_succ)
    filter_upwards [h1, h2, h3, itoProd_stochInt_sub hB (hS m) hZh,
      stochInt_finset_sum hB (Finset.range m) (fun k _ => hD m k)] with ω h1 h2 h3 h4 h5
    rw [h4 t, h5 t]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [h3 k t, h1 k t, h2 k t]
    have hk1 : k + 1 ≤ m := Finset.mem_range.1 hk
    rw [min_eq_right (itoProdGrid_le t (Nat.le_of_succ_le hk1)),
      min_eq_right (itoProdGrid_le t hk1)]
    ring
  -- the integrand `G_m` is `(step process - Z) h`
  let δ : ℕ → ℝ := fun n => ((t / n : ℝ≥0) : ℝ)
  have hcast : ∀ n k, ((g n k : ℝ≥0) : ℝ) = (k : ℝ) * δ n := fun n k => by
    simp only [hg, δ, itoProdGrid, NNReal.coe_mul, NNReal.coe_natCast]
  have hcast1 : ∀ n k, ((g n (k + 1) : ℝ≥0) : ℝ) = ((k : ℝ) + 1) * δ n := fun n k => by
    rw [hcast]
    push_cast
    ring
  let F : ℕ → ℝ → Ω → ℝ := fun n s ω =>
    itoGridStep (fun k ω => Z (k * δ n) ω) (δ n) n s ω - Z s ω
  have hGF : ∀ n, (fun i s ω => ∑ k ∈ Finset.range n,
      (rsH Z h (g n k) (g n k) i s ω - rsH Z h (g n k) (g n (k + 1)) i s ω) -
        Z s ω * h i s ω) = fun i s ω => F n s ω * h i s ω := by
    intro n
    funext i s ω
    simp only [F, itoGridStep, sub_mul, Finset.sum_mul, rsH]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ite_sub_ite_mul (NNReal.coe_le_coe.2 (itoProdGrid_mono t n k.le_succ)), hcast, hcast1]
  have hlim : Tendsto (fun n => energy μ (fun i s ω => F n s ω * h i s ω) t) atTop (𝓝 0) := by
    have hZm := measurable_pos_of_leftContinuous hZ' hZa hZlc
    refine energy_mul_tendsto hh (C := |C| + |C|) (fun n => ?_) (fun n ω s hs _ => ?_)
      (fun ω s hs hst => ?_)
    · have : (fun p : ℝ × Ω => if 0 < p.1 then F n p.1 p.2 else 0) =
          fun p => itoGridStep (fun k ω => Z (k * δ n) ω) (δ n) n p.1 p.2 -
            (if 0 < p.1 then Z p.1 p.2 else 0) := by
        funext p
        by_cases hp : 0 < p.1
        · simp [F, hp]
        · rw [itoGridStep_eq_zero (fun h => hp h.2)]
          simp [F, hp]
      rw [this]
      exact (measurable_itoGridStep (fun k => (itoGrid_measurable_point hZa (t / n) k).mono
        (𝓖.le _) le_rfl) _ _).sub hZm
    · have h1 := abs_itoGridStep_le (C := C) (ξ := fun k ω => Z (k * δ n) ω)
        (fun k ω => hZ ω _ (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _))) (δ n) n s ω
      exact (abs_sub _ _).trans (add_le_add h1 ((hZ' ω s hs).trans (le_abs_self C)))
    · have htpos : 0 < (t : ℝ) := hs.trans_le hst
      have hδ : ∀ n, δ n = (t : ℝ) / n := fun n => by simp [δ]
      have h := tendsto_itoGridStep (f := Z) (φ := id) continuous_id (ω := ω) hs
        (δ := δ) (N := fun n => n)
        ((eventually_ge_atTop 1).mono fun n hn => by
          rw [hδ n]; exact div_pos htpos (Nat.cast_pos.2 (by omega))) ?_ ?_ (hZlc ω s hs)
      · simpa [F] using h.sub_const (Z s ω)
      · exact (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)).congr fun n => (hδ n).symm
      · filter_upwards [eventually_ge_atTop 1] with n hn
        rw [hδ, mul_div_cancel₀ _ (by positivity)]
        exact hst
  have hE : ∀ m, ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range m,
      Z (itoProdGrid t m k) ω * (stochInt 𝓖 μ B h (itoProdGrid t m (k + 1)) ω -
        stochInt 𝓖 μ B h (itoProdGrid t m k) ω) -
      stochInt 𝓖 μ B (fun i s ω => Z s ω * h i s ω) t ω) ^ 2) ∂μ =
      energy μ (fun i s ω => F m s ω * h i s ω) t := by
    intro m
    rw [← hGF, ← lintegral_stochInt_sq hB (hG m)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae m] with ω hω
    rw [hω]
  simp_rw [hE]
  exact hlim

end QSSEPtoKPZ
