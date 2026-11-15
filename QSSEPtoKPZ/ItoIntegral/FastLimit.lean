/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Convergence
public import QSSEPtoKPZ.Martingales.Doob

/-!
# Pathwise limits of elementary integrals along fast sequences (package C, task C3, auxiliary)

All results are in the namespace `QSSEPtoKPZ.StochIntAux`.

* `elemInt_sub_doob`: Doob's inequality for the difference of two elementary integrals,
  `𝔼 sup_{[0,T]} (I(e) - I(e'))² ≤ 4 𝔼 ∫_0^T ∑ᵢ (eᵢ - e'ᵢ)²`.
* `exists_lim_of_geom`, `continuous_of_geom`: a sequence of functions whose increments are
  bounded by `C 2⁻ᵏ` on `(-∞, k]` converges, locally uniformly, to a limit (continuous if the
  functions are).
* `elemInt_ae_tendsto`: if `𝔼 ∫_0^k ∑ᵢ (e_{k+1} - e_k)² ≤ 4 · 8⁻ᵏ`, then almost surely the
  elementary integrals `I_t(e_k)` converge for every `t`, to a continuous function of `t`
  (Doob's inequality and `∑ₖ 4ᵏ sup_{[0,k]} |I(e_{k+1}) - I(e_k)|² ∈ L¹`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

namespace StochIntAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*}

/-! ### A deterministic lemma -/

/-- If `|F_{k+1}(t) - F_k(t)| ≤ C 2⁻ᵏ` for `t ≤ k`, then `F_k` converges pointwise to some `L`,
with `|F_k(t) - L(t)| ≤ 2 C 2⁻ᵏ` for `t ≤ n ≤ k`. -/
lemma exists_lim_of_geom {F : ℕ → ℝ → ℝ} {C : ℝ}
    (h : ∀ (k : ℕ) (t : ℝ), t ≤ k → |F (k + 1) t - F k t| ≤ C * (1 / 2) ^ k) :
    ∃ L : ℝ → ℝ, (∀ t, Tendsto (fun k => F k t) atTop (𝓝 (L t))) ∧
      ∀ n : ℕ, ∀ t : ℝ, t ≤ n → ∀ k : ℕ, n ≤ k → |F k t - L t| ≤ 2 * C * (1 / 2) ^ k := by
  have key : ∀ (n : ℕ) (t : ℝ), t ≤ n → ∀ m : ℕ,
      dist (F (m + n) t) (F (m + 1 + n) t) ≤ (2 * C * (1 / 2) ^ n) / 2 / 2 ^ m := by
    intro n t ht m
    rw [Real.dist_eq, abs_sub_comm, show m + 1 + n = (m + n) + 1 by ring]
    refine (h _ t (ht.trans (by exact_mod_cast Nat.le_add_left n m))).trans (le_of_eq ?_)
    rw [pow_add, one_div, inv_pow, inv_pow]
    field_simp
  have hconv : ∀ t, ∃ L, Tendsto (fun k => F k t) atTop (𝓝 L) := by
    intro t
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric_two (key ⌈t⌉₊ t (Nat.le_ceil t)))
    exact ⟨L, (tendsto_add_atTop_iff_nat ⌈t⌉₊).1 hL⟩
  choose L hL using hconv
  refine ⟨L, hL, fun n t ht k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, by omega⟩
  have := dist_le_of_le_geometric_two_of_tendsto (key n t ht)
    ((tendsto_add_atTop_iff_nat n).2 (hL t)) m
  rw [Real.dist_eq] at this
  refine this.trans (le_of_eq ?_)
  rw [pow_add, one_div, inv_pow, inv_pow]
  field_simp

/-- Under the bound of `exists_lim_of_geom`, the limit of continuous functions is continuous
(the convergence is uniform on every `(-∞, n]`). -/
lemma continuous_of_geom {F : ℕ → ℝ → ℝ} {C : ℝ} {L : ℝ → ℝ} (hF : ∀ k, Continuous (F k))
    (hb : ∀ n : ℕ, ∀ t : ℝ, t ≤ n → ∀ k : ℕ, n ≤ k → |F k t - L t| ≤ 2 * C * (1 / 2) ^ k) :
    Continuous L := by
  have hu : ∀ n : ℕ, TendstoUniformlyOn F L atTop (Set.Iic (n : ℝ)) := by
    intro n
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun k : ℕ => 2 * C * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (2 * C)
    filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_ge_atTop n] with k hk hkn t htn
    rw [Real.dist_eq, abs_sub_comm]
    exact (hb n t htn k hkn).trans_lt hk
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hc := (hu (⌈t⌉₊ + 1)).continuousOn
    (Eventually.frequently (Eventually.of_forall fun k => (hF k).continuousOn))
  exact hc.continuousAt (Iic_mem_nhds (by push_cast; linarith [Nat.le_ceil t]))

/-! ### Elementary integrals -/

variable {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ι → ℝ → Ω → ℝ}

/-- **Doob's inequality for the difference of two elementary integrals:**
`𝔼 sup_{[0,T]} (I(e) - I(e'))² ≤ 4 𝔼 ∫_0^T ∑ᵢ (eᵢ - e'ᵢ)²`, and the supremum is measurable. -/
lemma elemInt_sub_doob (hB : IsBrownianFamily 𝓖 B μ) (f g : ElemIntegrand 𝓖 ι) (T : ℝ) :
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((f.integral B t ω - g.integral B t ω) ^ 2)) μ ∧
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((f.integral B t ω - g.integral B t ω) ^ 2) ∂μ ≤
      4 * energy μ (fun i s ω => f.toFun i s ω - g.toFun i s ω) T := by
  set d : ElemIntegrand 𝓖 ι := f ++ QSSEPtoKPZ.ElemIntegrand.smul (-1) g
  have hI : ∀ t ω, f.integral B t ω - g.integral B t ω = d.integral B t ω := by
    intro t ω
    simp only [d, QSSEPtoKPZ.ElemIntegrand.integral_append,
      QSSEPtoKPZ.ElemIntegrand.integral_smul]
    ring
  have hF : (fun i s ω => f.toFun i s ω - g.toFun i s ω) = d.toFun := by
    funext i s ω
    simp only [d, QSSEPtoKPZ.ElemIntegrand.toFun_append, QSSEPtoKPZ.ElemIntegrand.toFun_smul]
    ring
  simp only [hI, hF]
  have := (QSSEPtoKPZ.ElemIntegrand.hasBracket_integral hB d T).toIsCL2Mart.lintegral_iSup_sq_le
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  rw [QSSEPtoKPZ.ElemIntegrand.lintegral_integral_sq hB d T]

/-- The elementary integral, as a function of a real time, is continuous almost surely. -/
lemma elemInt_continuous_real (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) :
    ∀ᵐ ω ∂μ, Continuous fun t : ℝ => e.integral B t ω := by
  filter_upwards [QSSEPtoKPZ.ElemIntegrand.integral_continuous hB e] with ω hc
  have : (fun t : ℝ => e.integral B t ω) =
      (fun t : ℝ≥0 => e.integral B t ω) ∘ Real.toNNReal := by
    funext t
    rcases le_total t 0 with ht | ht
    · simp [QSSEPtoKPZ.ElemIntegrand.integral_of_nonpos _ B ht, Real.toNNReal_of_nonpos ht,
        QSSEPtoKPZ.ElemIntegrand.integral_of_nonpos _ B (le_refl (0 : ℝ))]
    · simp [Real.coe_toNNReal t ht]
  rw [this]
  exact hc.comp continuous_real_toNNReal

set_option linter.deprecated false in
/-- Wrapper of the deprecated `AEMeasurable.ennreal_tsum`. -/
lemma aemeasurable_tsum_ennreal {α : Type*} [MeasurableSpace α] {ν : Measure α} {κ : Type*}
    [Countable κ] {f : κ → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) ν) :
    AEMeasurable (fun x => ∑' i, f i x) ν :=
  AEMeasurable.ennreal_tsum hf

lemma four_pow_mul_inv_eight_pow (k : ℕ) :
    (4 : ℝ≥0∞) ^ k * (8 : ℝ≥0∞)⁻¹ ^ k = (2 : ℝ≥0∞)⁻¹ ^ k := by
  rw [← mul_pow]
  congr 1
  rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, ENNReal.mul_inv (Or.inl (by norm_num))
    (Or.inl (by norm_num)), ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
    one_mul]

/-- **Pathwise convergence along a fast sequence.** If
`𝔼 ∫_0^k ∑ᵢ (e_{k+1,i} - e_{k,i})² ≤ 4 · 8⁻ᵏ` for all `k`, then almost surely there is a
continuous `L` with `I_t(e_k) → L(t)` for every real `t`. -/
theorem elemInt_ae_tendsto (hB : IsBrownianFamily 𝓖 B μ) (e : ℕ → ElemIntegrand 𝓖 ι)
    (he : ∀ k : ℕ, energy μ (fun i s ω => (e (k + 1)).toFun i s ω - (e k).toFun i s ω) k ≤
      4 * (8 : ℝ≥0∞)⁻¹ ^ k) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ → ℝ, Continuous L ∧
      ∀ t, Tendsto (fun k => (e k).integral B t ω) atTop (𝓝 (L t)) := by
  set D : ℕ → Ω → ℝ≥0∞ := fun k ω => ⨆ t ∈ Set.Icc (0 : ℝ) k,
    ENNReal.ofReal (((e (k + 1)).integral B t ω - (e k).integral B t ω) ^ 2) with hDdef
  have hD : ∀ k, AEMeasurable (D k) μ ∧ ∫⁻ ω, D k ω ∂μ ≤ 4 * (4 * (8 : ℝ≥0∞)⁻¹ ^ k) :=
    fun k => let h := elemInt_sub_doob hB (e (k + 1)) (e k) k
      ⟨h.1, h.2.trans (by gcongr; exact he k)⟩
  have hS : ∫⁻ ω, ∑' k, (4 : ℝ≥0∞) ^ k * D k ω ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => (hD k).1.const_mul _]
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, 16 * (2 : ℝ≥0∞)⁻¹ ^ k) ?_
      (ENNReal.tsum_le_tsum fun k => ?_)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      norm_num
    · rw [lintegral_const_mul' _ _ (by finiteness)]
      calc (4 : ℝ≥0∞) ^ k * ∫⁻ ω, D k ω ∂μ ≤ 4 ^ k * (4 * (4 * (8 : ℝ≥0∞)⁻¹ ^ k)) := by
            gcongr; exact (hD k).2
        _ = 16 * ((4 : ℝ≥0∞) ^ k * (8 : ℝ≥0∞)⁻¹ ^ k) := by ring
        _ = 16 * (2 : ℝ≥0∞)⁻¹ ^ k := by rw [four_pow_mul_inv_eight_pow]
  have hfin := ae_lt_top' (aemeasurable_tsum_ennreal fun k => (hD k).1.const_mul _) hS
  have hcont := ae_all_iff.2 fun k => elemInt_continuous_real hB (e k)
  filter_upwards [hfin, hcont] with ω hω hc
  set S := ∑' k, (4 : ℝ≥0∞) ^ k * D k ω
  have hb : ∀ (k : ℕ) (t : ℝ), t ≤ k →
      |(e (k + 1)).integral B t ω - (e k).integral B t ω| ≤ √S.toReal * (1 / 2) ^ k := by
    intro k t htk
    rcases lt_or_ge t 0 with ht | ht
    · rw [QSSEPtoKPZ.ElemIntegrand.integral_of_nonpos _ B ht.le,
        QSSEPtoKPZ.ElemIntegrand.integral_of_nonpos _ B ht.le, sub_self, abs_zero]
      positivity
    set Δ := (e (k + 1)).integral B t ω - (e k).integral B t ω
    have h1 : ENNReal.ofReal (Δ ^ 2) ≤ D k ω :=
      le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) k) =>
        ENNReal.ofReal (((e (k + 1)).integral B t ω - (e k).integral B t ω) ^ 2)) t ⟨ht, htk⟩
    have h2 : (4 : ℝ≥0∞) ^ k * D k ω ≤ S :=
      ENNReal.le_tsum (f := fun k => (4 : ℝ≥0∞) ^ k * D k ω) k
    have h4k : (4 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have h4k' : (4 : ℝ≥0∞) ^ k ≠ ∞ := by finiteness
    have h3 : ENNReal.ofReal (Δ ^ 2) ≤ ENNReal.ofReal (S.toReal * (1 / 4) ^ k) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω.ne]
      calc ENNReal.ofReal (Δ ^ 2) ≤ D k ω := h1
        _ = ((4 : ℝ≥0∞) ^ k)⁻¹ * ((4 : ℝ≥0∞) ^ k * D k ω) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h4k h4k', one_mul]
        _ ≤ ((4 : ℝ≥0∞) ^ k)⁻¹ * S := by gcongr
        _ = S * ENNReal.ofReal ((1 / 4) ^ k) := by
          rw [mul_comm, ENNReal.ofReal_pow (by norm_num), one_div,
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.inv_pow]
          norm_num
    have h4 : Δ ^ 2 ≤ S.toReal * (1 / 4) ^ k :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    calc |Δ| ≤ √(S.toReal * (1 / 4) ^ k) := Real.abs_le_sqrt h4
      _ = √S.toReal * (1 / 2) ^ k := by
        rw [Real.sqrt_mul ENNReal.toReal_nonneg,
          show ((1 : ℝ) / 4) ^ k = ((1 / 2) ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
          Real.sqrt_sq (by positivity)]
  obtain ⟨L, hL, hbL⟩ := exists_lim_of_geom (F := fun k t => (e k).integral B t ω) hb
  exact ⟨L, continuous_of_geom hc hbL, hL⟩

end StochIntAux

end QSSEPtoKPZ
