/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Product

/-!
# Itô processes up to a constant time: congruence and limits (task D4)

Two general facts on `IsItoProcessUpTo 𝓖 μ B (fun _ => N) X a b` (an Itô process up to the
deterministic time `N`), used to pass from finite boxes of `ℤ` to all of `ℤ`:

* `IsItoProcessUpTo.congr_const`: only the values of `X`, `a` on `[0, N]` and of `b` on
  `(-∞, N]` matter.
* `IsItoProcessUpTo.of_tendsto_const`: if `X_K = X_K(0) + ∫ a_K ds + ∫ b_K dB` up to `N` for
  every `K`, and, as `K → ∞`, `X_K(t) → Y(t)` and `∫_0^t a_K → ∫_0^t c` pathwise for `t ∈ [0, N]`
  (almost surely), and `b_K 𝟙_{[0,N]} → d 𝟙_{[0,N]}` for the energy `𝔼 ∫_0^N ∑ᵢ (·)² ds`, then
  `Y = Y(0) + ∫ c ds + ∫ d dB` up to `N`. (Doob's inequality makes the stochastic integrals
  converge uniformly on `[0, N]` along a subsequence, almost surely.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {B : ι → ℝ → Ω → ℝ}

omit [Countable ι] in
/-- **Congruence** for Itô processes up to a constant time `N`: only the values of the process
and of the drift on `[0, N]`, and of the diffusion at times `s ≤ N`, matter. -/
theorem IsItoProcessUpTo.congr_const {N : ℝ≥0} {X X' a a' : ℝ → Ω → ℝ}
    {b b' : ι → ℝ → Ω → ℝ} (h : IsItoProcessUpTo 𝓖 μ B (fun _ => N) X a b)
    (hX : ∀ ω (t : ℝ), 0 ≤ t → t ≤ N → X' t ω = X t ω)
    (ha : ∀ ω (s : ℝ), 0 ≤ s → s ≤ N → a' s ω = a s ω)
    (hb : ∀ i (s : ℝ) ω, s ≤ N → b' i s ω = b i s ω) :
    IsItoProcessUpTo 𝓖 μ B (fun _ => N) X' a' b' := by
  have hbe : (fun i (s : ℝ) ω => if s ≤ (N : ℝ) then b' i s ω else 0) =
      fun i s ω => if s ≤ (N : ℝ) then b i s ω else 0 := by
    funext i s ω
    split_ifs with hs
    · exact hb i s ω hs
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · have := h.integrable
    rwa [hbe]
  · filter_upwards [h.drift] with ω hω
    refine hω.congr_ae (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_)
    rw [Set.uIoc_of_le (NNReal.coe_nonneg N)] at hs
    exact (ha ω s hs.1.le hs.2).symm
  · filter_upwards [h.eq] with ω hω t
    have e := hω t
    have hm0 : (0 : ℝ) ≤ ((min t N : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hmN : ((min t N : ℝ≥0) : ℝ) ≤ N := NNReal.coe_le_coe.2 (min_le_right _ _)
    rw [hX ω _ hm0 hmN, hX ω 0 le_rfl (NNReal.coe_nonneg N), e, hbe]
    congr 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hm0] at hs
    exact (ha ω s hs.1 (hs.2.trans hmN)).symm

omit [Countable ι] in
/-- If `f` vanishes at times `s > N`, its energy on `[0, T]` is at most its energy on `[0, N]`. -/
lemma itoLimit_energy_le_of_vanish {f : ι → ℝ → Ω → ℝ} {N : ℝ}
    (hf : ∀ i s ω, N < s → f i s ω = 0) (T : ℝ) : energy μ f T ≤ energy μ f N := by
  refine lintegral_mono fun ω => ?_
  unfold pathEnergy
  calc ∫⁻ s in Set.Ioc 0 T, ∑' i, ‖f i s ω‖ₑ ^ 2
      ≤ ∫⁻ s in Set.Ioc 0 N ∪ Set.Ioi N, ∑' i, ‖f i s ω‖ₑ ^ 2 :=
        lintegral_mono_set fun s hs => by
          rcases le_or_gt s N with h | h
          · exact Or.inl ⟨hs.1, h⟩
          · exact Or.inr h
    _ ≤ (∫⁻ s in Set.Ioc 0 N, ∑' i, ‖f i s ω‖ₑ ^ 2) +
          ∫⁻ s in Set.Ioi N, ∑' i, ‖f i s ω‖ₑ ^ 2 := lintegral_union_le _ _ _
    _ = ∫⁻ s in Set.Ioc 0 N, ∑' i, ‖f i s ω‖ₑ ^ 2 := by
        rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun s hs => by
          simp [hf _ s ω hs]]
        simp

/-- From `∫⁻ Φ_K → 0` (with `Φ_K` almost everywhere measurable), a subsequence `Φ_{φ(n)}` tends
to `0` almost everywhere. -/
lemma itoLimit_exists_subseq_ae [IsFiniteMeasure μ] {Φ : ℕ → Ω → ℝ≥0∞}
    (hm : ∀ K, AEMeasurable (Φ K) μ) (h : Tendsto (fun K => ∫⁻ ω, Φ K ω ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => Φ (φ n) ω) atTop (𝓝 0) := by
  have hev : ∀ n : ℕ, ∀ᶠ K in atTop, ∫⁻ ω, Φ K ω ∂μ ≤ (2⁻¹ : ℝ≥0∞) ^ n := fun n =>
    h.eventually (ge_mem_nhds (ENNReal.pow_pos (by norm_num) n))
  obtain ⟨φ, hφ, hφn⟩ := extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hsum : ∫⁻ ω, ∑' n, Φ (φ n) ω ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun n => hm _]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφn)
    rw [ENNReal.tsum_geometric]
    norm_num
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun n => hm (φ n)) hsum] with ω hω
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne

/-- If `ofReal (x_n²) → 0` then `x_n → 0`. -/
lemma itoLimit_tendsto_of_ofReal_sq {x : ℕ → ℝ}
    (h : Tendsto (fun n => ENNReal.ofReal (x n ^ 2)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => x n ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h2 : Tendsto (fun n => Real.sqrt (x n ^ 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h1
  simp only [Real.sqrt_sq_eq_abs] at h2
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 h2

variable [IsProbabilityMeasure μ]

/-- **Limits of Itô processes up to a constant time `N`.** Let
`X_K = X_K(0) + ∫ a_K ds + ∫ b_K dB` up to `N` for every `K ∈ ℕ`. Assume that, almost surely,
`X_K(t) → Y(t)` and `∫_0^t a_K → ∫_0^t c` for all `t ∈ [0, N]`, that `c` is integrable on
`[0, N]`, that `d 𝟙_{[0,N]}` is jointly measurable, and that `b_K 𝟙_{[0,N]} → d 𝟙_{[0,N]}` for
the energy on `[0, N]`. Then `Y = Y(0) + ∫ c ds + ∫ d dB` up to `N`. -/
theorem IsItoProcessUpTo.of_tendsto_const (hB : IsBrownianFamily 𝓖 B μ) {N : ℝ≥0}
    {X a : ℕ → ℝ → Ω → ℝ} {b : ℕ → ι → ℝ → Ω → ℝ} {Y c : ℝ → Ω → ℝ} {d : ι → ℝ → Ω → ℝ}
    (hX : ∀ K, IsItoProcessUpTo 𝓖 μ B (fun _ => N) (X K) (a K) (b K))
    (hdm : ∀ i, Measurable fun p : ℝ × Ω =>
      if 0 < p.1 then (if p.1 ≤ (N : ℝ) then d i p.1 p.2 else 0) else 0)
    (hE : Tendsto (fun K => energy μ (fun i s ω => (if s ≤ (N : ℝ) then b K i s ω else 0) -
      (if s ≤ (N : ℝ) then d i s ω else 0)) N) atTop (𝓝 0))
    (hc : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => c s ω) volume 0 N)
    (hXl : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → t ≤ N →
      Tendsto (fun K => X K t ω) atTop (𝓝 (Y t ω)))
    (hal : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → t ≤ N →
      Tendsto (fun K => ∫ s in (0 : ℝ)..t, a K s ω) atTop (𝓝 (∫ s in (0 : ℝ)..t, c s ω))) :
    IsItoProcessUpTo 𝓖 μ B (fun _ => N) Y c d := by
  set h : ℕ → ι → ℝ → Ω → ℝ := fun K i s ω => if s ≤ (N : ℝ) then b K i s ω else 0 with hhdef
  set g : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ (N : ℝ) then d i s ω else 0 with hgdef
  have hhI : ∀ K, IsItoIntegrable 𝓖 μ (h K) := fun K => (hX K).integrable
  have hvan : ∀ K i s ω, (N : ℝ) < s → h K i s ω - g i s ω = 0 := fun K i s ω hs => by
    simp [hhdef, hgdef, not_le.2 hs]
  have hET : ∀ T : ℝ, Tendsto (fun K => energy μ (fun i s ω => h K i s ω - g i s ω) T) atTop
      (𝓝 0) := fun T =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE (fun _ => zero_le)
      fun K => itoLimit_energy_le_of_vanish (hvan K) T
  have hgI : IsItoIntegrable 𝓖 μ g := IsItoIntegrable.of_tendsto hhI hdm hET
  -- the differences `h_K - g`
  have e : ∀ K, (fun i s ω => h K i s ω + (-1) * g i s ω) = fun i s ω => h K i s ω - g i s ω :=
    fun K => by funext i s ω; ring
  have hkI : ∀ K, IsItoIntegrable 𝓖 μ (fun i s ω => h K i s ω - g i s ω) := fun K => by
    have := (hhI K).add (hgI.const_mul (-1))
    rwa [e K] at this
  have hlin : ∀ K, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (h K) t ω =
      stochInt 𝓖 μ B (fun i s ω => h K i s ω - g i s ω) t ω + stochInt 𝓖 μ B g t ω :=
    fun K => by
    have h1 := stochInt_add hB (hhI K) (hgI.const_mul (-1)) (B := B)
    rw [e K] at h1
    filter_upwards [h1, stochInt_const_mul hB hgI (-1)] with ω h1 h2 t
    rw [h1 t, h2 t]
    ring
  -- Doob: `𝔼 sup_{t ≤ N} I_t(h_K - g)² → 0`
  set Φ : ℕ → Ω → ℝ≥0∞ := fun K ω => ⨆ t ∈ Set.Icc (0 : ℝ) N,
    ENNReal.ofReal (stochInt 𝓖 μ B (fun i s ω => h K i s ω - g i s ω) t ω ^ 2) with hΦdef
  have hΦm : ∀ K, AEMeasurable (Φ K) μ := fun K =>
    ((hasBracket_stochInt hB (hkI K) N).toIsCL2Mart.lintegral_iSup_sq_le).1
  have hΦ : Tendsto (fun K => ∫⁻ ω, Φ K ω ∂μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun K => 4 * energy μ (fun i s ω => h K i s ω - g i s ω) N)
      (by simpa using ENNReal.Tendsto.const_mul hE (Or.inr (by norm_num)))
      (fun _ => zero_le) fun K => lintegral_iSup_stochInt_sq_le hB (hkI K) N
  obtain ⟨φ, hφ, hφae⟩ := itoLimit_exists_subseq_ae hΦm hΦ
  have hgstop := stochInt_indicator_stoppingTime hB hgI (τ := fun _ => N)
    (isStoppingTime_const _ N)
  have hgg : (fun i (s : ℝ) ω => if s ≤ (N : ℝ) then g i s ω else 0) = g := by
    funext i s ω
    by_cases hs : s ≤ (N : ℝ) <;> simp [hgdef, hs]
  refine ⟨hgI, hc, ?_⟩
  filter_upwards [hφae, ae_all_iff.2 fun K => (hX K).eq, ae_all_iff.2 hlin, hXl, hal,
    hgstop] with ω hω hXω hlinω hXlω halω hstopω t
  set t' : ℝ≥0 := min t N with ht'
  have ht'N : t' ≤ N := min_le_right _ _
  have ht'0 : (0 : ℝ) ≤ t' := NNReal.coe_nonneg _
  have ht'N' : (t' : ℝ) ≤ N := NNReal.coe_le_coe.2 ht'N
  -- the stochastic integrals at `t'` converge along `φ`
  have hI : Tendsto (fun n => stochInt 𝓖 μ B (fun i s ω => h (φ n) i s ω - g i s ω) t' ω)
      atTop (𝓝 0) := by
    refine itoLimit_tendsto_of_ofReal_sq (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hω (fun _ => zero_le) fun n => ?_)
    exact le_iSup₂ (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) N) => ENNReal.ofReal
      (stochInt 𝓖 μ B (fun i s ω => h (φ n) i s ω - g i s ω) t ω ^ 2)) (t' : ℝ) ⟨ht'0, ht'N'⟩
  -- the identity at `t'` for each `K`
  have hK : ∀ K, X K t' ω = X K 0 ω + (∫ s in (0 : ℝ)..t', a K s ω) +
      (stochInt 𝓖 μ B (fun i s ω => h K i s ω - g i s ω) t' ω + stochInt 𝓖 μ B g t' ω) := by
    intro K
    have e1 := hXω K t'
    rw [min_eq_left ht'N] at e1
    rw [e1, ← hlinω K t']
  have hlim : Tendsto (fun n => X (φ n) t' ω) atTop
      (𝓝 (Y 0 ω + (∫ s in (0 : ℝ)..t', c s ω) + (0 + stochInt 𝓖 μ B g t' ω))) := by
    have h0 := (hXlω 0 le_rfl (NNReal.coe_nonneg N)).comp hφ.tendsto_atTop
    have h1 := (halω t' ht'0 ht'N').comp hφ.tendsto_atTop
    refine ((h0.add h1).add (hI.add tendsto_const_nhds)).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hK (φ n)]
  have hY := tendsto_nhds_unique ((hXlω t' ht'0 ht'N').comp hφ.tendsto_atTop) hlim
  have hs := hstopω t
  rw [hgg] at hs
  change _ = _ + stochInt 𝓖 μ B g t ω
  rw [hY, hs]
  ring

end QSSEPtoKPZ
