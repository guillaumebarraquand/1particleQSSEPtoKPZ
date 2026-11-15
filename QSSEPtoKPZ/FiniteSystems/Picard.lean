/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.PicardIter
public import QSSEPtoKPZ.FiniteSystems.PicardLimit

/-!
# Strong existence of the wave function, every `L` (task L2b)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L2b.
`docs/stage5-design.md`, Section 1.2 (a).

* `exists_isWaveIto`: on any filtered space carrying a Brownian family, for every
  `L ∈ ℕ ∪ {∞}` and every initial condition `ψ₀ ∈ ℓ²` supported in `Λ_L`, there is an Itô
  solution (`IsWaveIto`) for the augmented filtration, with `𝔼 sup_{t ≤ T} ‖ψ_t‖² < ∞`. (The
  Picard iterates of `PicardIter.lean` converge almost surely uniformly on `[0,T]` in `ℓ²`;
  the limit is modified on a measurable null set.)
* `picard_isWaveFunction`: the case `ψ₀ = e₀` with `IsWaveIto.isWaveFunction`. It has the
  statement of `prop_2_1_existence` (`FiniteSystems/Statements.lean`), which quotes it.

Proof (task L2b): iterating `picard_step_bound` gives
`𝔼 sup_{[0,n]} ‖φ⁽ᵏ⁺¹⁾ - φ⁽ᵏ⁾‖² ≤ d₀ (Cn)^k / k!`, so `W_n = ∑_k 2^k sup_{[0,n]} ‖φ⁽ᵏ⁺¹⁾ - φ⁽ᵏ⁾‖²`
is integrable; by Cauchy–Schwarz `sup_{[0,n]} ‖φ⁽ᵖ⁾ - φ⁽ᵐ⁾‖² ≤ 2 (1/2)^m W_n` (`m ≤ p`), whence
a.s. uniform convergence on compacts and `𝔼 sup_{[0,n]} ‖ψ - φ⁽ᵐ⁾‖² ≤ 2 (1/2)^m 𝔼 W_n`. Applying
`picard_step_bound` once more to `ψ` and `φ⁽ᵐ⁾` shows that `ψ` coincides a.s. with an admissible
version of its Picard image (this replaces `tendsto_lintegral_iSup_stochInt_sub`), and the fixed
point equation gives the Itô form (stopping at constant times, `stochInt_indicator_stoppingTime`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-! ### Auxiliary results (task L2b) -/

/-- `ω ↦ sup_{t ∈ [0,n]} ‖X_t(ω) - Y_t(ω)‖²` is measurable for adapted processes with continuous
`ℓ²` paths. -/
private lemma picardEx_measurable_sup {𝓖 : Filtration ℝ≥0 mΩ} {X Y : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hXa : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => X t ω x)
    (hYa : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => Y t ω x)
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hYc : ∀ ω, Continuous fun t : ℝ≥0 => Y t ω)
    {n : ℝ} (hn : 0 ≤ n) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖X t ω - Y t ω‖ ^ 2) := by
  have ha : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => (X t ω - Y t ω) x := fun t x => by
    simp only [lp.coeFn_sub, Pi.sub_apply]
    exact (hXa t x).sub (hYa t x)
  exact picardEx_measurable_iSup (X := fun t ω => X t ω - Y t ω)
    (fun t => (measurable_norm_of_adapted (ψ := fun t ω => X t ω - Y t ω) ha t).mono
      (𝓖.le t) le_rfl)
    (fun ω => (hXc ω).sub (hYc ω)) hn

/-- **Summability of the Picard increments.** For the Picard iterates,
`𝔼 ∑_k 2^k sup_{s ∈ [0,n]} ‖φ⁽ᵏ⁺¹⁾_s - φ⁽ᵏ⁾_s‖² < ∞` (iterated contraction estimate:
`𝔼 sup_{[0,n]} ‖φ⁽ᵏ⁺¹⁾ - φ⁽ᵏ⁾‖² ≤ d_0 (Cn)^k / k!`). -/
private lemma picardEx_lintegral_W_lt_top [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {φ : ℕ → ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadm : ∀ m, IsPicardAdmissible L (nullAug μ 𝓕) ψ0 (φ m) μ)
    (h0 : ∀ t ω, φ 0 t ω = ψ0)
    (hstep : ∀ m, ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ),
        φ (m + 1) t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 (φ m) t ω x) (n : ℕ) :
    ∫⁻ ω, (∑' k, (2 : ℝ≥0∞) ^ k *
      ⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖φ (k + 1) s ω - φ k s ω‖ ^ 2)) ∂μ < ⊤ := by
  set d : ℕ → ℝ → ℝ≥0∞ := fun k t => ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t,
    ENNReal.ofReal (‖φ (k + 1) s ω - φ k s ω‖ ^ 2)) ∂μ with hd
  have hC : (0 : ℝ) ≤ 16 + 2 * n := by positivity
  have hg := picardEx_gronwall (d := d) (C := 16 + 2 * n) (T := n) hC
    (fun t ht => lintegral_mono fun ω => biSup_mono fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
    (fun k t ht => picard_step_bound hB (hadm (k + 1)) (hadm k) (hstep (k + 1)) (hstep k)
      ht.1 ht.2)
  have hd0 : d 0 n < ⊤ := by
    have hpt : ∀ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n,
        ENNReal.ofReal (‖φ (0 + 1) s ω - φ 0 s ω‖ ^ 2)) ≤
        2 * (⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖φ 1 s ω‖ ^ 2)) +
          2 * ENNReal.ofReal (‖ψ0‖ ^ 2) := by
      intro ω
      refine iSup₂_le fun s hs => ?_
      rw [h0 s ω]
      refine (picardEx_ofReal_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (norm_sub_le _ _)).trans ?_
      gcongr
      exact le_iSup₂_of_le (f := fun s _ => ENNReal.ofReal (‖φ 1 s ω‖ ^ 2)) s hs le_rfl
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) ((hadm 1).moment n),
      ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top⟩
  have hmeas : ∀ k, Measurable fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) n,
      ENNReal.ofReal (‖φ (k + 1) s ω - φ k s ω‖ ^ 2) := fun k =>
    picardEx_measurable_sup (hadm (k + 1)).adapted (hadm k).adapted (hadm (k + 1)).continuous
      (hadm k).continuous n.cast_nonneg
  rw [lintegral_tsum fun k => ((hmeas k).const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ (hmeas _)]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_)
    (picardEx_tsum_lt_top hd0 hC n.cast_nonneg)
  gcongr
  exact hg k n ⟨n.cast_nonneg, le_rfl⟩

/-- **The limit of the Picard iterates.** There are Picard iterates `φ⁽ᵐ⁾` and an admissible
process `ψ` with `𝔼 sup_{s ∈ [0,n]} ‖ψ_s - φ⁽ᵐ⁾_s‖² ≤ 2 (1/2)^m K_n`, `K_n < ∞` (`ψ` is the a.s.
uniform limit on compacts, put equal to `ψ₀` on a measurable null set). -/
private lemma picardEx_limit [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞)
    (ψ0 : ℓ²(ℤ, ℂ)) (hψ0 : ∀ x, x ∉ box L → ψ0 x = 0) :
    ∃ (φ : ℕ → ℝ → Ω → ℓ²(ℤ, ℂ)) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)),
      (∀ m, IsPicardAdmissible L (nullAug μ 𝓕) ψ0 (φ m) μ) ∧
      (∀ m, ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ),
        φ (m + 1) t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 (φ m) t ω x) ∧
      IsPicardAdmissible L (nullAug μ 𝓕) ψ0 ψ μ ∧
      ∀ n : ℕ, ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ m, ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n,
        ENNReal.ofReal (‖ψ s ω - φ m s ω‖ ^ 2)) ∂μ ≤ ENNReal.ofReal (2 * (1 / 2) ^ m) * K := by
  classical
  obtain ⟨φ, hadm, h0, hstep⟩ := picard_iterates hB L ψ0 hψ0
  set 𝓖 := nullAug μ 𝓕 with h𝓖
  set W : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑' k, (2 : ℝ≥0∞) ^ k *
      ⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖φ (k + 1) s ω - φ k s ω‖ ^ 2) with hW
  have hWint : ∀ n, ∫⁻ ω, W n ω ∂μ < ⊤ := picardEx_lintegral_W_lt_top hB hadm h0 hstep
  have hWm : ∀ n : ℕ, Measurable (W n) := fun n => Measurable.tsum fun k =>
    (picardEx_measurable_sup (hadm (k + 1)).adapted (hadm k).adapted (hadm (k + 1)).continuous
      (hadm k).continuous n.cast_nonneg).const_mul _
  have hWfin : ∀ᵐ ω ∂μ, ∀ n : ℕ, W n ω < ⊤ :=
    ae_all_iff.2 fun n => ae_lt_top (hWm n) (hWint n).ne
  -- the Cauchy bound
  have hcau : ∀ ω (n : ℕ), W n ω < ⊤ → ∀ m p, m ≤ p → ∀ s ∈ Set.Icc (0 : ℝ) n,
      ‖φ p s ω - φ m s ω‖ ^ 2 ≤ 2 * (1 / 2) ^ m * (W n ω).toReal := by
    intro ω n hWn m p hmp s hs
    have h : ENNReal.ofReal (‖φ p s ω - φ m s ω‖ ^ 2) ≤
        ENNReal.ofReal (2 * (1 / 2) ^ m) * W n ω :=
      picardEx_sq_norm_sub_le (f := fun k => φ k s ω)
        (u := fun k => ⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖φ (k + 1) s ω - φ k s ω‖ ^ 2))
        (fun k => le_iSup₂_of_le (f := fun s _ => ENNReal.ofReal (‖φ (k + 1) s ω - φ k s ω‖ ^ 2))
          s hs le_rfl) hmp
    rw [← ENNReal.ofReal_toReal hWn.ne, ← ENNReal.ofReal_mul (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  -- the null set
  set N := toMeasurable μ {ω | ∀ n : ℕ, W n ω < ⊤}ᶜ with hNdef
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hWfin
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNG : ∀ ω, ω ∉ N → ∀ n : ℕ, W n ω < ⊤ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hNt : ∀ t, MeasurableSet[𝓖 t] N := fun t =>
    nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0)
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the limit
  set ψ : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω =>
    if ω ∈ N then ψ0 else limUnder atTop fun m => φ m t ω with hψdef
  have hψN : ∀ t ω, ω ∈ N → ψ t ω = ψ0 := fun t ω h => by simp [hψdef, h]
  have hψG : ∀ t ω, ω ∉ N → ψ t ω = limUnder atTop fun m => φ m t ω := fun t ω h => by
    simp [hψdef, h]
  have hU : ∀ ω, ω ∉ N → ∀ n : ℕ, _ := fun ω hω (n : ℕ) =>
    picardEx_uniform (f := fun m (t : ℝ≥0) => φ m t ω) (S := Set.Iic (n : ℝ≥0))
      (c := (W n ω).toReal) fun m p hmp a ha =>
        hcau ω n (hNG ω hω n) m p hmp a ⟨a.2, by exact_mod_cast ha⟩
  have hlimT : ∀ ω, ω ∉ N → ∀ t : ℝ≥0, Tendsto (fun m => φ m t ω) atTop (𝓝 (ψ t ω)) := by
    intro ω hω t
    rw [hψG _ _ hω]
    exact (hU ω hω ⌈(t : ℝ)⌉₊).1 t (by
      rw [Set.mem_Iic, ← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _)
  have hbd : ∀ ω, ω ∉ N → ∀ (n : ℕ) m, ∀ s ∈ Set.Icc (0 : ℝ) n,
      ENNReal.ofReal (‖ψ s ω - φ m s ω‖ ^ 2) ≤ ENNReal.ofReal (2 * (1 / 2) ^ m) * W n ω := by
    intro ω hω n m s hs
    have h := (hU ω hω n).2.2 m s.toNNReal (by
      rw [Set.mem_Iic, ← NNReal.coe_le_coe, NNReal.coe_natCast, Real.coe_toNNReal _ hs.1]
      exact hs.2)
    rw [Real.coe_toNNReal _ hs.1, ← hψG _ _ hω] at h
    rw [← ENNReal.ofReal_toReal (hNG ω hω n).ne, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h
  have hψadm : IsPicardAdmissible L 𝓖 ψ0 ψ μ := by
    refine ⟨fun t x => ?_, fun ω => ?_, fun ω t x hx => ?_, fun ω => ?_, fun T => ?_⟩
    · -- adapted
      refine @measurable_of_tendsto_metrizable Ω ℂ (𝓖 t) _ _ _ _
        (fun m ω => if ω ∈ N then ψ0 x else φ m t ω x) _
        (fun m => Measurable.ite (hNt t) measurable_const ((hadm m).adapted t x))
        (tendsto_pi_nhds.2 fun ω => ?_)
      by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte, hψN _ _ hω]
        exact tendsto_const_nhds
      · simp only [hω, ↓reduceIte]
        exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.tendsto _).comp (hlimT ω hω t)
    · -- continuous
      by_cases hω : ω ∈ N
      · have : (fun t : ℝ≥0 => ψ t ω) = fun _ => ψ0 := funext fun t => hψN _ _ hω
        rw [this]
        exact continuous_const
      · rw [continuous_iff_continuousAt]
        intro t
        obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
        have hc := (hU ω hω n).2.1.continuousOn
          (Eventually.of_forall fun m => ((hadm m).continuous ω).continuousOn).frequently
        have e : (fun t : ℝ≥0 => ψ t ω) = fun t : ℝ≥0 => limUnder atTop fun m => φ m t ω :=
          funext fun t => hψG _ _ hω
        rw [e]
        exact hc.continuousAt (Iic_mem_nhds (by exact_mod_cast hn))
    · -- support
      by_cases hω : ω ∈ N
      · rw [hψN _ _ hω]; exact hψ0 x hx
      · have h1 := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.tendsto _).comp
          (hlimT ω hω t)
        have h2 : (fun m => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x) (φ m t ω)) = fun _ => 0 :=
          funext fun m => (hadm m).support ω t x hx
        exact tendsto_nhds_unique h1 (by rw [Function.comp_def, h2]; exact tendsto_const_nhds)
    · -- init
      by_cases hω : ω ∈ N
      · exact hψN _ _ hω
      · have h1 := hlimT ω hω 0
        simp only [NNReal.coe_zero, (hadm _).init ω] at h1
        exact tendsto_nhds_unique h1 tendsto_const_nhds
    · -- moment
      set n := ⌈T⌉₊
      have hpt : ∀ᵐ ω ∂μ, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖ψ t ω‖ ^ 2)) ≤
          2 * (ENNReal.ofReal (2 * (1 / 2) ^ 0) * W n ω) + 2 * ENNReal.ofReal (‖ψ0‖ ^ 2) := by
        filter_upwards [hNae] with ω hω
        refine iSup₂_le fun s hs => ?_
        have hs' : s ∈ Set.Icc (0 : ℝ) n := ⟨hs.1, hs.2.trans (Nat.le_ceil T)⟩
        refine (picardEx_ofReal_sq_le (norm_nonneg (ψ s ω - φ 0 s ω)) (norm_nonneg ψ0)
          (norm_nonneg _) ?_).trans ?_
        · calc ‖ψ s ω‖ ≤ ‖ψ s ω - φ 0 s ω‖ + ‖φ 0 s ω‖ := norm_le_norm_sub_add _ _
            _ = _ := by rw [h0 s ω]
        · gcongr
          exact hbd ω hω n 0 s hs'
      refine (lintegral_mono_ae hpt).trans_lt ?_
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hWint n)),
        ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top⟩
  refine ⟨φ, ψ, hadm, hstep, hψadm, fun n => ⟨∫⁻ ω, W n ω ∂μ, hWint n, fun m => ?_⟩⟩
  rw [← lintegral_const_mul _ (hWm n)]
  refine lintegral_mono_ae ?_
  filter_upwards [hNae] with ω hω
  exact iSup₂_le fun s hs => hbd ω hω n m s hs

/-- **The limit is a fixed point of the Picard map.** There is an admissible process `ψ` with
`ψ_t(x) = Φ(ψ)_t(x)` for all `t ≥ 0`, `x`, almost surely: with `ψ'` an admissible version of
`Φ(ψ)`, the contraction estimate gives `𝔼 sup_{[0,n]} ‖ψ' - φ⁽ᵐ⁺¹⁾‖² → 0`, hence
`𝔼 sup_{[0,n]} ‖ψ - ψ'‖² = 0`. -/
private lemma picardEx_fixed [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞)
    (ψ0 : ℓ²(ℤ, ℂ)) (hψ0 : ∀ x, x ∉ box L → ψ0 x = 0) :
    ∃ ψ : ℝ → Ω → ℓ²(ℤ, ℂ), IsPicardAdmissible L (nullAug μ 𝓕) ψ0 ψ μ ∧
      ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ),
        ψ t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 ψ t ω x := by
  obtain ⟨φ, ψ, hadm, hstep, hψ, hK⟩ := picardEx_limit hB L ψ0 hψ0
  obtain ⟨ψ', hψ', hψ'eq⟩ := picard_step_exists hB hψ0 hψ
  have hmeas : ∀ n : ℕ, Measurable fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) n,
      ENNReal.ofReal (‖ψ s ω - ψ' s ω‖ ^ 2) := fun n =>
    picardEx_measurable_sup hψ.adapted hψ'.adapted hψ.continuous hψ'.continuous n.cast_nonneg
  have hzero : ∀ n : ℕ, ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n,
      ENNReal.ofReal (‖ψ s ω - ψ' s ω‖ ^ 2)) ∂μ = 0 := by
    intro n
    obtain ⟨K, hKt, hbd⟩ := hK n
    set K' : ℝ≥0∞ := 2 * K + 2 * (ENNReal.ofReal (16 + 2 * n) * (K * ENNReal.ofReal n))
      with hK'def
    have hK' : K' < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hKt,
      ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top hKt ENNReal.ofReal_lt_top))⟩
    have hle : ∀ m, ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n,
        ENNReal.ofReal (‖ψ s ω - ψ' s ω‖ ^ 2)) ∂μ ≤ ENNReal.ofReal (2 * (1 / 2) ^ m) * K' := by
      intro m
      have h2 := picard_step_bound hB hψ (hadm m) hψ'eq (hstep m) (t := n) (T := n)
        n.cast_nonneg le_rfl
      have h3 : ∫⁻ s in Set.Icc (0 : ℝ) n, ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ) s,
          ENNReal.ofReal (‖ψ u ω - φ m u ω‖ ^ 2)) ∂μ ≤
          ENNReal.ofReal (2 * (1 / 2) ^ m) * K * ENNReal.ofReal n := by
        calc _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) n, ENNReal.ofReal (2 * (1 / 2) ^ m) * K :=
              setLIntegral_mono' measurableSet_Icc fun s hs =>
                (lintegral_mono fun ω => biSup_mono fun u hu => ⟨hu.1, hu.2.trans hs.2⟩).trans
                  (hbd m)
          _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
      have hpt : ∀ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖ψ s ω - ψ' s ω‖ ^ 2)) ≤
          2 * (⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖ψ s ω - φ (m + 1) s ω‖ ^ 2)) +
          2 * (⨆ s ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖ψ' s ω - φ (m + 1) s ω‖ ^ 2)) := by
        intro ω
        refine iSup₂_le fun s hs => ?_
        refine (picardEx_ofReal_sq_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) ?_).trans
          (add_le_add (mul_le_mul' le_rfl (le_iSup₂_of_le (f := fun s _ =>
            ENNReal.ofReal (‖ψ s ω - φ (m + 1) s ω‖ ^ 2)) s hs le_rfl))
            (mul_le_mul' le_rfl (le_iSup₂_of_le (f := fun s _ =>
            ENNReal.ofReal (‖ψ' s ω - φ (m + 1) s ω‖ ^ 2)) s hs le_rfl)))
        rw [norm_sub_rev (ψ' s ω)]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      have hm1 : Measurable fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) n,
          ENNReal.ofReal (‖ψ s ω - φ (m + 1) s ω‖ ^ 2) :=
        picardEx_measurable_sup hψ.adapted (hadm (m + 1)).adapted hψ.continuous
          (hadm (m + 1)).continuous n.cast_nonneg
      have hpow' : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2) ^ m :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
      have hpow : ENNReal.ofReal (2 * (1 / 2) ^ (m + 1)) ≤ ENNReal.ofReal (2 * (1 / 2) ^ m) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      calc _ ≤ _ := lintegral_mono hpt
        _ = 2 * ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n,
              ENNReal.ofReal (‖ψ s ω - φ (m + 1) s ω‖ ^ 2)) ∂μ +
            2 * ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) n,
              ENNReal.ofReal (‖ψ' s ω - φ (m + 1) s ω‖ ^ 2)) ∂μ := by
          rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * (ENNReal.ofReal (2 * (1 / 2) ^ m) * K) +
            2 * (ENNReal.ofReal (16 + 2 * n) *
              (ENNReal.ofReal (2 * (1 / 2) ^ m) * K * ENNReal.ofReal n)) := by
          gcongr
          · exact (hbd (m + 1)).trans (mul_le_mul' hpow le_rfl)
          · exact h2.trans (mul_le_mul' le_rfl h3)
        _ = ENNReal.ofReal (2 * (1 / 2) ^ m) * K' := by rw [hK'def]; ring
    have ht : Tendsto (fun m : ℕ => ENNReal.ofReal (2 * (1 / 2) ^ m) * K') atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => 2 * (1 / 2 : ℝ) ^ m) atTop (𝓝 (2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
      rw [mul_zero] at h1
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hK'.ne)
      rwa [ENNReal.ofReal_zero, zero_mul] at h2
    exact nonpos_iff_eq_zero.1 (ge_of_tendsto' ht hle)
  have hae : ∀ᵐ ω ∂μ, ∀ n : ℕ, (⨆ s ∈ Set.Icc (0 : ℝ) n,
      ENNReal.ofReal (‖ψ s ω - ψ' s ω‖ ^ 2)) = 0 :=
    ae_all_iff.2 fun n => (lintegral_eq_zero_iff (hmeas n)).1 (hzero n)
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hae, hψ'eq] with ω h1 h2 t x
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hle : ENNReal.ofReal (‖ψ t ω - ψ' t ω‖ ^ 2) ≤ 0 := by
    rw [← h1 n]
    exact le_iSup₂_of_le (f := fun s _ => ENNReal.ofReal (‖ψ s ω - ψ' s ω‖ ^ 2)) (t : ℝ)
      ⟨t.2, hn⟩ le_rfl
  have heq : ψ t ω = ψ' t ω := by
    rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    have h3 : ‖ψ t ω - ψ' t ω‖ = 0 := by nlinarith [norm_nonneg (ψ t ω - ψ' t ω)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  rw [heq]
  exact h2 t x

/-- **A fixed point of the Picard map is an Itô solution.** If `ψ` is admissible and
`ψ = Φ(ψ)` almost surely, then `ψ` is an Itô solution (`IsWaveIto`) for `𝓕ᵃ`. -/
private lemma picardEx_isWaveIto [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {L : ℕ∞} {ψ0 : ℓ²(ℤ, ℂ)} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hψ : IsPicardAdmissible L (nullAug μ 𝓕) ψ0 ψ μ)
    (hfix : ∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ),
      ψ t ω x = picardCoord (nullAug μ 𝓕) μ B L ψ0 ψ t ω x) :
    IsWaveIto L (nullAug μ 𝓕) B ψ0 ψ μ := by
  have hB' := hB.nullAug
  have hτ : ∀ N : ℝ≥0, IsStoppingTime (nullAug μ 𝓕) (fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0)) :=
    fun N => isStoppingTime_const _ _
  have hD : ∀ x, ((degree L x : ℂ) / 2) = (((degree L x : ℝ) / 2 : ℝ) : ℂ) := fun x => by
    push_cast; ring
  have hii : ∀ ω x (u : ℝ≥0), IntervalIntegrable (fun s => ψ s ω x) volume 0 u :=
    fun ω x u => picardBd_intervalIntegrable (hψ.continuous ω) x u.2
  have hcu : ∀ ω x (N : ℝ≥0), ContinuousOn (fun s => ψ s ω x) (Set.uIcc 0 (N : ℝ)) := by
    intro ω x N
    refine (picardBd_continuousOn (hψ.continuous ω) x).mono ?_
    rw [Set.uIcc_of_le (NNReal.coe_nonneg N)]
    exact Set.Icc_subset_Ici_self
  refine ⟨hψ.adapted, hψ.continuous, hψ.support, hψ.init, fun x hx N => ⟨?_, ?_, ?_⟩,
    fun x hx N => ⟨?_, ?_, ?_⟩⟩
  · exact (hψ.isItoIntegrable_re x).indicator_stoppingTime (hτ N)
  · exact ae_of_all _ fun ω =>
      ((Complex.continuous_re.comp_continuousOn (hcu ω x N)).intervalIntegrable).const_mul _
  · filter_upwards [hfix, stochInt_indicator_stoppingTime hB' (hψ.isItoIntegrable_re x) (hτ N)]
      with ω h1 h2 t
    rw [h2 t, h1 (min t N) x, hψ.init ω]
    have hre : (∫ s in (0 : ℝ)..((min t N : ℝ≥0) : ℝ), (ψ s ω x).re) =
        (∫ s in (0 : ℝ)..((min t N : ℝ≥0) : ℝ), ψ s ω x).re :=
      Complex.reCLM.intervalIntegral_comp_comm (hii ω x _)
    simp only [picardCoord, hx, ↓reduceIte, hD, intervalIntegral.integral_const_mul, hre,
      Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  · exact (hψ.isItoIntegrable_im x).indicator_stoppingTime (hτ N)
  · exact ae_of_all _ fun ω =>
      ((Complex.continuous_im.comp_continuousOn (hcu ω x N)).intervalIntegrable).const_mul _
  · filter_upwards [hfix, stochInt_indicator_stoppingTime hB' (hψ.isItoIntegrable_im x) (hτ N)]
      with ω h1 h2 t
    rw [h2 t, h1 (min t N) x, hψ.init ω]
    have him : (∫ s in (0 : ℝ)..((min t N : ℝ≥0) : ℝ), (ψ s ω x).im) =
        (∫ s in (0 : ℝ)..((min t N : ℝ≥0) : ℝ), ψ s ω x).im :=
      Complex.imCLM.intervalIntegral_comp_comm (hii ω x _)
    simp only [picardCoord, hx, ↓reduceIte, hD, intervalIntegral.integral_const_mul, him,
      Complex.add_im, Complex.sub_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring

/-- **Strong existence in Itô form** (Picard iteration). For every `L ∈ ℕ ∪ {∞}` and every
`ψ₀ ∈ ℓ²(ℤ)` vanishing outside `Λ_L`, there is an Itô solution of the wave equation on `Λ_L`
with initial condition `ψ₀`, driven by `B`, for the augmented filtration `𝓕ᵃ = nullAug μ 𝓕`,
with `𝔼 sup_{t ∈ [0,T]} ‖ψ_t‖² < ∞` for every `T`. -/
theorem exists_isWaveIto [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞)
    (ψ0 : ℓ²(ℤ, ℂ)) (hψ0 : ∀ x, x ∉ box L → ψ0 x = 0) :
    ∃ ψ : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveIto L (nullAug μ 𝓕) B ψ0 ψ μ ∧
      ∀ T : ℝ, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖ψ t ω‖ ^ 2)) ∂μ < ⊤ := by
  obtain ⟨ψ, hψ, hfix⟩ := picardEx_fixed hB L ψ0 hψ0
  exact ⟨ψ, picardEx_isWaveIto hB hψ hfix, hψ.moment⟩

/-- Twin of `prop_2_1_existence` (Proposition 2.1, existence; same statement): on any filtered
space carrying a Brownian family, there is a wave function on `Λ_L` driven by it, for the
augmented filtration. From `exists_isWaveIto` with `ψ₀ = e₀` and `IsWaveIto.isWaveFunction`. -/
theorem picard_isWaveFunction (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞) :
    ∃ ψ : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveFunction L (nullAug μ 𝓕) B ψ μ := by
  have := hB.isProbabilityMeasure
  obtain ⟨ψ, hψ, -⟩ := exists_isWaveIto hB L waveInit fun x hx => by
    rw [waveInit_apply, ite_eq_right_iff]
    rintro rfl
    exact absurd (by simp [box]) hx
  exact ⟨ψ, hψ.isWaveFunction hB.nullAug⟩

end QSSEPtoKPZ
