/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.LocalP
public import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Conservation of the mass for a good version of the wave function (task D2)

See `docs/stage2-design.md`, Section 1.2 (f). Let `ψ̃` be a good version of the wave function
(`IsGoodWave`) and `τ = τ_R ∧ N`. By `IsGoodWave.isItoProcessUpTo_boxMass`, almost surely,
for all `K ∈ ℕ`,
`∑_{|x| ≤ K} P(t∧τ, x) = 1 + ∫_0^{t∧τ} (P(K+1) - P(K) + P(-K-1) - P(-K)) ds + I_t(h_K)`,
with `h_K = (c_{-K-1} - c_K) 𝟙_{[0,τ]}`. As `K → ∞`:

* the left side tends to `‖ψ̃_{t∧τ}‖²` and the flux term tends to `0`, pathwise (dominated
  convergence; all `P(s,y) ≤ (max R 1)²` before `τ`);
* `𝔼[I_t(h_K)²] = 𝔼 ∫_0^{t∧τ} 2 (P(-K-1)P(-K) + P(K)P(K+1)) ds → 0` (Itô isometry and dominated
  convergence, twice).

By Fatou's lemma, `‖ψ̃_{t∧τ}‖² = 1` almost surely (`IsGoodWave.ae_norm_sq_stopped`). With
`R = 2`, path continuity gives `τ_2 ∧ N = N`, whence `IsGoodWave.ae_norm_eq_one`: almost surely,
`‖ψ̃_t‖ = 1` for all `t ≥ 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Paths -/

/-- A function continuous on `[0, ∞)` (as a function of `t : ℝ≥0`) is continuous on `Ici 0`, as
a function on `ℝ`. -/
lemma wavePath_continuousOn {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) : ContinuousOn f (Set.Ici 0) :=
  (hf.comp continuous_real_toNNReal).continuousOn.congr fun r hr => by
    simp [Real.coe_toNNReal _ (Set.mem_Ici.1 hr)]

/-- A function continuous on `[0, ∞)` (as a function of `t : ℝ≥0`) is continuous at every
`s > 0`, as a function on `ℝ`. -/
lemma wavePath_continuousAt {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) {s : ℝ} (hs : 0 < s) : ContinuousAt f s := by
  have h1 : ContinuousAt (fun r : ℝ => f (r.toNNReal : ℝ)) s :=
    (hf.comp continuous_real_toNNReal).continuousAt
  refine h1.congr ?_
  filter_upwards [eventually_gt_nhds hs] with r hr
  simp [Real.coe_toNNReal _ hr.le]

/-- `P(s, g(K)) → 0` as `K → ∞`, along any injective `g : ℕ → ℤ` (the density is summable). -/
lemma tendsto_density_comp_injective (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) {g : ℕ → ℤ}
    (hg : Function.Injective g) : Tendsto (fun K => density ψ ω s (g K)) atTop (𝓝 0) := by
  have hs : Summable fun x => density ψ ω s x := by
    have := (lp.memℓp (ψ s ω)).summable (p := 2) (by norm_num)
    simpa [density, Real.rpow_two] using this
  rw [← Nat.cofinite_eq_atTop]
  exact hs.tendsto_cofinite_zero.comp hg.tendsto_cofinite

/-- `∑_x P(t,x) = ‖ψ_t‖²`, as the limit of the sums over the boxes `|x| ≤ K`. -/
lemma tendsto_sum_Icc_density (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) :
    Tendsto (fun K : ℕ => ∑ x ∈ Finset.Icc (-(K : ℤ)) K, density ψ ω s x) atTop
      (𝓝 (‖ψ s ω‖ ^ 2)) := by
  have hsum := lp.hasSum_norm (p := 2) (by norm_num) (ψ s ω)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hsum
  exact hsum.comp Finset.tendsto_Icc_neg

/-- `HasSum (P(t,·)) ‖ψ_t‖²`. -/
lemma hasSum_density_norm_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) :
    HasSum (density ψ ω s) (‖ψ s ω‖ ^ 2) := by
  have hsum := lp.hasSum_norm (p := 2) (by norm_num) (ψ s ω)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hsum
  exact hsum

/-! ### Conservation of the mass -/

variable {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

omit [IsProbabilityMeasure μ] in
/-- `∑_{|x| ≤ K} P(0,x) = 1`. -/
lemma IsGoodWave.sum_Icc_density_zero (hg : IsGoodWave 𝓕 B ψ ψ' μ) (ω : Ω) (K : ℕ) :
    ∑ x ∈ Finset.Icc (-(K : ℤ)) K, density ψ' ω 0 x = 1 := by
  have : ∀ x, density ψ' ω 0 x = if x = 0 then 1 else 0 := fun x => by
    rw [density, hg.init_apply ω x]; split_ifs <;> simp
  simp only [this, Finset.sum_ite_eq', Finset.mem_Icc]
  simp

omit [IsProbabilityMeasure μ] in
/-- The bound `2 P(a) P(a+1) + 2 P(b) P(b+1) ≤ 4 M⁴` before `τ_R ∧ N`, `M = max R 1`. -/
private lemma massLim_bound (hg : IsGoodWave 𝓕 B ψ ψ' μ) {R : ℝ} {N : ℝ≥0} {ω : Ω} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ waveStop ψ' R N ω) (a b : ℤ) :
    2 * density ψ' ω s a * density ψ' ω s (a + 1) + 2 * density ψ' ω s b * density ψ' ω s (b + 1)
      ≤ 4 * max R 1 ^ 4 := by
  have h := fun y => hg.density_le_of_le_waveStop hs0 hs y
  have hn : ∀ y, 0 ≤ density ψ' ω s y := fun y => sq_nonneg _
  have h1 := mul_le_mul (h a) (h (a + 1)) (hn _) (sq_nonneg _)
  have h2 := mul_le_mul (h b) (h (b + 1)) (hn _) (sq_nonneg _)
  have e : max R 1 ^ 4 = max R 1 ^ 2 * max R 1 ^ 2 := by ring
  rw [e]
  nlinarith

/-- **Mass at `t ∧ τ_R ∧ N`.** For a good version `ψ'`, every `R`, `N` and `t ≥ 0`, almost
surely `‖ψ'_{t∧τ}‖² = 1`, `τ = τ_R ∧ N`. -/
theorem IsGoodWave.ae_norm_sq_stopped (hB : IsBrownianFamily 𝓕 B μ)
    (hg : IsGoodWave 𝓕 B ψ ψ' μ) (R : ℝ) (N t : ℝ≥0) :
    ∀ᵐ ω ∂μ, ‖ψ' (min t (waveStop ψ' R N ω) : ℝ≥0) ω‖ ^ 2 = 1 := by
  set τ := waveStop ψ' R N with hτdef
  set M := max R 1 with hMdef
  have hbox := fun K : ℕ => hg.isItoProcessUpTo_boxMass hB R N K
  set h : ℕ → ℤ × Fin 2 → ℝ → Ω → ℝ := fun K i s ω =>
    if s ≤ τ ω then waveCurrent ψ' (-K - 1) i s ω - waveCurrent ψ' K i s ω else 0 with hhdef
  have hhI : ∀ K, IsItoIntegrable (nullAug μ 𝓕) μ (h K) := fun K => (hbox K).integrable
  set I : ℕ → Ω → ℝ := fun K ω => stochInt (nullAug μ 𝓕) μ B (h K) t ω with hIdef
  set D : ℕ → Ω → ℝ := fun K ω => ∫ s in (0 : ℝ)..((min t (τ ω) : ℝ≥0) : ℝ),
    (density ψ' ω s (K + 1) - density ψ' ω s K +
      (density ψ' ω s (-K - 1) - density ψ' ω s (-K))) with hDdef
  set S : ℕ → Ω → ℝ := fun K ω =>
    ∑ x ∈ Finset.Icc (-(K : ℤ)) K, density ψ' ω (min t (τ ω) : ℝ≥0) x with hSdef
  -- (1) the identity on the boxes, for all `K`, almost surely
  have h1 : ∀ᵐ ω ∂μ, ∀ K : ℕ, S K ω = 1 + D K ω + I K ω := by
    rw [ae_all_iff]
    intro K
    filter_upwards [(hbox K).eq] with ω hω
    have e := hω t
    simp only [hg.sum_Icc_density_zero ω K] at e
    exact e
  -- (2) pathwise limits
  have hS : ∀ ω, Tendsto (fun K => S K ω) atTop
      (𝓝 (‖ψ' (min t (τ ω) : ℝ≥0) ω‖ ^ 2)) := fun ω =>
    tendsto_sum_Icc_density ψ' ω _
  have hinj1 : Function.Injective fun K : ℕ => (K : ℤ) + 1 := fun a b e => by
    simpa using e
  have hinj2 : Function.Injective fun K : ℕ => (K : ℤ) := Nat.cast_injective
  have hinj3 : Function.Injective fun K : ℕ => -(K : ℤ) - 1 := fun a b e => by
    simp only at e; omega
  have hinj4 : Function.Injective fun K : ℕ => -(K : ℤ) := fun a b e => by
    simp only at e; omega
  have hD : ∀ ω, Tendsto (fun K => D K ω) atTop (𝓝 0) := by
    intro ω
    set b : ℝ := ((min t (τ ω) : ℝ≥0) : ℝ) with hb
    have hb0 : 0 ≤ b := NNReal.coe_nonneg _
    have hbτ : b ≤ τ ω := NNReal.coe_le_coe.2 (min_le_right _ _)
    have hcont : ∀ y : ℤ, ContinuousOn (fun s => density ψ' ω s y) (Set.Ici 0) := fun y =>
      ((wavePath_continuousOn (hg.continuous_apply ω y)).norm).pow 2
    have hsub : Set.uIoc 0 b ⊆ Set.Ici 0 := by
      rw [Set.uIoc_of_le hb0]; exact fun s hs => le_of_lt hs.1
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := 0) (b := b) (f := fun _ => (0 : ℝ)) (l := atTop)
      (F := fun (K : ℕ) s => density ψ' ω s (K + 1) - density ψ' ω s K +
        (density ψ' ω s (-K - 1) - density ψ' ω s (-K))) (fun _ => 4 * M ^ 2)
      (Eventually.of_forall fun K => ((((hcont _).sub (hcont _)).add
        ((hcont _).sub (hcont _))).mono hsub).aestronglyMeasurable measurableSet_uIoc)
      (Eventually.of_forall fun K => ae_of_all _ fun s hs => ?_) intervalIntegrable_const
      (ae_of_all _ fun s hs => ?_)
    · simpa using this
    · rw [Set.uIoc_of_le hb0] at hs
      have hs0 : 0 ≤ s := hs.1.le
      have hsτ : s ≤ τ ω := hs.2.trans hbτ
      have h := fun y => hg.density_le_of_le_waveStop hs0 hsτ y
      have hn : ∀ y, 0 ≤ density ψ' ω s y := fun y => sq_nonneg _
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h (K + 1), h K, h (-K - 1), h (-K), hn (K + 1), hn K,
        hn (-K - 1), hn (-K)]
    · have := ((tendsto_density_comp_injective ψ' ω s hinj1).sub
        (tendsto_density_comp_injective ψ' ω s hinj2)).add
        ((tendsto_density_comp_injective ψ' ω s hinj3).sub
          (tendsto_density_comp_injective ψ' ω s hinj4))
      simpa using this
  -- (3) the energies tend to `0`
  set G : ℕ → ℝ → Ω → ℝ≥0∞ := fun K s ω => (Set.Iic (τ ω : ℝ)).indicator (fun s =>
    ENNReal.ofReal (2 * density ψ' ω s (-K - 1) * density ψ' ω s (-K - 1 + 1) +
      2 * density ψ' ω s K * density ψ' ω s (K + 1))) s with hGdef
  have hG : ∀ K s ω, ∑' i, ‖h K i s ω‖ₑ ^ 2 = G K s ω := by
    intro K s ω
    by_cases hs : s ≤ τ ω
    · simp only [hhdef, hs, ite_true, hGdef, Set.indicator_of_mem (Set.mem_Iic.2 hs)]
      simp_rw [StochIntAux.enorm_sq_eq]
      have hsum : Summable fun i =>
          (waveCurrent ψ' (-K - 1) i s ω - waveCurrent ψ' K i s ω) ^ 2 :=
        ((summable_waveCurrent_mul ψ' (-K - 1) (fun i => waveCurrent ψ' (-K - 1) i s ω -
          waveCurrent ψ' K i s ω) s ω).sub (summable_waveCurrent_mul ψ' K
            (fun i => waveCurrent ψ' (-K - 1) i s ω - waveCurrent ψ' K i s ω) s ω)).congr
          fun i => by ring
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsum,
        tsum_waveCurrent_sub_sq ψ' (by omega : -(K : ℤ) - 1 ≠ K)]
    · simp [hhdef, hs, hGdef]
  have hGb : ∀ K ω, ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      G K s ω ≤ ENNReal.ofReal (4 * M ^ 4) := by
    intro K ω
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    by_cases hsτ : s ≤ τ ω
    · simp only [hGdef, Set.indicator_of_mem (Set.mem_Iic.2 hsτ)]
      exact ENNReal.ofReal_le_ofReal (massLim_bound hg hs.1.le hsτ _ _)
    · simp [hGdef, Set.indicator_of_notMem (show s ∉ Set.Iic (τ ω : ℝ) from hsτ)]
  have hfin : ∫⁻ _ in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (4 * M ^ 4) ≠ ∞ := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpe : ∀ K ω, pathEnergy (h K) t ω = ∫⁻ s in Set.Ioc (0 : ℝ) t, G K s ω :=
    fun K ω => lintegral_congr fun s => hG K s ω
  have hinner : ∀ ω, Tendsto (fun K => ∫⁻ s in Set.Ioc (0 : ℝ) t, G K s ω) atTop (𝓝 0) := by
    intro ω
    have hcont : ∀ y : ℤ, ContinuousOn (fun s => density ψ' ω s y) (Set.Ici 0) := fun y =>
      ((wavePath_continuousOn (hg.continuous_apply ω y)).norm).pow 2
    have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ici 0 := fun s hs => le_of_lt hs.1
    have := tendsto_lintegral_of_dominated_convergence' (μ := volume.restrict (Set.Ioc (0 : ℝ) t))
      (F := fun K s => G K s ω) (f := fun _ => 0) (fun _ => ENNReal.ofReal (4 * M ^ 4))
      (fun K => ?_) (fun K => hGb K ω) hfin (ae_of_all _ fun s => ?_)
    · simpa using this
    · refine AEMeasurable.indicator ?_ measurableSet_Iic
      refine ContinuousOn.aemeasurable ?_ measurableSet_Ioc
      exact (ENNReal.continuous_ofReal.comp_continuousOn
        ((((continuousOn_const.mul (hcont _)).mul (hcont _))).add
          ((continuousOn_const.mul (hcont _)).mul (hcont _)))).mono hsub
    · by_cases hsτ : s ≤ τ ω
      · simp only [hGdef, Set.indicator_of_mem (Set.mem_Iic.2 hsτ)]
        have hinj5 : Function.Injective fun K : ℕ => -(K : ℤ) - 1 + 1 := fun a b e => by
          simp only at e; omega
        have := ((tendsto_const_nhds (x := (2 : ℝ))).mul
          (tendsto_density_comp_injective ψ' ω s hinj3)).mul
          (tendsto_density_comp_injective ψ' ω s hinj5) |>.add
          (((tendsto_const_nhds (x := (2 : ℝ))).mul
          (tendsto_density_comp_injective ψ' ω s hinj2)).mul
          (tendsto_density_comp_injective ψ' ω s hinj1))
        simpa using ENNReal.tendsto_ofReal this
      · simp [hGdef, Set.indicator_of_notMem (show s ∉ Set.Iic (τ ω : ℝ) from hsτ)]
  have hE : Tendsto (fun K => energy μ (h K) t) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun K ω => pathEnergy (h K) t ω) (f := fun _ => 0)
      (fun _ => ∫⁻ _ in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (4 * M ^ 4))
      (fun K => StochIntAux.measurable_pathEnergy (hhI K).meas t)
      (fun K => ae_of_all _ fun ω => by simp only [hpe]; exact lintegral_mono_ae (hGb K ω))
      (by rw [lintegral_const, measure_univ, mul_one]; exact hfin)
      (ae_of_all _ fun ω => by simp only [hpe]; exact hinner ω)
    simpa [energy] using this
  -- (4) Fatou's lemma
  have hIm : ∀ K, Measurable (I K) := fun K =>
    (stochInt_adapted hB.nullAug (h K) t).mono ((nullAug μ 𝓕).le t) le_rfl
  have hF := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun K ω => ENNReal.ofReal (I K ω ^ 2)) fun K => ((hIm K).pow_const 2).ennreal_ofReal
  have hI2 : (fun K => ∫⁻ ω, ENNReal.ofReal (I K ω ^ 2) ∂μ) = fun K => energy μ (h K) t :=
    funext fun K => lintegral_stochInt_sq hB.nullAug (hhI K) t
  rw [hI2, hE.liminf_eq] at hF
  have hmeas : Measurable fun ω => liminf (fun K => ENNReal.ofReal (I K ω ^ 2)) atTop :=
    Measurable.liminf fun K => ((hIm K).pow_const 2).ennreal_ofReal
  have h0 := (lintegral_eq_zero_iff hmeas).1 (le_antisymm hF zero_le)
  filter_upwards [h0, h1] with ω hω h1ω
  have hIt : Tendsto (fun K => I K ω) atTop
      (𝓝 (‖ψ' (min t (τ ω) : ℝ≥0) ω‖ ^ 2 - 1 - 0)) :=
    (((hS ω).sub_const 1).sub (hD ω)).congr fun K => by rw [h1ω K]; ring
  have hlim := ENNReal.tendsto_ofReal (hIt.pow 2)
  rw [hlim.liminf_eq] at hω
  have hL := ENNReal.ofReal_eq_zero.1 hω
  have hL' : ‖ψ' (min t (τ ω) : ℝ≥0) ω‖ ^ 2 - 1 - 0 = 0 :=
    pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hL (sq_nonneg _))
  linarith

/-- **Conservation of the mass for a good version.** Almost surely, `‖ψ'_t‖ = 1` for all
`t ≥ 0`. (With `R = 2`: `‖ψ'_{t∧τ}‖ = 1` for all `t` by continuity, so the path never reaches
`2` before `N` and `τ_2 ∧ N = N`; then let `N → ∞` along `ℕ`.) -/
theorem IsGoodWave.ae_norm_eq_one (hB : IsBrownianFamily 𝓕 B μ)
    (hg : IsGoodWave 𝓕 B ψ ψ' μ) : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ‖ψ' t ω‖ = 1 := by
  -- for each `N`, almost surely, `‖ψ'_{t∧τ}‖² = 1` for all `t`
  have hN : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      ‖ψ' (min t (waveStop ψ' 2 N ω) : ℝ≥0) ω‖ ^ 2 = 1 := by
    intro N
    have := StochIntAux.ae_forall_eq_of_continuous (μ := μ)
      (X := fun t ω => ‖ψ' (min t.toNNReal (waveStop ψ' 2 N ω) : ℝ≥0) ω‖ ^ 2)
      (Y := fun _ _ => 1) (ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => continuous_const)
      fun t => ?_
    · filter_upwards [this] with ω hω t
      simpa using hω t
    · simp only [Real.toNNReal_coe]
      exact ((hg.continuous ω).comp (continuous_id.min continuous_const)).norm.pow 2
    · filter_upwards [hg.ae_norm_sq_stopped hB 2 N t] with ω hω
      simpa using hω
  filter_upwards [ae_all_iff.2 hN] with ω hω t
  -- `τ_2 ∧ N = N` for every `N`
  have hstop : ∀ N : ℕ, waveStop ψ' 2 N ω = N := by
    intro N
    set τ := waveStop ψ' 2 N ω with hτ
    by_contra hne
    have hlt : τ < N := lt_of_le_of_ne (waveStop_le ψ' 2 N ω) hne
    set A : Set ℝ≥0 := {s | (2 : ℝ) ≤ ‖ψ' s ω‖} ∪ {(N : ℝ≥0)} with hA
    have hAc : IsClosed A :=
      (isClosed_le continuous_const (hg.continuous_norm ω)).union isClosed_singleton
    have hτA : τ = sInf A := by
      have : τ = sInf A ⊓ N := rfl
      rw [this] at hlt ⊢
      exact inf_eq_left.2 (le_of_lt (lt_of_not_ge fun h => absurd hlt (by
        rw [inf_eq_right.2 h]; exact lt_irrefl _)))
    have hmem : sInf A ∈ A := hAc.csInf_mem ⟨N, Or.inr rfl⟩ (OrderBot.bddBelow _)
    rw [← hτA] at hmem
    rcases hmem with h2 | h2
    · have h1 := hω N τ
      rw [min_self] at h1
      have h0 : ‖ψ' τ ω‖ = 1 := by
        have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero) |>.1 h1
        exact this
      simp only [Set.mem_ofPred_eq] at h2
      linarith
    · exact absurd h2 (ne_of_lt hlt)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, t ≤ N := ⟨⌈(t : ℝ)⌉₊, by
    rw [← NNReal.coe_le_coe]; push_cast; exact Nat.le_ceil _⟩
  have h1 := hω N t
  rw [hstop N, min_eq_left hN] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero) |>.1 h1

end QSSEPtoKPZ
