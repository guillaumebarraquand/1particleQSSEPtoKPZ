/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.ProductAux

/-!
# Martingale properties of Walsh integral processes (task G9)

Auxiliary results for `WhiteNoise/WalshProcess.lean`. For a white noise `ξ` and a Walsh integral
`X = ∫ h dξ`:

* `walshProc_split`: for every `s`, the integral `X' = ∫ 𝟙_{r ≤ s} h dξ` exists, is
  `𝒢_s`-measurable up to a null set, and `W (X - X') = ∫ W 𝟙_{r > s} h dξ` for every bounded
  `𝒢_s`-measurable `W` (induction on the definition of `IsWalshIntegral`).
* For the integrals `Y_t = ∫ 𝟙_{0 < r ≤ t} g dξ`: `Y_t` is `𝒢_t`-measurable up to a null set
  (`walshProc_aestronglyMeasurable`), `𝔼[Y_t | 𝒢_s] = Y_s` (`walshProc_condExp`), and the
  conditional isometry `𝔼[𝟙_B (Y_t - Y_s)(Y'_t - Y'_s)] = 𝔼 ∫∫ 𝟙_B 𝟙_{s < r ≤ t} g g'` for
  `B ∈ 𝒢_s` (`walshProc_setIntegral_mul`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- An almost everywhere limit of functions which are almost everywhere equal to
`m`-measurable functions is almost everywhere equal to an `m`-measurable function. -/
theorem walshProc_aesm_of_tendsto_ae {Ω : Type*} {m mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable[m] (f n) ν)
    (hlim : ∀ᵐ ω ∂ν, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    AEStronglyMeasurable[m] g ν := by
  choose g' hg' hfg using hf
  have hall : ∀ᵐ ω ∂ν, ∀ n, f n ω = g' n ω := ae_all_iff.2 hfg
  refine ⟨fun ω => limUnder atTop (fun n => g' n ω),
    @StronglyMeasurable.limUnder ℕ Ω ℝ m _ _ atTop _ g' _ _ hg', ?_⟩
  filter_upwards [hall, hlim] with ω h1 h2
  exact (h2.congr h1).limUnder_eq.symm

/-- The same for limits in `L²`. -/
theorem walshProc_aesm_of_tendsto_L2 {Ω : Type*} {m mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable[m] (f n) ν)
    (hlim : Tendsto (fun n => eLpNorm (f n - g) 2 ν) atTop (𝓝 0)) :
    AEStronglyMeasurable[m] g ν := by
  obtain ⟨ns, -, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hlim).exists_seq_tendsto_ae
  exact walshProc_aesm_of_tendsto_ae (fun n => hf (ns n)) hns

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- Product of two bounded functions. -/
private lemma walshProc_bdd_mul {W c : Ω → ℝ} (hW : ∃ C, ∀ ω, |W ω| ≤ C)
    (hc : ∃ C, ∀ ω, |c ω| ≤ C) : ∃ C, ∀ ω, |W ω * c ω| ≤ C := by
  obtain ⟨C, hC⟩ := hW
  obtain ⟨C', hC'⟩ := hc
  exact ⟨C * C', fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))⟩

/-- **Splitting a Walsh integral at time `s`**: if `X = ∫ h dξ`, then `X' = ∫ 𝟙_{r ≤ s} h dξ`
exists and is `𝒢_s`-measurable up to a null set, and for every bounded `𝒢_s`-measurable `W`,
`W (X - X') = ∫ W 𝟙_{r > s} h dξ`. -/
theorem walshProc_split (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) (s : ℝ≥0) :
    ∃ X' : Ω → ℝ, IsWalshIntegral 𝓖 S ν (fun r y ω => if r ≤ s then h r y ω else 0) X' ∧
      AEStronglyMeasurable[𝓖 s] X' ν ∧
      ∀ W : Ω → ℝ, Measurable[𝓖 s] W → (∃ C, ∀ ω, |W ω| ≤ C) →
        IsWalshIntegral 𝓖 S ν (fun r y ω => if (s : ℝ) < r then W ω * h r y ω else 0)
          (fun ω => W ω * (X ω - X' ω)) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hmem : ∀ {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}, IsWalshIntegral 𝓖 S ν h X →
      MemLp (uncurryField h) 2 (ν.prod volume) ∧ MemLp X 2 ν :=
    fun hX => ⟨(IsWalshIntegral.isometry_lib hS hX).1, (IsWalshIntegral.isometry_lib hS hX).2.1⟩
  induction hX with
  | block s₀ t₀ a b c hst hab hc hbdd =>
    rcases le_total s s₀ with hs | hs
    · have hs' : (s : ℝ) ≤ s₀ := by exact_mod_cast hs
      refine ⟨fun _ => 0, ?_, ⟨fun _ => 0, stronglyMeasurable_const, EventuallyEq.rfl⟩,
        fun W hW hWb => ?_⟩
      · convert IsWalshIntegral.zero 𝓖 S ν using 1
        funext r y ω
        rw [ite_eq_right_iff]
        intro _
        rw [ite_eq_right_iff]
        intro h2
        exfalso
        linarith [h2.1]
      · convert IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s₀ t₀ a b
          (fun ω => W ω * c ω) hst hab ((hW.mono (𝓖.mono hs) le_rfl).mul hc)
          (walshProc_bdd_mul hWb hbdd) using 1
        · funext r y ω
          by_cases h1 : (s₀ : ℝ) < r ∧ r ≤ t₀ ∧ a < y ∧ y ≤ b
          · have : (s : ℝ) < r := lt_of_le_of_lt hs' h1.1
            simp [h1, this]
          · simp [h1]
        · funext ω
          ring
    · have hs' : (s₀ : ℝ) ≤ s := by exact_mod_cast hs
      rcases le_total t₀ s with hts | hst'
      · have ht' : (t₀ : ℝ) ≤ s := by exact_mod_cast hts
        refine ⟨fun ω => c ω * rectMass S s₀ t₀ a b ω, ?_,
          ⟨_, ((hc.mono (𝓖.mono hs) le_rfl).mul
            (prodNoise_meas_rect hS hs hts a b)).stronglyMeasurable, EventuallyEq.rfl⟩,
          fun W hW hWb => ?_⟩
        · convert IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s₀ t₀ a b c hst hab hc
            hbdd using 1
          funext r y ω
          by_cases h1 : (s₀ : ℝ) < r ∧ r ≤ t₀ ∧ a < y ∧ y ≤ b
          · have : r ≤ (s : ℝ) := h1.2.1.trans ht'
            simp [h1, this]
          · simp [h1]
        · convert IsWalshIntegral.zero 𝓖 S ν using 1
          · funext r y ω
            rw [ite_eq_right_iff]
            intro h1
            have : ¬ ((s₀ : ℝ) < r ∧ r ≤ t₀ ∧ a < y ∧ y ≤ b) := fun h2 => by linarith [h2.2.1]
            simp [this]
          · funext ω
            simp
      · have ht' : (s : ℝ) ≤ t₀ := by exact_mod_cast hst'
        refine ⟨fun ω => c ω * rectMass S s₀ s a b ω, ?_,
          ⟨_, ((hc.mono (𝓖.mono hs) le_rfl).mul
            (prodNoise_meas_rect hS hs le_rfl a b)).stronglyMeasurable, EventuallyEq.rfl⟩,
          fun W hW hWb => ?_⟩
        · convert IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s₀ s a b c hs hab hc
            hbdd using 1
          funext r y ω
          by_cases h1 : r ≤ (s : ℝ)
          · have : r ≤ (t₀ : ℝ) := h1.trans ht'
            simp [h1, this]
          · simp [h1]
        · convert IsWalshIntegral.block (𝓖 := 𝓖) (S := S) (ν := ν) s t₀ a b
            (fun ω => W ω * c ω) hst' hab (hW.mul (hc.mono (𝓖.mono hs) le_rfl))
            (walshProc_bdd_mul hWb hbdd) using 1
          · funext r y ω
            by_cases h1 : (s : ℝ) < r
            · have : (s₀ : ℝ) < r := lt_of_le_of_lt hs' h1
              simp [h1, this]
            · simp [h1]
          · funext ω
            simp only [rectMass]
            ring
  | add h h' X X' hX hX' ih ih' =>
    obtain ⟨X₁, hX₁, hm₁, hW₁⟩ := ih
    obtain ⟨X₂, hX₂, hm₂, hW₂⟩ := ih'
    refine ⟨fun ω => X₁ ω + X₂ ω, ?_, hm₁.add hm₂, fun W hW hWb => ?_⟩
    · convert IsWalshIntegral.add _ _ _ _ hX₁ hX₂ using 1
      funext r y ω
      split_ifs <;> simp
    · convert IsWalshIntegral.add _ _ _ _ (hW₁ W hW hWb) (hW₂ W hW hWb) using 1
      · funext r y ω
        split_ifs <;> ring
      · funext ω
        ring
  | limit h X hs Xs hk h2 X2 hlim Xlim ih =>
    choose X' hX' hm' hW' using ih
    have hr : ∀ g : ℝ → ℝ → Ω → ℝ, uncurryField (fun r y ω => if r ≤ s then g r y ω else 0) =
        {p : Ω × ℝ × ℝ | p.2.1 ≤ s}.indicator (uncurryField g) := by
      intro g
      funext p
      simp only [uncurryField, Set.indicator, Set.mem_ofPred_eq]
    have hmeas : MeasurableSet {p : Ω × ℝ × ℝ | p.2.1 ≤ s} :=
      measurableSet_le (measurable_fst.comp measurable_snd) measurable_const
    have hr2 : MemLp (uncurryField (fun r y ω => if r ≤ s then h r y ω else 0)) 2
        (ν.prod volume) := by
      rw [hr]
      exact h2.indicator hmeas.nullMeasurableSet
    have hlim' : Tendsto (fun k => eLpNorm
        (uncurryField (fun r y ω => if r ≤ s then hs k r y ω else 0) -
          uncurryField (fun r y ω => if r ≤ s then h r y ω else 0)) 2 (ν.prod volume))
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => zero_le) fun k =>
          eLpNorm_mono ((IsWalshIntegral.isometry_lib hS (hX' k)).1.sub hr2).aestronglyMeasurable
            fun p => ?_
      simp only [hr, Pi.sub_apply, Set.indicator]
      split_ifs <;> simp
    obtain ⟨Y, hY, hYlim⟩ := IsWalshIntegral.exists_limit hS hX' hr2 hlim'
    refine ⟨Y, hY, walshProc_aesm_of_tendsto_L2 hm' hYlim, fun W hW hWb => ?_⟩
    obtain ⟨C, hC⟩ := hWb
    set C' := max C 0 with hC'
    have hWC : ∀ ω, ‖W ω‖ ≤ C' := fun ω => by
      rw [Real.norm_eq_abs]
      exact (hC ω).trans (le_max_left _ _)
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hWm : Measurable W := hW.mono (𝓖.le s) le_rfl
    have hsm : MeasurableSet {p : Ω × ℝ × ℝ | (s : ℝ) < p.2.1} :=
      measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)
    have hmf : ∀ g : ℝ → ℝ → Ω → ℝ,
        uncurryField (fun r y ω => if (s : ℝ) < r then W ω * g r y ω else 0) =
          {p : Ω × ℝ × ℝ | (s : ℝ) < p.2.1}.indicator (fun p => W p.1 * uncurryField g p) := by
      intro g
      funext p
      simp only [uncurryField, Set.indicator, Set.mem_ofPred_eq]
    have hmaesm : ∀ g : ℝ → ℝ → Ω → ℝ, AEStronglyMeasurable (uncurryField g) (ν.prod volume) →
        AEStronglyMeasurable
          (uncurryField (fun r y ω => if (s : ℝ) < r then W ω * g r y ω else 0))
          (ν.prod volume) := by
      intro g hg
      rw [hmf]
      exact ((hWm.comp measurable_fst).aestronglyMeasurable.mul hg).indicator hsm
    have hmb : ∀ g : ℝ → ℝ → Ω → ℝ, ∀ p, ‖uncurryField
        (fun r y ω => if (s : ℝ) < r then W ω * g r y ω else 0) p‖ ≤
          C' * ‖uncurryField g p‖ := by
      intro g p
      simp only [uncurryField]
      split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hWC _) (norm_nonneg _)
      · simp only [norm_zero]
        positivity
    have hY2 := (hmem hY).2
    refine IsWalshIntegral.limit _ _ _ (fun k ω => W ω * (Xs k ω - X' k ω))
      (fun k => hW' k W hW ⟨C, hC⟩)
      (MemLp.of_le_mul h2 (hmaesm h h2.aestronglyMeasurable) (ae_of_all _ (hmb h)))
      (MemLp.of_le_mul (X2.sub hY2)
        (hWm.aestronglyMeasurable.mul (X2.sub hY2).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hWC ω) (norm_nonneg _))) ?_ ?_
    · have hb : ∀ k, eLpNorm
          (uncurryField (fun r y ω => if (s : ℝ) < r then W ω * hs k r y ω else 0) -
            uncurryField (fun r y ω => if (s : ℝ) < r then W ω * h r y ω else 0)) 2
              (ν.prod volume) ≤
            ENNReal.ofReal C' * eLpNorm (uncurryField (hs k) - uncurryField h) 2
              (ν.prod volume) := by
        intro k
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          ((hmaesm _ (hmem (hk k)).1.aestronglyMeasurable).sub
            (hmaesm h h2.aestronglyMeasurable)) (ae_of_all _ fun p => ?_) 2
        simp only [uncurryField, Pi.sub_apply]
        split_ifs
        · rw [← mul_sub, norm_mul]
          exact mul_le_mul_of_nonneg_right (hWC _) (norm_nonneg _)
        · simp only [sub_self, norm_zero]
          positivity
      have h0 : Tendsto (fun k => ENNReal.ofReal C' *
          eLpNorm (uncurryField (hs k) - uncurryField h) 2 (ν.prod volume)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hb
    · have hb : ∀ k, eLpNorm ((fun ω => W ω * (Xs k ω - X' k ω)) -
          fun ω => W ω * (X ω - Y ω)) 2 ν ≤
            ENNReal.ofReal C' * (eLpNorm (Xs k - X) 2 ν + eLpNorm (X' k - Y) 2 ν) := by
        intro k
        have hXk := (hmem (hk k)).2
        have hX'k := (hmem (hX' k)).2
        refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := (Xs k - X) - (X' k - Y))
          (c := C') ((hWm.aestronglyMeasurable.mul (hXk.sub hX'k).aestronglyMeasurable).sub
            (hWm.aestronglyMeasurable.mul (X2.sub hY2).aestronglyMeasurable))
          (ae_of_all _ fun ω => ?_) 2).trans ?_
        · change ‖W ω * (Xs k ω - X' k ω) - W ω * (X ω - Y ω)‖ ≤
            C' * ‖Xs k ω - X ω - (X' k ω - Y ω)‖
          rw [show W ω * (Xs k ω - X' k ω) - W ω * (X ω - Y ω) =
            W ω * (Xs k ω - X ω - (X' k ω - Y ω)) by ring, norm_mul]
          exact mul_le_mul_of_nonneg_right (hWC ω) (norm_nonneg _)
        · gcongr
          exact eLpNorm_sub_le (by norm_num)
      have h0 : Tendsto (fun k => ENNReal.ofReal C' *
          (eLpNorm (Xs k - X) 2 ν + eLpNorm (X' k - Y) 2 ν)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (Xlim.add hYlim) (Or.inr ENNReal.ofReal_ne_top)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hb

/-! ### Walsh integral processes -/

/-- `Y_t = ∫ 𝟙_{0 < r ≤ t} g dξ` is `𝒢_t`-measurable up to a null set. -/
theorem walshProc_aestronglyMeasurable (hS : IsWhiteNoise 𝓖 S ν) {g : ℝ → ℝ → Ω → ℝ}
    {t : ℝ≥0} {Y : Ω → ℝ}
    (hY : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ t then g r y ω else 0) Y) :
    AEStronglyMeasurable[𝓖 t] Y ν := by
  obtain ⟨X', hX', hm, -⟩ := walshProc_split hS hY t
  have he : X' =ᵐ[ν] Y := by
    refine hX'.ae_eq_lib hS hY (ae_of_all _ fun p => ?_)
    simp only [uncurryField]
    by_cases h1 : p.2.1 ≤ t
    · simp [h1]
    · simp [h1]
  obtain ⟨Z, hZ, hXZ⟩ := hm
  exact ⟨Z, hZ, he.symm.trans hXZ⟩

/-- `𝔼[𝟙_B Y_t] = 𝔼[𝟙_B Y_s]` for `B ∈ 𝒢_s`, `s ≤ t`. -/
theorem walshProc_setIntegral_eq (hS : IsWhiteNoise 𝓖 S ν) {g : ℝ → ℝ → Ω → ℝ}
    {s t : ℝ≥0} (hst : s ≤ t) {Ys Yt : Ω → ℝ}
    (hYs : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ s then g r y ω else 0) Ys)
    (hYt : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ t then g r y ω else 0) Yt)
    {B : Set Ω} (hB : MeasurableSet[𝓖 s] B) :
    ∫ ω in B, Yt ω ∂ν = ∫ ω in B, Ys ω ∂ν := by
  obtain ⟨X', hX', e⟩ := prodNoise_walsh_restrict hS hYt s
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have he : X' =ᵐ[ν] Ys := by
    refine hX'.ae_eq_lib hS hYs (ae_of_all _ fun p => ?_)
    simp only [uncurryField]
    by_cases h1 : p.2.1 ≤ s
    · have : p.2.1 ≤ t := h1.trans hst'
      simp [h1, this]
    · simp [h1]
  have hBm : MeasurableSet B := 𝓖.le s B hB
  have h := e (B.indicator fun _ => 1) (measurable_const.indicator hB)
    ⟨1, fun ω => by by_cases h : ω ∈ B <;> simp [h]⟩
  have e1 : ∀ V : Ω → ℝ, (fun ω => B.indicator (fun _ => (1 : ℝ)) ω * V ω) = B.indicator V := by
    intro V
    funext ω
    by_cases h : ω ∈ B <;> simp [h]
  rw [e1, e1, integral_indicator hBm, integral_indicator hBm] at h
  rw [h]
  exact setIntegral_congr_ae hBm (he.mono fun ω hω _ => hω)

/-- **Martingale property**: `𝔼[Y_t | 𝒢_s] = Y_s` for `s ≤ t`. -/
theorem walshProc_condExp (hS : IsWhiteNoise 𝓖 S ν) {g : ℝ → ℝ → Ω → ℝ}
    {s t : ℝ≥0} (hst : s ≤ t) {Ys Yt : Ω → ℝ}
    (hYs : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ s then g r y ω else 0) Ys)
    (hYt : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ t then g r y ω else 0) Yt) :
    ν[Yt | 𝓖 s] =ᵐ[ν] Ys := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hi : ∀ {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}, IsWalshIntegral 𝓖 S ν h X → Integrable X ν :=
    fun hX => (IsWalshIntegral.isometry_lib hS hX).2.1.integrable one_le_two
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) (hi hYt)
    (fun _ _ _ => (hi hYs).integrableOn)
    (fun B hB _ => (walshProc_setIntegral_eq hS hst hYs hYt hB).symm)
    (walshProc_aestronglyMeasurable hS hYs)).symm

/-- **Conditional isometry**: for `B ∈ 𝒢_s` and `s ≤ t`,
`𝔼[𝟙_B (Y_t - Y_s)(Y'_t - Y'_s)] = 𝔼 ∫∫ 𝟙_B 𝟙_{s < r ≤ t} g g'`. -/
theorem walshProc_setIntegral_mul (hS : IsWhiteNoise 𝓖 S ν) {g g' : ℝ → ℝ → Ω → ℝ}
    {s t : ℝ≥0} (hst : s ≤ t) {Ys Yt Y's Y't : Ω → ℝ}
    (hYs : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ s then g r y ω else 0) Ys)
    (hYt : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ t then g r y ω else 0) Yt)
    (hY's : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ s then g' r y ω else 0) Y's)
    (hY't : IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ t then g' r y ω else 0) Y't)
    {B : Set Ω} (hB : MeasurableSet[𝓖 s] B) :
    ∫ ω in B, (Yt ω - Ys ω) * (Y't ω - Y's ω) ∂ν =
      ∫ p : Ω × ℝ × ℝ, B.indicator (fun _ => (1 : ℝ)) p.1 *
        (if (s : ℝ) < p.2.1 ∧ p.2.1 ≤ t then g p.2.1 p.2.2 p.1 * g' p.2.1 p.2.2 p.1 else 0)
        ∂(ν.prod volume) := by
  have hD := hYt.sub hYs
  have hD' := hY't.sub hY's
  obtain ⟨X', hX', -, hmult⟩ := walshProc_split hS hD s
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hX'0 : X' =ᵐ[ν] 0 := by
    refine hX'.ae_eq_lib hS (IsWalshIntegral.zero _ _ _) (ae_of_all _ fun p => ?_)
    simp only [uncurryField]
    by_cases h1 : p.2.1 ≤ s
    · have h2 : p.2.1 ≤ t := h1.trans (by exact_mod_cast hst)
      simp [h1, h2]
    · simp [h1]
  have hM := hmult (B.indicator fun _ => 1) (measurable_const.indicator hB)
    ⟨1, fun ω => by by_cases h : ω ∈ B <;> simp [h]⟩
  have hI := IsWalshIntegral.integral_mul hS hD' hM
  have hBm : MeasurableSet B := 𝓖.le s B hB
  have hL : ∫ ω in B, (Yt ω - Ys ω) * (Y't ω - Y's ω) ∂ν =
      ∫ ω, (Y't ω - Y's ω) * (B.indicator (fun _ => (1 : ℝ)) ω * ((Yt ω - Ys ω) - X' ω)) ∂ν := by
    rw [← integral_indicator hBm]
    refine integral_congr_ae (hX'0.mono fun ω hω => ?_)
    by_cases h : ω ∈ B <;> simp [h, hω, mul_comm]
  rw [hL, hI]
  congr 1
  funext p
  simp only [uncurryField]
  by_cases hp : p.1 ∈ B
  · by_cases h1 : (s : ℝ) < p.2.1
    · have h0 : 0 < p.2.1 := lt_of_le_of_lt hs0 h1
      have h2 : ¬ p.2.1 ≤ s := not_le.2 h1
      by_cases h3 : p.2.1 ≤ t
      · simp [hp, h1, h0, h2, h3, mul_comm]
      · simp [hp, h1, h0, h2, h3]
    · simp [hp, h1]
  · simp [hp]

end QSSEPtoKPZ
