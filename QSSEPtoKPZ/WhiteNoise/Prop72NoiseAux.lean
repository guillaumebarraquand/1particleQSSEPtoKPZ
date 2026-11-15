/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.MMIntegral
public import QSSEPtoKPZ.Martingales.NullAug
public import QSSEPtoKPZ.Martingales.StoppingAux

/-!
# Proposition 7.2, Step 2: generic lemmas on covariations and versions (task J1)

Auxiliary results for the construction of the white noise in Step 2 of the proof of
Proposition 7.2 (`WhiteNoise/Prop72NoiseBuild.lean`):

* `prop72Noise_cov_congr`, `prop72Noise_cov_mono`: `HasCovariation` is stable under
  indistinguishability and under restriction of the horizon;
* `prop72Noise_cov_stop`: a covariation on `[0, T]` extends to any horizon `T' ≥ T` after
  stopping at `T`: `⟨M_{· ∧ T}, N_{· ∧ T}⟩ = ⟨M, N⟩_{· ∧ T}`;
* `prop72Noise_cov_add4`: bilinearity, `⟨P + Q, P' + Q'⟩ = ⟨P,P'⟩ + ⟨P,Q'⟩ + ⟨Q,P'⟩ + ⟨Q,Q'⟩`;
* `prop72Noise_exists_version`: a process which is almost everywhere adapted, almost surely
  continuous and vanishing at `0` has a version which is adapted (the filtration contains the
  null sets) and vanishes at `0` for every `ω`;
* `prop72Noise_mm_zero`: a martingale-measure integral `h · M` vanishes at time `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}

/-- `HasCovariation` is stable under indistinguishability of `M`, `N` and `A` on `[0, T]`. -/
theorem prop72Noise_cov_congr {T : ℝ} (hT : 0 ≤ T) {M M' N N' A A' : ℝ → Ω → ℝ}
    (h : HasCovariation T 𝓕 M N A μ) (hM : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, M t ω = M' t ω)
    (hN : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, N t ω = N' t ω)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, A t ω = A' t ω) :
    HasCovariation T 𝓕 M' N' A' μ := by
  have h' := h.mmCongrCov hT hA
  have hae : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun ω => M t ω * N t ω - A' t ω) =ᵐ[μ]
      fun ω => M' t ω * N' t ω - A' t ω := fun t ht => by
    filter_upwards [hM, hN] with ω h1 h2
    rw [h1 t ⟨t.2, ht⟩, h2 t ⟨t.2, ht⟩]
  exact ⟨h'.left.congr hM, h'.right.congr hN, h'.integrable_cov, h'.zero, h'.cont_cov, h'.bv,
    fun s t hst ht => (condExp_congr_ae (hae t ht).symm).trans ((h'.condExp_mul s t hst ht).trans
      (hae s (le_trans (NNReal.coe_le_coe.2 hst) ht)))⟩

/-- Restriction of the horizon for `HasCovariation`. -/
theorem prop72Noise_cov_mono {S T : ℝ} {M N A : ℝ → Ω → ℝ} (h : HasCovariation T 𝓕 M N A μ)
    (hST : S ≤ T) : HasCovariation S 𝓕 M N A μ :=
  ⟨h.left.mono_horizon hST, h.right.mono_horizon hST,
    fun t ht => h.integrable_cov t (ht.trans hST), h.zero,
    h.cont_cov.mono fun _ hω => hω.mono (Set.Icc_subset_Icc_right hST),
    h.bv.mono fun _ hω => hω.mono (Set.Icc_subset_Icc_right hST),
    fun s t hst ht => h.condExp_mul s t hst (ht.trans hST)⟩

/-- The martingale property on `[0, T]` passes to the process stopped at `T`, on all of
`[0, ∞)`. -/
private lemma prop72Noise_condExp_stop [IsFiniteMeasure μ] {T : ℝ} (hT : 0 ≤ T) {P : ℝ → Ω → ℝ}
    (hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (P t) μ)
    (hP : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T → μ[P t | 𝓕 s] =ᵐ[μ] P s) (s t : ℝ≥0)
    (hst : s ≤ t) :
    μ[P (min (t : ℝ) T) | 𝓕 s] =ᵐ[μ] P (min (s : ℝ) T) := by
  set τ : ℝ≥0 := ⟨T, hT⟩ with hτ
  have hτT : (τ : ℝ) = T := rfl
  rcases le_total (t : ℝ) T with htT | hTt
  · rw [min_eq_left htT, min_eq_left ((NNReal.coe_le_coe.2 hst).trans htT)]
    exact hP s t hst htT
  · rw [min_eq_right hTt]
    rcases le_total (s : ℝ) T with hsT | hTs
    · rw [min_eq_left hsT]
      have hsτ : s ≤ τ := NNReal.coe_le_coe.1 (by rw [hτT]; exact hsT)
      exact hP s τ hsτ le_rfl
    · rw [min_eq_right hTs]
      have hτs : τ ≤ s := NNReal.coe_le_coe.1 (by rw [hτT]; exact hTs)
      exact condExp_of_aestronglyMeasurable' (𝓕.le s)
        ((aestronglyMeasurable_of_condExp_eq_self (hP τ τ le_rfl le_rfl)).mono (𝓕.mono hτs))
        (hint τ le_rfl)

/-- **Stopping and extension of the horizon**: a covariation `⟨M, N⟩ = A` on `[0, T]` gives
`⟨M_{· ∧ T}, N_{· ∧ T}⟩ = A_{· ∧ T}` on `[0, T']` for every `T'`. -/
theorem prop72Noise_cov_stop [IsFiniteMeasure μ] {T T' : ℝ} (hT : 0 ≤ T)
    {M N A : ℝ → Ω → ℝ} (h : HasCovariation T 𝓕 M N A μ) :
    HasCovariation T' 𝓕 (fun t => M (min t T)) (fun t => N (min t T)) (fun t => A (min t T))
      μ := by
  have hmaps : Set.MapsTo (fun u : ℝ => min u T) (Set.Icc 0 T') (Set.Icc 0 T) :=
    fun _ hu => ⟨le_min hu.1 hT, min_le_right _ _⟩
  have hcm : ContinuousOn (fun u : ℝ => min u T) (Set.Icc 0 T') :=
    (continuous_id.min continuous_const).continuousOn
  set τ : ℝ≥0 := ⟨T, hT⟩ with hτ
  have hc : ∀ t : ℝ≥0, min (t : ℝ) T = ((min t τ : ℝ≥0) : ℝ) := fun t => by
    rw [NNReal.coe_min]; rfl
  have hle : ∀ t : ℝ≥0, ((min t τ : ℝ≥0) : ℝ) ≤ T := fun t => by
    rw [NNReal.coe_min]; exact min_le_right _ _
  have mart : ∀ {P : ℝ → Ω → ℝ}, IsCL2Mart T 𝓕 P μ →
      IsCL2Mart T' 𝓕 (fun t => P (min t T)) μ := fun {P} hP =>
    ⟨hP.cont.mono fun _ hω => hω.comp hcm hmaps,
      fun t _ => by
        show MemLp (P (min (t : ℝ) T)) 2 μ
        rw [hc t]; exact hP.memLp _ (hle t),
      fun s t hst _ => prop72Noise_condExp_stop hT
        (fun t ht => (hP.memLp t ht).integrable one_le_two) hP.condExp s t hst⟩
  refine ⟨mart h.left, mart h.right, fun t _ => ?_, ?_, ?_, ?_, fun s t hst _ => ?_⟩
  · show Integrable (A (min (t : ℝ) T)) μ
    rw [hc t]; exact h.integrable_cov _ (hle t)
  · filter_upwards [h.zero] with ω hω
    simpa [min_eq_left hT] using hω
  · filter_upwards [h.cont_cov] with ω hω
    exact hω.comp hcm hmaps
  · filter_upwards [h.bv] with ω hω
    exact ne_top_of_le_ne_top hω (eVariationOn.comp_le_of_monotoneOn (fun u => A u ω)
      (fun u : ℝ => min u T) (fun _ _ _ _ hab => min_le_min_right _ hab) hmaps)
  · exact prop72Noise_condExp_stop (P := fun t ω => M t ω * N t ω - A t ω) hT
      (fun t ht => ((h.left.memLp t ht).integrable_mul (h.right.memLp t ht)).sub
        (h.integrable_cov t ht)) h.condExp_mul s t hst

/-- **Bilinearity**: `⟨P + Q, P' + Q'⟩ = (⟨P,P'⟩ + ⟨P,Q'⟩) + (⟨Q,P'⟩ + ⟨Q,Q'⟩)`. -/
theorem prop72Noise_cov_add4 [IsFiniteMeasure μ] {T : ℝ} {P Q P' Q' A B C D : ℝ → Ω → ℝ}
    (h1 : HasCovariation T 𝓕 P P' A μ) (h2 : HasCovariation T 𝓕 P Q' B μ)
    (h3 : HasCovariation T 𝓕 Q P' C μ) (h4 : HasCovariation T 𝓕 Q Q' D μ) :
    HasCovariation T 𝓕 (fun t ω => P t ω + Q t ω) (fun t ω => P' t ω + Q' t ω)
      (fun t ω => (A t ω + B t ω) + (C t ω + D t ω)) μ :=
  ((h1.symm.add_left h2.symm).symm).add_left ((h3.symm.add_left h4.symm).symm)

/-- **Adapted version vanishing at `0`.** If the filtration `𝓖` contains the null sets, a
process `N` which is almost everywhere `𝓖`-adapted, almost surely continuous on every `[0, n]`
and almost surely `0` at time `0` has a version `N'`, indistinguishable from it on `[0, ∞)`, with
`N' t` measurable for `𝓖_{t⁺}` (every real `t`) and `N' 0 = 0` everywhere. -/
theorem prop72Noise_exists_version {𝓖 : Filtration ℝ≥0 mΩ} (h0 : nullSets μ ≤ 𝓖 0)
    {N : ℝ → Ω → ℝ} (hN : ∀ t : ℝ≥0, AEStronglyMeasurable[𝓖 t] (N t) μ)
    (hc : ∀ᵐ ω ∂μ, ∀ n : ℕ, ContinuousOn (fun t => N t ω) (Set.Icc 0 n))
    (hN0 : ∀ᵐ ω ∂μ, N 0 ω = 0) :
    ∃ N' : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[𝓖 t.toNNReal] (N' t)) ∧ (∀ ω, N' 0 ω = 0) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → N' t ω = N t ω := by
  classical
  set Y : ℝ≥0 → Ω → ℝ := fun r => (hN r).mk (N r) with hY
  have hgood : ∀ᵐ ω ∂μ, (∀ n : ℕ, ContinuousOn (fun t => N t ω) (Set.Icc 0 n)) ∧ N 0 ω = 0 ∧
      ∀ p : ℕ × ℕ, N (ratGridPt p) ω = Y (ratGridPt p) ω :=
    hc.and (hN0.and (ae_all_iff.2 fun p => (hN (ratGridPt p)).ae_eq_mk))
  set B := toMeasurable μ {ω | ¬ ((∀ n : ℕ, ContinuousOn (fun t => N t ω) (Set.Icc 0 n)) ∧
      N 0 ω = 0 ∧ ∀ p : ℕ × ℕ, N (ratGridPt p) ω = Y (ratGridPt p) ω)} with hBdef
  have hB0 : μ B = 0 := by rw [hBdef, measure_toMeasurable]; exact ae_iff.1 hgood
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hBa : ∀ᵐ ω ∂μ, ω ∉ B := measure_eq_zero_iff_ae_notMem.1 hB0
  have hBt : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] B := fun t =>
    𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t) _ (h0 _ (measurableSet_nullSets hBm hB0))
  have hok : ∀ ω, ω ∉ B → (∀ n : ℕ, ContinuousOn (fun t => N t ω) (Set.Icc 0 n)) ∧
      N 0 ω = 0 ∧ ∀ p : ℕ × ℕ, N (ratGridPt p) ω = Y (ratGridPt p) ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  refine ⟨fun t ω => if ω ∈ B then 0 else N (max t 0) ω, fun t => ?_, fun ω => ?_, ?_⟩
  · -- measurability: limit of the versions at the grid points below `t⁺`
    set τ := t.toNNReal with hτdef
    have hτ : (τ : ℝ) = max t 0 := Real.coe_toNNReal' t
    have hseq : ∀ n, StronglyMeasurable[𝓖 τ]
        (fun ω => if ω ∈ B then 0 else Y (gridBelow τ n) ω) := fun n =>
      StronglyMeasurable.ite (hBt τ) stronglyMeasurable_const
        (((hN _).stronglyMeasurable_mk).mono (𝓖.mono (gridBelow_le τ n)))
    refine (stronglyMeasurable_of_tendsto atTop hseq (tendsto_pi_nhds.2 fun ω => ?_)).measurable
    by_cases hω : ω ∈ B
    · simp only [hω, ite_true]; exact tendsto_const_nhds
    · simp only [hω, ite_false]
      have e : ∀ n, Y (gridBelow τ n) ω = N (gridBelow τ n) ω := fun n =>
        ((hok ω hω).2.2 (⌊((n : ℝ) + 1) * τ⌋₊, n)).symm
      simp only [e, ← hτ]
      set m := ⌈(τ : ℝ)⌉₊
      have hmem : ∀ n, (gridBelow τ n : ℝ) ∈ Set.Icc (0 : ℝ) m := fun n =>
        ⟨(gridBelow τ n).coe_nonneg,
          (NNReal.coe_le_coe.2 (gridBelow_le τ n)).trans (Nat.le_ceil _)⟩
      have hlim : Tendsto (fun n => (gridBelow τ n : ℝ)) atTop (𝓝[Set.Icc 0 m] (τ : ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_gridBelow τ, Eventually.of_forall hmem⟩
      exact ((hok ω hω).1 m τ ⟨τ.coe_nonneg, Nat.le_ceil _⟩).tendsto.comp hlim
  · by_cases hω : ω ∈ B
    · simp [hω]
    · simp only [hω, ite_false, max_self]; exact (hok ω hω).2.1
  · filter_upwards [hBa] with ω hω t ht
    simp [hω, max_eq_left ht]

/-- A martingale-measure integral vanishes at time `0`, almost surely. -/
theorem prop72Noise_mm_zero [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 ≤ T)
    {𝒢 : Filtration ℝ≥0 mΩ} {q : ℝ → ℝ → Ω → ℝ} {M : (ℝ → ℝ) → ℝ → Ω → ℝ}
    {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ} (hX : IsMMIntegral T 𝒢 q M μ h X) :
    X 0 =ᵐ[μ] 0 := by
  induction hX with
  | block s t hst a φ C hφ ha hab =>
    refine ae_of_all _ fun ω => ?_
    show a ω * (M φ (min 0 (t : ℝ)) ω - M φ (min 0 (s : ℝ)) ω) = 0
    rw [min_eq_left t.coe_nonneg, min_eq_left s.coe_nonneg, sub_self, mul_zero]
  | add h h' X X' _ _ ih ih' =>
    filter_upwards [ih, ih'] with ω h1 h2
    show X 0 ω + X' 0 ω = 0
    rw [show X 0 ω = 0 from h1, show X' 0 ω = 0 from h2, add_zero]
  | limit h X hs Xs _ hpred hcont hmeas hconv hsup ih =>
    have h0mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
    have hle : ∀ k, ∫⁻ ω, ENNReal.ofReal (X 0 ω ^ 2) ∂μ ≤
        ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ := by
      intro k
      calc ∫⁻ ω, ENNReal.ofReal (X 0 ω ^ 2) ∂μ
          = ∫⁻ ω, ENNReal.ofReal ((Xs k 0 ω - X 0 ω) ^ 2) ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards [ih k] with ω hω
            rw [show Xs k 0 ω = 0 from hω]; ring_nf
        _ ≤ _ := lintegral_mono fun ω =>
            le_iSup₂_of_le (f := fun r (_ : r ∈ Set.Icc (0 : ℝ) T) =>
              ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) 0 h0mem le_rfl
    have hz : ∫⁻ ω, ENNReal.ofReal (X 0 ω ^ 2) ∂μ = 0 :=
      le_antisymm (ge_of_tendsto' hsup hle) zero_le
    rw [lintegral_eq_zero_iff' ((hmeas 0 h0mem).aemeasurable.pow_const 2).ennreal_ofReal] at hz
    filter_upwards [hz] with ω hω
    have : X 0 ω ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hω
    show X 0 ω = 0
    nlinarith [sq_nonneg (X 0 ω)]

end QSSEPtoKPZ
