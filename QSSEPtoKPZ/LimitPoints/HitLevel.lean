/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Stopping

/-!
# Hitting times of converging paths (task G2)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G2.
See `docs/stage4-design.md`, Sections 1.2 (d) and 3.2, and `docs/stage4-interfaces.md`.

For the localization of the proof of Proposition 7.1 (3) (decision D3″): with the library's
`hitTime X K T` (first time `X ≥ K`, capped at `T`) and the strict version `hitTimeStrict`
(first time `X > K`), hitting times of uniformly converging paths converge at every level `K`
where the two coincide for the limit, and for a process with continuous paths the levels where
they differ with positive probability are countably many (the article: "`K ↦ 𝔼[σ^K]` is
nondecreasing, so that it has at most countably many discontinuities").
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The first time `t ≥ 0` at which `X_t > K`, capped at `T`. -/
def hitTimeStrict (X : ℝ → Ω → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf ({t : ℝ≥0 | K < X t ω} ∪ {T}) ⊓ T

/-! ### Elementary properties of `hitTime` and `hitTimeStrict` -/

/-- The capped infimum `sInf (A ∪ {T}) ⊓ T` is antitone in the set `A`. -/
private lemma pathHit_sInf_anti {A B : Set ℝ≥0} (T : ℝ≥0) (h : A ⊆ B) :
    sInf (B ∪ {T}) ⊓ T ≤ sInf (A ∪ {T}) ⊓ T :=
  inf_le_inf_right _ (csInf_le_csInf (OrderBot.bddBelow _) ⟨T, Or.inr rfl⟩
    (Set.union_subset_union_left _ h))

/-- `sInf (A ∪ {T})` only depends on `A ∩ [0, T]` (one inequality). -/
private lemma pathHit_sInf_le_of {A B : Set ℝ≥0} {T : ℝ≥0}
    (h : ∀ t ≤ T, t ∈ A → t ∈ B) : sInf (B ∪ {T}) ≤ sInf (A ∪ {T}) := by
  refine le_csInf ⟨T, Or.inr rfl⟩ fun x hx => ?_
  rcases le_or_gt x T with hxT | hxT
  · rcases hx with hx | hx
    · exact csInf_le (OrderBot.bddBelow _) (Or.inl (h x hxT hx))
    · exact csInf_le (OrderBot.bddBelow _) (Or.inr hx)
  · exact (csInf_le (OrderBot.bddBelow (B ∪ {T})) (Or.inr rfl : T ∈ B ∪ {T})).trans hxT.le

/-- `sInf (A ∪ {T})` only depends on `A ∩ [0, T]`. -/
private lemma pathHit_sInf_congr {A B : Set ℝ≥0} {T : ℝ≥0}
    (h : ∀ t ≤ T, t ∈ A ↔ t ∈ B) : sInf (A ∪ {T}) = sInf (B ∪ {T}) :=
  le_antisymm (pathHit_sInf_le_of fun t ht => (h t ht).2)
    (pathHit_sInf_le_of fun t ht => (h t ht).1)

/-- `hitTime` is nondecreasing in the level. -/
private lemma pathHit_mono (X : ℝ → Ω → ℝ) {K K' : ℝ} (hK : K ≤ K') (T : ℝ≥0) (ω : Ω) :
    hitTime X K T ω ≤ hitTime X K' T ω :=
  pathHit_sInf_anti T fun _ ht => hK.trans ht

/-- `hitTime ≤ hitTimeStrict` at the same level. -/
private lemma pathHit_le_strict (X : ℝ → Ω → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) :
    hitTime X K T ω ≤ hitTimeStrict X K T ω :=
  pathHit_sInf_anti T fun t (ht : K < X t ω) => ht.le

/-- `hitTimeStrict X K ≤ hitTime X K'` for `K < K'`. -/
private lemma pathStrict_le_hit (X : ℝ → Ω → ℝ) {K K' : ℝ} (hK : K < K') (T : ℝ≥0) (ω : Ω) :
    hitTimeStrict X K T ω ≤ hitTime X K' T ω :=
  pathHit_sInf_anti T fun _ ht => hK.trans_le ht

/-- If `hitTimeStrict < b`, the path exceeds `K` at some time `t < min b T`. -/
private lemma pathStrict_exists {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω} {b : ℝ≥0}
    (hb : hitTimeStrict X K T ω < b) (hT : hitTimeStrict X K T ω < T) :
    ∃ t : ℝ≥0, t < b ∧ t < T ∧ K < X t ω := by
  unfold hitTimeStrict at hb hT
  have hlt : sInf ({t : ℝ≥0 | K < X t ω} ∪ {T}) < min b T := by
    rcases le_total (sInf ({t : ℝ≥0 | K < X t ω} ∪ {T})) T with h | h
    · rw [inf_eq_left.2 h] at hb hT; exact lt_min hb hT
    · rw [inf_eq_right.2 h] at hT; exact absurd hT (lt_irrefl _)
  obtain ⟨t, ht, htb⟩ := exists_lt_of_csInf_lt ⟨T, Or.inr rfl⟩ hlt
  rcases ht with ht | ht
  · exact ⟨t, htb.trans_le (min_le_left _ _), htb.trans_le (min_le_right _ _), ht⟩
  · rw [Set.mem_singleton_iff.1 ht] at htb; exact absurd (htb.trans_le (min_le_right _ _))
      (lt_irrefl _)

/-- `hitTime X K' ≤ t` as soon as `X_t ≥ K'`. -/
private lemma pathHit_le_of {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω} {t : ℝ≥0}
    (h : K ≤ X t ω) : hitTime X K T ω ≤ t :=
  inf_le_left.trans (csInf_le (OrderBot.bddBelow _) (Or.inl h))

/-- **Convergence of hitting times.** If `X_k(·, ω) → X(·, ω)` uniformly on `[0,T]`, the limit
being continuous on `[0,T]`, and the first times at which the limit reaches `K` and exceeds `K`
coincide, then the hitting times of `K` by `X_k` converge to that of `X`. -/
theorem tendsto_hitTime {X : ℕ → ℝ → Ω → ℝ} {Xl : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω}
    (hc : ContinuousOn (fun t => Xl t ω) (Set.Icc 0 T))
    (hu : TendstoUniformlyOn (fun k t => X k t ω) (fun t => Xl t ω) atTop (Set.Icc 0 T))
    (hK : hitTime Xl K T ω = hitTimeStrict Xl K T ω) :
    Tendsto (fun k => hitTime (X k) K T ω) atTop (𝓝 (hitTime Xl K T ω)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- below the hitting time the limit stays below `K - δ` on `[0, a']`
    obtain ⟨a', haa', ha'⟩ := exists_between ha
    have ha'T : (a' : ℝ) ≤ T := NNReal.coe_le_coe.2 (ha'.le.trans (hitTime_le _ _ _ _))
    obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) a')).exists_isMaxOn
      ⟨0, le_rfl, a'.2⟩ (hc.mono (Set.Icc_subset_Icc_right ha'T))
    have hs₀K : Xl s₀ ω < K := by
      have h := lt_of_lt_hitTime (X := Xl) (K := K) (T := T) (ω := ω)
        (t := ⟨s₀, hs₀.1⟩) ((show (⟨s₀, hs₀.1⟩ : ℝ≥0) ≤ a' from hs₀.2).trans_lt ha')
      exact h
    have hδ : 0 < K - Xl s₀ ω := sub_pos.2 hs₀K
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu _ hδ] with k hk
    have hle : a' ≤ sInf ({t : ℝ≥0 | K ≤ X k t ω} ∪ {T}) ⊓ T := by
      refine le_inf (le_csInf ⟨T, Or.inr rfl⟩ fun t ht => ?_) (ha'.le.trans (hitTime_le _ _ _ _))
      rcases ht with ht | ht
      · by_contra hta
        have hta' : (t : ℝ) ∈ Set.Icc (0 : ℝ) a' := ⟨t.2, NNReal.coe_le_coe.2 (not_le.1 hta).le⟩
        have h1 := hk t ⟨t.2, (hta'.2.trans ha'T)⟩
        have h2 := hmax hta'
        rw [Real.dist_eq] at h1
        simp only [Set.mem_ofPred_eq] at ht h2
        have := (abs_lt.1 h1).1
        linarith
      · rw [Set.mem_singleton_iff.1 ht]; exact ha'.le.trans (hitTime_le _ _ _ _)
    exact haa'.trans_le hle
  · -- above: the limit exceeds `K` at a time `t < b`, and so does `X k` for large `k`
    rcases eq_or_lt_of_le (hitTime_le Xl K T ω) with hT | hT
    · exact Eventually.of_forall fun k => (hitTime_le _ _ _ _).trans_lt (hT ▸ hb)
    rw [hK] at hb hT
    obtain ⟨t, htb, htT, hKt⟩ := pathStrict_exists hb hT
    have hlim := hu.tendsto_at (show (t : ℝ) ∈ Set.Icc (0 : ℝ) T from
      ⟨t.2, NNReal.coe_le_coe.2 htT.le⟩)
    filter_upwards [hlim.eventually (lt_mem_nhds hKt)] with k hk
    exact (pathHit_le_of hk.le).trans_lt htb

/-- For a process with measurable values and paths continuous on `[0,T]`, `ω ↦ hitTime V K T ω`
is measurable (apply `isStoppingTime_hitTime` to the process stopped at `T`, for the constant
filtration). -/
private lemma measurable_pathHit {V : ℝ → Ω → ℝ} {T : ℝ≥0} (hV : ∀ t, Measurable (V t))
    (hc : ∀ ω, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) (K : ℝ) :
    Measurable fun ω => hitTime V K T ω := by
  set V' : ℝ → Ω → ℝ := fun t ω => V (min t T) ω with hV'
  have heq : ∀ ω, hitTime V K T ω = hitTime V' K T ω := fun ω => by
    unfold hitTime
    congr 1
    refine pathHit_sInf_congr fun t ht => ?_
    simp only [hV', Set.mem_ofPred_eq, min_eq_left (NNReal.coe_le_coe.2 ht)]
  have hc' : ∀ ω, Continuous fun t : ℝ≥0 => V' t ω := fun ω =>
    (hc ω).comp_continuous (by fun_prop) fun t => ⟨le_min t.2 T.2, min_le_right _ _⟩
  have hst := isStoppingTime_hitTime (X := V') (𝓕 := Filtration.const ℝ≥0 mΩ le_rfl)
    (fun t => hV _) hc' K T
  simp_rw [heq]
  refine measurable_of_Iic fun t => ?_
  have := hst t
  simp only [WithTop.coe_le_coe] at this
  exact this

/-- `hitTimeStrict V K` is the limit of `hitTime V (K + 1/(n+1))` (no continuity needed). -/
private lemma tendsto_pathHit_strict (V : ℝ → Ω → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => hitTime V (K + 1 / ((n : ℝ) + 1)) T ω) atTop
      (𝓝 (hitTimeStrict V K T ω)) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (pathStrict_le_hit V (lt_add_of_pos_right _ (by positivity)) T ω),
    fun b hb => ?_⟩
  rcases eq_or_lt_of_le (show hitTimeStrict V K T ω ≤ T from inf_le_right) with hT | hT
  · exact Eventually.of_forall fun k => (hitTime_le _ _ _ _).trans_lt (hT ▸ hb)
  obtain ⟨t, htb, -, hKt⟩ := pathStrict_exists hb hT
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hKt)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (pathHit_le_of ?_).trans_lt htb
  have : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
  linarith

/-- **Countably many bad levels.** For a process with measurable values and paths continuous on
`[0,T]`, the set of levels `K` such that `hitTime ≠ hitTimeStrict` with positive (outer)
probability is countable. -/
theorem countable_hitTime_ne {μ : Measure Ω} [IsFiniteMeasure μ] {V : ℝ → Ω → ℝ} {T : ℝ≥0}
    (hV : ∀ t, Measurable (V t)) (hc : ∀ ω, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) :
    Set.Countable {K : ℝ | μ {ω | hitTime V K T ω ≠ hitTimeStrict V K T ω} ≠ 0} := by
  have hm : ∀ K, Measurable fun ω => hitTime V K T ω := measurable_pathHit hV hc
  have hms : ∀ K, Measurable fun ω => hitTimeStrict V K T ω := fun K =>
    measurable_of_tendsto_metrizable (fun n => hm _)
      (tendsto_pi_nhds.2 fun ω => tendsto_pathHit_strict V K T ω)
  have hb : ∀ (f : Ω → ℝ≥0), (∀ ω, f ω ≤ T) → Measurable f → Integrable (fun ω => (f ω : ℝ)) μ :=
    fun f hf hfm => Integrable.of_bound hfm.coe_nnreal_real.aestronglyMeasurable T
      (ae_of_all _ fun ω => by simpa using hf ω)
  have hi : ∀ K, Integrable (fun ω => (hitTime V K T ω : ℝ)) μ := fun K =>
    hb _ (fun ω => hitTime_le _ _ _ _) (hm K)
  have his : ∀ K, Integrable (fun ω => (hitTimeStrict V K T ω : ℝ)) μ := fun K =>
    hb _ (fun ω => inf_le_right) (hms K)
  -- `F K = 𝔼[hitTime V K T]` is nondecreasing
  set F : ℝ → ℝ := fun K => ∫ ω, (hitTime V K T ω : ℝ) ∂μ with hF
  have hFm : Monotone F := fun K K' hK =>
    integral_mono (hi K) (hi K') fun ω => NNReal.coe_le_coe.2 (pathHit_mono V hK T ω)
  refine hFm.countable_not_continuousAt.mono fun K hK => ?_
  simp only [Set.mem_ofPred_eq] at hK ⊢
  intro hcont
  apply hK
  -- at a continuity point of `F`, `hitTime = hitTimeStrict` almost surely
  set g : Ω → ℝ := fun ω => (hitTimeStrict V K T ω : ℝ) - hitTime V K T ω with hg
  have hg0 : 0 ≤ g := fun ω => sub_nonneg.2 (NNReal.coe_le_coe.2 (pathHit_le_strict V K T ω))
  have hgi : Integrable g μ := (his K).sub (hi K)
  have hle : ∀ n : ℕ, ∫ ω, g ω ∂μ ≤ F (K + 1 / ((n : ℝ) + 1)) - F K := fun n => by
    rw [hF, ← integral_sub (hi _) (hi K)]
    exact integral_mono hgi ((hi _).sub (hi K)) fun ω => sub_le_sub_right
      (NNReal.coe_le_coe.2 (pathStrict_le_hit V (lt_add_of_pos_right _ (by positivity)) T ω)) _
  have hlim : Tendsto (fun n : ℕ => F (K + 1 / ((n : ℝ) + 1)) - F K) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => K + 1 / ((n : ℝ) + 1)) atTop (𝓝 K) := by
      simpa using (tendsto_const_nhds (x := K)).add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ((hcont.tendsto.comp h1).sub_const (F K))
  have hint0 : ∫ ω, g ω ∂μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) (integral_nonneg hg0)
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hint0
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, hg] at hω ⊢
  intro h
  exact hω (NNReal.coe_injective (by linarith))

end QSSEPtoKPZ
