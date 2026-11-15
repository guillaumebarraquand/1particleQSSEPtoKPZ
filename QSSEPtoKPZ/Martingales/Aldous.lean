/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.AldousTrick
public import QSSEPtoKPZ.Martingales.AldousPathwise

/-!
# Aldous' criterion for processes with continuous paths (task H5b, second part)

INTERFACE FILE (task I0' of Stage 3): the statement below is an interface, proved by task H5b.
See `docs/stage3-design.md`, Sections 1.2 (e) and 2.5, and `docs/stage3-interfaces.md`.

Two-scale quantitative form of Aldous' criterion (Aldous 1978; Billingsley, Theorem 16.10, for
càdlàg processes), proved here for continuous paths only. Let `X` have all paths continuous on
`[0, ∞)` and be adapted. Let `a(δ)` bound `ℙ(|X_{ρ+s} - X_ρ| ≥ η/2)` over stopping times
`ρ ≤ T + 1` and `s ∈ [0, 2δ]`. For `0 < δ ≤ δ₁ ≤ 1/2` and `N ≥ 2T/δ₁`,
`ℙ(sup_{s,t ≤ T, |t-s| ≤ δ} |X_t - X_s| ≥ 3η) ≤ 6 a(δ₁) + 3 N a(δ)`.

Proof: hitting sequence `τ_k = aldousHit X η T k` (file `AldousPathwise.lean`). By (P1) the
event is contained in `{τ_N < T} ∪ ⋃_{k<N} {|X_{σ_k} - X_{τ_k}| ≥ η}` with
`σ_k = τ_{k+1} ∧ (τ_k + δ)`, each of probability at most `3a(δ)` by Aldous' trick
(`aldous_trick` with level `η/2`). By (P2) and Markov's inequality on the number of short genuine
hits (with `σ'_k = τ_{k+1} ∧ (τ_k + δ₁)`), `ℙ(τ_N < T) ≤ (2/N) · N · 3 a(δ₁) = 6 a(δ₁)`.

Choosing first `δ₁` (so that `6 a(δ₁)` is small), then `N = ⌈2T/δ₁⌉`, then `δ ≤ δ₁` (so that
`3 N a(δ)` is small) gives the modulus of continuity in probability needed for tightness in
`C([0,T], ℝ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **One step of the hitting sequence, capped.** With `τ_k = aldousHit X η T k` and
`σ_k = τ_{k+1} ∧ (τ_k + d)`, Aldous' trick at level `η/2` gives
`ℙ(|X_{σ_k} - X_{τ_k}| ≥ η) ≤ 3b` when `ℙ(|X_{ρ+s} - X_ρ| ≥ η/2) ≤ b` for `s ∈ [0, 2d]`. -/
private lemma aldousModulus_step [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    {T η d b : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hd : 0 < d) (hd1 : d ≤ 1)
    (hA : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * d),
        μ {ω | η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal b) (k : ℕ) :
    μ {ω | η ≤ |X (min (aldousHit X η T.toNNReal (k + 1) ω)
        (aldousHit X η T.toNNReal k ω + d.toNNReal)) ω - X (aldousHit X η T.toNNReal k ω) ω|}
      ≤ ENNReal.ofReal (3 * b) := by
  have hτ := isStoppingTime_aldousHit (𝓖 := 𝓖) hXc hXa η T.toNNReal k
  have hτ1 := isStoppingTime_aldousHit (𝓖 := 𝓖) hXc hXa η T.toNNReal (k + 1)
  have hτd : IsStoppingTime 𝓖
      (fun ω => ((aldousHit X η T.toNNReal k ω + d.toNNReal : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_comp_of_monotone hτ (F := fun x => x + d.toNNReal)
      (fun x y h => add_le_add_left h _) fun x => le_self_add
  have hσ : IsStoppingTime 𝓖 (fun ω => ((min (aldousHit X η T.toNNReal (k + 1) ω)
      (aldousHit X η T.toNNReal k ω + d.toNNReal) : ℝ≥0) : WithTop ℝ≥0)) := by
    have e : (fun ω => ((min (aldousHit X η T.toNNReal (k + 1) ω)
        (aldousHit X η T.toNNReal k ω + d.toNNReal) : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => min ((aldousHit X η T.toNNReal (k + 1) ω : ℝ≥0) : WithTop ℝ≥0)
          ((aldousHit X η T.toNNReal k ω + d.toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun ω => WithTop.coe_min _ _
    rw [e]; exact hτ1.min hτd
  have h := aldous_trick (μ := μ) (𝓖 := 𝓖) hXc hXa (T := T) (η := η / 2) hd hd1 hA hτ hσ
    (fun ω => by
      have := NNReal.coe_le_coe.2 (aldousHit_le X η T.toNNReal k ω)
      rwa [Real.coe_toNNReal T hT] at this)
    (fun ω => le_min (aldousHit_monotone hη _ ω (Nat.le_succ k)) le_self_add)
    (fun ω => by
      have := NNReal.coe_le_coe.2 (min_le_right (aldousHit X η T.toNNReal (k + 1) ω)
        (aldousHit X η T.toNNReal k ω + d.toNNReal))
      rwa [NNReal.coe_add, Real.coe_toNNReal d hd.le] at this)
  have e2 : 2 * (η / 2) = η := by ring
  rwa [e2] at h

/-- **Aldous' criterion, continuous paths** (two-scale quantitative form). If
`ℙ(|X_{ρ+s} - X_ρ| ≥ η/2) ≤ a₁` for stopping times `ρ ≤ T + 1` and `s ∈ [0, 2δ₁]`, and `≤ a` for
`s ∈ [0, 2δ]`, with `0 < δ ≤ δ₁ ≤ 1/2` and `2T ≤ N δ₁`, then
`ℙ(∃ s, t ∈ [0,T], |t - s| ≤ δ, |X_t - X_s| ≥ 3η) ≤ 6 a₁ + 3 N a`. -/
theorem aldous_modulus [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    {T η δ δ₁ a a₁ : ℝ} {N : ℕ} (hT : 0 ≤ T) (hη : 0 < η) (hδ : 0 < δ) (hδδ₁ : δ ≤ δ₁)
    (hδ₁ : δ₁ ≤ 1 / 2) (hN : 2 * T ≤ N * δ₁) (ha : 0 ≤ a) (ha₁ : 0 ≤ a₁)
    (hA₁ : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ₁),
        μ {ω | η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a₁)
    (hA : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ),
        μ {ω | η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a) :
    μ {ω | ∃ s ∈ Set.Icc (0 : ℝ) T, ∃ t ∈ Set.Icc (0 : ℝ) T,
      |t - s| ≤ δ ∧ 3 * η ≤ |X t ω - X s ω|} ≤ ENNReal.ofReal (6 * a₁ + 3 * N * a) := by
  classical
  have hδ₁0 : 0 < δ₁ := hδ.trans_le hδδ₁
  have hT' : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
  -- the union over the `N` first steps, capped at `δ`
  set U : ℕ → Set Ω := fun k => {ω | η ≤ |X (min (aldousHit X η T.toNNReal (k + 1) ω)
    (aldousHit X η T.toNNReal k ω + δ.toNNReal)) ω - X (aldousHit X η T.toNNReal k ω) ω|}
    with hU
  set B : Set Ω := {ω | aldousHit X η T.toNNReal N ω < T.toNNReal} with hB
  -- (P1): the event is contained in `B ∪ ⋃_{k<N} U_k`
  have hsub : {ω | ∃ s ∈ Set.Icc (0 : ℝ) T, ∃ t ∈ Set.Icc (0 : ℝ) T,
      |t - s| ≤ δ ∧ 3 * η ≤ |X t ω - X s ω|} ⊆ B ∪ ⋃ k ∈ Finset.range N, U k := by
    rintro ω ⟨s, hs, t, ht, hst, h3⟩
    by_cases hBω : aldousHit X η T.toNNReal N ω < T.toNNReal
    · exact Or.inl hBω
    right
    have hN' : aldousHit X η T.toNNReal N ω = T.toNNReal :=
      le_antisymm (aldousHit_le _ _ _ _ _) (not_lt.1 hBω)
    rw [← hT'] at hs ht
    obtain ⟨k, hk, hlen, hhit⟩ := aldousHit_exists_short_of_eq hη (hXc ω) hN' hs ht hst h3
    refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 hk, ?_⟩
    have hle : (aldousHit X η T.toNNReal (k + 1) ω : ℝ) ≤
        aldousHit X η T.toNNReal k ω + (δ.toNNReal : ℝ) := by
      rw [Real.coe_toNNReal δ hδ.le]; linarith
    show η ≤ _
    rw [min_eq_left hle]; exact hhit
  -- bound on the union
  have hUb : μ (⋃ k ∈ Finset.range N, U k) ≤ ENNReal.ofReal (3 * N * a) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ k ∈ Finset.range N, μ (U k)
        ≤ ∑ _k ∈ Finset.range N, ENNReal.ofReal (3 * a) := Finset.sum_le_sum fun k _ =>
          aldousModulus_step hXc hXa hT hη hδ (by linarith) hA k
      _ = ENNReal.ofReal (3 * N * a) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          ring_nf
  -- (P2) and Markov's inequality: bound on `B`
  have hBb : μ B ≤ ENNReal.ofReal (6 * a₁) := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · have hT0 : T.toNNReal = 0 := by
        rw [Real.toNNReal_eq_zero]; rw [hN0] at hN; simp at hN; linarith
      have hBe : B = ∅ := by
        ext ω; simp only [hB, Set.mem_ofPred_eq, hT0, Set.mem_empty_iff_false, iff_false]
        exact not_lt.2 zero_le
      rw [hBe, measure_empty]; exact zero_le
    set V : ℕ → Set Ω := fun k => {ω | η ≤ |X (min (aldousHit X η T.toNNReal (k + 1) ω)
      (aldousHit X η T.toNNReal k ω + δ₁.toNNReal)) ω - X (aldousHit X η T.toNNReal k ω) ω|}
      with hV
    set f : Ω → ℝ≥0∞ := fun ω => ∑ k ∈ Finset.range N,
      (toMeasurable μ (V k)).indicator 1 ω with hf
    have hfm : Measurable f := Finset.measurable_sum _ fun k _ =>
      measurable_const.indicator (measurableSet_toMeasurable μ (V k))
    have hBsub : B ⊆ {ω | (N : ℝ≥0∞) ≤ 2 * f ω} := by
      intro ω hω
      have hP2 := aldousHit_card_short_of_lt hη hδ₁0 (hXc ω) hω
      set F := (Finset.range N).filter fun k =>
        (aldousHit X η T.toNNReal (k + 1) ω : ℝ) - aldousHit X η T.toNNReal k ω ≤ δ₁ ∧
          η ≤ |X (aldousHit X η T.toNNReal (k + 1) ω) ω - X (aldousHit X η T.toNNReal k ω) ω|
        with hF
      have hdiv : T / δ₁ ≤ N / 2 := by
        rw [div_le_iff₀ hδ₁0]; linarith
      rw [hT'] at hP2
      have hNF : N ≤ 2 * F.card := by
        have : (N : ℝ) ≤ 2 * F.card := by linarith
        exact_mod_cast this
      have hFf : (F.card : ℝ≥0∞) ≤ f ω := by
        calc (F.card : ℝ≥0∞) = ∑ k ∈ F, (toMeasurable μ (V k)).indicator 1 ω := by
              rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
              refine Finset.sum_congr rfl fun k hk => ?_
              have hk' := (Finset.mem_filter.1 hk).2
              have hle : (aldousHit X η T.toNNReal (k + 1) ω : ℝ) ≤
                  aldousHit X η T.toNNReal k ω + (δ₁.toNNReal : ℝ) := by
                rw [Real.coe_toNNReal δ₁ hδ₁0.le]
                linarith [hk'.1]
              have hmem : ω ∈ V k := by
                show η ≤ _
                rw [min_eq_left hle]; exact hk'.2
              rw [Set.indicator_of_mem (subset_toMeasurable μ (V k) hmem)]; rfl
          _ ≤ f ω := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      show (N : ℝ≥0∞) ≤ 2 * f ω
      calc (N : ℝ≥0∞) ≤ ((2 * F.card : ℕ) : ℝ≥0∞) := by exact_mod_cast hNF
        _ = 2 * (F.card : ℝ≥0∞) := by push_cast; ring
        _ ≤ 2 * f ω := by gcongr
    have hmarkov := mul_meas_ge_le_lintegral₀ (μ := μ) (hfm.const_mul 2).aemeasurable (N : ℝ≥0∞)
    have hint : ∫⁻ ω, 2 * f ω ∂μ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (6 * a₁) := by
      rw [lintegral_const_mul _ hfm]
      simp only [hf]
      rw [lintegral_finsetSum (Finset.range N) (f := fun k => (toMeasurable μ (V k)).indicator 1)
        fun k _ => measurable_const.indicator (measurableSet_toMeasurable μ (V k))]
      simp_rw [lintegral_indicator_one (measurableSet_toMeasurable μ _), measure_toMeasurable]
      calc 2 * ∑ k ∈ Finset.range N, μ (V k)
          ≤ 2 * ∑ _k ∈ Finset.range N, ENNReal.ofReal (3 * a₁) := by
            gcongr with k hk
            exact aldousModulus_step hXc hXa hT hη hδ₁0 (by linarith) hA₁ k
        _ = (N : ℝ≥0∞) * ENNReal.ofReal (6 * a₁) := by
            have e6 : ENNReal.ofReal (6 * a₁) = 2 * ENNReal.ofReal (3 * a₁) := by
              rw [show (6 : ℝ) * a₁ = 2 * (3 * a₁) by ring,
                ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, e6]
            ring
    have hNB : (N : ℝ≥0∞) * μ B ≤ (N : ℝ≥0∞) * ENNReal.ofReal (6 * a₁) :=
      (mul_le_mul' le_rfl (measure_mono hBsub)).trans (hmarkov.trans hint)
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hNpos.ne')
      (ENNReal.natCast_ne_top N)).1 hNB
  calc μ {ω | ∃ s ∈ Set.Icc (0 : ℝ) T, ∃ t ∈ Set.Icc (0 : ℝ) T,
        |t - s| ≤ δ ∧ 3 * η ≤ |X t ω - X s ω|}
      ≤ μ (B ∪ ⋃ k ∈ Finset.range N, U k) := measure_mono hsub
    _ ≤ μ B + μ (⋃ k ∈ Finset.range N, U k) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (6 * a₁) + ENNReal.ofReal (3 * N * a) := add_le_add hBb hUb
    _ = ENNReal.ofReal (6 * a₁ + 3 * N * a) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end QSSEPtoKPZ
