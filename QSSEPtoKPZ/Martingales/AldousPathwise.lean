/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Stopping

/-!
# The hitting sequence of Aldous' criterion (task H5b, first part)

INTERFACE FILE (task I0' of Stage 3): the statements below are interfaces, proved by task H5b.
See `docs/stage3-design.md`, Sections 1.2 (e) and 2.5, and `docs/stage3-interfaces.md`.

For a real process `X`, a level `η > 0` and a horizon `T ≥ 0`, the hitting sequence is
`τ₀ = 0` and `τ_{k+1} = inf {t ≥ 0 : |X_t - X_{t ∧ τ_k}| ≥ η} ∧ T`, i.e. the first time after
`τ_k` at which `X` has moved by `η` from `X_{τ_k}`, capped at `T` (Stage 2's `hitTime` applied to
the process `t ↦ |X_t - X_{t ∧ τ_k}|`, which vanishes on `[0, τ_k]`).

* For each `ω`, `(τ_k)` is nondecreasing, bounded by `T`, `|X_u - X_{τ_k}| ≤ η` on
  `[τ_k, τ_{k+1}]`, and every `τ_{k+1} < T` is a genuine hit: `|X_{τ_{k+1}} - X_{τ_k}| ≥ η`.
* Each `τ_k` is a stopping time when all paths are continuous and `X` is adapted.
* Two pathwise lemmas (no probability): (P1) if `τ_N = T` and `|X_t - X_s| ≥ 3η` with
  `s, t ∈ [0,T]`, `|t - s| ≤ δ`, some `k < N` is a genuine hit with `τ_{k+1} - τ_k ≤ δ`;
  (P2) if `τ_N < T`, at least `N - T/δ₁` of the `N` first steps are genuine hits of length at
  most `δ₁`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- The hitting sequence: `τ₀ = 0`, `τ_{k+1}` = first time `t` with `|X_t - X_{t ∧ τ_k}| ≥ η`,
capped at `T`. -/
def aldousHit (X : ℝ → Ω → ℝ) (η : ℝ) (T : ℝ≥0) : ℕ → Ω → ℝ≥0
  | 0 => fun _ => 0
  | k + 1 => hitTime (fun t ω => |X t ω - X (min t (aldousHit X η T k ω : ℝ)) ω|) η T

/-- `τ₀ = 0`. **(proved)** -/
@[simp] theorem aldousHit_zero (X : ℝ → Ω → ℝ) (η : ℝ) (T : ℝ≥0) (ω : Ω) :
    aldousHit X η T 0 ω = 0 := rfl

/-- `τ_k ≤ T`. **(proved)** -/
theorem aldousHit_le (X : ℝ → Ω → ℝ) (η : ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    aldousHit X η T k ω ≤ T := by
  cases k with
  | zero => exact zero_le
  | succ k => exact hitTime_le _ _ _ _

/-! ### Auxiliary facts on `hitTime` -/

/-- The hitting time is at most any time `u` at which the level is reached. -/
private lemma aldousHitTime_le_of_le {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω} {u : ℝ≥0}
    (h : K ≤ X u ω) : hitTime X K T ω ≤ u :=
  inf_le_left.trans (csInf_le (OrderBot.bddBelow _) (Or.inl h))

/-- If `X < K` before `a ≤ T`, the hitting time is at least `a`. -/
private lemma aldousLe_hitTime_of_forall {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω} {a : ℝ≥0}
    (haT : a ≤ T) (h : ∀ t : ℝ≥0, t < a → X t ω < K) : a ≤ hitTime X K T ω := by
  refine le_inf (le_csInf ⟨T, Or.inr rfl⟩ ?_) haT
  rintro t (ht | ht)
  · by_contra hlt
    exact absurd (h t (not_le.1 hlt)) (not_lt.2 ht)
  · rw [Set.mem_singleton_iff.1 ht]; exact haT

/-- For a continuous path, the level is reached at the hitting time, if the hitting time is
`< T` or if the level is reached somewhere on `[0, T]` (the set `{X ≥ K} ∪ {T}` is closed). -/
private lemma aldousLe_at_hitTime {X : ℝ → Ω → ℝ} {K : ℝ} {T : ℝ≥0} {ω : Ω}
    (hc : Continuous fun s : ℝ≥0 => X s ω)
    (h : hitTime X K T ω < T ∨ ∃ u : ℝ≥0, u ≤ T ∧ K ≤ X u ω) :
    K ≤ X (hitTime X K T ω) ω := by
  have hS : IsClosed ({s : ℝ≥0 | K ≤ X s ω} ∪ {T}) :=
    (isClosed_le continuous_const hc).union isClosed_singleton
  have hmem := hS.csInf_mem ⟨T, Or.inr rfl⟩ (OrderBot.bddBelow _)
  have hmT : sInf ({s : ℝ≥0 | K ≤ X s ω} ∪ {T}) ≤ T :=
    csInf_le (OrderBot.bddBelow _) (Or.inr rfl)
  have he : hitTime X K T ω = sInf ({s : ℝ≥0 | K ≤ X s ω} ∪ {T}) := inf_eq_left.2 hmT
  rcases hmem with hK | hT
  · rw [he]; exact hK
  · rw [Set.mem_singleton_iff] at hT
    rcases h with h | ⟨u, huT, hu⟩
    · rw [he, hT] at h; exact absurd h (lt_irrefl _)
    · have hu' : sInf ({s : ℝ≥0 | K ≤ X s ω} ∪ {T}) ≤ u :=
        csInf_le (OrderBot.bddBelow _) (Or.inl hu)
      rw [hT] at hu'
      have hu2 : u = T := le_antisymm huT hu'
      rw [he, hT, ← hu2]; exact hu

/-! ### The process behind the hitting sequence -/

/-- The process `t ↦ |X_t - X_{t ∧ τ_k}|` whose hitting time of `η` is `τ_{k+1}`. -/
private def aldousHitProc (X : ℝ → Ω → ℝ) (η : ℝ) (T : ℝ≥0) (k : ℕ) : ℝ → Ω → ℝ :=
  fun t ω => |X t ω - X (min t (aldousHit X η T k ω : ℝ)) ω|

private lemma aldousHit_succ_eq (X : ℝ → Ω → ℝ) (η : ℝ) (T : ℝ≥0) (k : ℕ) :
    aldousHit X η T (k + 1) = hitTime (aldousHitProc X η T k) η T := rfl

private lemma aldousHitProc_of_le {X : ℝ → Ω → ℝ} {η : ℝ} {T : ℝ≥0} {k : ℕ} {ω : Ω} {u : ℝ≥0}
    (h : aldousHit X η T k ω ≤ u) :
    aldousHitProc X η T k u ω = |X u ω - X (aldousHit X η T k ω) ω| := by
  simp only [aldousHitProc, min_eq_right (NNReal.coe_le_coe.2 h)]

private lemma aldousHitProc_of_ge {X : ℝ → Ω → ℝ} {η : ℝ} {T : ℝ≥0} {k : ℕ} {ω : Ω} {u : ℝ≥0}
    (h : u ≤ aldousHit X η T k ω) : aldousHitProc X η T k u ω = 0 := by
  simp only [aldousHitProc, min_eq_left (NNReal.coe_le_coe.2 h), sub_self, abs_zero]

private lemma continuous_aldousHitProc {X : ℝ → Ω → ℝ} {η : ℝ} {T : ℝ≥0} {k : ℕ} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => X t ω) :
    Continuous fun t : ℝ≥0 => aldousHitProc X η T k t ω := by
  have e : (fun t : ℝ≥0 => X (min (t : ℝ) (aldousHit X η T k ω : ℝ)) ω) =
      (fun t : ℝ≥0 => X t ω) ∘ fun t => min t (aldousHit X η T k ω) := by
    ext t; simp [NNReal.coe_min]
  have h2 : Continuous fun t : ℝ≥0 => X (min (t : ℝ) (aldousHit X η T k ω : ℝ)) ω := by
    rw [e]; exact hc.comp (continuous_id.min continuous_const)
  exact (hc.sub h2).abs

/-- `τ_k ≤ τ_{k+1}`. -/
private lemma aldousHit_le_succ {X : ℝ → Ω → ℝ} {η : ℝ} (hη : 0 < η) (T : ℝ≥0) (k : ℕ)
    (ω : Ω) : aldousHit X η T k ω ≤ aldousHit X η T (k + 1) ω := by
  rw [aldousHit_succ_eq]
  refine aldousLe_hitTime_of_forall (aldousHit_le X η T k ω) fun t ht => ?_
  rw [aldousHitProc_of_ge ht.le]; exact hη

/-- The hitting sequence is nondecreasing (for `η > 0`). -/
theorem aldousHit_monotone {X : ℝ → Ω → ℝ} {η : ℝ} (hη : 0 < η) (T : ℝ≥0) (ω : Ω) :
    Monotone fun k => aldousHit X η T k ω := by
  exact monotone_nat_of_le_succ fun k => aldousHit_le_succ hη T k ω

/-- Before the next hit, `X` stays within `η` of `X_{τ_k}`: `|X_u - X_{τ_k}| < η` for
`τ_k ≤ u < τ_{k+1}`. -/
theorem aldousHit_abs_sub_lt {X : ℝ → Ω → ℝ} {η : ℝ} (hη : 0 < η) {T : ℝ≥0} {k : ℕ} {ω : Ω}
    {u : ℝ≥0} (h1 : aldousHit X η T k ω ≤ u) (h2 : u < aldousHit X η T (k + 1) ω) :
    |X u ω - X (aldousHit X η T k ω) ω| < η := by
  -- (`hη` is not needed for this inequality; it is kept for a uniform interface.)
  have _ := hη
  have h := lt_of_lt_hitTime (X := aldousHitProc X η T k)
    (show u < hitTime (aldousHitProc X η T k) η T ω from h2)
  rwa [aldousHitProc_of_le h1] at h

/-- For a continuous path, `|X_u - X_{τ_k}| ≤ η` on the closed interval `[τ_k, τ_{k+1}]`. -/
theorem aldousHit_abs_sub_le {X : ℝ → Ω → ℝ} {η : ℝ} (hη : 0 < η) {T : ℝ≥0} {k : ℕ} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => X t ω)
    {u : ℝ≥0} (h1 : aldousHit X η T k ω ≤ u) (h2 : u ≤ aldousHit X η T (k + 1) ω) :
    |X u ω - X (aldousHit X η T k ω) ω| ≤ η := by
  have h0 : aldousHitProc X η T k ((0 : ℝ≥0) : ℝ) ω ≤ η := by
    rw [aldousHitProc_of_ge zero_le]; exact hη.le
  have h := le_of_le_hitTime (continuous_aldousHitProc (η := η) (T := T) (k := k) hc)
    (by simpa using h0) (show u ≤ hitTime (aldousHitProc X η T k) η T ω from h2)
  rwa [aldousHitProc_of_le h1] at h

/-- For a continuous path, a hit before the horizon is genuine: if `τ_{k+1} < T` then
`|X_{τ_{k+1}} - X_{τ_k}| ≥ η`. -/
theorem aldousHit_hit {X : ℝ → Ω → ℝ} {η : ℝ} (hη : 0 < η) {T : ℝ≥0} {k : ℕ} {ω : Ω}
    (hc : Continuous fun t : ℝ≥0 => X t ω) (h : aldousHit X η T (k + 1) ω < T) :
    η ≤ |X (aldousHit X η T (k + 1) ω) ω - X (aldousHit X η T k ω) ω| := by
  have h' := aldousLe_at_hitTime (continuous_aldousHitProc (η := η) (T := T) (k := k) hc)
    (Or.inl (show hitTime (aldousHitProc X η T k) η T ω < T from h))
  rwa [← aldousHit_succ_eq, aldousHitProc_of_le (aldousHit_le_succ hη T k ω)] at h'

/-- If `τ_k` is a stopping time, the process `t ↦ |X_t - X_{t ∧ τ_k}|` is adapted (the stopped
process of a continuous adapted process is adapted, by progressive measurability). -/
private lemma measurable_aldousHitProc {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    {η : ℝ} {T : ℝ≥0} {k : ℕ}
    (hτ : IsStoppingTime 𝓖 (fun ω => (aldousHit X η T k ω : WithTop ℝ≥0))) (t : ℝ≥0) :
    Measurable[𝓖 t] (aldousHitProc X η T k t) := by
  have hXs : StronglyAdapted 𝓖 (fun s : ℝ≥0 => X s) := fun s => (hXa s).stronglyMeasurable
  have hstop := hXs.stoppedProcess hXc hτ t
  have e : aldousHitProc X η T k t = fun ω => |X t ω -
      stoppedProcess (fun s : ℝ≥0 => X s) (fun ω => (aldousHit X η T k ω : WithTop ℝ≥0)) t ω| := by
    ext ω
    simp only [aldousHitProc, stoppedProcess]
    rw [← WithTop.coe_min, ← NNReal.coe_min]
    rfl
  rw [e]
  exact continuous_abs.measurable.comp ((hXa t).sub hstop.measurable)

/-- If all paths are continuous and `X` is adapted, every `τ_k` is a stopping time. -/
theorem isStoppingTime_aldousHit {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    (η : ℝ) (T : ℝ≥0) (k : ℕ) :
    IsStoppingTime 𝓖 (fun ω => (aldousHit X η T k ω : WithTop ℝ≥0)) := by
  induction k with
  | zero => exact isStoppingTime_const 𝓖 0
  | succ k ih =>
    exact isStoppingTime_hitTime (measurable_aldousHitProc hXc hXa ih)
      (fun ω => continuous_aldousHitProc (hXc ω)) η T

/-- (P1) for `s ≤ t` in `ℝ≥0`. Let `τ_i ≤ s < τ_{i+1}`. Then `τ_{i+1} ≤ t` (otherwise
`|X_t - X_s| < 2η`), `|X_t - X_{τ_{i+1}}| ≥ 3η - η - η = η`, so the next step hits before `t`:
`τ_{i+2} ≤ t` is a genuine hit of length `≤ t - s`. -/
private lemma aldousHit_exists_short_aux {X : ℝ → Ω → ℝ} {η δ : ℝ} (hη : 0 < η) {T : ℝ≥0}
    {N : ℕ} {ω : Ω} (hc : Continuous fun t : ℝ≥0 => X t ω) (hN : aldousHit X η T N ω = T)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) (hδ : (t : ℝ) - s ≤ δ)
    (h3 : 3 * η ≤ |X t ω - X s ω|) :
    ∃ k < N, (aldousHit X η T (k + 1) ω : ℝ) - aldousHit X η T k ω ≤ δ ∧
      η ≤ |X (aldousHit X η T (k + 1) ω) ω - X (aldousHit X η T k ω) ω| := by
  classical
  have hmono := aldousHit_monotone (X := X) hη T ω
  have hsT : s < T := by
    rcases lt_or_eq_of_le (hst.trans htT) with h | h
    · exact h
    · exfalso
      have hts : t = s := le_antisymm (h ▸ htT) hst
      rw [hts, sub_self, abs_zero] at h3
      linarith
  have hex : ∃ m, s < aldousHit X η T m ω := ⟨N, by rw [hN]; exact hsT⟩
  have hm : s < aldousHit X η T (Nat.find hex) ω := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h; rw [h, aldousHit_zero] at hm; exact absurd hm (not_lt.2 zero_le)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hsi : aldousHit X η T i ω ≤ s := not_lt.1 (Nat.find_min hex (by omega : i < Nat.find hex))
  rw [hi] at hm
  have h1 := aldousHit_abs_sub_lt hη hsi hm
  have hti : aldousHit X η T (i + 1) ω ≤ t := by
    by_contra h
    have h2 := aldousHit_abs_sub_lt hη (hsi.trans hst) (not_le.1 h)
    have := abs_sub_le (X t ω) (X (aldousHit X η T i ω) ω) (X s ω)
    rw [abs_sub_comm (X (aldousHit X η T i ω) ω)] at this
    linarith
  have h2 := aldousHit_abs_sub_le hη hc (aldousHit_le_succ hη T i ω) le_rfl
  have h4 : η ≤ |X t ω - X (aldousHit X η T (i + 1) ω) ω| := by
    have e1 := abs_sub_le (X t ω) (X (aldousHit X η T (i + 1) ω) ω) (X s ω)
    have e2 := abs_sub_le (X (aldousHit X η T (i + 1) ω) ω) (X (aldousHit X η T i ω) ω) (X s ω)
    rw [abs_sub_comm (X (aldousHit X η T i ω) ω)] at e2
    linarith
  have hY : η ≤ aldousHitProc X η T (i + 1) t ω := by rw [aldousHitProc_of_le hti]; exact h4
  have hle : aldousHit X η T (i + 1 + 1) ω ≤ t := aldousHitTime_le_of_le hY
  have hhit : η ≤ |X (aldousHit X η T (i + 1 + 1) ω) ω - X (aldousHit X η T (i + 1) ω) ω| := by
    have h' := aldousLe_at_hitTime (continuous_aldousHitProc (η := η) (T := T) (k := i + 1) hc)
      (Or.inr ⟨t, htT, hY⟩)
    rwa [← aldousHit_succ_eq, aldousHitProc_of_le (aldousHit_le_succ hη T (i + 1) ω)] at h'
  have hlt : aldousHit X η T (i + 1) ω < T := by
    refine lt_of_lt_of_le (lt_of_le_of_ne hti ?_) htT
    intro e
    rw [e, sub_self, abs_zero] at h4
    linarith
  have hiN : i + 1 < N := by
    by_contra h
    have h' : aldousHit X η T N ω ≤ aldousHit X η T (i + 1) ω := hmono (not_lt.1 h)
    rw [hN] at h'
    exact absurd h' (not_le.2 hlt)
  refine ⟨i + 1, hiN, ?_, hhit⟩
  have e1 : (aldousHit X η T (i + 1 + 1) ω : ℝ) ≤ t := NNReal.coe_le_coe.2 hle
  have e2 : (s : ℝ) < aldousHit X η T (i + 1) ω := NNReal.coe_lt_coe.2 hm
  linarith

/-- **Pathwise lemma (P1).** If `τ_N = T` and `|X_t - X_s| ≥ 3η` for some `s, t ∈ [0,T]` with
`|t - s| ≤ δ`, then some step `k < N` is a genuine hit (`|X_{τ_{k+1}} - X_{τ_k}| ≥ η`) of length
`τ_{k+1} - τ_k ≤ δ`. -/
theorem aldousHit_exists_short_of_eq {X : ℝ → Ω → ℝ} {η δ : ℝ} (hη : 0 < η) {T : ℝ≥0} {N : ℕ}
    {ω : Ω} (hc : Continuous fun t : ℝ≥0 => X t ω) (hN : aldousHit X η T N ω = T)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) (ht : t ∈ Set.Icc (0 : ℝ) T) (hst : |t - s| ≤ δ)
    (h3 : 3 * η ≤ |X t ω - X s ω|) :
    ∃ k < N, (aldousHit X η T (k + 1) ω : ℝ) - aldousHit X η T k ω ≤ δ ∧
      η ≤ |X (aldousHit X η T (k + 1) ω) ω - X (aldousHit X η T k ω) ω| := by
  lift s to ℝ≥0 using hs.1
  lift t to ℝ≥0 using ht.1
  have hsT : s ≤ T := NNReal.coe_le_coe.1 hs.2
  have htT : t ≤ T := NNReal.coe_le_coe.1 ht.2
  rcases le_total s t with hst' | hts
  · exact aldousHit_exists_short_aux hη hc hN hst' htT ((le_abs_self _).trans hst) h3
  · refine aldousHit_exists_short_aux hη hc hN hts hsT ?_ ?_
    · rw [abs_sub_comm] at hst; exact (le_abs_self _).trans hst
    · rwa [abs_sub_comm]

open scoped Classical in
/-- **Pathwise lemma (P2).** If `τ_N < T`, then all `N` first steps are genuine hits and their
lengths add up to `τ_N < T`, so at least `N - T/δ₁` of them are genuine hits of length at most
`δ₁`. -/
theorem aldousHit_card_short_of_lt {X : ℝ → Ω → ℝ} {η δ₁ : ℝ} (hη : 0 < η) (hδ₁ : 0 < δ₁)
    {T : ℝ≥0} {N : ℕ} {ω : Ω} (hc : Continuous fun t : ℝ≥0 => X t ω)
    (hN : aldousHit X η T N ω < T) :
    (N : ℝ) - T / δ₁ ≤ ((Finset.range N).filter fun k =>
      (aldousHit X η T (k + 1) ω : ℝ) - aldousHit X η T k ω ≤ δ₁ ∧
        η ≤ |X (aldousHit X η T (k + 1) ω) ω - X (aldousHit X η T k ω) ω|).card := by
  have hmono := aldousHit_monotone (X := X) hη T ω
  have hhit : ∀ k < N,
      η ≤ |X (aldousHit X η T (k + 1) ω) ω - X (aldousHit X η T k ω) ω| := fun k hk =>
    aldousHit_hit hη hc (lt_of_le_of_lt (hmono (by omega : k + 1 ≤ N)) hN)
  have hfilt : ((Finset.range N).filter fun k =>
      (aldousHit X η T (k + 1) ω : ℝ) - aldousHit X η T k ω ≤ δ₁ ∧
        η ≤ |X (aldousHit X η T (k + 1) ω) ω - X (aldousHit X η T k ω) ω|) =
      (Finset.range N).filter fun k =>
        (aldousHit X η T (k + 1) ω : ℝ) - aldousHit X η T k ω ≤ δ₁ :=
    Finset.filter_congr fun k hk => and_iff_left (hhit k (Finset.mem_range.1 hk))
  rw [hfilt]
  set len : ℕ → ℝ := fun k => (aldousHit X η T (k + 1) ω : ℝ) - aldousHit X η T k ω with hlen
  have hsum : ∑ k ∈ Finset.range N, len k = aldousHit X η T N ω := by
    simp only [hlen]
    rw [Finset.sum_range_sub (fun k => (aldousHit X η T k ω : ℝ)) N]
    simp
  have hlong : (((Finset.range N).filter fun k => ¬ len k ≤ δ₁).card : ℝ) * δ₁ ≤
      ∑ k ∈ Finset.range N, len k := by
    calc (((Finset.range N).filter fun k => ¬ len k ≤ δ₁).card : ℝ) * δ₁
        = ∑ k ∈ (Finset.range N).filter (fun k => ¬ len k ≤ δ₁), δ₁ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ len k ≤ δ₁), len k :=
          Finset.sum_le_sum fun k hk => (not_le.1 (Finset.mem_filter.1 hk).2).le
      _ ≤ ∑ k ∈ Finset.range N, len k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ =>
            sub_nonneg.2 (NNReal.coe_le_coe.2 (hmono (Nat.le_succ k)))
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.range N) (fun k => len k ≤ δ₁)
  rw [Finset.card_range] at hcard
  have hcard' : (((Finset.range N).filter fun k => len k ≤ δ₁).card : ℝ) +
      ((Finset.range N).filter fun k => ¬ len k ≤ δ₁).card = N := by exact_mod_cast hcard
  have hTN : (aldousHit X η T N ω : ℝ) ≤ T := NNReal.coe_le_coe.2 hN.le
  have hdiv : (((Finset.range N).filter fun k => ¬ len k ≤ δ₁).card : ℝ) ≤ T / δ₁ := by
    rw [le_div_iff₀ hδ₁]; linarith
  linarith

end QSSEPtoKPZ
