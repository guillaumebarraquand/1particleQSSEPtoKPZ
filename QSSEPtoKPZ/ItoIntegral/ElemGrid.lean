/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Elementary

/-!
# Elementary integrands between consecutive grid points (package C, task C2, auxiliary)

For an elementary integrand `e`, let `P(e)` be the finite set of the endpoints `a`, `b` of its
blocks (`elemGridPts`) and `F(e)` the finite set of the indices of its blocks (`elemGridIdx`).
If no point of `P(e)` lies in the open interval `(s, t)`, then on `(s, t]` the integrand is
constant in time, equal to `xᵢ = eᵢ(t)`, which is bounded and `𝓖_s`-measurable, and
`I_t(e) - I_s(e) = ∑_{i ∈ F(e)} xᵢ (Bᵢ(t) - Bᵢ(s))` (`elemGrid_integral_sub`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*}

open Classical in
/-- The endpoints of the blocks of an elementary integrand. -/
def elemGridPts (e : ElemIntegrand 𝓖 ι) : Finset ℝ≥0 :=
  (e.map fun bl => bl.a).toFinset ∪ (e.map fun bl => bl.b).toFinset

open Classical in
/-- The indices of the blocks of an elementary integrand. -/
def elemGridIdx (e : ElemIntegrand 𝓖 ι) : Finset ι := (e.map fun bl => bl.i).toFinset

/-- The left end of a block is a grid point. -/
lemma mem_elemGridPts_a {e : ElemIntegrand 𝓖 ι} {bl : ElemBlock 𝓖 ι} (h : bl ∈ e) :
    bl.a ∈ elemGridPts e := by
  classical
  simp only [elemGridPts, Finset.mem_union, List.mem_toFinset, List.mem_map]
  exact Or.inl ⟨bl, h, rfl⟩

/-- The right end of a block is a grid point. -/
lemma mem_elemGridPts_b {e : ElemIntegrand 𝓖 ι} {bl : ElemBlock 𝓖 ι} (h : bl ∈ e) :
    bl.b ∈ elemGridPts e := by
  classical
  simp only [elemGridPts, Finset.mem_union, List.mem_toFinset, List.mem_map]
  exact Or.inr ⟨bl, h, rfl⟩

/-- The index of a block belongs to `elemGridIdx`. -/
lemma mem_elemGridIdx {e : ElemIntegrand 𝓖 ι} {bl : ElemBlock 𝓖 ι} (h : bl ∈ e) :
    bl.i ∈ elemGridIdx e := by
  classical
  simp only [elemGridIdx, List.mem_toFinset, List.mem_map]
  exact ⟨bl, h, rfl⟩

open Classical in
/-- `toFun` of a list with a block in front. -/
lemma elemGrid_toFun_cons (bl : ElemBlock 𝓖 ι) (e : ElemIntegrand 𝓖 ι) (i : ι) (r : ℝ)
    (ω : Ω) : ElemIntegrand.toFun (bl :: e) i r ω =
      (if bl.i = i ∧ (bl.a : ℝ) < r ∧ r ≤ bl.b then bl.ξ ω else 0) + e.toFun i r ω := by
  simp [ElemIntegrand.toFun]

/-- `eᵢ(r) = 0` for an index `i` carrying no block. -/
lemma elemGrid_toFun_eq_zero (e : ElemIntegrand 𝓖 ι) {i : ι} (hi : i ∉ elemGridIdx e)
    (r : ℝ) (ω : Ω) : e.toFun i r ω = 0 := by
  induction e with
  | nil => exact ElemIntegrand.toFun_nil i r ω
  | cons bl e ih =>
    rw [elemGrid_toFun_cons, ih (fun h => hi ?_)]
    · have : bl.i ≠ i := fun h' => hi (h' ▸ mem_elemGridIdx List.mem_cons_self)
      simp [this]
    · classical
      simp only [elemGridIdx, List.mem_toFinset, List.mem_map] at h ⊢
      obtain ⟨b, hb, rfl⟩ := h
      exact ⟨b, List.mem_cons_of_mem _ hb, rfl⟩

/-- `eᵢ(r) = 0` for `r` outside `(min P, max P]`: if `r ≤ p` for all endpoints `p`, or if
`p < r` for all endpoints `p`. -/
lemma elemGrid_toFun_eq_zero_of_out (e : ElemIntegrand 𝓖 ι) (i : ι) {r : ℝ}
    (hr : (∀ p ∈ elemGridPts e, r ≤ (p : ℝ)) ∨ (∀ p ∈ elemGridPts e, (p : ℝ) < r)) (ω : Ω) :
    e.toFun i r ω = 0 := by
  induction e with
  | nil => exact ElemIntegrand.toFun_nil i r ω
  | cons bl e ih =>
    have hsub : elemGridPts e ⊆ elemGridPts (bl :: e) := by
      classical
      intro p hp
      simp only [elemGridPts, Finset.mem_union, List.mem_toFinset, List.mem_map] at hp ⊢
      rcases hp with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
    rw [elemGrid_toFun_cons, ih (hr.imp (fun h p hp => h p (hsub hp))
      (fun h p hp => h p (hsub hp)))]
    have ha := mem_elemGridPts_a (List.mem_cons_self (a := bl) (l := e))
    have hb := mem_elemGridPts_b (List.mem_cons_self (a := bl) (l := e))
    have : ¬ ((bl.a : ℝ) < r ∧ r ≤ bl.b) := by
      rintro ⟨h1, h2⟩
      rcases hr with h | h
      · linarith [h _ ha]
      · linarith [h _ hb]
    simp [this]

/-- If no endpoint lies in `(s, t)`, a block containing `t` (`a < t ≤ b`) starts before `s`. -/
private lemma a_le_of_noPt {e : ElemIntegrand 𝓖 ι} {s t : ℝ≥0}
    (hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p) {bl : ElemBlock 𝓖 ι} (hbl : bl ∈ e)
    (h : (bl.a : ℝ) < t) : bl.a ≤ s := by
  rcases hno _ (mem_elemGridPts_a hbl) with h' | h'
  · exact h'
  · exact absurd (NNReal.coe_le_coe.2 h') (not_le.2 h)

/-- If no endpoint lies in `(s, t)` and `s < r ≤ t`, then `eᵢ(r) = eᵢ(t)`. -/
lemma elemGrid_toFun_eq {e : ElemIntegrand 𝓖 ι} {s t : ℝ≥0}
    (hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p) (i : ι) {r : ℝ} (hsr : (s : ℝ) < r)
    (hrt : r ≤ t) (ω : Ω) : e.toFun i r ω = e.toFun i t ω := by
  induction e with
  | nil => simp [ElemIntegrand.toFun_nil]
  | cons bl e ih =>
    have hno' : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p := by
      intro p hp
      refine hno p ?_
      classical
      simp only [elemGridPts, Finset.mem_union, List.mem_toFinset, List.mem_map] at hp ⊢
      rcases hp with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
    have ha := hno _ (mem_elemGridPts_a (List.mem_cons_self (a := bl) (l := e)))
    have hb := hno _ (mem_elemGridPts_b (List.mem_cons_self (a := bl) (l := e)))
    have hab : (bl.a : ℝ) < r ↔ (bl.a : ℝ) < t := by
      rcases ha with h | h
      · have : (bl.a : ℝ) ≤ s := NNReal.coe_le_coe.2 h
        constructor <;> intro <;> linarith
      · have : (t : ℝ) ≤ bl.a := NNReal.coe_le_coe.2 h
        constructor <;> intro <;> linarith
    have hbb : r ≤ (bl.b : ℝ) ↔ (t : ℝ) ≤ bl.b := by
      rcases hb with h | h
      · have : (bl.b : ℝ) ≤ s := NNReal.coe_le_coe.2 h
        constructor <;> intro <;> linarith
      · have : (t : ℝ) ≤ bl.b := NNReal.coe_le_coe.2 h
        constructor <;> intro <;> linarith
    rw [elemGrid_toFun_cons, elemGrid_toFun_cons, ih hno']
    congr 1
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1.1, hab.1 h1.2.1, hbb.1 h1.2.2⟩ h2
    · exact absurd ⟨h2.1, hab.2 h2.2.1, hbb.2 h2.2.2⟩ h1
    · rfl

/-- If no endpoint lies in `(s, t)`, then `eᵢ(t)` is `𝓖_s`-measurable. -/
lemma elemGrid_measurable_toFun {e : ElemIntegrand 𝓖 ι} {s t : ℝ≥0}
    (hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p) (i : ι) :
    Measurable[𝓖 s] (e.toFun i t) := by
  induction e with
  | nil =>
    show Measurable[𝓖 s] (fun ω => ElemIntegrand.toFun ([] : ElemIntegrand 𝓖 ι) i t ω)
    simp only [ElemIntegrand.toFun_nil]; exact measurable_const
  | cons bl e ih =>
    have hno' : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p := by
      intro p hp
      refine hno p ?_
      classical
      simp only [elemGridPts, Finset.mem_union, List.mem_toFinset, List.mem_map] at hp ⊢
      rcases hp with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
    show Measurable[𝓖 s] (fun ω => ElemIntegrand.toFun (bl :: e) i t ω)
    simp only [elemGrid_toFun_cons bl e i t]
    refine Measurable.add ?_ (ih hno')
    split_ifs with h
    · exact bl.meas.mono (𝓖.mono (a_le_of_noPt hno List.mem_cons_self h.2.1)) le_rfl
    · exact measurable_const

/-- `eᵢ(r)` is bounded, uniformly in `r` and `ω`. -/
lemma elemGrid_toFun_bdd (e : ElemIntegrand 𝓖 ι) : ∃ C, ∀ i r ω, |e.toFun i r ω| ≤ C := by
  induction e with
  | nil => exact ⟨0, fun i r ω => by simp [ElemIntegrand.toFun_nil]⟩
  | cons bl e ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := bl.bdd
    refine ⟨C' + C, fun i r ω => ?_⟩
    rw [elemGrid_toFun_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hC i r ω))
    split_ifs
    · exact hC' ω
    · simpa using (abs_nonneg _).trans (hC' ω)

/-- The values `eᵢ(r)` are essentially bounded. -/
lemma elemGrid_memLp_toFun {μ : Measure Ω} (e : ElemIntegrand 𝓖 ι) {i : ι} {r : ℝ}
    (hm : Measurable (e.toFun i r)) : MemLp (e.toFun i r) ∞ μ := by
  obtain ⟨C, hC⟩ := elemGrid_toFun_bdd e
  exact memLp_top_of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω => by
    simpa [Real.norm_eq_abs] using hC i r ω)

/-- One block between `s` and `t` (no endpoint in `(s, t)`):
`I_t(bl) - I_s(bl) = 𝟙_{a < t ≤ b} ξ (Bᵢ(t) - Bᵢ(s))`. -/
private lemma proc_sub_of_noPt {e : ElemIntegrand 𝓖 ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p) {bl : ElemBlock 𝓖 ι} (hbl : bl ∈ e)
    (B : ι → ℝ → Ω → ℝ) (ω : Ω) :
    bl.proc B t ω - bl.proc B s ω =
      (if (bl.a : ℝ) < t ∧ (t : ℝ) ≤ bl.b then bl.ξ ω else 0) * (B bl.i t ω - B bl.i s ω) := by
  have hab : (bl.a : ℝ) ≤ bl.b := NNReal.coe_le_coe.2 bl.le
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  simp only [ElemBlock.proc]
  split_ifs with h
  · have ha : (bl.a : ℝ) ≤ s := NNReal.coe_le_coe.2 (a_le_of_noPt hno hbl h.1)
    rw [min_eq_left h.2, min_eq_right (h.1.le), min_eq_left (hst'.trans h.2), min_eq_right ha]
    ring
  · rcases hno _ (mem_elemGridPts_b hbl) with hb | hb
    · have hb' : (bl.b : ℝ) ≤ s := NNReal.coe_le_coe.2 hb
      rw [min_eq_right (hb'.trans hst'), min_eq_right (hab.trans (hb'.trans hst')),
        min_eq_right hb', min_eq_right (hab.trans hb')]
      ring
    · have hb' : (t : ℝ) ≤ bl.b := NNReal.coe_le_coe.2 hb
      have ha : (t : ℝ) ≤ bl.a := by
        by_contra ha; exact h ⟨lt_of_not_ge ha, hb'⟩
      rw [min_eq_left hb', min_eq_left ha, min_eq_left (hst'.trans hb'),
        min_eq_left (hst'.trans ha)]
      ring

/-- **Increment of the elementary integral between grid points.** If no endpoint lies in
`(s, t)` and `F` contains the indices of the blocks, then
`I_t(e) - I_s(e) = ∑_{i ∈ F} eᵢ(t) (Bᵢ(t) - Bᵢ(s))`. -/
lemma elemGrid_integral_sub {e : ElemIntegrand 𝓖 ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hno : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p) {F : Finset ι} (hF : elemGridIdx e ⊆ F)
    (B : ι → ℝ → Ω → ℝ) (ω : Ω) :
    e.integral B t ω - e.integral B s ω =
      ∑ i ∈ F, e.toFun i t ω * (B i t ω - B i s ω) := by
  classical
  induction e with
  | nil => simp [ElemIntegrand.integral_nil, ElemIntegrand.toFun_nil]
  | cons bl e ih =>
    have hno' : ∀ p ∈ elemGridPts e, p ≤ s ∨ t ≤ p := by
      intro p hp
      refine hno p ?_
      simp only [elemGridPts, Finset.mem_union, List.mem_toFinset, List.mem_map] at hp ⊢
      rcases hp with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
    have hF' : elemGridIdx e ⊆ F := by
      intro i hi
      refine hF ?_
      simp only [elemGridIdx, List.mem_toFinset, List.mem_map] at hi ⊢
      obtain ⟨b, hb, rfl⟩ := hi
      exact ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
    have hiF : bl.i ∈ F := hF (mem_elemGridIdx List.mem_cons_self)
    rw [ElemIntegrand.integral_cons, ElemIntegrand.integral_cons,
      show bl.proc B t ω + ElemIntegrand.integral e B t ω -
          (bl.proc B s ω + ElemIntegrand.integral e B s ω) =
        (bl.proc B t ω - bl.proc B s ω) +
          (ElemIntegrand.integral e B t ω - ElemIntegrand.integral e B s ω) by ring,
      ih hno' hF', proc_sub_of_noPt hst hno List.mem_cons_self B ω]
    simp only [elemGrid_toFun_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single bl.i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd hiF h

end QSSEPtoKPZ
