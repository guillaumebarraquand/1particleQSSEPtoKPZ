/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Defs
public import QSSEPtoKPZ.ItoIntegral.Increments
public import QSSEPtoKPZ.ItoIntegral.ListSum

/-!
# Elementary integrands and their stochastic integrals (package C, task C1)

INTERFACE FILE (task I0 of Stage 2): the definitions below are complete; the theorems are
frozen interfaces, proved by task C1. See `docs/stage2-design.md`, Section 2.2 (design
decisions C-1, C-2), and `docs/stage2-interfaces.md`.

We integrate families `h : ι → ℝ → Ω → ℝ` (indexed by a type `ι`, in practice the countable
`ℤ × Fin 2`) against a Brownian family `B : ι → ℝ → Ω → ℝ`:
`I_t(h) = ∑ᵢ ∫_0^t hᵢ(s) dBᵢ(s)`. Only times `s > 0` matter for the integrand.

* `ElemBlock 𝓖 ι`: a block `ξ 𝟙_{(a,b]}(s) eᵢ`, with `a ≤ b` and `ξ` bounded and
  `𝓖_a`-measurable.
* `ElemIntegrand 𝓖 ι`: a finite list of blocks (overlaps allowed); `toFun` the family it
  represents, `integral B t` its stochastic integral `∑ ξ (Bᵢ(b ∧ t) - Bᵢ(a ∧ t))`.
* `pathEnergy h T ω = ∫_0^T ∑ᵢ hᵢ(s, ω)² ds` and `energy μ h T = 𝔼 ∫_0^T ∑ᵢ hᵢ(s)² ds`, in
  `[0, ∞]`.
* Interfaces: adaptedness, continuity, `L^p`, martingale property, bracket, cross bracket and
  isometry of the elementary integral.

Proofs (task C1). For one block, `I_t - I_s = ξ ΔBᵢ(u, v)` with `u = a ∨ s ≥ s`
(`ElemBlock.proc_sub`); for two blocks, the increment of `∫_0^t ∑ᵢ blᵢ bl'ᵢ` is
`𝟙_{i=i'} ξ ξ' |(u, v] ∩ (u', v']|` (`ElemBlock.ov_sub`). The moments of Brownian increments
against the past (`Increments.lean`) then give `∫_A (I_t I'_t - ∫_0^t ∑ᵢ blᵢ bl'ᵢ)` independent
of `t ≥ s` for `A ∈ 𝓖_s` (`ElemBlock.setIntegral_pairProc`). Pathwise, `∑ᵢ eᵢ e'ᵢ` is a finite
double sum over pairs of blocks (`hasSum_toFun_mul`, `bracket_eq`), and everything is summed over
the blocks with `SetIntEq.list_sum` (`ListSum.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Definitions -/

/-- One block `ξ 𝟙_{(a,b]}(s) eᵢ` of an elementary integrand: `0 ≤ a ≤ b`, an index `i`, and a
bounded `𝓖_a`-measurable random variable `ξ`. -/
structure ElemBlock (𝓖 : Filtration ℝ≥0 mΩ) (ι : Type*) where
  /-- Left end of the time interval `(a, b]`. -/
  a : ℝ≥0
  /-- Right end of the time interval `(a, b]`. -/
  b : ℝ≥0
  /-- The interval is not reversed. -/
  le : a ≤ b
  /-- The index of the Brownian motion. -/
  i : ι
  /-- The random coefficient. -/
  ξ : Ω → ℝ
  /-- The coefficient is known at time `a`. -/
  meas : Measurable[𝓖 a] ξ
  /-- The coefficient is bounded. -/
  bdd : ∃ C, ∀ ω, |ξ ω| ≤ C

/-- An elementary integrand: a finite list of blocks (overlaps allowed; the represented
integrand is the sum of the blocks). -/
abbrev ElemIntegrand (𝓖 : Filtration ℝ≥0 mΩ) (ι : Type*) := List (ElemBlock 𝓖 ι)

namespace ElemIntegrand

variable {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*}

open Classical in
/-- The family `(hᵢ(s, ω))` represented by an elementary integrand: the sum of its blocks
`ξ 𝟙_{(a,b]}(s) 𝟙_{i = bl.i}`. It vanishes for `s ≤ 0`. -/
def toFun (e : ElemIntegrand 𝓖 ι) : ι → ℝ → Ω → ℝ :=
  fun i s ω => (e.map fun bl =>
    if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0).sum

/-- The stochastic integral of an elementary integrand on `[0, t]`:
`∑_{blocks} ξ (B_i(b ∧ t) - B_i(a ∧ t))`. It vanishes for `t ≤ 0`. -/
def integral (e : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (e.map fun bl => bl.ξ ω * (B bl.i (min t bl.b) ω - B bl.i (min t bl.a) ω)).sum

/-- The block `ξ 𝟙_{(a,b]} eᵢ` multiplied by a constant `c`. -/
def _root_.QSSEPtoKPZ.ElemBlock.smul (c : ℝ) (bl : ElemBlock 𝓖 ι) : ElemBlock 𝓖 ι where
  a := bl.a
  b := bl.b
  le := bl.le
  i := bl.i
  ξ := fun ω => c * bl.ξ ω
  meas := bl.meas.const_mul c
  bdd := by
    obtain ⟨C, hC⟩ := bl.bdd
    exact ⟨|c| * C, fun ω => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩

/-- An elementary integrand multiplied by a constant `c` (each coefficient `ξ` becomes
`c ξ`). -/
def smul (c : ℝ) (e : ElemIntegrand 𝓖 ι) : ElemIntegrand 𝓖 ι := e.map (ElemBlock.smul c)

/-! ### Algebraic lemmas (proved) -/

lemma toFun_nil (i : ι) (s : ℝ) (ω : Ω) : toFun ([] : ElemIntegrand 𝓖 ι) i s ω = 0 := by
  simp [toFun]

lemma toFun_append (e e' : ElemIntegrand 𝓖 ι) (i : ι) (s : ℝ) (ω : Ω) :
    toFun (e ++ e') i s ω = e.toFun i s ω + e'.toFun i s ω := by
  simp [toFun]

lemma integral_nil (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    integral ([] : ElemIntegrand 𝓖 ι) B t ω = 0 := by
  simp [integral]

lemma integral_append (e e' : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    integral (e ++ e') B t ω = e.integral B t ω + e'.integral B t ω := by
  simp [integral]

open Classical in
lemma toFun_smul (c : ℝ) (e : ElemIntegrand 𝓖 ι) (i : ι) (s : ℝ) (ω : Ω) :
    (e.smul c).toFun i s ω = c * e.toFun i s ω := by
  unfold toFun smul
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro bl _
  show (if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then c * bl.ξ ω else 0) =
    c * (if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0)
  split_ifs <;> simp

lemma integral_smul (c : ℝ) (e : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (e.smul c).integral B t ω = c * e.integral B t ω := by
  induction e with
  | nil => simp [smul, integral]
  | cons bl e ih =>
    simp only [smul, integral, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    simp only [ElemBlock.smul]
    ring

/-- The elementary integral vanishes at times `t ≤ 0`. -/
lemma integral_of_nonpos (e : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) {t : ℝ} (ht : t ≤ 0)
    (ω : Ω) : e.integral B t ω = 0 := by
  induction e with
  | nil => simp [integral]
  | cons bl e ih =>
    simp only [integral, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, min_eq_left (ht.trans (NNReal.coe_nonneg bl.b)),
      min_eq_left (ht.trans (NNReal.coe_nonneg bl.a))]
    ring

end ElemIntegrand

/-- `∫_0^T ∑ᵢ hᵢ(s, ω)² ds`, pathwise, in `[0, ∞]` (only times `s ∈ (0, T]` matter). -/
def pathEnergy {ι : Type*} (h : ι → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioc 0 T, ∑' i, ‖h i s ω‖ₑ ^ 2

/-- The energy `𝔼 ∫_0^T ∑ᵢ hᵢ(s)² ds` of a family `h` on `[0, T]`, in `[0, ∞]`. -/
def energy {ι : Type*} (μ : Measure Ω) (h : ι → ℝ → Ω → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, pathEnergy h T ω ∂μ

/-! ### Auxiliary results on blocks (task C1) -/

namespace ElemBlock

variable {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} {μ : Measure Ω} {B : ι → ℝ → Ω → ℝ}

/-- The elementary integral of one block: `ξ (Bᵢ(t ∧ b) - Bᵢ(t ∧ a))`. -/
def proc (bl : ElemBlock 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  bl.ξ ω * (B bl.i (min t bl.b) ω - B bl.i (min t bl.a) ω)

/-- The length `|(a, b] ∩ (a', b'] ∩ (0, t]|` of the common support of two blocks before `t`. -/
def ov (bl bl' : ElemBlock 𝓖 ι) (t : ℝ) : ℝ :=
  volume.real (Set.Ioc (bl.a : ℝ) bl.b ∩ Set.Ioc (bl'.a : ℝ) bl'.b ∩ Set.Ioc 0 t)

open Classical in
/-- The coefficient `𝟙_{i = i'} ξ ξ'` of the product of two blocks. -/
def coef (bl bl' : ElemBlock 𝓖 ι) (ω : Ω) : ℝ := if bl.i = bl'.i then bl.ξ ω * bl'.ξ ω else 0

/-- `∑ᵢ blᵢ(r) bl'ᵢ(r) = 𝟙_{(a,b] ∩ (a',b']}(r) 𝟙_{i = i'} ξ ξ'` for two blocks. -/
def pairVal (bl bl' : ElemBlock 𝓖 ι) (ω : Ω) (r : ℝ) : ℝ :=
  (Set.Ioc (bl.a : ℝ) bl.b ∩ Set.Ioc (bl'.a : ℝ) bl'.b).indicator (fun _ => coef bl bl' ω) r

/-- `I_t(bl) I_t(bl') - ∫_0^t ∑ᵢ blᵢ bl'ᵢ` for two blocks (for `t ≥ 0`). -/
def pairProc (bl bl' : ElemBlock 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  bl.proc B t ω * bl'.proc B t ω - ov bl bl' t * coef bl bl' ω

lemma measurable_ξ (bl : ElemBlock 𝓖 ι) : Measurable bl.ξ := bl.meas.mono (𝓖.le _) le_rfl

lemma memLp_ξ (bl : ElemBlock 𝓖 ι) : MemLp bl.ξ ∞ μ := by
  obtain ⟨C, hC⟩ := bl.bdd
  exact memLp_top_of_bound bl.measurable_ξ.aestronglyMeasurable C (ae_of_all _ fun ω => hC ω)

lemma measurable_coef (bl bl' : ElemBlock 𝓖 ι) : Measurable (coef bl bl') := by
  unfold coef; split_ifs
  · exact bl.measurable_ξ.mul bl'.measurable_ξ
  · exact measurable_const

lemma memLp_coef (bl bl' : ElemBlock 𝓖 ι) : MemLp (coef bl bl') ∞ μ := by
  unfold coef; split_ifs
  · exact bl.memLp_ξ.mul bl'.memLp_ξ
  · exact memLp_top_const 0

/-- The block integral at a time `t ≥ 0`, with `ℝ≥0` times. -/
lemma proc_coe (bl : ElemBlock 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    bl.proc B t ω = bl.ξ ω * (B bl.i ((min t bl.b : ℝ≥0) : ℝ) ω -
      B bl.i ((min t bl.a : ℝ≥0) : ℝ) ω) := by
  simp [proc]

/-- The block integral vanishes at times `t ≤ 0`. -/
lemma proc_of_nonpos (bl : ElemBlock 𝓖 ι) (B : ι → ℝ → Ω → ℝ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    bl.proc B t ω = 0 := by
  rw [proc, min_eq_left (ht.trans (NNReal.coe_nonneg bl.b)),
    min_eq_left (ht.trans (NNReal.coe_nonneg bl.a))]
  ring

/-- The block integral is adapted. -/
lemma proc_adapted (hB : IsBrownianFamily 𝓖 B μ) (bl : ElemBlock 𝓖 ι) (t : ℝ≥0) :
    Measurable[𝓖 t] (bl.proc B t) := by
  by_cases h : bl.a ≤ t
  · have e : bl.proc B t = fun ω => bl.ξ ω * (B bl.i ((min t bl.b : ℝ≥0) : ℝ) ω -
        B bl.i ((min t bl.a : ℝ≥0) : ℝ) ω) := funext (proc_coe bl B t)
    rw [e]
    exact (bl.meas.mono (𝓖.mono h) le_rfl).mul
      (((hB.adapted _ _).mono (𝓖.mono (min_le_left _ _)) le_rfl).sub
        ((hB.adapted _ _).mono (𝓖.mono (min_le_left _ _)) le_rfl))
  · push Not at h
    have e : bl.proc B t = fun _ => 0 := by
      funext ω
      rw [proc_coe, min_eq_left h.le, min_eq_left (h.le.trans bl.le)]
      ring
    rw [e]
    exact measurable_const

/-- The block integral has moments of all finite orders. -/
lemma memLp_proc (hB : IsBrownianFamily 𝓖 B μ) (bl : ElemBlock 𝓖 ι) (t : ℝ≥0) {p : ℝ≥0∞}
    (hp : p ≠ ∞) : MemLp (bl.proc B t) p μ := by
  have hX := hB.memLp_incr bl.i (min_le_min_left t bl.le) hp
  obtain ⟨C, hC⟩ := bl.bdd
  refine hX.of_le_mul (c := C)
    ((bl.proc_adapted hB t).mono (𝓖.le t) le_rfl).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [proc_coe, norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using hC ω) (norm_nonneg _)

/-- The increment of a block integral between `s ≤ t` is `ξ ΔBᵢ(u, v)` with `u = a ∨ s` and
`v = u ∨ (b ∧ t)`. -/
lemma proc_sub (bl : ElemBlock 𝓖 ι) (B : ι → ℝ → Ω → ℝ) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    bl.proc B t ω = bl.proc B s ω + bl.ξ ω *
      (B bl.i ((max (max bl.a s) (min bl.b t) : ℝ≥0) : ℝ) ω -
        B bl.i ((max bl.a s : ℝ≥0) : ℝ) ω) := by
  rw [proc_coe, proc_coe]
  have hab := bl.le
  rcases le_total t bl.a with h1 | h1
  · have h2 : s ≤ bl.a := hst.trans h1
    rw [min_eq_left h1, min_eq_left (h1.trans hab), min_eq_left h2, min_eq_left (h2.trans hab),
      max_eq_left h2, min_eq_right (h1.trans hab), max_eq_left h1]
    ring
  rcases le_total s bl.a with h2 | h2
  · rw [min_eq_right h1, min_eq_left h2, min_eq_left (h2.trans hab), max_eq_left h2,
      max_eq_right (le_min hab h1), min_comm t]
    ring
  rw [min_eq_right h1, min_eq_right h2, max_eq_right h2]
  rcases le_total s bl.b with h3 | h3
  · rw [min_eq_left h3, max_eq_right (le_min h3 hst), min_comm t]
    ring
  · rw [min_eq_right h3, min_eq_right (h3.trans hst), min_eq_left (h3.trans hst),
      max_eq_left h3]
    ring

/-- `(a, b] ∩ (s, t] = (u, v]` with `u = a ∨ s`, `v = u ∨ (b ∧ t)`. -/
lemma Ioc_inter_Ioc_coe (a b s t : ℝ≥0) :
    Set.Ioc (a : ℝ) b ∩ Set.Ioc (s : ℝ) t =
      Set.Ioc ((max a s : ℝ≥0) : ℝ) ((max (max a s) (min b t) : ℝ≥0) : ℝ) := by
  rw [Set.Ioc_inter_Ioc]
  ext x
  simp only [Set.mem_Ioc, NNReal.coe_max, NNReal.coe_min, le_max_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact (not_le.2 h1 (le_max_iff.2 h2)).elim
    · exact ⟨h1, h2⟩

/-- The increment of the overlap length between `s ≤ t`. -/
lemma ov_sub (bl bl' : ElemBlock 𝓖 ι) {s t : ℝ≥0} (hst : s ≤ t) :
    ov bl bl' t = ov bl bl' s +
      volume.real (Set.Ioc ((max bl.a s : ℝ≥0) : ℝ) ((max (max bl.a s) (min bl.b t) : ℝ≥0) : ℝ) ∩
        Set.Ioc ((max bl'.a s : ℝ≥0) : ℝ) ((max (max bl'.a s) (min bl'.b t) : ℝ≥0) : ℝ)) := by
  rw [← Ioc_inter_Ioc_coe, ← Ioc_inter_Ioc_coe]
  set S := Set.Ioc (bl.a : ℝ) bl.b ∩ Set.Ioc (bl'.a : ℝ) bl'.b
  have e : Set.Ioc (bl.a : ℝ) bl.b ∩ Set.Ioc (s : ℝ) t ∩ (Set.Ioc (bl'.a : ℝ) bl'.b ∩
      Set.Ioc (s : ℝ) t) = S ∩ Set.Ioc (s : ℝ) t := by
    ext x; simp only [S, Set.mem_inter_iff]; tauto
  have hsplit : Set.Ioc (0 : ℝ) t = Set.Ioc (0 : ℝ) s ∪ Set.Ioc (s : ℝ) t :=
    (Set.Ioc_union_Ioc_eq_Ioc s.2 (by exact_mod_cast hst)).symm
  have hfin : ∀ x y : ℝ, volume (S ∩ Set.Ioc x y) ≠ ∞ := fun x y =>
    ((measure_mono Set.inter_subset_right).trans_lt measure_Ioc_lt_top).ne
  rw [e, ov, ov, hsplit, Set.inter_union_distrib_left,
    measureReal_union ((Set.Ioc_disjoint_Ioc_of_le le_rfl).mono Set.inter_subset_right
      Set.inter_subset_right) ((measurableSet_Ioc.inter measurableSet_Ioc).inter measurableSet_Ioc)
      (hfin _ _) (hfin _ _)]

/-- **Martingale property of a block integral**, in integrated form. -/
lemma setIntegral_proc (hB : IsBrownianFamily 𝓖 B μ) [IsProbabilityMeasure μ]
    (bl : ElemBlock 𝓖 ι) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, bl.proc B t ω ∂μ = ∫ ω in A, bl.proc B s ω ∂μ := by
  simp_rw [proc_sub bl B hst]
  exact hB.setIntegral_add_mul_incr hA bl.i (le_max_right _ _) (le_max_left _ _)
    (bl.meas.mono (𝓖.mono (le_max_left _ _)) le_rfl) bl.memLp_ξ
    ((bl.memLp_proc hB s (by simp)).integrable le_rfl)

/-- **Bracket of two blocks**, in integrated form: `∫_A (I_t I'_t - ∫_0^t ∑ᵢ blᵢ bl'ᵢ)` does not
depend on `t ≥ s` for `A ∈ 𝓖_s`. -/
lemma setIntegral_pairProc (hB : IsBrownianFamily 𝓖 B μ) [IsProbabilityMeasure μ]
    (bl bl' : ElemBlock 𝓖 ι) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, pairProc bl bl' B t ω ∂μ = ∫ ω in A, pairProc bl bl' B s ω ∂μ := by
  simp only [pairProc]
  simp_rw [proc_sub bl B hst, proc_sub bl' B hst, ov_sub bl bl' hst]
  exact hB.setIntegral_pair_step hA bl.i bl'.i (le_max_right _ _) (le_max_left _ _)
    (le_max_right _ _) (le_max_left _ _)
    (bl.meas.mono (𝓖.mono (le_max_left _ _)) le_rfl) bl.memLp_ξ
    (bl'.meas.mono (𝓖.mono (le_max_left _ _)) le_rfl) bl'.memLp_ξ
    (bl.proc_adapted hB s) (bl.memLp_proc hB s (by simp))
    (bl'.proc_adapted hB s) (bl'.memLp_proc hB s (by simp)) _ rfl

end ElemBlock

/-! ### Auxiliary results on lists of blocks (task C1) -/

namespace ElemIntegrand

variable {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} {μ : Measure Ω} {B : ι → ℝ → Ω → ℝ}

lemma integral_cons (bl : ElemBlock 𝓖 ι) (e : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ)
    (ω : Ω) : integral (bl :: e) B t ω = bl.proc B t ω + e.integral B t ω := by
  simp [integral, ElemBlock.proc]

open Classical in
/-- Pathwise, `∑ᵢ eᵢ(r) e'ᵢ(r)` is the finite double sum of the products of blocks. -/
lemma hasSum_toFun_mul (e e' : ElemIntegrand 𝓖 ι) (r : ℝ) (ω : Ω) :
    HasSum (fun i => e.toFun i r ω * e'.toFun i r ω)
      ((e.map fun bl => (e'.map fun bl' => ElemBlock.pairVal bl bl' ω r).sum).sum) := by
  have h : ∀ i, e.toFun i r ω * e'.toFun i r ω = (e.map fun bl => (e'.map fun bl' =>
      (if bl.i = i ∧ (bl.a : ℝ) < r ∧ r ≤ bl.b then bl.ξ ω else 0) *
        (if bl'.i = i ∧ (bl'.a : ℝ) < r ∧ r ≤ bl'.b then bl'.ξ ω else 0)).sum).sum := by
    intro i
    simp only [toFun]
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun bl _ => ?_
    rw [← List.sum_map_mul_left]
  simp_rw [h]
  refine hasSum_list_sum e fun bl _ => hasSum_list_sum e' fun bl' _ => ?_
  convert hasSum_ite_eq bl.i (ElemBlock.pairVal bl bl' ω r) using 1
  funext i
  simp only [ElemBlock.pairVal, ElemBlock.coef, Set.indicator_apply, Set.mem_inter_iff,
    Set.mem_Ioc]
  by_cases h1 : i = bl.i
  · subst h1
    by_cases hr1 : (bl.a : ℝ) < r ∧ r ≤ bl.b <;> by_cases hr2 : (bl'.a : ℝ) < r ∧ r ≤ bl'.b <;>
      by_cases h2 : bl'.i = bl.i <;> simp [hr1, hr2, h2, @eq_comm _ bl.i bl'.i]
  · simp [h1, Ne.symm h1]

/-- The function `r ↦ ∏` of two blocks is integrable. -/
lemma integrable_pairVal (bl bl' : ElemBlock 𝓖 ι) (ω : Ω) :
    Integrable (ElemBlock.pairVal bl bl' ω) volume :=
  (integrable_indicator_iff (measurableSet_Ioc.inter measurableSet_Ioc)).2
    (integrableOn_const ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top).ne)

lemma integral_pairVal (bl bl' : ElemBlock 𝓖 ι) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, ElemBlock.pairVal bl bl' ω r =
      ElemBlock.ov bl bl' t * ElemBlock.coef bl bl' ω := by
  rw [intervalIntegral.integral_of_le ht]
  unfold ElemBlock.pairVal
  rw [integral_indicator_const _ (measurableSet_Ioc.inter measurableSet_Ioc),
    measureReal_restrict_apply (measurableSet_Ioc.inter measurableSet_Ioc), smul_eq_mul]
  rfl

/-- `r ↦ ∑ᵢ eᵢ(r) e'ᵢ(r)` is integrable on every interval. -/
lemma intervalIntegrable_bracket (e e' : ElemIntegrand 𝓖 ι) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun r => ∑' i, e.toFun i r ω * e'.toFun i r ω) volume a b := by
  simp_rw [fun r => (hasSum_toFun_mul e e' r ω).tsum_eq]
  exact (intervalIntegral_list_sum e fun bl _ => (intervalIntegral_list_sum e' fun bl' _ =>
    (integrable_pairVal bl bl' ω).intervalIntegrable).1).1

/-- The bracket `∫_0^t ∑ᵢ eᵢ e'ᵢ` as a finite double sum over blocks. -/
lemma bracket_eq (e e' : ElemIntegrand 𝓖 ι) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e'.toFun i r ω =
      (e.map fun bl => (e'.map fun bl' =>
        ElemBlock.ov bl bl' t * ElemBlock.coef bl bl' ω).sum).sum := by
  simp_rw [fun r => (hasSum_toFun_mul e e' r ω).tsum_eq]
  have h' : ∀ bl ∈ e, IntervalIntegrable (fun r => (e'.map fun bl' =>
      ElemBlock.pairVal bl bl' ω r).sum) volume 0 t := fun bl _ =>
    (intervalIntegral_list_sum e' fun bl' _ => (integrable_pairVal bl bl' ω).intervalIntegrable).1
  rw [(intervalIntegral_list_sum e h').2]
  congr 1
  refine List.map_congr_left fun bl _ => ?_
  rw [(intervalIntegral_list_sum e' fun bl' _ =>
    (integrable_pairVal bl bl' ω).intervalIntegrable).2]
  congr 1
  exact List.map_congr_left fun bl' _ => integral_pairVal bl bl' ω ht

/-- `I_t(e) I_t(e') - ∫_0^t ∑ᵢ eᵢ e'ᵢ` as a finite double sum over pairs of blocks. -/
lemma mul_sub_bracket_eq (e e' : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (ω : Ω) {t : ℝ}
    (ht : 0 ≤ t) :
    e.integral B t ω * e'.integral B t ω -
        ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e'.toFun i r ω =
      (e.map fun bl => (e'.map fun bl' => ElemBlock.pairProc bl bl' B t ω).sum).sum := by
  rw [bracket_eq e e' ω ht]
  simp only [ElemBlock.pairProc, list_sum_map_sub]
  congr 1
  simp only [integral]
  rw [← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun bl _ => ?_
  rw [← List.sum_map_mul_left]
  rfl

/-- The overlap length vanishes before the later start. -/
lemma _root_.QSSEPtoKPZ.ElemBlock.ov_eq_zero (bl bl' : ElemBlock 𝓖 ι) {s : ℝ≥0}
    (h : s < bl.a ∨ s < bl'.a) : ElemBlock.ov bl bl' s = 0 := by
  have : Set.Ioc (bl.a : ℝ) bl.b ∩ Set.Ioc (bl'.a : ℝ) bl'.b ∩ Set.Ioc 0 s = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨h1, -⟩, ⟨h2, -⟩⟩, -, h3⟩
    rcases h with h | h
    · exact absurd (h1.trans_le h3) (not_lt.2 (by exact_mod_cast h.le))
    · exact absurd (h2.trans_le h3) (not_lt.2 (by exact_mod_cast h.le))
  simp [ElemBlock.ov, this]

/-- `I_s(bl) I_s(bl') - ∫_0^s ∑ᵢ blᵢ bl'ᵢ` is `𝓖_s`-measurable. -/
lemma _root_.QSSEPtoKPZ.ElemBlock.measurable_pairProc (hB : IsBrownianFamily 𝓖 B μ)
    (bl bl' : ElemBlock 𝓖 ι) (s : ℝ≥0) : Measurable[𝓖 s] (ElemBlock.pairProc bl bl' B s) := by
  refine ((bl.proc_adapted hB s).mul (bl'.proc_adapted hB s)).sub ?_
  by_cases h : bl.a ≤ s ∧ bl'.a ≤ s
  · refine measurable_const.mul ?_
    unfold ElemBlock.coef
    split_ifs
    · exact (bl.meas.mono (𝓖.mono h.1) le_rfl).mul (bl'.meas.mono (𝓖.mono h.2) le_rfl)
    · exact measurable_const
  · rw [not_and_or, not_le, not_le] at h
    simp only [ElemBlock.ov_eq_zero bl bl' h, zero_mul]
    exact measurable_const

lemma _root_.QSSEPtoKPZ.ElemBlock.integrable_pairProc (hB : IsBrownianFamily 𝓖 B μ)
    [IsProbabilityMeasure μ] (bl bl' : ElemBlock 𝓖 ι) (t : ℝ≥0) :
    Integrable (ElemBlock.pairProc bl bl' B t) μ :=
  ((bl.memLp_proc hB t (p := 2) (by simp)).integrable_mul
    (bl'.memLp_proc hB t (p := 2) (by simp))).sub
    (((bl.memLp_coef bl').const_mul _).integrable le_top)

/-- `I(e) I(e') - ∫ ∑ᵢ eᵢ e'ᵢ` satisfies the martingale property in integrated form. -/
lemma setIntEq_mul_sub_bracket (hB : IsBrownianFamily 𝓖 B μ) [IsProbabilityMeasure μ]
    (e e' : ElemIntegrand 𝓖 ι) {s t : ℝ≥0} (hst : s ≤ t) :
    SetIntEq μ (𝓖 s)
      (fun ω => e.integral B t ω * e'.integral B t ω -
        ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e'.toFun i r ω)
      (fun ω => e.integral B s ω * e'.integral B s ω -
        ∫ r in (0 : ℝ)..s, ∑' i, e.toFun i r ω * e'.toFun i r ω) := by
  refine (SetIntEq.list_sum e fun bl _ => SetIntEq.list_sum e' fun bl' _ =>
    ⟨bl.integrable_pairProc hB bl' t, bl.integrable_pairProc hB bl' s,
      (bl.measurable_pairProc hB bl' s).stronglyMeasurable,
      fun _ hA => bl.setIntegral_pairProc hB bl' hst hA⟩).congr
    (fun ω => mul_sub_bracket_eq e e' B ω t.2) (fun ω => mul_sub_bracket_eq e e' B ω s.2)

/-- The bracket `ω ↦ ∫_0^t ∑ᵢ eᵢ e'ᵢ` is integrable. -/
lemma integrable_bracket [IsFiniteMeasure μ] (e e' : ElemIntegrand 𝓖 ι) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e'.toFun i r ω) μ := by
  rw [show (fun ω => ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e'.toFun i r ω) = _ from
    funext fun ω => bracket_eq e e' ω ht]
  exact integrable_list_sum e fun bl _ => integrable_list_sum e' fun bl' _ =>
    ((bl.memLp_coef bl').const_mul _).integrable le_top

/-- The elementary integral at times `t ≥ 0` has moments of all finite orders. -/
lemma memLp_integral_coe (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) (t : ℝ≥0)
    {p : ℝ≥0∞} (hp : p ≠ ∞) : MemLp (e.integral B t) p μ := by
  induction e with
  | nil =>
    have e0 : integral ([] : ElemIntegrand 𝓖 ι) B t = 0 := funext fun ω => integral_nil B t ω
    rw [e0]
    exact MemLp.zero
  | cons bl e ih =>
    have e1 : integral (bl :: e) B t = fun ω => bl.proc B t ω + integral e B t ω :=
      funext (integral_cons bl e B t)
    rw [e1]
    exact (bl.memLp_proc hB t hp).add ih

end ElemIntegrand

/-! ### Interfaces (task C1) -/

namespace ElemIntegrand

variable {ι : Type*} {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ι → ℝ → Ω → ℝ}

set_option linter.unusedSectionVars false in
/-- The elementary integral is adapted, for every `ω`: `I_t(e)` is `𝓖_t`-measurable. -/
theorem integral_adapted (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) (t : ℝ≥0) :
    Measurable[𝓖 t] (e.integral B t) := by
  induction e with
  | nil =>
    have e0 : integral ([] : ElemIntegrand 𝓖 ι) B t = fun _ => 0 :=
      funext fun ω => integral_nil B t ω
    rw [e0]
    exact measurable_const
  | cons bl e ih =>
    rw [funext (integral_cons bl e B t)]
    exact (bl.proc_adapted hB t).add ih

set_option linter.unusedSectionVars false in
/-- Almost surely, `t ↦ I_t(e)` is continuous on `[0, ∞)`. -/
theorem integral_continuous (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) :
    ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => e.integral B t ω := by
  induction e with
  | nil => exact ae_of_all _ fun ω => by simpa [integral] using continuous_const
  | cons bl e ih =>
    filter_upwards [hB.continuous bl.i, ih] with ω h1 h2
    simp_rw [integral_cons, ElemBlock.proc_coe]
    exact (continuous_const.mul ((h1.comp (continuous_id.min continuous_const)).sub
      (h1.comp (continuous_id.min continuous_const)))).add h2

set_option linter.unusedSectionVars false in
/-- `I_t(e) ∈ L^p` for every finite `p`. -/
theorem memLp_integral (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) (t : ℝ)
    {p : ℝ≥0∞} (hp : p ≠ ∞) : MemLp (e.integral B t) p μ := by
  rcases le_total t 0 with ht | ht
  · rw [funext (integral_of_nonpos e B ht)]
    exact MemLp.zero
  · have := memLp_integral_coe hB e t.toNNReal hp
    rwa [Real.coe_toNNReal t ht] at this

/-- **Elementary bracket.** For every `T`, the elementary integral `I(e)` is a continuous `L²`
martingale on `[0, T]` with bracket `⟨I(e)⟩_t = ∫_0^t ∑ᵢ eᵢ(s)² ds`. -/
theorem hasBracket_integral (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) (T : ℝ) :
    HasBracket T 𝓖 (e.integral B) (fun t ω => ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω ^ 2) μ := by
  have hsq : ∀ (t : ℝ) ω, ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω ^ 2 =
      ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e.toFun i r ω := fun t ω => by simp_rw [sq]
  have hf : ∀ ω a b, IntervalIntegrable (fun r => ∑' i, e.toFun i r ω ^ 2) volume a b :=
    fun ω a b => by simpa only [sq] using intervalIntegrable_bracket e e ω a b
  refine
    { cont := ?_
      memLp := fun t _ => memLp_integral hB e t (by simp)
      condExp := fun s t hst _ => ?_
      integrable_bracket := fun t _ => ?_
      zero := ae_of_all _ fun ω => by simp
      mono := ae_of_all _ fun ω => ?_
      cont_bracket := ae_of_all _ fun ω =>
        (intervalIntegral.continuous_primitive (hf ω) 0).continuousOn
      condExp_sq := fun s t hst _ => ?_ }
  · filter_upwards [integral_continuous hB e] with ω h
    refine ((h.comp continuous_real_toNNReal).continuousOn).congr fun t ht => ?_
    simp only [Function.comp_apply, Real.coe_toNNReal t ht.1]
  · exact (SetIntEq.list_sum e fun bl _ =>
      ⟨(bl.memLp_proc hB t (p := 1) (by simp)).integrable le_rfl,
        (bl.memLp_proc hB s (p := 1) (by simp)).integrable le_rfl,
        (bl.proc_adapted hB s).stronglyMeasurable,
        fun _ hA => bl.setIntegral_proc hB hst hA⟩).condExp_ae_eq (𝓖.le s)
  · simp_rw [hsq]
    exact integrable_bracket e e t.2
  · intro x hx y hy hxy
    simp only
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf ω 0 x) (hf ω x y)]
    exact le_add_of_nonneg_right
      (intervalIntegral.integral_nonneg hxy fun r _ => tsum_nonneg fun i => sq_nonneg _)
  · simp_rw [sq]
    exact (setIntEq_mul_sub_bracket hB e e hst).condExp_ae_eq (𝓖.le s)

/-- **Elementary cross bracket.** For `s ≤ t`,
`𝔼[I_t(e) I_t(e') - ∫_0^t ∑ᵢ eᵢ e'ᵢ | 𝓖_s] = I_s(e) I_s(e') - ∫_0^s ∑ᵢ eᵢ e'ᵢ`. -/
theorem condExp_integral_mul (hB : IsBrownianFamily 𝓖 B μ) (e e' : ElemIntegrand 𝓖 ι)
    {s t : ℝ≥0} (hst : s ≤ t) :
    μ[fun ω => e.integral B t ω * e'.integral B t ω -
        ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e'.toFun i r ω | 𝓖 s] =ᵐ[μ]
      fun ω => e.integral B s ω * e'.integral B s ω -
        ∫ r in (0 : ℝ)..s, ∑' i, e.toFun i r ω * e'.toFun i r ω :=
  (setIntEq_mul_sub_bracket hB e e' hst).condExp_ae_eq (𝓖.le s)

/-- **Elementary Itô isometry**, in `[0, ∞]`: `𝔼[I_t(e)²] = 𝔼 ∫_0^t ∑ᵢ eᵢ(s)² ds` (both sides
vanish for `t ≤ 0`). -/
theorem lintegral_integral_sq (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (e.integral B t ω ^ 2) ∂μ = energy μ e.toFun t := by
  rcases le_or_gt t 0 with ht | ht
  · simp [integral_of_nonpos e B ht, energy, pathEnergy, Set.Ioc_eq_empty (not_lt.2 ht)]
  have hCnn : ∀ ω, 0 ≤ ∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e.toFun i r ω := fun ω =>
    intervalIntegral.integral_nonneg ht.le fun r _ => tsum_nonneg fun i => mul_self_nonneg _
  have hpath : ∀ ω, pathEnergy e.toFun t ω =
      ENNReal.ofReal (∫ r in (0 : ℝ)..t, ∑' i, e.toFun i r ω * e.toFun i r ω) := by
    intro ω
    have h1 : ∀ r, ∑' i, ‖e.toFun i r ω‖ₑ ^ 2 =
        ENNReal.ofReal (∑' i, e.toFun i r ω * e.toFun i r ω) := by
      intro r
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => mul_self_nonneg _)
        (hasSum_toFun_mul e e r ω).summable]
      congr 1
      funext i
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, sq]
    simp_rw [pathEnergy, h1, intervalIntegral.integral_of_le ht.le]
    exact (ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_bracket e e ω 0 t).1
      (ae_of_all _ fun r => tsum_nonneg fun i => mul_self_nonneg _)).symm
  have hI2 : MemLp (e.integral B t) 2 μ := memLp_integral hB e t (by simp)
  have hCi := integrable_bracket (μ := μ) e e ht.le
  have hzero := (setIntEq_mul_sub_bracket hB e e (zero_le (a := t.toNNReal))).2.2.2 Set.univ
    MeasurableSet.univ
  simp only [setIntegral_univ, Real.coe_toNNReal t ht.le, NNReal.coe_zero,
    integral_of_nonpos e B le_rfl, mul_zero, intervalIntegral.integral_same, sub_zero,
    integral_zero] at hzero
  rw [integral_sub (f := fun ω => e.integral B t ω * e.integral B t ω)
    (hI2.integrable_mul hI2) hCi, sub_eq_zero] at hzero
  rw [energy, lintegral_congr hpath, ← ofReal_integral_eq_lintegral_ofReal hCi
    (ae_of_all _ hCnn), ← ofReal_integral_eq_lintegral_ofReal hI2.integrable_sq
    (ae_of_all _ fun ω => sq_nonneg _)]
  simp_rw [sq]
  rw [hzero]

end ElemIntegrand

end QSSEPtoKPZ
