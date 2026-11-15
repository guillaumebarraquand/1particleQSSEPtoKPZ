/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Basic.Denumerable

/-!
# The countable family of test functions (package H, task H1)

INTERFACE FILE (task I0' of Stage 3): the statements below are interfaces, proved by task H1.
See `docs/stage3-design.md`, Sections 1.2 (a) and 2.2, and `docs/stage3-interfaces.md`.

Let `s = Real.smoothTransition` (smooth, nondecreasing, `0` on `(-∞, 0]`, `1` on `[1, ∞)`) and
`β(x) = s(x+1) - s(x)`. Then `β` is smooth, `0 ≤ β ≤ 1`, `β = 0` outside `(-1, 1)`, and
`∑_{k ∈ ℤ} β(x - k) = 1` (telescoping sum with finitely many nonzero terms).

The countable family of test functions is `f₀ = 1` and `f_{j+1}(x) = β((m+1) x - k)`, where
`(m, k) ∈ ℕ × ℤ` is the `j`-th element of `ℕ × ℤ` (`Denumerable.ofNat`). It determines weak
convergence of finite measures on `ℝ` (task H2), and each `f_j` is in `C_b³` (`isC13_bumpTestRaw`),
so that Proposition 3.1 applies to it.

Names are prefixed by `bump` (the design document calls them `tightBump`, `tightTestRaw`,
`tightTest`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

/-! ### The bump `β` -/

/-- The bump `β(x) = s(x+1) - s(x)`, with `s = Real.smoothTransition`. -/
def bumpBeta (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

/-- `β` is smooth. -/
theorem contDiff_bumpBeta : ContDiff ℝ (⊤ : ℕ∞) bumpBeta :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

/-- `β ≥ 0` (`s` is nondecreasing). **(proved)** -/
theorem bumpBeta_nonneg (x : ℝ) : 0 ≤ bumpBeta x :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

/-- `β ≤ 1` (`0 ≤ s ≤ 1`). **(proved)** -/
theorem bumpBeta_le_one (x : ℝ) : bumpBeta x ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (x + 1)
  have h2 := Real.smoothTransition.nonneg x
  unfold bumpBeta
  linarith

/-- `β` is continuous. **(proved)** -/
theorem continuous_bumpBeta : Continuous bumpBeta :=
  (Real.smoothTransition.continuous.comp (continuous_id.add continuous_const)).sub
    Real.smoothTransition.continuous

/-- `β(x) = 0` for `|x| ≥ 1`. -/
theorem bumpBeta_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : bumpBeta x = 0 := by
  unfold bumpBeta
  rcases le_abs'.1 hx with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le h, sub_self]

/-- Partition of unity: `∑_{k ∈ ℤ} β(x - k) = 1` (as a `HasSum`, so the series converges). -/
theorem hasSum_bumpBeta_sub (x : ℝ) : HasSum (fun k : ℤ => bumpBeta (x - k)) 1 := by
  set k₀ : ℤ := ⌊x⌋
  have h0 : (k₀ : ℝ) ≤ x := Int.floor_le x
  have h1 : x < k₀ + 1 := Int.lt_floor_add_one x
  have hsum : ∑ k ∈ ({k₀, k₀ + 1} : Finset ℤ), bumpBeta (x - k) = 1 := by
    rw [Finset.sum_pair (by omega)]
    unfold bumpBeta
    push_cast
    rw [show x - (k₀ + 1) + 1 = x - k₀ by ring,
      Real.smoothTransition.one_of_one_le (x := x - k₀ + 1) (by linarith),
      Real.smoothTransition.zero_of_nonpos (x := x - (k₀ + 1)) (by linarith)]
    ring
  rw [← hsum]
  refine hasSum_sum_of_ne_finset_zero fun k hk => bumpBeta_eq_zero_of_one_le_abs ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rcases lt_or_gt_of_ne hk.1 with h | h
  · have : (k : ℝ) + 1 ≤ k₀ := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by linarith))
  · have : (k₀ : ℝ) + 2 ≤ k := by
      have : k₀ + 2 ≤ k := by omega
      exact_mod_cast this
    exact le_abs.2 (Or.inr (by linarith))

/-- `β` has compact support (contained in `[-1, 1]`). -/
theorem hasCompactSupport_bumpBeta : HasCompactSupport bumpBeta :=
  HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => by
    refine bumpBeta_eq_zero_of_one_le_abs ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact le_abs.2 (Or.inr (by linarith))
    · exact le_abs.2 (Or.inl h.le)

/-- A smooth compactly supported `g : ℝ → ℝ` has bounded derivatives of order `≤ 3`. -/
private theorem bump_iteratedDeriv_bound_of_hasCompactSupport {g : ℝ → ℝ}
    (hg : HasCompactSupport g) (hg' : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 3, ∀ x, |iteratedDeriv k g x| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_iteratedFDeriv hg' 3
  refine ⟨C, hC0, fun k hk x => ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hC k hk x

/-- The first three derivatives of `β` are bounded (continuous with compact support), and
`β` itself is bounded by `1`. -/
theorem bumpBeta_iteratedDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 3, ∀ x, |iteratedDeriv k bumpBeta x| ≤ C :=
  bump_iteratedDeriv_bound_of_hasCompactSupport hasCompactSupport_bumpBeta contDiff_bumpBeta

/-! ### The family `f_j` -/

/-- The test functions as real functions: `f₀ = 1` and `f_{j+1}(x) = β((m+1) x - k)` where
`(m, k)` is the `j`-th element of `ℕ × ℤ`. -/
def bumpTestRaw (j : ℕ) (x : ℝ) : ℝ :=
  match j with
  | 0 => 1
  | j + 1 => bumpBeta (((Denumerable.ofNat (ℕ × ℤ) j).1 + 1 : ℝ) * x -
      (Denumerable.ofNat (ℕ × ℤ) j).2)

/-- `f₀ = 1`. **(proved)** -/
theorem bumpTestRaw_zero : bumpTestRaw 0 = fun _ => 1 := rfl

/-- Every `x ↦ β((m+1) x - k)`, `m ∈ ℕ`, `k ∈ ℤ`, is a member of the family, with index
`encode (m, k) + 1`. **(proved)** -/
theorem bumpTestRaw_encode_succ (m : ℕ) (k : ℤ) :
    bumpTestRaw (Encodable.encode (m, k) + 1) = fun x => bumpBeta ((m + 1 : ℝ) * x - k) := by
  funext x
  simp only [bumpTestRaw, Denumerable.ofNat_encode]

/-- Each `f_j` is continuous. **(proved)** -/
theorem continuous_bumpTestRaw (j : ℕ) : Continuous (bumpTestRaw j) := by
  cases j with
  | zero => exact continuous_const
  | succ j =>
    exact continuous_bumpBeta.comp ((continuous_const.mul continuous_id).sub continuous_const)

/-- `|f_j| ≤ 1`. **(proved)** -/
theorem abs_bumpTestRaw_le (j : ℕ) (x : ℝ) : |bumpTestRaw j x| ≤ 1 := by
  cases j with
  | zero => simp [bumpTestRaw]
  | succ j =>
    simp only [bumpTestRaw]
    exact abs_le.2 ⟨by linarith [bumpBeta_nonneg (((Denumerable.ofNat (ℕ × ℤ) j).1 + 1 : ℝ) * x -
      (Denumerable.ofNat (ℕ × ℤ) j).2)], bumpBeta_le_one _⟩

/-- The test functions `f_j` as bounded continuous functions (bound `1`). -/
def bumpTest (j : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (bumpTestRaw j) (continuous_bumpTestRaw j) 1
    (fun x => by simpa [Real.norm_eq_abs] using abs_bumpTestRaw_le j x)

/-- The bounded continuous function `bumpTest j` is `bumpTestRaw j`. **(proved)** -/
@[simp] theorem coe_bumpTest (j : ℕ) : ⇑(bumpTest j) = bumpTestRaw j := rfl

/-- Each `f_j` is smooth. -/
theorem contDiff_bumpTestRaw (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bumpTestRaw j) := by
  cases j with
  | zero => exact contDiff_const
  | succ j =>
    exact contDiff_bumpBeta.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The derivatives of order `≤ 3` of each `f_j` are bounded (by `1` for `f₀ = 1`; for
`f_{j+1} = β((m+1) · - k)`, which is smooth with compact support, by compactness). -/
theorem bumpTestRaw_iteratedDeriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ 3, ∀ x, |iteratedDeriv k (bumpTestRaw j) x| ≤ C := by
  cases j with
  | zero =>
    refine ⟨1, zero_le_one, fun k _ x => ?_⟩
    rw [bumpTestRaw_zero]
    rcases k with _ | k <;> simp [iteratedDeriv_const]
  | succ j =>
    refine bump_iteratedDeriv_bound_of_hasCompactSupport ?_ (contDiff_bumpTestRaw _)
    set a : ℝ := (Denumerable.ofNat (ℕ × ℤ) j).1 + 1
    set b : ℝ := ((Denumerable.ofNat (ℕ × ℤ) j).2 : ℝ)
    have ha : 0 < a := by positivity
    refine HasCompactSupport.intro (isCompact_Icc (a := (b - 1) / a) (b := (b + 1) / a))
      fun x hx => ?_
    simp only [bumpTestRaw]
    refine bumpBeta_eq_zero_of_one_le_abs ?_
    simp only [Set.mem_Icc, not_and_or, not_le, div_lt_iff₀ ha, lt_div_iff₀ ha] at hx
    rcases hx with h | h
    · exact le_abs.2 (Or.inr (by linarith))
    · exact le_abs.2 (Or.inl (by linarith))

/-- Each `f_j` is in `C_b³` with a norm `‖f_j‖_{1,3} ≤ C_j`, as a time-independent test function
on every horizon `T` (time derivative `0`); the form needed by Proposition 3.1 and by equation
(5.2) (`IsC13 1 (fun _ => φ) (fun _ _ => 0) C`). -/
theorem isC13_bumpTestRaw (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, IsC13 T (fun _ => bumpTestRaw j) (fun _ _ => 0) C := by
  obtain ⟨C, hC0, hC⟩ := bumpTestRaw_iteratedDeriv_bound j
  have hsm := contDiff_bumpTestRaw j
  refine ⟨4 * C, by positivity, fun T => ⟨fun _ _ => hsm.of_le (WithTop.coe_le_coe.2 le_top),
    fun x t _ => hasDerivWithinAt_const _ _ _,
    ⟨continuousOn_const, fun k _ =>
      ((hsm.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp
        continuous_snd).continuousOn⟩,
    ⟨![C, 0, C, C, C], ?_, fun t _ x => ?_⟩⟩⟩
  · simp only [Fin.sum_univ_five, Matrix.cons_val]
    linarith
  · simp only [Matrix.cons_val, abs_zero]
    have h0 := hC 0 (by norm_num) x
    rw [iteratedDeriv_zero] at h0
    exact ⟨h0, le_rfl, hC 1 (by norm_num) x, hC 2 (by norm_num) x, hC 3 (by norm_num) x⟩

end QSSEPtoKPZ
