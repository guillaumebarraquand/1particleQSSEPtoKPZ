/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite sums over lists, and a criterion for conditional expectations (package C, task C1,
auxiliary)

* `hasSum_list_sum`, `intervalIntegral_list_sum`, `integrable_list_sum`, `list_sum_map_sub`:
  sums over a list of `HasSum`, interval integrals, integrable functions, differences.
* `SetIntEq μ m X Y` (`X`, `Y` integrable, `Y` `m`-measurable, `∫_A X = ∫_A Y` for `A ∈ m`),
  which implies `𝔼[X | m] = Y` (`SetIntEq.condExp_ae_eq`) and is stable under finite sums
  (`SetIntEq.list_sum`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Finite sums over lists -/

/-- Sums of `HasSum` over a list. -/
lemma hasSum_list_sum {α β : Type*} (l : List α) {f : α → β → ℝ} {a : α → ℝ}
    (h : ∀ x ∈ l, HasSum (f x) (a x)) :
    HasSum (fun i => (l.map fun x => f x i).sum) (l.map a).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h x List.mem_cons_self).add (ih fun y hy => h y (List.mem_cons_of_mem x hy))

/-- Interval integrals of sums over a list. -/
lemma intervalIntegral_list_sum {α : Type*} (l : List α) {f : α → ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ l, IntervalIntegrable (f x) volume a b) :
    IntervalIntegrable (fun r => (l.map fun x => f x r).sum) volume a b ∧
      ∫ r in a..b, (l.map fun x => f x r).sum = (l.map fun x => ∫ r in a..b, f x r).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.sum_cons]
    exact ⟨(h x List.mem_cons_self).add h1,
      by rw [intervalIntegral.integral_add (h x List.mem_cons_self) h1, h2]⟩

/-- Integrability of sums over a list. -/
lemma integrable_list_sum {α : Type*} (l : List α) {f : α → Ω → ℝ}
    (h : ∀ x ∈ l, Integrable (f x) μ) :
    Integrable (fun ω => (l.map fun x => f x ω).sum) μ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h x List.mem_cons_self).add (ih fun y hy => h y (List.mem_cons_of_mem x hy))

/-- The sum over a list of differences. -/
lemma list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ### A criterion for conditional expectations -/

/-- `X`, `Y` are integrable, `Y` is `m`-measurable and `∫_A X = ∫_A Y` for every `A ∈ m`; this
implies `𝔼[X | m] = Y` a.s. (`SetIntEq.condExp_ae_eq`). -/
def SetIntEq (μ : Measure Ω) (m : MeasurableSpace Ω) (X Y : Ω → ℝ) : Prop :=
  Integrable X μ ∧ Integrable Y μ ∧ StronglyMeasurable[m] Y ∧
    ∀ A, MeasurableSet[m] A → ∫ ω in A, X ω ∂μ = ∫ ω in A, Y ω ∂μ

namespace SetIntEq

variable {m : MeasurableSpace Ω}

/-- `SetIntEq` gives the conditional expectation. -/
lemma condExp_ae_eq [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X Y : Ω → ℝ} (h : SetIntEq μ m X Y) :
    μ[X | m] =ᵐ[μ] Y :=
  (ae_eq_condExp_of_forall_setIntegral_eq hm h.1 (fun _ _ _ => h.2.1.integrableOn)
    (fun A hA _ => (h.2.2.2 A hA).symm) h.2.2.1.aestronglyMeasurable).symm

/-- `SetIntEq` is stable under pointwise equality. -/
lemma congr {X Y X' Y' : Ω → ℝ} (h : SetIntEq μ m X Y) (hX : ∀ ω, X' ω = X ω)
    (hY : ∀ ω, Y' ω = Y ω) : SetIntEq μ m X' Y' := by
  rw [funext hX, funext hY]
  exact h

/-- `SetIntEq` is stable under addition. -/
lemma add {X Y X' Y' : Ω → ℝ} (h : SetIntEq μ m X Y) (h' : SetIntEq μ m X' Y') :
    SetIntEq μ m (fun ω => X ω + X' ω) (fun ω => Y ω + Y' ω) := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, h.2.2.1.add h'.2.2.1, fun A hA => ?_⟩
  rw [integral_add h.1.integrableOn h'.1.integrableOn,
    integral_add h.2.1.integrableOn h'.2.1.integrableOn, h.2.2.2 A hA, h'.2.2.2 A hA]

/-- `SetIntEq` is stable under finite sums. -/
lemma list_sum {α : Type*} (l : List α) {X Y : α → Ω → ℝ}
    (h : ∀ x ∈ l, SetIntEq μ m (X x) (Y x)) :
    SetIntEq μ m (fun ω => (l.map fun x => X x ω).sum) (fun ω => (l.map fun x => Y x ω).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, stronglyMeasurable_const,
      fun _ _ => rfl⟩
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h x List.mem_cons_self).add (ih fun y hy => h y (List.mem_cons_of_mem x hy))

end SetIntEq

end QSSEPtoKPZ
