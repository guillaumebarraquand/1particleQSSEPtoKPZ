/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import QSSEPtoKPZ.SecondMoments.Generator
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Positivity of the semigroups `e^{tA}` on `ℓ^∞(ℤ)`, and a comparison principle

This file replaces the Markov property of the chain `(R_v)` of Section 4 by analytic facts on
the bounded operators of `ℓ^∞(ℤ)` (see `DEVIATIONS.md`, Section 4).

* An operator `P` is *positive* (`PosOp P`) if it maps nonnegative functions to nonnegative
  functions. An operator `A` is *quasi-positive* (`QuasiPos A`) if `A + c I` is positive for
  some real `c`: its off-diagonal part is nonnegative. The generator `𝓡` and the operators
  `a 𝓡 + b w` (`a, b ≥ 0`, `w ≥ 0`) of Lemma 4.2 are quasi-positive.
* `QuasiPos.posOp_exp`: if `A` is quasi-positive and `t ≥ 0`, then `e^{tA}` is positive.
* `QuasiPos.comparison`: if `d' - A d ≥ 0` on `(0, t)`, then `d(t) ≥ e^{tA} d(0)`; in
  particular `d(t) ≥ 0` when `d(0) ≥ 0` (`QuasiPos.comparison_nonneg`).
* `exp_smul_apply_of_apply_eq_zero`: if `A g = 0` then `e^{tA} g = g`; with `𝓡 𝟏 = 0`
  (`chainOp_one`) this gives `e^{t𝓡} 𝟏 = 𝟏`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- A function in `ℓ^∞(ℤ)` is nonnegative if all its values are. -/
def IsNonneg (g : BddZ) : Prop := ∀ r, 0 ≤ g r

/-- A bounded operator on `ℓ^∞(ℤ)` is positive if it maps nonnegative functions to nonnegative
functions. -/
def PosOp (P : BddZ →L[ℝ] BddZ) : Prop := ∀ g, IsNonneg g → IsNonneg (P g)

/-- A bounded operator `A` on `ℓ^∞(ℤ)` is quasi-positive if `A + c I` is positive for some real
`c` (its off-diagonal part is nonnegative). Such operators generate positive semigroups. -/
def QuasiPos (A : BddZ →L[ℝ] BddZ) : Prop := ∃ c : ℝ, PosOp (A + c • 1)

/-- The coordinate `g ↦ g(r)` on `ℓ^∞(ℤ)`, as a continuous linear form. -/
abbrev coord (r : ℤ) : BddZ →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℤ => ℝ) ∞ r

@[simp] lemma coord_apply (r : ℤ) (g : BddZ) : coord r g = g r := rfl

@[simp] lemma bddZ_add_apply (f g : BddZ) (r : ℤ) : (f + g) r = f r + g r := rfl

@[simp] lemma bddZ_sub_apply (f g : BddZ) (r : ℤ) : (f - g) r = f r - g r := rfl

@[simp] lemma bddZ_smul_apply (c : ℝ) (f : BddZ) (r : ℤ) : (c • f) r = c * f r := rfl

lemma IsNonneg.one : IsNonneg 1 := fun r => by simp [lp.infty_coeFn_one]

lemma posOp_one : PosOp 1 := fun _ hg => hg

lemma PosOp.mul {P Q : BddZ →L[ℝ] BddZ} (hP : PosOp P) (hQ : PosOp Q) : PosOp (P * Q) :=
  fun g hg => hP _ (hQ g hg)

lemma PosOp.add {P Q : BddZ →L[ℝ] BddZ} (hP : PosOp P) (hQ : PosOp Q) : PosOp (P + Q) :=
  fun g hg r => by simpa using add_nonneg (hP g hg r) (hQ g hg r)

lemma PosOp.smul {P : BddZ →L[ℝ] BddZ} (hP : PosOp P) {c : ℝ} (hc : 0 ≤ c) : PosOp (c • P) :=
  fun g hg r => by simpa using mul_nonneg hc (hP g hg r)

lemma PosOp.pow {P : BddZ →L[ℝ] BddZ} (hP : PosOp P) (n : ℕ) : PosOp (P ^ n) := by
  induction n with
  | zero => simpa using posOp_one
  | succ n ih => rw [pow_succ]; exact ih.mul hP

/-- The exponential of a positive operator is positive (each term of its series is). -/
lemma PosOp.exp {P : BddZ →L[ℝ] BddZ} (hP : PosOp P) : PosOp (NormedSpace.exp P) := by
  intro g hg r
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) P).mapL
    ((coord r).comp (ContinuousLinearMap.apply ℝ BddZ g))
  have hterm : ∀ n : ℕ, 0 ≤ ((coord r).comp (ContinuousLinearMap.apply ℝ BddZ g))
      ((n.factorial : ℝ)⁻¹ • P ^ n) := fun n => by
    simpa using mul_nonneg (by positivity) (hP.pow n g hg r)
  simpa using HasSum.nonneg hterm hs

lemma PosOp.quasiPos {P : BddZ →L[ℝ] BddZ} (hP : PosOp P) : QuasiPos P :=
  ⟨0, by
    have : P + (0 : ℝ) • (1 : BddZ →L[ℝ] BddZ) = P := by ext g r; simp
    rw [this]; exact hP⟩

lemma QuasiPos.add {A B : BddZ →L[ℝ] BddZ} (hA : QuasiPos A) (hB : QuasiPos B) :
    QuasiPos (A + B) := by
  obtain ⟨c, hc⟩ := hA
  obtain ⟨d, hd⟩ := hB
  refine ⟨c + d, ?_⟩
  have : A + B + (c + d) • (1 : BddZ →L[ℝ] BddZ) = (A + c • 1) + (B + d • 1) := by
    module
  rw [this]; exact hc.add hd

lemma QuasiPos.smul {A : BddZ →L[ℝ] BddZ} (hA : QuasiPos A) {a : ℝ} (ha : 0 ≤ a) :
    QuasiPos (a • A) := by
  obtain ⟨c, hc⟩ := hA
  refine ⟨a * c, ?_⟩
  have : a • A + (a * c) • (1 : BddZ →L[ℝ] BddZ) = a • (A + c • 1) := by
    module
  rw [this]; exact hc.smul ha

/-- `𝓡 + 6 I` is a positive operator: `(𝓡 + 6I) g(r) = 2 g(r+1) + 2 g(r-1)
+ (2 - 2 𝟙_{|r|=1}) g(r) + 2 𝟙_{|r|=1} g(0)`. -/
lemma quasiPos_chainOp : QuasiPos chainOp := by
  refine ⟨6, fun g hg r => ?_⟩
  have h0 := hg 0; have h1 := hg (r + 1); have h2 := hg (r - 1); have h3 := hg r
  simp only [add_apply, smul_apply, one_apply_eq_self, lp.coeFn_add, lp.coeFn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, chainOp_apply, chainGen]
  split_ifs <;> linarith

/-- The multiplication by a nonnegative `w ∈ ℓ^∞(ℤ)` is a positive operator. -/
lemma posOp_mul {w : BddZ} (hw : IsNonneg w) : PosOp (ContinuousLinearMap.mul ℝ BddZ w) :=
  fun g hg r => by
    simpa [lp.infty_coeFn_mul] using mul_nonneg (hw r) (hg r)

/-- The operators `a 𝓡 + b w` (multiplication by `w`), with `a, b ≥ 0` and `w ≥ 0`, are
quasi-positive. This covers the generator `(n c_n/2) 𝓡 + (n λ_n/2) 𝟙_{|r|=1}` of Lemma 4.2. -/
lemma quasiPos_generator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {w : BddZ} (hw : IsNonneg w) :
    QuasiPos (a • chainOp + b • ContinuousLinearMap.mul ℝ BddZ w) :=
  (quasiPos_chainOp.smul ha).add (((posOp_mul hw).smul hb).quasiPos)

lemma exp_smul_one (s : ℝ) :
    NormedSpace.exp (s • (1 : BddZ →L[ℝ] BddZ)) = Real.exp s • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
    ← NormedSpace.algebraMap_exp_comm, Real.exp_eq_exp_ℝ]

/-- **Positivity of the semigroup.** If `A` is quasi-positive and `t ≥ 0`, then `e^{tA}` maps
nonnegative functions to nonnegative functions. -/
theorem QuasiPos.posOp_exp {A : BddZ →L[ℝ] BddZ} (hA : QuasiPos A) {t : ℝ} (ht : 0 ≤ t) :
    PosOp (NormedSpace.exp (t • A)) := by
  obtain ⟨c, hc⟩ := hA
  have hsplit : t • A = t • (A + c • 1) + (-(t * c)) • (1 : BddZ →L[ℝ] BddZ) := by
    module
  have hcomm : Commute (t • (A + c • 1)) ((-(t * c)) • (1 : BddZ →L[ℝ] BddZ)) := by
    rw [← Algebra.algebraMap_eq_smul_one (A := BddZ →L[ℝ] BddZ) (-(t * c))]; exact Algebra.commute_algebraMap_right _ _
  rw [hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm
    ((NormedSpace.expSeries_radius_eq_top ℝ (BddZ →L[ℝ] BddZ)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ (BddZ →L[ℝ] BddZ)).symm ▸ edist_lt_top _ _),
    exp_smul_one]
  exact (hc.smul ht).exp.mul (posOp_one.smul (Real.exp_pos _).le)

/-- **Positivity** for the operators of Lemma 4.2: for `t ≥ 0`, `a, b ≥ 0` and `w ≥ 0`,
`e^{t (a 𝓡 + b w)}` maps nonnegative functions to nonnegative functions. -/
theorem posOp_exp_generator {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {w : BddZ} (hw : IsNonneg w)
    (ht : 0 ≤ t) :
    PosOp (NormedSpace.exp (t • (a • chainOp + b • ContinuousLinearMap.mul ℝ BddZ w))) :=
  (quasiPos_generator ha hb hw).posOp_exp ht

/-- Positivity of `e^{t𝓡}` for `t ≥ 0`. -/
theorem posOp_exp_chainOp {t : ℝ} (ht : 0 ≤ t) : PosOp (NormedSpace.exp (t • chainOp)) :=
  quasiPos_chainOp.posOp_exp ht

@[simp] lemma exp_zero_smul (A : BddZ →L[ℝ] BddZ) : NormedSpace.exp ((0 : ℝ) • A) = 1 := by
  have : (0 : ℝ) • A = 0 := by module
  rw [this, NormedSpace.exp_zero]

/-- `t ↦ e^{tA} g` is differentiable, with derivative `A e^{tA} g`. -/
lemma hasDerivAt_exp_smul_apply (A : BddZ →L[ℝ] BddZ) (g : BddZ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) g) (A (NormedSpace.exp (t • A) g)) t := by
  have := HasFDerivAt.comp_hasDerivAt _ (ContinuousLinearMap.apply ℝ BddZ g).hasFDerivAt
    (hasDerivAt_exp_smul_const' A t)
  simpa [Function.comp_def] using this

lemma continuous_exp_smul (A : BddZ →L[ℝ] BddZ) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const A t).continuousAt

lemma continuous_exp_smul_apply (A : BddZ →L[ℝ] BddZ) (g : BddZ) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) g :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_apply A g t).continuousAt

/-- If `A g = 0`, then `e^{tA} g = g`. -/
theorem exp_smul_apply_of_apply_eq_zero {A : BddZ →L[ℝ] BddZ} {g : BddZ} (hg : A g = 0)
    (t : ℝ) : NormedSpace.exp (t • A) g = g := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)).mapL
    (ContinuousLinearMap.apply ℝ BddZ g)
  refine hs.unique ?_
  convert hasSum_ite_eq 0 g with n
  rcases n with _ | n
  · simp
  · rw [pow_succ]; simp [hg]; right; exact Function.iterate_fixed (by simp) n

/-- `𝓡 𝟏 = 0`. -/
lemma chainOp_one : chainOp 1 = 0 := by
  ext r; simp [chainGen, lp.infty_coeFn_one]; norm_num

/-- `e^{t𝓡} 𝟏 = 𝟏`. -/
theorem exp_smul_chainOp_one (t : ℝ) : NormedSpace.exp (t • chainOp) 1 = 1 :=
  exp_smul_apply_of_apply_eq_zero chainOp_one t

/-- **Comparison principle** (Duhamel inequality). Let `A` be quasi-positive, `t ≥ 0`, and
`d : ℝ → ℓ^∞(ℤ)` continuous on `[0, t]`, differentiable on `(0, t)` with derivative `d'`, such
that `d'(s) - A d(s) ≥ 0` pointwise for `s ∈ (0, t)`. Then `d(t) ≥ e^{tA} d(0)` pointwise.
(Proof: `s ↦ e^{(t-s)A} d(s)` is nondecreasing on `[0, t]`.) -/
theorem QuasiPos.comparison {A : BddZ →L[ℝ] BddZ} (hA : QuasiPos A) {t : ℝ} (ht : 0 ≤ t)
    {d d' : ℝ → BddZ} (hc : ContinuousOn d (Set.Icc 0 t))
    (hd : ∀ s ∈ Set.Ioo 0 t, HasDerivAt d (d' s) s)
    (hsup : ∀ s ∈ Set.Ioo 0 t, IsNonneg (d' s - A (d s))) :
    IsNonneg (d t - NormedSpace.exp (t • A) (d 0)) := by
  intro r
  have hE : ∀ s, HasDerivAt (fun s : ℝ => NormedSpace.exp ((t - s) • A))
      (-(NormedSpace.exp ((t - s) • A) * A)) s := by
    intro s
    have := HasDerivAt.scomp s (hasDerivAt_exp_smul_const A (t - s)) ((hasDerivAt_id s).const_sub t)
    simpa [Function.comp_def] using this
  have hEc : Continuous fun s : ℝ => NormedSpace.exp ((t - s) • A) :=
    (continuous_exp_smul A).comp (continuous_const.sub continuous_id)
  have hmono : MonotoneOn (fun s => coord r (NormedSpace.exp ((t - s) • A) (d s)))
      (Set.Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      ((coord r).continuous.comp_continuousOn (hEc.continuousOn.clm_apply hc)) ?_ ?_
      (f' := fun s => coord r (NormedSpace.exp ((t - s) • A) (d' s - A (d s))))
    · intro s hs
      rw [interior_Icc] at hs
      have := HasFDerivAt.comp_hasDerivAt _ (coord r).hasFDerivAt ((hE s).clm_apply (hd s hs))
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      · rfl
      · simp only [map_sub, map_add, map_neg, neg_apply,
          mul_apply_eq_comp]
        ring
    · intro s hs
      rw [interior_Icc] at hs
      exact hA.posOp_exp (by linarith [hs.2]) _ (hsup s hs) r
  have := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [sub_self, sub_zero, exp_zero_smul, coord_apply] at this
  simpa using this

/-- **Comparison principle**, nonnegative form: under the hypotheses of `QuasiPos.comparison`,
if moreover `d(0) ≥ 0`, then `d(t) ≥ 0`. -/
theorem QuasiPos.comparison_nonneg {A : BddZ →L[ℝ] BddZ} (hA : QuasiPos A) {t : ℝ}
    (ht : 0 ≤ t) {d d' : ℝ → BddZ} (hc : ContinuousOn d (Set.Icc 0 t))
    (hd : ∀ s ∈ Set.Ioo 0 t, HasDerivAt d (d' s) s)
    (hsup : ∀ s ∈ Set.Ioo 0 t, IsNonneg (d' s - A (d s))) (h0 : IsNonneg (d 0)) :
    IsNonneg (d t) := by
  intro r
  have h1 := hA.comparison ht hc hd hsup r
  have h2 := hA.posOp_exp ht _ h0 r
  simp only [lp.coeFn_sub, Pi.sub_apply] at h1
  linarith

end QSSEPtoKPZ
