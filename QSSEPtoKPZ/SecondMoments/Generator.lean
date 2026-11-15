/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The generator `𝓡` of the chain of Section 4

The operator (3.24) of the article,

  `𝓡 g(r) = 2 [g(r+1) + g(r-1) - 2 g(r)] + 2 𝟙_{|r| = 1} [g(0) - g(r)]`,   `r ∈ ℤ`,

is the generator of the continuous-time Markov chain `(R_v)` of Section 4.1 (the difference of
the positions of two inclusion particles). We use it in two forms:

* `chainGen g`, for an arbitrary function `g : ℤ → ℝ` (used in Lemma 6.3 and in (4.3));
* `chainOp`, the same formula as a bounded linear operator on `ℓ^∞(ℤ)`, whose exponential
  replaces the semigroup of the chain (see `DEVIATIONS.md`, Section 4).

We also define the reversible measure `π` of (4.1) and the function `𝟙_{|r| = 1}` as an
element of `ℓ^∞(ℤ)`.
-/

@[expose] public section

open scoped lp ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The space `ℓ^∞(ℤ)` of bounded real functions on `ℤ`, with the supremum norm. -/
abbrev BddZ := lp (fun _ : ℤ => ℝ) ∞

/-- The generator `𝓡` of (3.24), acting on an arbitrary function `g : ℤ → ℝ`:
`𝓡 g(r) = 2 [g(r+1) + g(r-1) - 2 g(r)] + 2 𝟙_{|r| = 1} [g(0) - g(r)]`. -/
def chainGen (g : ℤ → ℝ) (r : ℤ) : ℝ :=
  2 * (g (r + 1) + g (r - 1) - 2 * g r) + 2 * (if |r| = 1 then g 0 - g r else 0)

/-- The reversible measure `π(r) = 1 + 𝟙_{r = 0}` of the chain, equation (4.1). -/
def chainPi (r : ℤ) : ℝ := 1 + if r = 0 then 1 else 0

lemma abs_chainGen_le (g : BddZ) (r : ℤ) : |chainGen g r| ≤ 12 * ‖g‖ := by
  have h : ∀ s : ℤ, |g s| ≤ ‖g‖ := fun s => by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero g s
  have h0 := h 0; have h1 := h (r + 1); have h2 := h (r - 1); have h3 := h r
  have hn : 0 ≤ ‖g‖ := norm_nonneg g
  unfold chainGen
  split_ifs
  · rw [abs_le] at *
    constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  · rw [abs_le] at *
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

lemma memℓp_chainGen (g : BddZ) : Memℓp (chainGen g) ∞ := by
  refine memℓp_infty_iff.2 ⟨12 * ‖g‖, ?_⟩
  rintro _ ⟨r, rfl⟩
  simpa [Real.norm_eq_abs] using abs_chainGen_le g r

/-- `𝓡` as a linear map on `ℓ^∞(ℤ)`. -/
def chainOpLinear : BddZ →ₗ[ℝ] BddZ where
  toFun g := ⟨chainGen g, memℓp_chainGen g⟩
  map_add' f g := by
    ext r
    simp only [lp.coeFn_add, Pi.add_apply, chainGen]
    split_ifs <;> ring
  map_smul' c g := by
    ext r
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, chainGen, RingHom.id_apply]
    split_ifs <;> ring

@[simp] lemma chainOpLinear_apply (g : BddZ) (r : ℤ) : chainOpLinear g r = chainGen g r := rfl

/-- The generator `𝓡` of (3.24), as a bounded linear operator on `ℓ^∞(ℤ)` (its norm is at
most `12`). -/
def chainOp : BddZ →L[ℝ] BddZ :=
  chainOpLinear.mkContinuous 12 fun g => by
    refine lp.norm_le_of_forall_le (by positivity) fun r => ?_
    rw [chainOpLinear_apply, Real.norm_eq_abs]
    exact abs_chainGen_le g r

@[simp] lemma chainOp_apply (g : BddZ) (r : ℤ) : chainOp g r = chainGen g r := by
  simp [chainOp]

lemma memℓp_defect : Memℓp (fun r : ℤ => if |r| = 1 then (1 : ℝ) else 0) ∞ := by
  refine memℓp_infty_iff.2 ⟨1, ?_⟩
  rintro _ ⟨r, rfl⟩
  dsimp only
  split_ifs <;> simp

/-- The function `𝟙_{|r| = 1}`, as an element of `ℓ^∞(ℤ)`. -/
def defectInd : BddZ := ⟨fun r => if |r| = 1 then 1 else 0, memℓp_defect⟩

@[simp] lemma defectInd_apply (r : ℤ) : defectInd r = if |r| = 1 then 1 else 0 := rfl

end QSSEPtoKPZ
