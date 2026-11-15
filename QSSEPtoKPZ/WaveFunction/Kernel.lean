/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Defs
public import QSSEPtoKPZ.SecondMoments.Generator
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The kernel `p_t` of the simple random walk (Section 2.2)

The article defines `p_t(x)` as the probability that the continuous-time random walk on `ℤ` with
generator `Δ` (rate `1` to each neighbour), started from `0`, is at `x` at time `t`. As for `u_n`
in Stage 1, the walk itself is not formalized: `p_t` is defined analytically as
`p_t = e^{tΔ} δ₀`, the exponential of the bounded operator `Δ` on `ℓ^∞(ℤ)` applied to the
indicator of the origin (since `Δ` is symmetric, `(e^{tΔ} δ₀)(x) = p_t(0, x) = p_t(x)`).
-/

@[expose] public section

open scoped lp ENNReal

noncomputable section

namespace QSSEPtoKPZ

lemma abs_lap_le (g : BddZ) (x : ℤ) : |lap g x| ≤ 4 * ‖g‖ := by
  have h : ∀ s : ℤ, |g s| ≤ ‖g‖ := fun s => by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero g s
  have h1 := h (x + 1); have h2 := h (x - 1); have h3 := h x
  unfold lap
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

lemma memℓp_lap (g : BddZ) : Memℓp (lap g) ∞ := by
  refine memℓp_infty_iff.2 ⟨4 * ‖g‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  simpa [Real.norm_eq_abs] using abs_lap_le g x

/-- `Δ` as a linear map on `ℓ^∞(ℤ)`. -/
def lapOpLinear : BddZ →ₗ[ℝ] BddZ where
  toFun g := ⟨lap g, memℓp_lap g⟩
  map_add' f g := by
    ext x
    simp only [lp.coeFn_add, Pi.add_apply, lap]
    ring
  map_smul' c g := by
    ext x
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lap, RingHom.id_apply]
    ring

/-- The Laplacian `Δ` on `ℤ` (generator of the simple random walk with rate `1` to each
neighbour), as a bounded operator on `ℓ^∞(ℤ)` (its norm is at most `4`). -/
def lapOp : BddZ →L[ℝ] BddZ :=
  lapOpLinear.mkContinuous 4 fun g => by
    refine lp.norm_le_of_forall_le (by positivity) fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_lap_le g x

lemma memℓp_delta0 : Memℓp (fun x : ℤ => if x = 0 then (1 : ℝ) else 0) ∞ := by
  refine memℓp_infty_iff.2 ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  dsimp only
  split_ifs <;> simp

/-- The function `δ₀ = 𝟙_{x = 0}`, as an element of `ℓ^∞(ℤ)`. -/
def delta0 : BddZ := ⟨fun x => if x = 0 then 1 else 0, memℓp_delta0⟩

/-- `p_t(x) = (e^{tΔ} δ₀)(x)`: the probability that the continuous-time simple random walk on
`ℤ` with generator `Δ`, started from `0`, is at `x` at time `t` (Section 2.2). -/
def rwKernel (t : ℝ) (x : ℤ) : ℝ := NormedSpace.exp (t • lapOp) delta0 x

end QSSEPtoKPZ
