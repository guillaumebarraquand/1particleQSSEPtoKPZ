/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Defs
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Atomic measures: total variation and integrals of differences (task L7)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L7.
`docs/stage5-design.md`, Sections 1.2 (e), (f), 3.4 (L7).

For two measures `∑ᵢ aᵢ δ_{yᵢ}`, `∑ᵢ bᵢ δ_{yᵢ}` with the same (countably many) atoms `yᵢ`, written
with `ENNReal.ofReal` of real summable weights:
* `etvDist_sum_dirac_le`: `‖μ - ν‖_TV ≤ ∑ᵢ |aᵢ - bᵢ|` (Mathlib's `etvDist`; Hahn decomposition);
* `abs_integral_sum_dirac_sub_le`: `|∫ f dμ - ∫ f dν| ≤ ‖f‖_∞ ∑ᵢ |aᵢ - bᵢ|`.
And `tiltedMeasureBox` as a sum over all of `ℤ` (`tiltedMeasureBox_eq_sum`), and for `L = ∞`
(`tiltedMeasureBox_top`: it is Stage 2's `tiltedMeasure`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The total mass of the atomic measure `∑ᵢ cᵢ δ_{yᵢ}` is `∑ᵢ cᵢ`. -/
private lemma atomTV_apply_univ {ι : Type*} (c : ι → ℝ≥0∞) (y : ι → ℝ) :
    (Measure.sum fun i => c i • Measure.dirac (y i)) Set.univ = ∑' i, c i := by
  simp [Measure.sum_apply _ MeasurableSet.univ]

/-- `cᵢ ≤ dᵢ` for all `i` gives `∑ᵢ cᵢ δ_{yᵢ} ≤ ∑ᵢ dᵢ δ_{yᵢ}`. -/
private lemma atomTV_mono {ι : Type*} {c d : ι → ℝ≥0∞} (y : ι → ℝ) (h : ∀ i, c i ≤ d i) :
    (Measure.sum fun i => c i • Measure.dirac (y i)) ≤
      Measure.sum fun i => d i • Measure.dirac (y i) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  refine ENNReal.tsum_le_tsum fun i => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact h i

/-- `∑ᵢ cᵢ δ_{yᵢ}` is finite when `∑ᵢ cᵢ < ∞`. -/
private lemma atomTV_isFinite {ι : Type*} (c : ι → ℝ≥0∞) (y : ι → ℝ) (hc : ∑' i, c i ≠ ∞) :
    IsFiniteMeasure (Measure.sum fun i => c i • Measure.dirac (y i)) :=
  ⟨by rw [atomTV_apply_univ]; exact hc.lt_top⟩

/-- `∑ᵢ aᵢ⁺ < ∞` for real summable weights `a`. -/
private lemma atomTV_tsum_ofReal_ne_top {ι : Type*} (a : ι → ℝ) (ha : Summable a) :
    ∑' i, ENNReal.ofReal (a i) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun i =>
    ENNReal.ofReal_le_ofReal (le_abs_self (a i)))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg (a i)) ha.abs]
  exact ENNReal.ofReal_ne_top

/-- For `cᵢ ≤ dᵢ` with `∑ᵢ dᵢ < ∞`: `‖∑ᵢ dᵢ δ_{yᵢ} - ∑ᵢ cᵢ δ_{yᵢ}‖_TV = ∑ᵢ (dᵢ - cᵢ)`. -/
private lemma atomTV_etvDist_of_le {ι : Type*} {c d : ι → ℝ≥0∞} (y : ι → ℝ)
    (h : ∀ i, c i ≤ d i) (hd : ∑' i, d i ≠ ∞) :
    etvDist (Measure.sum fun i => d i • Measure.dirac (y i))
      (Measure.sum fun i => c i • Measure.dirac (y i)) = ∑' i, (d i - c i) := by
  have hc : ∑' i, c i ≠ ∞ := ne_top_of_le_ne_top hd (ENNReal.tsum_le_tsum h)
  have := atomTV_isFinite c y hc
  rw [etvDist_of_ge (atomTV_mono y h), atomTV_apply_univ, atomTV_apply_univ]
  have e : ∑' i, d i = ∑' i, c i + ∑' i, (d i - c i) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun i => (add_tsub_cancel_of_le (h i)).symm
  rw [e, ENNReal.add_sub_cancel_left hc]

/-- `∫ f d(∑ᵢ aᵢ⁺ δ_{yᵢ}) = ∑ᵢ aᵢ⁺ f(yᵢ)` for a bounded continuous `f` and summable `a`. -/
private lemma atomTV_integral {ι : Type*} [Countable ι] (a : ι → ℝ) (y : ι → ℝ)
    (ha : Summable a) (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(Measure.sum fun i => ENNReal.ofReal (a i) • Measure.dirac (y i)) =
      ∑' i, max (a i) 0 * f (y i) := by
  have := atomTV_isFinite _ y (atomTV_tsum_ofReal_ne_top a ha)
  rw [integral_sum_measure (f.integrable _)]
  refine tsum_congr fun i => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal', smul_eq_mul]

/-- `∑ᵢ aᵢ⁺ f(yᵢ)` converges absolutely: `|aᵢ⁺ f(yᵢ)| ≤ |aᵢ| ‖f‖`. -/
private lemma atomTV_summable {ι : Type*} (a : ι → ℝ) (y : ι → ℝ) (ha : Summable a)
    (f : ℝ →ᵇ ℝ) : Summable fun i => max (a i) 0 * f (y i) := by
  refine Summable.of_norm_bounded (ha.abs.mul_right ‖f‖) fun i => ?_
  have h1 : |max (a i) 0| ≤ |a i| := by
    rw [abs_of_nonneg (le_max_right (a i) 0)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul h1 (f.norm_coe_le_norm _) (norm_nonneg _) (abs_nonneg _)

/-- **Total variation of a difference of atomic measures with the same atoms**:
`‖∑ᵢ aᵢ⁺ δ_{yᵢ} - ∑ᵢ bᵢ⁺ δ_{yᵢ}‖_TV ≤ ∑ᵢ |aᵢ - bᵢ|`, for real summable weights `a`, `b`
(`aᵢ⁺ = max(aᵢ, 0)`, as `ENNReal.ofReal` does). -/
theorem etvDist_sum_dirac_le {ι : Type*} [Countable ι] (a b : ι → ℝ) (y : ι → ℝ)
    (ha : Summable a) (hb : Summable b) :
    etvDist (Measure.sum fun i => ENNReal.ofReal (a i) • Measure.dirac (y i))
        (Measure.sum fun i => ENNReal.ofReal (b i) • Measure.dirac (y i)) ≤
      ENNReal.ofReal (∑' i, |a i - b i|) := by
  -- intermediate measure with weights `min(aᵢ⁺, bᵢ⁺)`
  set A := fun i => ENNReal.ofReal (a i) with hA
  set C := fun i => ENNReal.ofReal (b i) with hC
  set m := fun i => min (A i) (C i) with hm
  have hA' : ∑' i, A i ≠ ∞ := atomTV_tsum_ofReal_ne_top a ha
  have hC' : ∑' i, C i ≠ ∞ := atomTV_tsum_ofReal_ne_top b hb
  have h1 := atomTV_etvDist_of_le y (fun i => min_le_left (A i) (C i)) hA'
  have h2 := atomTV_etvDist_of_le y (fun i => min_le_right (A i) (C i)) hC'
  rw [etvDist_comm] at h2
  refine (etvDist_triangle _ (Measure.sum fun i => m i • Measure.dirac (y i)) _).trans ?_
  rw [h1, h2, ← ENNReal.tsum_add,
    ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) (ha.sub hb).abs]
  refine ENNReal.tsum_le_tsum fun i => ?_
  simp only [hA, hC]
  rcases le_total (ENNReal.ofReal (a i)) (ENNReal.ofReal (b i)) with h | h
  · rw [min_eq_left h, tsub_self, zero_add, tsub_le_iff_right]
    calc ENNReal.ofReal (b i) ≤ ENNReal.ofReal (|a i - b i| + a i) :=
          ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (a i - b i)])
      _ ≤ _ := ENNReal.ofReal_add_le
  · rw [min_eq_right h, tsub_self, add_zero, tsub_le_iff_right]
    calc ENNReal.ofReal (a i) ≤ ENNReal.ofReal (|a i - b i| + b i) :=
          ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a i - b i)])
      _ ≤ _ := ENNReal.ofReal_add_le

/-- **Integrals against atomic measures with the same atoms**: for a bounded continuous `f`,
`|∫ f d(∑ᵢ aᵢ⁺ δ_{yᵢ}) - ∫ f d(∑ᵢ bᵢ⁺ δ_{yᵢ})| ≤ ‖f‖_∞ ∑ᵢ |aᵢ - bᵢ|`. -/
theorem abs_integral_sum_dirac_sub_le {ι : Type*} [Countable ι] (a b : ι → ℝ) (y : ι → ℝ)
    (ha : Summable a) (hb : Summable b) (f : ℝ →ᵇ ℝ) :
    |(∫ x, f x ∂(Measure.sum fun i => ENNReal.ofReal (a i) • Measure.dirac (y i)))
        - ∫ x, f x ∂(Measure.sum fun i => ENNReal.ofReal (b i) • Measure.dirac (y i))| ≤
      ‖f‖ * ∑' i, |a i - b i| := by
  rw [atomTV_integral a y ha f, atomTV_integral b y hb f,
    ← (atomTV_summable a y ha f).tsum_sub (atomTV_summable b y hb f)]
  have hs : Summable fun i => |max (a i) 0 * f (y i) - max (b i) 0 * f (y i)| :=
    ((atomTV_summable a y ha f).sub (atomTV_summable b y hb f)).abs
  have hle : ∀ i, |max (a i) 0 * f (y i) - max (b i) 0 * f (y i)| ≤ ‖f‖ * |a i - b i| := by
    intro i
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul (f.norm_coe_le_norm _) (abs_max_sub_max_le_abs _ _ _) (abs_nonneg _)
      (norm_nonneg f)
  calc |∑' i, (max (a i) 0 * f (y i) - max (b i) 0 * f (y i))|
      ≤ ∑' i, |max (a i) 0 * f (y i) - max (b i) 0 * f (y i)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun i => max (a i) 0 * f (y i) - max (b i) 0 * f (y i)) hs
    _ ≤ ∑' i, ‖f‖ * |a i - b i| := hs.tsum_le_tsum hle ((ha.sub hb).abs.mul_left _)
    _ = ‖f‖ * ∑' i, |a i - b i| := tsum_mul_left

/-- `𝖹_n^L(t)` as a sum over all sites, the weights outside `Λ_L` being `0`. -/
theorem tiltedMeasureBox_eq_sum (L : ℕ∞) (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) :
    tiltedMeasureBox L n ψ ω t =
      Measure.sum fun x : ℤ => ENNReal.ofReal ((box L).indicator (zN n ψ ω t) x) •
        Measure.dirac (rescaledPosition n t x) := by
  ext s hs
  rw [tiltedMeasureBox, Measure.sum_apply _ hs, Measure.sum_apply _ hs,
    tsum_subtype (box L) fun x =>
      (ENNReal.ofReal (zN n ψ ω t x) • Measure.dirac (rescaledPosition n t x)) s]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ box L <;> simp [hx]

/-- For `L = ∞`, `𝖹_n^∞(t) = 𝖹_n(t)` (Stage 2's `tiltedMeasure`). -/
theorem tiltedMeasureBox_top (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) :
    tiltedMeasureBox ⊤ n ψ ω t = tiltedMeasure n ψ ω t := by
  have h : box ⊤ = Set.univ := Set.eq_univ_of_forall fun x => by simp [box]
  rw [tiltedMeasureBox_eq_sum, tiltedMeasure, h, Set.indicator_univ]

end QSSEPtoKPZ
