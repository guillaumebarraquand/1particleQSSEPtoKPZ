/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace

/-!
# Masses of atoms of a finite measure as Borel functionals (task Q1a, auxiliary)

For a finite measure `μ` on `ℝ` and `y ∈ ℝ`, the mass `μ({y})` is the decreasing limit of
`∫ τ_k(z - y) μ(dz)`, where `τ_k(u) = max(0, 1 - (k+1)|u|)` is a tent function. Each of these
integrals is continuous in `μ` (weak topology) and in `y`, hence jointly measurable; so
`x ↦ F(x)({Y(x)})` is measurable as soon as `F` is continuous into `ℳ₊` and `Y` is measurable
(`pathFun_measurable_atom`). This is the precise form of "`𝔷_n(t,x)` is the mass of an atom, a
Borel function of the path" (`docs/stage4-design.md`, Section 1.2 (b)); Mathlib's Giry
σ-algebra on `FiniteMeasure ℝ` is not used.

We also record that the masses of atoms at distinct points add up to at most the total mass
(`pathFun_tsum_atoms_le`), and that `x ↦ y_n(t,x)` is injective for `n > 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace QSSEPtoKPZ

/-- The tent function `τ_k(z - y) = max(0, 1 - (k+1)|z - y|)`. -/
private def pathFunTent (k : ℕ) (y z : ℝ) : ℝ := max 0 (1 - ((k : ℝ) + 1) * |z - y|)

private lemma pathFunTent_continuous (k : ℕ) :
    Continuous fun p : ℝ × ℝ => pathFunTent k p.1 p.2 := by
  unfold pathFunTent; fun_prop

private lemma pathFunTent_nonneg (k : ℕ) (y z : ℝ) : 0 ≤ pathFunTent k y z := le_max_left _ _

private lemma pathFunTent_le_one (k : ℕ) (y z : ℝ) : pathFunTent k y z ≤ 1 := by
  unfold pathFunTent
  refine max_le zero_le_one ?_
  have : 0 ≤ ((k : ℝ) + 1) * |z - y| := by positivity
  linarith

private lemma pathFunTent_abs_le (k : ℕ) (y z : ℝ) : |pathFunTent k y z| ≤ 1 := by
  rw [abs_of_nonneg (pathFunTent_nonneg k y z)]; exact pathFunTent_le_one k y z

/-- `τ_k(z - y) → 𝟙_{y}(z)` as `k → ∞`. -/
private lemma pathFunTent_tendsto (y z : ℝ) :
    Tendsto (fun k : ℕ => pathFunTent k y z) atTop (𝓝 (Set.indicator {y} 1 z)) := by
  by_cases hz : z = y
  · subst hz
    simp only [pathFunTent, sub_self, abs_zero, mul_zero, sub_zero, Set.indicator_of_mem
      (Set.mem_singleton z), Pi.one_apply]
    rw [max_eq_right zero_le_one]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem (by simpa using hz)]
    have hd : 0 < |z - y| := abs_pos.2 (sub_ne_zero.2 hz)
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / |z - y|)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (1 / |z - y|) ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [div_le_iff₀ hd] at hk'
    unfold pathFunTent
    rw [max_eq_left (by linarith)]

/-- `∫ τ_k(z - y) μ(dz) → μ({y})`. -/
private lemma pathFunTent_integral_tendsto (μ : FiniteMeasure ℝ) (y : ℝ) :
    Tendsto (fun k : ℕ => ∫ z, pathFunTent k y z ∂(μ : Measure ℝ)) atTop
      (𝓝 ((μ : Measure ℝ) {y}).toReal) := by
  have h := tendsto_integral_of_dominated_convergence (μ := (μ : Measure ℝ))
    (F := fun k z => pathFunTent k y z) (f := Set.indicator {y} 1) (fun _ => 1)
    (fun k => ((pathFunTent_continuous k).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_const _) (fun k => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact pathFunTent_abs_le k y z)
    (ae_of_all _ fun z => pathFunTent_tendsto y z)
  rwa [integral_indicator_one (measurableSet_singleton y), measureReal_def] at h

/-- **Atoms are Borel functionals.** If `F : X → ℳ₊` is continuous and `Y : X → ℝ` measurable,
then `x ↦ F(x)({Y(x)})` is measurable. -/
theorem pathFun_measurable_atom {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {F : X → FiniteMeasure ℝ} (hF : Continuous F) {Y : X → ℝ}
    (hY : Measurable Y) : Measurable fun x => ((F x : Measure ℝ) {Y x}).toReal := by
  refine measurable_of_tendsto_metrizable
    (f := fun k x => ∫ z, pathFunTent k (Y x) z ∂(F x : Measure ℝ)) (fun k => ?_)
    (tendsto_pi_nhds.2 fun x => pathFunTent_integral_tendsto (F x) (Y x))
  have hu : Measurable (Function.uncurry
      fun (y : ℝ) (x : X) => ∫ z, pathFunTent k y z ∂(F x : Measure ℝ)) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun x => ?_) (fun y => ?_)
    · refine continuous_of_dominated (bound := fun _ => 1)
        (fun y => ((pathFunTent_continuous k).comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        (fun y => ae_of_all _ fun z => by
          rw [Real.norm_eq_abs]; exact pathFunTent_abs_le k y z)
        (integrable_const _) (ae_of_all _ fun z => ?_)
      exact (pathFunTent_continuous k).comp (continuous_id.prodMk continuous_const)
    · exact ((continuous_pairFM ((pathFunTent_continuous k).comp
        (continuous_const.prodMk continuous_id)) ⟨1, pathFunTent_abs_le k y⟩).comp
        hF).measurable
  exact hu.comp (hY.prodMk measurable_id)

/-- The masses of the atoms of `μ` at the distinct points `y(x)`, `x ∈ ℤ`, are summable, with sum
at most the total mass of `μ`. -/
theorem pathFun_tsum_atoms_le (μ : FiniteMeasure ℝ) {y : ℤ → ℝ} (hy : Function.Injective y) :
    Summable (fun x => ((μ : Measure ℝ) {y x}).toReal) ∧
      ∑' x, ((μ : Measure ℝ) {y x}).toReal ≤ ((μ : Measure ℝ) Set.univ).toReal := by
  have hle : ∑' x, (μ : Measure ℝ) {y x} ≤ (μ : Measure ℝ) Set.univ :=
    (tsum_meas_le_meas_iUnion_of_disjoint (μ : Measure ℝ) (fun _ => measurableSet_singleton _)
      (fun a b hab => Set.disjoint_singleton.2 (hy.ne hab))).trans
      (measure_mono (Set.subset_univ _))
  have hne : ∑' x, (μ : Measure ℝ) {y x} ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top _ _) hle
  refine ⟨ENNReal.summable_toReal hne, ?_⟩
  rw [← ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- For `n > 0`, the positions `x ↦ y_n(t,x)` are distinct. -/
theorem pathFun_rescaledPosition_injective {n : ℝ} (hn : 0 < n) (t : ℝ) :
    Function.Injective (rescaledPosition n t) := by
  intro a b h
  have hp : (n ^ (1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  simp only [rescaledPosition] at h
  rw [div_left_inj' hp, sub_left_inj] at h
  exact_mod_cast h

end QSSEPtoKPZ
