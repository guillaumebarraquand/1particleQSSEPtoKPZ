/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathFunctionals
public import QSSEPtoKPZ.LimitPoints.MollifyCont
public import QSSEPtoKPZ.Replacement.L2Bound
public import QSSEPtoKPZ.Replacement.SmoothedSum
public import QSSEPtoKPZ.Tightness.FiniteMeasureEmbed
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Joint measurability of the path functionals in `(γ, t)` (task Q1b)

Auxiliary results for `LimitPoints/PrelimitLaw.lean`. On `C([0,T], ℳ₊) × ℝ` (product
σ-algebra; `ℳ₊` with its Borel σ-algebra inside the path space):

* `prelimMeas_measurable_atomPath`: `(γ, t) ↦ γ(t)({y_n(t,x)})` is measurable (limit of the
  continuous functions `(γ, t) ↦ ∫ (1 - k|z - y_n(t,x)|)⁺ γ(t)(dz)`);
* `prelimMeas_measurable_ENpath`: `(γ, t) ↦ ℰ_n(t; G_t)` (atoms of `γ(t)`) is measurable;
* `prelimMeas_continuous_smoothedNormSq`: `(γ, t) ↦ ‖(G_t γ(t)) ⋆ ρ_ε‖₂²` is continuous, for
  `G` bounded and jointly continuous and `ε > 0` (by (6.1), an integral of a bounded continuous
  function against `γ(t) ⊗ γ(t) ⊗ δ_t`);
* `prelimStop`: the path stopped at time `s`, `γ^s(u) = γ(min(u, s))`, measurable from the
  canonical filtration at time `s` (`measurable_prelimStop`); a functional of the path which only
  sees `γ(u)`, `u ≤ s`, is then adapted.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {T : ℝ}

/-! ### The mass of an atom -/

/-- The tent `(z, y) ↦ (1 - (k+1)|z - y|)⁺`, bounded continuous. -/
private def prelimTent (k : ℕ) : ℝ × ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q => max 0 (1 - ((k : ℝ) + 1) * |q.1 - q.2|))
    (continuous_const.max (continuous_const.sub
      (continuous_const.mul (continuous_fst.sub continuous_snd).abs))) 1
    fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      refine max_le zero_le_one ?_
      have : 0 ≤ ((k : ℝ) + 1) * |q.1 - q.2| := by positivity
      linarith

/-- `(μ, y) ↦ ∫ (1 - (k+1)|z - y|)⁺ μ(dz)` is continuous on `ℳ₊ × ℝ`. -/
private lemma prelimMeas_continuous_tent (k : ℕ) :
    Continuous fun p : FiniteMeasure ℝ × ℝ =>
      ∫ z, max 0 (1 - ((k : ℝ) + 1) * |z - p.2|) ∂(p.1 : Measure ℝ) := by
  have hc := (densFM_continuous_integral (prelimTent k)).comp
    (densFM_continuous_prod.comp (continuous_fst.prodMk (densFM_continuous_dirac.comp
      continuous_snd)))
  refine hc.congr fun p => ?_
  simp only [Function.comp_apply, FiniteMeasure.toMeasure_prod,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [integral_prod _ (BoundedContinuousFunction.integrable _ _)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show ∫ y, prelimTent k (z, y) ∂(Measure.dirac p.2) = _
  rw [integral_dirac]
  rfl

/-- `∫ (1 - (k+1)|z - y|)⁺ μ(dz) → μ({y})`. -/
private lemma prelimMeas_tendsto_tent (μ : FiniteMeasure ℝ) (y : ℝ) :
    Tendsto (fun k : ℕ => ∫ z, max 0 (1 - ((k : ℝ) + 1) * |z - y|) ∂(μ : Measure ℝ)) atTop
      (𝓝 (((μ : Measure ℝ) {y}).toReal)) := by
  have hlim : ∫ z, ({y} : Set ℝ).indicator (1 : ℝ → ℝ) z ∂(μ : Measure ℝ) =
      ((μ : Measure ℝ) {y}).toReal := by
    rw [integral_indicator_one (measurableSet_singleton y), measureReal_def]
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun k => ?_)
    (integrable_const 1) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · exact (Continuous.measurable (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    refine max_le zero_le_one ?_
    have : 0 ≤ ((k : ℝ) + 1) * |z - y| := by positivity
    linarith
  · by_cases hz : z = y
    · subst hz
      simp
    · have hpos : 0 < |z - y| := abs_pos.2 (sub_ne_zero.2 hz)
      rw [Set.indicator_of_notMem (by simpa using hz)]
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / |z - y|)
      filter_upwards [eventually_ge_atTop k₀] with k hk
      have h1 : 1 ≤ ((k : ℝ) + 1) * |z - y| := by
        have : (1 / |z - y|) < (k : ℝ) + 1 := by
          have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        rw [div_lt_iff₀ hpos] at this
        linarith
      exact (max_eq_left (by linarith)).symm

/-- **Joint measurability of the atoms**: `(γ, t) ↦ γ(t)({y_n(t,x)})` is measurable on
`C([0,T], ℳ₊) × ℝ`. -/
theorem prelimMeas_measurable_atomPath (n : ℝ) (x : ℤ) :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => atomPath n p.1 p.2 x := by
  have hc : ∀ k : ℕ, Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      ∫ z, max 0 (1 - ((k : ℝ) + 1) * |z - rescaledPosition n p.2 x|) ∂(pathAt p.1 p.2 :
        Measure ℝ) := fun k =>
    (prelimMeas_continuous_tent k).comp (continuous_pathAt_prod.prodMk
      ((continuous_const.sub (continuous_const.mul continuous_snd)).div_const _))
  refine measurable_of_tendsto_metrizable (fun k => (hc k).measurable)
    (tendsto_pi_nhds.2 fun p => ?_)
  exact prelimMeas_tendsto_tent _ _

/-- **Joint measurability of `ℰ_n`**: `(γ, t) ↦ ℰ_n(t; G_t)` (computed with the atoms of `γ(t)`)
is measurable, for test functions `G_t` with `t ↦ G_t(y_n(t,x))` measurable. -/
theorem prelimMeas_measurable_ENpath (n : ℝ) {G : ℝ → ℝ → ℝ}
    (hG : ∀ x : ℤ, Measurable fun t => G t (rescaledPosition n t x)) :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => ENpath n p.1 p.2 (G p.2) := by
  unfold ENpath
  exact measurable_const.mul (Measurable.tsum fun x =>
    ((((prelimMeas_measurable_atomPath n x).mul (prelimMeas_measurable_atomPath n (x + 1))).mul
      ((hG x).comp measurable_snd)).mul ((hG (x + 1)).comp measurable_snd)))

/-! ### The smoothed norm -/

/-- The bounded continuous kernel `((x, y), s) ↦ G_s(x) G_s(y) κ_ε(x - y)`. -/
private def prelimKernel {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {G : ℝ → ℝ → ℝ}
    (hG : Continuous (Function.uncurry G)) {c : ℝ} (hc : ∀ s x, |G s x| ≤ c) {ε : ℝ}
    (hε : 0 < ε) : (ℝ × ℝ) × ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q => G q.2 q.1.1 * G q.2 q.1.2 * kappaEps ρ ε (q.1.1 - q.1.2))
    (((hG.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).mul
      (hG.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))).mul
      ((replContinuous_kappaEps hρ ε).comp
        ((continuous_fst.comp continuous_fst).sub (continuous_snd.comp continuous_fst))))
    (c * c * (kappa ρ 0 / ε)) fun q => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hk : |kappaEps ρ ε (q.1.1 - q.1.2)| ≤ kappa ρ 0 / ε := by
        rw [kappaEps, abs_of_nonneg (div_nonneg (hρ.kappa_nonneg _) hε.le)]
        exact div_le_div_of_nonneg_right (hρ.kappa_le _) hε.le
      have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0 0)
      exact mul_le_mul (mul_le_mul (hc _ _) (hc _ _) (abs_nonneg _) hc0) hk (abs_nonneg _)
        (mul_nonneg hc0 hc0)

/-- **Joint continuity of the smoothed norm**: for `G` bounded and jointly continuous and
`ε > 0`, `(μ, s) ↦ ‖(G_s μ) ⋆ ρ_ε‖₂²` is continuous on `ℳ₊ × ℝ`. -/
theorem prelimMeas_continuous_smoothedNormSq_fm {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) {c : ℝ} (hc : ∀ s x, |G s x| ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous fun p : FiniteMeasure ℝ × ℝ => smoothedNormSq (p.1 : Measure ℝ) (G p.2) ρ ε := by
  set H := prelimKernel hρ hG hc hε
  have hG' : Continuous fun p : FiniteMeasure ℝ × ℝ => ∫ q, H q ∂(((p.1.prod p.1).prod
      (diracProba p.2).toFiniteMeasure : FiniteMeasure ((ℝ × ℝ) × ℝ)) : Measure _) :=
    (densFM_continuous_integral H).comp (densFM_continuous_prod.comp
      ((densFM_continuous_prod.comp (continuous_fst.prodMk continuous_fst)).prodMk
        (densFM_continuous_dirac.comp continuous_snd)))
  refine hG'.congr fun p => ?_
  have hGs : Continuous (G p.2) := hG.comp (continuous_const.prodMk continuous_id)
  rw [(smoothedNormSq_eq hρ (p.1 : Measure ℝ) hGs ⟨c, hc p.2⟩ hε).2.2]
  simp only [FiniteMeasure.toMeasure_prod,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [integral_prod _ (BoundedContinuousFunction.integrable _ _)]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  show ∫ e, H (q, e) ∂(Measure.dirac p.2) = _
  rw [integral_dirac]
  rfl

/-- `(γ, s) ↦ ‖(G_s γ(s)) ⋆ ρ_ε‖₂²` is continuous on `C([0,T], ℳ₊) × ℝ`. -/
theorem prelimMeas_continuous_smoothedNormSq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) {c : ℝ} (hc : ∀ s x, |G s x| ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      smoothedNormSq (pathAt p.1 p.2 : Measure ℝ) (G p.2) ρ ε :=
  (prelimMeas_continuous_smoothedNormSq_fm hρ hG hc hε).comp
    (continuous_pathAt_prod.prodMk continuous_snd)

/-! ### Test functions extended outside `[0,T]` -/

/-- `φ̃_s = φ_{proj_{[0,T]} s}`: equal to `φ_s` on `[0,T]`, jointly continuous on `ℝ × ℝ`. -/
def prelimExt (hT : 0 ≤ T) (φ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ → ℝ := φ (Set.projIcc 0 T hT s)

/-- `φ̃_s = φ_s` for `s ∈ [0,T]`. -/
theorem prelimExt_of_mem (hT : 0 ≤ T) (φ : ℝ → ℝ → ℝ) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    prelimExt hT φ s = φ s := by
  simp only [prelimExt, Set.projIcc_of_mem _ hs]

/-- `φ̃` is jointly continuous for `φ ∈ C_b^{1,3}`. -/
theorem prelimExt_continuous (hT : 0 ≤ T) {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    Continuous (Function.uncurry (prelimExt hT φ)) := by
  have hp : Continuous fun p : ℝ × ℝ => (((Set.projIcc 0 T hT p.1 : Set.Icc (0 : ℝ) T) : ℝ),
      p.2) :=
    (continuous_subtype_val.comp ((continuous_projIcc (h := hT)).comp continuous_fst)).prodMk
      continuous_snd
  have := (hφ.continuousOn.2 0 (by norm_num)).comp_continuous hp
    fun p => ⟨(Set.projIcc 0 T hT p.1).2, Set.mem_univ _⟩
  change Continuous fun p : ℝ × ℝ => φ (Set.projIcc 0 T hT p.1) p.2
  simpa only [iteratedDeriv_zero, Function.comp_def] using this

/-- `|φ̃_s(x)| ≤ C`. -/
theorem prelimExt_abs_le (hT : 0 ≤ T) {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    (s x : ℝ) : |prelimExt hT φ s x| ≤ C :=
  hφ.replAbs_le (Set.projIcc 0 T hT s).2 x

/-! ### The stopped path -/

/-- The path stopped at time `s`: `γ^s(u) = γ(min(u, s))`. -/
def prelimStop (s : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) :=
  ⟨fun u => pathAt γ (min (u : ℝ) s), continuous_pathAt_prod.comp
    (continuous_const.prodMk (continuous_subtype_val.min continuous_const))⟩

/-- `γ^s(u) = γ(u)` for `u ≤ s`, `0 ≤ s`. -/
theorem pathAt_prelimStop {s u : ℝ} (hs : 0 ≤ s) (hus : u ≤ s)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : pathAt (prelimStop s γ) u = pathAt γ u := by
  by_cases hT : 0 ≤ T
  · simp only [pathAt, hT, ↓reduceDIte, prelimStop, ContinuousMap.coe_mk]
    have hle : ((Set.projIcc 0 T hT u : Set.Icc (0 : ℝ) T) : ℝ) ≤ s := by
      rw [Set.coe_projIcc]
      exact max_le hs ((min_le_right _ _).trans hus)
    rw [min_eq_left hle, Set.projIcc_val]
  · simp only [pathAt, hT, ↓reduceDIte]

/-- The stopped path is measurable from the canonical filtration at time `s`. -/
theorem measurable_prelimStop (s : ℝ≥0) :
    Measurable[pathFiltrationCan T s] (prelimStop (T := T) s) := by
  refine @measurable_pathFiniteMeasure_iff_tightEmb _ (pathFiltrationCan T s) T _ |>.2
    fun u j => ?_
  exact measurable_pairFM_pathFiltrationCan (s := min (u : ℝ) s) (min_le_right _ _) (bumpTest j)

end QSSEPtoKPZ
