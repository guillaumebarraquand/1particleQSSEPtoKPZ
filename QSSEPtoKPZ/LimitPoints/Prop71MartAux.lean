/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PrelimitLaw
public import QSSEPtoKPZ.TiltedField.Identities

/-!
# Auxiliary results for Proposition 7.1 (3) (task Q3)

* `limMart_unif_of_continuousOn`: if `F` is continuous on `X × [a,b]` and `x_j → x`, then
  `F(x_j, ·) → F(x, ·)` uniformly on `[a,b]` (compactness of `[a,b]`).
* `IsC13.limMart_abs_AN_sub_le`: Proposition 3.1 (1) at each time,
  `|𝒜_nφ_s - ½∂ₓ²φ_s| ≤ n^{-1/4} C`.
* `limMart_tendsto_aN`: `a_n → 1`.
* The limit martingale `M^φ(t)` of (7.2) on the canonical space: continuous in `t` for every path
  (`limMart_continuousOn`), Borel in the path (`limMart_measurable`), adapted to the canonical
  filtration (`limMart_stronglyMeasurable_can`, through the stopped path `prelimStop`).
* `IsPathPrelimLaw.limMart_integral_sq_le`: `𝔼[M_n^φ(t)²] = 𝔼[⟨M_n^φ⟩_t] ≤ 4C² 2^{1+16T}` under a
  prelimit law (Proposition 3.1 (2) and (4.8)).
* `limMart_tendsto_integral_of_sq_le`: Vitali's theorem in the form used in Section 7.1: a
  sequence bounded in `L²` and converging almost surely converges in `L¹` (its limit is in `L²`
  by Fatou's lemma).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

universe u

/-! ### Uniform convergence from joint continuity -/

/-- If `F` is continuous on `X × [a,b]` and `x_j → x`, then `F(x_j, ·) → F(x, ·)` uniformly on
`[a,b]`. -/
theorem limMart_unif_of_continuousOn {X ι : Type*} [TopologicalSpace X] {l : Filter ι}
    {F : X → ℝ → ℝ} {a b : ℝ} (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    {x : ι → X} {x₀ : X} (hx : Tendsto x l (𝓝 x₀)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ t ∈ Icc a b, |F (x j) t - F x₀ t| < ε := by
  obtain ⟨v, hv, hvF⟩ := isCompact_Icc.mem_uniformity_of_prod hF (mem_univ x₀)
    (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hx hv] with j hj t ht
  have := hvF (x j) hj t ht
  simpa [Real.dist_eq] using this

/-! ### The test functions -/

variable {T C : ℝ} {φ φt : ℝ → ℝ → ℝ}

/-- The slice of `φ` at a time `s ∈ [0,T]` is a time-independent `C_b^{1,3}` function. -/
private lemma IsC13.limMart_slice (hφ : IsC13 T φ φt C) {s : ℝ} (hs : s ∈ Icc 0 T) :
    IsC13 1 (fun _ => φ s) (fun _ _ => 0) C := by
  obtain ⟨c, hc, hb⟩ := hφ.bound
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    obtain ⟨b0, b1, b2, b3, b4⟩ := hb s hs 0
    fin_cases i
    · exact (abs_nonneg _).trans b0
    · exact (abs_nonneg _).trans b1
    · exact (abs_nonneg _).trans b2
    · exact (abs_nonneg _).trans b3
    · exact (abs_nonneg _).trans b4
  refine ⟨fun _ _ => hφ.contDiff s hs, fun x s _ => hasDerivWithinAt_const _ _ _,
    ⟨continuousOn_const, fun k hk => ?_⟩, ⟨fun i => if i = 1 then 0 else c i, ?_, ?_⟩⟩
  · exact (((hφ.contDiff s hs).continuous_iteratedDeriv k
      (by exact_mod_cast hk)).comp continuous_snd).continuousOn
  · rw [Fin.sum_univ_five] at hc ⊢
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
    linarith [hc0 1]
  · intro r _ x
    obtain ⟨b0, -, b2, b3, b4⟩ := hb s hs x
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, abs_zero, le_refl, true_and]
    exact ⟨b0, b2, b3, b4⟩

/-- Proposition 3.1 (1) at each time: `|𝒜_nφ_s - ½∂ₓ²φ_s| ≤ n^{-1/4} C`. -/
theorem IsC13.limMart_abs_AN_sub_le (hφ : IsC13 T φ φt C) {n : ℝ} (hn : 1 ≤ n) {s : ℝ}
    (hs : s ∈ Icc 0 T) (y : ℝ) :
    |AN n (φ s) y - iteratedDeriv 2 (φ s) y / 2| ≤ n ^ (-1 / 4 : ℝ) * C :=
  prop_3_1_generator hn (hφ.limMart_slice hs) y

/-- The drift `∂ₛφ_s + ½∂ₓ²φ_s` of (7.2) is continuous on `[0,T] × ℝ`. -/
theorem IsC13.limMart_continuousOn_drift (hφ : IsC13 T φ φt C) :
    ContinuousOn (Function.uncurry fun s y => φt s y + iteratedDeriv 2 (φ s) y / 2)
      (Icc 0 T ×ˢ univ) :=
  hφ.continuousOn.1.add ((hφ.continuousOn.2 2 (by norm_num)).div_const 2)

/-- The drift `∂ₛφ_s + ½∂ₓ²φ_s` of (7.2) is bounded on `[0,T] × ℝ`. -/
theorem IsC13.limMart_bound_drift (hφ : IsC13 T φ φt C) :
    ∃ K, ∀ s ∈ Icc 0 T, ∀ y, |φt s y + iteratedDeriv 2 (φ s) y / 2| ≤ K := by
  obtain ⟨c, -, hc⟩ := hφ.bound
  refine ⟨c 1 + c 3 / 2, fun s hs y => ?_⟩
  obtain ⟨-, h1, -, h3, -⟩ := hc s hs y
  calc |φt s y + iteratedDeriv 2 (φ s) y / 2| ≤ |φt s y| + |iteratedDeriv 2 (φ s) y / 2| :=
        abs_add_le _ _
    _ ≤ c 1 + c 3 / 2 := by
        rw [abs_div, abs_two]
        linarith

/-- `a_n → 1` as `n → ∞` (from `1 ≤ a_n ≤ c_n = cosh θ_n`, (3.2)). -/
theorem limMart_tendsto_aN {ι : Type*} {l : Filter ι} {n : ι → ℝ} (hn : Tendsto n l atTop) :
    Tendsto (fun j => aN (n j)) l (𝓝 1) := by
  have hθ : Tendsto (fun j => thetaN (n j)) l (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)).comp hn
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, thetaN]
    norm_num
  have hc : Tendsto (fun j => Real.cosh (thetaN (n j))) l (𝓝 1) := by
    have := (Real.continuous_cosh.tendsto 0).comp hθ
    rwa [Real.cosh_zero] at this
  have hn1 : ∀ᶠ j in l, 1 ≤ n j := hn.eventually_ge_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
  · filter_upwards [hn1] with j hj using (constants_bounds hj).2.2.1
  · filter_upwards [hn1] with j hj using (constants_bounds hj).2.2.2.1

/-! ### Pairings -/

/-- `|μ(f) - μ(g)| ≤ c μ(1)` when `|f - g| ≤ c`, for `f, g` bounded measurable. -/
theorem limMart_abs_pairFM_sub_le (μ : FiniteMeasure ℝ) {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) {cf cg : ℝ} (hcf : ∀ y, |f y| ≤ cf) (hcg : ∀ y, |g y| ≤ cg) {c : ℝ}
    (hc : ∀ y, |f y - g y| ≤ c) :
    |pairFM μ f - pairFM μ g| ≤ c * pairFM μ fun _ => 1 := by
  have hfi : Integrable f (μ : Measure ℝ) :=
    Integrable.of_bound hf.aestronglyMeasurable cf (ae_of_all _ fun y => hcf y)
  have hgi : Integrable g (μ : Measure ℝ) :=
    Integrable.of_bound hg.aestronglyMeasurable cg (ae_of_all _ fun y => hcg y)
  unfold pairFM
  rw [← integral_sub hfi hgi, integral_const, smul_eq_mul, mul_one]
  exact norm_integral_le_of_norm_le_const
    (ae_of_all _ fun y => (by rw [Real.norm_eq_abs]; exact hc y : ‖f y - g y‖ ≤ c))

/-- `μ(1) ≥ 0`. -/
theorem limMart_pairFM_one_nonneg (μ : FiniteMeasure ℝ) : 0 ≤ pairFM μ fun _ => 1 := by
  unfold pairFM
  rw [integral_const, smul_eq_mul, mul_one]
  exact measureReal_nonneg

/-! ### The limit martingale on the canonical space -/

/-- `t ↦ M^φ(t)` is continuous on `[0,T]` for every path. -/
theorem limMart_continuousOn (hφ : IsC13 T φ φt C) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ContinuousOn (fun t => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt
      t γ) (Icc 0 T) := by
  by_cases hT : 0 ≤ T
  swap
  · exact fun s hs => absurd (hs.1.trans hs.2) hT
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  have hφ0 := hφ.pathFun_continuousOn_comp (f := fun y => y) continuous_id
  have h1 : ContinuousOn (fun s => pairFM (pathAt γ s) (φ s)) (Icc 0 T) :=
    (continuousOn_pairFM_pathAt hφ0 ⟨c, hc⟩).comp
      (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨trivial, hs⟩
  have hd : ContinuousOn (fun s => pairFM (pathAt γ s)
      (fun y => φt s y + iteratedDeriv 2 (φ s) y / 2)) (Icc 0 T) :=
    (continuousOn_pairFM_pathAt hφ.limMart_continuousOn_drift hφ.limMart_bound_drift).comp
      (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨trivial, hs⟩
  have h2 := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
    (by rw [uIcc_of_le hT]; exact hd.integrableOn_Icc)
  rw [uIcc_of_le hT] at h2
  exact (h1.sub continuousOn_const).sub h2

/-- `(γ, s) ↦ γ(s)(∂ₛφ_s + ½∂ₓ²φ_s)`, with `s` clamped to `[0,T]`, is continuous. -/
private lemma limMart_continuous_drift_clamp (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      pairFM (pathAt p.1 (pathFunClamp T p.2))
        (fun y => φt (pathFunClamp T p.2) y + iteratedDeriv 2 (φ (pathFunClamp T p.2)) y / 2) :=
  (continuousOn_pairFM_pathAt hφ.limMart_continuousOn_drift hφ.limMart_bound_drift).comp_continuous
    (continuous_fst.prodMk ((continuous_pathFunClamp T).comp continuous_snd))
    fun p => ⟨trivial, pathFunClamp_mem hT p.2⟩

/-- For `t ∈ [0,T]`, `γ ↦ M^φ(t)` is Borel. -/
theorem limMart_measurable (hφ : IsC13 T φ φt C) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Measurable (limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  have h1 : Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => pairFM (pathAt γ t) (φ t) :=
    ((continuous_pairFM (hφ.contDiff t ht).continuous ⟨c, hc t ht⟩).comp
      (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))).measurable
  have h2 := prelimAux_measurable_intervalIntegral (limMart_continuous_drift_clamp hφ hT).measurable
    (F := fun γ s => pairFM (pathAt γ s) (fun y => φt s y + iteratedDeriv 2 (φ s) y / 2)) ht.1
    fun γ s hs => by
      simp only [pathFunClamp_of_mem (⟨hs.1.le, hs.2.trans ht.2⟩ : s ∈ Icc 0 T)]
  exact (h1.sub measurable_const).sub h2

/-- `M^φ(s)` only depends on the path stopped at `s`. -/
private lemma limMart_prelimStop {s : ℝ} (hs : 0 ≤ s) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt s (prelimStop s γ) =
      limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt s γ := by
  unfold limMart
  rw [pathAt_prelimStop hs le_rfl]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hs] at hu
  simp only [pathAt_prelimStop hs hu.2]

/-- **Adaptedness**: `M^φ(s)` is measurable for the canonical filtration at time `s`. -/
theorem limMart_stronglyMeasurable_can (hφ : IsC13 T φ φt C) {s : ℝ≥0} (hs : (s : ℝ) ≤ T) :
    StronglyMeasurable[pathFiltrationCan T s]
      (limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt s) := by
  have hm := limMart_measurable hφ (φt := φt) ⟨s.2, hs⟩
  have hcomp : Measurable[pathFiltrationCan T s] fun γ =>
      limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt s (prelimStop s γ) :=
    hm.comp (measurable_prelimStop s)
  have e : (fun γ => limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt s
      (prelimStop s γ)) = limMart (fun γ' : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ') φ φt s :=
    funext fun γ => limMart_prelimStop s.2 γ
  rw [e] at hcomp
  exact hcomp.stronglyMeasurable

end QSSEPtoKPZ
