/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.SecondMomentConv
public import QSSEPtoKPZ.Uniqueness.SecondMomentVersion

/-!
# The renewal equation `F = K + K ⋆ F` and its iteration (task K2)

For a jointly measurable solution `Z` of (1.13), `F(t,x) = 𝔼[Z(t,x)²]` satisfies, for every
`t > 0` and `x` (Itô's isometry **W**, `𝔼 Z(t,x) = g_t(x)` and Tonelli),
`F(t,x) = K(t,x) + (K ⊛ F)(t,x)` with `K(t,x) = g_t(x)²` (`secondMom_base`). Iterating with the
associativity of `⊛` and `K ⊛ K^{⋆k} = K^{⋆(k+1)}`:
`F = ∑_{k=1}^{N+1} K^{⋆k} + K^{⋆(N+1)} ⊛ F`, and `K^{⋆(N+1)} ⊛ F ≤ ε_N (K ⊛ F) ≤ ε_N F` with
`ε_N → 0`; since `F(t,x) < ∞`, `F = ∑_{k ≥ 1} K^{⋆k}` (`secondMom_hasSum_of_measurable`, (7.15) in
series form). For the difference `D = 𝔼[(Z - Z')²]` of two solutions, `D = K ⊛ D`, hence
`D = K^{⋆(N+1)} ⊛ D ≤ ε_N D`, so `D = 0` (`secondMom_ae_eq_of_measurable`, the core of **U3**).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- **Itô's isometry and Tonelli** for an integrand of the mild form: if
`X = ∫∫ 𝟙_{0<s<t} g_{t-s}(x-y) W(s,y) ξ(ds dy)`, then `𝔼[X²] < ∞` and
`𝔼[X²] = ∫∫_{(0,t) × ℝ} g_{t-s}(x-y)² 𝔼[W(s,y)²] ds dy`. -/
theorem secondMom_lintegral_sq (hS : IsWhiteNoise 𝓖 S ν) {W : ℝ → ℝ → Ω → ℝ} {t x : ℝ}
    {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatKernel (t - s) (x - y) * W s y ω else 0) X) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂ν < ⊤ ∧
      ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂ν =
        secondMomConv (secondMomK 0) (fun s y => ∫⁻ ω, ENNReal.ofReal (W s y ω ^ 2) ∂ν) t x := by
  have := hS.isProbabilityMeasure
  obtain ⟨hh, hX2, heq⟩ := IsWalshIntegral.isometry_lib hS hX
  have h1 : ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂ν = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hX2.integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _)).symm
  refine ⟨h1 ▸ ENNReal.ofReal_lt_top, ?_⟩
  rw [h1, heq, ofReal_integral_eq_lintegral_ofReal hh.integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _),
    lintegral_prod_symm _ (hh.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal,
    secondMomConv, ← lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
  refine lintegral_congr fun q => ?_
  simp only [uncurryField, Set.indicator_apply, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true]
  by_cases hq : 0 < q.1 ∧ q.1 < t
  · simp only [hq, and_self, ↓reduceIte]
    simp_rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, secondMomK, secondMom_heatSqIter_zero]
  · simp only [hq, ↓reduceIte]
    simp

/-- `𝔼[Z(t,x)²]` as a function of `(t,x)` is measurable for a jointly measurable field. -/
theorem secondMom_measurable_moment {W : ℝ → ℝ → Ω → ℝ} [SFinite ν]
    (hW : Measurable (uncurryField W)) :
    Measurable (Function.uncurry fun s y => ∫⁻ ω, ENNReal.ofReal (W s y ω ^ 2) ∂ν) :=
  Measurable.lintegral_prod_left' (μ := ν)
    (f := fun p : Ω × ℝ × ℝ => ENNReal.ofReal (uncurryField W p ^ 2))
    (hW.pow_const 2).ennreal_ofReal

/-- **The renewal equation** `F = K + K ⊛ F` at a point `(t,x)`, `t > 0`, with `F(t,x) < ∞`. -/
theorem secondMom_base (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Z t x ω ^ 2) ∂ν < ⊤ ∧
      ∫⁻ ω, ENNReal.ofReal (Z t x ω ^ 2) ∂ν = secondMomK 0 t x +
        secondMomConv (secondMomK 0) (fun s y => ∫⁻ ω, ENNReal.ofReal (Z s y ω ^ 2) ∂ν) t x := by
  have := hS.isProbabilityMeasure
  have hX := hZ.mild t x ht
  obtain ⟨-, heq⟩ := secondMom_lintegral_sq hS hX
  have hX2 := (IsWalshIntegral.isometry_lib hS hX).2.1
  have hmean := secondMom_walsh_integral_eq_zero hS hX
  have hZ2 := secondMom_memLp hS hZ ht x
  set g := heatKernel t x
  have h1 : ∫⁻ ω, ENNReal.ofReal (Z t x ω ^ 2) ∂ν = ENNReal.ofReal (∫ ω, Z t x ω ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hZ2.integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _)).symm
  have hsplit : ∫ ω, Z t x ω ^ 2 ∂ν = ∫ ω, (Z t x ω - g) ^ 2 ∂ν + g ^ 2 := by
    have e : ∀ ω, Z t x ω ^ 2 = (Z t x ω - g) ^ 2 + (2 * g * (Z t x ω - g) + g ^ 2) :=
      fun ω => by ring
    simp_rw [e]
    have hi : Integrable (fun ω => Z t x ω - g) ν := hX2.integrable one_le_two
    have hi2 : Integrable (fun ω => 2 * g * (Z t x ω - g) + g ^ 2) ν :=
      (hi.const_mul _).add (integrable_const _)
    rw [integral_add hX2.integrable_sq hi2,
      integral_add (hi.const_mul _) (integrable_const _), integral_const_mul, hmean]
    simp
  refine ⟨h1 ▸ ENNReal.ofReal_lt_top, ?_⟩
  rw [h1, hsplit, ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hX2.integrable_sq (ae_of_all _ fun _ => sq_nonneg _),
    heq, secondMomK, secondMom_heatSqIter_zero, add_comm]

/-- Iteration of the renewal equation:
`C = ∑_{k=0}^{N} K^{⋆(k+1)} + K^{⋆(N+1)} ⊛ C` on `(0,∞) × ℝ`. -/
theorem secondMom_iter {C : ℝ → ℝ → ℝ≥0∞} (hC : Measurable (Function.uncurry C))
    (hbase : ∀ t, 0 < t → ∀ x, C t x = secondMomK 0 t x + secondMomConv (secondMomK 0) C t x)
    (N : ℕ) : ∀ t, 0 < t → ∀ x,
      C t x = ∑ k ∈ Finset.range (N + 1), secondMomK k t x + secondMomConv (secondMomK N) C t x := by
  induction N with
  | zero => intro t ht x; simpa using hbase t ht x
  | succ N ih =>
    intro t ht x
    have hK : secondMomConv (secondMomK 0) (secondMomK N) = secondMomK (N + 1) :=
      funext₂ fun r z => secondMomConv_K_iter N r z
    have hsum : Measurable (Function.uncurry fun s y =>
        ∑ k ∈ Finset.range (N + 1), secondMomK k s y) := by
      have : (Function.uncurry fun s y => ∑ k ∈ Finset.range (N + 1), secondMomK k s y) =
          fun p => ∑ k ∈ Finset.range (N + 1), Function.uncurry (secondMomK k) p := rfl
      rw [this]
      exact Finset.measurable_sum _ fun k _ => measurable_secondMomK k
    rw [hbase t ht x, secondMomConv_congr_right (B' := fun s y =>
        ∑ k ∈ Finset.range (N + 1), secondMomK k s y + secondMomConv (secondMomK N) C s y)
        (fun s y hs _ => ih s hs y),
      secondMomConv_add (measurable_secondMomK 0) hsum,
      secondMomConv_finset_sum (measurable_secondMomK 0) measurable_secondMomK,
      secondMomConv_assoc (measurable_secondMomK 0) (measurable_secondMomK N) hC, hK,
      Finset.sum_range_succ' _ (N + 1)]
    simp_rw [secondMomConv_K_iter]
    ring

/-- Iteration of the homogeneous equation `D = K ⊛ D`: `D = K^{⋆(N+1)} ⊛ D` on `(0,∞) × ℝ`. -/
theorem secondMom_iter_zero {C : ℝ → ℝ → ℝ≥0∞} (hC : Measurable (Function.uncurry C))
    (hbase : ∀ t, 0 < t → ∀ x, C t x = secondMomConv (secondMomK 0) C t x)
    (N : ℕ) : ∀ t, 0 < t → ∀ x, C t x = secondMomConv (secondMomK N) C t x := by
  induction N with
  | zero => exact hbase
  | succ N ih =>
    intro t ht x
    have hK : secondMomConv (secondMomK 0) (secondMomK N) = secondMomK (N + 1) :=
      funext₂ fun r z => secondMomConv_K_iter N r z
    rw [hbase t ht x, secondMomConv_congr_right (B' := secondMomConv (secondMomK N) C)
        (fun s y hs _ => ih s hs y),
      secondMomConv_assoc (measurable_secondMomK 0) (measurable_secondMomK N) hC, hK]

/-- `K^{⋆(k+1)} ⊛ C ≤ ε_k (K ⊛ C)` at `(t,x)`, from `K^{⋆(k+1)} ≤ ε_k K` on `(0,t]`. -/
theorem secondMom_conv_le {C : ℝ → ℝ → ℝ≥0∞} {t : ℝ} (x : ℝ) {ε : ℕ → ℝ}
    (hε0 : ∀ k, 0 ≤ ε k)
    (hε : ∀ k, ∀ r ∈ Set.Ioc (0 : ℝ) t, ∀ z, heatSqIter k r z ≤ ε k * heatKernel r z ^ 2)
    (k : ℕ) :
    secondMomConv (secondMomK k) C t x ≤
      ENNReal.ofReal (ε k) * secondMomConv (secondMomK 0) C t x := by
  calc secondMomConv (secondMomK k) C t x
      ≤ secondMomConv (fun r z => ENNReal.ofReal (ε k) * secondMomK 0 r z) C t x := by
        refine secondMomConv_mono_left fun r z hr hrt => ?_
        rw [secondMomK, secondMomK, secondMom_heatSqIter_zero, ← ENNReal.ofReal_mul (hε0 k)]
        exact ENNReal.ofReal_le_ofReal (hε k r ⟨hr, hrt⟩ z)
    _ = _ := secondMomConv_const_mul_left ENNReal.ofReal_ne_top _ _ _ _

/-- **(7.15) in series form** for a jointly measurable solution:
`𝔼[Z(t,x)²] = ∑_{k ≥ 0} K^{⋆(k+1)}(t,x)` (`t > 0`). -/
theorem secondMom_hasSum_of_measurable (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) (hZm : Measurable (uncurryField Z)) {t x : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => heatSqIter k t x) (∫ ω, Z t x ω ^ 2 ∂ν) := by
  have := hS.isProbabilityMeasure
  set F : ℝ → ℝ → ℝ≥0∞ := fun s y => ∫⁻ ω, ENNReal.ofReal (Z s y ω ^ 2) ∂ν with hFdef
  have hFm : Measurable (Function.uncurry F) := secondMom_measurable_moment hZm
  have hbase : ∀ s, 0 < s → ∀ y, F s y = secondMomK 0 s y + secondMomConv (secondMomK 0) F s y :=
    fun s hs y => (secondMom_base hS hZ hs y).2
  have hfin : F t x ≠ ⊤ := (secondMom_base hS hZ ht x).1.ne
  obtain ⟨ε, hεs, hε0, hε⟩ := heatSqIter_le t
  set a : ℕ → ℝ := fun N => ∑ k ∈ Finset.range (N + 1), heatSqIter k t x with hadef
  set Fr : ℝ := (F t x).toReal with hFr
  have hint : ∫ ω, Z t x ω ^ 2 ∂ν = Fr := by
    rw [hFr, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (secondMom_memLp hS hZ ht x).integrable_sq.aestronglyMeasurable]
  -- the two-sided bound `a N ≤ F ≤ a N + ε_N F`
  have hbound : ∀ N, a N ≤ Fr ∧ Fr - ε N * Fr ≤ a N := by
    intro N
    have hit := secondMom_iter hFm hbase N t ht x
    set R := secondMomConv (secondMomK N) F t x
    have hR : R ≤ ENNReal.ofReal (ε N) * F t x := by
      refine (secondMom_conv_le x hε0 (fun k r hr z => hε k r ⟨hr.1, hr.2⟩ z) N).trans ?_
      gcongr
      rw [hbase t ht x]
      exact le_add_self
    have hsum : ∑ k ∈ Finset.range (N + 1), secondMomK k t x = ENNReal.ofReal (a N) := by
      rw [hadef, ENNReal.ofReal_sum_of_nonneg fun k _ => heatSqIter_nonneg _ _ _]
      rfl
    rw [hsum] at hit
    have hRfin : R ≠ ⊤ := fun h => hfin (by rw [hit, h, add_top])
    have ha0 : 0 ≤ a N := Finset.sum_nonneg fun k _ => heatSqIter_nonneg _ _ _
    have hFeq : Fr = a N + R.toReal := by
      rw [hFr, hit, ENNReal.toReal_add ENNReal.ofReal_ne_top hRfin, ENNReal.toReal_ofReal ha0]
    have hRle : R.toReal ≤ ε N * Fr := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hR
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hε0 N)] at this
    exact ⟨by linarith [ENNReal.toReal_nonneg (a := R)], by linarith⟩
  have hlim : Tendsto a atTop (𝓝 Fr) := by
    have h0 : Tendsto (fun N => Fr - ε N * Fr) atTop (𝓝 Fr) := by
      simpa using tendsto_const_nhds.sub (hεs.tendsto_atTop_zero.mul_const Fr)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds
      (fun N => (hbound N).2) (fun N => (hbound N).1)
  rw [hint, hasSum_iff_tendsto_nat_of_nonneg (fun k => heatSqIter_nonneg _ _ _)]
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hlim

/-- **Core of U3** for jointly measurable solutions: two such solutions agree almost surely at
each point `(t,x)`, `t > 0`. -/
theorem secondMom_ae_eq_of_measurable (hS : IsWhiteNoise 𝓖 S ν) {Z Z' : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) (hZ' : IsMildSolution 𝓖 S Z' ν)
    (hZm : Measurable (uncurryField Z)) (hZm' : Measurable (uncurryField Z'))
    {t : ℝ} (ht : 0 < t) (x : ℝ) : Z t x =ᵐ[ν] Z' t x := by
  have := hS.isProbabilityMeasure
  set W : ℝ → ℝ → Ω → ℝ := fun s y ω => Z s y ω - Z' s y ω with hWdef
  have hWm : Measurable (uncurryField W) := hZm.sub hZm'
  set D : ℝ → ℝ → ℝ≥0∞ := fun s y => ∫⁻ ω, ENNReal.ofReal (W s y ω ^ 2) ∂ν with hDdef
  have hDm : Measurable (Function.uncurry D) := secondMom_measurable_moment hWm
  have hbase : ∀ s, 0 < s → ∀ y, D s y < ⊤ ∧ D s y = secondMomConv (secondMomK 0) D s y := by
    intro s hs y
    have hX : IsWalshIntegral 𝓖 S ν
        (fun r z ω => if 0 < r ∧ r < s then heatKernel (s - r) (y - z) * W r z ω else 0)
        (fun ω => (Z s y ω - heatKernel s y) - (Z' s y ω - heatKernel s y)) := by
      convert (hZ.mild s y hs).sub (hZ'.mild s y hs) using 1
      funext r z ω
      split_ifs <;> simp [hWdef, mul_sub]
    obtain ⟨h1, h2⟩ := secondMom_lintegral_sq hS hX
    have e : ∀ ω, (Z s y ω - heatKernel s y - (Z' s y ω - heatKernel s y)) ^ 2 = W s y ω ^ 2 :=
      fun ω => by simp only [hWdef]; ring
    simp_rw [e] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨ε, hεs, hε0, hε⟩ := heatSqIter_le t
  have hD0 : D t x = 0 := by
    have hfin := (hbase t ht x).1.ne
    have hle : ∀ N, (D t x).toReal ≤ ε N * (D t x).toReal := by
      intro N
      have h := (secondMom_iter_zero hDm (fun s hs y => (hbase s hs y).2) N t ht x).trans_le
        (secondMom_conv_le x hε0 (fun k r hr z => hε k r ⟨hr.1, hr.2⟩ z) N)
      rw [← (hbase t ht x).2] at h
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hε0 N)] at this
    have hlim : Tendsto (fun N => ε N * (D t x).toReal) atTop (𝓝 0) := by
      simpa using hεs.tendsto_atTop_zero.mul_const (D t x).toReal
    have hle0 : (D t x).toReal ≤ 0 := ge_of_tendsto' hlim hle
    rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hle0 ENNReal.toReal_nonneg) with h | h
    · exact h
    · exact absurd h hfin
  have hWtm : Measurable (W t x) :=
    hWm.comp (f := fun ω => (ω, t, x)) (measurable_id.prodMk measurable_const)
  have hz := (lintegral_eq_zero_iff (hWtm.pow_const 2).ennreal_ofReal).1 hD0
  filter_upwards [hz] with ω hω
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
  have : W t x ω = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hω (sq_nonneg _))
  simp only [hWdef] at this
  linarith

end QSSEPtoKPZ
