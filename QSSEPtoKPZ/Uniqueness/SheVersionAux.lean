/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace

/-!
# Deterministic tools for the version on `Ω'` (task K5)

Auxiliary results for `exists_sheVersion_map_eq` (`Uniqueness/SheVersion.lean`), see
`docs/stage4-design.md`, Section 1.2 (h), third item (decision D2″).

* The Stage 3 bumps `f_j = β((m+1)x - k)` (`j ≥ 1`) have compact support, and a continuous `g`
  with `g(x₀) < 0` has `∫ g f_j < 0` for some `j ≥ 1` (`sheVer_exists_bump_neg`).
* `sheVer_eq_withDensity_of_bump`: if a finite measure `μ` and a continuous `g` satisfy
  `μ(f_j) = ∫ g f_j` for all `j ≥ 1`, then `g ≥ 0` and `μ = g(x) dx` (the total masses agree by
  the partition of unity `∑_k β(x - k) = 1`; then `(f_j)_{j ≥ 0}` determines finite measures).
* `sheVer_exists_dense`: a set of full measure in `(0,T]` contains a countable set whose closure
  contains `[0,T]` (the good times `D`).
* `sheVerEmb D`: the map `ι(γ) = (γ(t)(f_j))_{t ∈ D, j}`, continuous, injective if `D` is dense.
* `sheVer_exists_measurable_inv`: a continuous injective map into a Hausdorff Borel space has a
  measurable left inverse on any countable union of images of compact sets (each restriction is a
  closed embedding); this replaces Lusin–Souslin.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### The bumps -/

/-- `x ↦ β(c x - b)` has compact support (in `[(b-1)/c, (b+1)/c]`) for `c > 0`. -/
theorem sheVer_hasCompactSupport_affine {c : ℝ} (hc : 0 < c) (b : ℝ) :
    HasCompactSupport fun x => bumpBeta (c * x - b) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (b - 1) / c) (b := (b + 1) / c))
    fun x hx => bumpBeta_eq_zero_of_one_le_abs ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [lt_div_iff₀ hc] at h
    exact le_abs.2 (Or.inr (by linarith))
  · rw [div_lt_iff₀ hc] at h
    exact le_abs.2 (Or.inl (by linarith))

/-- For `j ≥ 1`, the bump `f_j` has compact support. -/
theorem sheVer_hasCompactSupport_bumpTestRaw {j : ℕ} (hj : 1 ≤ j) :
    HasCompactSupport (bumpTestRaw j) := by
  cases j with
  | zero => omega
  | succ i => exact sheVer_hasCompactSupport_affine (by positivity) _

/-- `f_j ≥ 0`. -/
theorem sheVer_bumpTestRaw_nonneg (j : ℕ) (x : ℝ) : 0 ≤ bumpTestRaw j x := by
  cases j with
  | zero => simp [bumpTestRaw]
  | succ i => exact bumpBeta_nonneg _

/-- `β(y) > 0` for `|y| < 1`. -/
theorem sheVer_bumpBeta_pos {y : ℝ} (hy : |y| < 1) : 0 < bumpBeta y := by
  unfold bumpBeta
  rcases le_or_gt y 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith [neg_abs_le y])
  · rw [Real.smoothTransition.one_of_one_le (by linarith)]
    linarith [Real.smoothTransition.lt_one_of_lt_one (show y < 1 by linarith [le_abs_self y])]

/-- The bump `f_{encode(0,k)+1}` is `x ↦ β(x - k)`. -/
theorem sheVer_bumpTestRaw_unit (k : ℤ) (x : ℝ) :
    bumpTestRaw (Encodable.encode ((0 : ℕ), k) + 1) x = bumpBeta (x - k) := by
  rw [bumpTestRaw_encode_succ]
  simp

/-- **Sign test.** If `g` is continuous and `g(x₀) < 0`, some bump `f_j` (`j ≥ 1`) has
`∫ g f_j < 0`. -/
theorem sheVer_exists_bump_neg {g : ℝ → ℝ} (hg : Continuous g) {x₀ : ℝ} (hx₀ : g x₀ < 0) :
    ∃ j, 1 ≤ j ∧ (∫ x, g x * bumpTestRaw j x) < 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hg x₀ (-g x₀) (by linarith)
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ)
  have hc0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : |((m : ℝ) + 1) * x₀ - (round (((m : ℝ) + 1) * x₀) : ℤ)| ≤ 1 / 2 :=
    abs_sub_round _
  refine ⟨Encodable.encode (m, round (((m : ℝ) + 1) * x₀)) + 1, by omega, ?_⟩
  rw [bumpTestRaw_encode_succ]
  set k : ℤ := round (((m : ℝ) + 1) * x₀)
  have h2δ : 2 < δ * ((m : ℝ) + 1) := by
    rw [div_lt_iff₀ hδ] at hm
    linarith
  have hsupp : ∀ x, bumpBeta (((m : ℝ) + 1) * x - k) ≠ 0 → g x < 0 := by
    intro x hx
    have h1 : |((m : ℝ) + 1) * x - k| < 1 := by
      by_contra h
      exact hx (bumpBeta_eq_zero_of_one_le_abs (not_lt.1 h))
    have e : (((m : ℝ) + 1) * x - k) - (((m : ℝ) + 1) * x₀ - k) = (x - x₀) * ((m : ℝ) + 1) := by
      ring
    have h3 := abs_sub (((m : ℝ) + 1) * x - k) (((m : ℝ) + 1) * x₀ - k)
    rw [e, abs_mul, abs_of_pos hc0] at h3
    have h4 : |x - x₀| < δ := by
      by_contra h
      have : δ * ((m : ℝ) + 1) ≤ |x - x₀| * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (not_lt.1 h) hc0.le
      linarith
    have h5 := hball x (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at h5
    linarith [le_abs_self (g x - g x₀)]
  have hFc : Continuous fun x => -(g x * bumpBeta (((m : ℝ) + 1) * x - k)) :=
    (hg.mul (continuous_bumpBeta.comp ((continuous_const.mul continuous_id).sub
      continuous_const))).neg
  have hFs : HasCompactSupport fun x => -(g x * bumpBeta (((m : ℝ) + 1) * x - k)) :=
    ((sheVer_hasCompactSupport_affine hc0 (k : ℝ)).mul_left (f := g)).neg
  have hF0 : 0 ≤ fun x => -(g x * bumpBeta (((m : ℝ) + 1) * x - k)) := by
    intro x
    by_cases h : bumpBeta (((m : ℝ) + 1) * x - k) = 0
    · simp [h]
    · have h1 := hsupp x h
      have h2 := bumpBeta_nonneg (((m : ℝ) + 1) * x - k)
      simp only [Pi.zero_apply]
      nlinarith
  have hFx : (fun x => -(g x * bumpBeta (((m : ℝ) + 1) * x - k))) x₀ ≠ 0 := by
    have hb := sheVer_bumpBeta_pos (y := ((m : ℝ) + 1) * x₀ - k) (by linarith)
    have : 0 < -(g x₀ * bumpBeta (((m : ℝ) + 1) * x₀ - k)) := by nlinarith
    exact this.ne'
  have := hFc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hFs hF0 hFx
  rw [integral_neg] at this
  linarith

/-! ### Identification of a measure from its bump integrals -/

/-- `∫ f d(g dx) = ∫ g f` for a nonnegative measurable density `g`. -/
theorem sheVer_integral_withDensity {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (g x)) = ∫ x, g x * f x := by
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  ext x
  rw [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul]

/-- Partition of unity under an integral: `∫⁻ F dρ = ∑_k ∫ F(x) β(x - k) dρ` for `F ≥ 0`. -/
private lemma sheVer_lintegral_partition {ρ : Measure ℝ} {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ F x)
    (hint : ∀ k : ℤ, Integrable (fun x => F x * bumpBeta (x - k)) ρ) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂ρ = ∑' k : ℤ, ENNReal.ofReal (∫ x, F x * bumpBeta (x - k) ∂ρ) := by
  have h1 : ∀ x, ENNReal.ofReal (F x) = ∑' k : ℤ, ENNReal.ofReal (F x * bumpBeta (x - k)) := by
    intro x
    have hs := (hasSum_bumpBeta_sub x).mul_left (F x)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hF0 x) (bumpBeta_nonneg _))
      hs.summable, hs.tsum_eq, mul_one]
  simp_rw [h1]
  rw [lintegral_tsum fun k => (hint k).aemeasurable.ennreal_ofReal]
  refine tsum_congr fun k => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hint k)
    (ae_of_all _ fun x => mul_nonneg (hF0 x) (bumpBeta_nonneg _))]

/-- **A finite measure with continuous bump integrals `∫ g f_j` is `g(x) dx`, and `g ≥ 0`.** -/
theorem sheVer_eq_withDensity_of_bump {μ : FiniteMeasure ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ j, 1 ≤ j → pairFM μ (bumpTestRaw j) = ∫ x, g x * bumpTestRaw j x) :
    (∀ x, 0 ≤ g x) ∧ (μ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (g x) := by
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_contra hx
    obtain ⟨j, hj, hneg⟩ := sheVer_exists_bump_neg hg (not_le.1 hx)
    have hpos : 0 ≤ pairFM μ (bumpTestRaw j) :=
      integral_nonneg fun x => sheVer_bumpTestRaw_nonneg j x
    linarith [h j hj]
  refine ⟨hg0, ?_⟩
  set L : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (g x) with hL
  have hβ : ∀ k : ℤ, (fun x => bumpBeta (x - k)) =
      bumpTestRaw (Encodable.encode ((0 : ℕ), k) + 1) := fun k => by
    funext x
    rw [sheVer_bumpTestRaw_unit]
  have hint : ∀ k : ℤ, Integrable (fun x => g x * bumpBeta (x - k)) := by
    intro k
    have hcs : HasCompactSupport (fun x => bumpBeta (x - k)) := by
      rw [hβ k]
      exact sheVer_hasCompactSupport_bumpTestRaw (by omega)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => g x * bumpBeta (x - k))
      (hg.mul (continuous_bumpBeta.comp (continuous_id.sub continuous_const)))
      (hcs.mul_left (f := g))
  have hintμ : ∀ k : ℤ, Integrable (fun x => (fun _ => (1 : ℝ)) x * bumpBeta (x - k))
      (μ : Measure ℝ) := by
    intro k
    have : (fun x => (fun _ => (1 : ℝ)) x * bumpBeta (x - k)) =
        ⇑(bumpTest (Encodable.encode ((0 : ℕ), k) + 1)) := by
      funext x
      rw [coe_bumpTest, sheVer_bumpTestRaw_unit, one_mul]
    rw [this]
    exact (bumpTest _).integrable _
  have hmass : L univ = (μ : Measure ℝ) univ := by
    rw [hL, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      sheVer_lintegral_partition hg0 hint]
    have h2 := sheVer_lintegral_partition (ρ := (μ : Measure ℝ)) (F := fun _ => (1 : ℝ))
      (fun _ => zero_le_one) hintμ
    simp only [ENNReal.ofReal_one, lintegral_one, one_mul] at h2
    rw [h2]
    refine tsum_congr fun k => ?_
    have := h (Encodable.encode ((0 : ℕ), k) + 1) (by omega)
    rw [← hβ k] at this
    unfold pairFM at this
    rw [this]
  have hfin : IsFiniteMeasure L := ⟨by rw [hmass]; exact measure_lt_top _ _⟩
  let LF : FiniteMeasure ℝ := ⟨L, hfin⟩
  have hemb : tightEmb LF = tightEmb μ := by
    funext j
    simp only [tightEmb, coe_bumpTest]
    change ∫ x, bumpTestRaw j x ∂L = _
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [bumpTestRaw_zero, integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, hmass]
    · rw [hL, sheVer_integral_withDensity hg.measurable hg0, ← h j hj]
      rfl
  have := isEmbedding_tightEmb.injective hemb
  rw [← this]
  rfl

/-- Continuity in `t > 0` of `∫ g(t,x) f_j(x) dx` for `g` continuous on `(0,∞) × ℝ`, `j ≥ 1`. -/
theorem sheVer_continuousOn_integral {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ioi 0 ×ˢ univ)) {j : ℕ} (hj : 1 ≤ j) :
    ContinuousOn (fun t => ∫ x, g t x * bumpTestRaw j x) (Ioi 0) := by
  refine continuousOn_integral_of_compact_support (k := tsupport (bumpTestRaw j))
    (sheVer_hasCompactSupport_bumpTestRaw hj) ?_ ?_
  · exact hg.mul ((continuous_bumpTestRaw j).comp continuous_snd).continuousOn
  · intro t x _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-! ### Good times -/

/-- **Countable dense good times.** A set of full measure in `(0,T]` contains a countable set
`D ⊆ (0,T]` whose closure contains `[0,T]`. -/
theorem sheVer_exists_dense {T : ℝ} (hT : 0 < T) {A : Set ℝ}
    (hA : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), t ∈ A) :
    ∃ D : Set ℝ, D ⊆ A ∧ D ⊆ Ioc 0 T ∧ D.Countable ∧ Icc 0 T ⊆ closure D := by
  obtain ⟨D, hDs, hDc, hDcl⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (A ∩ Ioc 0 T)).exists_countable_dense_subset
  refine ⟨D, fun x hx => (hDs hx).1, fun x hx => (hDs hx).2, hDc, fun t ht => ?_⟩
  have hnull : volume ({t | t ∉ A} ∩ Ioc 0 T) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc, ae_iff] at hA
    exact measure_mono_null (fun s hs => not_imp.2 ⟨hs.2, hs.1⟩) hA
  refine closure_minimal hDcl isClosed_closure ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hsub : Ioo (max 0 (t - ε)) (min T (t + ε)) ⊆ {t | t ∉ A} ∩ Ioc 0 T := by
    intro b hb
    simp only [mem_Ioo, max_lt_iff, lt_min_iff] at hb
    have hbI : b ∈ Ioc 0 T := ⟨hb.1.1, hb.2.1.le⟩
    refine ⟨fun hbA => ?_, hbI⟩
    have := hcon b ⟨hbA, hbI⟩
    rw [Real.dist_eq, abs_sub_comm] at this
    have : |b - t| < ε := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  have hpos : 0 < volume (Ioo (max 0 (t - ε)) (min T (t + ε))) := by
    rw [Real.volume_Ioo]
    refine ENNReal.ofReal_pos.2 (sub_pos.2 ?_)
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [ht.1, ht.2]
  exact hpos.ne' (measure_mono_null hsub hnull)

/-! ### The embedding `ι` -/

/-- `ι(γ) = (γ(d)(f_j))_{d ∈ D, j}`, with `γ(d)(f_j)` the coordinates of `tightEmb (γ(d))`. -/
def sheVerEmb {T : ℝ} (D : Set ℝ) (γ : C(Icc (0 : ℝ) T, FiniteMeasure ℝ)) : D → ℕ → ℝ :=
  fun d => tightEmb (pathAt γ d)

/-- `ι` is continuous. -/
theorem continuous_sheVerEmb {T : ℝ} (D : Set ℝ) : Continuous (sheVerEmb (T := T) D) :=
  continuous_pi fun _ => continuous_tightEmb.comp
    (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))

/-- `ι` is injective when `[0,T] ⊆ closure D`. -/
theorem sheVerEmb_injective {T : ℝ} {D : Set ℝ} (hD : Icc 0 T ⊆ closure D) :
    Function.Injective (sheVerEmb (T := T) D) := by
  intro γ γ' h
  have h1 : EqOn (pathAt γ) (pathAt γ') D := fun d hd =>
    isEmbedding_tightEmb.injective (congrFun h ⟨d, hd⟩)
  have hc : ∀ γ : C(Icc (0 : ℝ) T, FiniteMeasure ℝ), Continuous (pathAt γ) := fun γ =>
    continuous_pathAt_prod.comp (continuous_const.prodMk continuous_id)
  have h2 := h1.closure (hc γ) (hc γ')
  refine ContinuousMap.ext fun t => ?_
  obtain ⟨t, ht⟩ := t
  rw [← pathAt_of_mem γ ht, ← pathAt_of_mem γ' ht]
  exact h2 (hD ht)

/-! ### A measurable inverse on a σ-compact set -/

/-- **Measurable inverse on a σ-compact set** (replaces Lusin–Souslin). A continuous injective map
`ι` into a Hausdorff Borel space has a measurable map `G` with `ι (G y) = y` on the (measurable)
union of the images of countably many compact sets. -/
theorem sheVer_exists_measurable_inv {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [BorelSpace Y] {ι : X → Y} (hc : Continuous ι) (hi : Function.Injective ι) {K : ℕ → Set X}
    (hK : ∀ m, IsCompact (K m)) :
    ∃ G : Y → X, Measurable G ∧ MeasurableSet (⋃ m, ι '' K m) ∧
      ∀ y ∈ ⋃ m, ι '' K m, ι (G y) = y := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hBm : MeasurableSet (⋃ m, ι '' K m) :=
    MeasurableSet.iUnion fun m => ((hK m).image hc).isClosed.measurableSet
  have hemb : ∀ m, MeasurableEmbedding (fun k : K m => ι k) := fun m => by
    have := isCompact_iff_compactSpace.1 (hK m)
    exact (Continuous.isClosedEmbedding (hc.comp continuous_subtype_val)
      (hi.comp Subtype.val_injective)).measurableEmbedding
  let Gm : ℕ → Y → X := fun m => Function.extend (fun k : K m => ι k) Subtype.val fun _ => x₀
  have hGm : ∀ m, Measurable (Gm m) := fun m =>
    (hemb m).measurable_extend measurable_subtype_coe measurable_const
  let f : ℕ → Y → X := fun n => match n with
    | 0 => fun _ => x₀
    | m + 1 => Gm m
  let p : ℕ → Y → Prop := fun n y => match n with
    | 0 => y ∉ ⋃ m, ι '' K m
    | m + 1 => y ∈ ι '' K m
  have hf : ∀ n, Measurable (f n) := fun n => by
    cases n
    · exact measurable_const
    · exact hGm _
  have hp : ∀ n, MeasurableSet {y | p n y} := fun n => by
    cases n
    · exact hBm.compl
    · exact ((hK _).image hc).isClosed.measurableSet
  have hex : ∀ y, ∃ n, p n y := fun y => by
    by_cases hy : y ∈ ⋃ m, ι '' K m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hy
      exact ⟨m + 1, hm⟩
    · exact ⟨0, hy⟩
  refine ⟨fun y => f (Nat.find (hex y)) y, Measurable.find hf hp hex, hBm, fun y hy => ?_⟩
  have hs := Nat.find_spec (hex y)
  show ι (f (Nat.find (hex y)) y) = y
  generalize Nat.find (hex y) = n at hs ⊢
  cases n with
  | zero => exact absurd hy hs
  | succ m =>
    obtain ⟨k, hk, rfl⟩ := hs
    have := (hemb m).injective.extend_apply Subtype.val (fun _ => x₀) ⟨k, hk⟩
    simp only at this
    change ι (Gm m (ι k)) = ι k
    simp only [Gm, this]

end QSSEPtoKPZ
