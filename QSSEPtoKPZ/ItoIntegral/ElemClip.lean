/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.ElemGrid

/-!
# Clipping an elementary integrand on a time interval (package C, task C2, auxiliary)

Let `e` be an elementary integrand, `u ≤ v` and `K ≥ 0`. The clipped integrand
`elemClip e u v K` is the elementary integrand equal to `e` outside `(u, v]` and to the radial
projection `π_K(e(r)) = e(r) min(1, √K / |e(r)|)` of `e(r)` onto the ball of radius `√K` of
`ℓ²(ι)` for `r ∈ (u, v]` (`elemClip_toFun`). It is built on the grid of the endpoints of `e`
and of `u`, `v`: on each cell `(p, p⁺]` between consecutive grid points, `e` is constant in time
and the clipped coefficient is a measurable function of the `𝓖_p`-measurable values `eᵢ(p⁺)`.

* `elemClip_sq_le`: `∑ᵢ π_K(e(r))ᵢ² ≤ K`.
* `elemClip_dist_le`: the projection is `1`-Lipschitz towards points of the ball:
  `∑ᵢ ‖π_K(e(r))ᵢ - yᵢ‖² ≤ ∑ᵢ ‖eᵢ(r) - yᵢ‖²` (in `[0, ∞]`) if `∑ᵢ yᵢ² ≤ K` whenever the
  series converges.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*}

/-! ### The successor of a point in a finite grid -/

/-- The smallest point of `P` larger than `p` (`p` itself if there is none). -/
def elemClipNext (P : Finset ℝ≥0) (p : ℝ≥0) : ℝ≥0 :=
  if h : (P.filter (p < ·)).Nonempty then (P.filter (p < ·)).min' h else p

/-- `p ≤ p⁺`. -/
lemma le_elemClipNext (P : Finset ℝ≥0) (p : ℝ≥0) : p ≤ elemClipNext P p := by
  unfold elemClipNext
  split_ifs with h
  · exact (Finset.mem_filter.1 ((P.filter (p < ·)).min'_mem h)).2.le
  · exact le_rfl

/-- `p⁺ ≤ q` for every grid point `q > p`. -/
lemma elemClipNext_le {P : Finset ℝ≥0} {p q : ℝ≥0} (hq : q ∈ P) (hpq : p < q) :
    elemClipNext P p ≤ q := by
  have hne : (P.filter (p < ·)).Nonempty := ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩
  simp only [elemClipNext, hne, ↓reduceDIte]
  exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hq, hpq⟩)

/-- If some grid point exceeds `p`, then `p⁺` is a grid point and `p < p⁺`. -/
lemma elemClipNext_mem {P : Finset ℝ≥0} {p q : ℝ≥0} (hq : q ∈ P) (hpq : p < q) :
    elemClipNext P p ∈ P ∧ p < elemClipNext P p := by
  have hne : (P.filter (p < ·)).Nonempty := ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩
  simp only [elemClipNext, hne, ↓reduceDIte]
  exact Finset.mem_filter.1 ((P.filter (p < ·)).min'_mem hne)

/-! ### The clipping factor -/

/-- The factor `min(1, √K / |x|)` of the radial projection of `x` (supported by `F`) onto the
ball of radius `√K`. -/
def elemClipFac (F : Finset ι) (K : ℝ) (x : ι → ℝ) : ℝ :=
  min 1 (Real.sqrt K / Real.sqrt (∑ i ∈ F, x i ^ 2))

/-- The clipping factor is nonnegative. -/
lemma elemClipFac_nonneg (F : Finset ι) (K : ℝ) (x : ι → ℝ) : 0 ≤ elemClipFac F K x :=
  le_min zero_le_one (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The clipping factor is at most `1`. -/
lemma elemClipFac_le_one (F : Finset ι) (K : ℝ) (x : ι → ℝ) : elemClipFac F K x ≤ 1 :=
  min_le_left _ _

/-- `|π_K(x)|² = c² |x|² ≤ K`. -/
lemma elemClipFac_sq_mul_le (F : Finset ι) {K : ℝ} (hK : 0 ≤ K) (x : ι → ℝ) :
    elemClipFac F K x ^ 2 * ∑ i ∈ F, x i ^ 2 ≤ K := by
  set A := ∑ i ∈ F, x i ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hA.eq_or_lt with hA0 | hA0
  · rw [← hA0, mul_zero]; exact hK
  have hc : elemClipFac F K x ≤ Real.sqrt K / Real.sqrt A := min_le_right _ _
  have hc0 := elemClipFac_nonneg F K x
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
  calc elemClipFac F K x ^ 2 * A ≤ (Real.sqrt K / Real.sqrt A) ^ 2 * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hc 2) hA
    _ = K := by
      rw [div_pow, Real.sq_sqrt hK, Real.sq_sqrt hA]; field_simp

/-- **The radial projection is `1`-Lipschitz towards the ball** (finite-dimensional form):
if `∑_{i ∈ F} yᵢ² ≤ K`, then `∑_{i ∈ F} (c xᵢ - yᵢ)² ≤ ∑_{i ∈ F} (xᵢ - yᵢ)²`. -/
lemma elemClipFac_sum_sq_le (F : Finset ι) {K : ℝ} (hK : 0 ≤ K) (x y : ι → ℝ)
    (hy : ∑ i ∈ F, y i ^ 2 ≤ K) :
    ∑ i ∈ F, (x i * elemClipFac F K x - y i) ^ 2 ≤ ∑ i ∈ F, (x i - y i) ^ 2 := by
  set c := elemClipFac F K x
  set A := ∑ i ∈ F, x i ^ 2
  set C := ∑ i ∈ F, x i * y i
  set Bm := ∑ i ∈ F, y i ^ 2
  have hdiff : ∑ i ∈ F, (x i * c - y i) ^ 2 - ∑ i ∈ F, (x i - y i) ^ 2 =
      (c ^ 2 - 1) * A - 2 * (c - 1) * C := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ Bm := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc0 : 0 ≤ c := elemClipFac_nonneg F K x
  have hc1 : c ≤ 1 := elemClipFac_le_one F K x
  set n := Real.sqrt A
  set k := Real.sqrt K
  have hn : n ^ 2 = A := Real.sq_sqrt hA
  have hk : k ^ 2 = K := Real.sq_sqrt hK
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  -- Cauchy–Schwarz: `C ≤ n m` with `m = √Bm ≤ k`
  have hCS : C ≤ n * k := by
    have h1 : C ^ 2 ≤ A * Bm := Finset.sum_mul_sq_le_sq_mul_sq F x y
    have h2 : C ≤ Real.sqrt (A * Bm) := Real.le_sqrt_of_sq_le h1
    rw [Real.sqrt_mul hA] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy) hn0)
  by_cases hnk : n ≤ k
  · -- `c = 1` (or `x = 0` on `F`)
    rcases hn0.eq_or_lt with hn' | hn'
    · have hA0 : A = 0 := by rw [← hn, ← hn']; ring
      have hx0 : ∀ i ∈ F, x i = 0 := fun i hi =>
        pow_eq_zero_iff (n := 2) two_ne_zero |>.1
          ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).1 hA0 i hi)
      exact le_of_eq (Finset.sum_congr rfl fun i hi => by rw [hx0 i hi]; ring)
    · have hc : c = 1 := by
        apply min_eq_left
        rw [le_div_iff₀ hn']; linarith
      rw [hc]; simp
  · push Not at hnk
    have hnpos : 0 < n := hk0.trans_lt hnk
    have hc : c = k / n := by
      apply min_eq_right
      rw [div_le_iff₀ hnpos]; linarith
    have hcn : c * n = k := by rw [hc]; field_simp
    have key : 0 ≤ (1 - c ^ 2) * A - 2 * (1 - c) * C := by
      have e1 : (1 - c ^ 2) * A = n ^ 2 - k ^ 2 := by
        rw [← hn, show k = c * n from hcn.symm]; ring
      have e2 : 2 * (1 - c) * (n * k) = 2 * n * k - 2 * k ^ 2 := by
        rw [show k = c * n from hcn.symm]; ring
      have h3 : 2 * (1 - c) * C ≤ 2 * (1 - c) * (n * k) :=
        mul_le_mul_of_nonneg_left hCS (by linarith)
      nlinarith [sq_nonneg (n - k)]
    linarith

/-! ### The clipped elementary integrand -/

/-- The grid: the endpoints of the blocks of `e`, and `u`, `v`. -/
def elemClipPts (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) : Finset ℝ≥0 :=
  elemGridPts e ∪ {u, v}

/-- No endpoint of `e` lies strictly between `p` and its successor in the grid. -/
lemma elemClip_noPt (e : ElemIntegrand 𝓖 ι) (u v p : ℝ≥0) :
    ∀ q ∈ elemGridPts e, q ≤ p ∨ elemClipNext (elemClipPts e u v) p ≤ q := by
  intro q hq
  rcases le_or_gt q p with h | h
  · exact Or.inl h
  · exact Or.inr (elemClipNext_le (Finset.mem_union_left _ hq) h)

/-- The coefficient of the clipped integrand on the cell `(p, p⁺]` for the index `i`. -/
def elemClipCoef (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) (p : ℝ≥0) (i : ι) (ω : Ω) :
    ℝ :=
  if u ≤ p ∧ elemClipNext (elemClipPts e u v) p ≤ v then
    e.toFun i (elemClipNext (elemClipPts e u v) p) ω *
      elemClipFac (elemGridIdx e) K (fun j => e.toFun j (elemClipNext (elemClipPts e u v) p) ω)
  else e.toFun i (elemClipNext (elemClipPts e u v) p) ω

/-- The clipped coefficient on `(p, p⁺]` is `𝓖_p`-measurable. -/
lemma measurable_elemClipCoef (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) (p : ℝ≥0)
    (i : ι) : Measurable[𝓖 p] (elemClipCoef e u v K p i) := by
  have hm := elemGrid_measurable_toFun (elemClip_noPt e u v p)
  unfold elemClipCoef elemClipFac
  split_ifs
  · refine (hm i).mul (measurable_const.min (measurable_const.div ?_))
    exact (Finset.measurable_sum _ fun j _ => (hm j).pow_const 2).sqrt
  · exact hm i

/-- The clipped coefficient is bounded. -/
lemma elemClipCoef_bdd (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) (p : ℝ≥0) (i : ι) :
    ∃ C, ∀ ω, |elemClipCoef e u v K p i ω| ≤ C := by
  obtain ⟨C, hC⟩ := elemGrid_toFun_bdd e
  refine ⟨C, fun ω => ?_⟩
  unfold elemClipCoef
  split_ifs
  · rw [abs_mul]
    calc _ ≤ |e.toFun i (elemClipNext (elemClipPts e u v) p) ω| * 1 :=
          mul_le_mul_of_nonneg_left (by
            rw [abs_of_nonneg (elemClipFac_nonneg _ _ _)]; exact elemClipFac_le_one _ _ _)
            (abs_nonneg _)
      _ ≤ C := by rw [mul_one]; exact hC _ _ _
  · exact hC _ _ _

/-- The block of the clipped integrand on the cell `(p, p⁺]` for the index `i`. -/
def elemClipBlock (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) (p : ℝ≥0) (i : ι) :
    ElemBlock 𝓖 ι where
  a := p
  b := elemClipNext (elemClipPts e u v) p
  le := le_elemClipNext _ p
  i := i
  ξ := elemClipCoef e u v K p i
  meas := measurable_elemClipCoef e u v K p i
  bdd := elemClipCoef_bdd e u v K p i

/-- **The clipped elementary integrand**: `e` outside `(u, v]`, its radial projection onto the
ball of radius `√K` on `(u, v]`. -/
def elemClip (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) : ElemIntegrand 𝓖 ι :=
  (elemClipPts e u v).toList.flatMap fun p =>
    (elemGridIdx e).toList.map fun i => elemClipBlock e u v K p i

/-- `toFun` of a concatenation of lists of blocks. -/
private lemma toFun_flatMap {α : Type*} (l : List α) (f : α → ElemIntegrand 𝓖 ι) (j : ι)
    (r : ℝ) (ω : Ω) : ElemIntegrand.toFun (l.flatMap f) j r ω =
      (l.map fun p => ElemIntegrand.toFun (f p) j r ω).sum := by
  induction l with
  | nil => simp [ElemIntegrand.toFun_nil]
  | cons p l ih => simp [List.flatMap_cons, ElemIntegrand.toFun_append, ih]

open Classical in
/-- The clipped integrand as a double sum over cells and indices. -/
private lemma elemClip_toFun_sum (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) (j : ι) (r : ℝ)
    (ω : Ω) : (elemClip e u v K).toFun j r ω =
      ∑ p ∈ elemClipPts e u v, ∑ i ∈ elemGridIdx e,
        (if i = j ∧ (p : ℝ) < r ∧ r ≤ elemClipNext (elemClipPts e u v) p then
          elemClipCoef e u v K p i ω else 0) := by
  rw [elemClip, toFun_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ElemIntegrand.toFun, List.map_map, Finset.sum_map_toList]
  rfl

/-- **Values of the clipped integrand.** For `r ∈ (u, v]` it is the radial projection
`eᵢ(r) min(1, √K / |e(r)|)`; outside, it is `eᵢ(r)`. -/
lemma elemClip_toFun (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) (K : ℝ) (j : ι) (r : ℝ) (ω : Ω) :
    (elemClip e u v K).toFun j r ω =
      if (u : ℝ) < r ∧ r ≤ v then
        e.toFun j r ω * elemClipFac (elemGridIdx e) K (fun i => e.toFun i r ω)
      else e.toFun j r ω := by
  classical
  set P := elemClipPts e u v with hP
  set F := elemGridIdx e
  have huP : u ∈ P := Finset.mem_union_right _ (by simp)
  have hvP : v ∈ P := Finset.mem_union_right _ (by simp)
  have hgP : elemGridPts e ⊆ P := Finset.subset_union_left
  rw [elemClip_toFun_sum]
  by_cases hcell : ∃ p ∈ P, (p : ℝ) < r ∧ r ≤ elemClipNext P p
  · obtain ⟨p, hpP, hpr, hrq⟩ := hcell
    -- the cell containing `r` is unique
    have huniq : ∀ p' ∈ P, (p' : ℝ) < r ∧ r ≤ elemClipNext P p' → p' = p := by
      intro p' hp'P ⟨hp'r, hrq'⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := NNReal.coe_le_coe.2 (elemClipNext_le hpP h); linarith
      · have := NNReal.coe_le_coe.2 (elemClipNext_le hp'P h); linarith
    rw [Finset.sum_eq_single p (fun p' hp' hne => Finset.sum_eq_zero fun i _ => by
      rw [ite_eq_right]; rintro ⟨_, h⟩; exact hne (huniq p' hp' h)) (fun h => absurd hpP h)]
    have hq : ∀ i, e.toFun i r ω = e.toFun i (elemClipNext P p) ω := fun i =>
      elemGrid_toFun_eq (elemClip_noPt e u v p) i hpr hrq ω
    -- the condition `u < r ≤ v` is the condition `u ≤ p ∧ p⁺ ≤ v`
    have hcond : ((u : ℝ) < r ∧ r ≤ v) ↔ (u ≤ p ∧ elemClipNext P p ≤ v) := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · by_contra h; push Not at h
          have := NNReal.coe_le_coe.2 (elemClipNext_le huP h); linarith
        · by_contra h; push Not at h
          have hpv : p < v := by
            by_contra h'; push Not at h'
            have : (v : ℝ) ≤ p := NNReal.coe_le_coe.2 h'; linarith
          have := elemClipNext_le hvP hpv; exact absurd this (not_le.2 h)
      · rintro ⟨h1, h2⟩
        exact ⟨(NNReal.coe_le_coe.2 h1).trans_lt hpr, hrq.trans (NNReal.coe_le_coe.2 h2)⟩
    by_cases hjF : j ∈ F
    · rw [Finset.sum_eq_single j (fun i _ hij => by rw [ite_eq_right]; rintro ⟨h, _⟩; exact hij h)
        (fun h => absurd hjF h), ite_eq_left ⟨rfl, hpr, hrq⟩]
      simp only [elemClipCoef, ← hP, hq]
      by_cases hc : u ≤ p ∧ elemClipNext P p ≤ v
      · rw [ite_eq_left hc, ite_eq_left (hcond.2 hc)]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hcond.1 h))]
    · rw [Finset.sum_eq_zero fun i hi => by
        rw [ite_eq_right]; rintro ⟨rfl, _⟩; exact hjF hi]
      rw [elemGrid_toFun_eq_zero e hjF]; simp
  · push Not at hcell
    rw [Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun i _ => by
      rw [ite_eq_right]; rintro ⟨_, h1, h2⟩; exact absurd h2 (not_le.2 (hcell p hp h1))]
    -- `r` lies outside `(min P, max P]`
    have hout : (∀ q ∈ P, r ≤ (q : ℝ)) ∨ (∀ q ∈ P, (q : ℝ) < r) := by
      by_contra h
      push Not at h
      obtain ⟨⟨q1, hq1, hq1r⟩, ⟨q2, hq2, hq2r⟩⟩ := h
      set L := P.filter (fun q : ℝ≥0 => (q : ℝ) < r)
      have hL : L.Nonempty := ⟨q1, Finset.mem_filter.2 ⟨hq1, hq1r⟩⟩
      set p := L.max' hL
      have hpL := Finset.mem_filter.1 (L.max'_mem hL)
      have hpq2 : p < q2 := by
        have : (p : ℝ) < q2 := hpL.2.trans_le hq2r
        exact_mod_cast this
      obtain ⟨hnP, hpn⟩ := elemClipNext_mem hq2 hpq2
      have hrn : r ≤ elemClipNext P p := by
        by_contra h'
        push Not at h'
        have := L.le_max' _ (Finset.mem_filter.2 ⟨hnP, h'⟩)
        exact absurd this (not_le.2 hpn)
      exact absurd hrn (not_le.2 (hcell p hpL.1 hpL.2))
    have he0 : e.toFun j r ω = 0 := elemGrid_toFun_eq_zero_of_out e j
      (hout.imp (fun h q hq => h q (hgP hq)) (fun h q hq => h q (hgP hq))) ω
    have hc : ¬ ((u : ℝ) < r ∧ r ≤ v) := by
      rintro ⟨h1, h2⟩
      rcases hout with h | h
      · linarith [h u huP]
      · linarith [h v hvP]
    rw [ite_eq_right hc, he0]

/-- The clipped integrand satisfies `∑ᵢ ēᵢ(r)² ≤ K` on `(u, v]`. -/
lemma elemClip_sq_le (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) {r : ℝ}
    (hur : (u : ℝ) < r) (hrv : r ≤ v) (ω : Ω) :
    ∑' i, (elemClip e u v K).toFun i r ω ^ 2 ≤ K := by
  simp only [elemClip_toFun, hur, hrv, and_self, ite_true]
  rw [tsum_eq_sum (s := elemGridIdx e) (fun i hi => by rw [elemGrid_toFun_eq_zero e hi]; ring)]
  calc ∑ i ∈ elemGridIdx e, (e.toFun i r ω * elemClipFac (elemGridIdx e) K
        (fun i => e.toFun i r ω)) ^ 2 =
      elemClipFac (elemGridIdx e) K (fun i => e.toFun i r ω) ^ 2 *
        ∑ i ∈ elemGridIdx e, e.toFun i r ω ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ K := elemClipFac_sq_mul_le _ hK _

/-- **The clipping does not increase the distance to points of the ball.** For `r ∈ (u, v]`
and `y` with `∑ᵢ yᵢ² ≤ K` whenever the series converges,
`∑ᵢ ‖ēᵢ(r) - yᵢ‖² ≤ ∑ᵢ ‖eᵢ(r) - yᵢ‖²` in `[0, ∞]` (both sides are `∞` if `∑ᵢ yᵢ² = ∞`). -/
lemma elemClip_dist_le (e : ElemIntegrand 𝓖 ι) (u v : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) {r : ℝ}
    (hur : (u : ℝ) < r) (hrv : r ≤ v) (ω : Ω) (y : ι → ℝ)
    (hy : Summable (fun i => y i ^ 2) → ∑' i, y i ^ 2 ≤ K) :
    ∑' i, ‖(elemClip e u v K).toFun i r ω - y i‖ₑ ^ 2 ≤
      ∑' i, ‖e.toFun i r ω - y i‖ₑ ^ 2 := by
  simp only [elemClip_toFun, hur, hrv, and_self, ite_true]
  set F := elemGridIdx e
  have hx0 : ∀ i ∉ F, e.toFun i r ω = 0 := fun i hi => elemGrid_toFun_eq_zero e hi r ω
  have hen : ∀ z : ℝ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (z ^ 2) := fun z => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [← ENNReal.sum_add_tsum_compl F, ← ENNReal.sum_add_tsum_compl F
    (fun i => ‖e.toFun i r ω - y i‖ₑ ^ 2)]
  have hcompl : ∀ i : ↥(F : Set ι)ᶜ,
      ‖e.toFun i r ω * elemClipFac F K (fun i => e.toFun i r ω) - y i‖ₑ ^ 2 =
        ‖e.toFun i r ω - y i‖ₑ ^ 2 := fun i => by
    rw [hx0 i i.2]; simp
  rw [tsum_congr hcompl]
  by_cases hs : Summable (fun i => y i ^ 2)
  · refine add_le_add_left ?_ _
    have hyF : ∑ i ∈ F, y i ^ 2 ≤ K :=
      (hs.sum_le_tsum F fun i _ => sq_nonneg _).trans (hy hs)
    simp only [hen]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (elemClipFac_sum_sq_le F hK (fun i => e.toFun i r ω) y hyF)
  · -- the right-hand side is infinite
    have htop : ∑' i : ↥(F : Set ι)ᶜ, ‖e.toFun i r ω - y i‖ₑ ^ 2 = ∞ := by
      by_contra hne
      apply hs
      have hcomp : ∑' i : ↥(F : Set ι)ᶜ, ‖y i‖ₑ ^ 2 ≠ ∞ := by
        convert hne using 3 with i; rw [hx0 i i.2]; simp
      have hall : ∑' i, ‖y i‖ₑ ^ 2 ≠ ∞ := by
        rw [← ENNReal.sum_add_tsum_compl F]
        exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun i _ => by simp, hcomp⟩
      have hnn : ∀ i, ‖y i‖ₑ ^ 2 = ((‖y i‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := fun i => by
        rw [ENNReal.coe_pow, enorm_eq_nnnorm]
      simp only [hnn] at hall
      have h1 := ENNReal.tsum_coe_ne_top_iff_summable.1 hall
      have h2 := NNReal.summable_coe.2 h1
      convert h2 using 2 with i
      simp [Real.norm_eq_abs, sq_abs]
    rw [htop]; simp

end QSSEPtoKPZ
