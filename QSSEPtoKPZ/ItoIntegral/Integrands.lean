/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Basic
public import QSSEPtoKPZ.ItoIntegral.Grid

/-!
# Integrands that occur (package C, task C4)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces, proved by
task C4. See `docs/stage2-design.md`, Section 2.2 ("Integrands that occur"), and
`docs/stage2-interfaces.md`.

No density theorem for general progressive integrands is proved. Membership in the closure
`IsItoIntegrable` is proved for the shapes that occur:

* `IsItoIntegrable.of_tendsto`: the closure is closed under limits for the energy;
* `isItoIntegrable_of_leftContinuous`: bounded (in `ℓ²(ι)`), componentwise left-continuous,
  adapted families;
* `IsItoIntegrable.indicator_stoppingTime`: `h 𝟙_{s ≤ τ}` for a stopping time `τ`;
* `IsItoIntegrable.mul_leftContinuous`: products with a bounded left-continuous adapted scalar
  process;
* `IsItoIntegrable.mul_indicator_gt`: `ξ 𝟙_{s > u} h` for `ξ` bounded `𝓖_u`-measurable;
* `IsItoIntegrable.indicator_index`: restriction to a set of indices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]

set_option linter.unusedSectionVars false in
/-- **Closedness.** If each `h_k` is Itô-integrable, `g` is jointly measurable on `(0, ∞) × Ω`,
and `h_k → g` for the energy on every `[0, T]`, then `g` is Itô-integrable. -/
theorem IsItoIntegrable.of_tendsto {h : ℕ → ι → ℝ → Ω → ℝ} {g : ι → ℝ → Ω → ℝ}
    (hh : ∀ k, IsItoIntegrable 𝓖 μ (h k))
    (hg : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then g i p.1 p.2 else 0)
    (hlim : ∀ T : ℝ,
      Tendsto (fun k => energy μ (fun i s ω => h k i s ω - g i s ω) T) atTop (𝓝 0)) :
    IsItoIntegrable 𝓖 μ g := by
  have hE : ∀ k : ℕ, ∃ e : ElemIntegrand 𝓖 ι,
      energy μ (fun i s ω => e.toFun i s ω - h k i s ω) k ≤ ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro k
    obtain ⟨e, he⟩ := (hh k).approx
    have hpos : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    obtain ⟨n, hn⟩ := ((he k).eventually (ge_mem_nhds hpos)).exists
    exact ⟨e n, hn⟩
  choose e he using hE
  refine ⟨hg, e, fun T => ?_⟩
  have hdiff : ∀ k i, Measurable fun p : ℝ × Ω =>
      if 0 < p.1 then h k i p.1 p.2 - g i p.1 p.2 else 0 := by
    intro k i
    have : (fun p : ℝ × Ω => if 0 < p.1 then h k i p.1 p.2 - g i p.1 p.2 else 0) =
        fun p => (if 0 < p.1 then h k i p.1 p.2 else 0) - (if 0 < p.1 then g i p.1 p.2 else 0) := by
      funext p
      split_ifs <;> simp
    rw [this]
    exact ((hh k).meas i).sub (hg i)
  have hb : ∀ᶠ k : ℕ in atTop, energy μ (fun i s ω => (e k).toFun i s ω - g i s ω) T ≤
      2 * energy μ (fun i s ω => h k i s ω - g i s ω) T + 2 * ((k : ℝ≥0∞) + 1)⁻¹ := by
    filter_upwards [eventually_ge_atTop ⌈T⌉₊] with k hk
    have hTk : T ≤ k := (Nat.le_ceil T).trans (by exact_mod_cast hk)
    have heq : (fun i s ω => (e k).toFun i s ω - g i s ω) =
        fun i s ω => (h k i s ω - g i s ω) + ((e k).toFun i s ω - h k i s ω) := by
      funext i s ω
      ring
    rw [heq]
    refine (itoEnergy_add_le (hdiff k) T).trans ?_
    gcongr
    exact (itoEnergy_mono_horizon μ _ hTk).trans (he k)
  have hinv : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have hup : Tendsto (fun k : ℕ => 2 * energy μ (fun i s ω => h k i s ω - g i s ω) T +
      2 * ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := 2) (hlim T) (Or.inr (by norm_num))
    have h2 := ENNReal.Tendsto.const_mul (a := 2) hinv (Or.inr (by norm_num))
    simpa using h1.add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) hb

/-- The clipping `x ↦ max (-C) (min C x)` onto `[-C, C]`. -/
private def clip (C x : ℝ) : ℝ := max (-C) (min C x)

private lemma continuous_clip (C : ℝ) : Continuous (clip C) :=
  continuous_const.max (continuous_const.min continuous_id)

private lemma abs_clip_le (C x : ℝ) : |clip C x| ≤ |C| := by
  unfold clip
  rw [abs_le]
  constructor
  · exact (neg_le_neg (le_abs_self C)).trans (le_max_left _ _)
  · exact max_le (neg_le_abs C) ((min_le_left _ _).trans (le_abs_self C))

private lemma clip_eq {C x : ℝ} (hx : |x| ≤ C) : clip C x = x := by
  unfold clip
  rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Dyadic-type mesh `1/(n+1)` of the approximating grids. -/
private def dyδ (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹

/-- Number of cells `(n+1)²` of the approximating grids (horizon `n + 1`). -/
private def dyN (n : ℕ) : ℕ := (n + 1) * (n + 1)

/-- The left-point step approximations of a bounded left-continuous process converge to it at
every `s > 0`. -/
private lemma dy_tendsto {f : ℝ → Ω → ℝ} {C : ℝ} (hbd : ∀ ω (s : ℝ), 0 < s → |f s ω| ≤ C)
    (hlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s)
    {ω : Ω} {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => itoGridStep (fun k ω => clip C (f (k * (dyδ n : ℝ)) ω)) (dyδ n) (dyN n)
      s ω) atTop (𝓝 (f s ω)) := by
  have hδ : ∀ n, (dyδ n : ℝ) = 1 / ((n : ℝ) + 1) := fun n => by simp [dyδ]
  have := tendsto_itoGridStep (f := f) (φ := clip C) (δ := fun n => (dyδ n : ℝ)) (N := dyN)
    (continuous_clip C) hs (Eventually.of_forall fun n => by rw [hδ]; positivity)
    (by simpa only [hδ] using tendsto_one_div_add_atTop_nhds_zero_nat) ?_ (hlc ω s hs)
  · rwa [clip_eq (hbd ω s hs)] at this
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop s)] with n hn
    rw [hδ]
    have : ((dyN n : ℕ) : ℝ) * (1 / ((n : ℝ) + 1)) = n + 1 := by
      simp only [dyN]
      push_cast
      field_simp
    rw [this]
    linarith

/-- **Joint measurability from adaptedness and left-continuity.** A process bounded on
`(0, ∞)`, adapted to `𝓖` and left-continuous at every `s > 0` is jointly measurable on
`(0, ∞) × Ω` (it is the pointwise limit of its left-point step approximations). -/
theorem measurable_pos_of_leftContinuous {f : ℝ → Ω → ℝ} {C : ℝ}
    (hbd : ∀ ω (s : ℝ), 0 < s → |f s ω| ≤ C) (hfa : ∀ t : ℝ≥0, Measurable[𝓖 t] (f t))
    (hlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s) :
    Measurable fun p : ℝ × Ω => if 0 < p.1 then f p.1 p.2 else 0 := by
  refine measurable_of_tendsto_metrizable (f := fun n (p : ℝ × Ω) =>
    itoGridStep (fun k ω => clip C (f (k * (dyδ n : ℝ)) ω)) (dyδ n) (dyN n) p.1 p.2)
    (fun n => measurable_itoGridStep (fun k => ((continuous_clip C).measurable.comp
      (itoGrid_measurable_point hfa (dyδ n) k)).mono (𝓖.le _) le_rfl) _ _) ?_
  rw [tendsto_pi_nhds]
  rintro ⟨s, ω⟩
  by_cases hs : 0 < s
  · simpa [hs] using dy_tendsto hbd hlc hs
  · simp only [hs, ite_false]
    exact tendsto_const_nhds.congr fun n => (itoGridStep_eq_zero (fun h => hs h.2) ω).symm

/-- **One index.** A real process `f`, bounded on `(0, ∞)`, adapted, with left-continuous paths
at every `s > 0`, placed on the index `i`, is Itô-integrable (left-point step approximations on
the grids `k/(n+1)`, `k < (n+1)²`). -/
theorem isItoIntegrable_single_of_leftContinuous [DecidableEq ι] (i : ι) {f : ℝ → Ω → ℝ}
    {C : ℝ} (hbd : ∀ ω (s : ℝ), 0 < s → |f s ω| ≤ C) (hfa : ∀ t : ℝ≥0, Measurable[𝓖 t] (f t))
    (hlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s) :
    IsItoIntegrable 𝓖 μ (fun j s ω => if j = i then f s ω else 0) := by
  have hfm := measurable_pos_of_leftContinuous hbd hfa hlc
  have hξ : ∀ n (k : ℕ), Measurable[𝓖 ((k : ℝ≥0) * dyδ n)]
      (fun ω => clip C (f (k * (dyδ n : ℝ)) ω)) := fun n k =>
    (continuous_clip C).measurable.comp (itoGrid_measurable_point hfa (dyδ n) k)
  refine ⟨fun j => ?_, fun n => itoGridElem i (dyδ n) (dyN n)
    (fun k ω => clip C (f (k * (dyδ n : ℝ)) ω)) (hξ n) |C| (fun k ω => abs_clip_le _ _),
    fun T => ?_⟩
  · by_cases hji : j = i
    · subst hji
      simpa using hfm
    · simp [hji]
  · exact tendsto_energy_itoGridElem_sub i hbd hfm _ _ _ hξ _ _
      (fun ω s hs _ => dy_tendsto hbd hlc hs)

/-- **Bounded left-continuous adapted families.** If, for all `s > 0` and all `ω`,
`∑ᵢ hᵢ(s, ω)² ≤ K` (the series converging), each `hᵢ` is adapted to `𝓖`, and each path
`s ↦ hᵢ(s, ω)` is left-continuous at every `s > 0`, then `h` is Itô-integrable. (Proof:
left-point dyadic step approximations for finitely many indices, then dominated convergence for
the truncation of `ι`, and `IsItoIntegrable.of_tendsto`.) -/
theorem isItoIntegrable_of_leftContinuous {h : ι → ℝ → Ω → ℝ} {K : ℝ}
    (hbd : ∀ ω (s : ℝ), 0 < s → Summable (fun i => h i s ω ^ 2) ∧ ∑' i, h i s ω ^ 2 ≤ K)
    (hadapt : ∀ i (t : ℝ≥0), Measurable[𝓖 t] (h i t))
    (hlc : ∀ i ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => h i r ω) (Set.Iic s) s) :
    IsItoIntegrable 𝓖 μ h := by
  classical
  have hsq : ∀ i ω (s : ℝ), 0 < s → |h i s ω| ≤ √K := fun i ω s hs =>
    Real.abs_le_sqrt (((hbd ω s hs).1.le_tsum i fun j _ => sq_nonneg _).trans (hbd ω s hs).2)
  have hG : ∀ i, IsItoIntegrable 𝓖 μ (fun j s ω => if j = i then h i s ω else 0) := fun i =>
    isItoIntegrable_single_of_leftContinuous i (hsq i) (hadapt i) (hlc i)
  have hm : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h i p.1 p.2 else 0 := fun i =>
    measurable_pos_of_leftContinuous (hsq i) (hadapt i) (hlc i)
  -- truncation to the finite sets `F n = {i | encode i < n}`
  let _ := Encodable.ofCountable ι
  let F : ℕ → Finset ι := fun n =>
    (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn
  have hF : ∀ n i, i ∈ F n ↔ Encodable.encode i < n := fun n i => by simp [F]
  have hFi : ∀ n, IsItoIntegrable 𝓖 μ (fun j s ω => if j ∈ F n then h j s ω else 0) := by
    intro n
    have e : (fun j s ω => if j ∈ F n then h j s ω else 0) =
        fun j s ω => ∑ k ∈ F n, (fun j s ω => if j = k then h k s ω else 0) j s ω := by
      funext j s ω
      rw [Finset.sum_ite_eq]
    rw [e]
    exact IsItoIntegrable.finset_sum (F n) fun k _ => hG k
  have hFmono : Monotone F := fun n n' hnn' i hi => (hF n' i).2 (((hF n i).1 hi).trans_le hnn')
  have hFcov : ∀ i, ∃ n, i ∈ F n := fun i => ⟨Encodable.encode i + 1, (hF _ i).2 (by omega)⟩
  refine IsItoIntegrable.of_tendsto hFi hm fun T => ?_
  refine itoEnergy_tendsto_zero_of_dominated (C := ENNReal.ofReal K) ENNReal.ofReal_ne_top
    ?_ ?_ ?_
  · intro n j
    by_cases hj : j ∈ F n
    · simp [hj]
    · have : (fun p : ℝ × Ω => if 0 < p.1 then
            (if j ∈ F n then h j p.1 p.2 else 0) - h j p.1 p.2 else 0) =
          fun p => -(if 0 < p.1 then h j p.1 p.2 else 0) := by
        funext p
        split_ifs <;> simp
      rw [this]
      exact (hm j).neg
  · intro n ω s hs _
    calc ∑' j, ‖(if j ∈ F n then h j s ω else 0) - h j s ω‖ₑ ^ 2
        ≤ ∑' j, ‖h j s ω‖ₑ ^ 2 := ENNReal.tsum_le_tsum fun j => by
          by_cases hj : j ∈ F n <;> simp [hj]
      _ = ENNReal.ofReal (∑' j, h j s ω ^ 2) := itoEnergy_tsum_enorm_sq (hbd ω s hs).1
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hbd ω s hs).2
  · intro ω s hs _
    have hne : ∑' j, ‖h j s ω‖ₑ ^ 2 ≠ ∞ := by
      rw [itoEnergy_tsum_enorm_sq (hbd ω s hs).1]
      exact ENNReal.ofReal_ne_top
    have htail := (ENNReal.tendsto_tsum_compl_atTop_zero hne).comp
      (tendsto_atTop_finset_of_monotone hFmono hFcov)
    refine htail.congr fun n => ?_
    simp only [Function.comp_apply]
    refine (tsum_subtype ((F n : Set ι)ᶜ) (fun j => ‖h j s ω‖ₑ ^ 2)).trans
      (tsum_congr fun j => ?_)
    by_cases hj : j ∈ F n <;> simp [hj]

/-- `∑_{a ∈ l} G_a` is Itô-integrable if each `G_a` is. -/
private lemma isItoIntegrable_list_sum {α : Type*} (l : List α) (G : α → ι → ℝ → Ω → ℝ)
    (hG : ∀ a ∈ l, IsItoIntegrable 𝓖 μ (G a)) :
    IsItoIntegrable 𝓖 μ (fun j s ω => (l.map fun a => G a j s ω).sum) := by
  induction l with
  | nil => exact isItoIntegrable_zero
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hG a List.mem_cons_self).add (ih fun b hb => hG b (List.mem_cons_of_mem a hb))

/-- A real function of time that is eventually equal to its value at `s` on the left of `s` is
left-continuous at `s`. -/
private lemma lc_of_eventually {g : ℝ → ℝ} {s : ℝ} (h : ∀ᶠ r in 𝓝[≤] s, g r = g s) :
    ContinuousWithinAt g (Set.Iic s) s :=
  tendsto_const_nhds.congr' (h.mono fun _ hr => hr.symm)

/-- `r ↦ c 𝟙_{(a, b]}(r)` is left-continuous. -/
private lemma lc_ite_Ioc (a b c s : ℝ) :
    ContinuousWithinAt (fun r => if a < r ∧ r ≤ b then c else 0) (Set.Iic s) s := by
  apply lc_of_eventually
  rcases le_or_gt s a with h1 | h1
  · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≤ s)
    have h2 : ¬ a < r := fun h => by linarith
    have h3 : ¬ a < s := fun h => by linarith
    simp [h2, h3]
  · rcases le_or_gt s b with h2 | h2
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds h1).filter_mono nhdsWithin_le_nhds] with r (hr : r ≤ s) har
      simp [har, h1, h2, hr.trans h2]
    · filter_upwards [(eventually_gt_nhds h2).filter_mono nhdsWithin_le_nhds] with r hbr
      simp [not_le.2 hbr, not_le.2 h2]

/-- Products with a bounded left-continuous adapted process (proof of
`IsItoIntegrable.mul_leftContinuous`): `Z e_k` is a finite sum of bounded left-continuous adapted
families on single indices, and `energy (Z e_k - Z h) ≤ K² energy (e_k - h)`. -/
private lemma mul_leftContinuous_aux {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    {Z : ℝ → Ω → ℝ} {K : ℝ} (hZ : ∀ ω (s : ℝ), 0 < s → |Z s ω| ≤ K)
    (hZa : ∀ t : ℝ≥0, Measurable[𝓖 t] (Z t))
    (hZlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => Z r ω) (Set.Iic s) s) :
    IsItoIntegrable 𝓖 μ (fun i s ω => Z s ω * h i s ω) := by
  classical
  obtain ⟨E, hE⟩ := hh.approx
  have hZm := measurable_pos_of_leftContinuous hZ hZa hZlc
  have hZE : ∀ k, IsItoIntegrable 𝓖 μ (fun i s ω => Z s ω * (E k).toFun i s ω) := by
    intro k
    have e : (fun i s ω => Z s ω * (E k).toFun i s ω) = fun i s ω =>
        ((E k).map fun bl => (fun j s ω => if j = bl.i then
          Z s ω * (if (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0) else 0) i s ω).sum := by
      funext i s ω
      unfold ElemIntegrand.toFun
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun bl _ => ?_
      by_cases h1 : bl.i = i <;> by_cases h2 : (bl.a : ℝ) < s ∧ s ≤ bl.b <;>
        simp [h1, h2, Ne.symm]
    rw [e]
    refine isItoIntegrable_list_sum _ _ fun bl _ => ?_
    obtain ⟨Cb, hCb⟩ := bl.bdd
    refine isItoIntegrable_single_of_leftContinuous (C := |K| * |Cb|) bl.i ?_ ?_ ?_
    · intro ω s hs
      rw [abs_mul]
      refine mul_le_mul ((hZ ω s hs).trans (le_abs_self K)) ?_ (abs_nonneg _) (abs_nonneg _)
      split_ifs
      · exact (hCb ω).trans (le_abs_self _)
      · simp
    · intro t
      refine (hZa t).mul ?_
      by_cases hc : (bl.a : ℝ) < t ∧ (t : ℝ) ≤ bl.b
      · simp only [hc, and_self, ↓reduceIte]
        exact bl.meas.mono (𝓖.mono (NNReal.coe_lt_coe.1 hc.1).le) le_rfl
      · simp only [hc, ↓reduceIte]
        exact measurable_const
    · intro ω s hs
      exact (hZlc ω s hs).mul (lc_ite_Ioc _ _ _ _)
  refine IsItoIntegrable.of_tendsto hZE (fun i => ?_) fun T => ?_
  · have : (fun p : ℝ × Ω => if 0 < p.1 then Z p.1 p.2 * h i p.1 p.2 else 0) =
        fun p => (if 0 < p.1 then Z p.1 p.2 else 0) * (if 0 < p.1 then h i p.1 p.2 else 0) := by
      funext p
      split_ifs <;> simp
    rw [this]
    exact hZm.mul (hh.meas i)
  · have hle : ∀ k, energy μ (fun i s ω => Z s ω * (E k).toFun i s ω - Z s ω * h i s ω) T ≤
        ENNReal.ofReal (K ^ 2) * energy μ (fun i s ω => (E k).toFun i s ω - h i s ω) T :=
      fun k => itoEnergy_le_mul ENNReal.ofReal_ne_top fun ω s hs _ => by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← mul_sub, itoEnergy_enorm_sq, itoEnergy_enorm_sq,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_pow]
        have hZs : Z s ω ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hZ ω s hs) 2
        exact mul_le_mul_of_nonneg_right hZs (sq_nonneg _)
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (K ^ 2)) (hE T)
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) hle

/-- **Stopping the integrand.** If `h` is Itô-integrable and `τ` is a stopping time of `𝓖`, then
`h 𝟙_{s ≤ τ}` is Itô-integrable. -/
theorem IsItoIntegrable.indicator_stoppingTime {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) :
    IsItoIntegrable 𝓖 μ (fun i s ω => if s ≤ τ ω then h i s ω else 0) := by
  have hZ := mul_leftContinuous_aux hh (Z := fun s ω => if s ≤ τ ω then 1 else 0) (K := 1)
    (fun ω s _ => by split_ifs <;> simp) (fun t => ?_) (fun ω s _ => ?_)
  · convert hZ using 3 with i s ω
    funext ω
    split_ifs <;> simp
  · refine Measurable.ite ?_ measurable_const measurable_const
    have : {ω | ((t : ℝ≥0) : ℝ) ≤ τ ω} = {ω | (τ ω : WithTop ℝ≥0) < t}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, NNReal.coe_le_coe]
      exact ⟨fun h => not_lt.2 (WithTop.coe_le_coe.2 h), fun h => WithTop.coe_le_coe.1 (not_lt.1 h)⟩
    rw [this]
    exact (hτ.measurableSet_lt t).compl
  · apply lc_of_eventually
    by_cases hs : s ≤ τ ω
    · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≤ s)
      simp [hs, hr.trans hs]
    · filter_upwards [(eventually_gt_nhds (not_le.1 hs)).filter_mono nhdsWithin_le_nhds]
        with r hr
      simp [hs, not_le.2 hr]

/-- **Products with a bounded left-continuous adapted process.** If `h` is Itô-integrable and
`Z` is a real process, bounded by `K` at times `s > 0`, adapted, with left-continuous paths at
every `s > 0`, then `Z h` is Itô-integrable. -/
theorem IsItoIntegrable.mul_leftContinuous {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    {Z : ℝ → Ω → ℝ} {K : ℝ} (hZ : ∀ ω (s : ℝ), 0 < s → |Z s ω| ≤ K)
    (hZa : ∀ t : ℝ≥0, Measurable[𝓖 t] (Z t))
    (hZlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => Z r ω) (Set.Iic s) s) :
    IsItoIntegrable 𝓖 μ (fun i s ω => Z s ω * h i s ω) :=
  mul_leftContinuous_aux hh hZ hZa hZlc

/-- **Pulling out a known factor.** If `h` is Itô-integrable and `ξ` is bounded and
`𝓖_u`-measurable, then `ξ 𝟙_{s > u} h` is Itô-integrable. -/
theorem IsItoIntegrable.mul_indicator_gt {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    {u : ℝ≥0} {ξ : Ω → ℝ} (hξ : Measurable[𝓖 u] ξ) (hξb : ∃ C, ∀ ω, |ξ ω| ≤ C) :
    IsItoIntegrable 𝓖 μ (fun i s ω => if (u : ℝ) < s then ξ ω * h i s ω else 0) := by
  obtain ⟨C, hC⟩ := hξb
  have hZ := mul_leftContinuous_aux hh (Z := fun s ω => if (u : ℝ) < s then ξ ω else 0)
    (K := |C|) (fun ω s _ => ?_) (fun t => ?_) (fun ω s _ => ?_)
  · convert hZ using 3 with i s ω
    split_ifs <;> simp
  · split_ifs
    · exact (hC ω).trans (le_abs_self C)
    · simp
  · by_cases ht : (u : ℝ) < t
    · simp only [ht, ↓reduceIte]
      exact hξ.mono (𝓖.mono (NNReal.coe_lt_coe.1 ht).le) le_rfl
    · simp only [ht, ↓reduceIte]
      exact measurable_const
  · apply lc_of_eventually
    by_cases hs : (u : ℝ) < s
    · filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds] with r hr
      simp [hs, hr]
    · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≤ s)
      have : ¬ (u : ℝ) < r := fun h => hs (h.trans_le hr)
      simp [hs, this]

omit [Countable ι] in
open Classical in
/-- The family represented by the blocks of `e` whose index lies in `S` is `e 𝟙_{i ∈ S}`. -/
private lemma toFun_filter (e : ElemIntegrand 𝓖 ι) (S : Set ι) (i : ι) (s : ℝ) (ω : Ω) :
    ElemIntegrand.toFun (e.filter fun bl => decide (bl.i ∈ S)) i s ω =
      if i ∈ S then e.toFun i s ω else 0 := by
  induction e with
  | nil => simp [ElemIntegrand.toFun]
  | cons bl l ih =>
    have hc : ∀ l' : ElemIntegrand 𝓖 ι, ElemIntegrand.toFun (bl :: l') i s ω =
        (if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0) +
          ElemIntegrand.toFun l' i s ω := fun l' => by
      simp [ElemIntegrand.toFun]
    by_cases hb : bl.i ∈ S
    · rw [List.filter_cons_of_pos (by simpa using hb), hc, ih, hc]
      by_cases hi : i ∈ S
      · simp [hi]
      · have : bl.i ≠ i := fun h => hi (h ▸ hb)
        simp [hi, this]
    · rw [List.filter_cons_of_neg (by simpa using hb), ih, hc]
      by_cases hi : i ∈ S
      · have : bl.i ≠ i := fun h => hb (h ▸ hi)
        simp [hi, this]
      · simp [hi]

open Classical in
set_option linter.unusedSectionVars false in
/-- **Restriction to a set of indices.** If `h` is Itô-integrable, so is `h 𝟙_{i ∈ S}`. -/
theorem IsItoIntegrable.indicator_index {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    (S : Set ι) : IsItoIntegrable 𝓖 μ (fun i s ω => if i ∈ S then h i s ω else 0) := by
  obtain ⟨E, hE⟩ := hh.approx
  refine ⟨fun i => ?_, fun k => (E k).filter fun bl => decide (bl.i ∈ S), fun T => ?_⟩
  · by_cases hi : i ∈ S
    · simpa [hi] using hh.meas i
    · simp [hi]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE T) (fun _ => zero_le)
      fun k => ?_
    have := itoEnergy_le_mul (μ := μ) (T := T) (c := 1) ENNReal.one_ne_top
      (h := fun i s ω => ElemIntegrand.toFun ((E k).filter fun bl => decide (bl.i ∈ S)) i s ω -
        if i ∈ S then h i s ω else 0)
      (g := fun i s ω => (E k).toFun i s ω - h i s ω) fun ω s _ _ => by
        rw [one_mul]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [toFun_filter]
        split_ifs <;> simp
    simpa using this

end QSSEPtoKPZ
