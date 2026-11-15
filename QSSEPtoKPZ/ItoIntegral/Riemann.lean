/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Integrands

/-!
# Riemann sums (package C, task C4)

INTERFACE FILE (task I0 of Stage 2): the definition below is complete; the theorems are frozen
interfaces, proved by task C4. See `docs/stage2-design.md`, Section 2.2 ("Riemann sums"), and
`docs/stage2-interfaces.md`.

This is the bridge between the project's Itô integral `stochInt` and the left-point Riemann sums
`itoSum` of the frozen statement (`Definitions.lean`): `realRiemann f W t m` is the real
analogue of `itoSum f W t m`, with the same grid `t_k = k t / m`. Left-point Riemann sums of a
bounded, left-continuous, adapted integrand converge in `L²` to its Itô integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The left-point Riemann sum `∑_{k < m} f(t_k) (W(t_{k+1}) - W(t_k))`, `t_k = k t / m`, of a
real process `f` against a real process `W` (the real analogue of `itoSum`). -/
def realRiemann (f W : ℝ → Ω → ℝ) (t : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range m,
    f ((k : ℝ) * t / m) ω * (W (((k : ℝ) + 1) * t / m) ω - W ((k : ℝ) * t / m) ω)

variable {ι : Type*} [Countable ι] {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-- `eLpNorm g 2 μ = (∫ g²)^{1/2}` for measurable `g`. -/
private lemma eLpNorm_two_eq {g : Ω → ℝ} (hg : Measurable g) (μ : Measure Ω) :
    eLpNorm g 2 μ = (∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  congr 2
  funext ω
  rw [ENNReal.rpow_two, itoEnergy_enorm_sq]

/-- **Core of the Riemann-sum theorems.** For one index `i` and one bounded left-continuous
adapted `f`, the difference `realRiemann f (B i) t m - ∫_0^t f dBᵢ` is almost surely the Itô
integral `I_t(D_m)` of `D_m = e_m - f 𝟙_{j = i}`, where `e_m` is the elementary integrand with
coefficients `f(kt/m)` on the cells `(kt/m, (k+1)t/m]`, and `‖I_t(D_m)‖_{L²} → 0` by the
isometry and dominated convergence. -/
private lemma riemann_aux [DecidableEq ι] (hB : IsBrownianFamily 𝓖 B μ) (i : ι)
    {f : ℝ → Ω → ℝ} {K : ℝ} (hf : ∀ s : ℝ, 0 ≤ s → ∀ ω, |f s ω| ≤ K)
    (hfa : ∀ t : ℝ≥0, Measurable[𝓖 t] (f t))
    (hlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s)
    (t : ℝ≥0) :
    ∃ D : ℕ → ι → ℝ → Ω → ℝ, (∀ m, ∀ᵐ ω ∂μ, realRiemann f (B i) t m ω -
        stochInt 𝓖 μ B (fun j s ω => if j = i then f s ω else 0) t ω =
          stochInt 𝓖 μ B (D m) t ω) ∧
      Tendsto (fun m => eLpNorm (stochInt 𝓖 μ B (D m) t) 2 μ) atTop (𝓝 0) := by
  have hbd : ∀ ω (s : ℝ), 0 < s → |f s ω| ≤ K := fun ω s hs => hf s hs.le ω
  have hF : IsItoIntegrable 𝓖 μ (fun j s ω => if j = i then f s ω else 0) :=
    isItoIntegrable_single_of_leftContinuous i hbd hfa hlc
  let δ : ℕ → ℝ≥0 := fun m => t / m
  have hδ : ∀ m, (δ m : ℝ) = t / m := fun m => by simp [δ]
  have hξ : ∀ m (k : ℕ), Measurable[𝓖 ((k : ℝ≥0) * δ m)] (f (k * (δ m : ℝ))) :=
    fun m k => itoGrid_measurable_point hfa (δ m) k
  have hξb : ∀ m (k : ℕ) ω, |f (k * (δ m : ℝ)) ω| ≤ K := fun m k ω => hf _ (by positivity) ω
  let e : ℕ → ElemIntegrand 𝓖 ι := fun m =>
    itoGridElem i (δ m) m (fun k => f (k * (δ m : ℝ))) (hξ m) K (hξb m)
  have hint : ∀ m ω, (e m).integral B t ω = realRiemann f (B i) t m ω := by
    intro m ω
    simp only [e, ElemIntegrand.integral, itoGridElem, realRiemann]
    rw [List.map_map, itoGrid_list_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k < m := Finset.mem_range.1 hk
    have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le k).trans_lt hkm
    have hkm' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hkm
    have ht : (0 : ℝ) ≤ t := t.2
    have e1 : (((k : ℝ≥0) * δ m : ℝ≥0) : ℝ) = k * t / m := by
      rw [NNReal.coe_mul, hδ]; push_cast; ring
    have e2 : ((((k : ℝ≥0) + 1) * δ m : ℝ≥0) : ℝ) = (k + 1) * t / m := by
      rw [NNReal.coe_mul, hδ]; push_cast; ring
    have l1 : (k : ℝ) * t / m ≤ t := by
      rw [div_le_iff₀ hm]; nlinarith
    have l2 : ((k : ℝ) + 1) * t / m ≤ t := by
      rw [div_le_iff₀ hm]; nlinarith
    simp only [Function.comp_apply, e1, e2, min_eq_right l1, min_eq_right l2, hδ]
    congr 2
  refine ⟨fun m j s ω => (e m).toFun j s ω + -1 * (if j = i then f s ω else 0),
    fun m => ?_, ?_⟩
  · filter_upwards [stochInt_elem hB (e m),
      stochInt_add hB (isItoIntegrable_elem (e m)) (hF.const_mul (-1)),
      stochInt_const_mul hB hF (-1)] with ω h1 h2 h3
    rw [h2 t, h1 t, h3 t, hint]
    ring
  · have hE : Tendsto (fun m => energy μ (fun j s ω => (e m).toFun j s ω -
        (if j = i then f s ω else 0)) t) atTop (𝓝 0) := by
      refine tendsto_energy_itoGridElem_sub i hbd
        (measurable_pos_of_leftContinuous hbd hfa hlc) δ (fun m => m)
        (fun m k => f (k * (δ m : ℝ))) hξ K hξb fun ω s hs hst => ?_
      have htpos : (0 : ℝ) < t := hs.trans_le hst
      exact tendsto_itoGridStep (φ := id) (δ := fun m => (δ m : ℝ)) continuous_id hs
        ((eventually_gt_atTop 0).mono fun m hm => by rw [hδ]; positivity)
        (by simpa only [hδ] using tendsto_const_div_atTop_nhds_zero_nat (t : ℝ))
        ((eventually_gt_atTop 0).mono fun m hm => by
          rw [hδ, mul_div_cancel₀ _ (by exact_mod_cast hm.ne')]; exact hst)
        (hlc ω s hs)
    have hDi : ∀ m, IsItoIntegrable 𝓖 μ
        (fun j s ω => (e m).toFun j s ω + -1 * (if j = i then f s ω else 0)) :=
      fun m => (isItoIntegrable_elem (e m)).add (hF.const_mul (-1))
    have heq : ∀ m, eLpNorm (stochInt 𝓖 μ B
        (fun j s ω => (e m).toFun j s ω + -1 * (if j = i then f s ω else 0)) t) 2 μ =
        energy μ (fun j s ω => (e m).toFun j s ω - (if j = i then f s ω else 0)) t ^
          (1 / (2 : ℝ)) := by
      intro m
      rw [eLpNorm_two_eq ((stochInt_adapted hB _ t).mono (𝓖.le t) le_rfl),
        lintegral_stochInt_sq hB (hDi m)]
      congr 2
      funext j s ω
      ring
    simp_rw [heq]
    have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hE
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

/-- **Riemann sums, one Brownian motion.** Let `f` be a real process, bounded by `K` at times
`s ≥ 0`, adapted to `𝓖`, with left-continuous paths at every `s > 0`. Then the family
`f 𝟙_{j = i}` is Itô-integrable, and for every `t ≥ 0` the left-point Riemann sums of `f`
against `Bᵢ` on `[0, t]` converge in `L²` to `∫_0^t f(s) dBᵢ(s)`. -/
theorem tendsto_riemann_stochInt [DecidableEq ι] (hB : IsBrownianFamily 𝓖 B μ) (i : ι)
    {f : ℝ → Ω → ℝ} {K : ℝ} (hf : ∀ s : ℝ, 0 ≤ s → ∀ ω, |f s ω| ≤ K)
    (hfa : ∀ t : ℝ≥0, Measurable[𝓖 t] (f t))
    (hlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s)
    (t : ℝ≥0) :
    IsItoIntegrable 𝓖 μ (fun j s ω => if j = i then f s ω else 0) ∧
    Tendsto (fun m : ℕ => eLpNorm (fun ω => realRiemann f (B i) t m ω -
        stochInt 𝓖 μ B (fun j s ω => if j = i then f s ω else 0) t ω) 2 μ) atTop (𝓝 0) := by
  refine ⟨isItoIntegrable_single_of_leftContinuous i (fun ω s hs => hf s hs.le ω) hfa hlc, ?_⟩
  obtain ⟨D, hD, hlim⟩ := riemann_aux hB i hf hfa hlc t
  exact hlim.congr fun m => (eLpNorm_congr_ae (hD m)).symm

/-- **Riemann sums, finitely many Brownian motions.** Same as `tendsto_riemann_stochInt` for a
finite set `S` of indices and processes `f j`, `j ∈ S`: the family `f j 𝟙_{j ∈ S}` is
Itô-integrable, and `∑_{j ∈ S} (Riemann sum of f j against B j)` converges in `L²` to
`∑_{j ∈ S} ∫_0^t f j(s) dB j(s)`. -/
theorem tendsto_riemann_stochInt_finset [DecidableEq ι] (hB : IsBrownianFamily 𝓖 B μ)
    (S : Finset ι) {f : ι → ℝ → Ω → ℝ} {K : ℝ}
    (hf : ∀ j ∈ S, ∀ s : ℝ, 0 ≤ s → ∀ ω, |f j s ω| ≤ K)
    (hfa : ∀ j ∈ S, ∀ t : ℝ≥0, Measurable[𝓖 t] (f j t))
    (hlc : ∀ j ∈ S, ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f j r ω) (Set.Iic s) s)
    (t : ℝ≥0) :
    IsItoIntegrable 𝓖 μ (fun j s ω => if j ∈ S then f j s ω else 0) ∧
    Tendsto (fun m : ℕ => eLpNorm (fun ω => ∑ j ∈ S, realRiemann (f j) (B j) t m ω -
        stochInt 𝓖 μ B (fun j s ω => if j ∈ S then f j s ω else 0) t ω) 2 μ)
      atTop (𝓝 0) := by
  classical
  -- `f'` agrees with `f` on `S` and vanishes outside
  let f' : ι → ℝ → Ω → ℝ := fun k s ω => if k ∈ S then f k s ω else 0
  have hf' : ∀ k s, 0 ≤ s → ∀ ω, |f' k s ω| ≤ |K| := fun k s hs ω => by
    simp only [f']
    split_ifs with hk
    · exact (hf k hk s hs ω).trans (le_abs_self K)
    · simp
  have hfa' : ∀ k (t : ℝ≥0), Measurable[𝓖 t] (f' k t) := fun k t => by
    by_cases hk : k ∈ S
    · simpa [f', hk] using hfa k hk t
    · simp [f', hk]
  have hlc' : ∀ k ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f' k r ω) (Set.Iic s) s :=
    fun k ω s hs => by
      by_cases hk : k ∈ S
      · simpa [f', hk] using hlc k hk ω s hs
      · simpa [f', hk] using continuousWithinAt_const
  have hG : ∀ k, IsItoIntegrable 𝓖 μ (fun j s ω => if j = k then f' k s ω else 0) :=
    fun k => isItoIntegrable_single_of_leftContinuous k (fun ω s hs => hf' k s hs.le ω)
      (hfa' k) (hlc' k)
  have hsum : (fun j s ω => if j ∈ S then f j s ω else 0) =
      fun j s ω => ∑ k ∈ S, (fun j s ω => if j = k then f' k s ω else 0) j s ω := by
    funext j s ω
    rw [Finset.sum_ite_eq]
    by_cases hj : j ∈ S <;> simp [f', hj]
  refine ⟨hsum ▸ IsItoIntegrable.finset_sum S fun k _ => hG k, ?_⟩
  choose D hD hlim using fun k => riemann_aux hB k (hf' k) (hfa' k) (hlc' k) t
  have hae : ∀ m, ∀ᵐ ω ∂μ, (∑ j ∈ S, realRiemann (f j) (B j) t m ω -
      stochInt 𝓖 μ B (fun j s ω => if j ∈ S then f j s ω else 0) t ω) =
      ∑ k ∈ S, stochInt 𝓖 μ B (D k m) t ω := by
    intro m
    have hall : ∀ᵐ ω ∂μ, ∀ k ∈ S, realRiemann (f' k) (B k) t m ω -
        stochInt 𝓖 μ B (fun j s ω => if j = k then f' k s ω else 0) t ω =
          stochInt 𝓖 μ B (D k m) t ω :=
      (eventually_all_finset S).2 fun k _ => hD k m
    filter_upwards [hall, stochInt_finset_sum hB S fun k _ => hG k] with ω hω hsω
    rw [hsum, hsω t, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← hω k hk]
    have : f' k = f k := by funext s ω; simp [f', hk]
    rw [this]
  have hle : ∀ m, eLpNorm (fun ω => ∑ j ∈ S, realRiemann (f j) (B j) t m ω -
      stochInt 𝓖 μ B (fun j s ω => if j ∈ S then f j s ω else 0) t ω) 2 μ ≤
      ∑ k ∈ S, eLpNorm (stochInt 𝓖 μ B (D k m) t) 2 μ := by
    intro m
    rw [eLpNorm_congr_ae (hae m)]
    refine le_of_eq_of_le ?_ (eLpNorm_sum_le (f := fun k => stochInt 𝓖 μ B (D k m) t)
      (s := S) (by norm_num))
    congr 1
    funext ω
    simp [Finset.sum_apply]
  have hup : Tendsto (fun m => ∑ k ∈ S, eLpNorm (stochInt 𝓖 μ B (D k m) t) 2 μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum S fun k _ => hlim k
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) hle

end QSSEPtoKPZ
