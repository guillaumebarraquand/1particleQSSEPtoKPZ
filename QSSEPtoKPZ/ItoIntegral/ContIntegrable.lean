/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Integrands
public import QSSEPtoKPZ.ItoIntegral.Basic
public import QSSEPtoKPZ.ItoIntegral.Energy
public import QSSEPtoKPZ.ItoIntegral.Grid
public import QSSEPtoKPZ.Martingales.Doob

/-!
# Continuous adapted integrands with finite energy (task G11a)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task G11a.
`docs/stage5-design.md`, Section 3.3.

* `isItoIntegrable_of_continuous`: a countable family `h` of adapted processes with continuous
  paths (for every `ω`), whose pointwise energy `s ↦ ∑ᵢ hᵢ(s)²` is finite and continuous and
  whose energy `𝔼 ∫_0^T ∑ᵢ hᵢ²` is finite for every `T`, is Itô-integrable. (Truncate:
  `h · min(1, K / ‖h‖)` is bounded, adapted and continuous, `isItoIntegrable_of_leftContinuous`;
  dominated convergence as `K → ∞`; `IsItoIntegrable.of_tendsto`.)
* `lintegral_tsum_iSup_stochInt_sq_le`: Doob's inequality summed over a countable family of
  integrands, `𝔼 ∑ₖ sup_{t ≤ T} I_t(h^k)² ≤ 4 ∑ₖ 𝔼 ∫_0^T ∑ᵢ (h^k_i)²`.

Proofs (task G11a). The truncation is `h · c_K(∑ᵢ hᵢ²)` with `c_K(x) = K / max(K, √x)`
(`= min(1, K / ‖h‖)`), `K = n + 1`. For fixed `(s, ω)` it equals `h` for `K` large, which gives
the joint measurability of `h` as a pointwise limit; for fixed `ω`, `∑ᵢ hᵢ²` is bounded on
`[0, T]` by continuity, so the path energy of the difference vanishes for `K` large, and
dominated convergence in `ω` (by the path energy of `h`) concludes. For the summed Doob
inequality, each supremum over `[0, T]` is almost surely the supremum over the dyadic grid of
`[0, T]` (`gridPt`), hence a.e. measurable, and `lintegral_tsum` applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

open StochIntAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Countable ι]
  {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Auxiliary results (task G11a) -/

/-- The truncation factor `c_K(x) = K / max(K, √x) ∈ [0, 1]`, used with `x = ∑ᵢ hᵢ²`. -/
private def contIntCut (K x : ℝ) : ℝ := K / max K (√x)

private lemma contIntCut_max_pos {K : ℝ} (hK : 0 < K) (x : ℝ) : 0 < max K (√x) :=
  hK.trans_le (le_max_left _ _)

private lemma continuous_contIntCut {K : ℝ} (hK : 0 < K) : Continuous (contIntCut K) :=
  continuous_const.div (continuous_const.max Real.continuous_sqrt)
    fun x => (contIntCut_max_pos hK x).ne'

private lemma contIntCut_nonneg {K : ℝ} (hK : 0 < K) (x : ℝ) : 0 ≤ contIntCut K x :=
  div_nonneg hK.le (contIntCut_max_pos hK x).le

private lemma contIntCut_le_one {K : ℝ} (hK : 0 < K) (x : ℝ) : contIntCut K x ≤ 1 :=
  div_le_one_of_le₀ (le_max_left _ _) (contIntCut_max_pos hK x).le

/-- `c_K(x) = 1` for `x ≤ K²`. -/
private lemma contIntCut_eq_one {K x : ℝ} (hK : 0 < K) (hx : x ≤ K ^ 2) :
    contIntCut K x = 1 := by
  have : √x ≤ K := Real.sqrt_le_iff.2 ⟨hK.le, hx⟩
  rw [contIntCut, max_eq_left this, div_self hK.ne']

/-- `x c_K(x)² ≤ K²` for `x ≥ 0`. -/
private lemma contIntCut_sq_mul_le {K x : ℝ} (hK : 0 < K) (hx : 0 ≤ x) :
    x * contIntCut K x ^ 2 ≤ K ^ 2 := by
  have hm := contIntCut_max_pos hK x
  have hxm : x ≤ (max K √x) ^ 2 :=
    calc x = √x ^ 2 := (Real.sq_sqrt hx).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
  rw [contIntCut, div_pow, mul_div_assoc', div_le_iff₀ (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_left hxm (sq_nonneg K)

/-- A function of `t ∈ ℝ` whose restriction to `[0, ∞)` is continuous (as a function on `ℝ≥0`)
is continuous at every `s > 0`. -/
private lemma contInt_continuousAt {f : ℝ → ℝ} (hf : Continuous fun t : ℝ≥0 => f t) {s : ℝ}
    (hs : 0 < s) : ContinuousAt f s := by
  have : ContinuousAt (fun r : ℝ => f (r.toNNReal : ℝ)) s :=
    (hf.comp continuous_real_toNNReal).continuousAt
  refine this.congr ?_
  filter_upwards [lt_mem_nhds hs] with r hr
  simp [Real.coe_toNNReal _ hr.le]

/-- The truncated family `h · c_{n+1}(∑ⱼ hⱼ²)`. -/
private def contIntTrunc (h : ι → ℝ → Ω → ℝ) (n : ℕ) (i : ι) (s : ℝ) (ω : Ω) : ℝ :=
  h i s ω * contIntCut ((n : ℝ) + 1) (∑' j, h j s ω ^ 2)

omit [Countable ι] in
private lemma contIntTrunc_eventually_eq (h : ι → ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, ∀ i, contIntTrunc h n i s ω = h i s ω := by
  filter_upwards [eventually_ge_atTop ⌈∑' j, h j s ω ^ 2⌉₊] with n hn i
  have h1 : ∑' j, h j s ω ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  rw [contIntTrunc, contIntCut_eq_one (by positivity) (h1.trans h2), mul_one]

/-- The supremum over `[0, T]` of `I_t(h)²` is almost everywhere measurable (it equals,
almost surely, the supremum over the dyadic grid of `[0, T]`, by path continuity). -/
private lemma contInt_aemeasurable_iSup {B : ι → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓖 B μ)
    {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) (T : ℝ) :
    AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (stochInt 𝓖 μ B h t ω ^ 2)) μ := by
  rcases lt_or_ge T 0 with hT | hT
  · simp only [Set.Icc_eq_empty (not_le.2 hT), Set.mem_empty_iff_false, iSup_false,
      iSup_const]
    exact aemeasurable_const
  set τ := T.toNNReal with hτ
  have hτT : (τ : ℝ) = T := Real.coe_toNNReal _ hT
  have hgrid : ∀ j k, ((gridPt τ j k : ℝ≥0) : ℝ) ∈ Set.Icc (0 : ℝ) T := fun j k =>
    ⟨NNReal.coe_nonneg _, hτT ▸ NNReal.coe_le_coe.2 (gridPt_le τ j k)⟩
  refine AEMeasurable.congr (f := fun ω => ⨆ j : ℕ, ⨆ k : ℕ,
      ENNReal.ofReal (stochInt 𝓖 μ B h (gridPt τ j k) ω ^ 2)) ?_ ?_
  · exact (Measurable.iSup fun j => Measurable.iSup fun k => ENNReal.measurable_ofReal.comp
      ((((stochInt_adapted hB h _).mono (𝓖.le _) le_rfl)).pow_const 2)).aemeasurable
  · filter_upwards [stochInt_continuous hB hh] with ω hω
    apply le_antisymm
    · exact iSup_le fun j => iSup_le fun k =>
        le_iSup₂ (f := fun t _ => ENNReal.ofReal (stochInt 𝓖 μ B h t ω ^ 2)) _ (hgrid j k)
    · refine iSup₂_le fun t ht => ?_
      obtain ⟨_, hlim⟩ := tendsto_gridPt hT ht
      have hc : Continuous fun r : ℝ =>
          ENNReal.ofReal (stochInt 𝓖 μ B h (r.toNNReal : ℝ) ω ^ 2) :=
        ENNReal.continuous_ofReal.comp ((hω.comp continuous_real_toNNReal).pow 2)
      have hl := (hc.tendsto t).comp hlim
      simp only [Function.comp_def, Real.toNNReal_coe, Real.coe_toNNReal _ ht.1] at hl
      exact le_of_tendsto' hl fun j => le_iSup_of_le j (le_iSup_of_le _ le_rfl)

/-! ### Interfaces -/

/-- **Continuous adapted integrands with finite energy are Itô-integrable.** If each `hᵢ` is
adapted to `𝓖` with all paths continuous on `[0, ∞)`, if `∑ᵢ hᵢ(s)²` converges for all `s` and
`ω` and is continuous in `s ≥ 0` for every `ω`, and if `𝔼 ∫_0^T ∑ᵢ hᵢ(s)² ds < ∞` for every
`T`, then `h` is Itô-integrable. -/
theorem isItoIntegrable_of_continuous {h : ι → ℝ → Ω → ℝ}
    (hadapt : ∀ i (t : ℝ≥0), Measurable[𝓖 t] (h i t))
    (hcont : ∀ i ω, Continuous fun t : ℝ≥0 => h i t ω)
    (hsum : ∀ ω (s : ℝ), Summable fun i => h i s ω ^ 2)
    (hsc : ∀ ω, Continuous fun t : ℝ≥0 => ∑' i, h i t ω ^ 2)
    (hE : ∀ T : ℝ, energy μ h T < ⊤) :
    IsItoIntegrable 𝓖 μ h := by
  have hK : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hNm : ∀ t : ℝ≥0, Measurable[𝓖 t] fun ω => ∑' j, h j t ω ^ 2 := by
    intro t
    let : MeasurableSpace Ω := 𝓖 t
    exact measurable_tsum_real fun j => (hadapt j t).pow_const 2
  -- the truncations are bounded, adapted and continuous
  have hgI : ∀ n, IsItoIntegrable 𝓖 μ (contIntTrunc h n) := by
    intro n
    refine isItoIntegrable_of_leftContinuous (K := ((n : ℝ) + 1) ^ 2) (fun ω s _ => ?_)
      (fun i t => ?_) (fun i ω s hs => ?_)
    · have hsm : Summable fun i => contIntTrunc h n i s ω ^ 2 := by
        simp only [contIntTrunc, mul_pow]
        exact (hsum ω s).mul_right _
      refine ⟨hsm, ?_⟩
      simp only [contIntTrunc, mul_pow]
      rw [tsum_mul_right]
      exact contIntCut_sq_mul_le (hK n) (tsum_nonneg fun i => sq_nonneg _)
    · exact (hadapt i t).mul ((continuous_contIntCut (hK n)).measurable.comp (hNm t))
    · exact ((contInt_continuousAt (hcont i ω) hs).mul
        ((continuous_contIntCut (hK n)).continuousAt.comp
          (contInt_continuousAt (hsc ω) hs))).continuousWithinAt
  -- joint measurability of `h`: pointwise limit of the truncations
  have hm : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h i p.1 p.2 else 0 := by
    intro i
    refine measurable_of_tendsto_metrizable (fun n => (hgI n).meas i) ?_
    rw [tendsto_pi_nhds]
    rintro ⟨s, ω⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [contIntTrunc_eventually_eq h s ω] with n hn
    simp only [hn i]
  refine IsItoIntegrable.of_tendsto hgI hm fun T => ?_
  have hEm : ∀ n, EnergyMeas fun i s ω => contIntTrunc h n i s ω - h i s ω :=
    fun n => EnergyMeas.sub (hgI n).meas hm
  -- dominated convergence in `ω`, dominated by the path energy of `h`
  have := tendsto_lintegral_of_dominated_convergence (μ := μ) (f := fun _ => 0)
    (F := fun n => pathEnergy (fun i s ω => contIntTrunc h n i s ω - h i s ω) T)
    (pathEnergy h T) (fun n => measurable_pathEnergy (hEm n) T)
    (fun n => ae_of_all _ fun ω => ?_) (hE T).ne (ae_of_all _ fun ω => ?_)
  · simpa [energy] using this
  · refine lintegral_mono fun s => ENNReal.tsum_le_tsum fun i => ?_
    have hc0 := contIntCut_nonneg (hK n) (∑' j, h j s ω ^ 2)
    have hc1 := contIntCut_le_one (hK n) (∑' j, h j s ω ^ 2)
    have : |contIntTrunc h n i s ω - h i s ω| ≤ |h i s ω| := by
      rw [contIntTrunc, ← mul_sub_one, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩)
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    gcongr
  · -- for fixed `ω`, `∑ᵢ hᵢ²` is bounded on `[0, T]`, so the truncation is eventually exact
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T.toNNReal)).exists_bound_of_continuousOn
      (hsc ω).continuousOn
    have hbd : ∀ s ∈ Set.Ioc 0 T, ∑' j, h j s ω ^ 2 ≤ C := by
      intro s hs
      have := hC s.toNNReal ⟨zero_le, Real.toNNReal_le_toNNReal hs.2⟩
      rw [Real.coe_toNNReal _ hs.1.le] at this
      exact (le_abs_self _).trans this
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈C⌉₊] with n hn
    symm
    refine le_antisymm ((setLIntegral_mono' measurableSet_Ioc fun s hs => ?_).trans_eq
      (lintegral_zero)) (zero_le)
    have h1 : ∑' j, h j s ω ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      have := (hbd s hs).trans ((Nat.le_ceil C).trans (Nat.cast_le.2 hn))
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    simp [contIntTrunc, contIntCut_eq_one (hK n) h1]

/-- **Doob's inequality, summed over a countable family of integrands:**
`𝔼 ∑ₖ sup_{t ∈ [0,T]} I_t(h^k)² ≤ 4 ∑ₖ 𝔼 ∫_0^T ∑ᵢ h^k_i(s)² ds` (in `[0, ∞]`). Used for the
`ℓ²(ℤ)`-valued martingale parts of the Picard iterates (one integrand per site). -/
theorem lintegral_tsum_iSup_stochInt_sq_le {B : ι → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓖 B μ)
    {κ : Type*} [Countable κ] {h : κ → ι → ℝ → Ω → ℝ} (hh : ∀ k, IsItoIntegrable 𝓖 μ (h k))
    (T : ℝ) :
    ∫⁻ ω, (∑' k, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (stochInt 𝓖 μ B (h k) t ω ^ 2)) ∂μ ≤
      4 * ∑' k, energy μ (h k) T := by
  rw [lintegral_tsum fun k => contInt_aemeasurable_iSup hB (hh k) T, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun k => lintegral_iSup_stochInt_sq_le hB (hh k) T

end QSSEPtoKPZ
