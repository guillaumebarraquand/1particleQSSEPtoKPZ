/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Compact sets of `ℳ₊(ℝ)`: the `cosh`-balls (task H3)

INTERFACE FILE (task I0' of Stage 3): the statement below is an interface, proved by task H3.
See `docs/stage3-design.md`, Sections 1.2 (b) and 2.4, and `docs/stage3-interfaces.md`.

For `M < ∞`, the set `𝒦_M = {μ ∈ ℳ₊(ℝ) : ∫ cosh dμ ≤ M}` is compact for the topology of weak
convergence (article, proof of Proposition 5.1, condition (i)). Proof: it is closed, since
`μ ↦ ∫ cosh dμ = sup_N ∫ min(cosh, N) dμ` is lower semicontinuous; its elements have mass at
most `M` and give mass at most `M / cosh ℓ` to `ℝ ∖ [-ℓ, ℓ]`; Prokhorov's theorem in Mathlib's
form (`isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le`) concludes.

The integral is the lower Lebesgue integral of `ofReal ∘ cosh` in `[0, ∞]`, which needs no
integrability.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The `cosh`-ball `𝒦_M = {μ ∈ ℳ₊(ℝ) : ∫ cosh dμ ≤ M}` (integral in `[0, ∞]`). -/
def tightCoshBall (M : ℝ≥0∞) : Set (FiniteMeasure ℝ) :=
  {μ | ∫⁻ x, ENNReal.ofReal (Real.cosh x) ∂(μ : Measure ℝ) ≤ M}

/-- The truncation `min(cosh, N)` as a bounded continuous function (bound `N`). -/
private def coshTrunc (N : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (Real.cosh x) N)
    (Real.continuous_cosh.min continuous_const) N fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.cosh_pos x).le (Nat.cast_nonneg N))]
      exact min_le_right _ _

/-- `∫⁻ min(cosh, N) dμ = ofReal (∫ min(cosh, N) dμ)` for a finite measure `μ`. -/
private theorem coshTrunc_lintegral (μ : FiniteMeasure ℝ) (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (coshTrunc N x) ∂(μ : Measure ℝ) =
      ENNReal.ofReal (∫ x, coshTrunc N x ∂(μ : Measure ℝ)) :=
  (ofReal_integral_eq_lintegral_ofReal ((coshTrunc N).integrable _)
    (ae_of_all _ fun x => le_min (Real.cosh_pos x).le (Nat.cast_nonneg N))).symm

/-- Monotone convergence: `∫⁻ cosh dμ = sup_N ∫⁻ min(cosh, N) dμ`. -/
private theorem lintegral_cosh_eq_iSup (μ : Measure ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh x) ∂μ =
      ⨆ N : ℕ, ∫⁻ x, ENNReal.ofReal (coshTrunc N x) ∂μ := by
  rw [← lintegral_iSup (f := fun N x => ENNReal.ofReal (coshTrunc N x))
    (fun N => ENNReal.measurable_ofReal.comp (coshTrunc N).continuous.measurable)
    fun N N' h x => ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 h))]
  congr 1
  funext x
  refine le_antisymm ?_ (iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _))
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.cosh x)
  refine le_iSup_of_le N (le_of_eq ?_)
  change ENNReal.ofReal (Real.cosh x) = ENNReal.ofReal (min (Real.cosh x) N)
  rw [min_eq_left hN]

/-- The `cosh`-ball is closed: `μ ↦ ∫ cosh dμ` is lower semicontinuous, as the supremum of the
continuous maps `μ ↦ ∫ min(cosh, N) dμ`. -/
private theorem isClosed_tightCoshBall (M : ℝ≥0∞) (hM : M ≠ ⊤) : IsClosed (tightCoshBall M) := by
  have : tightCoshBall M =
      ⋂ N : ℕ, {μ : FiniteMeasure ℝ | ∫ x, coshTrunc N x ∂(μ : Measure ℝ) ≤ M.toReal} := by
    ext μ
    simp only [tightCoshBall, Set.mem_ofPred_eq, Set.mem_iInter, lintegral_cosh_eq_iSup,
      iSup_le_iff, coshTrunc_lintegral, ENNReal.ofReal_le_iff_le_toReal hM]
  rw [this]
  exact isClosed_iInter fun N =>
    isClosed_le (FiniteMeasure.continuous_integral_boundedContinuousFunction _) continuous_const

/-- `cosh x ≥ (|x| + 1) / 2`. -/
private theorem coshBall_cosh_ge (x : ℝ) : (|x| + 1) / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (-x)
  have h3 := Real.exp_pos x
  have h4 := Real.exp_pos (-x)
  rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

/-- **Compact containment set** (article, proof of Proposition 5.1, condition (i)):
`{μ : ∫ cosh dμ ≤ M}` is compact in `ℳ₊(ℝ)` for `M < ∞`. -/
theorem isCompact_tightCoshBall (M : ℝ≥0∞) (hM : M ≠ ⊤) : IsCompact (tightCoshBall M) := by
  set M' : ℝ≥0 := M.toNNReal
  have hMM' : M = M' := (ENNReal.coe_toNNReal hM).symm
  set K : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) n
  set u : ℕ → ℝ≥0 := fun n => 2 * M' * (1 / ((n : ℝ≥0) + 1))
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).const_mul (2 * M')
  have hK : Monotone K := fun n n' h => Set.Icc_subset_Icc (by simpa using h) (by simpa using h)
  refine (isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le M' hu
    (fun n => isCompact_Icc) (Or.inr hK)).of_isClosed_subset (isClosed_tightCoshBall M hM) ?_
  intro μ hμ
  simp only [tightCoshBall, Set.mem_ofPred_eq] at hμ
  refine ⟨?_, fun n => ?_⟩
  · -- mass `≤ M`, since `cosh ≥ 1`
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, ← hMM']
    calc (μ : Measure ℝ) Set.univ = ∫⁻ _, 1 ∂(μ : Measure ℝ) := by rw [lintegral_one]
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.cosh x) ∂(μ : Measure ℝ) :=
          lintegral_mono fun x => by
            simp
      _ ≤ M := hμ
  · -- Markov: `μ([-n, n]ᶜ) ≤ 2 M / (n + 1)`, since `cosh ≥ (n + 1) / 2` off `[-n, n]`
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    have hc : ENNReal.ofReal (((n : ℝ) + 1) / 2) * (μ : Measure ℝ) (K n)ᶜ ≤ M := by
      calc ENNReal.ofReal (((n : ℝ) + 1) / 2) * (μ : Measure ℝ) (K n)ᶜ
          = ∫⁻ _ in (K n)ᶜ, ENNReal.ofReal (((n : ℝ) + 1) / 2) ∂(μ : Measure ℝ) := by
            rw [setLIntegral_const]
        _ ≤ ∫⁻ x in (K n)ᶜ, ENNReal.ofReal (Real.cosh x) ∂(μ : Measure ℝ) := by
            refine setLIntegral_mono
              (ENNReal.measurable_ofReal.comp Real.continuous_cosh.measurable) fun x hx => ?_
            refine ENNReal.ofReal_le_ofReal (le_trans ?_ (coshBall_cosh_ge x))
            have : (n : ℝ) ≤ |x| := by
              simp only [K, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
              rcases hx with h | h
              · exact le_abs.2 (Or.inr (by linarith))
              · exact le_abs.2 (Or.inl h.le)
            linarith
        _ ≤ ∫⁻ x, ENNReal.ofReal (Real.cosh x) ∂(μ : Measure ℝ) := setLIntegral_le_lintegral _ _
        _ ≤ M := hμ
    have hpos : ENNReal.ofReal (((n : ℝ) + 1) / 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)] at hc
    refine hc.trans (le_of_eq ?_)
    have hc0 : (((n : ℝ) + 1) / 2).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
    rw [hMM', ENNReal.ofReal, ← ENNReal.coe_div hc0, ENNReal.coe_inj, ← NNReal.coe_inj]
    have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 := by positivity
    simp only [u, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one,
      NNReal.coe_add, NNReal.coe_natCast, Real.coe_toNNReal _ hn]
    field_simp


end QSSEPtoKPZ
