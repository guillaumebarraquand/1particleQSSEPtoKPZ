/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.CovariationAlgebra
public import QSSEPtoKPZ.Martingales.StoppingAux

/-!
# Covariation of elementary integrals `a (M_{t ∧ ·} - M_{s ∧ ·})` (task G8a, auxiliary)

Generic martingale lemmas used for the simple integrands `a 𝟙_{(s,t]}(r) φ(x)` of
`IsMMIntegral`:

* `HasCovariation.mmStop`: stopping at a deterministic time,
  `⟨M_{· ∧ τ}, N⟩ = ⟨M, N⟩_{· ∧ τ}`;
* `HasCovariation.mmMulOfVanish`: if `D` and its covariation `E` with `N` vanish up to time
  `σ`, and `a` is bounded and `𝓕_σ`-measurable, then `⟨a D, N⟩ = a E`;
* `HasCovariation.mmBlock`: their combination,
  `⟨a (M_{· ∧ t} - M_{· ∧ s}), N⟩ = a (⟨M, N⟩_{· ∧ t} - ⟨M, N⟩_{· ∧ s})` for `s ≤ t` and `a`
  bounded and `𝓕_s`-measurable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {T : ℝ}

/-- The covariation process at time `τ ≤ T` is almost everywhere `𝓕_τ`-measurable. -/
private lemma mm_aesm_cov {M N C : ℝ → Ω → ℝ} (h : HasCovariation T 𝓕 M N C μ) (τ : ℝ≥0)
    (hτ : (τ : ℝ) ≤ T) : AEStronglyMeasurable[𝓕 τ] (C τ) μ := by
  have h1 : AEStronglyMeasurable[𝓕 τ] (fun ω => M τ ω * N τ ω - C τ ω) μ :=
    aestronglyMeasurable_of_condExp_eq_self (h.condExp_mul τ τ le_rfl hτ)
  have h2 : AEStronglyMeasurable[𝓕 τ] (fun ω => M τ ω * N τ ω) μ :=
    (aestronglyMeasurable_of_condExp_eq_self (h.left.condExp τ τ le_rfl hτ)).mul
      (aestronglyMeasurable_of_condExp_eq_self (h.right.condExp τ τ le_rfl hτ))
  refine (h2.sub h1).congr (ae_of_all _ fun ω => ?_)
  simp

/-- `min u τ` maps `[0, T]` into `[0, T]`. -/
private lemma mm_mapsTo_min (τ : ℝ≥0) :
    Set.MapsTo (fun u : ℝ => min u τ) (Set.Icc 0 T) (Set.Icc 0 T) :=
  fun _ hu => ⟨le_min hu.1 τ.2, (min_le_left _ _).trans hu.2⟩

/-- **Stopping at a deterministic time**: `⟨M_{· ∧ τ}, N⟩ = ⟨M, N⟩_{· ∧ τ}`. -/
theorem HasCovariation.mmStop [IsFiniteMeasure μ] {M N C : ℝ → Ω → ℝ}
    (h : HasCovariation T 𝓕 M N C μ) (τ : ℝ≥0) :
    HasCovariation T 𝓕 (fun u => M (min u τ)) N (fun u => C (min u τ)) μ := by
  have hc : ∀ u : ℝ≥0, (min (u : ℝ) τ) = ((min u τ : ℝ≥0) : ℝ) := fun u => (NNReal.coe_min u τ).symm
  have hle : ∀ u : ℝ≥0, (u : ℝ) ≤ T → ((min u τ : ℝ≥0) : ℝ) ≤ T :=
    fun u hu => (NNReal.coe_le_coe.2 (min_le_left u τ)).trans hu
  refine ⟨⟨?_, fun t ht => ?_, fun s t hst ht => ?_⟩, h.right, fun t ht => ?_, ?_, ?_, ?_,
    fun s t hst ht => ?_⟩
  · filter_upwards [h.left.cont] with ω hω
    exact hω.comp ((continuous_id.min continuous_const).continuousOn) (mm_mapsTo_min τ)
  · simp only [hc]; exact h.left.memLp _ (hle t ht)
  · simp only [hc]
    rcases le_total s τ with hsτ | hτs
    · rw [min_eq_left hsτ]
      exact h.left.condExp s _ (le_min hst hsτ) (hle t ht)
    · rw [min_eq_right hτs, min_eq_right (hτs.trans hst)]
      have hτT : (τ : ℝ) ≤ T := (NNReal.coe_le_coe.2 (hτs.trans hst)).trans ht
      exact condExp_of_aestronglyMeasurable' (𝓕.le s)
        ((aestronglyMeasurable_of_condExp_eq_self (h.left.condExp τ τ le_rfl hτT)).mono
          (𝓕.mono hτs)) ((h.left.memLp τ hτT).integrable one_le_two)
  · simp only [hc]; exact h.integrable_cov _ (hle t ht)
  · filter_upwards [h.zero] with ω hω
    simpa [min_eq_left τ.2] using hω
  · filter_upwards [h.cont_cov] with ω hω
    exact hω.comp ((continuous_id.min continuous_const).continuousOn) (mm_mapsTo_min τ)
  · filter_upwards [h.bv] with ω hω
    exact ne_top_of_le_ne_top hω (eVariationOn.comp_le_of_monotoneOn (fun u => C u ω)
      (fun u : ℝ => min u τ) (fun _ _ _ _ hab => min_le_min_right _ hab) (mm_mapsTo_min τ))
  · simp only [hc]
    -- the key computation, for `τ ≤ v ≤ t`
    have key : ∀ v : ℝ≥0, τ ≤ v → v ≤ t →
        μ[fun ω => M τ ω * N t ω - C τ ω | 𝓕 v] =ᵐ[μ] fun ω => M τ ω * N v ω - C τ ω := by
      intro v hτv hvt
      have hτT : (τ : ℝ) ≤ T := (NNReal.coe_le_coe.2 (hτv.trans hvt)).trans ht
      have hMτ : AEStronglyMeasurable[𝓕 v] (M τ) μ :=
        (aestronglyMeasurable_of_condExp_eq_self (h.left.condExp τ τ le_rfl hτT)).mono
          (𝓕.mono hτv)
      have hint1 : Integrable (M τ * N t) μ :=
        (h.left.memLp τ hτT).integrable_mul (h.right.memLp t ht)
      have hint2 : Integrable (C τ) μ := h.integrable_cov τ hτT
      have e1 : (fun ω => M τ ω * N t ω - C τ ω) = M τ * N t - C τ := rfl
      rw [e1]
      refine (condExp_sub hint1 hint2 _).trans ?_
      have h1 := condExp_mul_of_aestronglyMeasurable_left hMτ hint1
        ((h.right.memLp t ht).integrable one_le_two)
      have h2 := h.right.condExp v t hvt ht
      have h3 := condExp_of_aestronglyMeasurable' (𝓕.le v)
        ((mm_aesm_cov h τ hτT).mono (𝓕.mono hτv)) hint2
      filter_upwards [h1, h2, h3] with ω e1 e2 e3
      simp only [Pi.sub_apply, Pi.mul_apply] at e1 ⊢
      rw [e1, e2, e3]
    rcases le_total t τ with htτ | hτt
    · rw [min_eq_left htτ, min_eq_left (hst.trans htτ)]
      exact h.condExp_mul s t hst ht
    · rw [min_eq_right hτt]
      rcases le_total s τ with hsτ | hτs
      · rw [min_eq_left hsτ]
        have hτT : (τ : ℝ) ≤ T := (NNReal.coe_le_coe.2 hτt).trans ht
        refine (condExp_condExp_of_le (𝓕.mono hsτ) (𝓕.le τ)).symm.trans ?_
        refine (condExp_congr_ae (key τ le_rfl hτt)).trans ?_
        exact h.condExp_mul s τ hsτ hτT
      · rw [min_eq_right hτs]
        exact key s hτs hst

/-- If a martingale `Y` vanishes up to time `σ`, and `a` is bounded and `𝓕_σ`-measurable, then
`a Y` is a martingale. -/
private lemma mm_condExp_mul_vanish [IsFiniteMeasure μ] {Y : ℝ → Ω → ℝ}
    (hY : ∀ v u : ℝ≥0, v ≤ u → (u : ℝ) ≤ T → μ[Y u | 𝓕 v] =ᵐ[μ] Y v)
    (hYi : ∀ u : ℝ≥0, (u : ℝ) ≤ T → Integrable (Y u) μ) (σ : ℝ≥0)
    (h0 : ∀ u : ℝ≥0, u ≤ σ → ∀ ω, Y u ω = 0) {a : Ω → ℝ} (ha : Measurable[𝓕 σ] a) {K : ℝ}
    (hK : ∀ ω, |a ω| ≤ K) (v u : ℝ≥0) (hvu : v ≤ u) (hu : (u : ℝ) ≤ T) :
    μ[fun ω => a ω * Y u ω | 𝓕 v] =ᵐ[μ] fun ω => a ω * Y v ω := by
  have case1 : ∀ v : ℝ≥0, σ ≤ v → v ≤ u →
      μ[fun ω => a ω * Y u ω | 𝓕 v] =ᵐ[μ] fun ω => a ω * Y v ω := by
    intro v hσv hvu
    have ham : StronglyMeasurable[𝓕 v] a := (ha.mono (𝓕.mono hσv) le_rfl).stronglyMeasurable
    have hint : Integrable (a * Y u) μ :=
      (hYi u hu).bdd_mul (ha.mono (𝓕.le σ) le_rfl).aestronglyMeasurable
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hK ω)
    exact (condExp_mul_of_stronglyMeasurable_left ham hint (hYi u hu)).trans
      ((hY v u hvu hu).mono fun ω hω => by simp only [Pi.mul_apply, hω])
  rcases le_total σ v with hσv | hvσ
  · exact case1 v hσv hvu
  have hv0 : (fun ω => a ω * Y v ω) = 0 := by funext ω; simp [h0 v hvσ ω]
  rw [hv0]
  rcases le_total u σ with huσ | hσu
  · have hu0 : (fun ω => a ω * Y u ω) = 0 := by funext ω; simp [h0 u huσ ω]
    rw [hu0, condExp_zero]
  · refine (condExp_condExp_of_le (𝓕.mono hvσ) (𝓕.le σ)).symm.trans ?_
    have hσ0 : (fun ω => a ω * Y σ ω) = (0 : Ω → ℝ) := by funext ω; simp [h0 σ le_rfl ω]
    refine (condExp_congr_ae ((case1 σ le_rfl hσu).trans (EventuallyEq.of_eq hσ0))).trans ?_
    rw [condExp_zero]

/-- **Multiplication by a bounded `𝓕_σ`-measurable factor**: if `D` and the covariation `E`
vanish up to time `σ`, then `⟨a D, N⟩ = a E`. -/
theorem HasCovariation.mmMulOfVanish [IsFiniteMeasure μ] {D N E : ℝ → Ω → ℝ}
    (h : HasCovariation T 𝓕 D N E μ) (σ : ℝ≥0) (hD : ∀ u : ℝ, u ≤ σ → ∀ ω, D u ω = 0)
    (hE : ∀ u : ℝ, u ≤ σ → ∀ ω, E u ω = 0) {a : Ω → ℝ} (ha : Measurable[𝓕 σ] a) {K : ℝ}
    (hK : ∀ ω, |a ω| ≤ K) :
    HasCovariation T 𝓕 (fun u ω => a ω * D u ω) N (fun u ω => a ω * E u ω) μ := by
  have ham : AEStronglyMeasurable a μ := (ha.mono (𝓕.le σ) le_rfl).aestronglyMeasurable
  have hbd : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ K := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hK ω
  refine ⟨⟨?_, fun t ht => ?_, fun s t hst ht => ?_⟩, h.right, fun t ht => ?_, ?_, ?_, ?_,
    fun s t hst ht => ?_⟩
  · filter_upwards [h.left.cont] with ω hω using continuousOn_const.mul hω
  · refine (h.left.memLp t ht).of_le_mul (c := K)
      (ham.mul (h.left.memLp t ht).aestronglyMeasurable) ?_
    filter_upwards [hbd] with ω hω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  · exact mm_condExp_mul_vanish h.left.condExp (fun u hu => (h.left.memLp u hu).integrable
      one_le_two) σ (fun u hu ω => hD u (NNReal.coe_le_coe.2 hu) ω) ha hK s t hst ht
  · exact (h.integrable_cov t ht).bdd_mul ham hbd
  · filter_upwards [h.zero] with ω hω; simp [hω]
  · filter_upwards [h.cont_cov] with ω hω using continuousOn_const.mul hω
  · filter_upwards [h.bv] with ω hω
    simpa using mmBoundedVariationOn_lincomb hω hω (a ω) 0
  · have e : ∀ u : ℝ≥0, (fun ω => a ω * D u ω * N u ω - a ω * E u ω) =
        fun ω => a ω * (D u ω * N u ω - E u ω) := fun u => by funext ω; ring
    rw [e, e]
    refine mm_condExp_mul_vanish (Y := fun u ω => D u ω * N u ω - E u ω) h.condExp_mul
      (fun u hu => ((h.left.memLp u hu).integrable_mul (h.right.memLp u hu)).sub
        (h.integrable_cov u hu)) σ (fun u hu ω => ?_) ha hK s t hst ht
    simp [hD u (NNReal.coe_le_coe.2 hu) ω, hE u (NNReal.coe_le_coe.2 hu) ω]

/-- **Covariation of an elementary integral**: for `s ≤ t` and `a` bounded and
`𝓕_s`-measurable, `⟨a (M_{· ∧ t} - M_{· ∧ s}), N⟩ = a (C_{· ∧ t} - C_{· ∧ s})` where
`C = ⟨M, N⟩`. -/
theorem HasCovariation.mmBlock [IsFiniteMeasure μ] {M N C : ℝ → Ω → ℝ}
    (h : HasCovariation T 𝓕 M N C μ) (s t : ℝ≥0) (hst : s ≤ t) {a : Ω → ℝ}
    (ha : Measurable[𝓕 s] a) {K : ℝ} (hK : ∀ ω, |a ω| ≤ K) :
    HasCovariation T 𝓕 (fun u ω => a ω * (M (min u t) ω - M (min u s) ω)) N
      (fun u ω => a ω * (C (min u t) ω - C (min u s) ω)) μ := by
  have h1 := (h.mmStop t).add_left ((h.mmStop s).const_mul_left (-1))
  have e1 : (fun u ω => M (min u t) ω + -1 * M (min u s) ω) =
      fun u ω => M (min u t) ω - M (min u s) ω := by funext u ω; ring
  have e2 : (fun u ω => C (min u t) ω + -1 * C (min u s) ω) =
      fun u ω => C (min u t) ω - C (min u s) ω := by funext u ω; ring
  rw [e1, e2] at h1
  have hv : ∀ u : ℝ, u ≤ s → min u t = u ∧ min u s = u := fun u hu =>
    ⟨min_eq_left (hu.trans (NNReal.coe_le_coe.2 hst)), min_eq_left hu⟩
  exact h1.mmMulOfVanish s (fun u hu ω => by simp [(hv u hu).1, (hv u hu).2])
    (fun u hu ω => by simp [(hv u hu).1, (hv u hu).2]) ha hK

end QSSEPtoKPZ
