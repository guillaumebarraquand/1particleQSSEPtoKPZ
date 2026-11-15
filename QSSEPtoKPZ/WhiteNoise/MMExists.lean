/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.MMIntegral
public import QSSEPtoKPZ.WhiteNoise.MMExistsDynkin

/-!
# Existence of martingale-measure integrals (task G8b)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G8b.
See `docs/stage4-design.md`, Sections 1.2 (f) and 3.3, and `docs/stage4-interfaces.md`.

Step 1 of the proof of Proposition 7.2: "since the measure `Z(s,x)² dℙ ds dx` is finite by
(7.1), simple functions are dense in `𝓛²_Z`". Indicators of predictable rectangles are
approximated by sets of the generating ring (`exists_measure_symmDiff_lt_of_generateFrom_isSetRing`,
for the finite measure `q dℙ dr dx`), and `𝟙_B(x)` by smooth bumps in `L²` of a finite measure on
`ℝ`; the limit process is obtained by Doob's maximal inequality (`IsCL2Mart.lintegral_iSup_sq_le`)
and has a continuous version.

Proof (task G8b), in four files: `MMExistsLimit.lean` (closure under energy limits, with the
limit process built as an almost sure uniform limit along a fast subsequence),
`MMExistsDense.lean` (closure properties, smooth bumps, dominated convergence),
`MMExistsDynkin.lean` (indicators of `𝒫 ⊗ 𝓑(ℝ)`-sets, Dynkin argument) and this file: the
fields `f` on `Ω × ℝ × ℝ` measurable for `𝒫 ⊗ 𝓑(ℝ)` pulled back by `(ω, r, x) ↦ ((r⁺, ω), x)`,
in `L²` of the finite measure `q dℙ dr dx` on `Ω × [0,T] × ℝ` (trimmed to that σ-algebra), all
have an integral (`MemLp.induction`: indicators by the Dynkin argument, sums, closedness in `L²`,
almost everywhere modifications); a predictable `h` of finite energy is such a field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Helpers

variable {μ : Measure Ω} {T : ℝ} {𝒢 : Filtration ℝ≥0 mΩ} {q : ℝ → ℝ → Ω → ℝ}
  {M : (ℝ → ℝ) → ℝ → Ω → ℝ}

/-! ### The pulled-back σ-algebra and the measure `q dℙ dr dx` -/

/-- The map `(ω, r, x) ↦ ((r⁺, ω), x)`. -/
private def mmExPredMap (p : Ω × ℝ × ℝ) : (ℝ≥0 × Ω) × ℝ := ((p.2.1.toNNReal, p.1), p.2.2)

/-- The map `((r, ω), x) ↦ (ω, r, x)`, a right inverse of `mmExPredMap`. -/
private def mmExIota (p : (ℝ≥0 × Ω) × ℝ) : Ω × ℝ × ℝ := (p.1.2, (p.1.1 : ℝ), p.2)

private lemma mmEx_predictable_le :
    𝒢.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact (measurableSet_singleton _).prod (𝒢.le _ _ hA)
  · exact measurableSet_Ioi.prod (𝒢.le _ _ hA)

private lemma measurable_mmExPredMap :
    Measurable[inferInstance, (𝒢.predictable).prod (borel ℝ)] (mmExPredMap (Ω := Ω)) := by
  have h : Measurable (mmExPredMap (Ω := Ω)) := by
    unfold mmExPredMap
    fun_prop
  refine h.mono le_rfl ?_
  exact sup_le_sup (MeasurableSpace.comap_mono mmEx_predictable_le)
    (MeasurableSpace.comap_mono BorelSpace.measurable_eq.ge)

/-- The σ-algebra `𝒫 ⊗ 𝓑(ℝ)` pulled back to `Ω × ℝ × ℝ` by `mmExPredMap`. -/
@[instance_reducible]
private def mmExSigma (𝒢 : Filtration ℝ≥0 mΩ) : MeasurableSpace (Ω × ℝ × ℝ) :=
  MeasurableSpace.comap mmExPredMap ((𝒢.predictable).prod (borel ℝ))

private lemma mmExSigma_le (𝒢 : Filtration ℝ≥0 mΩ) : mmExSigma 𝒢 ≤ (inferInstance : MeasurableSpace (Ω × ℝ × ℝ)) :=
  measurable_mmExPredMap.comap_le

private lemma measurable_mmExIota :
    Measurable[(𝒢.predictable).prod (borel ℝ), mmExSigma 𝒢] (mmExIota (Ω := Ω)) := by
  refine Measurable.of_comap_le ?_
  have e : mmExPredMap ∘ mmExIota = (id : (ℝ≥0 × Ω) × ℝ → (ℝ≥0 × Ω) × ℝ) := by
    funext p
    simp [mmExPredMap, mmExIota]
  rw [mmExSigma, MeasurableSpace.comap_comp, e, MeasurableSpace.comap_id]

/-- The field `(r, x, ω) ↦ g(ω, r, x)` of a function on `Ω × ℝ × ℝ`. -/
private def mmExFld (g : Ω × ℝ × ℝ → ℝ) (r x : ℝ) (ω : Ω) : ℝ := g (ω, r, x)

/-- Fields of pulled-back measurable functions are predictable. -/
private lemma mmEx_pred_fld {g : Ω × ℝ × ℝ → ℝ} (hg : Measurable[mmExSigma 𝒢] g) :
    MMPred 𝒢 (mmExFld g) :=
  hg.comp measurable_mmExIota

/-- The measure `q dℙ dr dx` on `Ω × [0,T] × ℝ`. -/
private def mmExNu (μ : Measure Ω) (T : ℝ) (q : ℝ → ℝ → Ω → ℝ) : Measure (Ω × ℝ × ℝ) :=
  (μ.prod (mmRho T)).withDensity fun p => ENNReal.ofReal (q (p.2.1.toNNReal : ℝ) p.2.2 p.1)

private lemma mmEx_ae_nonneg {μ : Measure Ω} [SFinite μ] :
    ∀ᵐ p ∂(μ.prod (mmRho T)), 0 ≤ p.2.1 := by
  rw [ae_iff]
  have e : {p : Ω × ℝ × ℝ | ¬ 0 ≤ p.2.1} = Set.univ ×ˢ (Set.Iio 0 ×ˢ Set.univ) := by
    ext p
    simp
  have e2 : Set.Iio (0 : ℝ) ∩ Set.Icc 0 T = ∅ := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_empty_iff_false, iff_false,
      not_and, not_le]
    intro h1 h2
    linarith
  rw [e, Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply measurableSet_Iio, e2]
  simp

/-- The energy of the field of a pulled-back measurable function is its squared `L²` norm. -/
private lemma mmEx_energy_fld [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {g : Ω × ℝ × ℝ → ℝ} (hg : Measurable[mmExSigma 𝒢] g) :
    mmEnergy μ T q (mmExFld g) =
      ∫⁻ p, ENNReal.ofReal (g p ^ 2) ∂((mmExNu μ T q).trim (mmExSigma_le 𝒢)) := by
  have hg' : Measurable g := hg.mono (mmExSigma_le 𝒢) le_rfl
  rw [lintegral_trim (mmExSigma_le 𝒢) (hg.pow_const 2).ennreal_ofReal]
  unfold mmEnergy
  rw [mmEx_lintegral3_eq (fun r x ω => ENNReal.ofReal (mmExFld g r x ω ^ 2 * q r x ω))
    (((mmEx_pred_fld hg).lift.pow_const 2).mul hq.lift).ennreal_ofReal, mmExNu,
    lintegral_withDensity_eq_lintegral_mul _ hq.lift.ennreal_ofReal
      (hg'.pow_const 2).ennreal_ofReal]
  refine lintegral_congr_ae ?_
  filter_upwards [mmEx_ae_nonneg] with p hp
  simp only [mmExFld, Pi.mul_apply, Real.coe_toNNReal _ hp, Prod.mk.eta]
  rw [mul_comm, ENNReal.ofReal_mul (hq0 _ _ _)]

/-- `∫ u² = ‖u‖₂²`. -/
private lemma mmEx_lintegral_sq {α : Type*} {m : MeasurableSpace α} {ν : Measure α} {u : α → ℝ}
    (hu : AEStronglyMeasurable u ν) :
    ∫⁻ p, ENNReal.ofReal (u p ^ 2) ∂ν = eLpNorm u 2 ν ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hu
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at this
  rw [this]
  exact lintegral_congr fun p => (StochIntAux.enorm_sq_eq _).symm

/-! ### Extension to all predictable integrands of finite energy -/

section Extension

variable [IsProbabilityMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
  (hq0 : ∀ r x ω, 0 ≤ q r x ω)
  (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
  (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
include hT hq hq0 hq1 hM

/-- Almost everywhere modifications of pulled-back measurable functions. -/
private lemma mmEx_congr_ae_fld {g₁ g₂ : Ω × ℝ × ℝ → ℝ}
    (h1 : MMExIntegrable T 𝒢 q M μ (mmExFld g₁)) (hg₁ : Measurable[mmExSigma 𝒢] g₁)
    (hg₂ : Measurable[mmExSigma 𝒢] g₂) (hae : g₁ =ᵐ[(mmExNu μ T q).trim (mmExSigma_le 𝒢)] g₂) :
    MMExIntegrable T 𝒢 q M μ (mmExFld g₂) := by
  refine h1.congr_energy hT hq hq0 hq1 hM (mmEx_pred_fld hg₂) ?_
  change mmEnergy μ T q (mmExFld (g₁ - g₂)) = 0
  rw [mmEx_energy_fld hq hq0 (hg₁.sub hg₂)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hae] with p hp
  simp [hp]

/-- Every function in `L²(q dℙ dr dx)`, for the pulled-back σ-algebra, has an integral. -/
private lemma mmEx_of_memLp {f : Ω × ℝ × ℝ → ℝ}
    (hf : MemLp f 2 ((mmExNu μ T q).trim (mmExSigma_le 𝒢))) :
    ∀ g, Measurable[mmExSigma 𝒢] g → g =ᵐ[(mmExNu μ T q).trim (mmExSigma_le 𝒢)] f →
      MMExIntegrable T 𝒢 q M μ (mmExFld g) := by
  refine @MemLp.induction _ _ (mmExSigma 𝒢) _ 2 ((mmExNu μ T q).trim (mmExSigma_le 𝒢)) _
    ENNReal.ofNat_ne_top (fun f => ∀ g, Measurable[mmExSigma 𝒢] g →
      g =ᵐ[(mmExNu μ T q).trim (mmExSigma_le 𝒢)] f → MMExIntegrable T 𝒢 q M μ (mmExFld g))
    ?_ ?_ ?_ ?_ f hf
  · -- indicators
    intro c s hs _ g hg hgs
    have hsm : Measurable[mmExSigma 𝒢] (s.indicator fun _ => c) := measurable_const.indicator hs
    refine mmEx_congr_ae_fld hT hq hq0 hq1 hM ?_ hsm hg hgs.symm
    obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    convert (mmEx_indicator hT hq hq0 hq1 hM hA).const_mul c using 1
    funext r x ω
    simp only [mmExFld, mmExInd]
    by_cases h : ((r.toNNReal, ω), x) ∈ A
    · rw [Set.indicator_of_mem (show (ω, r, x) ∈ mmExPredMap ⁻¹' A from h),
        Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem (show (ω, r, x) ∉ mmExPredMap ⁻¹' A from h),
        Set.indicator_of_notMem h, mul_zero]
  · -- sums
    intro f₁ f₂ _ hf₁ hf₂ ih₁ ih₂ g hg hgs
    have m₁ := hf₁.aestronglyMeasurable
    have m₂ := hf₂.aestronglyMeasurable
    have i₁ := ih₁ _ m₁.stronglyMeasurable_mk.measurable m₁.ae_eq_mk.symm
    have i₂ := ih₂ _ m₂.stronglyMeasurable_mk.measurable m₂.ae_eq_mk.symm
    refine mmEx_congr_ae_fld hT hq hq0 hq1 hM (g₁ := m₁.mk f₁ + m₂.mk f₂) (i₁.add i₂)
      (m₁.stronglyMeasurable_mk.measurable.add m₂.stronglyMeasurable_mk.measurable) hg ?_
    filter_upwards [m₁.ae_eq_mk, m₂.ae_eq_mk, hgs] with p e₁ e₂ e₃
    simp only [Pi.add_apply] at e₃ ⊢
    rw [e₃, e₁, e₂]
  · -- closedness in `L²`
    refine IsSeqClosed.isClosed fun F G hF hFG => ?_
    intro g hg hgG
    have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F G).1 hFG
    have hFm : ∀ k, Measurable[mmExSigma 𝒢] (F k) := fun k =>
      (Lp.stronglyMeasurable (F k)).measurable
    refine MMExIntegrable.of_tendsto hT hq hq0 hq1 hM (hs := fun k => mmExFld (F k))
      (fun k => hF k _ (hFm k) EventuallyEq.rfl) (mmEx_pred_fld hg) ?_
    have e : ∀ k, mmEnergy μ T q (fun r x ω => mmExFld (F k) r x ω - mmExFld g r x ω) =
        eLpNorm (⇑(F k) - ⇑G) 2 ((mmExNu μ T q).trim (mmExSigma_le 𝒢)) ^ 2 := by
      intro k
      change mmEnergy μ T q (mmExFld (⇑(F k) - g)) = _
      rw [mmEx_energy_fld hq hq0 ((hFm k).sub hg),
        mmEx_lintegral_sq ((Lp.aestronglyMeasurable (F k)).sub
          (hg.stronglyMeasurable.aestronglyMeasurable))]
      have hae : (⇑(F k) - g) =ᵐ[(mmExNu μ T q).trim (mmExSigma_le 𝒢)] (⇑(F k) - ⇑G) := by
        filter_upwards [hgG] with p hp
        simp [hp]
      rw [eLpNorm_congr_ae hae]
    simp only [e]
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
    simpa [Function.comp_def] using this
  · -- almost everywhere modifications
    intro f₁ f₂ hf _ ih g hg hgs
    exact ih g hg (hgs.trans hf.symm)

/-- **Existence for predictable integrands of finite energy** (`T ≥ 0`). -/
private lemma mmEx_main {h : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h)
    (hh2 : mmEnergy μ T q h < ⊤) : MMExIntegrable T 𝒢 q M μ h := by
  set f : Ω × ℝ × ℝ → ℝ := fun p => h (p.2.1.toNNReal : ℝ) p.2.2 p.1 with hfdef
  have hfm : Measurable[mmExSigma 𝒢] f := hh.comp (comap_measurable mmExPredMap)
  have hEf : mmEnergy μ T q (mmExFld f) = mmEnergy μ T q h :=
    mmEx_energy_congr fun r hr x ω => by
      show h ((r.toNNReal : ℝ)) x ω = h r x ω
      rw [Real.coe_toNNReal r hr.1]
  have hf2 : MemLp f 2 ((mmExNu μ T q).trim (mmExSigma_le 𝒢)) := by
    have hfa : AEStronglyMeasurable[mmExSigma 𝒢] f ((mmExNu μ T q).trim (mmExSigma_le 𝒢)) :=
      hfm.stronglyMeasurable.aestronglyMeasurable
    have h2 := mmEx_lintegral_sq hfa
    rw [← mmEx_energy_fld hq hq0 hfm, hEf] at h2
    refine memLp_iff.2 (lt_top_iff_ne_top.2 fun htop => ?_)
    rw [htop] at h2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.top_pow] at h2
    exact hh2.ne h2
  exact (mmEx_of_memLp hT hq hq0 hq1 hM hf2 f hfm EventuallyEq.rfl).congr hT hq hq0 hq1 hM hh
    fun r hr x ω => by
      show h ((r.toNNReal : ℝ)) x ω = h r x ω
      rw [Real.coe_toNNReal r hr.1.le]

end Extension

end Helpers

/-- **Existence of `h · M`** for predictable integrands with `𝔼 ∫_0^T ∫ h² q < ∞`, when the
intensity `q` is predictable, nonnegative and `𝔼 ∫_0^T ∫ q < ∞`. -/
theorem exists_isMMIntegral {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℝ}
    {𝒢 : Filtration ℝ≥0 mΩ} {q : ℝ → ℝ → Ω → ℝ} {M : (ℝ → ℝ) → ℝ → Ω → ℝ}
    (hq : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => q p.1.1 p.2 p.1.2)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {h : ℝ → ℝ → Ω → ℝ}
    (hh : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2)
    (hh2 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal (h r x ω ^ 2 * q r x ω)) ∂μ < ⊤) :
    ∃ X : ℝ → Ω → ℝ, IsMMIntegral T 𝒢 q M μ h X := by
  rcases lt_or_ge T 0 with hT | hT
  · -- empty horizon: a limit of zero blocks
    have hE : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.2 hT)
    obtain ⟨C, -, hC⟩ := isC13_bumpTestRaw 0
    refine ⟨fun _ _ => 0, IsMMIntegral.limit h _ (fun _ r x ω =>
      if ((0 : ℝ≥0) : ℝ) < r ∧ r ≤ ((0 : ℝ≥0) : ℝ) then (fun _ => (0 : ℝ)) ω * bumpTestRaw 0 x
        else 0)
      (fun _ r ω => (fun _ => (0 : ℝ)) ω * (M (bumpTestRaw 0) (min r ((0 : ℝ≥0) : ℝ)) ω -
        M (bumpTestRaw 0) (min r ((0 : ℝ≥0) : ℝ)) ω))
      (fun _ => IsMMIntegral.block 0 0 le_rfl _ _ C (hC T) measurable_const ⟨0, by simp⟩) hh
      (fun ω => continuousOn_const) (fun r hr => by rw [hE] at hr; exact absurd hr id) ?_ ?_⟩
    · simp [hE]
    · simp [hE]
  exact (mmEx_main hT hq hq0 hq1 hM hh hh2).2

end QSSEPtoKPZ
