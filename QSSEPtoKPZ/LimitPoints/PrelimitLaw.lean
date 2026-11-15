/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathFunctionals
public import QSSEPtoKPZ.LimitPoints.PathMart
public import QSSEPtoKPZ.TiltedField.Martingales
public import QSSEPtoKPZ.SecondMoments.TotalMass
public import QSSEPtoKPZ.Replacement.L2Bound
public import QSSEPtoKPZ.Replacement.ReplacementLemma
public import QSSEPtoKPZ.Tightness.Version
public import QSSEPtoKPZ.LimitPoints.PrelimitRepl
public import QSSEPtoKPZ.LimitPoints.PrelimitAux

/-!
# The estimates of Sections 3–6 under the law of `𝖹_n` (task Q1b)

INTERFACE FILE (task I0″ of Stage 4): the definition is complete; the statements below are
interfaces, proved by task Q1b. See `docs/stage4-design.md`, Sections 1.2 (b) and 3.5, risk R4,
and `docs/stage4-interfaces.md`.

`IsPathPrelimLaw T n P`: `P` is the law on `C([0,T], ℳ₊)` of an (almost everywhere measurable)
version of `(𝖹_n(t))_{t ∈ [0,T]}`, for some realization of the one-particle QSSEP on `ℤ` (on a
probability space in the universe `u`). The estimates (4.8), (6.2), Proposition 3.1 (2)–(3) and
Proposition 6.2, and the martingale property of `M_n^φ` with bracket `⟨M_n^φ⟩`, are restated
under `P`, on the canonical space with the augmented canonical filtration, as statements about
`P` only (so that they transfer to any random path with law `P`).

**Uniformity.** The constants must not depend on the realization: in Proposition 7.1 the
realizations change with `n`. The frozen `prop_6_2` fixes the realization before choosing
`ε₀` and `N`; its proof (constant `Kρ` of the private `prop62_main`, from `lemma_6_4`, depending
only on `ρ`) is uniform, and task Q1b restates it uniformly (`pathPrelim_replacement`), by
redoing the final step of `prop_6_2` from a public copy of `prop62_main` (`PrelimitRepl.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- `P` is the law of an almost everywhere measurable version of `(𝖹_n(t))_{t ∈ [0,T]}` for a
realization of the one-particle QSSEP on `ℤ` on a probability space in the universe `u`. -/
def IsPathPrelimLaw (T n : ℝ) (P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ))
    (Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
    IsProbabilityMeasure μ ∧ IsBrownianFamily 𝓕 B μ ∧ IsWaveFunction ⊤ 𝓕 B ψ μ ∧
    AEMeasurable Zv μ ∧
    (∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t) ∧
    μ.map Zv = P

variable {T n : ℝ} {P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}

/-- **A measurable adapted version.** A prelimit law is the law of a measurable version `Zv` of
`𝖹_n` on `[0,T]` whose test integrals are adapted to `𝓕ⁿ ∨ σ(null sets)` (that of
`exists_tiltedPath_version`, which is almost surely equal to the given one). -/
private lemma IsPathPrelimLaw.prelimVersion (hP : IsPathPrelimLaw.{u} T n P) (hn : 1 ≤ n) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ))
      (Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      IsProbabilityMeasure μ ∧ IsBrownianFamily 𝓕 B μ ∧ IsWaveFunction ⊤ 𝓕 B ψ μ ∧
      Measurable Zv ∧
      (∀ (t : Set.Icc (0 : ℝ) T) (j : ℕ), Measurable[nullAug μ (filtN n 𝓕) (t : ℝ).toNNReal]
        fun ω => ∫ x, bumpTest j x ∂(Zv ω t : Measure ℝ)) ∧
      (∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t) ∧
      μ.map Zv = P := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, -, hZv, hmap⟩ := hP
  obtain ⟨Zv', hm', ha', he'⟩ := exists_tiltedPath_version hB hψ hn T
  refine ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv', hμ, hB, hψ, hm', ha', he', ?_⟩
  rw [← hmap]
  refine Measure.map_congr ?_
  filter_upwards [hZv, he'] with ω h1 h2
  exact ContinuousMap.ext fun t => FiniteMeasure.toMeasure_injective ((h2 t).trans (h1 t).symm)

/-- On a version, the path functionals at `t ∈ [0,T]` are those of Stage 2. -/
private lemma prelim_version_mem {Ω : Type*} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hγ : ∀ t : Set.Icc (0 : ℝ) T, (γ t : Measure ℝ) = tiltedMeasure n ψ ω t) :
    ∀ t (ht : t ∈ Set.Icc 0 T), (γ ⟨t, ht⟩ : Measure ℝ) = tiltedMeasure n ψ ω t :=
  fun t ht => hγ ⟨t, ht⟩

/-- `pathAt γ t = 𝖹_n(t)` on a version, for `t ∈ [0,T]`. -/
private lemma prelim_pathAt_eq {Ω : Type*} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω}
    {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hγ : ∀ t : Set.Icc (0 : ℝ) T, (γ t : Measure ℝ) = tiltedMeasure n ψ ω t) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : (pathAt γ t : Measure ℝ) = tiltedMeasure n ψ ω t := by
  rw [pathAt_of_mem γ ht]; exact hγ ⟨t, ht⟩

/-- `ℰ_n(t;1) ≥ 0`. -/
private lemma prelimLaw_EN_one_nonneg {Ω : Type*} {n : ℝ} (hn : 0 ≤ n)
    (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) : 0 ≤ EN n ψ ω t fun _ => 1 :=
  mul_nonneg (Real.rpow_nonneg hn _) (tsum_nonneg fun x => by
    simp only [mul_one]; exact mul_nonneg (replZN_nonneg _ _ _ _ _) (replZN_nonneg _ _ _ _ _))

/-- A prelimit law is a probability measure. -/
theorem IsPathPrelimLaw.isProbabilityMeasure (hP : IsPathPrelimLaw.{u} T n P) :
    IsProbabilityMeasure P := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, -, -, -, -, rfl⟩ := hP
  infer_instance

/-- `𝖹_n(0) = δ₀` (Proposition 7.1 (1)): almost surely under `P`, `γ(0) = δ₀`. -/
theorem IsPathPrelimLaw.ae_dirac (hP : IsPathPrelimLaw.{u} T n P) (hn : 1 ≤ n) (hT : 0 ≤ T) :
    ∀ᵐ γ ∂P, (pathAt γ 0 : Measure ℝ) = Measure.dirac 0 := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, hZm, -, hZv, rfl⟩ := hP.prelimVersion hn
  have hS : IsClosed {ν : FiniteMeasure ℝ | (ν : Measure ℝ) = Measure.dirac 0} := by
    have e : {ν : FiniteMeasure ℝ | (ν : Measure ℝ) = Measure.dirac 0} =
        {(⟨Measure.dirac 0, inferInstance⟩ : FiniteMeasure ℝ)} := by
      ext ν
      exact ⟨fun h => FiniteMeasure.toMeasure_injective h, fun h => by rw [h]; rfl⟩
    rw [e]
    exact isClosed_singleton
  have hE : MeasurableSet {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) |
      (pathAt γ 0 : Measure ℝ) = Measure.dirac 0} :=
    (hS.preimage (continuous_pathAt_prod.comp
      (continuous_id.prodMk continuous_const))).measurableSet
  rw [ae_map_iff hZm.aemeasurable hE]
  filter_upwards [hZv, hψ.ae_init] with ω h1 h2
  show (pathAt (Zv ω) 0 : Measure ℝ) = Measure.dirac 0
  rw [prelim_pathAt_eq h1 ⟨le_rfl, hT⟩]
  ext s hs
  rw [tiltedMeasure, Measure.sum_apply _ hs, tsum_eq_single 0]
  · simp [zN, density, h2, waveInit_apply, rescaledPosition]
  · intro x hx
    simp [zN, density, h2, waveInit_apply, hx]

/-- Proposition 3.1 under `P`: `M_n^φ` is a continuous square-integrable martingale for the
augmented canonical filtration, with bracket `⟨M_n^φ⟩ = QNpath`, (3.14)–(3.15). -/
theorem IsPathPrelimLaw.hasBracket (hP : IsPathPrelimLaw.{u} T n P) (hn : 1 ≤ n) (hT : 0 < T)
    {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    HasBracket T (nullAug P (pathFiltrationCan T)) (MNpath n φ φt) (QNpath n φ) P := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, hZm, ha, hZv, rfl⟩ := hP.prelimVersion hn
  obtain ⟨h31, hBr, -, -⟩ := prop_3_1 hB hψ hn hT hφ
  -- the bracket on `Ω`, for the path functionals of the version
  have h1 : HasBracket T (nullAug μ (filtN n 𝓕)) (fun t ω => MNpath n φ φt t (Zv ω))
      (fun t ω => QNpath n φ t (Zv ω)) μ := by
    refine (hasBracket_nullAug_iff.2 hBr).congr hT.le ?_ ?_
    · filter_upwards [h31, hZv] with ω h h' t ht
      exact ((MNpath_QNpath_eq hn hφ (prelim_version_mem h') h.1 ht).1).symm
    · filter_upwards [h31, hZv] with ω h h' t ht
      exact ((MNpath_QNpath_eq hn hφ (prelim_version_mem h') h.1 ht).2).symm
  -- adaptedness of the path functionals to the canonical filtration (stopped paths)
  have hadM : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable[pathFiltrationCan T t] (MNpath n φ φt t) := by
    intro t ht
    have e : MNpath n φ φt (t : ℝ) = MNpath n φ φt t ∘ prelimStop (T := T) t := by
      funext γ
      simp only [Function.comp_apply, MNpath]
      rw [pathAt_prelimStop (NNReal.coe_nonneg t) le_rfl]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
      simp only [pathAt_prelimStop (NNReal.coe_nonneg t) hs.2]
    rw [e]
    exact (measurable_MNpath hn hφ ⟨(NNReal.coe_nonneg t), ht⟩).comp (measurable_prelimStop t)
  have hadQ : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable[pathFiltrationCan T t] (QNpath n φ t) := by
    intro t ht
    have e : QNpath n φ (t : ℝ) = QNpath n φ t ∘ prelimStop (T := T) t := by
      funext γ
      simp only [Function.comp_apply, QNpath]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
      simp only [QNdensPath, atomPath, pathAt_prelimStop (NNReal.coe_nonneg t) hs.2]
    rw [e]
    exact (measurable_QNpath hn hφ ⟨(NNReal.coe_nonneg t), ht⟩).comp (measurable_prelimStop t)
  -- the natural filtration of the version is smaller than `𝓕ⁿ ∨ σ(null sets)`
  have hle : ∀ t, pathFiltration Zv t ≤ nullAug μ (filtN n 𝓕) t := fun t => by
    rw [pathFiltration_eq_comap hZm]
    have hinf : pathFiltrationCan T t ≤ ⨆ s : Set.Icc (0 : ℝ) T, ⨆ (_ : (s : ℝ) ≤ t),
        (borel (FiniteMeasure ℝ)).comap fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ s :=
      inf_le_left
    refine (MeasurableSpace.comap_mono hinf).trans ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun s => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun hs => ?_
    rw [MeasurableSpace.comap_comp]
    refine measurable_iff_comap_le.1 ?_
    refine (@measurable_finiteMeasure_iff_tightEmb Ω (nullAug μ (filtN n 𝓕) t) _).2 fun j => ?_
    exact (ha s j).mono ((nullAug μ (filtN n 𝓕)).mono (Real.toNNReal_le_iff_le_coe.2 hs)) le_rfl
  have hcomap : ∀ t : ℝ≥0, ∀ {g : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ},
      Measurable[pathFiltrationCan T t] g →
        Measurable[nullAug μ (pathFiltration Zv) t] fun ω => g (Zv ω) := by
    intro t g hg
    refine Measurable.mono ?_ (le_nullAug μ _ t) le_rfl
    rw [pathFiltration_eq_comap hZm]
    exact hg.comp (comap_measurable Zv)
  have h2 : HasBracket T (nullAug μ (pathFiltration Zv)) (fun t ω => MNpath n φ φt t (Zv ω))
      (fun t ω => QNpath n φ t (Zv ω)) μ :=
    prelimAux_hasBracket_of_le h1 (fun t => sup_le (hle t) (nullSets_le_nullAug t))
      (fun t ht => hcomap t (hadM t ht)) (fun t ht => hcomap t (hadQ t ht))
  exact (hasBracket_map_iff hZm (fun t ht => measurable_MNpath hn hφ ht)
    (fun t ht => measurable_QNpath hn hφ ht) (continuousOn_MNpath hn hφ)
    (fun γ => (continuousOn_monotoneOn_QNpath hn hφ γ).1)
    (fun γ => (continuousOn_monotoneOn_QNpath hn hφ γ).2)).1 h2

/-- Proposition 3.1 (2)–(3) under `P`, with the almost sure integrability of `s ↦ ℰ_n(s;φ_s)`
and `s ↦ ℰ_n(s)` on `[0,T]`:
`⟨M_n^φ⟩_t - ⟨M_n^φ⟩_s ≤ 2 C² a_n ∫_s^t ℰ_n(r) dr` and
`|⟨M_n^φ⟩_t - a_n ∫_0^t ℰ_n(s;φ_s) ds| ≤ 5 n^{-1/4} C² ∫_0^t ℰ_n(s) ds`. -/
theorem IsPathPrelimLaw.prop_3_1_path (hP : IsPathPrelimLaw.{u} T n P) (hn : 1 ≤ n)
    (hT : 0 < T) {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    ∀ᵐ γ ∂P, IntervalIntegrable (fun s => ENpath n γ s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => ENpath n γ s fun _ => 1) volume 0 T ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        QNpath n φ t γ - QNpath n φ s γ ≤
          2 * C ^ 2 * (aN n * ∫ r in s..t, ENpath n γ r fun _ => 1)) ∧
      ∀ t ∈ Set.Icc 0 T,
        |QNpath n φ t γ - aN n * ∫ s in (0 : ℝ)..t, ENpath n γ s (φ s)| ≤
          5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..t, ENpath n γ s fun _ => 1 := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, hZm, -, hZv, rfl⟩ := hP.prelimVersion hn
  have hn0 : 0 < n := by linarith
  have hT0 := hT.le
  have hf1m : Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      ENpath n p.1 p.2 (prelimExt hT0 φ p.2) :=
    prelimMeas_measurable_ENpath n fun x => ((prelimExt_continuous hT0 hφ).comp
      (continuous_id.prodMk (by unfold rescaledPosition; fun_prop :
        Continuous fun s : ℝ => rescaledPosition n s x))).measurable
  have hf2m : Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      ENpath n p.1 p.2 fun _ => 1 :=
    prelimMeas_measurable_ENpath n (G := fun _ _ => 1) fun x => measurable_const
  have hf1e : ∀ γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), ∀ s ∈ Set.Icc 0 T,
      ENpath n γ s (φ s) = ENpath n γ s (prelimExt hT0 φ s) := fun γ s hs => by
    rw [prelimExt_of_mem hT0 φ hs]
  -- the property restricted to rational times is an event
  have hG : MeasurableSet {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) |
      IntervalIntegrable (fun s => ENpath n γ s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => ENpath n γ s fun _ => 1) volume 0 T ∧
      (∀ q r : ℚ, (0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ r ∧ (r : ℝ) ≤ T) →
        QNpath n φ r γ - QNpath n φ q γ ≤
          2 * C ^ 2 * (aN n * ∫ x in (q : ℝ)..r, ENpath n γ x fun _ => 1)) ∧
      ∀ q : ℚ, (q : ℝ) ∈ Set.Icc 0 T →
        |QNpath n φ q γ - aN n * ∫ s in (0 : ℝ)..q, ENpath n γ s (φ s)| ≤
          5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..q, ENpath n γ s fun _ => 1} := by
    have hI1 : ∀ q : ℝ, q ∈ Set.Icc 0 T → Measurable fun γ : C(Set.Icc (0 : ℝ) T,
        FiniteMeasure ℝ) => ∫ s in (0 : ℝ)..q, ENpath n γ s (φ s) := fun q hq =>
      prelimAux_measurable_intervalIntegral hf1m hq.1 fun γ s hs =>
        hf1e γ s ⟨hs.1.le, hs.2.trans hq.2⟩
    have hI2 : ∀ q r : ℝ, q ≤ r → Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
        ∫ s in q..r, ENpath n γ s fun _ => 1 := fun q r hqr =>
      prelimAux_measurable_intervalIntegral hf2m hqr fun _ _ _ => rfl
    simp only [Set.ofPred_and]
    refine (prelimAux_measurableSet_intervalIntegrable hf1m hT0 fun γ s hs =>
      hf1e γ s ⟨hs.1.le, hs.2⟩).inter ((prelimAux_measurableSet_intervalIntegrable hf2m hT0
        fun _ _ _ => rfl).inter (MeasurableSet.inter ?_ ?_))
    · simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun r =>
        MeasurableSet.iInter fun h => ?_
      exact measurableSet_le ((measurable_QNpath hn hφ ⟨h.1.trans h.2.1, h.2.2⟩).sub
        (measurable_QNpath hn hφ ⟨h.1, h.2.1.trans h.2.2⟩))
        (measurable_const.mul (measurable_const.mul (hI2 _ _ h.2.1)))
    · simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun h => ?_
      exact measurableSet_le (continuous_abs.measurable.comp ((measurable_QNpath hn hφ h).sub
        (measurable_const.mul (hI1 _ h)))) (measurable_const.mul (hI2 _ _ h.1))
  -- the property holds for the version
  have hgood : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => ENpath n (Zv ω) s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => ENpath n (Zv ω) s fun _ => 1) volume 0 T ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        QNpath n φ t (Zv ω) - QNpath n φ s (Zv ω) ≤
          2 * C ^ 2 * (aN n * ∫ r in s..t, ENpath n (Zv ω) r fun _ => 1)) ∧
      ∀ t ∈ Set.Icc 0 T,
        |QNpath n φ t (Zv ω) - aN n * ∫ s in (0 : ℝ)..t, ENpath n (Zv ω) s (φ s)| ≤
          5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..t, ENpath n (Zv ω) s fun _ => 1 := by
    obtain ⟨h31, -, hc, hd⟩ := prop_3_1 hB hψ hn hT hφ
    filter_upwards [h31, hc, hd, hZv] with ω ha hc hd hv
    have hE : ∀ s ∈ Set.Icc 0 T, ∀ g, ENpath n (Zv ω) s g = EN n ψ ω s g := fun s hs g =>
      (WNpath_ENpath_eq hn0 (prelim_version_mem hv) ha.1 hs).2 g
    have hQ : ∀ s ∈ Set.Icc 0 T, QNpath n φ s (Zv ω) = QN n ψ φ s ω := fun s hs =>
      (MNpath_QNpath_eq hn hφ (prelim_version_mem hv) ha.1 hs).2
    have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT0⟩
    have hTT : T ∈ Set.Icc 0 T := ⟨hT0, le_rfl⟩
    refine ⟨prelimAux_intervalIntegrable_congr ha.2.2.2.1 fun s hs =>
        (hE s (Set.uIcc_subset_Icc h0T hTT hs) _).symm,
      prelimAux_intervalIntegrable_congr ha.2.2.2.2 fun s hs =>
        (hE s (Set.uIcc_subset_Icc h0T hTT hs) _).symm, ?_, ?_⟩
    · intro s t hs hst htT
      have hsT : s ∈ Set.Icc 0 T := ⟨hs, hst.trans htT⟩
      have htT' : t ∈ Set.Icc 0 T := ⟨hs.trans hst, htT⟩
      rw [hQ t htT', hQ s hsT, intervalIntegral.integral_congr fun r hr =>
        hE r (Set.uIcc_subset_Icc hsT htT' hr) _]
      exact hc s t hs hst htT
    · intro t ht
      rw [hQ t ht, intervalIntegral.integral_congr fun r hr =>
          hE r (Set.uIcc_subset_Icc h0T ht hr) _,
        intervalIntegral.integral_congr fun r hr => hE r (Set.uIcc_subset_Icc h0T ht hr) _]
      exact hd t ht
  refine ((ae_map_iff hZm.aemeasurable hG).2 (hgood.mono fun ω h => ⟨h.1, h.2.1,
    fun q r hqr => h.2.2.1 q r hqr.1 hqr.2.1 hqr.2.2, fun q hq => h.2.2.2 q hq⟩)).mono ?_
  -- from rational times to all times, by continuity
  rintro γ ⟨ha, hb, hc, hd⟩
  have hsub : ∀ t ∈ Set.Icc 0 T, Set.uIcc 0 t ⊆ Set.uIcc 0 T := fun t ht =>
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.uIcc_of_le hT0]; exact ht)
  have hcont : ∀ {g : ℝ → ℝ}, IntervalIntegrable g volume 0 T →
      ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, g r) (Set.Icc 0 T) := fun hg => by
    have := intervalIntegral.continuousOn_primitive_interval' hg Set.left_mem_uIcc
    rwa [Set.uIcc_of_le hT0] at this
  have hQc := (continuousOn_monotoneOn_QNpath hn hφ γ).1
  refine ⟨ha, hb, ?_, ?_⟩
  · have hmono := prelimAux_monotoneOn_of_rat (T := T)
      (g := fun t => 2 * C ^ 2 * (aN n * ∫ r in (0 : ℝ)..t, ENpath n γ r fun _ => 1) -
        QNpath n φ t γ)
      ((continuousOn_const.mul (continuousOn_const.mul (hcont hb))).sub hQc)
      (fun q r hq hqr hr => by
        have h := hc q r ⟨hq, hqr, hr⟩
        have e := intervalIntegral.integral_interval_sub_left
          (hb.mono_set (hsub r ⟨hq.trans hqr, hr⟩)) (hb.mono_set (hsub q ⟨hq, hqr.trans hr⟩))
        have e' : 2 * C ^ 2 * (aN n * ∫ x in (0 : ℝ)..r, ENpath n γ x fun _ => 1) -
            2 * C ^ 2 * (aN n * ∫ x in (0 : ℝ)..q, ENpath n γ x fun _ => 1) =
            2 * C ^ 2 * (aN n * ∫ x in (q : ℝ)..r, ENpath n γ x fun _ => 1) := by
          rw [← e]; ring
        show _ ≤ _
        linarith)
    intro s t hs hst htT
    have h := hmono ⟨hs, hst.trans htT⟩ ⟨hs.trans hst, htT⟩ hst
    have e := intervalIntegral.integral_interval_sub_left
      (hb.mono_set (hsub t ⟨hs.trans hst, htT⟩)) (hb.mono_set (hsub s ⟨hs, hst.trans htT⟩))
    have e' : 2 * C ^ 2 * (aN n * ∫ x in (0 : ℝ)..t, ENpath n γ x fun _ => 1) -
        2 * C ^ 2 * (aN n * ∫ x in (0 : ℝ)..s, ENpath n γ x fun _ => 1) =
        2 * C ^ 2 * (aN n * ∫ x in s..t, ENpath n γ x fun _ => 1) := by
      rw [← e]; ring
    linarith
  · intro t ht
    have := prelimAux_le_of_rat hT
      (g := fun t => |QNpath n φ t γ - aN n * ∫ s in (0 : ℝ)..t, ENpath n γ s (φ s)| -
        5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..t, ENpath n γ s fun _ => 1)
      ((hQc.sub (continuousOn_const.mul (hcont ha))).abs.sub
        (continuousOn_const.mul (hcont hb)))
      (fun q hq => by
        have h := hd q ⟨hq.1.le, hq.2.le⟩
        show _ ≤ _
        linarith) t ht
    linarith

/-- (4.8) under `P`: `𝔼[sup_{s ≤ T} 𝒲_n(s)²] ≤ 2^{3+16T}` and `𝔼 ∫_0^T ℰ_n(s) ds ≤ 2^{1+16T}`
(the functionals being measurable). -/
theorem IsPathPrelimLaw.prop_4_3_path (hP : IsPathPrelimLaw.{u} T n P) (hn : 1 ≤ n) (hT : 0 ≤ T) :
    Measurable (fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
        ⨆ s ∈ Set.Icc 0 T, ENNReal.ofReal (WNpath s γ ^ 2)) ∧
      ∫⁻ γ, ⨆ s ∈ Set.Icc 0 T, ENNReal.ofReal (WNpath s γ ^ 2) ∂P ≤
        ENNReal.ofReal (2 ^ (3 + 16 * T)) ∧
      Measurable (fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
        ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1)) ∧
      ∫⁻ γ, ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) ∂P ≤
        ENNReal.ofReal (2 ^ (1 + 16 * T)) := by
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, hZm, -, hZv, rfl⟩ := hP.prelimVersion hn
  have hn0 : 0 < n := by linarith
  have hWc : ∀ s, Continuous fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      ENNReal.ofReal (WNpath s γ ^ 2) := fun s =>
    ENNReal.continuous_ofReal.comp (((continuous_pairFM continuous_const
      ⟨1, fun _ => by simp⟩).comp
      (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))).pow 2)
  have hm1 : Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      ⨆ s ∈ Set.Icc 0 T, ENNReal.ofReal (WNpath s γ ^ 2) :=
    (lowerSemicontinuous_biSup fun s _ => (hWc s).lowerSemicontinuous).measurable
  have hf2m : Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      ENpath n p.1 p.2 fun _ => 1 :=
    prelimMeas_measurable_ENpath n (G := fun _ _ => 1) fun x => measurable_const
  have hm2 : Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) :=
    ENNReal.measurable_ofReal.comp
      (prelimAux_measurable_intervalIntegral hf2m hT fun _ _ _ => rfl)
  obtain ⟨h0, -, hb1, hEint, hb2⟩ := prop_4_3_bounds hB hψ hn hT
  refine ⟨hm1, ?_, hm2, ?_⟩
  · rw [lintegral_map hm1 hZm]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hb1
    filter_upwards [h0, hZv] with ω ha hv
    refine iSup_congr fun s => iSup_congr fun hs => ?_
    rw [(WNpath_ENpath_eq hn0 (prelim_version_mem hv) ha.1 hs).1]
  · rw [lintegral_map hm2 hZm]
    have e : ∀ᵐ ω ∂μ, ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath n (Zv ω) s fun _ => 1) =
        ENNReal.ofReal (∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) := by
      filter_upwards [h0, hZv] with ω ha hv
      rw [intervalIntegral.integral_congr fun s hs => (WNpath_ENpath_eq hn0
        (prelim_version_mem hv) ha.1 (by rwa [Set.uIcc_of_le hT] at hs)).2 _]
    rw [lintegral_congr_ae e, ← ofReal_integral_eq_lintegral_ofReal hEint
      (ae_of_all _ fun ω => intervalIntegral.integral_nonneg hT fun s _ =>
        prelimLaw_EN_one_nonneg hn0.le ψ ω s)]
    exact ENNReal.ofReal_le_ofReal hb2

/-- (6.2) under `P`, with a constant depending only on `ρ`. -/
theorem pathPrelim_eq_6_2 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ {T n : ℝ} {P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)},
      IsPathPrelimLaw.{u} T n P → 1 ≤ n → 0 < T → ∀ m : ℕ, 1 ≤ m →
        Measurable (fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => ENNReal.ofReal
          (smoothedNormSq (pathAt p.1 p.2 : Measure ℝ) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ)))) ∧
        ∫⁻ γ, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal
          (smoothedNormSq (pathAt γ t : Measure ℝ) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ)))) ∂P ≤
        ENNReal.ofReal (C * 2 ^ (16 * T)) := by
  obtain ⟨C, hC⟩ := prop_6_1.{u} hρ
  refine ⟨C, fun {T n P} hP hn hT m hm => ?_⟩
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, hZm, -, hZv, rfl⟩ := hP.prelimVersion hn
  have hε : (0 : ℝ) < m * n ^ (-1 / 2 : ℝ) :=
    mul_pos (Nat.cast_pos.2 (by omega)) (Real.rpow_pos_of_pos (by linarith) _)
  have hmeas : Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => ENNReal.ofReal
      (smoothedNormSq (pathAt p.1 p.2 : Measure ℝ) (fun _ => 1) ρ (m * n ^ (-1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (prelimMeas_continuous_smoothedNormSq (T := T) hρ
      (G := fun _ _ => (1 : ℝ)) continuous_const (c := 1) (fun _ _ => by simp) hε).measurable
  refine ⟨hmeas, ?_⟩
  obtain ⟨-, -, -, hb⟩ := hC hB hψ hn hm hT
  rw [lintegral_map (hmeas.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))) hZm]
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hb
  filter_upwards [hZv] with ω hv
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  simp only [prelim_pathAt_eq hv ht]

set_option linter.unusedVariables false in
/-- The event of Proposition 6.2 on the path space is measurable (supremum over rational
times). -/
theorem measurableSet_pathReplEvent {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {C : ℝ}
    {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) (n ε η : ℝ) (hn : 1 ≤ n) (hε : 0 < ε) :
    MeasurableSet {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) | ∃ t ∈ Set.Icc 0 T,
      η < |∫ s in (0 : ℝ)..t,
        (ENpath n γ s (φ s) - smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε)|} := by
  by_cases hT0 : 0 ≤ T
  swap
  · convert MeasurableSet.empty
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨t, ht, -⟩
    exact hT0 (ht.1.trans ht.2)
  by_cases hη : η < 0
  · convert MeasurableSet.univ
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨0, ⟨le_rfl, hT0⟩, hη.trans_le (abs_nonneg _)⟩
  have hη0 : 0 ≤ η := not_lt.1 hη
  set F : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ → ℝ := fun γ t => ∫ s in (0 : ℝ)..t,
    (ENpath n γ s (φ s) - smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε) with hF
  show MeasurableSet {γ | ∃ t ∈ Set.Icc 0 T, η < |F γ t|}
  have hfm : Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      ENpath n p.1 p.2 (prelimExt hT0 φ p.2) -
        smoothedNormSq (pathAt p.1 p.2 : Measure ℝ) (prelimExt hT0 φ p.2) ρ ε :=
    (prelimMeas_measurable_ENpath n fun x => ((prelimExt_continuous hT0 hφ).comp
      (continuous_id.prodMk (by unfold rescaledPosition; fun_prop :
        Continuous fun s : ℝ => rescaledPosition n s x))).measurable).sub
      (prelimMeas_continuous_smoothedNormSq hρ (prelimExt_continuous hT0 hφ)
        (prelimExt_abs_le hT0 hφ) hε).measurable
  have hFm : ∀ q : ℝ, q ∈ Set.Icc 0 T → Measurable fun γ => F γ q := fun q hq =>
    prelimAux_measurable_intervalIntegral hfm hq.1 fun γ s hs => by
      simp only [prelimExt_of_mem hT0 φ ⟨hs.1.le, hs.2.trans hq.2⟩]
  have e : {γ | ∃ t ∈ Set.Icc 0 T, η < |F γ t|} =
      ⋃ q : ℚ, {γ | (q : ℝ) ∈ Set.Icc 0 T ∧ η < |F γ q|} := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, hlt⟩
      have hF0 : F γ t ≠ 0 := fun h => by rw [h, abs_zero] at hlt; linarith
      have hint : IntervalIntegrable (fun s => ENpath n γ s (φ s) -
          smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε) volume 0 t := by
        by_contra hni
        exact hF0 (intervalIntegral.integral_undef hni)
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 fun h => hF0 (by
        simp only [hF, ← h, intervalIntegral.integral_same])
      have hc := intervalIntegral.continuousOn_primitive_interval' hint Set.left_mem_uIcc
      rw [Set.uIcc_of_le ht.1] at hc
      have hev : ∀ᶠ u in 𝓝[Set.Icc 0 t] t, η < |F γ u| :=
        ((continuous_abs.continuousAt).comp_continuousWithinAt
          (hc t ⟨ht.1, le_rfl⟩)).eventually (lt_mem_nhds hlt)
      have hcl := prelimAux_Icc_subset_closure ht0 ⟨ht.1, le_rfl⟩
      rw [mem_closure_iff_nhdsWithin_neBot] at hcl
      have hev' : ∀ᶠ u in 𝓝[Set.Ioo 0 t ∩ Set.range ((↑) : ℚ → ℝ)] t,
          η < |F γ u| ∧ u ∈ Set.Ioo 0 t ∩ Set.range ((↑) : ℚ → ℝ) :=
        (hev.filter_mono (nhdsWithin_mono t fun u hu => Set.Ioo_subset_Icc_self hu.1)).and
          self_mem_nhdsWithin
      have := hcl
      obtain ⟨u, hu1, hu2, q, rfl⟩ := hev'.exists
      exact ⟨q, ⟨hu2.1.le, hu2.2.le.trans ht.2⟩, hu1⟩
    · rintro ⟨q, hq, hlt⟩
      exact ⟨q, hq, hlt⟩
  rw [e]
  refine MeasurableSet.iUnion fun q => ?_
  by_cases hq : (q : ℝ) ∈ Set.Icc 0 T
  · simp only [hq, true_and]
    exact measurableSet_lt measurable_const (continuous_abs.measurable.comp (hFm q hq))
  · simp [hq]

/-- **Proposition 6.2 under the prelimit laws, uniformly in the realization.** -/
theorem pathPrelim_replacement {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T C : ℝ} (hT : 0 < T)
    {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    ∀ η δ : ℝ, 0 < η → 0 < δ →
      ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ N : ℝ, ∀ n ≥ N, 1 ≤ n →
        ∀ P : Measure C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), IsPathPrelimLaw.{u} T n P →
        P {γ | ∃ t ∈ Set.Icc 0 T, η < |∫ s in (0 : ℝ)..t,
          (ENpath n γ s (φ s) - smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε)|} ≤
        ENNReal.ofReal δ := by
  intro η δ hη hδ
  obtain ⟨ε₀, hε₀, h⟩ := prelimRepl_uniform.{u} hρ hT hφ η δ hη hδ
  refine ⟨ε₀, hε₀, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hnN hn P hP => ?_⟩
  obtain ⟨Ω, mΩ, μ, 𝓕, B, ψ, Zv, hμ, hB, hψ, hZm, -, hZv, rfl⟩ := hP.prelimVersion hn
  have hn0 : 0 < n := by linarith
  rw [Measure.map_apply hZm (measurableSet_pathReplEvent hρ hφ n ε η hn hε.1)]
  refine le_trans (measure_mono_ae ?_) (hN n hnN hB hψ)
  obtain ⟨h31, -⟩ := prop_3_1 hB hψ hn hT hφ
  filter_upwards [h31, hZv] with ω ha hv
  rintro ⟨t, ht, hlt⟩
  refine ⟨t, ht, ?_⟩
  have e : ∫ s in (0 : ℝ)..t, (ENpath n (Zv ω) s (φ s) -
      smoothedNormSq (pathAt (Zv ω) s : Measure ℝ) (φ s) ρ ε) = ∫ s in (0 : ℝ)..t,
      (EN n ψ ω s (φ s) - smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc 0 T := Set.uIcc_subset_Icc ⟨le_rfl, hT.le⟩ ht hs
    simp only [(WNpath_ENpath_eq hn0 (prelim_version_mem hv) ha.1 hs').2,
      prelim_pathAt_eq hv hs']
  rw [e] at hlt
  exact hlt

end QSSEPtoKPZ
