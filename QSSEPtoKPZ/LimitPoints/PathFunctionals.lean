/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.LimitPoints.PathFunAtoms
public import QSSEPtoKPZ.LimitPoints.PathFunTest
public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.Tightness.Integral

/-!
# The quantities of Sections 3–6 as functionals of the path (task Q1a)

INTERFACE FILE (task I0″ of Stage 4): the definitions are complete; the statements below are
interfaces, proved by task Q1a. See `docs/stage4-design.md`, Sections 1.2 (b) and 3.5, and
`docs/stage4-interfaces.md`.

Section 7.1 of the article: "all the quantities introduced in the previous sections, in
particular `𝒲_n`, `ℰ_n`, `M_n^φ` and `⟨M_n^φ⟩`, are measurable functions of the trajectory
`(𝖹_n(t))_{t ∈ [0,T]}`, because `𝔷_n(t,x)` is the mass of the atom of `𝖹_n(t)` located at
`y_n(t,x)`". The path versions below are those functions, on `C([0,T], ℳ₊)`; on a version of
`𝖹_n` they coincide with the quantities of Stage 2 (`WN`, `EN`, `QN`, `MN`) at all times of
`[0,T]` (pointwise statements: for every path equal to `𝖹_n(t)` at all `t ∈ [0,T]`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {T : ℝ}

/-- The mass of the atom of `γ(t)` at `y_n(t,x)`; it is `𝔷_n(t,x)` on a version of `𝖹_n`. -/
def atomPath (n : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t : ℝ) (x : ℤ) : ℝ :=
  ((pathAt γ t : Measure ℝ) {rescaledPosition n t x}).toReal

/-- `𝒲_n(t) = γ(t)(1)`, the total mass (3.6). -/
def WNpath (t : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : ℝ :=
  pairFM (pathAt γ t) fun _ => 1

/-- `ℰ_n(t;φ)` of (3.12), with atoms in place of `𝔷_n`. -/
def ENpath (n : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  n ^ (1 / 2 : ℝ) * ∑' x : ℤ, atomPath n γ t x * atomPath n γ t (x + 1) *
    φ (rescaledPosition n t x) * φ (rescaledPosition n t (x + 1))

/-- The integrand of (3.15), with atoms in place of `𝔷_n`. -/
def QNdensPath (n : ℝ) (φ : ℝ → ℝ → ℝ) (s : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ℝ :=
  ∑' x : ℤ, atomPath n γ s x * atomPath n γ s (x + 1) *
    (Real.exp (thetaN n / 2) * φ s (rescaledPosition n s (x + 1)) -
      Real.exp (-thetaN n / 2) * φ s (rescaledPosition n s x)) ^ 2

/-- `⟨M_n^φ⟩_t = n ∫_0^t QNdensPath(s) ds`, (3.15). -/
def QNpath (n : ℝ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : ℝ :=
  n * ∫ s in (0 : ℝ)..t, QNdensPath n φ s γ

/-- `M_n^φ(t) = γ(t)(φ_t) - φ_0(0) - ∫_0^t γ(s)(∂ₛφ_s + 𝒜_nφ_s) ds`, (3.14). -/
def MNpath (n : ℝ) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : ℝ :=
  pairFM (pathAt γ t) (φ t) - φ 0 0 -
    ∫ s in (0 : ℝ)..t, pairFM (pathAt γ s) (fun y => φt s y + AN n (φ s) y)

/-! ### Auxiliary results -/

/-- The atoms are jointly measurable in `(γ, s)`. -/
private lemma pathFun_measurable_atomPath_prod (n : ℝ) (x : ℤ) :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => atomPath n p.1 p.2 x := by
  have hY : Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      rescaledPosition n p.2 x := by
    unfold rescaledPosition; fun_prop
  have h := pathFun_measurable_atom
    (F := fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => pathAt p.1 p.2)
    continuous_pathAt_prod hY.measurable
  unfold atomPath
  exact h

/-- The integrand of (3.15) at the clamped time `max(0, min(T, s))` is jointly measurable in
`(γ, s)`. -/
private lemma pathFun_measurable_QNdens_clamp {n C : ℝ} {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      QNdensPath n φ (pathFunClamp T p.2) p.1 := by
  have hc := continuous_pathFunClamp T
  have hA : ∀ x, Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      atomPath n p.1 (pathFunClamp T p.2) x := fun x =>
    (pathFun_measurable_atomPath_prod n x).comp
      (measurable_fst.prodMk (hc.measurable.comp measurable_snd))
  have hP : ∀ x, Continuous fun s =>
      φ (pathFunClamp T s) (rescaledPosition n (pathFunClamp T s) x) := by
    intro x
    have h0 := hφ.pathFun_continuousOn_comp (f := fun y => y) continuous_id
    refine h0.comp_continuous (f := fun s => (pathFunClamp T s,
      rescaledPosition n (pathFunClamp T s) x)) ?_ fun s => ⟨pathFunClamp_mem hT s, trivial⟩
    refine hc.prodMk ?_
    unfold rescaledPosition; fun_prop
  unfold QNdensPath
  refine Measurable.tsum fun x => ((hA x).mul (hA (x + 1))).mul ?_
  exact ((((hP (x + 1)).measurable.comp measurable_snd).const_mul _).sub
    (((hP x).measurable.comp measurable_snd).const_mul _)).pow_const 2

/-- The integrand of (3.15) is nonnegative. -/
private lemma pathFun_QNdensPath_nonneg (n : ℝ) (φ : ℝ → ℝ → ℝ) (s : ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : 0 ≤ QNdensPath n φ s γ :=
  tsum_nonneg fun _ => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (sq_nonneg _)

/-- `∑ₓ aₓ aₓ₊₁ bₓ ≤ M · B · M` when `0 ≤ aₓ ≤ M`, `∑ₓ aₓ ≤ M` and `0 ≤ bₓ ≤ B`. -/
private lemma pathFun_tsum_bound {a b : ℤ → ℝ} {M B : ℝ} (ha : ∀ x, 0 ≤ a x) (hs : Summable a)
    (haM : ∀ x, a x ≤ M) (hsum : ∑' x, a x ≤ M) (hb : ∀ x, 0 ≤ b x ∧ b x ≤ B) :
    ∑' x, a x * a (x + 1) * b x ≤ M * B * M := by
  have hM : 0 ≤ M := (ha 0).trans (haM 0)
  have hle : ∀ x, a x * a (x + 1) * b x ≤ a x * (M * B) := fun x => by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (haM _) (hb x).2 (hb x).1 hM) (ha x)
  have hnn : ∀ x, 0 ≤ a x * a (x + 1) * b x := fun x =>
    mul_nonneg (mul_nonneg (ha x) (ha _)) (hb x).1
  have hg : Summable fun x => a x * (M * B) := hs.mul_right _
  calc ∑' x, a x * a (x + 1) * b x ≤ ∑' x, a x * (M * B) :=
        Summable.tsum_le_tsum hle (hg.of_nonneg_of_le hnn hle) hg
    _ = (∑' x, a x) * (M * B) := tsum_mul_right
    _ ≤ M * (M * B) := mul_le_mul_of_nonneg_right hsum
        (mul_nonneg hM (((hb 0).1).trans (hb 0).2))
    _ = M * B * M := by ring

/-- For every path, `s ↦ QNdensPath(s)` is integrable on `[0,T]`. -/
private lemma pathFun_integrableOn_QNdens {n C : ℝ} (hn : 0 < n) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    MeasureTheory.IntegrableOn (fun s => QNdensPath n φ s γ) (Set.Icc 0 T) := by
  -- a bound `M` on the masses `γ(s)(ℝ)`, `s ∈ [0,T]`
  have hmc : Continuous fun s => ((pathAt γ s).mass : ℝ) :=
    NNReal.continuous_coe.comp (FiniteMeasure.continuous_mass.comp
      (continuous_pathAt_prod.comp (continuous_const.prodMk continuous_id)))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hmc.continuousOn
  have hmass : ∀ s ∈ Set.Icc 0 T, ((pathAt γ s : Measure ℝ) Set.univ).toReal ≤ M := by
    intro s hs
    rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM s hs)
  obtain ⟨c, hc0, hc⟩ := hφ.pathFun_bound
  set B := (Real.exp (thetaN n / 2) * c + Real.exp (-thetaN n / 2) * c) ^ 2
  have hbound : ∀ s ∈ Set.Icc 0 T, QNdensPath n φ s γ ≤ M * B * M := by
    intro s hs
    obtain ⟨hsum, hle⟩ := pathFun_tsum_atoms_le (pathAt γ s)
      (pathFun_rescaledPosition_injective hn s)
    unfold QNdensPath
    refine pathFun_tsum_bound (a := fun x => atomPath n γ s x)
      (b := fun x => (Real.exp (thetaN n / 2) * φ s (rescaledPosition n s (x + 1)) -
        Real.exp (-thetaN n / 2) * φ s (rescaledPosition n s x)) ^ 2)
      (fun _ => ENNReal.toReal_nonneg) hsum (fun x => ?_)
      (hle.trans (hmass s hs)) (fun x => ⟨sq_nonneg _, ?_⟩)
    · exact (ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (Set.subset_univ _))).trans (hmass s hs)
    · rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add ?_ ?_)) 2
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hc s hs _) (Real.exp_pos _).le
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hc s hs _) (Real.exp_pos _).le
  have hg : Measurable fun s => QNdensPath n φ (pathFunClamp T s) γ := by
    have h := (pathFun_measurable_QNdens_clamp (n := n) hφ hT).comp
      (measurable_prodMk_left (x := γ))
    rw [Function.comp_def] at h
    exact h
  have hint : MeasureTheory.IntegrableOn (fun s => QNdensPath n φ (pathFunClamp T s) γ)
      (Set.Icc 0 T) := by
    refine Measure.integrableOn_of_bounded (M := M * B * M) measure_Icc_lt_top.ne
      hg.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pathFun_QNdensPath_nonneg _ _ _ _)]
    exact hbound _ (pathFunClamp_mem hT s)
  exact hint.congr_fun (fun s hs => by simp only [pathFunClamp_of_mem hs]) measurableSet_Icc

/-- The drift term `γ(s)(∂ₛφ_s + 𝒜_nφ_s)` at the clamped time is jointly continuous in
`(γ, s)`. -/
private lemma pathFun_continuous_drift_clamp {n C : ℝ} {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      pairFM (pathAt p.1 (pathFunClamp T p.2))
        (fun y => φt (pathFunClamp T p.2) y + AN n (φ (pathFunClamp T p.2)) y) := by
  have h := continuousOn_pairFM_pathAt (hφ.pathFun_continuousOn_drift n)
    (hφ.pathFun_bound_drift n)
  exact h.comp_continuous
    (f := fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => (p.1, pathFunClamp T p.2))
    (continuous_fst.prodMk ((continuous_pathFunClamp T).comp continuous_snd))
    fun p => ⟨trivial, pathFunClamp_mem hT p.2⟩

/-- On `[0,T]`, the pairing of the path with a bounded measurable function is that of `𝖹_n`. -/
private lemma pathFun_pairFM_eq {Ω : Type*} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {n : ℝ}
    {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hγ : ∀ t (ht : t ∈ Set.Icc 0 T), (γ ⟨t, ht⟩ : Measure ℝ) = tiltedMeasure n ψ ω t)
    (hs : ∀ t, 0 ≤ t → Summable (zN n ψ ω t)) {s : ℝ} (hsT : s ∈ Set.Icc 0 T) {h : ℝ → ℝ}
    (hm : Measurable h) {c : ℝ} (hc : ∀ y, |h y| ≤ c) :
    pairFM (pathAt γ s) h = pairZ n ψ ω s h := by
  rw [pairFM, pathAt_of_mem γ hsT, hγ s hsT]
  exact (integral_tiltedMeasure (hs s hsT.1) hm hc).2.2

/-! ### Measurability and continuity in time -/

/-- The atoms are Borel functions of the path. -/
theorem measurable_atomPath (n t : ℝ) (x : ℤ) :
    Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => atomPath n γ t x := by
  have h := (pathFun_measurable_atomPath_prod (T := T) n x).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  rw [Function.comp_def] at h
  exact h

set_option linter.unusedVariables false in
/-- `γ ↦ ℰ_n(t;φ)` is measurable (`φ` measurable). -/
theorem measurable_ENpath (n t : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => ENpath n γ t φ := by
  unfold ENpath
  exact measurable_const.mul (Measurable.tsum fun x =>
    (((measurable_atomPath n t x).mul (measurable_atomPath n t (x + 1))).mul
      measurable_const).mul measurable_const)

set_option linter.unusedVariables false in
/-- For `φ ∈ C_b^{1,3}` and `t ∈ [0,T]`, `γ ↦ M_n^φ(t)` is measurable. -/
theorem measurable_MNpath {n C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Measurable (MNpath n φ φt t (T := T)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  have h1 : Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => pairFM (pathAt γ t) (φ t) :=
    ((continuous_pairFM (hφ.contDiff t ht).continuous ⟨c, hc t ht⟩).comp
      (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))).measurable
  have h2 := (pathFun_continuous_drift_clamp (n := n) hφ hT).measurable.stronglyMeasurable
    |>.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 t))
  have heq : MNpath n φ φt t (T := T) = fun γ => pairFM (pathAt γ t) (φ t) - φ 0 0 -
      ∫ s, pairFM (pathAt γ (pathFunClamp T s))
        (fun y => φt (pathFunClamp T s) y + AN n (φ (pathFunClamp T s)) y)
        ∂(volume.restrict (Set.Ioc 0 t)) := by
    funext γ
    rw [MNpath, intervalIntegral.integral_of_le ht.1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [pathFunClamp_of_mem (⟨hs.1.le, hs.2.trans ht.2⟩ : s ∈ Set.Icc 0 T)]
  rw [heq]
  exact (h1.sub measurable_const).sub h2.measurable

set_option linter.unusedVariables false in
/-- For `φ ∈ C_b^{1,3}` and `t ∈ [0,T]`, `γ ↦ ⟨M_n^φ⟩_t` is measurable. -/
theorem measurable_QNpath {n C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Measurable (QNpath n φ t (T := T)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h2 := (pathFun_measurable_QNdens_clamp (n := n) hφ hT).stronglyMeasurable
    |>.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 t))
  have heq : QNpath n φ t (T := T) = fun γ => n *
      ∫ s, QNdensPath n φ (pathFunClamp T s) γ ∂(volume.restrict (Set.Ioc 0 t)) := by
    funext γ
    rw [QNpath, intervalIntegral.integral_of_le ht.1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [pathFunClamp_of_mem (⟨hs.1.le, hs.2.trans ht.2⟩ : s ∈ Set.Icc 0 T)]
  rw [heq]
  exact measurable_const.mul h2.measurable

set_option linter.unusedVariables false in
/-- For every path, `t ↦ M_n^φ(t)` is continuous on `[0,T]`. -/
theorem continuousOn_MNpath {n C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ContinuousOn (fun t => MNpath n φ φt t γ) (Set.Icc 0 T) := by
  by_cases hT : 0 ≤ T
  swap
  · exact fun s hs => absurd (hs.1.trans hs.2) hT
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  have hφ0 := hφ.pathFun_continuousOn_comp (f := fun y => y) continuous_id
  have h1 : ContinuousOn (fun s => pairFM (pathAt γ s) (φ s)) (Set.Icc 0 T) :=
    (continuousOn_pairFM_pathAt hφ0 ⟨c, hc⟩).comp
      (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨trivial, hs⟩
  have hd : ContinuousOn (fun s => pairFM (pathAt γ s) (fun y => φt s y + AN n (φ s) y))
      (Set.Icc 0 T) :=
    (continuousOn_pairFM_pathAt (hφ.pathFun_continuousOn_drift n)
      (hφ.pathFun_bound_drift n)).comp
      (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨trivial, hs⟩
  have h2 := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
    (by rw [Set.uIcc_of_le hT]; exact hd.integrableOn_Icc)
  rw [Set.uIcc_of_le hT] at h2
  exact (h1.sub continuousOn_const).sub h2

/-- For every path, `t ↦ ⟨M_n^φ⟩_t` is continuous and nondecreasing on `[0,T]`. -/
theorem continuousOn_monotoneOn_QNpath {n C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) :
    ContinuousOn (fun t => QNpath n φ t γ) (Set.Icc 0 T) ∧
      MonotoneOn (fun t => QNpath n φ t γ) (Set.Icc 0 T) := by
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨fun s hs => absurd (hs.1.trans hs.2) hT, fun s hs => absurd (hs.1.trans hs.2) hT⟩
  have hint := pathFun_integrableOn_QNdens (n := n) (by linarith) hφ hT γ
  refine ⟨?_, fun a ha b hb hab => ?_⟩
  · have h2 := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (by rw [Set.uIcc_of_le hT]; exact hint)
    rw [Set.uIcc_of_le hT] at h2
    exact continuousOn_const.mul h2
  · refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine intervalIntegral.integral_mono_interval le_rfl ha.1 hab
      (ae_of_all _ fun s => pathFun_QNdensPath_nonneg n φ s γ) ?_
    exact (hint.mono_set (Set.uIcc_subset_Icc ⟨le_rfl, hT⟩ hb)).intervalIntegrable

/-! ### Identification on a version of `𝖹_n` -/

section Version

variable {Ω : Type*} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {n : ℝ}
  {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}

/-- On a version, the atoms are the `𝔷_n(t,x)`. -/
theorem atomPath_eq (hn : 0 < n)
    (hγ : ∀ t (ht : t ∈ Set.Icc 0 T), (γ ⟨t, ht⟩ : Measure ℝ) = tiltedMeasure n ψ ω t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : ℤ) : atomPath n γ t x = zN n ψ ω t x := by
  have hz : ∀ x', 0 ≤ zN n ψ ω t x' := fun x' =>
    mul_nonneg (Real.exp_pos _).le (by unfold density; positivity)
  have hinj := pathFun_rescaledPosition_injective hn t
  rw [atomPath, pathAt_of_mem γ ht, hγ t ht, tiltedMeasure,
    Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [tsum_eq_single x, Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one,
    ENNReal.toReal_ofReal (hz x)]
  intro x' hx'
  rw [Set.indicator_of_notMem (fun h => hx' (hinj (Set.mem_singleton_iff.1 h))), mul_zero]

/-- On a version, `𝒲_n` and `ℰ_n` are those of Stage 2. -/
theorem WNpath_ENpath_eq (hn : 0 < n)
    (hγ : ∀ t (ht : t ∈ Set.Icc 0 T), (γ ⟨t, ht⟩ : Measure ℝ) = tiltedMeasure n ψ ω t)
    (hs : ∀ t, 0 ≤ t → Summable (zN n ψ ω t)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    WNpath t γ = WN n ψ t ω ∧ ∀ φ : ℝ → ℝ, ENpath n γ t φ = EN n ψ ω t φ := by
  refine ⟨?_, fun φ => ?_⟩
  · rw [WNpath, WN]
    exact pathFun_pairFM_eq hγ hs ht measurable_const (c := 1) fun _ => by simp
  · simp only [ENpath, EN, atomPath_eq hn hγ ht]

/-- On a version, `M_n^φ` and `⟨M_n^φ⟩` are those of Stage 2 (Proposition 3.1). -/
theorem MNpath_QNpath_eq (hn : 1 ≤ n) {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    (hγ : ∀ t (ht : t ∈ Set.Icc 0 T), (γ ⟨t, ht⟩ : Measure ℝ) = tiltedMeasure n ψ ω t)
    (hs : ∀ t, 0 ≤ t → Summable (zN n ψ ω t)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    MNpath n φ φt t γ = MN n ψ φ φt t ω ∧ QNpath n φ t γ = QN n ψ φ t ω := by
  have hn0 : 0 < n := by linarith
  obtain ⟨c, -, hc⟩ := hφ.pathFun_bound
  obtain ⟨K, hK⟩ := hφ.pathFun_bound_drift n
  have hdc := hφ.pathFun_continuousOn_drift n
  constructor
  · rw [MNpath, MN, pathFun_pairFM_eq hγ hs ht (hφ.contDiff t ht).continuous.measurable (hc t ht)]
    congr 1
    refine intervalIntegral.integral_congr fun s hsI => ?_
    rw [Set.uIcc_of_le ht.1] at hsI
    have hsT : s ∈ Set.Icc 0 T := ⟨hsI.1, hsI.2.trans ht.2⟩
    have hm : Continuous fun y => φt s y + AN n (φ s) y :=
      hdc.comp_continuous (f := fun y => (s, y)) (continuous_const.prodMk continuous_id)
        fun y => ⟨hsT, trivial⟩
    exact pathFun_pairFM_eq hγ hs hsT hm.measurable (hK s hsT)
  · rw [QNpath, QN]
    congr 1
    refine intervalIntegral.integral_congr fun s hsI => ?_
    rw [Set.uIcc_of_le ht.1] at hsI
    have hsT : s ∈ Set.Icc 0 T := ⟨hsI.1, hsI.2.trans ht.2⟩
    simp only [QNdensPath, QNdens, atomPath_eq hn0 hγ hsT]

end Version

end QSSEPtoKPZ
