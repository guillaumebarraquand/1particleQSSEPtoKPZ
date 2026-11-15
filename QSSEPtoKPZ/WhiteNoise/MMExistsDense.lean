/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.MMExistsLimit
public import QSSEPtoKPZ.Tightness.TestFunctions

/-!
# Indicators of predictable sets are integrable against the martingale measure
(task G8b, auxiliary)

Let `𝒫` be the predictable σ-algebra of `𝒢`. For every `A ∈ 𝒫 ⊗ 𝓑(ℝ)`, the field
`(r, x, ω) ↦ 𝟙_A((r⁺, ω), x)` has an integral against `M` (`mmEx_indicator`). The class of such
`A` is a Dynkin system (complements: `𝟙_{Aᶜ} = 1 - 𝟙_A`; disjoint unions: dominated convergence
for the finite measure `q dℙ dr dx` on `[0,T] × ℝ`, `mmEx_tendsto_energy`, and the closure
`mmEx_of_tendsto`), and it contains the generators `((i, ∞) × A₀) × (l, u]`: on `[0, T]` these are
limits of the blocks `𝟙_{A₀}(ω) 𝟙_{(i, T']}(r) φₙ(x)`, where
`φₙ(x) = s((n+1)(x - l)) s((n+1)(u - x) + 1)` (`s` the smooth transition) is smooth with compact
support and tends to `𝟙_{(l,u]}(x)` at every `x` (`mmExBump`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {T : ℝ} {𝒢 : Filtration ℝ≥0 mΩ}
  {q : ℝ → ℝ → Ω → ℝ} {M : (ℝ → ℝ) → ℝ → Ω → ℝ}

/-- The fields `h` that are predictable and have an integral `h · M`. -/
def MMExIntegrable (T : ℝ) (𝒢 : Filtration ℝ≥0 mΩ) (q : ℝ → ℝ → Ω → ℝ)
    (M : (ℝ → ℝ) → ℝ → Ω → ℝ) (μ : Measure Ω) (h : ℝ → ℝ → Ω → ℝ) : Prop :=
  MMPred 𝒢 h ∧ ∃ X : ℝ → Ω → ℝ, IsMMIntegral T 𝒢 q M μ h X

/-- The field `(r, x, ω) ↦ 𝟙_A((r⁺, ω), x)` of a set `A ⊆ (ℝ≥0 × Ω) × ℝ`. -/
def mmExInd (A : Set ((ℝ≥0 × Ω) × ℝ)) (r x : ℝ) (ω : Ω) : ℝ :=
  A.indicator (fun _ => (1 : ℝ)) ((r.toNNReal, ω), x)

/-! ### Iterated integrals as integrals on `Ω × ℝ × ℝ` -/

private lemma mmEx_lintegral_eq_rho (F : ℝ → ℝ → Ω → ℝ≥0∞)
    (hF : Measurable fun p : Ω × ℝ × ℝ => F (p.2.1.toNNReal : ℝ) p.2.2 p.1) (ω : Ω) :
    ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω =
      ∫⁻ y, F (y.1.toNNReal : ℝ) y.2 ω ∂(mmRho T) := by
  have hm : Measurable fun y : ℝ × ℝ => F (y.1.toNNReal : ℝ) y.2 ω :=
    hF.comp measurable_prodMk_left
  rw [lintegral_prod _ hm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only [Real.coe_toNNReal r hr.1]

/-- `𝔼 ∫_0^T ∫ F = ∫ F d(ℙ ⊗ Leb|_{[0,T]} ⊗ Leb)` for a field with a measurable lift. -/
theorem mmEx_lintegral3_eq [SFinite μ] (F : ℝ → ℝ → Ω → ℝ≥0∞)
    (hF : Measurable fun p : Ω × ℝ × ℝ => F (p.2.1.toNNReal : ℝ) p.2.2 p.1) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω) ∂μ =
      ∫⁻ p, F (p.2.1.toNNReal : ℝ) p.2.2 p.1 ∂(μ.prod (mmRho T)) := by
  rw [lintegral_prod _ hF.aemeasurable]
  exact lintegral_congr fun ω => mmEx_lintegral_eq_rho F hF ω

/-- The energy only depends on the values of the field for `r ∈ [0, T]`. -/
theorem mmEx_energy_congr {h₁ h₂ : ℝ → ℝ → Ω → ℝ}
    (h : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x ω, h₁ r x ω = h₂ r x ω) :
    mmEnergy μ T q h₁ = mmEnergy μ T q h₂ := by
  unfold mmEnergy
  refine lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only [h r hr]

/-- A field vanishing for `r ∈ (0, T]` has energy `0`. -/
theorem mmEx_energy_eq_zero {h : ℝ → ℝ → Ω → ℝ}
    (h0 : ∀ r ∈ Set.Ioc (0 : ℝ) T, ∀ x ω, h r x ω = 0) : mmEnergy μ T q h = 0 := by
  unfold mmEnergy
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  refine ae_of_all _ fun ω => ?_
  simp only [Pi.zero_apply]
  rw [← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := T))]
  rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) fun r hr => by simp [h0 r hr]]
  simp

/-! ### Closure properties -/

section Closure

variable [IsProbabilityMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
  (hq0 : ∀ r x ω, 0 ≤ q r x ω)
  (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
  (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
include hT hq hq0 hq1 hM

/-- Closure of `MMExIntegrable` under energy limits. -/
theorem MMExIntegrable.of_tendsto {hs : ℕ → ℝ → ℝ → Ω → ℝ}
    (hhs : ∀ k, MMExIntegrable T 𝒢 q M μ (hs k)) {h : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h)
    (hlim : Tendsto (fun k => mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω)) atTop (𝓝 0)) :
    MMExIntegrable T 𝒢 q M μ h := by
  choose hp Xs hXs using hhs
  exact ⟨hh, mmEx_of_tendsto hT hq hq0 hq1 hM hXs hp hh hlim⟩

/-- Modification on a set of zero energy. -/
theorem MMExIntegrable.congr_energy {h₁ h₂ : ℝ → ℝ → Ω → ℝ}
    (h1 : MMExIntegrable T 𝒢 q M μ h₁) (hp : MMPred 𝒢 h₂)
    (hE : mmEnergy μ T q (fun r x ω => h₁ r x ω - h₂ r x ω) = 0) :
    MMExIntegrable T 𝒢 q M μ h₂ :=
  MMExIntegrable.of_tendsto hT hq hq0 hq1 hM (hs := fun _ => h₁) (fun _ => h1) hp
    (by simp only [hE]; exact tendsto_const_nhds)

/-- Modification for `r ∉ (0, T]`. -/
theorem MMExIntegrable.congr {h₁ h₂ : ℝ → ℝ → Ω → ℝ}
    (h1 : MMExIntegrable T 𝒢 q M μ h₁) (hp : MMPred 𝒢 h₂)
    (h : ∀ r ∈ Set.Ioc (0 : ℝ) T, ∀ x ω, h₁ r x ω = h₂ r x ω) :
    MMExIntegrable T 𝒢 q M μ h₂ :=
  h1.congr_energy hT hq hq0 hq1 hM hp
    (mmEx_energy_eq_zero fun r hr x ω => by rw [h r hr x ω, sub_self])

end Closure

theorem MMExIntegrable.add [IsProbabilityMeasure μ] {h₁ h₂ : ℝ → ℝ → Ω → ℝ}
    (h1 : MMExIntegrable T 𝒢 q M μ h₁) (h2 : MMExIntegrable T 𝒢 q M μ h₂) :
    MMExIntegrable T 𝒢 q M μ (fun r x ω => h₁ r x ω + h₂ r x ω) := by
  obtain ⟨p1, X1, hX1⟩ := h1
  obtain ⟨p2, X2, hX2⟩ := h2
  exact ⟨p1.add p2, _, IsMMIntegral.add _ _ _ _ hX1 hX2⟩

theorem MMExIntegrable.const_mul [IsProbabilityMeasure μ] {h : ℝ → ℝ → Ω → ℝ}
    (h1 : MMExIntegrable T 𝒢 q M μ h) (c : ℝ) :
    MMExIntegrable T 𝒢 q M μ (fun r x ω => c * h r x ω) := by
  obtain ⟨p1, X1, hX1⟩ := h1
  exact ⟨p1.const_mul c, _, hX1.const_mul c⟩

theorem MMExIntegrable.sub [IsProbabilityMeasure μ] {h₁ h₂ : ℝ → ℝ → Ω → ℝ}
    (h1 : MMExIntegrable T 𝒢 q M μ h₁) (h2 : MMExIntegrable T 𝒢 q M μ h₂) :
    MMExIntegrable T 𝒢 q M μ (fun r x ω => h₁ r x ω - h₂ r x ω) := by
  have := h1.add (h2.const_mul (-1))
  convert this using 1
  funext r x ω; ring

/-- The simple integrand `a 𝟙_{(s,t]}(r) φ(x)` is predictable (`φ` measurable). -/
theorem mmEx_block_pred {s t : ℝ≥0} {a : Ω → ℝ} (ha : Measurable[𝒢 s] a) {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    MMPred 𝒢 fun r x ω => if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0 := by
  have hg : Measurable[𝒢.predictable] fun p : ℝ≥0 × Ω =>
      if (s : ℝ) < p.1 ∧ (p.1 : ℝ) ≤ t then a p.2 else 0 := by
    intro B hB
    have e : (fun p : ℝ≥0 × Ω => if (s : ℝ) < p.1 ∧ (p.1 : ℝ) ≤ t then a p.2 else 0) ⁻¹' B =
        (Set.Ioc s t ×ˢ (a ⁻¹' B)) ∪ ((Set.Ioc s t ×ˢ Set.univ)ᶜ ∩ {_p | (0 : ℝ) ∈ B}) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_Ioc, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, NNReal.coe_lt_coe,
        NNReal.coe_le_coe]
      split_ifs with h <;> tauto
    rw [e]
    refine (measurableSet_predictable_Ioc_prod s t (ha hB)).union
      ((measurableSet_predictable_Ioc_prod s t MeasurableSet.univ).compl.inter ?_)
    by_cases h0 : (0 : ℝ) ∈ B
    · simp [h0]
    · simp [h0]
  unfold MMPred
  have hφ' : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => φ p.2 :=
    hφ.comp (measurable_snd.mono le_rfl BorelSpace.measurable_eq.le)
  have := (hg.comp (@measurable_fst _ _ 𝒢.predictable (borel ℝ))).mul hφ'
  convert this using 1
  funext p
  simp only [Pi.mul_apply, Function.comp_apply, ite_mul, zero_mul]

/-- Blocks `a 𝟙_{(s,t]}(r) φ(x)` with `φ ∈ C_b³`, `a` bounded and `𝒢_s`-measurable. -/
theorem mmEx_block [IsProbabilityMeasure μ] (hT : 0 ≤ T) (s t : ℝ≥0) (hst : s ≤ t)
    {a : Ω → ℝ} (ha : Measurable[𝒢 s] a) (hab : ∃ K, ∀ ω, |a ω| ≤ K) {φ : ℝ → ℝ} {C : ℝ}
    (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C) :
    MMExIntegrable T 𝒢 q M μ (fun r x ω => if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0) :=
  ⟨mmEx_block_pred ha (hφ.contDiff 0 ⟨le_rfl, hT⟩).continuous.measurable, _,
    IsMMIntegral.block s t hst a φ C hφ ha hab⟩

/-- The constant `1` is in `C_b³`. -/
private lemma mmEx_isC13_one : ∃ C, IsC13 T (fun _ => fun _ : ℝ => (1 : ℝ)) (fun _ _ => 0) C := by
  obtain ⟨C, -, hC⟩ := isC13_bumpTestRaw 0
  exact ⟨C, hC T⟩

theorem mmEx_zero [IsProbabilityMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ) :
    MMExIntegrable T 𝒢 q M μ (fun _ _ _ => 0) := by
  obtain ⟨C, hC⟩ := mmEx_isC13_one (T := T)
  refine (mmEx_block (q := q) (M := M) (μ := μ) hT 0 0 le_rfl (a := fun _ => 0)
    measurable_const ⟨0, by simp⟩ hC).congr hT hq hq0 hq1 hM measurable_const
    fun r _ x ω => ?_
  simp

/-! ### Smooth approximations of `𝟙_{(l,u]}` -/

/-- `φₙ(x) = s((n+1)(x - l)) s((n+1)(u - x) + 1)`, `s` the smooth transition. -/
def mmExBump (n : ℕ) (l u x : ℝ) : ℝ :=
  Real.smoothTransition ((n + 1) * (x - l)) * Real.smoothTransition ((n + 1) * (u - x) + 1)

theorem mmExBump_abs_le (n : ℕ) (l u x : ℝ) : |mmExBump n l u x| ≤ 1 := by
  unfold mmExBump
  rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _),
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (Real.smoothTransition.le_one _)
        (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem mmExBump_tendsto (l u x : ℝ) :
    Tendsto (fun n => mmExBump n l u x) atTop (𝓝 ((Set.Ioc l u).indicator (fun _ => 1) x)) := by
  refine tendsto_const_nhds.congr' ?_
  rcases le_or_gt x l with hxl | hxl
  · refine Eventually.of_forall fun n => ?_
    have h0 : ((n : ℝ) + 1) * (x - l) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hx : x ∉ Set.Ioc l u := fun h => absurd h.1 (not_lt.2 hxl)
    simp only [mmExBump, Real.smoothTransition.zero_of_nonpos h0, zero_mul,
      Set.indicator_of_notMem hx]
  rcases le_or_gt x u with hxu | hxu
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - l))
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Set.indicator_of_mem (show x ∈ Set.Ioc l u from ⟨hxl, hxu⟩)]
    unfold mmExBump
    have h1 : 1 ≤ ((n : ℝ) + 1) * (x - l) := by
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ (by linarith)] at hN
      nlinarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le
      (by nlinarith [(by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]), one_mul]
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - u))
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hxu))]
    unfold mmExBump
    have h1 : ((n : ℝ) + 1) * (u - x) + 1 ≤ 0 := by
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ (by linarith)] at hN
      nlinarith
    rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]

theorem mmExBump_isC13 (n : ℕ) (l u : ℝ) (T : ℝ) :
    ∃ C, IsC13 T (fun _ => mmExBump n l u) (fun _ _ => 0) C := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (mmExBump n l u) := by
    unfold mmExBump
    exact (Real.smoothTransition.contDiff.comp (contDiff_const.mul
      (contDiff_id.sub contDiff_const))).mul (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).add contDiff_const))
  have hcs : HasCompactSupport (mmExBump n l u) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := l) (b := u + 1)) fun x hx => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    unfold mmExBump
    rcases hx with h | h
    · have h0 : ((n : ℝ) + 1) * (x - l) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      simp [Real.smoothTransition.zero_of_nonpos h0]
    · have h0 : ((n : ℝ) + 1) * (u - x) + 1 ≤ 0 := by
        nlinarith [(by positivity : (0 : ℝ) ≤ (n : ℝ))]
      simp [Real.smoothTransition.zero_of_nonpos h0]
  obtain ⟨C, hC0, hC⟩ := hcs.exists_bound_iteratedFDeriv hsm 3
  have hC' : ∀ k ≤ 3, ∀ x, |iteratedDeriv k (mmExBump n l u) x| ≤ C := fun k hk x => by
    rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC k hk x
  refine ⟨4 * C, fun _ _ => hsm.of_le (WithTop.coe_le_coe.2 le_top),
    fun x t _ => hasDerivWithinAt_const _ _ _,
    ⟨continuousOn_const, fun k _ =>
      ((hsm.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp
        continuous_snd).continuousOn⟩,
    ⟨![C, 0, C, C, C], ?_, fun t _ x => ?_⟩⟩
  · simp only [Fin.sum_univ_five, Matrix.cons_val]
    linarith
  · simp only [Matrix.cons_val, abs_zero]
    have h0 := hC' 0 (by norm_num) x
    rw [iteratedDeriv_zero] at h0
    exact ⟨h0, le_rfl, hC' 1 (by norm_num) x, hC' 2 (by norm_num) x, hC' 3 (by norm_num) x⟩

/-! ### Dominated convergence for the energy -/

/-- If `F_n → G` pointwise with `|F_n - G| ≤ K`, then `𝔼 ∫_0^T ∫ (F_n - G)² q → 0`. -/
theorem mmEx_tendsto_energy [IsFiniteMeasure μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    {F : ℕ → ℝ → ℝ → Ω → ℝ} {G : ℝ → ℝ → Ω → ℝ} (hF : ∀ n, MMPred 𝒢 (F n)) (hG : MMPred 𝒢 G)
    {K : ℝ} (hK : ∀ n r x ω, |F n r x ω - G r x ω| ≤ K)
    (hlim : ∀ r x ω, Tendsto (fun n => F n r x ω) atTop (𝓝 (G r x ω))) :
    Tendsto (fun n => mmEnergy μ T q (fun r x ω => F n r x ω - G r x ω)) atTop (𝓝 0) := by
  set L : (ℝ → ℝ → Ω → ℝ) → Ω × ℝ × ℝ → ℝ := fun f p => f (p.2.1.toNNReal : ℝ) p.2.2 p.1
    with hLdef
  have e : ∀ n, mmEnergy μ T q (fun r x ω => F n r x ω - G r x ω) =
      ∫⁻ p, ENNReal.ofReal ((L (F n) p - L G p) ^ 2 * L q p) ∂(μ.prod (mmRho T)) := fun n =>
    mmEx_lintegral3_eq (fun r x ω => ENNReal.ofReal ((F n r x ω - G r x ω) ^ 2 * q r x ω))
      (((((hF n).sub hG).lift).pow_const 2).mul hq.lift).ennreal_ofReal
  refine (tendsto_congr e).2 ?_
  have hq1' : ∫⁻ p, ENNReal.ofReal (L q p) ∂(μ.prod (mmRho T)) < ⊤ := by
    rw [← mmEx_lintegral3_eq (fun r x ω => ENNReal.ofReal (q r x ω)) hq.lift.ennreal_ofReal]
    exact hq1
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _p, 0 ∂(μ.prod (mmRho T)) := by simp
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence (fun p => ENNReal.ofReal (K ^ 2 * L q p))
    (fun n => (((((hF n).sub hG).lift).pow_const 2).mul hq.lift).ennreal_ofReal)
    (fun n => ae_of_all _ fun p => ENNReal.ofReal_le_ofReal ?_) ?_ (ae_of_all _ fun p => ?_)
  · refine mul_le_mul_of_nonneg_right ?_ (hq0 _ _ _)
    have := hK n (p.2.1.toNNReal : ℝ) p.2.2 p.1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  · simp_rw [ENNReal.ofReal_mul (sq_nonneg K)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq1'.ne
  · have h1 := ((hlim (p.2.1.toNNReal : ℝ) p.2.2 p.1).sub_const (G (p.2.1.toNNReal : ℝ) p.2.2 p.1))
    rw [sub_self] at h1
    have h2 := ENNReal.tendsto_ofReal ((h1.pow 2).mul_const (q (p.2.1.toNNReal : ℝ) p.2.2 p.1))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      ENNReal.ofReal_zero] at h2
    exact h2

end QSSEPtoKPZ
