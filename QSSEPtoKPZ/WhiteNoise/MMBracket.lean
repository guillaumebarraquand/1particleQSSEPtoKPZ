/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.CovariationAlgebra
public import QSSEPtoKPZ.ItoIntegral.Convergence
public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Brackets `∫_0^t ∫ q h g dx dr` of martingale-measure integrals (task G8a, auxiliary)

For an intensity `q ≥ 0` and fields `h, g : ℝ → ℝ → Ω → ℝ` measurable for the predictable
σ-algebra (`MMPred`), with finite energies `𝔼 ∫_0^T ∫ h² q`, `𝔼 ∫_0^T ∫ g² q` (`mmEnergy`), the
bracket `mmBr q h g t ω = ∫_0^t ∫ q h g dx dr` is, almost surely, a genuine iterated integral,
continuous and of bounded variation on `[0, T]` (`mmBr_ae_good`); it is integrable at each time
(`integrable_mmBr`), linear in `h` almost surely (`mmBr_lincomb_ae`), and continuous in `h` for
the energy, in `L¹(ℙ)` at each time (`tendsto_mmBr_sub`).

The basic estimate is `𝔼 ∫_0^T ∫ |q h g| ≤ λ 𝔼 ∫_0^T ∫ h² q + λ⁻¹ 𝔼 ∫_0^T ∫ g² q`
(`mm_lintegral_enorm_le`), proved on the product space `Ω × ℝ × ℝ`, to which predictable fields
are lifted by `(ω, r, x) ↦ h(r⁺, x, ω)` (`MMPred.lift`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The bracket `t ↦ ∫_0^t ∫ q h g dx dr` of (7.10). -/
def mmBr (q h g : ℝ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * h r x ω * g r x ω

/-- The energy `𝔼 ∫_0^T ∫ h² q dx dr` (iterated lower integrals). -/
def mmEnergy (μ : Measure Ω) (T : ℝ) (q h : ℝ → ℝ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (h r x ω ^ 2 * q r x ω)) ∂μ

/-- A field `h(r, x, ω)` measurable for `𝒫 ⊗ 𝓑(ℝ)`, `𝒫` the predictable σ-algebra of `𝒢`. -/
def MMPred (𝒢 : Filtration ℝ≥0 mΩ) (h : ℝ → ℝ → Ω → ℝ) : Prop :=
  Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2

variable {𝒢 : Filtration ℝ≥0 mΩ}

/-- The map `(ω, r, x) ↦ ((r⁺, ω), x)`. -/
private def mmPredMap (p : Ω × ℝ × ℝ) : (ℝ≥0 × Ω) × ℝ := ((p.2.1.toNNReal, p.1), p.2.2)

private lemma mm_predictable_le :
    𝒢.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact (measurableSet_singleton _).prod (𝒢.le _ _ hA)
  · exact measurableSet_Ioi.prod (𝒢.le _ _ hA)

private lemma measurable_mmPredMap :
    Measurable[inferInstance, (𝒢.predictable).prod (borel ℝ)] (mmPredMap (Ω := Ω)) := by
  have h : Measurable (mmPredMap (Ω := Ω)) := by
    unfold mmPredMap
    fun_prop
  refine h.mono le_rfl ?_
  exact sup_le_sup (MeasurableSpace.comap_mono mm_predictable_le)
    (MeasurableSpace.comap_mono BorelSpace.measurable_eq.ge)

/-- The lift `(ω, r, x) ↦ h(r⁺, x, ω)` of a predictable field is measurable. -/
theorem MMPred.lift {h : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) :
    Measurable fun p : Ω × ℝ × ℝ => h (p.2.1.toNNReal : ℝ) p.2.2 p.1 :=
  hh.comp measurable_mmPredMap

theorem MMPred.mul {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) :
    MMPred 𝒢 fun r x ω => h r x ω * g r x ω := Measurable.mul hh hg

theorem MMPred.add {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) :
    MMPred 𝒢 fun r x ω => h r x ω + g r x ω := Measurable.add hh hg

theorem MMPred.sub {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) :
    MMPred 𝒢 fun r x ω => h r x ω - g r x ω := Measurable.sub hh hg

theorem MMPred.const_mul {h : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (c : ℝ) :
    MMPred 𝒢 fun r x ω => c * h r x ω := Measurable.const_mul hh c

/-- A deterministic field `ψ(x)`, `ψ` measurable, is predictable. -/
theorem mmPred_of_measurable {ψ : ℝ → ℝ} (hψ : Measurable ψ) :
    MMPred 𝒢 fun _ x _ => ψ x := by
  unfold MMPred
  exact hψ.comp (measurable_snd.mono le_rfl BorelSpace.measurable_eq.le)

/-! ### Iterated integrals on `[0, T] × ℝ` -/

/-- The measure `Leb|_{[0,T]} ⊗ Leb` on `ℝ × ℝ`. -/
abbrev mmRho (T : ℝ) : Measure (ℝ × ℝ) := (volume.restrict (Set.Icc (0 : ℝ) T)).prod volume

private lemma mm_lintegral_eq_rho {T : ℝ} (F : ℝ → ℝ → Ω → ℝ≥0∞)
    (hF : Measurable fun p : Ω × ℝ × ℝ => F (p.2.1.toNNReal : ℝ) p.2.2 p.1) (ω : Ω) :
    ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω =
      ∫⁻ y, F (y.1.toNNReal : ℝ) y.2 ω ∂(mmRho T) := by
  have hm : Measurable fun y : ℝ × ℝ => F (y.1.toNNReal : ℝ) y.2 ω :=
    hF.comp measurable_prodMk_left
  rw [lintegral_prod _ hm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only [Real.coe_toNNReal r hr.1]

/-- The inner iterated integral `ω ↦ ∫_0^T ∫ F` of a field with a measurable lift is
measurable. -/
theorem mm_measurable_lintegral {T : ℝ} (F : ℝ → ℝ → Ω → ℝ≥0∞)
    (hF : Measurable fun p : Ω × ℝ × ℝ => F (p.2.1.toNNReal : ℝ) p.2.2 p.1) :
    Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω := by
  simp_rw [mm_lintegral_eq_rho F hF]
  exact hF.lintegral_prod_right'

private lemma mm_lintegral3_eq {μ : Measure Ω} [SFinite μ] {T : ℝ} (F : ℝ → ℝ → Ω → ℝ≥0∞)
    (hF : Measurable fun p : Ω × ℝ × ℝ => F (p.2.1.toNNReal : ℝ) p.2.2 p.1) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω) ∂μ =
      ∫⁻ p, F (p.2.1.toNNReal : ℝ) p.2.2 p.1 ∂(μ.prod (mmRho T)) := by
  rw [lintegral_prod _ hF.aemeasurable]
  exact lintegral_congr fun ω => mm_lintegral_eq_rho F hF ω

/-- Linearity of the iterated integral `𝔼 ∫_0^T ∫`. -/
private lemma mm_lintegral3_lincomb {μ : Measure Ω} [SFinite μ] {T : ℝ}
    (F G : ℝ → ℝ → Ω → ℝ≥0∞)
    (hF : Measurable fun p : Ω × ℝ × ℝ => F (p.2.1.toNNReal : ℝ) p.2.2 p.1)
    (hG : Measurable fun p : Ω × ℝ × ℝ => G (p.2.1.toNNReal : ℝ) p.2.2 p.1)
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, (a * F r x ω + b * G r x ω)) ∂μ =
      a * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω) ∂μ +
        b * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, G r x ω) ∂μ := by
  rw [mm_lintegral3_eq _ ((hF.const_mul a).add (hG.const_mul b)), mm_lintegral3_eq _ hF,
    mm_lintegral3_eq _ hG, lintegral_add_left (hF.const_mul a), lintegral_const_mul' _ _ ha,
    lintegral_const_mul' _ _ hb]

/-- Monotonicity of the iterated lower integral (no measurability needed). -/
theorem mm_lintegral3_mono {μ : Measure Ω} {T : ℝ} {F G : ℝ → ℝ → Ω → ℝ≥0∞}
    (h : ∀ r x ω, F r x ω ≤ G r x ω) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω) ∂μ ≤
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, G r x ω) ∂μ :=
  lintegral_mono fun _ => lintegral_mono fun _ => lintegral_mono fun _ => h _ _ _

/-- Constants come out of the iterated lower integral (no measurability needed). -/
theorem mm_lintegral3_const_mul {μ : Measure Ω} {T : ℝ} (F : ℝ → ℝ → Ω → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : c ≠ ∞) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, c * F r x ω) ∂μ =
      c * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, F r x ω) ∂μ := by
  simp_rw [lintegral_const_mul' _ _ hc]

/-! ### Energy estimates -/

/-- `|q a b| ≤ λ a² q + λ⁻¹ b² q` for `q ≥ 0`. -/
private lemma mm_enorm_le_lam {q a b : ℝ} (hq : 0 ≤ q) {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ∞) :
    ‖q * a * b‖ₑ ≤ l * ENNReal.ofReal (a ^ 2 * q) + l⁻¹ * ENNReal.ofReal (b ^ 2 * q) := by
  have h := StochIntAux.enorm_mul_le_lam (Real.sqrt q * a) (Real.sqrt q * b) hl0 hlt
  rw [StochIntAux.enorm_sq_eq, StochIntAux.enorm_sq_eq, mul_pow, mul_pow,
    Real.sq_sqrt hq] at h
  have e : Real.sqrt q * a * (Real.sqrt q * b) = q * a * b := by
    have := Real.mul_self_sqrt hq
    calc Real.sqrt q * a * (Real.sqrt q * b) = (Real.sqrt q * Real.sqrt q) * a * b := by ring
      _ = q * a * b := by rw [this]
  rw [e] at h
  simpa only [mul_comm q] using h

variable {μ : Measure Ω} {T : ℝ} {q : ℝ → ℝ → Ω → ℝ}

/-- **Basic estimate**: `𝔼 ∫_0^T ∫ |q h g| ≤ λ 𝔼 ∫_0^T ∫ h² q + λ⁻¹ 𝔼 ∫_0^T ∫ g² q`. -/
theorem mm_lintegral_enorm_le [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) {l : ℝ≥0∞} (hl0 : l ≠ 0)
    (hlt : l ≠ ∞) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖q r x ω * h r x ω * g r x ω‖ₑ) ∂μ ≤
      l * mmEnergy μ T q h + l⁻¹ * mmEnergy μ T q g := by
  refine (mm_lintegral3_mono fun r x ω => mm_enorm_le_lam (hq0 r x ω) hl0 hlt).trans
    (le_of_eq ?_)
  exact mm_lintegral3_lincomb _ _ ((hh.lift.pow_const 2).mul hq.lift).ennreal_ofReal
    ((hg.lift.pow_const 2).mul hq.lift).ennreal_ofReal hlt (ENNReal.inv_ne_top.2 hl0)

/-- The energy of a sum: `E(a h + b g) ≤ 2 a² E(h) + 2 b² E(g)`. -/
theorem mmEnergy_lincomb_le [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) (a b : ℝ) :
    mmEnergy μ T q (fun r x ω => a * h r x ω + b * g r x ω) ≤
      ENNReal.ofReal (2 * a ^ 2) * mmEnergy μ T q h +
        ENNReal.ofReal (2 * b ^ 2) * mmEnergy μ T q g := by
  unfold mmEnergy
  refine (mm_lintegral3_mono fun r x ω => ?_).trans (le_of_eq (mm_lintegral3_lincomb _ _
    ((hh.lift.pow_const 2).mul hq.lift).ennreal_ofReal
    ((hg.lift.pow_const 2).mul hq.lift).ennreal_ofReal ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top))
  have hq := hq0 r x ω
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg (a * h r x ω - b * g r x ω), mul_nonneg hq
    (sq_nonneg (a * h r x ω - b * g r x ω))]

/-- `E(c h) = c² E(h)`. -/
theorem mmEnergy_const_mul (h : ℝ → ℝ → Ω → ℝ) (c : ℝ) :
    mmEnergy μ T q (fun r x ω => c * h r x ω) = ENNReal.ofReal (c ^ 2) * mmEnergy μ T q h := by
  unfold mmEnergy
  rw [← mm_lintegral3_const_mul _ ENNReal.ofReal_ne_top]
  congr 1; funext ω; congr 1; funext r; congr 1; funext x
  rw [← ENNReal.ofReal_mul (sq_nonneg c)]
  congr 1; ring

/-- A bounded field has energy at most `K² 𝔼 ∫_0^T ∫ q`. -/
theorem mmEnergy_le_of_bdd (hq0 : ∀ r x ω, 0 ≤ q r x ω) {h : ℝ → ℝ → Ω → ℝ} {K : ℝ}
    (hK : ∀ r x ω, |h r x ω| ≤ K) :
    mmEnergy μ T q h ≤ ENNReal.ofReal (K ^ 2) *
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ := by
  unfold mmEnergy
  rw [← mm_lintegral3_const_mul _ ENNReal.ofReal_ne_top]
  refine mm_lintegral3_mono fun r x ω => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg K)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hq0 r x ω))
  have := hK r x ω
  nlinarith [abs_nonneg (h r x ω), sq_abs (h r x ω)]

/-! ### The bracket -/

/-- Symmetry of the bracket. -/
theorem mmBr_comm (q h g : ℝ → ℝ → Ω → ℝ) : mmBr q h g = mmBr q g h := by
  funext t ω; unfold mmBr
  congr 1; funext r; congr 1; funext x; ring

/-- `|∫_0^t ∫ q h g| ≤ ∫_0^T ∫ |q h g|` for `t ∈ [0, T]`. -/
theorem mm_enorm_mmBr_le (h g : ℝ → ℝ → Ω → ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (ω : Ω) :
    ‖mmBr q h g t ω‖ₑ ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖q r x ω * h r x ω * g r x ω‖ₑ := by
  unfold mmBr
  rw [intervalIntegral.integral_of_le ht.1]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono fun r => enorm_integral_le_lintegral_enorm _).trans ?_
  exact lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right ht.2))

/-- Almost surely, `∫_0^T ∫ |q h g| < ∞`. -/
theorem mm_ae_lintegral_lt_top [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) (hEh : mmEnergy μ T q h ≠ ∞)
    (hEg : mmEnergy μ T q g ≠ ∞) :
    ∀ᵐ ω ∂μ, ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖q r x ω * h r x ω * g r x ω‖ₑ < ∞ := by
  refine ae_lt_top (mm_measurable_lintegral _ ((hq.mul hh).mul hg).lift.enorm)
    (ne_top_of_le_ne_top ?_ (mm_lintegral_enorm_le hq hq0 hh hg one_ne_zero ENNReal.one_ne_top))
  simp only [inv_one, one_mul]
  exact ENNReal.add_ne_top.2 ⟨hEh, hEg⟩

/-- For a field `H` with a measurable lift and `∫_0^T ∫ |H(·,·,ω)| < ∞`: `H(r, ·, ω)` is
integrable for almost every `r ∈ [0, T]`, and `r ↦ ∫ H(r, x, ω) dx` is integrable on `[0, T]`. -/
private lemma mm_integrable_of_lt_top {H : ℝ → ℝ → Ω → ℝ}
    (hH : Measurable fun p : Ω × ℝ × ℝ => H (p.2.1.toNNReal : ℝ) p.2.2 p.1) {ω : Ω}
    (hω : ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖H r x ω‖ₑ < ∞) :
    (∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Integrable fun x => H r x ω) ∧
      MeasureTheory.IntegrableOn (fun r => ∫ x, H r x ω) (Set.Icc 0 T) := by
  have hm2 : Measurable fun y : ℝ × ℝ => H (y.1.toNNReal : ℝ) y.2 ω :=
    hH.comp measurable_prodMk_left
  have hIcc : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), r ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hinner : Measurable fun r : ℝ => ∫⁻ x, ‖H (r.toNNReal : ℝ) x ω‖ₑ :=
    hm2.enorm.lintegral_prod_right'
  have heq : ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖H r x ω‖ₑ =
      ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖H (r.toNNReal : ℝ) x ω‖ₑ :=
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by simp only [Real.coe_toNNReal r hr.1]
  refine ⟨?_, ?_, ?_⟩
  · have hfin := ae_lt_top' hinner.aemeasurable (heq ▸ hω).ne
    filter_upwards [hfin, hIcc] with r h1 h2
    have hmx : Measurable fun x => H (r.toNNReal : ℝ) x ω := hm2.comp measurable_prodMk_left
    rw [Real.coe_toNNReal r h2.1] at h1 hmx
    exact ⟨hmx.aestronglyMeasurable, h1⟩
  · have hsm : StronglyMeasurable fun r : ℝ => ∫ x, H (r.toNNReal : ℝ) x ω :=
      hm2.stronglyMeasurable.integral_prod_right'
    refine hsm.aestronglyMeasurable.congr ?_
    filter_upwards [hIcc] with r hr
    simp only [Real.coe_toNNReal r hr.1]
  · exact lt_of_le_of_lt (lintegral_mono fun r => enorm_integral_le_lintegral_enorm _) hω

/-- Almost surely the bracket is a genuine iterated integral: `q h g (r, ·, ω)` is integrable
for almost every `r ∈ [0, T]` and `r ↦ ∫ q h g dx` is integrable on `[0, T]`. -/
theorem mm_ae_integrable [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) (hEh : mmEnergy μ T q h ≠ ∞)
    (hEg : mmEnergy μ T q g ≠ ∞) :
    ∀ᵐ ω ∂μ, (∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Integrable fun x => q r x ω * h r x ω * g r x ω) ∧
      MeasureTheory.IntegrableOn (fun r => ∫ x, q r x ω * h r x ω * g r x ω) (Set.Icc 0 T) := by
  filter_upwards [mm_ae_lintegral_lt_top hq hq0 hh hg hEh hEg] with ω hω
  exact mm_integrable_of_lt_top (H := fun r x ω => q r x ω * h r x ω * g r x ω)
    ((hq.mul hh).mul hg).lift hω

/-- Almost surely the bracket is continuous and of bounded variation on `[0, T]`. -/
theorem mmBr_ae_good [SFinite μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) (hEh : mmEnergy μ T q h ≠ ∞)
    (hEg : mmEnergy μ T q g ≠ ∞) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t => mmBr q h g t ω) (Set.Icc 0 T) ∧
      BoundedVariationOn (fun t => mmBr q h g t ω) (Set.Icc 0 T) := by
  filter_upwards [mm_ae_integrable hq hq0 hh hg hEh hEg] with ω hω
  have hii : IntervalIntegrable (fun r => ∫ x, q r x ω * h r x ω * g r x ω) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hω.2
  have hac := hii.absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) Set.left_mem_uIcc
  have e : (fun t => mmBr q h g t ω) =
      fun t => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * h r x ω * g r x ω := rfl
  rw [e]
  have h1 := hac.continuousOn
  have h2 := hac.boundedVariationOn
  rw [Set.uIcc_of_le hT] at h1 h2
  exact ⟨h1, h2⟩

/-- The bracket is integrable at each time of `[0, T]`. -/
theorem integrable_mmBr [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h g : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) (hEh : mmEnergy μ T q h ≠ ∞)
    (hEg : mmEnergy μ T q g ≠ ∞) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    Integrable (mmBr q h g t) μ := by
  have hH := ((hq.mul hh).mul hg).lift
  set H : Ω × ℝ × ℝ → ℝ := fun p => q (p.2.1.toNNReal : ℝ) p.2.2 p.1 *
    h (p.2.1.toNNReal : ℝ) p.2.2 p.1 * g (p.2.1.toNNReal : ℝ) p.2.2 p.1 with hHdef
  have hH2 : StronglyMeasurable fun z : Ω × ℝ => ∫ x, H (z.1, z.2, x) :=
    (hH.comp (by fun_prop : Measurable fun z : (Ω × ℝ) × ℝ => (z.1.1, z.1.2, z.2))
      ).stronglyMeasurable.integral_prod_right'
  have hH3 : StronglyMeasurable fun ω =>
      ∫ r, (∫ x, H (ω, r, x)) ∂(volume.restrict (Set.Ioc 0 t)) :=
    hH2.integral_prod_right' (f := fun z : Ω × ℝ => ∫ x, H (z.1, z.2, x))
  refine ⟨hH3.aestronglyMeasurable.congr (ae_of_all _ fun ω => ?_), ?_⟩
  · simp only [mmBr, intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [hHdef, Real.coe_toNNReal r hr.1.le]
  · refine lt_of_le_of_lt (lintegral_mono fun ω => mm_enorm_mmBr_le h g ht ω) ?_
    refine lt_of_le_of_lt (mm_lintegral_enorm_le hq hq0 hh hg one_ne_zero ENNReal.one_ne_top) ?_
    simp only [inv_one, one_mul]
    exact ENNReal.add_lt_top.2 ⟨hEh.lt_top, hEg.lt_top⟩

/-- **Linearity**: almost surely, for every `t ∈ [0, T]`,
`∫_0^t ∫ q (a h₁ + b h₂) g = a ∫_0^t ∫ q h₁ g + b ∫_0^t ∫ q h₂ g`. -/
theorem mmBr_lincomb_ae [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h₁ h₂ g : ℝ → ℝ → Ω → ℝ} (hh₁ : MMPred 𝒢 h₁) (hh₂ : MMPred 𝒢 h₂) (hg : MMPred 𝒢 g)
    (hE₁ : mmEnergy μ T q h₁ ≠ ∞) (hE₂ : mmEnergy μ T q h₂ ≠ ∞) (hEg : mmEnergy μ T q g ≠ ∞)
    (a b : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      mmBr q (fun r x ω => a * h₁ r x ω + b * h₂ r x ω) g t ω =
        a * mmBr q h₁ g t ω + b * mmBr q h₂ g t ω := by
  filter_upwards [mm_ae_integrable hq hq0 hh₁ hg hE₁ hEg, mm_ae_integrable hq hq0 hh₂ hg hE₂ hEg]
    with ω h1 h2 t ht
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc 0 T :=
    Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right ht.2)
  have ii : ∀ {f : ℝ → ℝ}, MeasureTheory.IntegrableOn f (Set.Icc 0 T) →
      IntervalIntegrable f volume 0 t := fun hf =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hf.mono_set hsub)
  unfold mmBr
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((ii h1.2).const_mul a) ((ii h2.2).const_mul b)]
  refine intervalIntegral.integral_congr_ae ?_
  have h1' := (ae_restrict_iff' measurableSet_Icc).1 h1.1
  have h2' := (ae_restrict_iff' measurableSet_Icc).1 h2.1
  filter_upwards [h1', h2'] with r hr1 hr2 hr
  rw [Set.uIoc_of_le ht.1] at hr
  have i1 := hr1 (hsub hr)
  have i2 := hr2 (hsub hr)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a)
    (i2.const_mul b)]
  congr 1; funext x; ring

/-- Almost surely, `∫_0^t ∫ q (h₁ - h₂) g = ∫_0^t ∫ q h₁ g - ∫_0^t ∫ q h₂ g` on `[0, T]`. -/
theorem mmBr_sub_ae [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h₁ h₂ g : ℝ → ℝ → Ω → ℝ} (hh₁ : MMPred 𝒢 h₁) (hh₂ : MMPred 𝒢 h₂) (hg : MMPred 𝒢 g)
    (hE₁ : mmEnergy μ T q h₁ ≠ ∞) (hE₂ : mmEnergy μ T q h₂ ≠ ∞) (hEg : mmEnergy μ T q g ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      mmBr q (fun r x ω => h₁ r x ω - h₂ r x ω) g t ω = mmBr q h₁ g t ω - mmBr q h₂ g t ω := by
  filter_upwards [mmBr_lincomb_ae hq hq0 hh₁ hh₂ hg hE₁ hE₂ hEg 1 (-1)] with ω hω t ht
  have e : (fun r x ω => h₁ r x ω - h₂ r x ω) = fun r x ω => 1 * h₁ r x ω + -1 * h₂ r x ω := by
    funext r x ω; ring
  rw [e, hω t ht]; ring

/-- Almost surely, `∫_0^t ∫ q (h₁ + h₂) g = ∫_0^t ∫ q h₁ g + ∫_0^t ∫ q h₂ g` on `[0, T]`. -/
theorem mmBr_add_ae [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {h₁ h₂ g : ℝ → ℝ → Ω → ℝ} (hh₁ : MMPred 𝒢 h₁) (hh₂ : MMPred 𝒢 h₂) (hg : MMPred 𝒢 g)
    (hE₁ : mmEnergy μ T q h₁ ≠ ∞) (hE₂ : mmEnergy μ T q h₂ ≠ ∞) (hEg : mmEnergy μ T q g ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      mmBr q (fun r x ω => h₁ r x ω + h₂ r x ω) g t ω = mmBr q h₁ g t ω + mmBr q h₂ g t ω := by
  filter_upwards [mmBr_lincomb_ae hq hq0 hh₁ hh₂ hg hE₁ hE₂ hEg 1 1] with ω hω t ht
  have e : (fun r x ω => h₁ r x ω + h₂ r x ω) = fun r x ω => 1 * h₁ r x ω + 1 * h₂ r x ω := by
    funext r x ω; ring
  rw [e, hω t ht]; ring

/-- **Continuity of the bracket for the energy**: if `E(h_k - h) → 0`, then
`𝔼 |∫_0^t ∫ q h_k g - ∫_0^t ∫ q h g| → 0` for every `t ∈ [0, T]`. -/
theorem tendsto_mmBr_sub [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {hs : ℕ → ℝ → ℝ → Ω → ℝ} {h g : ℝ → ℝ → Ω → ℝ} (hhs : ∀ k, MMPred 𝒢 (hs k))
    (hh : MMPred 𝒢 h) (hg : MMPred 𝒢 g) (hEs : ∀ k, mmEnergy μ T q (hs k) ≠ ∞)
    (hEh : mmEnergy μ T q h ≠ ∞) (hEg : mmEnergy μ T q g ≠ ∞)
    (hlim : Tendsto (fun k => mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω)) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    Tendsto (fun k => ∫⁻ ω, ‖mmBr q (hs k) g t ω - mmBr q h g t ω‖ₑ ∂μ) atTop (𝓝 0) := by
  refine StochIntAux.tendsto_zero_of_le_lam hlim (tendsto_const_nhds (x := mmEnergy μ T q g))
    hEg fun l hl0 hlt => Eventually.of_forall fun k => ?_
  calc ∫⁻ ω, ‖mmBr q (hs k) g t ω - mmBr q h g t ω‖ₑ ∂μ
      = ∫⁻ ω, ‖mmBr q (fun r x ω => hs k r x ω - h r x ω) g t ω‖ₑ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [mmBr_sub_ae hq hq0 (hhs k) hh hg (hEs k) hEh hEg] with ω hω
        rw [hω t ht]
    _ ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x,
          ‖q r x ω * (hs k r x ω - h r x ω) * g r x ω‖ₑ) ∂μ :=
        lintegral_mono fun ω => mm_enorm_mmBr_le _ g ht ω
    _ ≤ _ := mm_lintegral_enorm_le hq hq0 ((hhs k).sub hh) hg hl0 hlt

/-- `∫_0^u 𝟙_{(s,t]} f = ∫_0^{u ∧ t} f - ∫_0^{u ∧ s} f` for `0 ≤ s ≤ t`, `0 ≤ u ≤ T`, `f`
integrable on `[0, T]`. -/
private lemma mm_integral_indicator_Ioc {f : ℝ → ℝ} (hf : MeasureTheory.IntegrableOn f
    (Set.Icc 0 T)) {s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hu : u ∈ Set.Icc 0 T) :
    ∫ r in (0 : ℝ)..u, Set.indicator (Set.Ioc s t) f r =
      (∫ r in (0 : ℝ)..min u t, f r) - ∫ r in (0 : ℝ)..min u s, f r := by
  have ii : ∀ v ∈ Set.Icc (0 : ℝ) T, IntervalIntegrable f volume 0 v := fun v hv =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hv.1).2 (hf.mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right hv.2)))
  have hmt : min u t ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_min hu.1 (hs.trans hst), (min_le_left _ _).trans hu.2⟩
  have hms : min u s ∈ Set.Icc (0 : ℝ) T := ⟨le_min hu.1 hs, (min_le_left _ _).trans hu.2⟩
  rw [intervalIntegral.integral_interval_sub_left (ii _ hmt) (ii _ hms),
    intervalIntegral.integral_of_le hu.1, setIntegral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (min_le_min_left u hst), Set.Ioc_inter_Ioc,
    max_eq_right hs]
  rcases le_total s u with hsu | hus
  · rw [min_eq_right hsu]
  · rw [min_eq_left hus, min_eq_left (hus.trans hst), Set.Ioc_eq_empty (not_lt.2 hus),
      Set.Ioc_self]

/-- **Bracket of a simple integrand**: almost surely, for `u ∈ [0, T]`,
`∫_0^u ∫ q (a 𝟙_{(s,t]} φ) g = a (∫_0^{u ∧ t} ∫ q φ g - ∫_0^{u ∧ s} ∫ q φ g)`. -/
theorem mmBr_block_ae [SFinite μ] (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    {φ : ℝ → ℝ} (hφ : MMPred 𝒢 fun _ x _ => φ x) (hEφ : mmEnergy μ T q (fun _ x _ => φ x) ≠ ∞)
    {g : ℝ → ℝ → Ω → ℝ} (hg : MMPred 𝒢 g) (hEg : mmEnergy μ T q g ≠ ∞) (s t : ℝ≥0)
    (hst : s ≤ t) (a : Ω → ℝ) :
    ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc (0 : ℝ) T,
      mmBr q (fun r x ω => if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0) g u ω =
        a ω * (mmBr q (fun _ x _ => φ x) g (min u t) ω -
          mmBr q (fun _ x _ => φ x) g (min u s) ω) := by
  filter_upwards [mm_ae_integrable hq hq0 hφ hg hEφ hEg] with ω hω u hu
  have e : ∀ r, (∫ x, q r x ω * (if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0) * g r x ω) =
      a ω * Set.indicator (Set.Ioc (s : ℝ) t) (fun r => ∫ x, q r x ω * φ x * g r x ω) r := by
    intro r
    simp only [Set.indicator_apply, Set.mem_Ioc]
    split_ifs with hr
    · rw [← integral_const_mul]; congr 1; funext x; ring
    · simp
  unfold mmBr
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact mm_integral_indicator_Ioc hω.2 s.2 (NNReal.coe_le_coe.2 hst) hu

end QSSEPtoKPZ
