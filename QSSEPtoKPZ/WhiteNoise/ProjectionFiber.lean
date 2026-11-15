/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.NoiseFiltration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Fiberwise conditional expectation on a product space (task G6)

Let `(Ω, 𝓕, ν)` and `(T, 𝓣, τ)` be probability spaces, `𝒢 ⊆ 𝓕` a sub-σ-algebra and
`F ∈ L¹(ν ⊗ τ)`. The conditional expectation of `F` given `𝒢 ⊗ 𝓣` is, for `τ`-almost every `t`,
a version of the conditional expectation of the section `F(·, t)` given `𝒢`:

  `𝔼_{ν⊗τ}[F | 𝒢 ⊗ 𝓣](·, t) = 𝔼_ν[F(·, t) | 𝒢]`   `ν`-a.s., for `τ`-a.e. `t`
  (`noiseFiber_condExp`).

The exceptional set of `t` must not depend on the events of `𝒢` (which need not be countably
generated), so the proof is by approximation: the property holds for products `c(ω) b(t)`
(`noiseFiber_condExp_fst` and the pull-out property), is linear, and is closed under `L¹`
limits (along a subsequence the fiber distances tend to `0` for almost every `t`); the
π-λ theorem gives it for indicators of measurable sets, and `Integrable.induction` for all
integrable `F`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω T : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {mT : MeasurableSpace T}
  {ν : Measure Ω} [IsProbabilityMeasure ν] {τ : Measure T} [IsProbabilityMeasure τ]

/-- `𝒢 ⊗ 𝓣 ≤ 𝓕 ⊗ 𝓣` for `𝒢 ≤ 𝓕`. -/
theorem noiseFiber_prod_le (h𝒢 : 𝒢 ≤ mΩ) :
    𝒢.prod mT ≤ (inferInstance : MeasurableSpace (Ω × T)) :=
  sup_le_sup (MeasurableSpace.comap_mono h𝒢) le_rfl

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] in
/-- A property holding `ν ⊗ τ`-almost everywhere holds, for `τ`-a.e. `t`, at `(ω, t)` for
`ν`-a.e. `ω`. -/
theorem noiseFiber_ae_ae [SFinite ν] [SFinite τ] {p : Ω × T → Prop}
    (h : ∀ᵐ z ∂ν.prod τ, p z) : ∀ᵐ t ∂τ, ∀ᵐ ω ∂ν, p (ω, t) :=
  Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := τ) (ν := ν)).quasiMeasurePreserving.ae h)

/-- **Product case**: `𝔼_{ν⊗τ}[c(ω) | 𝒢 ⊗ 𝓣] = 𝔼_ν[c | 𝒢](ω)`. -/
theorem noiseFiber_condExp_fst (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → ℝ} (hc : Integrable c ν) :
    (ν.prod τ)[fun z => c z.1 | 𝒢.prod mT] =ᵐ[ν.prod τ] fun z => ν[c | 𝒢] z.1 := by
  have hm := noiseFiber_prod_le (mT := mT) h𝒢
  have hfst : Measurable[𝒢.prod mT, 𝒢] (Prod.fst : Ω × T → Ω) :=
    measurable_iff_comap_le.2 le_sup_left
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hc.comp_fst τ)
    (fun s _ _ => (integrable_condExp.comp_fst τ).integrableOn) (fun E hE _ => ?_)
    ((stronglyMeasurable_condExp.comp_measurable hfst).aestronglyMeasurable)).symm
  have key : ∀ g : Ω → ℝ, Integrable g ν →
      ∫ z in E, g z.1 ∂(ν.prod τ) = ∫ ω, τ.real (Prod.mk ω ⁻¹' E) * g ω ∂ν := by
    intro g hg
    rw [← integral_indicator (hm _ hE), integral_prod _ ((hg.comp_fst τ).indicator (hm _ hE))]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have e : (fun t => E.indicator (fun z => g z.1) (ω, t)) =
        (Prod.mk ω ⁻¹' E).indicator (fun _ => g ω) := by
      funext t
      rfl
    simp only [e]
    rw [integral_indicator_const _ (measurable_prodMk_left (hm _ hE)), smul_eq_mul]
  have hk : StronglyMeasurable[𝒢] fun ω => τ.real (Prod.mk ω ⁻¹' E) :=
    ((@measurable_measure_prodMk_left Ω T 𝒢 mT τ _ E hE).ennreal_toReal).stronglyMeasurable
  have hkb : ∀ ω, ‖τ.real (Prod.mk ω ⁻¹' E)‖ ≤ 1 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hkc : Integrable (fun ω => τ.real (Prod.mk ω ⁻¹' E) * c ω) ν :=
    hc.bdd_mul (hk.mono h𝒢).aestronglyMeasurable (ae_of_all _ hkb)
  rw [key _ integrable_condExp, key _ hc]
  calc ∫ ω, τ.real (Prod.mk ω ⁻¹' E) * ν[c | 𝒢] ω ∂ν
      = ∫ ω, ν[fun ω => τ.real (Prod.mk ω ⁻¹' E) * c ω | 𝒢] ω ∂ν :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hk hkc hc).symm
    _ = _ := integral_condExp h𝒢

/-- The fiberwise property of `F`: for `τ`-a.e. `t`, `𝔼[F | 𝒢 ⊗ 𝓣](·, t) = 𝔼[F(·, t) | 𝒢]`. -/
private def noiseFiberProp (ν : Measure Ω) (τ : Measure T) (F : Ω × T → ℝ) : Prop :=
  ∀ᵐ t ∂τ, (fun ω => (ν.prod τ)[F | 𝒢.prod mT] (ω, t)) =ᵐ[ν] ν[fun ω => F (ω, t) | 𝒢]

/-- The fiberwise property for products `c(ω) b(t)`, `b` bounded. -/
private lemma noiseFiber_rect (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → ℝ} (hc : Integrable c ν) {b : T → ℝ}
    (hb : Measurable b) {C : ℝ} (hbC : ∀ t, ‖b t‖ ≤ C) :
    noiseFiberProp (𝒢 := 𝒢) ν τ (fun z => c z.1 * b z.2) := by
  have hsnd' : Measurable[𝒢.prod mT, mT] (Prod.snd : Ω × T → T) :=
    measurable_iff_comap_le.2 le_sup_right
  have hsnd : StronglyMeasurable[𝒢.prod mT] (fun z : Ω × T => b z.2) :=
    (hb.comp hsnd').stronglyMeasurable
  have h1 : (ν.prod τ)[fun z => c z.1 * b z.2 | 𝒢.prod mT] =ᵐ[ν.prod τ]
      fun z => b z.2 * ν[c | 𝒢] z.1 := by
    have e : (fun z : Ω × T => c z.1 * b z.2) = (fun z => b z.2) * (fun z => c z.1) := by
      funext z
      simp [mul_comm]
    rw [e]
    have hint : Integrable ((fun z : Ω × T => b z.2) * fun z => c z.1) (ν.prod τ) :=
      (hc.comp_fst τ).bdd_mul (hb.comp measurable_snd).aestronglyMeasurable
        (ae_of_all _ fun z => hbC z.2)
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hsnd hint (hc.comp_fst τ),
      noiseFiber_condExp_fst h𝒢 hc] with z h1 h2
    rw [h1, Pi.mul_apply, h2]
  filter_upwards [noiseFiber_ae_ae h1] with t ht
  have e2 : (fun ω => c (ω, t).1 * b (ω, t).2) = b t • c := by
    funext ω
    simp [mul_comm]
  rw [e2]
  filter_upwards [ht, condExp_smul (b t) c 𝒢] with ω h1 h2
  rw [h1, h2]
  simp

/-- The fiberwise property is additive. -/
private lemma noiseFiber_add {F G : Ω × T → ℝ} (hF : Integrable F (ν.prod τ))
    (hG : Integrable G (ν.prod τ)) (hPF : noiseFiberProp (𝒢 := 𝒢) ν τ F)
    (hPG : noiseFiberProp (𝒢 := 𝒢) ν τ G) : noiseFiberProp (𝒢 := 𝒢) ν τ (F + G) := by
  filter_upwards [noiseFiber_ae_ae (condExp_add hF hG (𝒢.prod mT)), hPF, hPG,
    hF.prod_left_ae, hG.prod_left_ae] with t h1 h2 h3 h4 h5
  filter_upwards [h1, h2, h3, condExp_add h4 h5 𝒢] with ω e1 e2 e3 e4
  have e : (fun ω => (F + G) (ω, t)) = (fun ω => F (ω, t)) + fun ω => G (ω, t) := rfl
  rw [e, e4, e1, Pi.add_apply, Pi.add_apply, e2, e3]

/-- The fiberwise property is stable under scalar multiplication. -/
private lemma noiseFiber_smul {F : Ω × T → ℝ} (c : ℝ) (hPF : noiseFiberProp (𝒢 := 𝒢) ν τ F) :
    noiseFiberProp (𝒢 := 𝒢) ν τ (c • F) := by
  filter_upwards [noiseFiber_ae_ae (condExp_smul (μ := ν.prod τ) c F (𝒢.prod mT)), hPF] with t h1 h2
  filter_upwards [h1, h2, condExp_smul c (fun ω => F (ω, t)) 𝒢] with ω e1 e2 e3
  have e : (fun ω => (c • F) (ω, t)) = c • fun ω => F (ω, t) := rfl
  rw [e, e3, e1, Pi.smul_apply, Pi.smul_apply, e2]

/-- The fiberwise property only depends on the almost-everywhere class of `F`. -/
private lemma noiseFiber_congr {F G : Ω × T → ℝ} (hFG : F =ᵐ[ν.prod τ] G)
    (hPF : noiseFiberProp (𝒢 := 𝒢) ν τ F) : noiseFiberProp (𝒢 := 𝒢) ν τ G := by
  filter_upwards [noiseFiber_ae_ae (ν := ν) (τ := τ) (condExp_congr_ae (m := 𝒢.prod mT) hFG), hPF,
    noiseFiber_ae_ae hFG] with t h1 h2 h3
  have h3' : (fun ω => F (ω, t)) =ᵐ[ν] fun ω => G (ω, t) := h3
  filter_upwards [h1, h2, condExp_congr_ae (m := 𝒢) h3'] with ω e1 e2 e3
  rw [← e1, e2, e3]

/-- Closure of the fiberwise property under `L¹` limits (strongly measurable case). -/
private lemma noiseFiber_closed_aux (h𝒢 : 𝒢 ≤ mΩ) {Fs : ℕ → Ω × T → ℝ} {F : Ω × T → ℝ}
    (hFs : ∀ n, StronglyMeasurable (Fs n)) (hF : StronglyMeasurable F)
    (hFsi : ∀ n, Integrable (Fs n) (ν.prod τ)) (hFi : Integrable F (ν.prod τ))
    (hlim : Tendsto (fun n => eLpNorm (Fs n - F) 1 (ν.prod τ)) atTop (𝓝 0))
    (hP : ∀ n, noiseFiberProp (𝒢 := 𝒢) ν τ (Fs n)) : noiseFiberProp (𝒢 := 𝒢) ν τ F := by
  have hm := noiseFiber_prod_le (mT := mT) h𝒢
  let A : ℕ → T → ℝ≥0∞ := fun n t => ∫⁻ ω, ‖Fs n (ω, t) - F (ω, t)‖ₑ ∂ν
  let B : ℕ → T → ℝ≥0∞ := fun n t =>
    ∫⁻ ω, ‖(ν.prod τ)[Fs n | 𝒢.prod mT] (ω, t) - (ν.prod τ)[F | 𝒢.prod mT] (ω, t)‖ₑ ∂ν
  have hAm' : ∀ n, Measurable fun z : Ω × T => ‖Fs n z - F z‖ₑ := fun n =>
    ((hFs n).sub hF).measurable.enorm
  have hBm' : ∀ n, Measurable fun z : Ω × T =>
      ‖(ν.prod τ)[Fs n | 𝒢.prod mT] z - (ν.prod τ)[F | 𝒢.prod mT] z‖ₑ := fun n =>
    ((stronglyMeasurable_condExp.mono hm).sub (stronglyMeasurable_condExp.mono hm)).measurable.enorm
  have hAm : ∀ n, Measurable (A n) := fun n => (hAm' n).lintegral_prod_left'
  have hBm : ∀ n, Measurable (B n) := fun n => (hBm' n).lintegral_prod_left'
  have hAint : ∀ n, ∫⁻ t, A n t ∂τ = eLpNorm (Fs n - F) 1 (ν.prod τ) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm ((hFs n).sub hF).aestronglyMeasurable]
    simp only [Pi.sub_apply]
    rw [lintegral_prod_symm _ (hAm' n).aemeasurable]
  have hBint : ∀ n, ∫⁻ t, B n t ∂τ ≤ eLpNorm (Fs n - F) 1 (ν.prod τ) := by
    intro n
    have e : ∫⁻ t, B n t ∂τ =
        eLpNorm ((ν.prod τ)[Fs n | 𝒢.prod mT] - (ν.prod τ)[F | 𝒢.prod mT]) 1 (ν.prod τ) := by
      rw [eLpNorm_one_eq_lintegral_enorm
        ((stronglyMeasurable_condExp.mono hm).sub (stronglyMeasurable_condExp.mono hm)).aestronglyMeasurable]
      simp only [Pi.sub_apply]
      rw [lintegral_prod_symm _ (hBm' n).aemeasurable]
    rw [e, eLpNorm_congr_ae (condExp_sub (hFsi n) hFi (𝒢.prod mT)).symm]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hsub : ∀ k : ℕ, ∃ n, ∫⁻ t, (A n t + B n t) ∂τ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have h2 : Tendsto (fun n => 2 * eLpNorm (Fs n - F) 1 (ν.prod τ)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofNat_ne_top)
    obtain ⟨n, hn⟩ := (h2.eventually (ge_mem_nhds
      (ENNReal.pow_pos (by norm_num) k : (0 : ℝ≥0∞) < 2⁻¹ ^ k))).exists
    refine ⟨n, le_trans ?_ hn⟩
    rw [lintegral_add_left (hAm n), hAint n, two_mul]
    gcongr
    exact hBint n
  choose φ hφ using hsub
  have hDm : ∀ k, Measurable fun t => A (φ k) t + B (φ k) t := fun k =>
    (hAm (φ k)).add (hBm (φ k))
  have hsum : ∀ᵐ t ∂τ, ∑' k, (A (φ k) t + B (φ k) t) < ∞ := by
    refine ae_lt_top' (AEMeasurable.tsum fun k => (hDm k).aemeasurable) ?_
    rw [lintegral_tsum fun k => (hDm k).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφ)
    rw [ENNReal.tsum_geometric]
    norm_num
  filter_upwards [hsum, ae_all_iff.2 fun k => hP (φ k), hFi.prod_left_ae,
    ae_all_iff.2 fun n => (hFsi n).prod_left_ae] with t hts hPt hFt hFst
  have htend : Tendsto (fun k => A (φ k) t + B (φ k) t) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hts.ne
  have hsec : ∀ {G : Ω × T → ℝ}, StronglyMeasurable G →
      StronglyMeasurable fun ω => G (ω, t) := fun hG => hG.comp_measurable measurable_prodMk_right
  have hbound : ∀ k, eLpNorm ((fun ω => (ν.prod τ)[F | 𝒢.prod mT] (ω, t)) -
      ν[fun ω => F (ω, t) | 𝒢]) 1 ν ≤ A (φ k) t + B (φ k) t := by
    intro k
    have e : (fun ω => (ν.prod τ)[F | 𝒢.prod mT] (ω, t)) - ν[fun ω => F (ω, t) | 𝒢] =ᵐ[ν]
        ((fun ω => (ν.prod τ)[F | 𝒢.prod mT] (ω, t)) -
          fun ω => (ν.prod τ)[Fs (φ k) | 𝒢.prod mT] (ω, t)) +
        ν[(fun ω => Fs (φ k) (ω, t)) - fun ω => F (ω, t) | 𝒢] := by
      filter_upwards [hPt k, condExp_sub (hFst (φ k)) hFt 𝒢] with ω e1 e2
      simp only [Pi.add_apply, Pi.sub_apply] at e2 ⊢
      rw [e2, ← e1]
      ring
    rw [eLpNorm_congr_ae e, add_comm (A (φ k) t)]
    refine (eLpNorm_add_le le_rfl).trans (add_le_add ?_ ?_)
    · rw [eLpNorm_one_eq_lintegral_enorm
        ((hsec ((stronglyMeasurable_condExp (m := 𝒢.prod mT) (μ := ν.prod τ) (f := F)).mono hm)).sub
        (hsec ((stronglyMeasurable_condExp (m := 𝒢.prod mT) (μ := ν.prod τ)
          (f := Fs (φ k))).mono hm))).aestronglyMeasurable]
      refine le_of_eq (lintegral_congr fun ω => ?_)
      rw [Pi.sub_apply, enorm_sub_rev]
    · refine (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans (le_of_eq ?_)
      rw [eLpNorm_one_eq_lintegral_enorm ((hsec (hFs (φ k))).sub (hsec hF)).aestronglyMeasurable]
      rfl
  have h0 : eLpNorm ((fun ω => (ν.prod τ)[F | 𝒢.prod mT] (ω, t)) -
      ν[fun ω => F (ω, t) | 𝒢]) 1 ν = 0 :=
    le_antisymm (ge_of_tendsto' htend hbound) zero_le
  rw [eLpNorm_eq_zero_iff one_ne_zero] at h0
  filter_upwards [h0] with ω hω
  exact sub_eq_zero.1 hω

/-- Closure of the fiberwise property under `L¹` limits. -/
private lemma noiseFiber_closed (h𝒢 : 𝒢 ≤ mΩ) {Fs : ℕ → Ω × T → ℝ} {F : Ω × T → ℝ}
    (hFsi : ∀ n, Integrable (Fs n) (ν.prod τ)) (hFi : Integrable F (ν.prod τ))
    (hlim : Tendsto (fun n => eLpNorm (Fs n - F) 1 (ν.prod τ)) atTop (𝓝 0))
    (hP : ∀ n, noiseFiberProp (𝒢 := 𝒢) ν τ (Fs n)) : noiseFiberProp (𝒢 := 𝒢) ν τ F := by
  refine noiseFiber_congr hFi.1.ae_eq_mk.symm (noiseFiber_closed_aux h𝒢
    (Fs := fun n => (hFsi n).1.mk _) (fun n => (hFsi n).1.stronglyMeasurable_mk)
    hFi.1.stronglyMeasurable_mk (fun n => (hFsi n).congr (hFsi n).1.ae_eq_mk)
    (hFi.congr hFi.1.ae_eq_mk) ?_ (fun n => noiseFiber_congr (hFsi n).1.ae_eq_mk (hP n)))
  convert hlim using 2 with n
  exact eLpNorm_congr_ae (((hFsi n).1.ae_eq_mk.symm).sub hFi.1.ae_eq_mk.symm)

/-- The fiberwise property for indicators of measurable sets (π-λ theorem). -/
private lemma noiseFiber_indicator (h𝒢 : 𝒢 ≤ mΩ) {E : Set (Ω × T)} (hE : MeasurableSet E) :
    noiseFiberProp (𝒢 := 𝒢) ν τ (E.indicator fun _ => (1 : ℝ)) := by
  have hone : noiseFiberProp (𝒢 := 𝒢) ν τ (fun _ => (1 : ℝ)) := by
    have := noiseFiber_rect (τ := τ) h𝒢 (integrable_const (μ := ν) (1 : ℝ)) (measurable_const (a := (1 : ℝ)))
      (C := 1) (fun _ => by simp)
    simpa using this
  induction E, hE using MeasurableSpace.induction_on_inter generateFrom_prod.symm
    isPiSystem_prod with
  | empty =>
    have := noiseFiber_smul (𝒢 := 𝒢) (ν := ν) (τ := τ) 0 hone
    convert this using 1
    funext z
    simp
  | basic t ht =>
    obtain ⟨A, hA, B, hB, rfl⟩ := ht
    have := noiseFiber_rect (τ := τ) h𝒢 ((integrable_const (μ := ν) (1 : ℝ)).indicator hA)
      ((measurable_const (a := (1 : ℝ))).indicator hB) (C := 1)
      (fun t => by by_cases h : t ∈ B <;> simp [h])
    convert this using 1
    funext z
    by_cases h1 : z.1 ∈ A <;> by_cases h2 : z.2 ∈ B <;> simp [h1, h2]
  | compl t htm ih =>
    have := noiseFiber_add (integrable_const (1 : ℝ))
      (((integrable_const (1 : ℝ)).indicator htm).smul (-1 : ℝ)) hone (noiseFiber_smul (-1) ih)
    convert this using 1
    funext z
    by_cases h : z ∈ t <;> simp [h]
  | iUnion f hdisj hfm ih =>
    let U : ℕ → Set (Ω × T) := fun n => ⋃ i ∈ Finset.range n, f i
    have hUm : ∀ n, MeasurableSet (U n) := fun n =>
      Finset.measurableSet_biUnion _ fun i _ => hfm i
    have hU : ∀ n, noiseFiberProp (𝒢 := 𝒢) ν τ ((U n).indicator fun _ => (1 : ℝ)) := by
      intro n
      induction n with
      | zero =>
        have := noiseFiber_smul (𝒢 := 𝒢) (ν := ν) (τ := τ) 0 hone
        convert this using 1
        funext z
        simp [U]
      | succ n ihn =>
        have hd : Disjoint (U n) (f n) := by
          simp only [U, Set.disjoint_iUnion_left]
          intro i hi
          exact hdisj (Finset.mem_range.1 hi).ne
        have e : U (n + 1) = U n ∪ f n := by
          simp only [U, Finset.range_add_one, Finset.set_biUnion_insert]
          exact Set.union_comm _ _
        rw [e, Set.indicator_union_of_disjoint hd]
        exact noiseFiber_add ((integrable_const (1 : ℝ)).indicator (hUm n))
          ((integrable_const (1 : ℝ)).indicator (hfm n)) ihn (ih n)
    have hUU : ⋃ n, U n = ⋃ i, f i := by
      ext z
      simp only [U, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨n, i, -, hi⟩
        exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i + 1, i, Nat.lt_succ_self i, hi⟩
    refine noiseFiber_closed h𝒢 (fun n => (integrable_const (1 : ℝ)).indicator (hUm n))
      ((integrable_const (1 : ℝ)).indicator (MeasurableSet.iUnion hfm)) ?_ hU
    have hmono : Monotone U := fun m n hmn =>
      Set.biUnion_subset_biUnion_left (by simpa using Finset.range_mono hmn)
    have e : ∀ n, eLpNorm ((U n).indicator (fun _ => (1 : ℝ)) -
        (⋃ i, f i).indicator fun _ => (1 : ℝ)) 1 (ν.prod τ) =
        (ν.prod τ) ((⋃ i, f i) \ U n) := by
      intro n
      have hsub : U n ⊆ ⋃ i, f i := hUU ▸ Set.subset_iUnion U n
      have e1 : (U n).indicator (fun _ => (1 : ℝ)) - (⋃ i, f i).indicator (fun _ => (1 : ℝ)) =
          ((⋃ i, f i) \ U n).indicator fun _ => (-1 : ℝ) := by
        funext z
        by_cases h1 : z ∈ U n
        · simp [h1, hsub h1]
        · by_cases h2 : z ∈ ⋃ i, f i
          · have h3 : z ∈ (⋃ i, f i) \ U n := ⟨h2, h1⟩
            rw [Pi.sub_apply, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
              Set.indicator_of_mem h3]
            ring
          · simp [h1, h2]
      rw [e1, eLpNorm_indicator_const ((MeasurableSet.iUnion hfm).diff (hUm n)).nullMeasurableSet
        one_ne_zero ENNReal.one_ne_top]
      simp
    simp_rw [e]
    have hlim := tendsto_measure_iInter_atTop (μ := ν.prod τ)
      (s := fun n => (⋃ i, f i) \ U n)
      (fun n => ((MeasurableSet.iUnion hfm).diff (hUm n)).nullMeasurableSet)
      (fun m n hmn => Set.sdiff_subset_sdiff_right (hmono hmn)) ⟨0, measure_ne_top _ _⟩
    have h0 : (⋂ n, (⋃ i, f i) \ U n) = ∅ := by
      rw [← Set.sdiff_iUnion, hUU, Set.sdiff_self]
    rw [h0, measure_empty] at hlim
    exact hlim

/-- **Fiberwise conditional expectation.** For `F ∈ L¹(ν ⊗ τ)` and `τ`-a.e. `t`,
`𝔼_{ν⊗τ}[F | 𝒢 ⊗ 𝓣](·, t) = 𝔼_ν[F(·, t) | 𝒢]` `ν`-almost surely. -/
theorem noiseFiber_condExp (h𝒢 : 𝒢 ≤ mΩ) {F : Ω × T → ℝ} (hF : Integrable F (ν.prod τ)) :
    ∀ᵐ t ∂τ, (fun ω => (ν.prod τ)[F | 𝒢.prod mT] (ω, t)) =ᵐ[ν]
      ν[fun ω => F (ω, t) | 𝒢] := by
  refine Integrable.induction (noiseFiberProp (𝒢 := 𝒢) ν τ) ?_ ?_ ?_ ?_ hF
  · intro c s hs _
    have := noiseFiber_smul c (noiseFiber_indicator (ν := ν) (τ := τ) h𝒢 hs)
    convert this using 1
    funext z
    by_cases h : z ∈ s <;> simp [h]
  · intro f g _ hf hg hPf hPg
    exact noiseFiber_add hf hg hPf hPg
  · refine IsSeqClosed.isClosed fun fs f hfs hlim => ?_
    exact noiseFiber_closed h𝒢 (fun n => L1.integrable_coeFn (fs n)) (L1.integrable_coeFn f)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' fs f).1 hlim) hfs
  · intro f g hfg _ hPf
    exact noiseFiber_congr hfg hPf

end QSSEPtoKPZ
