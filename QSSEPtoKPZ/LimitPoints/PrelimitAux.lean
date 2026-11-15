/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PrelimitMeas
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Generic tools for the prelimit laws (task Q1b)

Auxiliary results for `LimitPoints/PrelimitLaw.lean`:

* measurability of `a ↦ ∫_a^b F(γ, s) ds` and of `{γ : s ↦ F(γ,s) integrable on [a,b]}` for a
  jointly measurable `F` (`prelimAux_measurable_intervalIntegral`,
  `prelimAux_measurableSet_intervalIntegrable`);
* density of the rationals: a function continuous on `[a,b]` and `≤ 0` at the rationals of
  `(a,b)` is `≤ 0` on `[a,b]` (`prelimAux_le_of_rat`), and the monotone version
  (`prelimAux_monotoneOn_of_rat`);
* a martingale (with bracket) for a filtration is one for a smaller filtration to which it is
  adapted (`prelimAux_hasBracket_of_le`, tower property).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### Measurability of integrals in a parameter -/

section Meas

variable {α : Type*} [MeasurableSpace α]

/-- `a ↦ ∫_s F(a,t) dt` is measurable for a jointly measurable `F`. -/
theorem prelimAux_measurable_setIntegral {f : α × ℝ → ℝ} (hf : Measurable f) (s : Set ℝ) :
    Measurable fun a => ∫ t in s, f (a, t) :=
  (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict s)).measurable

/-- `a ↦ ∫_a^b F(γ,s) ds` is measurable when `F(γ, ·)` agrees on `(a,b]` with a jointly
measurable function. -/
theorem prelimAux_measurable_intervalIntegral {f : α × ℝ → ℝ} (hf : Measurable f)
    {F : α → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hFf : ∀ γ, ∀ s ∈ Ioc a b, F γ s = f (γ, s)) :
    Measurable fun γ => ∫ s in a..b, F γ s := by
  have e : (fun γ => ∫ s in a..b, F γ s) = fun γ => ∫ s in Ioc a b, f (γ, s) := by
    funext γ
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun measurableSet_Ioc (hFf γ)
  rw [e]
  exact prelimAux_measurable_setIntegral hf _

/-- `{γ : F(γ, ·) integrable on [a,b]}` is measurable when `F(γ, ·)` agrees on `(a,b]` with a
jointly measurable function. -/
theorem prelimAux_measurableSet_intervalIntegrable {f : α × ℝ → ℝ} (hf : Measurable f)
    {F : α → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hFf : ∀ γ, ∀ s ∈ Ioc a b, F γ s = f (γ, s)) :
    MeasurableSet {γ | IntervalIntegrable (F γ) volume a b} := by
  have e : {γ | IntervalIntegrable (F γ) volume a b} =
      {γ | ∫⁻ s in Ioc a b, ‖f (γ, s)‖ₑ < ∞} := by
    ext γ
    simp only [mem_ofPred_eq, intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hcongr : IntegrableOn (F γ) (Ioc a b) ↔ IntegrableOn (fun s => f (γ, s)) (Ioc a b) :=
      integrableOn_congr_fun (hFf γ) measurableSet_Ioc
    rw [hcongr]
    exact ⟨fun h => h.2, fun h => ⟨(hf.comp measurable_prodMk_left).aestronglyMeasurable, h⟩⟩
  rw [e]
  exact measurableSet_lt (hf.enorm.lintegral_prod_right') measurable_const

/-- Interval integrability is a property of the values on `[a,b]`. -/
theorem prelimAux_intervalIntegrable_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (h : EqOn f g (uIcc a b)) :
    IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hf).congr_fun (h.mono uIoc_subset_uIcc)
    measurableSet_uIoc)

end Meas

/-! ### Density of the rationals -/

/-- The rationals of `(a,b)` are dense in `[a,b]`. -/
theorem prelimAux_Icc_subset_closure {a b : ℝ} (hab : a < b) :
    Icc a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) := by
  rw [← closure_Ioo hab.ne]
  exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
    isClosed_closure

/-- A function continuous on `[a,b]` and `≤ 0` at the rationals of `(a,b)` is `≤ 0` on `[a,b]`. -/
theorem prelimAux_le_of_rat {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (h : ∀ q : ℚ, (q : ℝ) ∈ Ioo a b → g q ≤ 0) : ∀ t ∈ Icc a b, g t ≤ 0 := by
  intro t ht
  have hcl : closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) ⊆ Icc a b := by
    refine closure_minimal (fun x hx => Ioo_subset_Icc_self hx.1) isClosed_Icc
  refine le_on_closure (f := g) (g := fun _ => 0) (fun x hx => ?_)
    (hg.mono hcl) continuousOn_const (prelimAux_Icc_subset_closure hab ht)
  obtain ⟨hx, q, rfl⟩ := hx
  exact h q hx

/-- A function continuous on `[0,T]` and nondecreasing on the rationals of `[0,T]` is
nondecreasing on `[0,T]`. -/
theorem prelimAux_monotoneOn_of_rat {T : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T))
    (h : ∀ q r : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ r → (r : ℝ) ≤ T → g q ≤ g r) :
    MonotoneOn g (Icc 0 T) := by
  -- first with a rational left end
  have h1 : ∀ q : ℚ, ∀ t, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t → t ≤ T → g q ≤ g t := by
    intro q t hq hqt htT
    rcases hqt.lt_or_eq with hlt | heq
    · have := prelimAux_le_of_rat hlt (g := fun x => g q - g x)
        (continuousOn_const.sub (hg.mono (Icc_subset_Icc hq htT)))
        (fun r hr => sub_nonpos.2 (h q r hq hr.1.le (hr.2.le.trans htT))) t ⟨hlt.le, le_rfl⟩
      linarith
    · rw [heq]
  intro s hs t ht hst
  rcases hst.lt_or_eq with hlt | heq
  · have := prelimAux_le_of_rat hlt (g := fun x => g x - g t)
      ((hg.mono (Icc_subset_Icc hs.1 ht.2)).sub continuousOn_const)
      (fun q hq => sub_nonpos.2 (h1 q t (hs.1.trans hq.1.le) hq.2.le ht.2)) s ⟨le_rfl, hlt.le⟩
    linarith
  · rw [heq]

/-! ### Martingales for a smaller filtration -/

section Filt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Tower property: if `𝔼[f | m₂] = g` and `g` is `m₁`-measurable, `m₁ ≤ m₂`, then
`𝔼[f | m₁] = g`. -/
theorem prelimAux_condExp_of_le {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hfg : μ[f | m₂] =ᵐ[μ] g) (hg : Measurable[m₁] g) (hgi : Integrable g μ) :
    μ[f | m₁] =ᵐ[μ] g :=
  (condExp_condExp_of_le h12 h2).symm.trans ((condExp_congr_ae hfg).trans
    (EventuallyEq.of_eq (condExp_of_stronglyMeasurable (h12.trans h2) hg.stronglyMeasurable hgi)))

/-- **Restriction of the filtration.** A continuous `L²` martingale with bracket `A` for `𝓕`,
adapted (with `A`) to a smaller filtration `𝓖`, is one for `𝓖`. -/
theorem prelimAux_hasBracket_of_le {T : ℝ} {𝓕 𝓖 : Filtration ℝ≥0 mΩ} {M A : ℝ → Ω → ℝ}
    (h : HasBracket T 𝓕 M A μ) (hle : ∀ t, 𝓖 t ≤ 𝓕 t)
    (hM : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable[𝓖 t] (M t))
    (hA : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Measurable[𝓖 t] (A t)) : HasBracket T 𝓖 M A μ := by
  have hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (M t) μ := fun t ht =>
    (h.memLp t ht).integrable one_le_two
  have hint2 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (fun ω => M t ω ^ 2 - A t ω) μ :=
    fun t ht => (h.memLp t ht).integrable_sq.sub (h.integrable_bracket t ht)
  exact { toIsCL2Mart := ⟨h.cont, h.memLp, fun s t hst ht =>
            prelimAux_condExp_of_le (hle s) (𝓕.le s) (h.condExp s t hst ht)
              (hM s ((NNReal.coe_le_coe.2 hst).trans ht))
              (hint s ((NNReal.coe_le_coe.2 hst).trans ht))⟩
          integrable_bracket := h.integrable_bracket
          zero := h.zero
          mono := h.mono
          cont_bracket := h.cont_bracket
          condExp_sq := fun s t hst ht =>
            prelimAux_condExp_of_le (hle s) (𝓕.le s) (h.condExp_sq s t hst ht)
              (((hM s ((NNReal.coe_le_coe.2 hst).trans ht)).pow_const 2).sub
                (hA s ((NNReal.coe_le_coe.2 hst).trans ht)))
              (hint2 s ((NNReal.coe_le_coe.2 hst).trans ht)) }

end Filt

end QSSEPtoKPZ
