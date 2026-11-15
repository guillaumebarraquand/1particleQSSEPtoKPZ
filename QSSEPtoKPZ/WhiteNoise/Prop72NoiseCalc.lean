/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Prop72NoiseDefs
public import QSSEPtoKPZ.WhiteNoise.WalshProcess

/-!
# Proposition 7.2, Step 2: covariations of the pieces of the white noise (task J1)

On `Ω × Ω''` with the product filtration `𝒢̄ = prodFiltration 𝒢 𝒢''`:

* `prop72NoiseK_pred`, `prop72NoiseK_energy`: the integrand `prop72NoiseK` of the part driven by
  the auxiliary noise is `𝒢̄`-predictable, with finite energy on every `[0, n]`;
* `prop72Noise_covMM`: two martingale-measure integrals `h · M`, `h' · M`, stopped at `T` and
  lifted to the product, have covariation `∫_0^{t ∧ T} ∫ q h h'` on every horizon ((7.10));
* `prop72Noise_covCross`: such an integral and a Walsh integral process against the auxiliary
  noise are orthogonal (independence of `ξ'` and `𝒵`);
* `prop72Noise_calc`: the computation `⟨ξ(A), ξ(B)⟩_t = t |A ∩ B|` of the article, in the form
  `∫_0^{t ∧ T} ∫ 𝟙_P 𝟙_s + ∫_0^t ∫ (1 - 𝟙_{0<r≤T} 𝟙_P) 𝟙_s = t |s|`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 : Filtration ℝ≥0 mΩ} {Z : ℝ → ℝ → Ω → ℝ}
  {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {𝓖'' : Filtration ℝ≥0 m''}

/-- The integrand `prop72NoiseK` is predictable for the product filtration. -/
theorem prop72NoiseK_pred (P : Measure (Ω × Ω''))
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    Measurable[((prodFiltration 𝒢 𝓖'' P).predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × (Ω × Ω'')) × ℝ => prop72NoiseK Z T x p.1.1 p.2 p.1.2 := by
  have hz := measurable_predictable_prod_fst (𝒢₂ := 𝓖'') P (prop72NoiseZp_pred hZp)
  have he : Measurable[((prodFiltration 𝒢 𝓖'' P).predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × (Ω × Ω'')) × ℝ => prop72NoiseE x p.2 :=
    (prop72NoiseE_measurable x).comp (measurable_snd.mono le_rfl BorelSpace.measurable_eq.le)
  have hI : MeasurableSet[((prodFiltration 𝒢 𝓖'' P).predictable).prod (borel ℝ)]
      (Prod.fst ⁻¹' (Set.Ioc 0 T.toNNReal ×ˢ Set.univ) :
        Set ((ℝ≥0 × (Ω × Ω'')) × ℝ)) :=
    (@measurable_fst _ _ ((prodFiltration 𝒢 𝓖'' P).predictable) (borel ℝ))
      (measurableSet_predictable_Ioc_prod 0 _ MeasurableSet.univ)
  have e : {p : (ℝ≥0 × (Ω × Ω'')) × ℝ | 0 < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) ≤ T ∧
      0 < prop72NoiseZp Z p.1.1 p.2 p.1.2.1} =
      Prod.fst ⁻¹' (Set.Ioc 0 T.toNNReal ×ˢ Set.univ) ∩
        {p | 0 < prop72NoiseZp Z p.1.1 p.2 p.1.2.1} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_Ioc, Set.mem_univ, and_true, NNReal.coe_pos, Real.le_toNNReal_iff_coe_le hT]
    tauto
  unfold prop72NoiseK
  refine Measurable.ite ?_ measurable_const he
  rw [e]
  exact hI.inter (measurableSet_lt measurable_const hz)

/-- The energy of `prop72NoiseK` on `[0, n]` is finite. -/
theorem prop72NoiseK_energy {P : Measure (Ω × Ω'')} [IsFiniteMeasure P] (T x n : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) n, ∫⁻ y, ENNReal.ofReal (prop72NoiseK Z T x s y ω ^ 2)) ∂P
      < ⊤ := by
  refine lt_of_le_of_lt (mm_lintegral3_mono fun s y ω => ENNReal.ofReal_le_ofReal ?_)
    (prop72NoiseE_lintegral3_lt_top (μ := P) n x)
  unfold prop72NoiseK
  split_ifs
  · simp [sq_nonneg]
  · exact le_rfl

variable {Pr : Measure Ω} [IsProbabilityMeasure Pr] {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
  {T : ℝ} {q : ℝ → ℝ → Ω → ℝ} {M : (ℝ → ℝ) → ℝ → Ω → ℝ}

/-- **(7.10), stopped and lifted**: `⟨(h · M)_{· ∧ T}, (h' · M)_{· ∧ T}⟩_t = ∫_0^{t ∧ T} ∫ q h h'`
on `Ω × Ω''`, on every horizon `n`. -/
theorem prop72Noise_covMM (hT : 0 ≤ T)
    (hq : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => q p.1.1 p.2 p.1.2)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂Pr < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) Pr)
    {h h' : ℝ → ℝ → Ω → ℝ} {X X' : ℝ → Ω → ℝ}
    (hX : IsMMIntegral T 𝒢 q M Pr h X) (hX' : IsMMIntegral T 𝒢 q M Pr h' X') (n : ℝ) :
    HasCovariation n (prodFiltration 𝒢 𝓖'' (Pr.prod ν'')) (fun t ω => X (min t T) ω.1)
      (fun t ω => X' (min t T) ω.1)
      (fun t ω => ∫ r in (0 : ℝ)..(min t T), ∫ x, q r x ω.1 * h r x ω.1 * h' r x ω.1)
      (Pr.prod ν'') :=
  (prop72Noise_cov_stop (T' := n) hT (IsMMIntegral.hasCovariation hq hq0 hq1 hM hX hX')).prod_fst

omit [IsProbabilityMeasure ν''] in
/-- **Orthogonality**: a stopped martingale-measure integral, lifted to `Ω × Ω''`, and a Walsh
integral process against the auxiliary noise have covariation `0`. -/
theorem prop72Noise_covCross (hT : 0 ≤ T)
    (hq : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => q p.1.1 p.2 p.1.2)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂Pr < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) Pr)
    {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ} (hX : IsMMIntegral T 𝒢 q M Pr h X)
    {S'' : ℝ → ℝ → Ω'' → ℝ} (hS'' : IsWhiteNoise 𝓖'' S'' ν'') {n : ℝ}
    {k : ℝ → ℝ → Ω × Ω'' → ℝ} {W : ℝ → Ω × Ω'' → ℝ}
    (hW : ∀ t ∈ Set.Icc (0 : ℝ) n, IsWalshIntegral (prodFiltration 𝒢 𝓖'' (Pr.prod ν''))
      (fun t x ω => S'' t x ω.2) (Pr.prod ν'')
      (fun s y ω => if 0 < s ∧ s ≤ t then k s y ω else 0) (W t))
    (hWc : IsCL2Mart n (prodFiltration 𝒢 𝓖'' (Pr.prod ν'')) W (Pr.prod ν'')) :
    HasCovariation n (prodFiltration 𝒢 𝓖'' (Pr.prod ν'')) (fun t ω => X (min t T) ω.1) W
      (fun _ _ => 0) (Pr.prod ν'') :=
  hasCovariation_prod_fst_walsh hS''
    (prop72Noise_cov_stop (T' := n) hT (IsMMIntegral.hasCovariation hq hq0 hq1 hM hX hX)).left
    hW hWc

/-- A bounded strongly measurable function is interval integrable. -/
private lemma prop72Noise_ii {f : ℝ → ℝ} (hf : StronglyMeasurable f) {B : ℝ}
    (hB : ∀ r, ‖f r‖ ≤ B) (u v : ℝ) : IntervalIntegrable f volume u v :=
  ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
      (ae_of_all _ fun r => hB r),
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf.aestronglyMeasurable
      (ae_of_all _ fun r => hB r)⟩

/-- **The bracket of the white noise**: for a measurable function `g` on `ℝ × ℝ` (here `Z`), with `P = {g > 0}`, and a
set `s` of finite measure, `∫_0^{t ∧ T} ∫ 𝟙_P 𝟙_s + ∫_0^t ∫ (1 - 𝟙_{0 < r ≤ T} 𝟙_P) 𝟙_s = t |s|`. -/
theorem prop72Noise_calc {s : Set ℝ} (hs : MeasurableSet s) (hsf : volume s ≠ ⊤)
    {g : ℝ → ℝ → ℝ} (hg : Measurable fun p : ℝ × ℝ => g p.1 p.2) {t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..(min t T), ∫ y, (if 0 < g r y then s.indicator 1 y else 0)) +
      ∫ r in (0 : ℝ)..t, ∫ y, (if 0 < r ∧ r ≤ T ∧ 0 < g r y then 0 else s.indicator 1 y)
      = t * volume.real s := by
  classical
  have hind : Integrable (s.indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff hs).2 (integrableOn_const hsf)
  have hint1 : (∫ y, s.indicator (1 : ℝ → ℝ) y) = volume.real s := integral_indicator_one hs
  set F₁ : ℝ × ℝ → ℝ := fun p => if 0 < g p.1 p.2 then s.indicator 1 p.2 else 0 with hF₁
  set F₂ : ℝ × ℝ → ℝ := fun p => if 0 < p.1 ∧ p.1 ≤ T ∧ 0 < g p.1 p.2 then 0 else s.indicator 1 p.2
    with hF₂
  have hsm : Measurable fun p : ℝ × ℝ => s.indicator (1 : ℝ → ℝ) p.2 :=
    (measurable_const.indicator hs).comp measurable_snd
  have hF₁m : StronglyMeasurable F₁ := (Measurable.ite (measurableSet_lt measurable_const hg) hsm measurable_const).stronglyMeasurable
  have hF₂m : StronglyMeasurable F₂ := by
    refine (Measurable.ite ?_ measurable_const hsm).stronglyMeasurable
    exact ((measurableSet_Ioi.preimage measurable_fst).inter
      ((measurableSet_Iic.preimage measurable_fst).inter (measurableSet_lt measurable_const hg)))
  have hbd : ∀ (F : ℝ × ℝ → ℝ), (∀ p, F p = 0 ∨ F p = s.indicator 1 p.2) →
      ∀ r y, ‖F (r, y)‖ ≤ s.indicator (1 : ℝ → ℝ) y := by
    intro F hF r y
    rcases hF (r, y) with h | h <;> rw [h]
    · simp only [norm_zero]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
    · by_cases hy : y ∈ s <;> simp [hy]
  have hF₁b := hbd F₁ fun p => by simp only [hF₁]; split_ifs <;> simp
  have hF₂b := hbd F₂ fun p => by simp only [hF₂]; split_ifs <;> simp
  have hsec : ∀ (F : ℝ × ℝ → ℝ), StronglyMeasurable F → (∀ r y, ‖F (r, y)‖ ≤ s.indicator 1 y) →
      ∀ r, Integrable fun y => F (r, y) := fun F hF hb r =>
    hind.mono' (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ fun y => hb r y)
  set f₁ : ℝ → ℝ := fun r => ∫ y, F₁ (r, y) with hf₁
  set f₂ : ℝ → ℝ := fun r => ∫ y, F₂ (r, y) with hf₂
  have hfb : ∀ (F : ℝ × ℝ → ℝ), (∀ r y, ‖F (r, y)‖ ≤ s.indicator 1 y) →
      ∀ r, ‖∫ y, F (r, y)‖ ≤ volume.real s := fun F hb r => by
    rw [← hint1]; exact norm_integral_le_of_norm_le hind (ae_of_all _ fun y => hb r y)
  have ii₁ := prop72Noise_ii hF₁m.integral_prod_right' (hfb F₁ hF₁b)
  have ii₂ := prop72Noise_ii hF₂m.integral_prod_right' (hfb F₂ hF₂b)
  have hsum : ∀ r, 0 < r → r ≤ T → f₁ r + f₂ r = volume.real s := by
    intro r hr0 hrT
    rw [hf₁, hf₂, ← integral_add (hsec F₁ hF₁m hF₁b r) (hsec F₂ hF₂m hF₂b r), ← hint1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hF₁, hF₂, hr0, hrT, true_and]
    split_ifs <;> simp
  have hlate : ∀ r, T < r → f₂ r = volume.real s := by
    intro r hr
    rw [hf₂, ← hint1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have : ¬ (0 < r ∧ r ≤ T ∧ 0 < g r y) := fun h => absurd h.2.1 (not_le.2 hr)
    simp only [hF₂, this, ite_false]
  change (∫ r in (0 : ℝ)..(min t T), f₁ r) + ∫ r in (0 : ℝ)..t, f₂ r = t * volume.real s
  set τ := min t T with hτ
  have hτ0 : 0 ≤ τ := le_min ht hT
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii₂ 0 τ) (ii₂ τ t), ← add_assoc,
    ← intervalIntegral.integral_add (ii₁ 0 τ) (ii₂ 0 τ)]
  have h1 : ∫ r in (0 : ℝ)..τ, (f₁ r + f₂ r) = τ * volume.real s := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => volume.real s) (ae_of_all _ fun r hr => by
      rw [Set.uIoc_of_le hτ0] at hr
      exact hsum r hr.1 (hr.2.trans (min_le_right _ _)))]
    simp
  have h2 : ∫ r in τ..t, f₂ r = (t - τ) * volume.real s := by
    rcases le_total t T with htT | hTt
    · rw [hτ, min_eq_left htT, intervalIntegral.integral_same, sub_self, zero_mul]
    · rw [hτ, min_eq_right hTt, intervalIntegral.integral_congr_ae
        (g := fun _ => volume.real s) (ae_of_all _ fun r hr => by
          rw [Set.uIoc_of_le hTt] at hr
          exact hlate r hr.1)]
      simp
  rw [h1, h2]; ring

end QSSEPtoKPZ
