/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.WhiteNoise.MMBracket
public import QSSEPtoKPZ.Martingales.CovariationAlgebra
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Proposition 7.2, Step 1: the cross brackets (7.9) (task J1)

For time-independent test functions `φ, ψ ∈ C_b³(ℝ)`, the martingales `M^φ`, `M^ψ` of (7.2)
have covariation `⟨M^φ, M^ψ⟩_t = ∫_0^t ∫ Z(s,x)² φ(x) ψ(x) dx ds` (7.9). Proof by polarization
from the brackets (7.3) of `M^φ`, `M^ψ` and `M^{φ+ψ} = M^φ + M^ψ` (linearity of `φ ↦ M^φ`,
`limMart_add`), the brackets being bilinear almost surely (`mmBr_add_ae`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The sum of two time-independent test functions of `C_b³` is in `C_b³`. -/
private lemma prop72Noise_isC13_add {T : ℝ} (hT : 0 ≤ T) {φ ψ : ℝ → ℝ} {C C' : ℝ}
    (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C) (hψ : IsC13 T (fun _ => ψ) (fun _ _ => 0) C') :
    IsC13 T (fun _ => fun x => φ x + ψ x) (fun _ _ => 0) (C + C') := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hφc : ContDiff ℝ 3 φ := hφ.contDiff 0 h0
  have hψc : ContDiff ℝ 3 ψ := hψ.contDiff 0 h0
  have hid : ∀ k ≤ 3, ∀ x, iteratedDeriv k (fun x => φ x + ψ x) x =
      iteratedDeriv k φ x + iteratedDeriv k ψ x := by
    intro k hk x
    have hk' : ((k : ℕ∞) : WithTop ℕ∞) ≤ 3 := WithTop.coe_le_coe.2 (by exact_mod_cast hk)
    exact iteratedDeriv_fun_add (hφc.of_le hk').contDiffAt (hψc.of_le hk').contDiffAt
  refine ⟨fun _ _ => hφc.add hψc, fun x t _ => ?_, ⟨continuousOn_const, fun k hk => ?_⟩, ?_⟩
  · simpa using hasDerivWithinAt_const t (Set.Icc 0 T) (φ x + ψ x)
  · exact ((hφ.continuousOn.2 k hk).add (hψ.continuousOn.2 k hk)).congr
      fun p _ => hid k hk p.2
  · obtain ⟨c, hc, hcb⟩ := hφ.bound
    obtain ⟨c', hc', hcb'⟩ := hψ.bound
    refine ⟨c + c', ?_, fun t ht x => ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib]
      linarith
    obtain ⟨a0, a1, a2, a3, a4⟩ := hcb t ht x
    obtain ⟨b0, b1, b2, b3, b4⟩ := hcb' t ht x
    simp only [Pi.add_apply, hid 1 (by norm_num), hid 2 (by norm_num), hid 3 (by norm_num)]
    refine ⟨(abs_add_le _ _).trans (add_le_add a0 b0), ?_, (abs_add_le _ _).trans (add_le_add a2 b2),
      (abs_add_le _ _).trans (add_le_add a3 b3), (abs_add_le _ _).trans (add_le_add a4 b4)⟩
    simp only [abs_zero] at a1 b1 ⊢
    linarith

/-- A bounded continuous function is integrable for a finite measure on `ℝ`. -/
private lemma prop72Noise_integrable {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ x, |f x| ≤ K) (μ : FiniteMeasure ℝ) : Integrable f (μ : Measure ℝ) :=
  Integrable.of_bound hf.aestronglyMeasurable K (ae_of_all _ fun x => by
    simpa [Real.norm_eq_abs] using hK x)

/-- `μ(f + g) = μ(f) + μ(g)` for bounded continuous `f`, `g`. -/
private lemma prop72Noise_pairFM_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {K K' : ℝ} (hK : ∀ x, |f x| ≤ K) (hK' : ∀ x, |g x| ≤ K') (μ : FiniteMeasure ℝ) :
    pairFM μ (fun x => f x + g x) = pairFM μ f + pairFM μ g :=
  integral_add (prop72Noise_integrable hf hK μ) (prop72Noise_integrable hg hK' μ)

/-- `s ↦ 𝒵(s; f)` is continuous for `f` bounded and continuous. -/
private lemma prop72Noise_continuous_pair {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Continuous fun s => pairFM (pathAt γ s) f :=
  (continuous_pairFM hf ⟨K, hK⟩).comp
    (continuous_pathAt_prod.comp (continuous_const.prodMk continuous_id))

/-- **Linearity of `φ ↦ M^φ`** for time-independent test functions:
`M^{φ+ψ} = M^φ + M^ψ` (7.2). -/
private lemma prop72Noise_limMart_add {T : ℝ} (hT : 0 ≤ T)
    (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) {φ ψ : ℝ → ℝ} {C C' : ℝ}
    (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C) (hψ : IsC13 T (fun _ => ψ) (fun _ _ => 0) C') :
    limMart Y (fun _ => fun x => φ x + ψ x) (fun _ _ => 0) =
      fun t ω => limMart Y (fun _ => φ) (fun _ _ => 0) t ω +
        limMart Y (fun _ => ψ) (fun _ _ => 0) t ω := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hφc : ContDiff ℝ 3 φ := hφ.contDiff 0 h0
  have hψc : ContDiff ℝ 3 ψ := hψ.contDiff 0 h0
  obtain ⟨c, -, hcb⟩ := hφ.bound
  obtain ⟨c', -, hcb'⟩ := hψ.bound
  have h2 : ∀ x, iteratedDeriv 2 (fun x => φ x + ψ x) x =
      iteratedDeriv 2 φ x + iteratedDeriv 2 ψ x := fun x =>
    iteratedDeriv_fun_add (hφc.of_le (by norm_num)).contDiffAt
      (hψc.of_le (by norm_num)).contDiffAt
  -- the second derivatives, halved, are bounded and continuous
  set u : ℝ → ℝ := fun x => 0 + iteratedDeriv 2 φ x / 2 with hu
  set v : ℝ → ℝ := fun x => 0 + iteratedDeriv 2 ψ x / 2 with hv
  have huc : Continuous u := continuous_const.add
    ((hφc.continuous_iteratedDeriv 2 (by norm_num)).div_const 2)
  have hvc : Continuous v := continuous_const.add
    ((hψc.continuous_iteratedDeriv 2 (by norm_num)).div_const 2)
  have huK : ∀ x, |u x| ≤ |c 3| := fun x => by
    have := (hcb 0 h0 x).2.2.2.1
    simp only [hu, zero_add, abs_div, abs_two]
    have := le_abs_self (c 3)
    have := abs_nonneg (iteratedDeriv 2 φ x)
    linarith
  have hvK : ∀ x, |v x| ≤ |c' 3| := fun x => by
    have := (hcb' 0 h0 x).2.2.2.1
    simp only [hv, zero_add, abs_div, abs_two]
    have := le_abs_self (c' 3)
    have := abs_nonneg (iteratedDeriv 2 ψ x)
    linarith
  have hφK : ∀ x, |φ x| ≤ c 0 := fun x => (hcb 0 h0 x).1
  have hψK : ∀ x, |ψ x| ≤ c' 0 := fun x => (hcb' 0 h0 x).1
  funext t ω
  have e : (fun x => (0 : ℝ) + iteratedDeriv 2 (fun x => φ x + ψ x) x / 2) =
      fun x => u x + v x := by
    funext x; simp only [hu, hv, h2 x]; ring
  simp only [limMart]
  rw [e, prop72Noise_pairFM_add hφc.continuous hψc.continuous hφK hψK]
  have hi : ∀ s, pairFM (pathAt (Y ω) s) (fun x => u x + v x) =
      pairFM (pathAt (Y ω) s) u + pairFM (pathAt (Y ω) s) v := fun s =>
    prop72Noise_pairFM_add huc hvc huK hvK _
  simp_rw [hi]
  rw [intervalIntegral.integral_add
    ((prop72Noise_continuous_pair (Y ω) huc huK).intervalIntegrable _ _)
    ((prop72Noise_continuous_pair (Y ω) hvc hvK).intervalIntegrable _ _)]
  ring

/-- **(7.9)**, Step 1 of the proof of Proposition 7.2: by polarization, for time-independent
`φ, ψ ∈ C_b³(ℝ)`, `⟨M^φ, M^ψ⟩_t = ∫_0^t ∫ Z(r,x)² φ(x) ψ(x) dx dr`. -/
theorem prop72Noise_hasCovariation {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {𝒢 : Filtration ℝ≥0 mΩ} {T : ℝ} (hT : 0 < T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Z : ℝ → ℝ → Ω → ℝ}
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {φ ψ : ℝ → ℝ} {C C' : ℝ} (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C)
    (hψ : IsC13 T (fun _ => ψ) (fun _ _ => 0) C') :
    HasCovariation T 𝒢 (limMart Y (fun _ => φ) (fun _ _ => 0))
      (limMart Y (fun _ => ψ) (fun _ _ => 0))
      (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, Z r x ω ^ 2 * φ x * ψ x) Pr := by
  have hT0 : 0 ≤ T := hT.le
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT0⟩
  have hC := hmart (prop72Noise_isC13_add hT0 hφ hψ)
  rw [prop72Noise_limMart_add hT0 Y hφ hψ] at hC
  have hcov := HasCovariation.of_hasBracket_add (hmart hφ) (hmart hψ) hC
  refine hcov.mmCongrCov hT0 ?_
  -- the brackets as `mmBr`, and their bilinearity
  set q : ℝ → ℝ → Ω → ℝ := fun r x ω => Z r x ω ^ 2 with hq_def
  set fφ : ℝ → ℝ → Ω → ℝ := fun _ x _ => φ x with hfφ
  set fψ : ℝ → ℝ → Ω → ℝ := fun _ x _ => ψ x with hfψ
  set fs : ℝ → ℝ → Ω → ℝ := fun r x ω => fφ r x ω + fψ r x ω with hfs
  have hq : MMPred 𝒢 q := hZp.pow_const 2
  have hq0 : ∀ r x ω, 0 ≤ q r x ω := fun _ _ _ => sq_nonneg _
  have hφm : MMPred 𝒢 fφ := mmPred_of_measurable (hφ.contDiff 0 h0).continuous.measurable
  have hψm : MMPred 𝒢 fψ := mmPred_of_measurable (hψ.contDiff 0 h0).continuous.measurable
  have hsm : MMPred 𝒢 fs := hφm.add hψm
  obtain ⟨c, -, hcb⟩ := hφ.bound
  obtain ⟨c', -, hcb'⟩ := hψ.bound
  have hE : ∀ {h : ℝ → ℝ → Ω → ℝ} {K : ℝ}, (∀ r x ω, |h r x ω| ≤ K) →
      mmEnergy Pr T q h ≠ ∞ := fun hK =>
    ((mmEnergy_le_of_bdd hq0 hK).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZ2)).ne
  have hEφ : mmEnergy Pr T q fφ ≠ ∞ := hE fun _ x _ => (hcb 0 h0 x).1
  have hEψ : mmEnergy Pr T q fψ ≠ ∞ := hE fun _ x _ => (hcb' 0 h0 x).1
  have hEs : mmEnergy Pr T q fs ≠ ∞ := hE fun _ x _ =>
    (abs_add_le _ _).trans (add_le_add (hcb 0 h0 x).1 (hcb' 0 h0 x).1)
  have hbr : ∀ g : ℝ → ℝ, limBracket Z (fun _ => g) =
      mmBr q (fun _ x _ => g x) (fun _ x _ => g x) := fun g => by
    funext t ω
    simp only [limBracket, mmBr, hq_def]
    congr 1; funext r; congr 1; funext x; ring
  have hbs : limBracket Z (fun _ => fun x => φ x + ψ x) = mmBr q fs fs := hbr _
  filter_upwards [mmBr_add_ae hq hq0 hφm hψm hsm hEφ hEψ hEs,
    mmBr_add_ae hq hq0 hφm hψm hφm hEφ hEψ hEφ,
    mmBr_add_ae hq hq0 hφm hψm hψm hEφ hEψ hEψ] with ω e1 e2 e3 t ht
  rw [hbs, hbr φ, hbr ψ]
  have e1' := e1 t ht
  have e2' := e2 t ht
  have e3' := e3 t ht
  rw [mmBr_comm q fφ fs, mmBr_comm q fψ fs] at e1'
  rw [mmBr_comm q fψ fφ] at e2'
  change (mmBr q fs fs t ω - mmBr q fφ fφ t ω - mmBr q fψ fψ t ω) / 2 = mmBr q fφ fψ t ω
  rw [e1', e2', e3']
  ring

end QSSEPtoKPZ
