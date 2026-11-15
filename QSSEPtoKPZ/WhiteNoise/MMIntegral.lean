/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.Martingales.Covariation
public import Mathlib.Probability.Process.Predictable
public import QSSEPtoKPZ.WhiteNoise.MMBlock
public import QSSEPtoKPZ.WhiteNoise.MMLimit

/-!
# The integral against the martingale measure `φ ↦ M^φ` (task G8a)

INTERFACE FILE (task I0″ of Stage 4): the definition is complete; the statements below are
interfaces, proved by task G8a. See `docs/stage4-design.md`, Sections 1.2 (f) and 3.3, and
`docs/stage4-interfaces.md`. Proved by task G8a, with the auxiliary files `MMBlock.lean`
(elementary integrals), `MMBracket.lean` (the brackets `∫_0^t ∫ q h g`) and `MMLimit.lean`
(passage to the limit).

Step 1 of the proof of Proposition 7.2. `M φ` is a family of continuous martingales indexed by
the time-independent test functions `φ ∈ C_b³` with covariations
`⟨M^φ, M^ψ⟩_t = ∫_0^t ∫ q(r,x) φ(x) ψ(x) dx dr` (here `q = Z²`, (7.9)). The integral `h · M` is
the smallest relation that contains the simple integrands `a 𝟙_{(s,t]}(r) φ(x)` (`a` bounded
`𝒢_s`-measurable), is stable under addition, and is closed under limits in `L²(q dℙ dr dx)`
(integrands, which must be predictable) and in `L²(ℙ; sup_{r ≤ T})` (processes, which must have
continuous paths and be almost everywhere strongly measurable at each time of `[0,T]`).
`IsMMIntegral.hasCovariation` is (7.10). The covariation and uniqueness lemmas assume the
intensity `q` predictable, nonnegative and with `𝔼 ∫_0^T ∫ q < ∞` (so that the brackets
`∫_0^t ∫ q h h'` are genuine integrals; in Proposition 7.2, `q = Z²` and this is (7.1)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsMMIntegral T 𝒢 q M μ h X`: `X = h · M` on `[0,T]`, for the orthogonal martingale measure
`φ ↦ M φ` with intensity `q(r,x) dr dx`. -/
inductive IsMMIntegral (T : ℝ) (𝒢 : Filtration ℝ≥0 mΩ) (q : ℝ → ℝ → Ω → ℝ)
    (M : (ℝ → ℝ) → ℝ → Ω → ℝ) (μ : Measure Ω) : (ℝ → ℝ → Ω → ℝ) → (ℝ → Ω → ℝ) → Prop
  /-- Simple integrands `a 𝟙_{(s,t]}(r) φ(x)`, with value `a (M^φ(r ∧ t) - M^φ(r ∧ s))`. -/
  | block (s t : ℝ≥0) (hst : s ≤ t) (a : Ω → ℝ) (φ : ℝ → ℝ) (C : ℝ)
      (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C) (ha : Measurable[𝒢 s] a)
      (hab : ∃ K, ∀ ω, |a ω| ≤ K) :
      IsMMIntegral T 𝒢 q M μ (fun r x ω => if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0)
        (fun r ω => a ω * (M φ (min r t) ω - M φ (min r s) ω))
  /-- Additivity. -/
  | add (h h' : ℝ → ℝ → Ω → ℝ) (X X' : ℝ → Ω → ℝ) :
      IsMMIntegral T 𝒢 q M μ h X → IsMMIntegral T 𝒢 q M μ h' X' →
      IsMMIntegral T 𝒢 q M μ (fun r x ω => h r x ω + h' r x ω) (fun r ω => X r ω + X' r ω)
  /-- Closure under limits: predictable limit integrand in `L²(q dℙ dr dx)` on `[0,T]`, limit
  process with continuous paths, almost everywhere strongly measurable at each time of `[0,T]`,
  in `L²(ℙ; sup_{r ∈ [0,T]})`. (Without the measurability of `X r`, the lower integral below can
  vanish for an error that is not almost surely `0`.) -/
  | limit (h : ℝ → ℝ → Ω → ℝ) (X : ℝ → Ω → ℝ) (hs : ℕ → ℝ → ℝ → Ω → ℝ) (Xs : ℕ → ℝ → Ω → ℝ) :
      (∀ k, IsMMIntegral T 𝒢 q M μ (hs k) (Xs k)) →
      Measurable[(𝒢.predictable).prod (borel ℝ)]
        (fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2) →
      (∀ ω, ContinuousOn (fun r => X r ω) (Set.Icc 0 T)) →
      (∀ r ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (X r) μ) →
      Tendsto (fun k => ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x,
        ENNReal.ofReal ((hs k r x ω - h r x ω) ^ 2 * q r x ω)) ∂μ) atTop (𝓝 0) →
      Tendsto (fun k => ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ) atTop (𝓝 0) →
      IsMMIntegral T 𝒢 q M μ h X

variable {μ : Measure Ω} {T : ℝ} {𝒢 : Filtration ℝ≥0 mΩ} {q : ℝ → ℝ → Ω → ℝ}
  {M : (ℝ → ℝ) → ℝ → Ω → ℝ}

/-! ### Auxiliary lemmas (task G8a)

The proof of (7.10) runs by two inductions on `IsMMIntegral`. The first (`mm_stageA`) shows
that every integral `X = h · M` has a predictable integrand of finite energy, vanishes at time
`0`, is a continuous `L²` martingale, and has covariation `∫_0^· ∫ q h ψ` with every `M^ψ`
(blocks: `HasCovariation.mmBlock` applied to `hM`; sums: bilinearity; limits:
`mm_hasCovariation_limit`). The second (`mm_stageB`) gives `⟨X, X'⟩` for any two integrals,
with the same three cases, using the first for `X'`. -/

/-- A test function of `C_b³` (time-independent) is measurable and bounded (`T ≥ 0`). -/
private lemma mm_isC13_facts (hT : 0 ≤ T) {φ : ℝ → ℝ} {C : ℝ}
    (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C) : Measurable φ ∧ ∃ K, ∀ x, |φ x| ≤ K := by
  refine ⟨(hφ.contDiff 0 ⟨le_rfl, hT⟩).continuous.measurable, ?_⟩
  obtain ⟨c, -, hc⟩ := hφ.bound
  exact ⟨c 0, fun x => (hc 0 ⟨le_rfl, hT⟩ x).1⟩

/-- The simple integrand `a 𝟙_{(s,t]}(r) φ(x)` is predictable. -/
private lemma mm_block_pred {s t : ℝ≥0} {a : Ω → ℝ} (ha : Measurable[𝒢 s] a) {φ : ℝ → ℝ}
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

/-- The covariation on an empty horizon (`T < 0`). -/
private lemma mm_hasCovariation_of_neg (hT : T < 0) {X Y A : ℝ → Ω → ℝ}
    (hA : ∀ ω, A 0 ω = 0) : HasCovariation T 𝒢 X Y A μ := by
  have hE : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.2 hT)
  have hn : ∀ t : ℝ≥0, ¬ (t : ℝ) ≤ T := fun t ht => absurd (t.2.trans ht) (not_le.2 hT)
  have hM : ∀ Z : ℝ → Ω → ℝ, IsCL2Mart T 𝒢 Z μ := fun Z =>
    ⟨ae_of_all _ fun ω => (by rw [hE]; exact continuousOn_empty _),
      fun t ht => absurd ht (hn t), fun _ t _ ht => absurd ht (hn t)⟩
  exact ⟨hM X, hM Y, fun t ht => absurd ht (hn t), ae_of_all _ hA,
    ae_of_all _ fun ω => (by rw [hE]; exact continuousOn_empty _),
    ae_of_all _ fun ω =>
      (by rw [hE]; exact BoundedVariationOn.of_subsingleton Set.subsingleton_empty),
    fun _ t _ ht => absurd ht (hn t)⟩

/-- **First induction**: properties of `X = h · M`, and `⟨X, M^ψ⟩ = ∫_0^· ∫ q h ψ`. -/
private lemma mm_stageA [IsProbabilityMeasure μ] (hT : 0 ≤ T)
    (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ} (hX : IsMMIntegral T 𝒢 q M μ h X) :
    MMPred 𝒢 h ∧ mmEnergy μ T q h ≠ ∞ ∧ X 0 =ᵐ[μ] 0 ∧ IsCL2Mart T 𝒢 X μ ∧
      ∀ {ψ : ℝ → ℝ} {C' : ℝ}, IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
        HasCovariation T 𝒢 X (M ψ) (mmBr q h fun _ x _ => ψ x) μ := by
  -- deterministic test functions
  have hdet : ∀ {ψ : ℝ → ℝ} {C' : ℝ}, IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      MMPred 𝒢 (fun _ x _ => ψ x) ∧ mmEnergy μ T q (fun _ x _ => ψ x) ≠ ∞ := by
    intro ψ C' hψ
    obtain ⟨hψm, K, hK⟩ := mm_isC13_facts hT hψ
    exact ⟨mmPred_of_measurable hψm, ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq1.ne)
      (mmEnergy_le_of_bdd hq0 fun _ x _ => hK x)⟩
  induction hX with
  | block s t hst a φ C hφ ha hab =>
    obtain ⟨K, hK⟩ := hab
    obtain ⟨hφm, Kφ, hKφ⟩ := mm_isC13_facts hT hφ
    have hpred := mm_block_pred (t := t) ha hφm
    refine ⟨hpred, ?_, ae_of_all _ fun ω => by simp, ?_, ?_⟩
    · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq1.ne)
        (mmEnergy_le_of_bdd (K := max K 0 * max Kφ 0) hq0 fun r x ω => ?_)
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul ((hK ω).trans (le_max_left _ _)) ((hKφ x).trans (le_max_left _ _))
          (abs_nonneg _) (le_max_right _ _)
      · simp only [abs_zero]
        exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
    · exact ((hM hφ hφ).mmBlock s t hst ha hK).left
    · intro ψ C' hψ
      refine ((hM hφ hψ).mmBlock s t hst ha hK).mmCongrCov hT ?_
      filter_upwards [mmBr_block_ae hq hq0 (hdet hφ).1 (hdet hφ).2 (hdet hψ).1 (hdet hψ).2
        s t hst a] with ω hω u hu
      rw [hω u hu]
      rfl
  | add h h' X X' _ _ ih ih' =>
    obtain ⟨p1, e1, z1, m1, c1⟩ := ih
    obtain ⟨p2, e2, z2, m2, c2⟩ := ih'
    refine ⟨p1.add p2, ?_, ?_, m1.add m2, fun hψ => ?_⟩
    · have := mmEnergy_lincomb_le (μ := μ) (T := T) hq hq0 p1 p2 1 1
      simp only [one_mul] at this
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top e1,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top e2⟩) this
    · filter_upwards [z1, z2] with ω h1 h2
      simp [h1, h2]
    · refine ((c1 hψ).add_left (c2 hψ)).mmCongrCov hT ?_
      filter_upwards [mmBr_add_ae hq hq0 p1 p2 (hdet hψ).1 e1 e2 (hdet hψ).2] with ω hω u hu
      rw [hω u hu]
  | limit h X hs Xs _ hpred hcont hmeas hconv hsup ih =>
    have hEh := mmEnergy_ne_top_of_tendsto hq hq0 (fun k => (ih k).1) hpred
      (fun k => (ih k).2.1) hconv
    refine ⟨hpred, hEh, mm_ae_zero_limit hT (fun k => (ih k).2.2.1) (hmeas 0 ⟨le_rfl, hT⟩) hsup,
      mm_isCL2Mart_limit (fun k => (ih k).2.2.2.1) hcont hmeas hsup, fun hψ => ?_⟩
    exact mm_hasCovariation_limit hT hq hq0 (hdet hψ).1 (hdet hψ).2
      (fun k => (ih k).2.2.2.2 hψ) (fun k => (ih k).1) (fun k => (ih k).2.1) hpred hEh hconv
      hcont hmeas hsup

/-- **Second induction**: `⟨X, X'⟩ = ∫_0^· ∫ q h h'` for two integrals `X = h · M`,
`X' = h' · M`. -/
private lemma mm_stageB [IsProbabilityMeasure μ] (hT : 0 ≤ T)
    (hq : MMPred 𝒢 q) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ} (hX : IsMMIntegral T 𝒢 q M μ h X) :
    ∀ {h' : ℝ → ℝ → Ω → ℝ} {X' : ℝ → Ω → ℝ}, IsMMIntegral T 𝒢 q M μ h' X' →
      HasCovariation T 𝒢 X X' (mmBr q h h') μ := by
  induction hX with
  | block s t hst a φ C hφ ha hab =>
    intro h' X' hX'
    obtain ⟨K, hK⟩ := hab
    obtain ⟨p', e', -, -, c'⟩ := mm_stageA hT hq hq0 hq1 hM hX'
    obtain ⟨hφm, Kφ, hKφ⟩ := mm_isC13_facts hT hφ
    have hφp : MMPred 𝒢 (fun _ x _ => φ x) := mmPred_of_measurable hφm
    have hφE : mmEnergy μ T q (fun _ x _ => φ x) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq1.ne)
        (mmEnergy_le_of_bdd hq0 fun _ x _ => hKφ x)
    have c2 := (c' hφ).symm.mmBlock s t hst ha hK
    rw [mmBr_comm q h' (fun _ x _ => φ x)] at c2
    refine c2.mmCongrCov hT ?_
    filter_upwards [mmBr_block_ae hq hq0 hφp hφE p' e' s t hst a] with ω hω u hu
    rw [hω u hu]
  | add h₁ h₂ X₁ X₂ _ _ ih₁ ih₂ =>
    intro h' X' hX'
    obtain ⟨p1, e1, -, -, -⟩ := mm_stageA hT hq hq0 hq1 hM ‹IsMMIntegral T 𝒢 q M μ h₁ X₁›
    obtain ⟨p2, e2, -, -, -⟩ := mm_stageA hT hq hq0 hq1 hM ‹IsMMIntegral T 𝒢 q M μ h₂ X₂›
    obtain ⟨p', e', -, -, -⟩ := mm_stageA hT hq hq0 hq1 hM hX'
    refine ((ih₁ hX').add_left (ih₂ hX')).mmCongrCov hT ?_
    filter_upwards [mmBr_add_ae hq hq0 p1 p2 p' e1 e2 e'] with ω hω u hu
    rw [hω u hu]
  | limit h X hs Xs hk hpred hcont hmeas hconv hsup ih =>
    intro h' X' hX'
    obtain ⟨p', e', -, -, -⟩ := mm_stageA hT hq hq0 hq1 hM hX'
    have hA := fun k => mm_stageA hT hq hq0 hq1 hM (hk k)
    have hEh := mmEnergy_ne_top_of_tendsto hq hq0 (fun k => (hA k).1) hpred
      (fun k => (hA k).2.1) hconv
    exact mm_hasCovariation_limit hT hq hq0 p' e' (fun k => ih k hX') (fun k => (hA k).1)
      (fun k => (hA k).2.1) hpred hEh hconv hcont hmeas hsup

/-- **Covariation of martingale-measure integrals**, (7.10):
`⟨h · M, h' · M⟩_t = ∫_0^t ∫ h h' q dx dr`. -/
theorem IsMMIntegral.hasCovariation [IsProbabilityMeasure μ]
    (hq : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => q p.1.1 p.2 p.1.2)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {h h' : ℝ → ℝ → Ω → ℝ} {X X' : ℝ → Ω → ℝ}
    (hX : IsMMIntegral T 𝒢 q M μ h X) (hX' : IsMMIntegral T 𝒢 q M μ h' X') :
    HasCovariation T 𝒢 X X'
      (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * h r x ω * h' r x ω) μ := by
  rcases lt_or_ge T 0 with hT | hT
  · exact mm_hasCovariation_of_neg hT fun ω => by simp
  · exact mm_stageB hT hq hq0 hq1 hM hX hX'

/-- Scalar multiples of martingale-measure integrals. -/
theorem IsMMIntegral.const_mul [IsProbabilityMeasure μ] {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ}
    (hX : IsMMIntegral T 𝒢 q M μ h X) (c : ℝ) :
    IsMMIntegral T 𝒢 q M μ (fun r x ω => c * h r x ω) (fun r ω => c * X r ω) := by
  induction hX with
  | block s t hst a φ C hφ ha hab =>
    obtain ⟨K, hK⟩ := hab
    have e1 : (fun r x ω => c * (if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0)) =
        fun r x ω => if (s : ℝ) < r ∧ r ≤ t then (c * a ω) * φ x else 0 := by
      funext r x ω; split_ifs <;> ring
    have e2 : (fun r ω => c * (a ω * (M φ (min r t) ω - M φ (min r s) ω))) =
        fun r ω => (c * a ω) * (M φ (min r t) ω - M φ (min r s) ω) := by
      funext r ω; ring
    rw [e1, e2]
    exact IsMMIntegral.block s t hst (fun ω => c * a ω) φ C hφ (ha.const_mul c)
      ⟨|c| * K, fun ω => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK ω) (abs_nonneg c)⟩
  | add h h' X X' _ _ ih ih' =>
    have e1 : (fun r x ω => c * (h r x ω + h' r x ω)) =
        fun r x ω => c * h r x ω + c * h' r x ω := by funext r x ω; ring
    have e2 : (fun r ω => c * (X r ω + X' r ω)) = fun r ω => c * X r ω + c * X' r ω := by
      funext r ω; ring
    rw [e1, e2]
    exact IsMMIntegral.add _ _ _ _ ih ih'
  | limit h X hs Xs _ hpred hcont hmeas hconv hsup ih =>
    refine IsMMIntegral.limit _ _ (fun k r x ω => c * hs k r x ω) (fun k r ω => c * Xs k r ω) ih
      (hpred.const_mul c) (fun ω => continuousOn_const.mul (hcont ω))
      (fun r hr => (hmeas r hr).const_mul c) ?_ ?_
    · have e : ∀ k, (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x,
          ENNReal.ofReal ((c * hs k r x ω - c * h r x ω) ^ 2 * q r x ω)) ∂μ) =
          ENNReal.ofReal (c ^ 2) * mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω) := by
        intro k
        rw [← mmEnergy_const_mul]
        unfold mmEnergy
        simp_rw [← mul_sub]
      simp only [e]
      have := ENNReal.Tendsto.const_mul hconv (Or.inr (ENNReal.ofReal_ne_top (r := c ^ 2)))
      rw [mul_zero] at this
      exact this
    · have e : ∀ k, (∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
          ENNReal.ofReal ((c * Xs k r ω - c * X r ω) ^ 2)) ∂μ) =
          ENNReal.ofReal (c ^ 2) * ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
            ENNReal.ofReal ((Xs k r ω - X r ω) ^ 2)) ∂μ := by
        intro k
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.mul_iSup]
        refine iSup_congr fun r => ?_
        rw [ENNReal.mul_iSup]
        refine iSup_congr fun _ => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg c)]
        congr 1; ring
      simp only [e]
      have := ENNReal.Tendsto.const_mul hsup (Or.inr (ENNReal.ofReal_ne_top (r := c ^ 2)))
      rw [mul_zero] at this
      exact this

/-- **Uniqueness**: two integrals of integrands that agree `q dℙ dr dx`-almost everywhere on
`[0,T]` are indistinguishable on `[0,T]`. -/
theorem IsMMIntegral.ae_eq [IsProbabilityMeasure μ]
    (hq : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => q p.1.1 p.2 p.1.2)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {h h' : ℝ → ℝ → Ω → ℝ} {X X' : ℝ → Ω → ℝ}
    (hX : IsMMIntegral T 𝒢 q M μ h X) (hX' : IsMMIntegral T 𝒢 q M μ h' X')
    (hh : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal ((h r x ω - h' r x ω) ^ 2 * q r x ω)) ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = X' t ω := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ae_of_all _ fun ω t ht => absurd (ht.1.trans ht.2) (not_le.2 hT)
  -- `Z = X - X'` is the integral of `F = h - h'`
  have hZ := IsMMIntegral.add _ _ _ _ hX (hX'.const_mul (-1))
  set F : ℝ → ℝ → Ω → ℝ := fun r x ω => h r x ω + -1 * h' r x ω with hF
  set Z : ℝ → Ω → ℝ := fun r ω => X r ω + -1 * X' r ω with hZdef
  obtain ⟨pF, -, hZ0, -, -⟩ := mm_stageA hT hq hq0 hq1 hM hZ
  have hcov := mm_stageB hT hq hq0 hq1 hM hZ hZ
  have hEF : mmEnergy μ T q F = 0 := by
    rw [← hh]
    unfold mmEnergy
    congr 1; funext ω; congr 1; funext r; congr 1; funext x
    simp only [hF]; ring_nf
  -- the bracket vanishes
  have hA0 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → mmBr q F F t =ᵐ[μ] 0 := by
    intro t ht
    have hle : ∫⁻ ω, ‖mmBr q F F t ω‖ₑ ∂μ ≤ 0 := by
      calc ∫⁻ ω, ‖mmBr q F F t ω‖ₑ ∂μ
          ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ‖q r x ω * F r x ω * F r x ω‖ₑ) ∂μ :=
            lintegral_mono fun ω => mm_enorm_mmBr_le F F ⟨t.2, ht⟩ ω
        _ ≤ 1 * mmEnergy μ T q F + 1⁻¹ * mmEnergy μ T q F :=
            mm_lintegral_enorm_le hq hq0 pF pF one_ne_zero ENNReal.one_ne_top
        _ = 0 := by simp [hEF]
    have h0 := le_antisymm hle zero_le
    rw [lintegral_eq_zero_iff' (hcov.integrable_cov t ht).aestronglyMeasurable.aemeasurable.enorm]
      at h0
    filter_upwards [h0] with ω hω
    simpa using hω
  -- `Z_t = 0` almost surely for each `t`
  have hZt : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Z t =ᵐ[μ] 0 := by
    intro t ht
    have hce := hcov.condExp_mul 0 t (zero_le : (0 : ℝ≥0) ≤ t) ht
    have hint : Integrable (fun ω => Z t ω * Z t ω - mmBr q F F t ω) μ :=
      ((hcov.left.memLp t ht).integrable_mul (hcov.left.memLp t ht)).sub
        (hcov.integrable_cov t ht)
    have h1 : ∫ ω, (Z t ω * Z t ω - mmBr q F F t ω) ∂μ = 0 := by
      rw [← integral_condExp (𝒢.le 0), integral_congr_ae hce]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hZ0, hA0 0 (by simpa using hT)] with ω h1 h2
      simp only [NNReal.coe_zero] at h1 h2 ⊢
      simp [h1, h2]
    have h2 : ∫ ω, Z t ω * Z t ω ∂μ = 0 := by
      rw [← h1]
      refine integral_congr_ae ?_
      filter_upwards [hA0 t ht] with ω hω
      simp [hω]
    rw [integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg _)
      ((hcov.left.memLp t ht).integrable_mul (hcov.left.memLp t ht))] at h2
    filter_upwards [h2] with ω hω
    simpa using hω
  -- indistinguishability
  have hall := StochIntAux.ae_forall_le_eq_of_continuous (μ := μ) (T := T)
    (X := fun t ω => Z (min t T) ω) (Y := fun _ _ => 0)
    (hcov.left.cont.mono fun ω hω => hω.comp_continuous (by fun_prop)
      fun t => ⟨le_min t.2 hT, min_le_right _ _⟩)
    (ae_of_all _ fun _ => continuous_const) fun t ht => by
      filter_upwards [hZt t ht] with ω hω
      simp only [min_eq_left ht]
      simpa using hω
  filter_upwards [hall] with ω hω t ht
  have := hω t.toNNReal (by rw [Real.coe_toNNReal t ht.1]; exact ht.2)
  simp only [Real.coe_toNNReal t ht.1, min_eq_left ht.2, hZdef] at this
  linarith

end QSSEPtoKPZ
