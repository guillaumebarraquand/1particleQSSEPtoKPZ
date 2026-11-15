/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Elementary

/-!
# The energy of a family of integrands (package C, task C3, auxiliary)

Tools for the construction of the Itô integral in `ItoIntegral/Basic.lean`. All results are in
the namespace `QSSEPtoKPZ.StochIntAux`.

* Elementary inequalities: `|x y| ≤ λ x² + λ⁻¹ y²`, `(x + y)² ≤ 2 x² + 2 y²` (in `[0, ∞]`), and
  `tendsto_zero_of_le_lam`: if `x_k ≤ λ a_k + λ⁻¹ b_k` for every `λ > 0`, with `a_k → 0` and
  `b_k` convergent, then `x_k → 0`.
* `measurable_tsum_real`: a countable sum of measurable real functions is measurable.
* `EnergyMeas h`: joint measurability of `h` on `(0, ∞) × Ω` (the first field of
  `IsItoIntegrable`), and its stability.
* The energy `𝔼 ∫_0^T ∑ᵢ hᵢ² ds`: measurability of the path energy, `energy_add_le`
  (`E(f + g) ≤ 2 E(f) + 2 E(g)`), monotonicity in `T`, scaling, finiteness for elementary
  integrands.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

namespace StochIntAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*}

/-! ### Elementary inequalities -/

/-- `|x y| ≤ λ x² + λ⁻¹ y²` for `λ > 0`. -/
lemma abs_mul_le_lam (x y : ℝ) {l : ℝ} (hl : 0 < l) : |x * y| ≤ l * x ^ 2 + l⁻¹ * y ^ 2 := by
  have hm : l * l⁻¹ = 1 := mul_inv_cancel₀ hl.ne'
  rw [abs_mul, ← sq_abs x, ← sq_abs y]
  have ha : 0 ≤ |x| := abs_nonneg x
  have hb : 0 ≤ |y| := abs_nonneg y
  refine le_of_mul_le_mul_left ?_ hl
  have e : l * (l * |x| ^ 2 + l⁻¹ * |y| ^ 2) = l ^ 2 * |x| ^ 2 + |y| ^ 2 := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, hm]; ring
  rw [e]
  nlinarith [sq_nonneg (l * |x| - |y|), mul_nonneg (mul_nonneg hl.le ha) hb]

/-- `‖x‖ₑ² = (x²)⁺` for a real `x`. -/
lemma enorm_sq_eq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- `‖x y‖ₑ ≤ λ ‖x‖ₑ² + λ⁻¹ ‖y‖ₑ²` for `0 < λ < ∞`. -/
lemma enorm_mul_le_lam (x y : ℝ) {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ∞) :
    ‖x * y‖ₑ ≤ l * ‖x‖ₑ ^ 2 + l⁻¹ * ‖y‖ₑ ^ 2 := by
  lift l to ℝ≥0 using hlt
  have hl : (0 : ℝ) < l := by
    have : (l : ℝ≥0∞) ≠ 0 := hl0
    exact_mod_cast pos_iff_ne_zero.2 (by exact_mod_cast this)
  rw [enorm_sq_eq, enorm_sq_eq, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_inv_of_pos hl, ← ENNReal.ofReal_mul hl.le,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hl.le), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
  exact ENNReal.ofReal_le_ofReal (abs_mul_le_lam x y hl)

/-- `‖x + y‖ₑ² ≤ 2 ‖x‖ₑ² + 2 ‖y‖ₑ²`. -/
lemma enorm_add_sq_le (x y : ℝ) : ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  rw [enorm_sq_eq, enorm_sq_eq, enorm_sq_eq, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])

/-- `‖a b - c d‖ₑ ≤ λ ‖a - c‖ₑ² + λ⁻¹ ‖b‖ₑ² + λ⁻¹ ‖c‖ₑ² + λ ‖b - d‖ₑ²` for `0 < λ < ∞`. -/
lemma enorm_mul_sub_mul_le (a b c d : ℝ) {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ∞) :
    ‖a * b - c * d‖ₑ ≤ l * ‖a - c‖ₑ ^ 2 + l⁻¹ * ‖b‖ₑ ^ 2 + l⁻¹ * ‖c‖ₑ ^ 2 +
      l * ‖b - d‖ₑ ^ 2 := by
  have e : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [e]
  refine (enorm_add_le _ _).trans ?_
  have h1 := enorm_mul_le_lam (a - c) b hl0 hlt
  have h2 := enorm_mul_le_lam c (b - d) (ENNReal.inv_ne_zero.2 hlt) (ENNReal.inv_ne_top.2 hl0)
  rw [inv_inv] at h2
  calc ‖(a - c) * b‖ₑ + ‖c * (b - d)‖ₑ ≤ (l * ‖a - c‖ₑ ^ 2 + l⁻¹ * ‖b‖ₑ ^ 2) +
        (l⁻¹ * ‖c‖ₑ ^ 2 + l * ‖b - d‖ₑ ^ 2) := add_le_add h1 h2
    _ = _ := by ring

/-- **The `λ`-trick.** If `x_k ≤ λ a_k + λ⁻¹ b_k` (eventually) for every `0 < λ < ∞`, with
`a_k → 0` and `b_k → β < ∞`, then `x_k → 0`. -/
lemma tendsto_zero_of_le_lam {x a b : ℕ → ℝ≥0∞} {β : ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 β)) (hβ : β ≠ ∞)
    (h : ∀ l : ℝ≥0∞, l ≠ 0 → l ≠ ∞ → ∀ᶠ k in atTop, x k ≤ l * a k + l⁻¹ * b k) :
    Tendsto x atTop (𝓝 0) := by
  have hls : ∀ l : ℝ≥0∞, l ≠ 0 → l ≠ ∞ → limsup x atTop ≤ l⁻¹ * β := by
    intro l h0 htop
    have ht : Tendsto (fun k => l * a k + l⁻¹ * b k) atTop (𝓝 (l⁻¹ * β)) := by
      have := (ENNReal.Tendsto.const_mul ha (Or.inr htop)).add
        (ENNReal.Tendsto.const_mul hb (Or.inr (ENNReal.inv_ne_top.2 h0)))
      simpa using this
    calc limsup x atTop ≤ limsup (fun k => l * a k + l⁻¹ * b k) atTop :=
          limsup_le_limsup (h l h0 htop)
      _ = l⁻¹ * β := ht.limsup_eq
  have ht : Tendsto (fun n : ℕ => ((n : ℝ≥0∞))⁻¹ * β) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hβ)
  have hlim : limsup x atTop ≤ 0 :=
    ge_of_tendsto ht ((eventually_ge_atTop 1).mono fun n hn =>
      hls n (by exact_mod_cast (show n ≠ 0 by omega)) (ENNReal.natCast_ne_top n))
  exact tendsto_of_le_liminf_of_limsup_le zero_le hlim

/-! ### Measurability of countable sums -/

set_option linter.deprecated false in
/-- A countable sum of measurable functions with values in `[0, ∞]` is measurable (wrapper of
the deprecated `Measurable.ennreal_tsum`, whose announced replacement is not yet in Mathlib). -/
lemma measurable_tsum_ennreal {α : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x :=
  Measurable.ennreal_tsum hf

/-- A countable sum of measurable real functions is measurable (it is `0` off the measurable set
where the series converges absolutely). -/
lemma measurable_tsum_real {α : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℝ}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  classical
  have hS : MeasurableSet {x | Summable fun i => f i x} := by
    have : {x | Summable fun i => f i x} = (fun x => ∑' i, ‖f i x‖ₑ) ⁻¹' {∞}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      refine ⟨fun hs => ?_, fun hs => Summable.of_enorm hs⟩
      have h1 : Summable fun i => ‖f i x‖₊ := by
        rw [← NNReal.summable_coe]; exact hs.norm
      simp only [enorm_eq_nnnorm]
      exact ENNReal.tsum_coe_ne_top_iff_summable.2 h1
    rw [this]
    exact (measurable_tsum_ennreal fun i => (hf i).enorm) (measurableSet_singleton ∞).compl
  have heq : (fun x => ∑' i, f i x) = fun x => if Summable (fun i => f i x) then
      (∑' i, ENNReal.ofReal (f i x)).toReal - (∑' i, ENNReal.ofReal (-f i x)).toReal
      else 0 := by
    funext x
    split_ifs with hs
    · rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
        ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      simp only [ENNReal.toReal_ofReal']
      have habs := hs.abs
      have h1 : Summable fun i => max (f i x) 0 :=
        habs.of_nonneg_of_le (fun _ => le_max_right _ _) (fun i => by
          rcases le_total 0 (f i x) with h | h
          · rw [max_eq_left h, abs_of_nonneg h]
          · rw [max_eq_right h]; exact abs_nonneg _)
      have h2 : Summable fun i => max (-f i x) 0 :=
        habs.of_nonneg_of_le (fun _ => le_max_right _ _) (fun i => by
          rcases le_total 0 (f i x) with h | h
          · rw [max_eq_right (by linarith)]; exact abs_nonneg _
          · rw [max_eq_left (by linarith), abs_of_nonpos h])
      rw [← h1.tsum_sub h2]
      congr 1
      funext i
      rcases le_total 0 (f i x) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · exact tsum_eq_zero_of_not_summable hs
  rw [heq]
  exact Measurable.ite hS
    ((measurable_tsum_ennreal fun i => (hf i).ennreal_ofReal).ennreal_toReal.sub
    (measurable_tsum_ennreal fun i => (hf i).neg.ennreal_ofReal).ennreal_toReal) measurable_const

/-! ### Joint measurability on `(0, ∞) × Ω` -/

/-- `h` is jointly measurable on `(0, ∞) × Ω` (extended by `0` for `s ≤ 0`); this is the first
field of `IsItoIntegrable`. -/
def EnergyMeas (h : ι → ℝ → Ω → ℝ) : Prop :=
  ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h i p.1 p.2 else 0

lemma ite_pos_add {a b : ℝ} (P : Prop) [Decidable P] :
    (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
  split_ifs <;> simp

lemma EnergyMeas.add {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) (hg : EnergyMeas g) :
    EnergyMeas fun i s ω => f i s ω + g i s ω := fun i => by
  simp only [ite_pos_add]
  exact (hf i).add (hg i)

lemma EnergyMeas.const_mul {f : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) (c : ℝ) :
    EnergyMeas fun i s ω => c * f i s ω := fun i => by
  have : (fun p : ℝ × Ω => if 0 < p.1 then c * f i p.1 p.2 else 0) =
      fun p => c * (if 0 < p.1 then f i p.1 p.2 else 0) := by
    funext p; split_ifs <;> simp
  rw [this]
  exact (hf i).const_mul c

lemma EnergyMeas.sub {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) (hg : EnergyMeas g) :
    EnergyMeas fun i s ω => f i s ω - g i s ω := by
  have := hf.add (hg.const_mul (-1))
  simpa [sub_eq_add_neg] using this

lemma EnergyMeas.congr {f g : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (h : ∀ i s ω, 0 < s → g i s ω = f i s ω) : EnergyMeas g := fun i => by
  have : (fun p : ℝ × Ω => if 0 < p.1 then g i p.1 p.2 else 0) =
      fun p => if 0 < p.1 then f i p.1 p.2 else 0 := by
    funext p; split_ifs with hp
    · exact h i p.1 p.2 hp
    · rfl
  rw [this]
  exact hf i

/-- For fixed `ω`, `s ↦ hᵢ(s, ω)` is measurable on `(0, ∞)` (extended by `0`). -/
lemma EnergyMeas.measurable_ext {f : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) (i : ι) (ω : Ω) :
    Measurable fun s => if 0 < s then f i s ω else 0 :=
  (hf i).comp (measurable_prodMk_right (y := ω))

/-- On `(0, T]`, the extension by `0` agrees with the function. -/
lemma ae_restrict_Ioc_pos (T : ℝ) : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), 0 < s :=
  (ae_restrict_mem measurableSet_Ioc).mono fun _ hs => hs.1

namespace ElemIntegrand

variable {𝓖 : Filtration ℝ≥0 mΩ}

open Classical in
lemma toFun_cons (bl : ElemBlock 𝓖 ι) (e : ElemIntegrand 𝓖 ι) (i : ι) (s : ℝ) (ω : Ω) :
    QSSEPtoKPZ.ElemIntegrand.toFun (bl :: e) i s ω =
      (if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0) +
        QSSEPtoKPZ.ElemIntegrand.toFun e i s ω := by
  simp [QSSEPtoKPZ.ElemIntegrand.toFun]

/-- An elementary integrand is jointly measurable. -/
lemma measurable_toFun (e : ElemIntegrand 𝓖 ι) (i : ι) :
    Measurable fun p : ℝ × Ω => QSSEPtoKPZ.ElemIntegrand.toFun e i p.1 p.2 := by
  classical
  induction e with
  | nil => simp [QSSEPtoKPZ.ElemIntegrand.toFun_nil]
  | cons bl e ih =>
    simp only [toFun_cons]
    refine Measurable.add ?_ ih
    refine Measurable.ite ?_ (bl.measurable_ξ.comp measurable_snd) measurable_const
    exact (MeasurableSet.const _).inter ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))

/-- An elementary integrand vanishes at times `s ≤ 0`. -/
lemma toFun_of_nonpos (e : ElemIntegrand 𝓖 ι) (i : ι) {s : ℝ} (hs : s ≤ 0) (ω : Ω) :
    QSSEPtoKPZ.ElemIntegrand.toFun e i s ω = 0 := by
  classical
  induction e with
  | nil => simp [QSSEPtoKPZ.ElemIntegrand.toFun_nil]
  | cons bl e ih =>
    rw [toFun_cons, ih, add_zero]
    split_ifs with h
    · exact absurd (h.2.1.trans_le hs) (not_lt.2 (NNReal.coe_nonneg _))
    · rfl

lemma energyMeas_toFun (e : ElemIntegrand 𝓖 ι) :
    EnergyMeas (QSSEPtoKPZ.ElemIntegrand.toFun e) := fun i =>
  Measurable.ite (measurableSet_lt measurable_const measurable_fst) (measurable_toFun e i)
    measurable_const

/-- `∑ᵢ eᵢ(s, ω)²` is bounded uniformly in `(s, ω)`. -/
lemma exists_tsum_sq_le (e : ElemIntegrand 𝓖 ι) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ s ω, ∑' i, ‖QSSEPtoKPZ.ElemIntegrand.toFun e i s ω‖ₑ ^ 2 ≤ K := by
  classical
  induction e with
  | nil => exact ⟨0, by simp, fun s ω => by simp [QSSEPtoKPZ.ElemIntegrand.toFun_nil]⟩
  | cons bl e ih =>
    obtain ⟨K, hK, hb⟩ := ih
    obtain ⟨C, hC⟩ := bl.bdd
    refine ⟨2 * ‖C‖ₑ ^ 2 + 2 * K, by finiteness, fun s ω => ?_⟩
    have hblk : ∑' i, ‖(if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0)‖ₑ ^ 2 ≤
        ‖C‖ₑ ^ 2 := by
      rw [tsum_eq_single bl.i (fun i hi => by simp [Ne.symm hi])]
      gcongr
      split_ifs
      · rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal ((hC ω).trans (le_abs_self C))
      · simp
    calc ∑' i, ‖QSSEPtoKPZ.ElemIntegrand.toFun (bl :: e) i s ω‖ₑ ^ 2
        ≤ ∑' i, (2 * ‖(if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0)‖ₑ ^ 2 +
            2 * ‖QSSEPtoKPZ.ElemIntegrand.toFun e i s ω‖ₑ ^ 2) :=
          ENNReal.tsum_le_tsum fun i => by rw [toFun_cons]; exact enorm_add_sq_le _ _
      _ = 2 * ∑' i, ‖(if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0)‖ₑ ^ 2 +
            2 * ∑' i, ‖QSSEPtoKPZ.ElemIntegrand.toFun e i s ω‖ₑ ^ 2 := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ 2 * ‖C‖ₑ ^ 2 + 2 * K := by gcongr; exact hb s ω

end ElemIntegrand

/-! ### The energy -/

section Energy

variable {μ : Measure Ω}

omit mΩ in
/-- The path energy only depends on `‖hᵢ(s)‖` at times `s > 0`. -/
lemma pathEnergy_congr {f g : ι → ℝ → Ω → ℝ} (T : ℝ) (ω : Ω)
    (h : ∀ i s, 0 < s → ‖f i s ω‖ₑ = ‖g i s ω‖ₑ) : pathEnergy f T ω = pathEnergy g T ω :=
  setLIntegral_congr_fun measurableSet_Ioc fun s hs => by simp only [h _ s hs.1]

lemma energy_congr {f g : ι → ℝ → Ω → ℝ} (T : ℝ)
    (h : ∀ i s ω, 0 < s → ‖f i s ω‖ₑ = ‖g i s ω‖ₑ) : energy μ f T = energy μ g T :=
  lintegral_congr fun ω => pathEnergy_congr T ω fun i s hs => h i s ω hs

lemma energy_sub_comm (f g : ι → ℝ → Ω → ℝ) (T : ℝ) :
    energy μ (fun i s ω => f i s ω - g i s ω) T = energy μ (fun i s ω => g i s ω - f i s ω) T :=
  energy_congr T fun _ _ _ _ => enorm_sub_rev _ _

/-- The integrand `s ↦ ∑ᵢ ‖hᵢ(s, ω)‖ₑ²` is measurable on `(0, T]`. -/
lemma aemeasurable_tsum_sq [Countable ι] {f : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) (T : ℝ)
    (ω : Ω) : AEMeasurable (fun s => ∑' i, ‖f i s ω‖ₑ ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
  refine (measurable_tsum_ennreal fun i => ((hf.measurable_ext i ω).enorm.pow_const 2)
    ).aemeasurable.congr ?_
  filter_upwards [ae_restrict_Ioc_pos T] with s hs
  simp [hs]

/-- The path energy is measurable. -/
lemma measurable_pathEnergy [Countable ι] {f : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f) (T : ℝ) :
    Measurable (pathEnergy f T) := by
  have : pathEnergy f T = fun ω => ∫⁻ s in Set.Ioc 0 T,
      ∑' i, ‖(if 0 < s then f i s ω else 0)‖ₑ ^ 2 :=
    funext fun ω => setLIntegral_congr_fun measurableSet_Ioc fun s hs => by simp [hs.1]
  rw [this]
  exact Measurable.lintegral_prod_right'
    (f := fun p : Ω × ℝ => ∑' i, ‖(if 0 < p.2 then f i p.2 p.1 else 0)‖ₑ ^ 2)
    (measurable_tsum_ennreal fun i => (((hf i).comp measurable_swap).enorm.pow_const 2))

/-- `E(F) ≤ 2 E(f) + 2 E(g)` if `F = f + g` (with `f` jointly measurable). -/
lemma energy_add_le [Countable ι] {f g F : ι → ℝ → Ω → ℝ} (hf : EnergyMeas f)
    (hF : ∀ i s ω, F i s ω = f i s ω + g i s ω) (T : ℝ) :
    energy μ F T ≤ 2 * energy μ f T + 2 * energy μ g T := by
  have hp : ∀ ω, pathEnergy F T ω ≤ 2 * pathEnergy f T ω + 2 * pathEnergy g T ω := by
    intro ω
    unfold pathEnergy
    rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num),
      ← lintegral_add_left' ((aemeasurable_tsum_sq hf T ω).const_mul 2)]
    refine lintegral_mono fun s => ?_
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun i => by rw [hF]; exact enorm_add_sq_le _ _
  unfold energy
  rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_left' (((measurable_pathEnergy hf T).const_mul 2).aemeasurable)]
  exact lintegral_mono hp

/-- The energy is nondecreasing in the horizon. -/
lemma energy_mono (f : ι → ℝ → Ω → ℝ) {T T' : ℝ} (h : T ≤ T') :
    energy μ f T ≤ energy μ f T' :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Ioc_subset_Ioc_right h)

/-- `E(c f) = c² E(f)`. -/
lemma energy_const_mul (c : ℝ) (f : ι → ℝ → Ω → ℝ) (T : ℝ) :
    energy μ (fun i s ω => c * f i s ω) T = ‖c‖ₑ ^ 2 * energy μ f T := by
  unfold energy pathEnergy
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_congr fun s => ?_
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext i
  rw [enorm_mul, mul_pow]

/-- The energy of an elementary integrand is finite. -/
lemma energy_elem_lt_top [IsFiniteMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (e : QSSEPtoKPZ.ElemIntegrand 𝓖 ι) (T : ℝ) : energy μ e.toFun T < ∞ := by
  obtain ⟨K, hK, hb⟩ := ElemIntegrand.exists_tsum_sq_le e
  calc energy μ e.toFun T ≤ ∫⁻ _, ∫⁻ _ in Set.Ioc (0 : ℝ) T, K ∂volume ∂μ :=
        lintegral_mono fun ω => lintegral_mono fun s => hb s ω
    _ < ∞ := by
      simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioc]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hK.lt_top ENNReal.ofReal_lt_top)
        (measure_lt_top _ _)

end Energy

end StochIntAux

end QSSEPtoKPZ
