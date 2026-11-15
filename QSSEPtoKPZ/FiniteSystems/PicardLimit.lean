/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.PicardAux
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Auxiliary results for the limit of the Picard iteration (task L2b)

Deterministic lemmas used in `FiniteSystems/Picard.lean`:

* `picardEx_ofReal_sq_le`: `c ≤ a + b ⇒ c² ≤ 2a² + 2b²`, in `[0, ∞]`;
* `picardEx_measurable_iSup`: `ω ↦ sup_{t ∈ [0,n]} ‖X_t(ω)‖²` is measurable for a process with
  measurable norms and continuous paths (supremum over the rationals);
* `picardEx_gronwall`: the iterated Gronwall bound `d_k(t) ≤ d_0(T) (Ct)^k / k!` from
  `d_{k+1}(t) ≤ C ∫_0^t d_k(s) ds`;
* `picardEx_tsum_lt_top`: `∑_k 2^k d_0 (CT)^k / k! < ∞`;
* `picardEx_sq_norm_sub_le`: for a sequence `f`, `‖f_p - f_m‖² ≤ 2 (1/2)^m ∑_k 2^k ‖f_{k+1} - f_k‖²`
  (`m ≤ p`; Cauchy–Schwarz with the weights `2^{-k}`);
* `picardEx_uniform`: a sequence of functions satisfying such a bound converges uniformly.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal Nat

noncomputable section

namespace QSSEPtoKPZ

/-- `c ≤ a + b` (all nonnegative) implies `c² ≤ 2a² + 2b²`, in `[0, ∞]`. -/
theorem picardEx_ofReal_sq_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : c ≤ a + b) :
    ENNReal.ofReal (c ^ 2) ≤ 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
  have key : c ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  refine (ENNReal.ofReal_le_ofReal key).trans_eq ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- **Measurability of the running supremum.** If `ω ↦ ‖X_t(ω)‖` is measurable for every `t ≥ 0`
and every path `t ↦ X_t(ω)` is continuous on `[0, ∞)`, then
`ω ↦ sup_{t ∈ [0,n]} ‖X_t(ω)‖²` is measurable (it is the supremum over the rationals). -/
theorem picardEx_measurable_iSup {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {X : ℝ → Ω → E} (hm : ∀ t : ℝ≥0, Measurable fun ω => ‖X t ω‖)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) {n : ℝ} (hn : 0 ≤ n) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖X t ω‖ ^ 2) := by
  have e : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) n, ENNReal.ofReal (‖X t ω‖ ^ 2)) =
      fun ω => ⨆ q : ℚ, ENNReal.ofReal (‖X (max 0 (min (q : ℝ) n)) ω‖ ^ 2) := by
    funext ω
    refine le_antisymm (iSup₂_le fun t ht => ?_)
      (picardAux_iSup_rat_le (X := fun t => ‖X t ω‖) hn)
    exact picardAux_ofReal_sq_le_iSup_rat (X := fun t => ‖X t ω‖) (hc ω).norm ht
  rw [e]
  refine Measurable.iSup fun q => ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ 2)
  have := hm (max 0 (min (q : ℝ) n)).toNNReal
  rwa [Real.coe_toNNReal _ (le_max_left _ _)] at this

/-- `∫_0^t C (Cs)^k / k! ds = (Ct)^{k+1} / (k+1)!`, in `[0, ∞]`. -/
private lemma picardEx_lintegral_pow {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (k : ℕ) :
    ENNReal.ofReal C * ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((C * s) ^ k / k !) =
      ENNReal.ofReal ((C * t) ^ (k + 1) / (k + 1)!) := by
  have hcont : Continuous fun s : ℝ => (C * s) ^ k / k ! := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_Icc (μ := volume))
      (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => by
        have := hs.1
        positivity),
    ← ENNReal.ofReal_mul hC, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht]
  congr 1
  have e : (fun s : ℝ => (C * s) ^ k / k !) = fun s => (C ^ k / k !) * s ^ k := by
    funext s; rw [mul_pow]; ring
  rw [e, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **Iterated Gronwall bound.** If `d_0(t) ≤ d_0(T)` and `d_{k+1}(t) ≤ C ∫_0^t d_k(s) ds` for
`t ∈ [0,T]`, then `d_k(t) ≤ d_0(T) (Ct)^k / k!` for `t ∈ [0,T]`. -/
theorem picardEx_gronwall {d : ℕ → ℝ → ℝ≥0∞} {C T : ℝ} (hC : 0 ≤ C)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) T, d 0 t ≤ d 0 T)
    (hrec : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      d (k + 1) t ≤ ENNReal.ofReal C * ∫⁻ s in Set.Icc (0 : ℝ) t, d k s) :
    ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, d k t ≤ d 0 T * ENNReal.ofReal ((C * t) ^ k / k !) := by
  intro k
  induction k with
  | zero =>
    intro t ht
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, mul_one]
    exact h0 t ht
  | succ k ih =>
    intro t ht
    calc d (k + 1) t ≤ ENNReal.ofReal C * ∫⁻ s in Set.Icc (0 : ℝ) t, d k s := hrec k t ht
      _ ≤ ENNReal.ofReal C * ∫⁻ s in Set.Icc (0 : ℝ) t,
            d 0 T * ENNReal.ofReal ((C * s) ^ k / k !) := by
          exact mul_le_mul' le_rfl
            (setLIntegral_mono' measurableSet_Icc fun s hs => ih s ⟨hs.1, hs.2.trans ht.2⟩)
      _ = d 0 T * (ENNReal.ofReal C *
            ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((C * s) ^ k / k !)) := by
          rw [lintegral_const_mul _ (by fun_prop)]
          ring
      _ = d 0 T * ENNReal.ofReal ((C * t) ^ (k + 1) / (k + 1)!) := by
          rw [picardEx_lintegral_pow hC ht.1]

/-- `∑_k 2^k d (CT)^k / k! < ∞` for `d < ∞`. -/
theorem picardEx_tsum_lt_top {d : ℝ≥0∞} (hd : d < ⊤) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) :
    ∑' k : ℕ, (2 : ℝ≥0∞) ^ k * (d * ENNReal.ofReal ((C * T) ^ k / k !)) < ⊤ := by
  have e : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * (d * ENNReal.ofReal ((C * T) ^ k / k !)) =
      d * ENNReal.ofReal ((2 * C * T) ^ k / k !) := fun k => by
    rw [show (2 * C * T) ^ k / k ! = 2 ^ k * ((C * T) ^ k / k !) by rw [mul_assoc, mul_pow]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    ring
  simp_rw [e]
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    (Real.summable_pow_div_factorial _)]
  exact ENNReal.mul_lt_top hd ENNReal.ofReal_lt_top

/-- **Cauchy–Schwarz for the increments of a sequence.** For `m ≤ p`,
`‖f_p - f_m‖² ≤ 2 (1/2)^m ∑_k 2^k ‖f_{k+1} - f_k‖²`, in `[0, ∞]`, with any upper bounds
`u_k ≥ ‖f_{k+1} - f_k‖²`. -/
theorem picardEx_sq_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E}
    {u : ℕ → ℝ≥0∞} (hu : ∀ k, ENNReal.ofReal (‖f (k + 1) - f k‖ ^ 2) ≤ u k) {m p : ℕ}
    (hmp : m ≤ p) :
    ENNReal.ofReal (‖f p - f m‖ ^ 2) ≤
      ENNReal.ofReal (2 * (1 / 2) ^ m) * ∑' k, (2 : ℝ≥0∞) ^ k * u k := by
  set v : ℕ → ℝ := fun k => ‖f (k + 1) - f k‖ with hv
  have htri : ‖f p - f m‖ ≤ ∑ k ∈ Finset.Ico m p, v k := by
    induction p, hmp using Nat.le_induction with
    | base => simp
    | succ p hmp ih =>
      rw [Finset.sum_Ico_succ_top hmp]
      calc ‖f (p + 1) - f m‖ ≤ ‖f p - f m‖ + ‖f (p + 1) - f p‖ := by
            rw [add_comm (‖f p - f m‖)]
            exact norm_sub_le_norm_sub_add_norm_sub (f (p + 1)) (f p) (f m)
        _ ≤ ‖f p - f m‖ + v p := le_rfl
        _ ≤ (∑ k ∈ Finset.Ico m p, v k) + v p := add_le_add ih le_rfl
  rcases hmp.eq_or_lt with rfl | hlt
  · simp
  have hg : ∀ k ∈ Finset.Ico m p, (0 : ℝ) < (1 / 2) ^ k := fun k _ => by positivity
  have hne : (0 : ℝ) < ∑ k ∈ Finset.Ico m p, (1 / 2 : ℝ) ^ k :=
    Finset.sum_pos hg ⟨m, Finset.mem_Ico.2 ⟨le_rfl, hlt⟩⟩
  have hcs := Finset.sq_sum_div_le_sum_sq_div (Finset.Ico m p) v hg
  rw [div_le_iff₀ hne] at hcs
  have hgeom : ∑ k ∈ Finset.Ico m p, (1 / 2 : ℝ) ^ k ≤ 2 * (1 / 2) ^ m := by
    have := geom_sum_Ico_le_of_lt_one (m := m) (n := p) (x := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, div_inv_eq_mul] at this
    linarith
  have e : ∀ k, v k ^ 2 / (1 / 2) ^ k = 2 ^ k * v k ^ 2 := fun k => by
    rw [one_div, inv_pow, div_inv_eq_mul]; ring
  simp_rw [e] at hcs
  have hv0 : ∀ k, 0 ≤ (2 : ℝ) ^ k * v k ^ 2 := fun k =>
    mul_nonneg (pow_nonneg (by norm_num) k) (sq_nonneg _)
  have hreal : ‖f p - f m‖ ^ 2 ≤ 2 * (1 / 2) ^ m * ∑ k ∈ Finset.Ico m p, 2 ^ k * v k ^ 2 := by
    calc ‖f p - f m‖ ^ 2 ≤ (∑ k ∈ Finset.Ico m p, v k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ _ := hcs.trans (by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hgeom
            (Finset.sum_nonneg fun k _ => hv0 k))
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => hv0 k)]
  gcongr
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (ENNReal.sum_le_tsum _)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  gcongr
  exact hu k

/-- **Uniform convergence** of a sequence of functions with
`‖f_p(a) - f_m(a)‖² ≤ 2 (1/2)^m c` on `S` for `m ≤ p`: the pointwise limits exist on `S`, the
convergence is uniform on `S`, and `‖lim f(a) - f_m(a)‖² ≤ 2 (1/2)^m c`. -/
theorem picardEx_uniform {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → α → E} {S : Set α} {c : ℝ}
    (h : ∀ m p, m ≤ p → ∀ a ∈ S, ‖f p a - f m a‖ ^ 2 ≤ 2 * (1 / 2) ^ m * c) :
    (∀ a ∈ S, Tendsto (fun m => f m a) atTop (𝓝 (limUnder atTop fun m => f m a))) ∧
      TendstoUniformlyOn f (fun a => limUnder atTop fun m => f m a) atTop S ∧
      ∀ m, ∀ a ∈ S, ‖(limUnder atTop fun m => f m a) - f m a‖ ^ 2 ≤ 2 * (1 / 2) ^ m * c := by
  set b : ℕ → ℝ := fun m => Real.sqrt (2 * (1 / 2) ^ m * c) with hb
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => 2 * (1 / 2 : ℝ) ^ m * c) atTop (𝓝 (2 * 0 * c)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2).mul_const c
    rw [mul_zero, zero_mul] at this
    have h2 := (Real.continuous_sqrt.tendsto 0).comp this
    rwa [Real.sqrt_zero] at h2
  have hle : ∀ m p, m ≤ p → ∀ a ∈ S, ‖f p a - f m a‖ ≤ b m := fun m p hmp a ha =>
    Real.le_sqrt_of_sq_le (h m p hmp a ha)
  have hlim : ∀ a ∈ S, Tendsto (fun m => f m a) atTop (𝓝 (limUnder atTop fun m => f m a)) := by
    intro a ha
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * b N) (fun p q N hp hq => ?_)
      (by simpa using hb0.const_mul 2)
    rw [dist_eq_norm]
    calc ‖f p a - f q a‖ ≤ ‖f p a - f N a‖ + ‖f q a - f N a‖ := by
          rw [← norm_neg (f q a - f N a)]
          refine (norm_sub_le_norm_sub_add_norm_sub _ (f N a) _).trans_eq ?_
          rw [neg_sub]
      _ ≤ b N + b N := add_le_add (hle N p hp a ha) (hle N q hq a ha)
      _ = 2 * b N := by ring
  have hbd : ∀ m, ∀ a ∈ S, ‖(limUnder atTop fun m => f m a) - f m a‖ ≤ b m := by
    intro m a ha
    have ht : Tendsto (fun p => ‖f p a - f m a‖) atTop
        (𝓝 ‖(limUnder atTop fun m => f m a) - f m a‖) :=
      ((hlim a ha).sub_const (f m a)).norm
    exact le_of_tendsto ht (eventually_atTop.2 ⟨m, fun p hp => hle m p hp a ha⟩)
  refine ⟨hlim, ?_, fun m a ha => ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hb0).2 ε hε] with m hm a ha
    rw [dist_eq_norm]
    exact (hbd m a ha).trans_lt hm
  · have h1 := hbd m a ha
    have h2 : 0 ≤ 2 * (1 / 2 : ℝ) ^ m * c := by
      have := h m m le_rfl a ha
      simp only [sub_self, norm_zero] at this
      linarith [sq_nonneg (0 : ℝ)]
    calc _ ≤ b m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = _ := Real.sq_sqrt h2

end QSSEPtoKPZ
