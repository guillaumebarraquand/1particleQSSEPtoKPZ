/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Lemma82
public import QSSEPtoKPZ.FiniteSystems.AtomicTV
public import QSSEPtoKPZ.Tightness.ExpMoments

/-!
# Proposition 8.1 (task L8)

Interfaces of task I0‴ of Stage 5 (`docs/stage5-interfaces.md`), proved in task L8.
`docs/stage5-design.md`, Sections 1.2 (e), 3.4 (L8). Lemma 8.2 (`lemma82_bound`, task L6) is used
as a black box.

* `prop81Rhs n T ε L` (definition, complete): the right side of the quantitative bound,
  `(16/ε²) nT (8 + nT/2) e^{2θ_n L - r L / 3} + 4 e^{2T} / (ε cosh ℓ)`, with
  `r = min(1, L/(nT))` and `ℓ = n^{-1/2}(L - n^{3/4} T)`.
* `prop81_bound`: for `n ≥ 1`, `L ≥ 1`, `T, ε > 0` with `n^{3/4} T < L`,
  `ℙ*(sup_{t ≤ T} ∑ₓ |𝔷^L_n(t,x) - 𝔷_n(t,x)| > ε) ≤ prop81Rhs n T ε L`
  ((8.3), Lemma 8.2 with `S = nT/2`, Chebyshev, `rwTail_le` with `r`, `cosh_sub_one_le`,
  Lemma 5.2 ((5.1)) for the atoms outside `Λ_L`).
* `prop81Rhs_tendsto`, `prop81Rhs_tendsto_enat`: the deterministic bound tends to `0` along
  `n_k → ∞` with `L_k / n_k^{3/4} → ∞` (the article's asymptotics), for integer `L_k`
  (Proposition 8.1) and for `L_k ∈ ℕ ∪ {∞}` in the form of the hypothesis of `main_theorem`
  (task M3; the indices with `L_k = ∞` contribute `0`).
* `prop81_tendsto`: twin of `prop_8_1` (`FiniteSystems/Statements.lean`), which quotes it
  (`etvDist_sum_dirac_le` with `tiltedMeasureBox_eq_sum`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- The right side of the quantitative form of Proposition 8.1:
`(16/ε²) nT (8 + nT/2) exp(2θ_n L - r L/3) + 4 e^{2T} / (ε cosh ℓ)`, `r = min(1, L/(nT))`,
`ℓ = (L - n^{3/4} T) / n^{1/2}`. -/
def prop81Rhs (n T ε : ℝ) (L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (16 / ε ^ 2 * (n * T * (8 + n * T / 2)) *
      Real.exp (2 * thetaN n * L - min 1 (L / (n * T)) * L / 3)) +
    ENNReal.ofReal (4 * Real.exp (2 * T) /
      (ε * Real.cosh ((L - n ^ (3 / 4 : ℝ) * T) / n ^ (1 / 2 : ℝ))))

/-! ### Auxiliary lemmas -/

/-- On an `ω` where `ψ^L` vanishes outside `Λ_L`, `𝔷^L_n(t,x) = 0` for `x ∉ Λ_L`, `t ≥ 0`. -/
private lemma prop81_zN_eq_zero {ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {L : ℕ}
    (hsupp : ∀ (t : ℝ≥0) (x : ℤ), x ∉ box (L : ℕ∞) → ψL t ω x = 0)
    {n t : ℝ} (hn : 0 ≤ n) (ht : 0 ≤ t) {x : ℤ} (hx : x ∉ box (L : ℕ∞)) :
    zN n ψL ω t x = 0 := by
  have h : ψL (n * t / 2) ω x = 0 := hsupp ⟨n * t / 2, by positivity⟩ x hx
  simp [zN, density, h]

/-- **Pointwise form of (8.3)**: for `t ∈ [0,T]`, on an `ω` where `ψ^L` vanishes outside `Λ_L`
and the series `∑ₓ 𝔷_n(t,x) e^{b y_n(t,x)}` converge (`b ∈ [-1,1]`),
`∑ₓ |𝔷^L_n(t,x) - 𝔷_n(t,x)| ≤ e^{θ_n L} ∑_{x ∈ Λ_L} |P(nt/2,x) - P^L(nt/2,x)| + 𝖹_n(t;cosh)/cosh ℓ`,
with `ℓ = (L - n^{3/4} T)/n^{1/2}` (`|y_n(t,x)| ≥ ℓ` outside `Λ_L`). -/
private lemma prop81_pointwise {ψ ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} {ω : Ω} {L : ℕ}
    (hsupp : ∀ (t : ℝ≥0) (x : ℤ), x ∉ box (L : ℕ∞) → ψL t ω x = 0)
    {n T t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) (htT : t ≤ T) (hℓ : n ^ (3 / 4 : ℝ) * T < L)
    (hsum : ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      Summable fun x => zN n ψ ω t x * Real.exp (b * rescaledPosition n t x)) :
    ∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x| ≤
      Real.exp (thetaN n * L) * (∑ x ∈ Finset.Icc (-(L : ℤ)) L,
          |density ψ ω (n * t / 2) x - density ψL ω (n * t / 2) x|) +
        pairZ n ψ ω t Real.cosh / Real.cosh ((L - n ^ (3 / 4 : ℝ) * T) / n ^ (1 / 2 : ℝ)) := by
  set I := Finset.Icc (-(L : ℤ)) L with hI
  set ℓ := (L - n ^ (3 / 4 : ℝ) * T) / n ^ (1 / 2 : ℝ) with hℓdef
  have hn0 : 0 < n := by linarith
  have h12 : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have h34 : 0 ≤ n ^ (3 / 4 : ℝ) := (Real.rpow_pos_of_pos hn0 _).le
  have hθ : 0 < thetaN n := Real.rpow_pos_of_pos hn0 _
  have hlam : 0 ≤ lambdaN n := by unfold lambdaN; linarith [Real.one_le_cosh (thetaN n)]
  have hℓ0 : 0 ≤ ℓ := div_nonneg (by linarith) h12.le
  have hzψ : ∀ x, 0 ≤ zN n ψ ω t x := fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hzL' : ∀ x, x ∉ box (L : ℕ∞) → zN n ψL ω t x = 0 := fun x hx =>
    prop81_zN_eq_zero hsupp hn0.le ht hx
  have hzL : ∀ x, x ∉ I → zN n ψL ω t x = 0 := fun x hx =>
    hzL' x fun h => hx (pairing_mem_box_iff.1 h)
  have hs0 : Summable (zN n ψ ω t) := by
    simpa using hsum 0 ⟨by norm_num, by norm_num⟩
  have hsL : Summable (zN n ψL ω t) := summable_of_ne_finset_zero (s := I) hzL
  have hcosh : Summable fun x => zN n ψ ω t x * Real.cosh (rescaledPosition n t x) := by
    have h1 := hsum 1 ⟨by norm_num, by norm_num⟩
    have h2 := hsum (-1) ⟨by norm_num, by norm_num⟩
    refine ((h1.add h2).div_const 2).congr fun x => ?_
    rw [Real.cosh_eq]
    simp only [one_mul, neg_mul]
    ring
  set f1 : ℤ → ℝ := fun x => if x ∈ I then Real.exp (thetaN n * L) *
    |density ψ ω (n * t / 2) x - density ψL ω (n * t / 2) x| else 0 with hf1def
  set f2 : ℤ → ℝ := fun x => zN n ψ ω t x * Real.cosh (rescaledPosition n t x) / Real.cosh ℓ
    with hf2def
  have hf1 : Summable f1 := summable_of_ne_finset_zero (s := I) fun x hx => ite_eq_right hx
  have hf2 : Summable f2 := hcosh.div_const _
  have hle : ∀ x, |zN n ψL ω t x - zN n ψ ω t x| ≤ f1 x + f2 x := by
    intro x
    by_cases hx : x ∈ I
    · have hf2x : 0 ≤ f2 x :=
        div_nonneg (mul_nonneg (hzψ x) (Real.cosh_pos _).le) (Real.cosh_pos _).le
      have : |zN n ψL ω t x - zN n ψ ω t x| ≤ f1 x := by
        simp only [hf1def, ite_eq_left hx, zN]
        rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
        have hxL : (x : ℝ) ≤ L := by
          have := (Finset.mem_Icc.1 hx).2
          exact_mod_cast this
        nlinarith [mul_nonneg (mul_nonneg hn0.le hlam) ht]
      linarith
    · have hxb : x ∉ box (L : ℕ∞) := fun h => hx (pairing_mem_box_iff.1 h)
      rw [hzL' x hxb, zero_sub, abs_neg, abs_of_nonneg (hzψ x)]
      simp only [hf1def, ite_eq_right hx, zero_add, hf2def]
      rw [mul_div_assoc]
      refine le_mul_of_one_le_right (hzψ x) ((one_le_div (Real.cosh_pos _)).2 ?_)
      rw [Real.cosh_le_cosh, abs_of_nonneg hℓ0]
      have htT' : n ^ (3 / 4 : ℝ) * t ≤ n ^ (3 / 4 : ℝ) * T := mul_le_mul_of_nonneg_left htT h34
      have ht' : 0 ≤ n ^ (3 / 4 : ℝ) * t := mul_nonneg h34 ht
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
      unfold rescaledPosition
      rcases hx with hx | hx
      · have hx' : (x : ℝ) ≤ -(L : ℝ) := by
          have : x ≤ -(L : ℤ) := hx.le
          exact_mod_cast this
        refine le_abs.2 (Or.inr ?_)
        rw [← neg_div]
        exact div_le_div_of_nonneg_right (by linarith) h12.le
      · have hx' : (L : ℝ) ≤ x := by
          have : (L : ℤ) ≤ x := hx.le
          exact_mod_cast this
        refine le_abs.2 (Or.inl ?_)
        exact div_le_div_of_nonneg_right (by linarith) h12.le
  calc ∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x| ≤ ∑' x, (f1 x + f2 x) :=
        (hsL.sub hs0).abs.tsum_le_tsum hle (hf1.add hf2)
    _ = ∑' x, f1 x + ∑' x, f2 x := hf1.tsum_add hf2
    _ = _ := by
      congr 1
      · rw [tsum_eq_sum (s := I) fun x hx => ite_eq_right hx, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x hx => ite_eq_left hx
      · rw [hf2def, tsum_div_const]
        rfl

/-- **The exponent of the first term** (the article's asymptotics): if `n ≥ 1`, `n^{1/4} ≥ 12`
and `L ≥ (1 + 12T) n^{3/4}`, then `2θ_n ≤ r/6` and `rL ≥ min(1, 1/T) n^{1/2}`, hence
`2θ_n L - rL/3 ≤ -min(1, 1/T) n^{1/2}/6`, with `r = min(1, L/(nT))`. -/
private lemma prop81_exponent_le {n T L : ℝ} (hn : 1 ≤ n) (hT : 0 < T)
    (ha : 12 ≤ n ^ (1 / 4 : ℝ)) (hL : (1 + 12 * T) * n ^ (3 / 4 : ℝ) ≤ L) :
    2 * thetaN n * L - min 1 (L / (n * T)) * L / 3 ≤
      -(min 1 (1 / T) * n ^ (1 / 2 : ℝ) / 6) := by
  have hn0 : 0 ≤ n := by linarith
  set a := n ^ (1 / 4 : ℝ) with hadef
  have e4 : n = a ^ 4 := by
    rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have e3 : n ^ (3 / 4 : ℝ) = a ^ 3 := by
    rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have e2 : n ^ (1 / 2 : ℝ) = a ^ 2 := by
    rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have eθ : thetaN n = a⁻¹ := by
    rw [thetaN, hadef, ← Real.rpow_neg hn0]; norm_num
  rw [e3] at hL
  rw [eθ, e2, e4]
  have ha0 : 0 < a := by linarith
  have ha3p : 0 < a ^ 3 := pow_pos ha0 3
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have ha3 : 12 * T * a ^ 3 ≤ L := by nlinarith
  have ha3' : a ^ 3 ≤ L := by nlinarith
  set r := min 1 (L / (a ^ 4 * T)) with hrdef
  have hr : 12 / a ≤ r := by
    refine le_min ((div_le_one ha0).2 ha) ?_
    rw [div_le_div_iff₀ ha0 (by positivity)]
    nlinarith
  have hm : min 1 (1 / T) * a ^ 2 ≤ r * L := by
    rw [hrdef, min_mul_of_nonneg _ _ hL0, one_mul]
    refine le_min ?_ ?_
    · calc min 1 (1 / T) * a ^ 2 ≤ 1 * a ^ 2 := by gcongr; exact min_le_left _ _
        _ ≤ a ^ 3 := by nlinarith
        _ ≤ L := ha3'
    · calc min 1 (1 / T) * a ^ 2 ≤ 1 / T * a ^ 2 := by gcongr; exact min_le_right _ _
        _ = a ^ 3 * a ^ 3 / (a ^ 4 * T) := by field_simp
        _ ≤ L * L / (a ^ 4 * T) := by gcongr
        _ = L / (a ^ 4 * T) * L := by ring
  have h2 : 2 * a⁻¹ * L ≤ r / 6 * L := by
    refine mul_le_mul_of_nonneg_right ?_ hL0
    have : 2 * a⁻¹ = 12 / a / 6 := by field_simp; ring
    linarith
  linarith

/-- `n T (8 + nT/2) e^{-m n^{1/2}/6} → 0` as `n → ∞` (`m > 0`). -/
private lemma prop81_poly_exp_tendsto {T m : ℝ} (hm : 0 < m) :
    Tendsto (fun n : ℝ => n * T * (8 + n * T / 2) * Real.exp (-(m * n ^ (1 / 2 : ℝ) / 6)))
      atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℝ => n ^ (1 / 2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (m / 6) (by positivity)
  have h4 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 (m / 6) (by positivity)
  have hH := ((h2.const_mul (8 * T)).add (h4.const_mul (T ^ 2 / 2))).comp hx
  simp only [mul_zero, add_zero] at hH
  refine hH.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n hn
  simp only [Function.comp]
  have e2 : (n ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = n := by rw [← Real.rpow_mul hn]; norm_num
  have e4 : (n ^ (1 / 2 : ℝ)) ^ (4 : ℝ) = n ^ 2 := by
    rw [← Real.rpow_mul hn, ← Real.rpow_natCast]; norm_num
  rw [e2, e4, show -(m / 6) * n ^ (1 / 2 : ℝ) = -(m * n ^ (1 / 2 : ℝ) / 6) by ring]
  ring

/-- **Quantitative form of Proposition 8.1** (internal). Let `ψ` (on `ℤ`) and `ψ^L` (on `Λ_L`,
`L ≥ 1`) be wave functions driven by the same Brownian family for the same filtration, `n ≥ 1`,
`T, ε > 0` with `n^{3/4} T < L`. Then
`ℙ*(sup_{t ∈ [0,T]} ∑ₓ |𝔷^L_n(t,x) - 𝔷_n(t,x)| > ε) ≤ prop81Rhs n T ε L`. -/
theorem prop81_bound [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {L : ℕ} (hL : 1 ≤ L) (hψL : IsWaveFunction L 𝓕 B ψL μ)
    {n T ε : ℝ} (hn : 1 ≤ n) (hT : 0 < T) (hε : 0 < ε) (hℓ : n ^ (3 / 4 : ℝ) * T < L) :
    μ {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|)} ≤ prop81Rhs n T ε L := by
  have hn0 : 0 < n := by linarith
  set S := n * T / 2 with hSdef
  have hS : 0 < S := by positivity
  set ℓ := (L - n ^ (3 / 4 : ℝ) * T) / n ^ (1 / 2 : ℝ) with hℓdef
  have hcl : 0 < Real.cosh ℓ := Real.cosh_pos ℓ
  set r := min 1 ((L : ℝ) / (n * T)) with hr
  set c := ε / 2 * Real.exp (-(thetaN n * L)) with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨-, hint, hmeas, hlint⟩ := lemma82_bound hB hψ hL hψL hS
  obtain ⟨hsum, -, h52⟩ := lemma_5_2 hB hψ hn
  set F : Ω → ℝ → ℝ := fun ω s =>
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x| with hFdef
  set S1 := {ω | ENNReal.ofReal (c ^ 2) ≤
    ⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal (F ω s ^ 2)} with hS1
  set S2 := {ω | ENNReal.ofReal (ε * Real.cosh ℓ / 2) ≤
    ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (pairZ n ψ ω t Real.cosh)} with hS2
  have hincl : {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|)} ≤ᵐ[μ] S1 ∪ S2 := by
    filter_upwards [hsum, hψL.support] with ω hsω hsupp hω
    by_contra hcon
    simp only [Set.mem_union, not_or, hS1, hS2, Set.mem_ofPred_eq, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine (not_lt.2 ?_) hω
    refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
    have hs : n * t / 2 ∈ Set.Icc 0 S :=
      ⟨by have := ht.1; positivity, by
        have := ht.2; rw [hSdef]; nlinarith⟩
    have hF : F ω (n * t / 2) < c := by
      have h := (le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0 : ℝ) S) =>
        ENNReal.ofReal (F ω s ^ 2)) (n * t / 2) hs).trans_lt h1
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h
      exact lt_of_pow_lt_pow_left₀ 2 hcpos.le h
    have hP : pairZ n ψ ω t Real.cosh < ε * Real.cosh ℓ / 2 := by
      have h := (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal (pairZ n ψ ω t Real.cosh)) t ht).trans_lt h2
      rwa [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h
    have hpw := prop81_pointwise hsupp hn ht.1 ht.2 hℓ (hsω t ht.1)
    have e1 : Real.exp (thetaN n * L) * F ω (n * t / 2) < ε / 2 := by
      calc Real.exp (thetaN n * L) * F ω (n * t / 2) < Real.exp (thetaN n * L) * c :=
            mul_lt_mul_of_pos_left hF (Real.exp_pos _)
        _ = ε / 2 := by
          rw [hc, Real.exp_neg]
          field_simp
    have e2 : pairZ n ψ ω t Real.cosh / Real.cosh ℓ < ε / 2 := by
      rw [div_lt_iff₀ hcl]; linarith
    exact hpw.trans (by linarith)
  -- the Chernoff bound integrated over `[0, S]`
  have hr0 : 0 ≤ r := le_min zero_le_one (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrL : r * (n * T) ≤ L := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hI : ∫ s in (0 : ℝ)..S, rwTail s L ≤ S * (2 * Real.exp (-(r * L / 3))) := by
    calc ∫ s in (0 : ℝ)..S, rwTail s L ≤ ∫ s in (0 : ℝ)..S, 2 * Real.exp (-(r * L / 3)) :=
          intervalIntegral.integral_mono_on hS.le hint intervalIntegrable_const fun s hs => by
            refine (rwTail_le hB hψ hs.1 hr0 L).trans ?_
            gcongr
            have hc1 := cosh_sub_one_le hr0 hr1
            have hc0 : 0 ≤ Real.cosh r - 1 := by linarith [Real.one_le_cosh r]
            have : s * (Real.cosh r - 1) ≤ S * (2 / 3 * r ^ 2) :=
              mul_le_mul hs.2 hc1 hc0 hS.le
            rw [hSdef] at this
            nlinarith
      _ = S * (2 * Real.exp (-(r * L / 3))) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hIpos : 0 ≤ ∫ s in (0 : ℝ)..S, rwTail s L :=
    intervalIntegral.integral_nonneg hS.le fun s hs => rwTail_nonneg hB hψ hs.1 L
  calc μ {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|)}
      ≤ μ (S1 ∪ S2) := measure_mono_ae hincl
    _ ≤ μ S1 + μ S2 := measure_union_le _ _
    _ ≤ _ := by
      refine add_le_add ?_ ?_
      · calc μ S1 ≤ (∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal (F ω s ^ 2)) ∂μ) /
              ENNReal.ofReal (c ^ 2) :=
            meas_ge_le_lintegral_div hmeas (ENNReal.ofReal_pos.2 (by positivity)).ne'
              ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal (4 * (8 + S) * ∫ s in (0 : ℝ)..S, rwTail s L) /
              ENNReal.ofReal (c ^ 2) := by gcongr
          _ = ENNReal.ofReal (4 * (8 + S) * (∫ s in (0 : ℝ)..S, rwTail s L) / c ^ 2) :=
            (ENNReal.ofReal_div_of_pos (by positivity)).symm
          _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hE : Real.exp (2 * thetaN n * L - r * L / 3) =
                Real.exp (thetaN n * L) ^ 2 * Real.exp (-(r * L / 3)) := by
              rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
            calc 4 * (8 + S) * (∫ s in (0 : ℝ)..S, rwTail s L) / c ^ 2
                ≤ 4 * (8 + S) * (S * (2 * Real.exp (-(r * L / 3)))) / c ^ 2 := by gcongr
              _ = 16 / ε ^ 2 * (n * T * (8 + n * T / 2)) *
                  Real.exp (2 * thetaN n * L - r * L / 3) := by
                rw [hE, hc, Real.exp_neg (thetaN n * L), hSdef]
                field_simp
                ring
      · refine (h52 T (ε * Real.cosh ℓ / 2) hT (by positivity)).trans
          (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        show 2 * Real.exp (2 * T) / (ε * Real.cosh ℓ / 2) = 4 * Real.exp (2 * T) /
          (ε * Real.cosh ℓ)
        field_simp
        ring

/-- **The bound tends to `0`** (integer sizes): if `n_k ≥ 1`, `n_k → ∞`, and
`L_k / n_k^{3/4} → ∞`, then eventually `n_k^{3/4} T < L_k`, and
`prop81Rhs n_k T ε L_k → 0`. -/
theorem prop81Rhs_tendsto (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ) (hL : Tendsto (fun k => (L k : ℝ) / n k ^ (3 / 4 : ℝ)) atTop atTop)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    (∀ᶠ k in atTop, n k ^ (3 / 4 : ℝ) * T < L k) ∧
      Tendsto (fun k => prop81Rhs (n k) T ε (L k)) atTop (𝓝 0) := by
  have hn0 : ∀ k, 0 < n k := fun k => by linarith [hn₁ k]
  have h34 : ∀ k, 0 < n k ^ (3 / 4 : ℝ) := fun k => Real.rpow_pos_of_pos (hn0 k) _
  have hev1 : ∀ᶠ k in atTop, 12 ≤ n k ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp hn).eventually_ge_atTop 12
  have hev2 : ∀ᶠ k in atTop, (1 + 12 * T) * n k ^ (3 / 4 : ℝ) ≤ L k := by
    filter_upwards [hL.eventually_ge_atTop (1 + 12 * T)] with k hk
    rwa [le_div_iff₀ (h34 k)] at hk
  have hfirst : ∀ᶠ k in atTop, n k ^ (3 / 4 : ℝ) * T < L k := by
    filter_upwards [hev2] with k hk
    nlinarith [h34 k]
  refine ⟨hfirst, ?_⟩
  set m := min 1 (1 / T) with hmdef
  have hm : 0 < m := lt_min one_pos (by positivity)
  have h1 : Tendsto (fun k => 16 / ε ^ 2 * (n k * T * (8 + n k * T / 2)) *
      Real.exp (2 * thetaN (n k) * L k - min 1 (L k / (n k * T)) * L k / 3)) atTop (𝓝 0) := by
    have hg := ((prop81_poly_exp_tendsto (T := T) hm).comp hn).const_mul (16 / ε ^ 2)
    rw [mul_zero] at hg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · exact Eventually.of_forall fun k => by have := hn0 k; positivity
    · filter_upwards [hev1, hev2] with k hk1 hk2
      have he := prop81_exponent_le (hn₁ k) hT hk1 hk2
      have := hn0 k
      simp only [Function.comp, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) (by positivity)
  have h2 : Tendsto (fun k => 4 * Real.exp (2 * T) /
      (ε * Real.cosh ((L k - n k ^ (3 / 4 : ℝ) * T) / n k ^ (1 / 2 : ℝ)))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hε ?_)
    have hℓ : Tendsto (fun k => (L k : ℝ) / n k ^ (3 / 4 : ℝ) + -T) atTop atTop :=
      tendsto_atTop_add_const_right _ (-T) hL
    refine tendsto_atTop_mono' atTop ?_ hℓ
    filter_upwards [hfirst] with k hk
    have h12 : 0 < n k ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (hn0 k) _
    have hle : (L k : ℝ) / n k ^ (3 / 4 : ℝ) + -T ≤
        (L k - n k ^ (3 / 4 : ℝ) * T) / n k ^ (1 / 2 : ℝ) := by
      rw [show (L k : ℝ) / n k ^ (3 / 4 : ℝ) + -T =
          (L k - n k ^ (3 / 4 : ℝ) * T) / n k ^ (3 / 4 : ℝ) by
          rw [sub_div, mul_div_cancel_left₀ T (h34 k).ne', sub_eq_add_neg]]
      exact div_le_div_of_nonneg_left (by linarith) h12
        (Real.rpow_le_rpow_of_exponent_le (hn₁ k) (by norm_num))
    refine hle.trans ?_
    have hx0 : 0 ≤ (L k - n k ^ (3 / 4 : ℝ) * T) / n k ^ (1 / 2 : ℝ) :=
      div_nonneg (by linarith) h12.le
    rw [Real.cosh_eq]
    nlinarith [Real.quadratic_le_exp_of_nonneg hx0,
      Real.exp_pos (-((L k - n k ^ (3 / 4 : ℝ) * T) / n k ^ (1 / 2 : ℝ)))]
  have := (ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)
  simp only [ENNReal.ofReal_zero, add_zero] at this
  exact this

/-- **The bound tends to `0`** (sizes in `ℕ ∪ {∞}`, hypothesis of `main_theorem`): eventually
`L_k = ∞` or `n_k^{3/4} T < L_k`, and the bound (`0` when `L_k = ∞`) tends to `0`. -/
theorem prop81Rhs_tendsto_enat (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ∞)
    (hL : Tendsto (fun k => (L k : ℝ≥0∞) / ENNReal.ofReal (n k ^ (3 / 4 : ℝ))) atTop (𝓝 ⊤))
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    (∀ᶠ k in atTop, L k = ⊤ ∨ n k ^ (3 / 4 : ℝ) * T < (L k).toNat) ∧
      Tendsto (fun k => if L k = ⊤ then 0 else prop81Rhs (n k) T ε (L k).toNat) atTop
        (𝓝 0) := by
  have h34 : ∀ k, 0 < n k ^ (3 / 4 : ℝ) := fun k =>
    Real.rpow_pos_of_pos (by linarith [hn₁ k]) _
  -- integer sizes `L'_k`, equal to `L_k` when it is finite
  set L' : ℕ → ℕ := fun k => if L k = ⊤ then ⌈n k ^ (3 / 4 : ℝ) * n k⌉₊ else (L k).toNat
    with hL'def
  have hL' : Tendsto (fun k => (L' k : ℝ) / n k ^ (3 / 4 : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hL.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := b))),
      hn.eventually_ge_atTop b] with k hk hkn
    rw [le_div_iff₀ (h34 k)]
    by_cases hk' : L k = ⊤
    · simp only [hL'def, hk', ite_true]
      calc b * n k ^ (3 / 4 : ℝ) ≤ n k ^ (3 / 4 : ℝ) * n k := by nlinarith [h34 k]
        _ ≤ _ := Nat.le_ceil _
    · simp only [hL'def, hk', ite_false]
      have e : (L k : ℝ≥0∞) = ENNReal.ofReal ((L k).toNat : ℝ) := by
        rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, ENat.natCast_toNat hk']
      rw [e, ← ENNReal.ofReal_div_of_pos (h34 k), ENNReal.ofReal_lt_ofReal_iff'] at hk
      rw [← le_div_iff₀ (h34 k)]
      exact hk.1.le
  obtain ⟨hev, hlim⟩ := prop81Rhs_tendsto n hn₁ hn L' hL' hT hε
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with k hk
    by_cases hk' : L k = ⊤
    · exact Or.inl hk'
    · right
      simpa only [hL'def, hk', ite_false] using hk
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => zero_le) fun k => ?_
    by_cases hk' : L k = ⊤
    · simp only [hk', ite_true]
      exact zero_le
    · simp only [hk', ite_false, hL'def]
      exact le_rfl

/-- Twin of `prop_8_1` (**Proposition 8.1**; same statement). -/
theorem prop81_tendsto (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ) (hL₁ : ∀ k, 1 ≤ L k)
    (hL : Tendsto (fun k => (L k : ℝ) / n k ^ (3 / 4 : ℝ)) atTop atTop)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (ψL : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ))
    (hψL : ∀ k, IsWaveFunction (L k) (𝓕 k) (B k) (ψL k) (μ k))
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k => μ k {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
        etvDist (tiltedMeasureBox (L k) (n k) (ψL k) ω t) (tiltedMeasure (n k) (ψ k) ω t)})
      atTop (𝓝 0) := by
  obtain ⟨hev, hlim⟩ := prop81Rhs_tendsto n hn₁ hn L hL hT hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun k => zero_le) ?_
  filter_upwards [hev] with k hk
  refine le_trans (measure_mono_ae ?_)
    (prop81_bound (hB k) (hψ k) (hL₁ k) (hψL k) (hn₁ k) hT hε hk)
  have hn0 : 0 ≤ n k := by linarith [hn₁ k]
  obtain ⟨hsum, -, -⟩ := lemma_5_2 (hB k) (hψ k) (hn₁ k)
  filter_upwards [hsum, (hψL k).support] with ω hsω hsupp hω
  refine lt_of_lt_of_le hω (iSup₂_mono fun t ht => ?_)
  -- `‖𝖹^L_n(t) - 𝖹_n(t)‖_TV ≤ ∑ₓ |𝔷^L_n(t,x) - 𝔷_n(t,x)|`
  have hind : (box (L k : ℕ∞)).indicator (zN (n k) (ψL k) ω t) = zN (n k) (ψL k) ω t := by
    funext x
    by_cases hx : x ∈ box (L k : ℕ∞)
    · simp [hx]
    · simp [hx, prop81_zN_eq_zero hsupp hn0 ht.1 hx]
  rw [tiltedMeasureBox_eq_sum, tiltedMeasure, hind]
  refine etvDist_sum_dirac_le _ _ _ ?_ ?_
  · refine summable_of_ne_finset_zero (s := Finset.Icc (-(L k : ℤ)) (L k)) fun x hx => ?_
    exact prop81_zN_eq_zero hsupp hn0 ht.1 fun h => hx (pairing_mem_box_iff.1 h)
  · simpa using hsω t ht.1 0 ⟨by norm_num, by norm_num⟩

end QSSEPtoKPZ
