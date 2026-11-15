/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.TiltedField.MartingalesBounds
public import QSSEPtoKPZ.TiltedField.MartingalesCalc
public import QSSEPtoKPZ.WaveFunction.Linear
public import QSSEPtoKPZ.WaveFunction.MomentBound
public import QSSEPtoKPZ.WaveFunction.Good
public import QSSEPtoKPZ.Martingales.NullAug

/-!
# Section 3.2: the martingales `M_n^φ` and `𝒲_n`

Statements: Stage 2, task T0; proofs: task E2. Proposition 3.1 is deduced, as in the article,
from Lemma 2.3 (1) on `[0, nT/2]` with the weight `α_s(x) = e^{θ_n x - λ_n s} φ_{2s/n}(y_n(2s/n,x))`
(`tiltAlpha`, `TiltedField/MartingalesCalc.lean`), after the change of time `s = nt/2`
(`HasBracket.timeChange`). The integrability of `ℰ_n` and the measurability in (3.7) come from
the pathwise bounds of `TiltedField/MartingalesBounds.lean` (moment bound (2.2)).

In all statements, the conjunct "almost surely, for all `t ≥ 0`, `∑ₓ 𝔷_n(t,x)` converges" makes
every series of the statement an honest one: `𝔷_n ≥ 0`, and all the other series have terms
bounded by a constant times `𝔷_n(t,x)` (bounded test functions; `𝔷_n(t,x+1) ≤ 𝒲_n(t)`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-! ### Auxiliary results -/

/-- Change of variables `s = c u` in `∫_0^{ct}`. -/
private lemma integral_zero_mul_left {c : ℝ} (hc : c ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..c * t, f s = c * ∫ u in (0 : ℝ)..t, f (c * u) := by
  rw [intervalIntegral.integral_comp_mul_left f hc, smul_eq_mul, mul_zero, ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul]

/-- `⟨M + c⟩ = ⟨M⟩`. -/
private lemma hasBracket_add_const' {T : ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {M A : ℝ → Ω → ℝ}
    (h : HasBracket T 𝓖 M A μ) (c : ℝ) : HasBracket T 𝓖 (fun t ω => M t ω + c) A μ := by
  have hcond : ∀ s : ℝ≥0, μ[fun _ => c | 𝓖 s] = fun _ => c := fun s => condExp_const (𝓖.le s) c
  refine { cont := ?_, memLp := fun t ht => (h.memLp t ht).add (memLp_const c),
           condExp := fun s t hst ht => ?_, integrable_bracket := h.integrable_bracket,
           zero := h.zero, mono := h.mono, cont_bracket := h.cont_bracket,
           condExp_sq := fun s t hst ht => ?_ }
  · filter_upwards [h.cont] with ω hω using hω.add continuousOn_const
  · have hi := (h.memLp t ht).integrable one_le_two
    have e := condExp_add hi (integrable_const c) (𝓖 s)
    rw [hcond s] at e
    filter_upwards [e, h.condExp s t hst ht] with ω h1 h2
    simp only [Pi.add_apply] at h1
    rw [show (fun ω => M t ω + c) = M t + fun _ => c from rfl, h1, h2]
  · have hM := h.memLp t ht
    have hi := hM.integrable one_le_two
    have hq : Integrable (fun ω => M t ω ^ 2 - A t ω) μ :=
      hM.integrable_sq.sub (h.integrable_bracket t ht)
    have e : (fun ω => (M t ω + c) ^ 2 - A t ω) =
        (fun ω => M t ω ^ 2 - A t ω) + ((2 * c) • M t + fun _ => c ^ 2) := by
      ext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    have e1 := condExp_add hq ((hi.smul (2 * c)).add (integrable_const (c ^ 2))) (𝓖 s)
    have e2 := condExp_add (hi.smul (2 * c)) (integrable_const (c ^ 2)) (𝓖 s)
    have e3 := condExp_smul (μ := μ) (2 * c) (M t) (𝓖 s)
    rw [condExp_const (𝓖.le s)] at e2
    filter_upwards [e1, e2, e3, h.condExp_sq s t hst ht, h.condExp s t hst ht]
      with ω h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul]
    ring

/-- The bounds on `u = φ_r(y_n(r,x+1))` and `v = φ_r(y_n(r,x))` used in items (2), (3):
`|u|, |v| ≤ c₀` and `|u - v| ≤ n^{-1/2} c₂` (mean value inequality). -/
private lemma phi_uv_bounds {n T C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {c : Fin 5 → ℝ} (hc : ∀ t ∈ Set.Icc 0 T, ∀ x,
      |φ t x| ≤ c 0 ∧ |φt t x| ≤ c 1 ∧ |iteratedDeriv 1 (φ t) x| ≤ c 2 ∧
      |iteratedDeriv 2 (φ t) x| ≤ c 3 ∧ |iteratedDeriv 3 (φ t) x| ≤ c 4)
    {r : ℝ} (hr : r ∈ Set.Icc 0 T) (x : ℤ) :
    |φ r (rescaledPosition n r (x + 1))| ≤ c 0 ∧ |φ r (rescaledPosition n r x)| ≤ c 0 ∧
      |φ r (rescaledPosition n r (x + 1)) - φ r (rescaledPosition n r x)| ≤
        n ^ (-1 / 2 : ℝ) * c 2 := by
  refine ⟨(hc r hr _).1, (hc r hr _).1, ?_⟩
  rw [(tiltPos_add_one hn r x).1]
  set y := rescaledPosition n r x
  have hd := (hφ.contDiff r hr).differentiable (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := φ r) (s := Set.univ) (x := y)
    (y := y + n ^ (-1 / 2 : ℝ)) (C := c 2) (fun z _ => hd z)
    (fun z _ => by rw [← iteratedDeriv_one]; exact (hc r hr z).2.2.1) convex_univ trivial trivial
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left,
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hn) _)] at this
  linarith

/-- `a_n n^{1/2} = n λ_n`. -/
private lemma aN_mul_rpow {n : ℝ} (hn : 1 ≤ n) (X : ℝ) :
    aN n * (n ^ (1 / 2 : ℝ) * X) = n * lambdaN n * X := by
  have : n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  unfold aN; linear_combination (lambdaN n * X) * this

/-- `ℰ_n(r;φ)` with the two values of `φ` grouped:
`n^{1/2} ∑ₓ 𝔷_n(r,x) 𝔷_n(r,x+1) [φ(y_n(r,x)) φ(y_n(r,x+1))]`. -/
private lemma EN_eq_tsum (n : ℝ) (ω : Ω) (r : ℝ) (φ : ℝ → ℝ) :
    EN n ψ ω r φ = n ^ (1 / 2 : ℝ) * ∑' x, zN n ψ ω r x * zN n ψ ω r (x + 1) *
      (φ (rescaledPosition n r x) * φ (rescaledPosition n r (x + 1))) := by
  simp only [EN, mul_assoc]

/-- **Item (2), pointwise in time**: `n QNdens(r) ≤ 2 C² a_n ℰ_n(r)` for `r ∈ [0,T]`. -/
private lemma item2_at {n T C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {ω : Ω} (hg : TiltGood n T ψ ω) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    n * QNdens n ψ φ r ω ≤ 2 * C ^ 2 * (aN n * EN n ψ ω r fun _ => 1) := by
  obtain ⟨c, hcs, hc⟩ := hφ.bound
  have hc0 : 0 ≤ c 0 := (abs_nonneg _).trans (hc r hr 0).1
  have hc1 : 0 ≤ c 1 := (abs_nonneg _).trans (hc r hr 0).2.1
  have hc2 : 0 ≤ c 2 := (abs_nonneg _).trans (hc r hr 0).2.2.1
  have hc3 : 0 ≤ c 3 := (abs_nonneg _).trans (hc r hr 0).2.2.2.1
  have hc4 : 0 ≤ c 4 := (abs_nonneg _).trans (hc r hr 0).2.2.2.2
  have hC : c 0 + c 2 ≤ C := by
    simp only [Fin.sum_univ_five] at hcs; linarith
  have hl := tiltLambda_nonneg n
  have hQ : ∀ x, (Real.exp (thetaN n / 2) * φ r (rescaledPosition n r (x + 1)) -
      Real.exp (-thetaN n / 2) * φ r (rescaledPosition n r x)) ^ 2 ≤ 2 * C ^ 2 * lambdaN n :=
    fun x => by
      obtain ⟨hu, -, huv⟩ := phi_uv_bounds hn hφ hc hr x
      exact tilt_item2_pointwise hn hu huv hc0 hc2 hC
  have hs1 := hg.summable_zz hr (G := fun x => (Real.exp (thetaN n / 2) *
      φ r (rescaledPosition n r (x + 1)) - Real.exp (-thetaN n / 2) *
        φ r (rescaledPosition n r x)) ^ 2) (b := 2 * C ^ 2 * lambdaN n)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; exact hQ x)
  have hs2 := hg.summable_zz hr (G := fun _ => 2 * C ^ 2 * lambdaN n)
    (b := |2 * C ^ 2 * lambdaN n|) (fun x => le_rfl)
  have hle : QNdens n ψ φ r ω ≤
      ∑' x, zN n ψ ω r x * zN n ψ ω r (x + 1) * (2 * C ^ 2 * lambdaN n) :=
    hs1.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (hQ x)
      (mul_nonneg (tiltZ_nonneg n ω r x) (tiltZ_nonneg n ω r (x + 1)))) hs2
  rw [tsum_mul_right] at hle
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  calc n * QNdens n ψ φ r ω
      ≤ n * ((∑' x, zN n ψ ω r x * zN n ψ ω r (x + 1)) * (2 * C ^ 2 * lambdaN n)) := by gcongr
    _ = 2 * C ^ 2 * (aN n * EN n ψ ω r fun _ => 1) := by
        simp only [EN, mul_one]
        rw [aN_mul_rpow hn]; ring

/-- **Item (3), pointwise in time**:
`|n QNdens(r) - a_n ℰ_n(r;φ_r)| ≤ 5 n^{-1/4} C² ℰ_n(r)` for `r ∈ [0,T]`. -/
private lemma item3_at {n T C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {ω : Ω} (hg : TiltGood n T ψ ω) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    |n * QNdens n ψ φ r ω - aN n * EN n ψ ω r (φ r)| ≤
      5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * EN n ψ ω r fun _ => 1 := by
  obtain ⟨c, hcs, hc⟩ := hφ.bound
  have hc0 : 0 ≤ c 0 := (abs_nonneg _).trans (hc r hr 0).1
  have hc1 : 0 ≤ c 1 := (abs_nonneg _).trans (hc r hr 0).2.1
  have hc2 : 0 ≤ c 2 := (abs_nonneg _).trans (hc r hr 0).2.2.1
  have hc3 : 0 ≤ c 3 := (abs_nonneg _).trans (hc r hr 0).2.2.2.1
  have hc4 : 0 ≤ c 4 := (abs_nonneg _).trans (hc r hr 0).2.2.2.2
  have hC0 : c 0 ≤ C := by simp only [Fin.sum_univ_five] at hcs; linarith
  have hC2 : c 2 ≤ C := by simp only [Fin.sum_univ_five] at hcs; linarith
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  set u : ℤ → ℝ := fun x => φ r (rescaledPosition n r (x + 1)) with hu
  set v : ℤ → ℝ := fun x => φ r (rescaledPosition n r x) with hv
  set D : ℤ → ℝ := fun x => (Real.exp (thetaN n / 2) * u x - Real.exp (-thetaN n / 2) * v x) ^ 2 -
    lambdaN n * (u x * v x) with hD
  set k := 5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * n ^ (1 / 2 : ℝ) with hk
  have hDb : ∀ x, n * |D x| ≤ k := fun x => by
    obtain ⟨hu', -, huv⟩ := phi_uv_bounds hn hφ hc hr x
    exact tilt_item3_pointwise hn hu' huv hc2 hC0 hC2
  have hDb' : ∀ x, |n * D x| ≤ k := fun x => by
    rw [abs_mul, abs_of_nonneg hn0]; exact hDb x
  have hubd : ∀ x, |u x| ≤ c 0 := fun x => (phi_uv_bounds hn hφ hc hr x).1
  have hvbd : ∀ x, |v x| ≤ c 0 := fun x => (phi_uv_bounds hn hφ hc hr x).2.1
  have hQb : ∀ x, |(Real.exp (thetaN n / 2) * u x - Real.exp (-thetaN n / 2) * v x) ^ 2| ≤
      (Real.exp (thetaN n / 2) * c 0 + Real.exp (-thetaN n / 2) * c 0) ^ 2 := fun x => by
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    gcongr
    exacts [hubd x, hvbd x]
  have hs1 := hg.summable_zz hr (G := fun x =>
    (Real.exp (thetaN n / 2) * u x - Real.exp (-thetaN n / 2) * v x) ^ 2) hQb
  have huv : ∀ x, |v x * u x| ≤ c 0 * c 0 := fun x => by
    rw [abs_mul]; exact mul_le_mul (hvbd x) (hubd x) (abs_nonneg _) hc0
  have hs2 := hg.summable_zz hr (G := fun x => v x * u x) huv
  have hs3 := hg.summable_zz hr (G := fun x => n * D x) hDb'
  have hs4 := hg.summable_zz hr (G := fun _ => k) (b := |k|) (fun x => le_rfl)
  -- `n QNdens - a_n ℰ_n(φ) = ∑ₓ 𝔷𝔷 n D`
  have hsplit : n * QNdens n ψ φ r ω - aN n * EN n ψ ω r (φ r) =
      ∑' x, zN n ψ ω r x * zN n ψ ω r (x + 1) * (n * D x) := by
    rw [EN_eq_tsum, QNdens, aN_mul_rpow hn]
    have e : ∀ x, zN n ψ ω r x * zN n ψ ω r (x + 1) * (n * D x) =
        n * (zN n ψ ω r x * zN n ψ ω r (x + 1) *
          (Real.exp (thetaN n / 2) * u x - Real.exp (-thetaN n / 2) * v x) ^ 2) -
        n * lambdaN n * (zN n ψ ω r x * zN n ψ ω r (x + 1) * (v x * u x)) := fun x => by
      rw [hD]; ring
    rw [tsum_congr e, (hs1.mul_left n).tsum_sub (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
  rw [hsplit]
  have hle : |∑' x, zN n ψ ω r x * zN n ψ ω r (x + 1) * (n * D x)| ≤
      ∑' x, zN n ψ ω r x * zN n ψ ω r (x + 1) * k := by
    have hz : ∀ x, 0 ≤ zN n ψ ω r x * zN n ψ ω r (x + 1) := fun x =>
      mul_nonneg (tiltZ_nonneg n ω r x) (tiltZ_nonneg n ω r (x + 1))
    rw [abs_le]
    constructor
    · rw [← tsum_neg]
      exact (hs4.neg).tsum_le_tsum (fun x => by
        have := (abs_le.1 (hDb' x)).1
        nlinarith [hz x]) hs3
    · exact hs3.tsum_le_tsum (fun x => by
        have := (abs_le.1 (hDb' x)).2
        nlinarith [hz x]) hs4
  refine hle.trans (le_of_eq ?_)
  rw [tsum_mul_right, hk]
  simp only [EN, mul_one]
  ring

/-- **Equation (3.7)**: for `n ≥ 1`, `T` and `k`, almost surely the series `𝒲_n(t) = ∑ₓ 𝔷_n(t,x)`
converges for all `t ≥ 0`, the supremum `sup_{t ∈ [0,T]} 𝒲_n(t)` is almost everywhere
measurable, and `𝔼[sup_{t ∈ [0,T]} 𝒲_n(t)^k] < ∞` (computed in `[0, ∞]`). -/
theorem WN_moments (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n T : ℝ} (hn : 1 ≤ n) (k : ℕ) :
    (∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (WN n ψ t ω)) μ ∧
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (WN n ψ t ω)) ^ k ∂μ < ⊤ := by
  refine ⟨tilt_ae_summable hB hψ hn, ?_, ?_⟩
  · -- the supremum over `[0,T]` is almost surely a supremum over the grid points `k/(m+1)`
    have hFm : Measurable fun ω => ⨆ p : ℕ × ℕ, ⨆ (_ : (ratGridPt p : ℝ) ≤ T),
        ∑' x, ENNReal.ofReal (zN n ψ ω (ratGridPt p) x) :=
      Measurable.iSup fun p => Measurable.iSup_Prop _ (Measurable.tsum fun x =>
        ENNReal.measurable_ofReal.comp (tiltZ_measurable hψ hn (ratGridPt p).2 x))
    refine hFm.aemeasurable.congr ?_
    filter_upwards [ae_tiltGood hB hψ hn] with ω hg
    have hW : ∀ r ∈ Set.Icc 0 T, ENNReal.ofReal (WN n ψ r ω) =
        ∑' x, ENNReal.ofReal (zN n ψ ω r x) := fun r hr => by
      simp only [WN, pairZ, mul_one]
      exact ENNReal.ofReal_tsum_of_nonneg (fun x => tiltZ_nonneg n ω r x) ((hg T).summable hr)
    refine le_antisymm (iSup_le fun p => iSup_le fun hp => ?_) (iSup₂_le fun t ht => ?_)
    · have hp' : (ratGridPt p : ℝ) ∈ Set.Icc 0 T := ⟨(ratGridPt p).2, hp⟩
      rw [← hW _ hp']
      exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ENNReal.ofReal (WN n ψ t ω)) _ hp'
    · set τ : ℝ≥0 := ⟨t, ht.1⟩
      have hle : ∀ m : ℕ, (gridBelow τ m : ℝ) ≤ T := fun m =>
        (NNReal.coe_le_coe.2 (gridBelow_le τ m)).trans ht.2
      have hlim : Tendsto (fun m => (gridBelow τ m : ℝ)) atTop (𝓝[Set.Icc 0 T] t) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_gridBelow τ,
          Eventually.of_forall fun m => ⟨(gridBelow τ m).2, hle m⟩⟩
      have hc := (ENNReal.continuous_ofReal.comp_continuousOn (hg T).continuousOn_WN) t ht
      refine le_of_tendsto' (hc.tendsto.comp hlim) fun m => ?_
      simp only [Function.comp_apply]
      rw [hW (gridBelow τ m : ℝ) ⟨(gridBelow τ m).2, hle m⟩]
      exact le_iSup₂_of_le (f := fun p (_ : (ratGridPt p : ℝ) ≤ T) =>
        ∑' x, ENNReal.ofReal (zN n ψ ω (ratGridPt p) x)) (⌊((m : ℝ) + 1) * τ⌋₊, m) (hle m) le_rfl
  · -- comparison with (2.2): `𝒲_n(t) ≤ ∑ₓ e^{θ_n |x|} P(nt/2, x)`
    have hn0 : 0 < n := zero_lt_one.trans_le hn
    obtain ⟨-, hmb⟩ := moment_bound hB hψ (tiltTheta_nonneg hn) (T := n / 2 * T) k
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hmb
    refine pow_le_pow_left₀ zero_le (iSup₂_le fun t ht => ?_) k
    have hs : n * t / 2 ∈ Set.Icc 0 (n / 2 * T) :=
      ⟨by have := ht.1; positivity, by have := ht.2; nlinarith⟩
    refine le_trans ?_ (le_iSup₂_of_le (f := fun s (_ : s ∈ Set.Icc 0 (n / 2 * T)) =>
      ∑' x : ℤ, ENNReal.ofReal (Real.exp (thetaN n * |(x : ℝ)|) * density ψ ω s x))
      (n * t / 2) hs le_rfl)
    by_cases hsum : Summable (zN n ψ ω t)
    · simp only [WN, pairZ, mul_one]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun x => tiltZ_nonneg n ω t x) hsum]
      exact ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal (tiltZ_le_exp hn ω ht.1 x)
    · simp only [WN, pairZ, mul_one, tsum_eq_zero_of_not_summable hsum, ENNReal.ofReal_zero]
      exact zero_le

/-- **Proposition 3.1**, equations (3.14), (3.15), and items (2), (3). Let `n ≥ 1`, `T > 0` and
`φ ∈ C_b^{1,3}([0,T] × ℝ)` with `‖φ‖_{1,3} ≤ C` (time derivative `φt`). Then:
* almost surely, `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`, and the functions
  `s ↦ 𝒵_n(s; ∂ₛφ_s + 𝒜_nφ_s)`, the integrand `QNdens` of (3.15), `s ↦ ℰ_n(s;φ_s)` and
  `s ↦ ℰ_n(s)` are integrable on `[0,T]`;
* (3.14)-(3.15): `M_n^φ` is a continuous square-integrable `(𝓕ⁿ_t)`-martingale on `[0,T]`, with
  `⟨M_n^φ⟩_t = n ∫_0^t ∑ₓ 𝔷_n(s,x) 𝔷_n(s,x+1) [e^{θ_n/2} φ_s(y_n(s,x+1)) - e^{-θ_n/2} φ_s(y_n(s,x))]² ds`;
* (2): almost surely, for `0 ≤ s ≤ t ≤ T`,
  `⟨M_n^φ⟩_t - ⟨M_n^φ⟩_s ≤ 2 C² (⟨𝒲_n⟩_t - ⟨𝒲_n⟩_s)`, where `⟨𝒲_n⟩_t = a_n ∫_0^t ℰ_n(r) dr` (3.16);
* (3): almost surely, for `t ∈ [0,T]`,
  `|⟨M_n^φ⟩_t - a_n ∫_0^t ℰ_n(s;φ_s) ds| ≤ 5 n^{-1/4} C² ∫_0^t ℰ_n(s) ds`.
Item (1) is `prop_3_1_generator`, and (3.16) is `hasBracket_WN`. -/
theorem prop_3_1 (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n T C : ℝ} (hn : 1 ≤ n) (hT : 0 < T) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    (∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => pairZ n ψ ω s (fun y => φt s y + AN n (φ s) y)) volume 0 T ∧
      IntervalIntegrable (fun s => QNdens n ψ φ s ω) volume 0 T ∧
      IntervalIntegrable (fun s => EN n ψ ω s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => EN n ψ ω s fun _ => 1) volume 0 T) ∧
    HasBracket T (filtN n 𝓕) (MN n ψ φ φt) (QN n ψ φ) μ ∧
    (∀ᵐ ω ∂μ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      QN n ψ φ t ω - QN n ψ φ s ω ≤
        2 * C ^ 2 * (aN n * ∫ r in s..t, EN n ψ ω r fun _ => 1)) ∧
    (∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      |QN n ψ φ t ω - aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s (φ s)| ≤
        5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hc2 : n / 2 ≠ 0 := by positivity
  -- Lemma 2.3 (1) on `[0, nT/2]` for `α_s(x) = e^{θ_n x - λ_n s} φ_{2s/n}(y_n(2s/n, x))`
  obtain ⟨C', hC'⟩ := tiltAlpha_bound hn hφ
  obtain ⟨hLae, hLbr⟩ := lemma_2_3_linear hB hψ (T := n / 2 * T) (by positivity)
    (tiltTheta_nonneg hn) (α := tiltAlpha n φ) (α' := tiltAlphaDeriv n φ φt)
    (tiltAlpha_hasDerivWithinAt hn hφ) (tiltAlphaDeriv_continuousOn hn hφ) hC'
  -- the identities of the proof, after the change of time `s = nt/2`
  have hpair : ∀ ω t, ∑' x, tiltAlpha n φ (n / 2 * t) x * density ψ ω (n / 2 * t) x =
      pairZ n ψ ω t (φ t) := fun ω t => by
    simp only [tiltAlpha_pair hn]; rfl
  have hdrift : ∀ ω u, ∑' x, (tiltAlphaDeriv n φ φt (n / 2 * u) x +
      lap (tiltAlpha n φ (n / 2 * u)) x) * density ψ ω (n / 2 * u) x =
      2 / n * pairZ n ψ ω u (fun y => φt u y + AN n (φ u) y) := fun ω u => by
    simp only [tiltAlpha_drift hn]; rw [tsum_mul_left]; rfl
  have hbr : ∀ ω u, ∑' x, 2 * (tiltAlpha n φ (n / 2 * u) (x + 1) -
      tiltAlpha n φ (n / 2 * u) x) ^ 2 * density ψ ω (n / 2 * u) x *
        density ψ ω (n / 2 * u) (x + 1) = 2 * QNdens n ψ φ u ω := fun ω u => by
    simp only [tiltAlpha_bracket hn]; rw [tsum_mul_left]; rfl
  have hM : ∀ ω t, (∑' x, tiltAlpha n φ (n / 2 * t) x * density ψ ω (n / 2 * t) x -
      tiltAlpha n φ 0 0 - ∫ s in (0 : ℝ)..n / 2 * t, ∑' x, (tiltAlphaDeriv n φ φt s x +
        lap (tiltAlpha n φ s) x) * density ψ ω s x) = MN n ψ φ φt t ω := by
    intro ω t
    rw [hpair, tiltAlpha_zero, integral_zero_mul_left hc2, MN]
    simp only [hdrift]
    rw [intervalIntegral.integral_const_mul, ← mul_assoc, show n / 2 * (2 / n) = 1 by field_simp,
      one_mul]
  have hA : ∀ ω t, ∫ s in (0 : ℝ)..n / 2 * t, ∑' x, 2 * (tiltAlpha n φ s (x + 1) -
      tiltAlpha n φ s x) ^ 2 * density ψ ω s x * density ψ ω s (x + 1) = QN n ψ φ t ω := by
    intro ω t
    rw [integral_zero_mul_left hc2]
    simp only [hbr]
    rw [intervalIntegral.integral_const_mul, QN, ← mul_assoc]
    congr 1; ring
  -- (3.14)-(3.15): the change of time
  have hcR : (((n / 2).toNNReal : ℝ)) = n / 2 := Real.coe_toNNReal _ (by positivity)
  have hL' := hLbr
  rw [← hcR] at hL'
  have hbrack : HasBracket T (filtN n 𝓕) (MN n ψ φ φt) (QN n ψ φ) μ := by
    refine hL'.timeChange.congr hT.le (ae_of_all _ fun ω t _ => ?_)
      (ae_of_all _ fun ω t _ => ?_)
    · simp only [hcR]; exact hM ω t
    · simp only [hcR]; exact hA ω t
  -- summability and integrability
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → Set.uIcc a b ⊆ Set.uIcc 0 T := fun a b ha hab hb => by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT.le]; exact Set.Icc_subset_Icc ha hb
  obtain ⟨c, -, hc⟩ := hφ.bound
  have hc0 : 0 ≤ c 0 := (abs_nonneg _).trans (hc 0 ⟨le_rfl, hT.le⟩ 0).1
  have hφcont : ∀ x : ℤ, ContinuousOn (fun s => φ s (rescaledPosition n s x)) (Set.Icc 0 T) :=
    fun x => hφ.tilt_continuousOn_val.comp (by unfold rescaledPosition; fun_prop :
      Continuous fun s => (s, rescaledPosition n s x)).continuousOn
      (fun s hs => ⟨hs, Set.mem_univ _⟩)
  have hint : ∀ᵐ ω ∂μ, (∀ T', TiltGood n T' ψ ω) ∧ ((∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => pairZ n ψ ω s (fun y => φt s y + AN n (φ s) y)) volume 0 T ∧
      IntervalIntegrable (fun s => QNdens n ψ φ s ω) volume 0 T ∧
      IntervalIntegrable (fun s => EN n ψ ω s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => EN n ψ ω s fun _ => 1) volume 0 T) := by
    filter_upwards [ae_tiltGood hB hψ hn, hLae] with ω hg hL
    obtain ⟨-, hdI, hbI⟩ := hL
    have hd' := hdI.comp_mul_left (c := n / 2)
    have hb' := hbI.comp_mul_left (c := n / 2)
    rw [zero_div, mul_div_cancel_left₀ _ hc2] at hd' hb'
    refine ⟨hg, fun t ht => (hg t).summable ⟨ht, le_rfl⟩, ?_, ?_, ?_, ?_⟩
    · have e : (fun s => pairZ n ψ ω s (fun y => φt s y + AN n (φ s) y)) = fun s => n / 2 *
          ((fun s => ∑' x, (tiltAlphaDeriv n φ φt s x + lap (tiltAlpha n φ s) x) *
            density ψ ω s x) (n / 2 * s)) := by
        ext s; simp only [hdrift]; field_simp
      rw [e]; exact hd'.const_mul _
    · have e : (fun s => QNdens n ψ φ s ω) = fun s => 1 / 2 *
          ((fun s => ∑' x, 2 * (tiltAlpha n φ s (x + 1) - tiltAlpha n φ s x) ^ 2 *
            density ψ ω s x * density ψ ω s (x + 1)) (n / 2 * s)) := by
        ext s; simp only [hbr]; ring
      rw [e]; exact hb'.const_mul _
    · have hG : ContinuousOn (fun s => EN n ψ ω s (φ s)) (Set.Icc 0 T) := by
        simp only [EN_eq_tsum]
        refine continuousOn_const.mul ((hg T).continuousOn_zz (b := c 0 * c 0)
          (G := fun s x => φ s (rescaledPosition n s x) * φ s (rescaledPosition n s (x + 1)))
          (fun x => (hφcont x).mul (hφcont (x + 1))) (fun s hs x => ?_))
        rw [abs_mul]; exact mul_le_mul (hc s hs _).1 (hc s hs _).1 (abs_nonneg _) hc0
      rw [← Set.uIcc_of_le hT.le] at hG
      exact hG.intervalIntegrable
    · have hG := (hg T).continuousOn_zz (G := fun _ _ => (1 : ℝ) * 1) (b := 1)
        (fun _ => continuousOn_const) (fun _ _ _ => by norm_num)
      have hG' : ContinuousOn (fun s => EN n ψ ω s fun _ => 1) (Set.Icc 0 T) := by
        simp only [EN_eq_tsum]; exact continuousOn_const.mul hG
      rw [← Set.uIcc_of_le hT.le] at hG'
      exact hG'.intervalIntegrable
  refine ⟨?_, hbrack, ?_, ?_⟩
  · filter_upwards [hint] with ω h using h.2
  · -- item (2)
    filter_upwards [hint] with ω hω s t hs hst htT
    obtain ⟨hg, -, -, hQ, -, hE1⟩ := hω
    have hQs := hQ.mono_set (hsub 0 s le_rfl hs (hst.trans htT))
    have hQt := hQ.mono_set (hsub 0 t le_rfl (hs.trans hst) htT)
    have hQst := hQ.mono_set (hsub s t hs hst htT)
    have hEst := hE1.mono_set (hsub s t hs hst htT)
    calc QN n ψ φ t ω - QN n ψ φ s ω = n * ∫ r in s..t, QNdens n ψ φ r ω := by
          rw [QN, QN, ← mul_sub, intervalIntegral.integral_interval_sub_left hQt hQs]
      _ = ∫ r in s..t, n * QNdens n ψ φ r ω := (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ r in s..t, 2 * C ^ 2 * (aN n * EN n ψ ω r fun _ => 1) :=
          intervalIntegral.integral_mono_on hst (hQst.const_mul _)
            ((hEst.const_mul _).const_mul _) fun r hr =>
              item2_at hn hφ (hg T) ⟨hs.trans hr.1, hr.2.trans htT⟩
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · -- item (3)
    filter_upwards [hint] with ω hω t ht
    obtain ⟨hg, -, -, hQ, hEφ, hE1⟩ := hω
    have hQt := hQ.mono_set (hsub 0 t le_rfl ht.1 ht.2)
    have hEφt := hEφ.mono_set (hsub 0 t le_rfl ht.1 ht.2)
    have hE1t := hE1.mono_set (hsub 0 t le_rfl ht.1 ht.2)
    have e : QN n ψ φ t ω - aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s (φ s) =
        ∫ s in (0 : ℝ)..t, (n * QNdens n ψ φ s ω - aN n * EN n ψ ω s (φ s)) := by
      rw [intervalIntegral.integral_sub (hQt.const_mul _) (hEφt.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, QN]
    rw [e]
    calc _ ≤ ∫ s in (0 : ℝ)..t, |n * QNdens n ψ φ s ω - aN n * EN n ψ ω s (φ s)| :=
          intervalIntegral.abs_integral_le_integral_abs ht.1
      _ ≤ ∫ s in (0 : ℝ)..t, 5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * EN n ψ ω s fun _ => 1 :=
          intervalIntegral.integral_mono_on ht.1 ((hQt.const_mul _).sub (hEφt.const_mul _)).abs
            (hE1t.const_mul _) fun r hr => item3_at hn hφ (hg T) ⟨hr.1, hr.2.trans ht.2⟩
      _ = _ := intervalIntegral.integral_const_mul _ _

/-- **Equation (3.16)** (end of Proposition 3.1), with `𝒲_n(0) = 1` (recalled at the beginning of
Section 4.2): for `n ≥ 1` and `T > 0`, almost surely `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`
and `s ↦ ℰ_n(s)` is integrable on `[0,T]`; `𝒲_n` is a continuous square-integrable
`(𝓕ⁿ_t)`-martingale on `[0,T]` with `⟨𝒲_n⟩_t = a_n ∫_0^t ℰ_n(s) ds`; and `𝒲_n(0) = 1` almost
surely. -/
theorem hasBracket_WN (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {n T : ℝ} (hn : 1 ≤ n) (hT : 0 < T) :
    (∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => EN n ψ ω s fun _ => 1) volume 0 T) ∧
    HasBracket T (filtN n 𝓕) (WN n ψ)
      (fun t ω => aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) μ ∧
    ∀ᵐ ω ∂μ, WN n ψ 0 ω = 1 := by
  have hφ1 : IsC13 T (fun _ _ => (1 : ℝ)) (fun _ _ => 0) 1 := by
    refine ⟨fun _ _ => contDiff_const, fun _ _ _ => hasDerivWithinAt_const _ _ _,
      ⟨continuousOn_const, fun k _ => ?_⟩, ⟨![1, 0, 0, 0, 0], ?_, fun t _ x => ?_⟩⟩
    · simp only [iteratedDeriv_const]; exact continuousOn_const
    · simp [Fin.sum_univ_five]
    · simp [iteratedDeriv_const]
  obtain ⟨hA, hBr, -, -⟩ := prop_3_1 hB hψ hn hT hφ1
  have hAN : ∀ y, AN n (fun _ => (1 : ℝ)) y = 0 := fun y => by
    simp only [AN, deriv_const', mul_zero, sub_zero, mul_one]
    rw [cN, Real.cosh_eq]; ring
  have hMN : ∀ t ω, MN n ψ (fun _ _ => 1) (fun _ _ => 0) t ω = WN n ψ t ω - 1 := fun t ω => by
    simp only [MN, hAN, zero_add, pairZ, mul_zero, tsum_zero, intervalIntegral.integral_zero,
      sub_zero]
    rfl
  have hQN : ∀ t ω, QN n ψ (fun _ _ => 1) t ω =
      aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1 := fun t ω => by
    obtain ⟨ha, hab, hb, hl⟩ := tilt_exp_half (thetaN n)
    have hlam : (Real.exp (thetaN n / 2) - Real.exp (-thetaN n / 2)) ^ 2 = lambdaN n := by
      unfold lambdaN; rw [hl]; nlinarith
    simp only [QN, QNdens, EN, mul_one, hlam, tsum_mul_right]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, aN_mul_rpow hn]
    ring
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hA] with ω h using ⟨h.1, h.2.2.2.2⟩
  · have h1 := hasBracket_add_const' (hBr.congr hT.le (ae_of_all _ fun ω t _ => hMN t ω)
      (ae_of_all _ fun ω t _ => hQN t ω)) 1
    exact h1.congr hT.le (ae_of_all _ fun ω t _ => by ring) (ae_of_all _ fun _ _ _ => rfl)
  · filter_upwards [hψ.ae_init] with ω hω
    have e : ∀ x : ℤ, zN n ψ ω 0 x * 1 = if x = 0 then 1 else 0 := fun x => by
      by_cases hx : x = 0 <;> simp [zN, density, hω, waveInit_apply, hx]
    simp only [WN, pairZ]
    rw [tsum_congr e, tsum_ite_eq]

end QSSEPtoKPZ
