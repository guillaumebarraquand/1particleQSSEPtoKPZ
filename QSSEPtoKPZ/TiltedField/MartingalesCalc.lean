/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.TiltedField.Defs
public import QSSEPtoKPZ.WaveFunction.Defs

/-!
# Proof of Proposition 3.1: the deterministic computations (task E2)

The proof of Proposition 3.1 applies Lemma 2.3 (1) on `[0, nT/2]` to the weight
`α_s(x) = e^{θ_n x - λ_n s} φ_{2s/n}(y_n(2s/n, x))` (`tiltAlpha`). This file contains everything
about `α` that does not involve probability:

* `tiltChain_hasDerivWithinAt`: the chain rule for `s ↦ φ(κ s, A + β s)` when `φ` has continuous
  partial derivatives on `[0,T] × ℝ` (one-sided in time at `0` and `T`);
* `tiltAlpha_hasDerivWithinAt`, `tiltAlphaDeriv_continuousOn`, `tiltAlpha_bound`: the hypotheses
  of Lemma 2.3 (1) for `α`, with `∂ₛα = tiltAlphaDeriv`;
* `tiltAlpha_pair`, `tiltAlpha_drift`, `tiltAlpha_bracket`: the identities of the proof of
  Proposition 3.1, `𝒵_n(t;φ_t) = ∑ₓ α_{nt/2}(x) P(nt/2,x)`,
  `(∂ₛα_s + Δα_s)(x) = (2/n) e^{θ_n x - λ_n s} [∂ₜφ_t + 𝒜_nφ_t](y_n(t,x))` and
  `2 (α_s(x+1) - α_s(x))² P(s,x) P(s,x+1)
  = 2 𝔷_n(t,x) 𝔷_n(t,x+1) [e^{θ_n/2} φ_t(y_n(t,x+1)) - e^{-θ_n/2} φ_t(y_n(t,x))]²`,
  with `s = nt/2`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **Chain rule with partial derivatives.** Let `φ : ℝ → ℝ → ℝ` have, for `t ∈ [0,T]`, a time
derivative `φt` within `[0,T]` and a space derivative `φx`, the latter being continuous on
`[0,T] × ℝ`. If `s ↦ κ s` maps `S` into `[0,T]`, then `s ↦ φ(κ s, A + β s)` has derivative
`φt(κ s, A + β s) κ + φx(κ s, A + β s) β` within `S` at every `s ∈ S`. (Proof: split the
increment into a time increment and a space increment; the latter is controlled by the mean value
inequality and the continuity of `φx`.) -/
theorem tiltChain_hasDerivWithinAt {T : ℝ} {φ φt φx : ℝ → ℝ → ℝ}
    (hφt : ∀ y, ∀ t ∈ Icc 0 T, HasDerivWithinAt (φ · y) (φt t y) (Icc 0 T) t)
    (hφx : ∀ t ∈ Icc 0 T, ∀ y, HasDerivAt (φ t) (φx t y) y)
    (hc : ContinuousOn (Function.uncurry φx) (Icc 0 T ×ˢ univ))
    {S : Set ℝ} {κ A β s : ℝ} (hS : MapsTo (fun s => κ * s) S (Icc 0 T)) (hs : s ∈ S) :
    HasDerivWithinAt (fun s => φ (κ * s) (A + β * s))
      (φt (κ * s) (A + β * s) * κ + φx (κ * s) (A + β * s) * β) S s := by
  set q : ℝ → ℝ := fun s' => A + β * s' with hq
  have hG2 : HasDerivWithinAt (fun s' => φ (κ * s') (q s)) (φt (κ * s) (q s) * κ) S s := by
    have h1 : HasDerivWithinAt (fun s' => κ * s') κ S s := by
      simpa using (hasDerivWithinAt_id s S).const_mul κ
    exact (hφt (q s) (κ * s) (hS hs)).comp s h1 hS
  have hG1 : HasDerivWithinAt (fun s' => φ (κ * s') (q s') - φ (κ * s') (q s))
      (φx (κ * s) (q s) * β) S s := by
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    set c0 := φx (κ * s) (q s) with hc0
    have hcw : ContinuousWithinAt (Function.uncurry φx) (Icc 0 T ×ˢ univ) (κ * s, q s) :=
      hc _ ⟨hS hs, mem_univ _⟩
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hcw (ε / (|β| + 1)) (by positivity)
    have hδ2 : 0 < δ / (|κ| + |β| + 1) := by positivity
    have hev : ∀ᶠ s' in 𝓝[S] s, s' ∈ S ∧ s' ∈ Metric.ball s (δ / (|κ| + |β| + 1)) :=
      eventually_mem_nhdsWithin.and
        (eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds s hδ2))
    filter_upwards [hev] with s' ⟨hs', hd⟩
    rw [Metric.mem_ball, Real.dist_eq] at hd
    have hκd : |κ| * |s' - s| < δ := by
      calc |κ| * |s' - s| ≤ (|κ| + |β| + 1) * |s' - s| := by
            gcongr; linarith [abs_nonneg β]
        _ < (|κ| + |β| + 1) * (δ / (|κ| + |β| + 1)) := by gcongr
        _ = δ := by field_simp
    have hβd : |β| * |s' - s| < δ := by
      calc |β| * |s' - s| ≤ (|κ| + |β| + 1) * |s' - s| := by
            gcongr; linarith [abs_nonneg κ]
        _ < (|κ| + |β| + 1) * (δ / (|κ| + |β| + 1)) := by gcongr
        _ = δ := by field_simp
    have hderiv : ∀ η ∈ uIcc (q s) (q s'), HasDerivWithinAt (fun η => φ (κ * s') η - c0 * η)
        (φx (κ * s') η - c0) (uIcc (q s) (q s')) η := by
      intro η _
      have := ((hφx _ (hS hs') η).sub ((hasDerivAt_id η).const_mul c0)).hasDerivWithinAt
        (s := uIcc (q s) (q s'))
      convert this using 1
      · ext η; simp
      · ring
    have hbound : ∀ η ∈ uIcc (q s) (q s'), ‖φx (κ * s') η - c0‖ ≤ ε / (|β| + 1) := by
      intro η hη
      have hdist : dist (κ * s', η) (κ * s, q s) < δ := by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
        refine ⟨?_, ?_⟩
        · rw [← mul_sub, abs_mul]; exact hκd
        · calc |η - q s| ≤ |q s' - q s| := Set.abs_sub_left_of_mem_uIcc hη
            _ = |β| * |s' - s| := by rw [hq]; simp only; rw [← abs_mul]; ring_nf
            _ < δ := hβd
      have := hδ' (x := (κ * s', η)) ⟨hS hs', mem_univ _⟩ hdist
      rw [Real.dist_eq] at this
      exact this.le
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
    have e1 : (φ (κ * s') (q s') - φ (κ * s') (q s)) - (φ (κ * s) (q s) - φ (κ * s) (q s)) -
        (s' - s) • (c0 * β) = (φ (κ * s') (q s') - c0 * q s') - (φ (κ * s') (q s) - c0 * q s) := by
      rw [hq, smul_eq_mul]; ring
    have e2 : ‖q s' - q s‖ = |β| * ‖s' - s‖ := by
      rw [hq, Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]; ring_nf
    rw [e1]
    calc _ ≤ ε / (|β| + 1) * ‖q s' - q s‖ := hmvt
      _ = ε * (|β| / (|β| + 1)) * ‖s' - s‖ := by rw [e2]; ring
      _ ≤ ε * 1 * ‖s' - s‖ := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = ε * ‖s' - s‖ := by ring
  have := hG1.add hG2
  convert this using 1
  · ext s'; simp only [Pi.add_apply, hq, sub_add_cancel]
  · simp only [hq]; ring

/-! ### Powers of `n` and exponentials of `θ_n` -/

/-- The powers of `n` used in Section 3, in terms of `r = n^{1/4}`. -/
lemma tilt_rpow {n : ℝ} (hn : 1 ≤ n) :
    0 < n ^ (1 / 4 : ℝ) ∧ n ^ (1 / 2 : ℝ) = (n ^ (1 / 4 : ℝ)) ^ 2 ∧ n = (n ^ (1 / 4 : ℝ)) ^ 4 ∧
      n ^ (3 / 4 : ℝ) = (n ^ (1 / 4 : ℝ)) ^ 3 ∧ n ^ (-1 / 2 : ℝ) = ((n ^ (1 / 4 : ℝ)) ^ 2)⁻¹ ∧
      n ^ (-1 / 4 : ℝ) = (n ^ (1 / 4 : ℝ))⁻¹ := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hp : ∀ k : ℕ, (n ^ (1 / 4 : ℝ)) ^ k = n ^ ((k : ℝ) / 4) := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  refine ⟨Real.rpow_pos_of_pos hn0 _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; norm_num
  · rw [hp]; norm_num
  · rw [hp]; norm_num
  · rw [hp, ← Real.rpow_neg hn0.le]; norm_num
  · rw [← Real.rpow_neg hn0.le]; norm_num

/-- `e^{θ/2} e^{θ/2} = e^θ`, `e^{-θ/2} e^{θ/2} = 1`, `e^{-θ/2} e^{-θ/2} = e^{-θ}`, and
`2 (cosh θ - 1) = e^θ + e^{-θ} - 2`. -/
lemma tilt_exp_half (θ : ℝ) :
    Real.exp (θ / 2) * Real.exp (θ / 2) = Real.exp θ ∧
      Real.exp (θ / 2) * Real.exp (-θ / 2) = 1 ∧
      Real.exp (-θ / 2) * Real.exp (-θ / 2) = Real.exp (-θ) ∧
      2 * (Real.cosh θ - 1) = Real.exp θ + Real.exp (-θ) - 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.exp_add]; ring_nf
  · rw [← Real.exp_add]; ring_nf; simp
  · rw [← Real.exp_add]; ring_nf
  · rw [Real.cosh_eq]; ring

/-- `λ_n ≥ 0`. -/
lemma tiltLambda_nonneg (n : ℝ) : 0 ≤ lambdaN n := by
  have := Real.one_le_cosh (thetaN n)
  unfold lambdaN; linarith

/-- `θ_n ≥ 0`. -/
lemma tiltTheta_nonneg {n : ℝ} (hn : 1 ≤ n) : 0 ≤ thetaN n :=
  Real.rpow_nonneg (zero_le_one.trans hn) _

/-! ### The weight `α` of the proof of Proposition 3.1 -/

/-- The slope `d/ds y_n(2s/n, x) = -2 n^{-3/4}`, written `-(n^{3/4} (2/n)) / n^{1/2}`. -/
def tiltSlope (n : ℝ) : ℝ := -(n ^ (3 / 4 : ℝ) * (2 / n)) / n ^ (1 / 2 : ℝ)

/-- The weight of the proof of Proposition 3.1:
`α_s(x) = e^{θ_n x - λ_n s} φ_{2s/n}(y_n(2s/n, x))`. -/
def tiltAlpha (n : ℝ) (φ : ℝ → ℝ → ℝ) (s : ℝ) (x : ℤ) : ℝ :=
  Real.exp (thetaN n * x - lambdaN n * s) * φ (2 / n * s) (rescaledPosition n (2 / n * s) x)

/-- The time derivative of `tiltAlpha`:
`∂ₛα_s(x) = e^{θ_n x - λ_n s} [-λ_n φ_t + (2/n) ∂ₜφ_t + ∂ₓφ_t · (-2 n^{-3/4})](y_n(t,x))`,
`t = 2s/n`. -/
def tiltAlphaDeriv (n : ℝ) (φ φt : ℝ → ℝ → ℝ) (s : ℝ) (x : ℤ) : ℝ :=
  Real.exp (thetaN n * x - lambdaN n * s) *
    (-lambdaN n * φ (2 / n * s) (rescaledPosition n (2 / n * s) x) +
      (φt (2 / n * s) (rescaledPosition n (2 / n * s) x) * (2 / n) +
        deriv (φ (2 / n * s)) (rescaledPosition n (2 / n * s) x) * tiltSlope n))

/-- `y_n(2s/n, x)` is affine in `s`. -/
lemma tiltPos_two_div (n s : ℝ) (x : ℤ) :
    rescaledPosition n (2 / n * s) x = x / n ^ (1 / 2 : ℝ) + tiltSlope n * s := by
  unfold rescaledPosition tiltSlope; ring

/-- `y_n(t, x ± 1) = y_n(t, x) ± n^{-1/2}`. -/
lemma tiltPos_add_one {n : ℝ} (hn : 1 ≤ n) (t : ℝ) (x : ℤ) :
    rescaledPosition n t (x + 1) = rescaledPosition n t x + n ^ (-1 / 2 : ℝ) ∧
      rescaledPosition n t (x - 1) = rescaledPosition n t x - n ^ (-1 / 2 : ℝ) := by
  obtain ⟨hr, h2, -, -, hm2, -⟩ := tilt_rpow hn
  unfold rescaledPosition
  rw [h2, hm2]
  push_cast
  constructor <;> field_simp <;> ring

/-- The map `s ↦ 2s/n` sends `[0, nT/2]` into `[0, T]`. -/
lemma tilt_mapsTo_two_div {n T : ℝ} (hn : 1 ≤ n) :
    MapsTo (fun s => 2 / n * s) (Icc 0 (n / 2 * T)) (Icc 0 T) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  intro s hs
  refine ⟨by have := hs.1; positivity, ?_⟩
  calc 2 / n * s ≤ 2 / n * (n / 2 * T) := by gcongr; exact hs.2
    _ = T := by field_simp

/-- The space derivatives of `φ` in `IsC13`, rewritten. -/
lemma IsC13.tilt_continuousOn_val {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc 0 T ×ˢ univ) := by
  simpa [iteratedDeriv_zero] using hφ.continuousOn.2 0 (by norm_num)

/-- The first space derivative of `φ` is continuous on `[0,T] × ℝ`. -/
lemma IsC13.tilt_continuousOn_deriv {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (φ p.1) p.2) (Icc 0 T ×ˢ univ) := by
  simpa [iteratedDeriv_one] using hφ.continuousOn.2 1 (by norm_num)

/-- **The time derivative of `α`** (hypothesis of Lemma 2.3 (1)). -/
lemma tiltAlpha_hasDerivWithinAt {n T C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) (x : ℤ) :
    ∀ s ∈ Icc 0 (n / 2 * T), HasDerivWithinAt (tiltAlpha n φ · x) (tiltAlphaDeriv n φ φt s x)
      (Icc 0 (n / 2 * T)) s := by
  intro s hs
  have hfun : (tiltAlpha n φ · x) = fun s => Real.exp (thetaN n * x - lambdaN n * s) *
      φ (2 / n * s) (x / n ^ (1 / 2 : ℝ) + tiltSlope n * s) := by
    ext s; simp only [tiltAlpha, tiltPos_two_div]
  rw [hfun]
  have hφx : ∀ t ∈ Icc 0 T, ∀ y, HasDerivAt (φ t) (deriv (φ t) y) y := fun t ht y =>
    (((hφ.contDiff t ht).differentiable (by norm_num)) y).hasDerivAt
  have hc : ContinuousOn (Function.uncurry fun t y => deriv (φ t) y) (Icc 0 T ×ˢ univ) :=
    hφ.tilt_continuousOn_deriv
  have hchain := tiltChain_hasDerivWithinAt (φx := fun t y => deriv (φ t) y)
    (A := x / n ^ (1 / 2 : ℝ)) (β := tiltSlope n) hφ.hasDerivWithinAt hφx hc
    (tilt_mapsTo_two_div hn) hs
  have hexp : HasDerivAt (fun s => Real.exp (thetaN n * x - lambdaN n * s))
      (Real.exp (thetaN n * x - lambdaN n * s) * (-lambdaN n)) s := by
    have := ((hasDerivAt_const s (thetaN n * x)).sub ((hasDerivAt_id s).const_mul (lambdaN n))).exp
    convert this using 1
    · ext; simp
    · simp
  convert hexp.hasDerivWithinAt.mul hchain using 1
  simp only [tiltAlphaDeriv, tiltPos_two_div]
  ring

/-- **Continuity of `∂ₛα`** (hypothesis of Lemma 2.3 (1)). -/
lemma tiltAlphaDeriv_continuousOn {n T C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) (x : ℤ) :
    ContinuousOn (tiltAlphaDeriv n φ φt · x) (Icc 0 (n / 2 * T)) := by
  set g : ℝ → ℝ × ℝ := fun s => (2 / n * s, rescaledPosition n (2 / n * s) x) with hg
  have hgc : Continuous g := by
    simp only [hg, tiltPos_two_div]; fun_prop
  have hgm : MapsTo g (Icc 0 (n / 2 * T)) (Icc 0 T ×ˢ univ) := fun s hs =>
    ⟨tilt_mapsTo_two_div hn hs, mem_univ _⟩
  have h0 := hφ.tilt_continuousOn_val.comp hgc.continuousOn hgm
  have h1 := hφ.continuousOn.1.comp hgc.continuousOn hgm
  have h2 := hφ.tilt_continuousOn_deriv.comp hgc.continuousOn hgm
  have he : Continuous fun s : ℝ => Real.exp (thetaN n * x - lambdaN n * s) := by fun_prop
  exact he.continuousOn.mul ((continuousOn_const.mul h0).add
    ((h1.mul continuousOn_const).add (h2.mul continuousOn_const)))

/-- **The growth bound on `α`** (hypothesis of Lemma 2.3 (1), with `a = θ_n`). -/
lemma tiltAlpha_bound {n T C : ℝ} (hn : 1 ≤ n) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) :
    ∃ C' : ℝ, ∀ x : ℤ, ∀ s ∈ Icc 0 (n / 2 * T),
      |tiltAlpha n φ s x| + |tiltAlphaDeriv n φ φt s x| ≤ C' * Real.exp (thetaN n * |(x : ℝ)|) := by
  obtain ⟨c, -, hc⟩ := hφ.bound
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hl := tiltLambda_nonneg n
  refine ⟨c 0 + lambdaN n * c 0 + c 1 * (2 / n) + c 2 * |tiltSlope n|, fun x s hs => ?_⟩
  have ht := tilt_mapsTo_two_div (T := T) hn hs
  obtain ⟨h0, h1, h2, -, -⟩ := hc _ ht (rescaledPosition n (2 / n * s) x)
  rw [iteratedDeriv_one] at h2
  set E := Real.exp (thetaN n * x - lambdaN n * s)
  have hE : E ≤ Real.exp (thetaN n * |(x : ℝ)|) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left (le_abs_self (x : ℝ)) (tiltTheta_nonneg hn)
    nlinarith [hs.1]
  have hE0 : 0 < E := Real.exp_pos _
  have hc0 : 0 ≤ c 0 := (abs_nonneg _).trans h0
  have hc1 : 0 ≤ c 1 := (abs_nonneg _).trans h1
  have hc2 : 0 ≤ c 2 := (abs_nonneg _).trans h2
  have hA : |tiltAlpha n φ s x| ≤ E * c 0 := by
    rw [tiltAlpha, abs_mul, abs_of_pos hE0]; gcongr
  have hB : |tiltAlphaDeriv n φ φt s x| ≤
      E * (lambdaN n * c 0 + c 1 * (2 / n) + c 2 * |tiltSlope n|) := by
    rw [tiltAlphaDeriv, abs_mul, abs_of_pos hE0]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [add_assoc]
    gcongr
    · rw [abs_mul, abs_neg, abs_of_nonneg hl]; gcongr
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / n)]
      gcongr
  calc _ ≤ E * c 0 + E * (lambdaN n * c 0 + c 1 * (2 / n) + c 2 * |tiltSlope n|) :=
        add_le_add hA hB
    _ = (c 0 + lambdaN n * c 0 + c 1 * (2 / n) + c 2 * |tiltSlope n|) * E := by ring
    _ ≤ _ := by gcongr

/-! ### The identities of the proof of Proposition 3.1 -/

variable {Ω : Type*}

/-- `zN` in terms of the time `s = (n/2) t` of `P`. -/
lemma tiltZ_eq_half {n : ℝ} (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) :
    zN n ψ ω t x =
      Real.exp (thetaN n * x - lambdaN n * (n / 2 * t)) * density ψ ω (n / 2 * t) x := by
  unfold zN; ring_nf

/-- `𝒵_n(t;φ_t) = ∑ₓ α_{nt/2}(x) P(nt/2,x)`, termwise. -/
lemma tiltAlpha_pair {n : ℝ} (hn : 1 ≤ n) (φ : ℝ → ℝ → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω)
    (t : ℝ) (x : ℤ) :
    tiltAlpha n φ (n / 2 * t) x * density ψ ω (n / 2 * t) x =
      zN n ψ ω t x * φ t (rescaledPosition n t x) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have e : 2 / n * (n / 2 * t) = t := by field_simp
  rw [tiltZ_eq_half, tiltAlpha, e]; ring

/-- `α_0(0) = φ_0(0)`. -/
lemma tiltAlpha_zero (n : ℝ) (φ : ℝ → ℝ → ℝ) : tiltAlpha n φ 0 0 = φ 0 0 := by
  simp [tiltAlpha, rescaledPosition]

/-- **The drift**: `(∂ₛα_s + Δα_s)(x) P(s,x) = (2/n) 𝔷_n(t,x) [∂ₜφ_t + 𝒜_nφ_t](y_n(t,x))` for
`s = nt/2` (uses `2 + λ_n = 2 c_n`). -/
lemma tiltAlpha_drift {n : ℝ} (hn : 1 ≤ n) (φ φt : ℝ → ℝ → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω)
    (u : ℝ) (x : ℤ) :
    (tiltAlphaDeriv n φ φt (n / 2 * u) x + lap (tiltAlpha n φ (n / 2 * u)) x) *
        density ψ ω (n / 2 * u) x =
      (2 / n) * (zN n ψ ω u x *
        (φt u (rescaledPosition n u x) + AN n (φ u) (rescaledPosition n u x))) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨hr, h2, h4, h3, -, -⟩ := tilt_rpow hn
  have e : 2 / n * (n / 2 * u) = u := by field_simp
  obtain ⟨hp, hm⟩ := tiltPos_add_one hn u x
  have hsl : tiltSlope n = -(2 / n) * n ^ (1 / 4 : ℝ) := by
    unfold tiltSlope; rw [h2, h3]; field_simp
  have hEp : Real.exp (thetaN n * ((x + 1 : ℤ) : ℝ) - lambdaN n * (n / 2 * u)) =
      Real.exp (thetaN n * x - lambdaN n * (n / 2 * u)) * Real.exp (thetaN n) := by
    rw [← Real.exp_add]; push_cast; ring_nf
  have hEm : Real.exp (thetaN n * ((x - 1 : ℤ) : ℝ) - lambdaN n * (n / 2 * u)) =
      Real.exp (thetaN n * x - lambdaN n * (n / 2 * u)) * Real.exp (-thetaN n) := by
    rw [← Real.exp_add]; push_cast; ring_nf
  have hl : cN n = (lambdaN n + 2) / 2 := by unfold lambdaN cN; ring
  rw [tiltZ_eq_half, lap, tiltAlphaDeriv, tiltAlpha, tiltAlpha, tiltAlpha, e, hEp, hEm, hp, hm, AN,
    hsl, hl]
  generalize Real.exp (thetaN n * x - lambdaN n * (n / 2 * u)) = E
  field_simp
  ring

/-- **The bracket**: `2 (α_s(x+1) - α_s(x))² P(s,x) P(s,x+1)
= 2 𝔷_n(t,x) 𝔷_n(t,x+1) [e^{θ_n/2} φ_t(y_n(t,x+1)) - e^{-θ_n/2} φ_t(y_n(t,x))]²` for `s = nt/2`. -/
lemma tiltAlpha_bracket {n : ℝ} (hn : 1 ≤ n) (φ : ℝ → ℝ → ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω)
    (u : ℝ) (x : ℤ) :
    2 * (tiltAlpha n φ (n / 2 * u) (x + 1) - tiltAlpha n φ (n / 2 * u) x) ^ 2 *
        density ψ ω (n / 2 * u) x * density ψ ω (n / 2 * u) (x + 1) =
      2 * (zN n ψ ω u x * zN n ψ ω u (x + 1) *
        (Real.exp (thetaN n / 2) * φ u (rescaledPosition n u (x + 1)) -
          Real.exp (-thetaN n / 2) * φ u (rescaledPosition n u x)) ^ 2) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have e : 2 / n * (n / 2 * u) = u := by field_simp
  set E := Real.exp (thetaN n * x - lambdaN n * (n / 2 * u))
  have hEp : Real.exp (thetaN n * ((x + 1 : ℤ) : ℝ) - lambdaN n * (n / 2 * u)) =
      E * Real.exp (thetaN n) := by
    rw [← Real.exp_add]; push_cast; ring_nf
  obtain ⟨ha, hab, -, -⟩ := tilt_exp_half (thetaN n)
  rw [tiltZ_eq_half, tiltZ_eq_half, tiltAlpha, tiltAlpha, e, hEp, ← ha]
  set a := Real.exp (thetaN n / 2)
  set b := Real.exp (-thetaN n / 2)
  set A := φ u (rescaledPosition n u (x + 1))
  set B := φ u (rescaledPosition n u x)
  set P1 := density ψ ω (n / 2 * u) x
  set P2 := density ψ ω (n / 2 * u) (x + 1)
  linear_combination (2 * E ^ 2 * P1 * P2 * (2 * a ^ 2 * A * B - B ^ 2 * (1 + a * b))) * hab

/-! ### The pointwise inequalities of items (2) and (3) -/

/-- Item (2), pointwise: if `|u| ≤ c₀`, `|u - v| ≤ n^{-1/2} c₂` and `c₀ + c₂ ≤ C`, then
`(e^{θ_n/2} u - e^{-θ_n/2} v)² ≤ 2 C² λ_n`. -/
lemma tilt_item2_pointwise {n : ℝ} (hn : 1 ≤ n) {u v c0 c2 C : ℝ} (hu : |u| ≤ c0)
    (huv : |u - v| ≤ n ^ (-1 / 2 : ℝ) * c2) (hc0 : 0 ≤ c0) (hc2 : 0 ≤ c2) (hC : c0 + c2 ≤ C) :
    (Real.exp (thetaN n / 2) * u - Real.exp (-thetaN n / 2) * v) ^ 2 ≤ 2 * C ^ 2 * lambdaN n := by
  obtain ⟨ha, hab, hb, hl⟩ := tilt_exp_half (thetaN n)
  obtain ⟨hlo, -⟩ := constants_bounds hn
  set h := n ^ (-1 / 2 : ℝ)
  have hh0 : 0 ≤ h := Real.rpow_nonneg (zero_le_one.trans hn) _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  set a := Real.exp (thetaN n / 2)
  set b := Real.exp (-thetaN n / 2)
  have hb1 : b * b ≤ 1 := by
    rw [hb]; exact Real.exp_le_one_iff.2 (by linarith [tiltTheta_nonneg hn])
  have hlam : (a - b) ^ 2 = lambdaN n := by
    unfold lambdaN; rw [hl]; nlinarith [ha, hab, hb]
  have hX : (a * u - b * v) ^ 2 ≤ 2 * (a - b) ^ 2 * u ^ 2 + 2 * (b * b) * (u - v) ^ 2 := by
    nlinarith [sq_nonneg ((a - b) * u - b * (u - v))]
  have hu2 : u ^ 2 ≤ c0 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have huv2 : (u - v) ^ 2 ≤ lambdaN n * c2 ^ 2 := by
    rw [← sq_abs]
    calc |u - v| ^ 2 ≤ (h * c2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) huv 2
      _ = (h * h) * c2 ^ 2 := by ring
      _ ≤ h * c2 ^ 2 := by gcongr; nlinarith
      _ ≤ _ := by gcongr
  have hl0 := tiltLambda_nonneg n
  have hvv : 0 ≤ (u - v) ^ 2 := sq_nonneg _
  calc _ ≤ 2 * (a - b) ^ 2 * u ^ 2 + 2 * (b * b) * (u - v) ^ 2 := hX
    _ ≤ 2 * lambdaN n * c0 ^ 2 + 2 * 1 * (lambdaN n * c2 ^ 2) := by
        rw [hlam]; gcongr
    _ = 2 * lambdaN n * (c0 ^ 2 + c2 ^ 2) := by ring
    _ ≤ 2 * lambdaN n * C ^ 2 := by gcongr; nlinarith
    _ = _ := by ring

/-- Item (3), pointwise, with (3.18): if `|u| ≤ c₀`, `|u - v| ≤ n^{-1/2} c₂`, `c₀, c₂ ≤ C`, then
`n |(e^{θ_n/2} u - e^{-θ_n/2} v)² - λ_n u v| ≤ 5 n^{-1/4} C² n^{1/2}`. -/
lemma tilt_item3_pointwise {n : ℝ} (hn : 1 ≤ n) {u v c0 c2 C : ℝ} (hu : |u| ≤ c0)
    (huv : |u - v| ≤ n ^ (-1 / 2 : ℝ) * c2) (hc2 : 0 ≤ c2) (hC0 : c0 ≤ C)
    (hC2 : c2 ≤ C) :
    n * |(Real.exp (thetaN n / 2) * u - Real.exp (-thetaN n / 2) * v) ^ 2 - lambdaN n * (u * v)| ≤
      5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * n ^ (1 / 2 : ℝ) := by
  obtain ⟨ha, hab, hb, hl⟩ := tilt_exp_half (thetaN n)
  obtain ⟨-, -, -, -, hc1, hc12⟩ := constants_bounds hn
  obtain ⟨hr, h2, h4, -, hm2, hm4⟩ := tilt_rpow hn
  have hθ0 := tiltTheta_nonneg hn
  set θ := thetaN n
  set r := n ^ (1 / 4 : ℝ)
  have hθr : θ = r⁻¹ := hm4
  -- the identity (3.18)
  have hid : (Real.exp (θ / 2) * u - Real.exp (-θ / 2) * v) ^ 2 - lambdaN n * (u * v) =
      (u - v) * (Real.exp θ * u - Real.exp (-θ) * v) := by
    unfold lambdaN; rw [hl, ← ha, ← hb]; linear_combination (-(2 : ℝ) * u * v) * hab
  -- `|e^θ u - e^{-θ} v| ≤ 5 θ C`
  have hsinh : Real.sinh θ ≤ 2 * θ := by
    have h1 := sinh_le_mul_cosh hθ0
    have h2' : Real.cosh θ ≤ 2 := by
      have : cN n ≤ Real.cosh 1 := hc1
      unfold cN at this; linarith
    nlinarith
  have he' : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hh : n ^ (-1 / 2 : ℝ) ≤ θ := by
    rw [hm2, hθr]
    rw [inv_le_inv₀ (by positivity) hr]
    have : 1 ≤ r := Real.one_le_rpow hn (by norm_num)
    nlinarith
  have hw : |Real.exp θ * u - Real.exp (-θ) * v| ≤ 5 * θ * C := by
    have e : Real.exp θ * u - Real.exp (-θ) * v =
        2 * Real.sinh θ * u + Real.exp (-θ) * (u - v) := by
      rw [Real.sinh_eq]; ring
    rw [e]
    have hs0 : 0 ≤ Real.sinh θ := Real.sinh_nonneg_iff.2 hθ0
    calc _ ≤ |2 * Real.sinh θ * u| + |Real.exp (-θ) * (u - v)| := abs_add_le _ _
      _ = 2 * Real.sinh θ * |u| + Real.exp (-θ) * |u - v| := by
          rw [abs_mul (2 * Real.sinh θ) u, abs_mul (Real.exp (-θ)) (u - v),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sinh θ),
            abs_of_pos (Real.exp_pos _)]
      _ ≤ 2 * (2 * θ) * C + 1 * (θ * C) := by
          gcongr
          · exact hu.trans hC0
          · exact huv.trans (mul_le_mul hh hC2 hc2 hθ0)
      _ = 5 * θ * C := by ring
  have hv : |u - v| ≤ n ^ (-1 / 2 : ℝ) * C := huv.trans (by gcongr)
  rw [hid, abs_mul]
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  calc n * (|u - v| * |Real.exp θ * u - Real.exp (-θ) * v|)
      ≤ n * (n ^ (-1 / 2 : ℝ) * C * (5 * θ * C)) := by
        gcongr
        exact (abs_nonneg _).trans hv
    _ = 5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * n ^ (1 / 2 : ℝ) := by
        rw [hm2, hθr, hm4, h2]
        nth_rewrite 1 [h4]
        field_simp

end QSSEPtoKPZ
