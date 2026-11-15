/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.LevyQV

/-!
# Lévy's characterization: the bounded case (task G7a)

Let `⟨M⟩ = A` on `[0, T]`, `s ≤ t ≤ T`, and assume that for every `ω`, `|M_r - M_s| ≤ R` and
`0 ≤ A_{r'} - A_r ≤ c (r' - r)` for `s ≤ r ≤ r' ≤ t`, and that the path of `M` is continuous on
`[s, t]`. Then for `B ∈ 𝓕_s`,
`∫_B exp(i u (M_t - M_s) + u² (A_t - A_s) / 2) dℙ = ℙ(B)` (`HasBracket.levy_setIntegral_bdd`).

Proof. Cut `[s, t]` into `n` pieces `t_k`, and write `d_k = M_{t_{k+1}} - M_{t_k}`,
`β_k = u² (A_{t_{k+1}} - A_{t_k}) / 2`, `Z_k = exp(i u (M_{t_k} - M_s) + u² (A_{t_k} - A_s) / 2)`,
so that `Z_{k+1} = Z_k e^{i u d_k + β_k}`. By the third-order Taylor formula
`e^{i u d + β} - 1 = i u d - (u²/2) (d² - 2β/u²) + ρ`, and the first two terms integrate to `0`
against `𝟙_B Z_k` (martingale and bracket increments against the past). The remainders satisfy
`|ρ_k| ≤ |u| D β_k + O(n⁻²) + 4 e^W (|u|³ D d_k² + O(n⁻³))` with `D = max_k |d_k|`, so that
`|∫_B Z_n - ℙ(B)| ≲ 𝔼 D + λ 𝔼 D² + λ⁻¹ 𝔼 Q² + O(n⁻¹)` for every `λ > 0`, where
`Q = ∑_k d_k²` has `𝔼 Q² ≤ 6 R⁴` (`IsCL2Mart.levy_integral_qv_sq_le`). As `n → ∞`,
`D → 0` (uniform continuity of the path) boundedly, hence `𝔼 D, 𝔼 D² → 0`; then `λ → ∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `(a + b)³ ≤ 4 (a³ + b³)` for `a, b ≥ 0`. -/
private lemma levy_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

/-- The bound on the Taylor remainder used for one step of the discretization. -/
private lemma levy_rho_le (u d β D W e : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ e) (hdD : |d| ≤ D)
    (hW : |u| * |d| + β ≤ W) :
    ‖Complex.exp (((u * d : ℝ) : ℂ) * Complex.I + (β : ℂ)) - 1 - ((u * d : ℝ) : ℂ) * Complex.I -
        ((β - (u * d) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      |u| * D * β + e ^ 2 / 2 + 4 * Real.exp W * (|u| ^ 3 * (D * d ^ 2) + e ^ 3) := by
  refine (levy_norm_exp_sub_le (u * d) β).trans ?_
  rw [abs_mul, abs_of_nonneg hβ0]
  have hu := abs_nonneg u
  have hd := abs_nonneg d
  have he : 0 ≤ e := hβ0.trans hβ
  have h1 : |u| * |d| * β ≤ |u| * D * β :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdD hu) hβ0
  have h2 : β ^ 2 / 2 ≤ e ^ 2 / 2 := by gcongr
  have h3 : (|u| * |d| + β) ^ 3 ≤ 4 * (|u| ^ 3 * (D * d ^ 2) + e ^ 3) := by
    refine (levy_cube_le (mul_nonneg hu hd) hβ0).trans ?_
    have hd3 : |d| ^ 3 ≤ D * d ^ 2 := by
      rw [← sq_abs d, pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right hdD (sq_nonneg _)
    have : (|u| * |d|) ^ 3 ≤ |u| ^ 3 * (D * d ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hd3 (pow_nonneg hu 3)
    have : β ^ 3 ≤ e ^ 3 := by gcongr
    linarith
  have h4 : Real.exp (|u| * |d| + β) ≤ Real.exp W := Real.exp_le_exp.2 hW
  have h5 : 0 ≤ (|u| * |d| + β) ^ 3 := by positivity
  have h6 : 0 ≤ 4 * (|u| ^ 3 * (D * d ^ 2) + e ^ 3) := h5.trans h3
  calc |u| * |d| * β + β ^ 2 / 2 + (|u| * |d| + β) ^ 3 * Real.exp (|u| * |d| + β)
      ≤ |u| * D * β + e ^ 2 / 2 +
          4 * (|u| ^ 3 * (D * d ^ 2) + e ^ 3) * Real.exp W := by
        gcongr
    _ = _ := by ring

/-- `∑_{k < n} (α f_k + c₁ + (γ g_k + c₂)) = α ∑ f + n c₁ + (γ ∑ g + n c₂)`. -/
private lemma levy_sum_lin (n : ℕ) (f g : ℕ → ℝ) (α c₁ γ c₂ : ℝ) :
    ∑ k ∈ range n, (α * f k + c₁ + (γ * g k + c₂)) =
      α * ∑ k ∈ range n, f k + n * c₁ + (γ * ∑ k ∈ range n, g k + n * c₂) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_range_succ, ih]; push_cast; ring

/-- The maximal increment `max_{k ≤ m} |M_{t_{k+1}} - M_{t_k}|` of `M` on the uniform partition
of `[s, t]` into `m + 1` pieces. -/
def levyMaxIncr (M : ℝ → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  (range (m + 1)).sup' nonempty_range_add_one fun k =>
    |M (levyPt s t (m + 1) (k + 1)) ω - M (levyPt s t (m + 1) k) ω|

/-- The discrete quadratic variation `∑_{k ≤ m} (M_{t_{k+1}} - M_{t_k})²` of `M` on the uniform
partition of `[s, t]` into `m + 1` pieces. -/
def levyQV (M : ℝ → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range (m + 1), (M (levyPt s t (m + 1) (k + 1)) ω - M (levyPt s t (m + 1) k) ω) ^ 2

variable [IsProbabilityMeasure μ] {T : ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ → Ω → ℝ}

/-- **The estimate for one partition.** Under the hypotheses of `HasBracket.levy_setIntegral_bdd`
(without continuity), for the partition into `m + 1` pieces and every `λ > 0`,
`|∫_B Z_t - ℙ(B)| ≤ K₀ (α₁ 𝔼 D + α₂ λ 𝔼 D² + α₂ λ⁻¹ 𝔼 Q² + α_m)` with `D` the maximal increment,
`Q` the discrete quadratic variation, and `α_m = O(1/m)`. -/
private theorem levy_estimate (h : HasBracket T 𝓕 M A μ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : (t : ℝ) ≤ T) {c R : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ ω (r : ℝ≥0), s ≤ r → r ≤ t → |M r ω - M s ω| ≤ R)
    (hA : ∀ ω (r r' : ℝ≥0), s ≤ r → r ≤ r' → r' ≤ t →
      0 ≤ A r' ω - A r ω ∧ A r' ω - A r ω ≤ c * ((r' : ℝ) - r))
    (u : ℝ) {B : Set Ω} (hB : MeasurableSet[𝓕 s] B) (m : ℕ) {l : ℝ} (hl : 0 < l) :
    ‖∫ ω in B, Complex.exp (((u * (M t ω - M s ω) : ℝ) : ℂ) * Complex.I +
        ((u ^ 2 / 2 * (A t ω - A s ω) : ℝ) : ℂ)) ∂μ - (μ.real B : ℂ)‖ ≤
      Real.exp (u ^ 2 / 2 * (c * (t - s))) *
        (|u| * (u ^ 2 / 2 * (c * (t - s))) * ∫ ω, levyMaxIncr M s t m ω ∂μ +
          2 * Real.exp (|u| * (2 * R) + u ^ 2 / 2 * (c * (t - s))) * |u| ^ 3 * l *
            ∫ ω, levyMaxIncr M s t m ω ^ 2 ∂μ +
          2 * Real.exp (|u| * (2 * R) + u ^ 2 / 2 * (c * (t - s))) * |u| ^ 3 / l *
            ∫ ω, levyQV M s t m ω ^ 2 ∂μ +
          (((m : ℝ) + 1) * (u ^ 2 / 2 * (c * ((t - s) / ((m : ℝ) + 1)))) ^ 2 / 2 +
            4 * Real.exp (|u| * (2 * R) + u ^ 2 / 2 * (c * (t - s))) *
              (((m : ℝ) + 1) * (u ^ 2 / 2 * (c * ((t - s) / ((m : ℝ) + 1)))) ^ 3))) := by
  -- the partition
  set n : ℕ := m + 1 with hn
  have hn0 : n ≠ 0 := Nat.succ_ne_zero m
  have hncast : (n : ℝ) = (m : ℝ) + 1 := by simp [hn]
  set p : ℕ → ℝ≥0 := levyPt s t n with hp
  have hpm : Monotone p := levyPt_mono s t n
  have hpt : ∀ k, p k ≤ t := levyPt_le hst n
  have hsp : ∀ k, s ≤ p k := le_levyPt s t n
  have hpT : ∀ k, (p k : ℝ) ≤ T := fun k => (NNReal.coe_le_coe.2 (hpt k)).trans htT
  have hsT : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans htT
  have hp0 : p 0 = s := levyPt_zero s t n
  have hpn : p n = t := levyPt_of_le hst hn0 le_rfl
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  set Δ : ℝ := ((t : ℝ) - s) / ((m : ℝ) + 1) with hΔdef
  have hΔ : ∀ k < n, (p (k + 1) : ℝ) - p k = Δ := fun k hk => by
    rw [levyPt_succ_sub hst hk, hncast]
  have hΔ0 : 0 ≤ Δ := div_nonneg (sub_nonneg.2 hst') (by positivity)
  have hΔts : Δ ≤ t - s := div_le_self (sub_nonneg.2 hst') (by linarith [m.cast_nonneg (α := ℝ)])
  -- measurability of `M` and `A` at the partition points
  have hMk : ∀ r : ℝ≥0, (r : ℝ) ≤ T → AEStronglyMeasurable[𝓕 r] (M r) μ := fun r hr =>
    aestronglyMeasurable_of_condExp_eq_self (h.condExp r r le_rfl hr)
  have hAk : ∀ r : ℝ≥0, (r : ℝ) ≤ T → AEStronglyMeasurable[𝓕 r] (A r) μ := fun r hr => by
    have hX := aestronglyMeasurable_of_condExp_eq_self (h.condExp_sq r r le_rfl hr)
    have := ((hMk r hr).pow 2).sub hX
    convert this using 1; ext ω; simp
  set y : ℕ → Ω → ℝ := fun k ω => M (p k) ω - M s ω with hy
  set a : ℕ → Ω → ℝ := fun k ω => A (p k) ω - A s ω with ha
  set d : ℕ → Ω → ℝ := fun k ω => M (p (k + 1)) ω - M (p k) ω with hd
  set b : ℕ → Ω → ℝ := fun k ω => A (p (k + 1)) ω - A (p k) ω with hb
  have hyk : ∀ k, AEStronglyMeasurable[𝓕 (p k)] (y k) μ := fun k =>
    (hMk _ (hpT k)).sub ((hMk s hsT).mono (𝓕.mono (hsp k)))
  have hak : ∀ k, AEStronglyMeasurable[𝓕 (p k)] (a k) μ := fun k =>
    (hAk _ (hpT k)).sub ((hAk s hsT).mono (𝓕.mono (hsp k)))
  have hdm : ∀ k, AEStronglyMeasurable (d k) μ := fun k =>
    ((hMk _ (hpT (k + 1))).mono (𝓕.le _)).sub ((hMk _ (hpT k)).mono (𝓕.le _))
  have hbm : ∀ k, AEStronglyMeasurable (b k) μ := fun k =>
    ((hAk _ (hpT (k + 1))).mono (𝓕.le _)).sub ((hAk _ (hpT k)).mono (𝓕.le _))
  -- bounds
  have hyb' : ∀ ω k, |y k ω| ≤ R := fun ω k => hbd ω (p k) (hsp k) (hpt k)
  have hdb' : ∀ ω k, |d k ω| ≤ 2 * R := fun ω k => by
    have e : d k ω = y (k + 1) ω - y k ω := by simp only [hd, hy]; ring
    rw [e]; exact (abs_sub _ _).trans (by linarith [hyb' ω (k + 1), hyb' ω k])
  have hab' : ∀ ω k, 0 ≤ a k ω ∧ a k ω ≤ c * (t - s) := fun ω k => by
    obtain ⟨h1, h2⟩ := hA ω s (p k) le_rfl (hsp k) (hpt k)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (by linarith [NNReal.coe_le_coe.2 (hpt k)]) hc)⟩
  have hbb' : ∀ ω k, 0 ≤ b k ω ∧ b k ω ≤ c * (t - s) := fun ω k => by
    obtain ⟨h1, h2⟩ := hA ω (p k) (p (k + 1)) (hsp k) (hpm (Nat.le_succ k)) (hpt _)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (by
      linarith [NNReal.coe_le_coe.2 (hpt (k + 1)), NNReal.coe_le_coe.2 (hsp k)]) hc)⟩
  have hbΔ : ∀ ω k, k < n → b k ω ≤ c * Δ := fun ω k hk => by
    have := (hA ω (p k) (p (k + 1)) (hsp k) (hpm (Nat.le_succ k)) (hpt _)).2
    rwa [hΔ k hk] at this
  have hdb : ∀ k, LevyBdd (d k) := fun k => levyBdd_of_le fun ω => hdb' ω k
  have hbb : ∀ k, LevyBdd (b k) := fun k => levyBdd_of_le fun ω => by
    rw [abs_of_nonneg (hbb' ω k).1]; exact (hbb' ω k).2
  -- the exponentials `Z_k` and `ξ_k = 𝟙_B Z_k`
  set K0 : ℝ := Real.exp (u ^ 2 / 2 * (c * (t - s))) with hK0
  set Z : ℕ → Ω → ℂ := fun k ω =>
    Complex.exp (((u * y k ω : ℝ) : ℂ) * Complex.I + ((u ^ 2 / 2 * a k ω : ℝ) : ℂ)) with hZ
  have hZn : ∀ k ω, ‖Z k ω‖ ≤ K0 := fun k ω => by
    simp only [hZ, Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hab' ω k).2 (by positivity))
  have hBm : MeasurableSet B := 𝓕.le s _ hB
  set ξ : ℕ → Ω → ℂ := fun k => B.indicator (Z k) with hξ
  have hξn : ∀ k ω, ‖ξ k ω‖ ≤ K0 := fun k ω =>
    (norm_indicator_le_norm_self _ _).trans (hZn k ω)
  have hZk : ∀ k, AEStronglyMeasurable[𝓕 (p k)] (Z k) μ := fun k => by
    have h1 := hyk k; have h2 := hak k
    simp only [hZ]; fun_prop
  have hξk : ∀ k, AEStronglyMeasurable[𝓕 (p k)] (ξ k) μ := fun k =>
    ⟨B.indicator ((hZk k).mk _),
      (hZk k).stronglyMeasurable_mk.indicator (𝓕.mono (hsp k) _ hB),
      (hZk k).ae_eq_mk.indicator⟩
  have hξm : ∀ k, AEStronglyMeasurable (ξ k) μ := fun k => (hξk k).mono (𝓕.le _)
  have hξi : ∀ k, Integrable (ξ k) μ := fun k =>
    Integrable.of_bound (hξm k) K0 (ae_of_all _ (hξn k))
  -- the endpoints
  have hend : ∫ ω in B, Complex.exp (((u * (M t ω - M s ω) : ℝ) : ℂ) * Complex.I +
      ((u ^ 2 / 2 * (A t ω - A s ω) : ℝ) : ℂ)) ∂μ = ∫ ω, ξ n ω ∂μ := by
    simp only [hξ]; rw [integral_indicator hBm]
    congr 1; ext ω; simp only [hZ, hy, ha, hpn]
  have hstart : (μ.real B : ℂ) = ∫ ω, ξ 0 ω ∂μ := by
    have h1 : ∀ ω, Z 0 ω = 1 := fun ω => by simp [hZ, hy, ha, hp0]
    simp only [hξ]; rw [integral_indicator hBm]
    simp [h1]
  rw [hend, hstart, ← sum_range_sub (fun k => ∫ ω, ξ k ω ∂μ) n]
  -- the remainders
  set e : ℝ := u ^ 2 / 2 * (c * Δ) with he
  set W : ℝ := |u| * (2 * R) + u ^ 2 / 2 * (c * (t - s)) with hW
  set D : Ω → ℝ := levyMaxIncr M s t m with hD
  set Q : Ω → ℝ := levyQV M s t m with hQ
  have hDd : ∀ ω k, k < n → |d k ω| ≤ D ω := fun ω k hk =>
    Finset.le_sup' (f := fun k => |d k ω|) (mem_range.2 hk)
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => (abs_nonneg _).trans (hDd ω 0 (by omega))
  have hD2R : ∀ ω, D ω ≤ 2 * R := fun ω => Finset.sup'_le _ _ fun k _ => hdb' ω k
  have hDm : AEStronglyMeasurable D μ :=
    levy_aestronglyMeasurable_sup' (f := fun k ω => |d k ω|) (fun k => by fun_prop) m
  have hDb : LevyBdd D := levyBdd_of_le fun ω => by rw [abs_of_nonneg (hD0 ω)]; exact hD2R ω
  have hQd : ∀ ω, Q ω = ∑ k ∈ range n, d k ω ^ 2 := fun ω => rfl
  have hQm : AEStronglyMeasurable Q μ := by
    have : Q = fun ω => ∑ k ∈ range n, d k ω ^ 2 := rfl
    rw [this]; fun_prop
  have hQb : LevyBdd Q := by
    have : Q = fun ω => ∑ k ∈ range n, d k ω ^ 2 := rfl
    rw [this]; fun_prop
  set g : ℕ → Ω → ℝ := fun k ω => |u| * D ω * (u ^ 2 / 2 * b k ω) + e ^ 2 / 2 +
    4 * Real.exp W * (|u| ^ 3 * (D ω * d k ω ^ 2) + e ^ 3) with hg
  have hgb : ∀ k, LevyBdd (g k) := fun k => by simp only [hg]; fun_prop
  have hgi : ∀ k, Integrable (g k) μ := fun k =>
    LevyBdd.integrable (hgb k) (by simp only [hg]; fun_prop)
  set ρ : ℕ → Ω → ℂ := fun k ω =>
    Complex.exp (((u * d k ω : ℝ) : ℂ) * Complex.I + ((u ^ 2 / 2 * b k ω : ℝ) : ℂ)) - 1 -
      ((u * d k ω : ℝ) : ℂ) * Complex.I - ((u ^ 2 / 2 * b k ω - (u * d k ω) ^ 2 / 2 : ℝ) : ℂ)
    with hρ
  have hρn : ∀ k ω, k < n → ‖ρ k ω‖ ≤ g k ω := fun k ω hk =>
    levy_rho_le u (d k ω) (u ^ 2 / 2 * b k ω) (D ω) W e
      (mul_nonneg (by positivity) (hbb' ω k).1)
      (mul_le_mul_of_nonneg_left (hbΔ ω k hk) (by positivity)) (hDd ω k hk)
      (add_le_add (mul_le_mul_of_nonneg_left (hdb' ω k) (abs_nonneg u))
        (mul_le_mul_of_nonneg_left (hbb' ω k).2 (by positivity)))
  -- one step
  have hstep : ∀ k < n, ‖∫ ω, ξ (k + 1) ω ∂μ - ∫ ω, ξ k ω ∂μ‖ ≤ ∫ ω, K0 * g k ω ∂μ := by
    intro k hk
    have e1 : ∀ ω, ξ (k + 1) ω - ξ k ω = ((u : ℂ) * Complex.I) * (ξ k ω * (d k ω : ℂ)) +
        ((-(u ^ 2 / 2) : ℝ) : ℂ) * (ξ k ω * ((d k ω ^ 2 - b k ω : ℝ) : ℂ)) + ξ k ω * ρ k ω := by
      intro ω
      by_cases hω : ω ∈ B
      · simp only [hξ, Set.indicator_of_mem hω]
        have hZs : Z (k + 1) ω = Z k ω *
            Complex.exp (((u * d k ω : ℝ) : ℂ) * Complex.I + ((u ^ 2 / 2 * b k ω : ℝ) : ℂ)) := by
          simp only [hZ]; rw [← Complex.exp_add]; congr 1
          simp only [hy, ha, hd, hb]; push_cast; ring
        rw [hZs]; simp only [hρ]; push_cast; ring
      · simp [hξ, Set.indicator_of_notMem hω]
    have i1 : Integrable (fun ω => ξ k ω * (d k ω : ℂ)) μ :=
      (LevyBdd.integrable (hdb k) (hdm k)).ofReal.bdd_mul (hξm k) (ae_of_all _ (hξn k))
    have i2 : Integrable (fun ω => ξ k ω * ((d k ω ^ 2 - b k ω : ℝ) : ℂ)) μ :=
      (LevyBdd.integrable (f := fun ω => d k ω ^ 2 - b k ω) (by fun_prop)
        (by fun_prop)).ofReal.bdd_mul (hξm k) (ae_of_all _ (hξn k))
    have hρm : AEStronglyMeasurable (ρ k) μ := by
      have := hdm k; have := hbm k; simp only [hρ]; fun_prop
    obtain ⟨C, hC⟩ := hgb k
    have hbound : ∀ ω, ‖ξ k ω * ρ k ω‖ ≤ K0 * g k ω := fun ω => by
      rw [norm_mul]
      exact mul_le_mul (hξn k ω) (hρn k ω hk) (norm_nonneg _) (Real.exp_pos _).le
    have i3 : Integrable (fun ω => ξ k ω * ρ k ω) μ :=
      Integrable.of_bound ((hξm k).mul hρm) (K0 * C) (ae_of_all _ fun ω => (hbound ω).trans
        (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC ω)) (Real.exp_pos _).le))
    have c1 : ∫ ω, ξ k ω * (d k ω : ℂ) ∂μ = 0 :=
      h.toIsCL2Mart.levy_integral_mul_incr_complex (hpm (Nat.le_succ k)) (hpT (k + 1)) (hξk k)
        (hξn k)
    have c2 : ∫ ω, ξ k ω * ((d k ω ^ 2 - b k ω : ℝ) : ℂ) ∂μ = 0 :=
      h.levy_integral_mul_incr_sq_complex (hpm (Nat.le_succ k)) (hpT (k + 1)) (hξk k) (hξn k)
    rw [← integral_sub (hξi _) (hξi _)]
    simp_rw [e1]
    have j1 := integral_add ((i1.const_mul ((u : ℂ) * Complex.I)).add
      (i2.const_mul ((-(u ^ 2 / 2) : ℝ) : ℂ))) i3
    have j2 := integral_add (i1.const_mul ((u : ℂ) * Complex.I))
      (i2.const_mul ((-(u ^ 2 / 2) : ℝ) : ℂ))
    simp only [Pi.add_apply] at j1 j2
    rw [j1, j2, integral_const_mul, integral_const_mul, c1, c2, mul_zero, mul_zero, zero_add,
      zero_add]
    exact norm_integral_le_of_norm_le ((hgi k).const_mul K0) (ae_of_all _ hbound)
  -- summing the steps
  set α₁ : ℝ := |u| * (u ^ 2 / 2 * (c * (t - s))) with hα₁
  set α₂ : ℝ := 2 * Real.exp W * |u| ^ 3 with hα₂
  set αm : ℝ := ((m : ℝ) + 1) * e ^ 2 / 2 + 4 * Real.exp W * (((m : ℝ) + 1) * e ^ 3) with hαm
  have hpt_sum : ∀ ω, ∑ k ∈ range n, K0 * g k ω ≤
      K0 * (α₁ * D ω + α₂ * l * D ω ^ 2 + α₂ / l * Q ω ^ 2 + αm) := by
    intro ω
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hsum : ∑ k ∈ range n, g k ω = (|u| * D ω * (u ^ 2 / 2)) * ∑ k ∈ range n, b k ω +
        (n : ℝ) * (e ^ 2 / 2) + ((4 * Real.exp W * |u| ^ 3 * D ω) * Q ω +
          (n : ℝ) * (4 * Real.exp W * e ^ 3)) := by
      rw [hQd, ← levy_sum_lin]
      exact sum_congr rfl fun k _ => by simp only [hg]; ring
    have hbsum : ∑ k ∈ range n, b k ω ≤ c * (t - s) := by
      have : ∑ k ∈ range n, b k ω = A t ω - A s ω := by
        simp only [hb]
        rw [sum_range_sub (fun k => A (p k) ω), hpn, hp0]
      rw [this]; exact (hA ω s t le_rfl hst le_rfl).2
    have hDQ : D ω * Q ω ≤ (l * D ω ^ 2 + Q ω ^ 2 / l) / 2 := by
      have h1 : (l * D ω ^ 2 + Q ω ^ 2 / l) / 2 - D ω * Q ω = (l * D ω - Q ω) ^ 2 / (2 * l) := by
        field_simp; ring
      have h2 : 0 ≤ (l * D ω - Q ω) ^ 2 / (2 * l) := by positivity
      linarith
    have hE : 0 ≤ 4 * Real.exp W * |u| ^ 3 := by positivity
    have h1 : (|u| * D ω * (u ^ 2 / 2)) * ∑ k ∈ range n, b k ω ≤ α₁ * D ω := by
      have : (|u| * D ω * (u ^ 2 / 2)) * ∑ k ∈ range n, b k ω ≤
          (|u| * D ω * (u ^ 2 / 2)) * (c * (t - s)) :=
        mul_le_mul_of_nonneg_left hbsum (by have := hD0 ω; positivity)
      exact this.trans_eq (by simp only [hα₁]; ring)
    have h2 : (4 * Real.exp W * |u| ^ 3 * D ω) * Q ω ≤ α₂ * l * D ω ^ 2 + α₂ / l * Q ω ^ 2 := by
      have := mul_le_mul_of_nonneg_left hDQ hE
      have e3 : α₂ * l * D ω ^ 2 + α₂ / l * Q ω ^ 2 =
          4 * Real.exp W * |u| ^ 3 * ((l * D ω ^ 2 + Q ω ^ 2 / l) / 2) := by
        simp only [hα₂]; field_simp; ring
      rw [e3]; linarith
    rw [hsum, hncast]
    simp only [hαm]
    linarith
  have hiD : Integrable D μ := LevyBdd.integrable hDb hDm
  have hiD2 : Integrable (fun ω => D ω ^ 2) μ := LevyBdd.integrable (by fun_prop) (by fun_prop)
  have hiQ2 : Integrable (fun ω => Q ω ^ 2) μ := LevyBdd.integrable (by fun_prop) (by fun_prop)
  have hiG : Integrable (fun ω => α₁ * D ω + α₂ * l * D ω ^ 2 + α₂ / l * Q ω ^ 2 + αm) μ :=
    (((hiD.const_mul _).add (hiD2.const_mul _)).add (hiQ2.const_mul _)).add (integrable_const _)
  have hiG' : ∫ ω, (α₁ * D ω + α₂ * l * D ω ^ 2 + α₂ / l * Q ω ^ 2 + αm) ∂μ =
      α₁ * ∫ ω, D ω ∂μ + α₂ * l * ∫ ω, D ω ^ 2 ∂μ + α₂ / l * ∫ ω, Q ω ^ 2 ∂μ + αm := by
    have j1 := integral_add (((hiD.const_mul α₁).add (hiD2.const_mul (α₂ * l))).add
      (hiQ2.const_mul (α₂ / l))) (integrable_const αm)
    have j2 := integral_add ((hiD.const_mul α₁).add (hiD2.const_mul (α₂ * l)))
      (hiQ2.const_mul (α₂ / l))
    have j3 := integral_add (hiD.const_mul α₁) (hiD2.const_mul (α₂ * l))
    simp only [Pi.add_apply] at j1 j2 j3
    rw [j1, j2, j3, integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
    simp
  calc ‖∑ k ∈ range n, (∫ ω, ξ (k + 1) ω ∂μ - ∫ ω, ξ k ω ∂μ)‖
      ≤ ∑ k ∈ range n, ‖∫ ω, ξ (k + 1) ω ∂μ - ∫ ω, ξ k ω ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range n, ∫ ω, K0 * g k ω ∂μ := sum_le_sum fun k hk => hstep k (mem_range.1 hk)
    _ = ∫ ω, ∑ k ∈ range n, K0 * g k ω ∂μ :=
        (integral_finsetSum _ fun k _ => (hgi k).const_mul K0).symm
    _ ≤ ∫ ω, K0 * (α₁ * D ω + α₂ * l * D ω ^ 2 + α₂ / l * Q ω ^ 2 + αm) ∂μ :=
        integral_mono (integrable_finsetSum _ fun k _ => (hgi k).const_mul K0)
          (hiG.const_mul K0) hpt_sum
    _ = _ := by rw [integral_const_mul, hiG']

omit [IsProbabilityMeasure μ] in
/-- Properties of the maximal increment: measurability, `0 ≤ D ≤ 2R`. -/
private lemma levy_maxIncr_props (hM : IsCL2Mart T 𝓕 M μ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : (t : ℝ) ≤ T) {R : ℝ} (hbd : ∀ ω (r : ℝ≥0), s ≤ r → r ≤ t → |M r ω - M s ω| ≤ R)
    (m : ℕ) :
    AEStronglyMeasurable (levyMaxIncr M s t m) μ ∧
      ∀ ω, 0 ≤ levyMaxIncr M s t m ω ∧ levyMaxIncr M s t m ω ≤ 2 * R := by
  set p := levyPt s t (m + 1)
  have hpT : ∀ k, (p k : ℝ) ≤ T := fun k =>
    (NNReal.coe_le_coe.2 (levyPt_le hst _ k)).trans htT
  have hd : ∀ k, AEStronglyMeasurable (fun ω => |M (p (k + 1)) ω - M (p k) ω|) μ := fun k =>
    (((hM.memLp _ (hpT (k + 1))).sub (hM.memLp _ (hpT k))).aestronglyMeasurable).norm
  refine ⟨levy_aestronglyMeasurable_sup' hd m, fun ω => ⟨?_, ?_⟩⟩
  · exact (abs_nonneg _).trans (Finset.le_sup' (f := fun k => |M (p (k + 1)) ω - M (p k) ω|)
      (mem_range.2 (Nat.succ_pos m)))
  · refine Finset.sup'_le _ _ fun k _ => ?_
    have h1 := hbd ω (p (k + 1)) (le_levyPt _ _ _ _) (levyPt_le hst _ _)
    have h2 := hbd ω (p k) (le_levyPt _ _ _ _) (levyPt_le hst _ _)
    calc |M (p (k + 1)) ω - M (p k) ω| =
        |(M (p (k + 1)) ω - M s ω) - (M (p k) ω - M s ω)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (by linarith)

/-- The maximal increment of a path continuous on `[s, t]` tends to `0` as the mesh of the
partition tends to `0` (uniform continuity). -/
private lemma levy_tendsto_maxIncr {s t : ℝ≥0} (hst : s ≤ t) {ω : Ω}
    (hc : ContinuousOn (fun r => M r ω) (Set.Icc (s : ℝ) t)) :
    Tendsto (fun m => levyMaxIncr M s t m ω) atTop (𝓝 0) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (((t : ℝ) - s) / δ)
  refine ⟨N, fun m hm => ?_⟩
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  have hmesh : ((t : ℝ) - s) / ((m : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hle : levyMaxIncr M s t m ω ≤ ε / 2 := by
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' : k < m + 1 := mem_range.1 hk
    have hmem : ∀ j, (levyPt s t (m + 1) j : ℝ) ∈ Set.Icc (s : ℝ) t := fun j =>
      ⟨NNReal.coe_le_coe.2 (le_levyPt _ _ _ _), NNReal.coe_le_coe.2 (levyPt_le hst _ _)⟩
    have hdist : dist (levyPt s t (m + 1) (k + 1) : ℝ) (levyPt s t (m + 1) k) < δ := by
      rw [Real.dist_eq, levyPt_succ_sub hst hk', abs_of_nonneg (div_nonneg (sub_nonneg.2 hst')
        (by positivity))]
      simpa using hmesh
    have := hδε _ (hmem (k + 1)) _ (hmem k) hdist
    rw [Real.dist_eq] at this
    exact this.le
  have h0 : 0 ≤ levyMaxIncr M s t m ω :=
    (abs_nonneg _).trans (Finset.le_sup' (f := fun k =>
      |M (levyPt s t (m + 1) (k + 1)) ω - M (levyPt s t (m + 1) k) ω|)
      (mem_range.2 (Nat.succ_pos m)))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- `C / (m + 1) → 0`. -/
private lemma levy_tendsto_div (C : ℝ) :
    Tendsto (fun m : ℕ => C / ((m : ℝ) + 1)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C

/-- **Lévy's characterization, bounded case.** Let `⟨M⟩ = A` on `[0, T]` and `s ≤ t ≤ T`.
Assume that for every `ω` the path of `M` is continuous on `[s, t]`, `|M_r - M_s| ≤ R` and
`0 ≤ A_{r'} - A_r ≤ c (r' - r)` for `s ≤ r ≤ r' ≤ t`. Then for `B ∈ 𝓕_s`,
`∫_B exp(i u (M_t - M_s) + u² (A_t - A_s) / 2) dℙ = ℙ(B)`. -/
theorem HasBracket.levy_setIntegral_bdd (h : HasBracket T 𝓕 M A μ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : (t : ℝ) ≤ T) {c R : ℝ} (hc : 0 ≤ c)
    (hcont : ∀ ω, ContinuousOn (fun r => M r ω) (Set.Icc (s : ℝ) t))
    (hbd : ∀ ω (r : ℝ≥0), s ≤ r → r ≤ t → |M r ω - M s ω| ≤ R)
    (hA : ∀ ω (r r' : ℝ≥0), s ≤ r → r ≤ r' → r' ≤ t →
      0 ≤ A r' ω - A r ω ∧ A r' ω - A r ω ≤ c * ((r' : ℝ) - r))
    (u : ℝ) {B : Set Ω} (hB : MeasurableSet[𝓕 s] B) :
    ∫ ω in B, Complex.exp (((u * (M t ω - M s ω) : ℝ) : ℂ) * Complex.I +
        ((u ^ 2 / 2 * (A t ω - A s ω) : ℝ) : ℂ)) ∂μ = μ.real B := by
  set L := ‖∫ ω in B, Complex.exp (((u * (M t ω - M s ω) : ℝ) : ℂ) * Complex.I +
        ((u ^ 2 / 2 * (A t ω - A s ω) : ℝ) : ℂ)) ∂μ - (μ.real B : ℂ)‖ with hL
  set K0 := Real.exp (u ^ 2 / 2 * (c * (t - s)))
  set W := Real.exp (|u| * (2 * R) + u ^ 2 / 2 * (c * (t - s)))
  set γ := u ^ 2 / 2 * (c * ((t : ℝ) - s)) with hγ
  -- `𝔼 D_m → 0` and `𝔼 D_m² → 0`
  have hprops := levy_maxIncr_props h.toIsCL2Mart hst htT hbd
  have hlimD : Tendsto (fun m => ∫ ω, levyMaxIncr M s t m ω ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun _ => 2 * R)
      (fun m => (hprops m).1) (integrable_const _)
      (fun m => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((hprops m).2 ω).1]; exact ((hprops m).2 ω).2)
      (ae_of_all _ fun ω => levy_tendsto_maxIncr hst (hcont ω))
    simpa using this
  have hlimD2 : Tendsto (fun m => ∫ ω, levyMaxIncr M s t m ω ^ 2 ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun _ => (2 * R) ^ 2)
      (fun m => (hprops m).1.pow 2) (integrable_const _)
      (fun m => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ ((hprops m).2 ω).1 ((hprops m).2 ω).2 2)
      (ae_of_all _ fun ω => by simpa using (levy_tendsto_maxIncr hst (hcont ω)).pow 2)
    simpa using this
  -- `𝔼 Q_m² ≤ 6 R⁴`
  have hQ2 : ∀ m, ∫ ω, levyQV M s t m ω ^ 2 ∂μ ≤ 6 * R ^ 4 := fun m => by
    have hpT : ∀ k, (levyPt s t (m + 1) k : ℝ) ≤ T := fun k =>
      (NNReal.coe_le_coe.2 (levyPt_le hst _ k)).trans htT
    refine h.toIsCL2Mart.levy_integral_qv_sq_le (levyPt_mono s t (m + 1)) hpT
      (fun ω k => ?_) (m + 1)
    rw [levyPt_zero]
    exact hbd ω _ (le_levyPt _ _ _ _) (levyPt_le hst _ _)
  -- for every `λ > 0`, `L ≤ K₀ · 2 e^W |u|³ · 6 R⁴ / λ`
  have hlam : ∀ l : ℝ, 0 < l → L ≤ K0 * (2 * W * |u| ^ 3 / l * (6 * R ^ 4)) := by
    intro l hl
    have hbound : ∀ m, L ≤ K0 * (|u| * γ * ∫ ω, levyMaxIncr M s t m ω ∂μ +
        2 * W * |u| ^ 3 * l * ∫ ω, levyMaxIncr M s t m ω ^ 2 ∂μ +
        2 * W * |u| ^ 3 / l * (6 * R ^ 4) +
        (γ ^ 2 / 2 * (1 / ((m : ℝ) + 1)) + 4 * W * (γ ^ 3 * (1 / ((m : ℝ) + 1)) ^ 2))) := by
      intro m
      refine (levy_estimate h hst htT hc hbd hA u hB m hl).trans ?_
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have e1 : ((m : ℝ) + 1) * (u ^ 2 / 2 * (c * ((t - s) / ((m : ℝ) + 1)))) ^ 2 / 2 =
          γ ^ 2 / 2 * (1 / ((m : ℝ) + 1)) := by rw [hγ]; field_simp
      have e2 : ((m : ℝ) + 1) * (u ^ 2 / 2 * (c * ((t - s) / ((m : ℝ) + 1)))) ^ 3 =
          γ ^ 3 * (1 / ((m : ℝ) + 1)) ^ 2 := by rw [hγ]; field_simp
      rw [e1, e2]
      have : 2 * W * |u| ^ 3 / l * ∫ ω, levyQV M s t m ω ^ 2 ∂μ ≤
          2 * W * |u| ^ 3 / l * (6 * R ^ 4) :=
        mul_le_mul_of_nonneg_left (hQ2 m) (by positivity)
      gcongr
    have hlim : Tendsto (fun m : ℕ => K0 * (|u| * γ * ∫ ω, levyMaxIncr M s t m ω ∂μ +
        2 * W * |u| ^ 3 * l * ∫ ω, levyMaxIncr M s t m ω ^ 2 ∂μ +
        2 * W * |u| ^ 3 / l * (6 * R ^ 4) +
        (γ ^ 2 / 2 * (1 / ((m : ℝ) + 1)) + 4 * W * (γ ^ 3 * (1 / ((m : ℝ) + 1)) ^ 2))))
        atTop (𝓝 (K0 * (2 * W * |u| ^ 3 / l * (6 * R ^ 4)))) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((((hlimD.const_mul (|u| * γ)).add (hlimD2.const_mul (2 * W * |u| ^ 3 * l))).add
        (tendsto_const_nhds (x := 2 * W * |u| ^ 3 / l * (6 * R ^ 4)))).add
        ((h1.const_mul (γ ^ 2 / 2)).add ((((h1.pow 2).const_mul (γ ^ 3)).const_mul (4 * W))))
        ).const_mul K0
      simpa using this
    exact ge_of_tendsto' hlim hbound
  -- hence `L = 0`
  have hL0 : L ≤ 0 := by
    refine ge_of_tendsto' ((levy_tendsto_div (K0 * (2 * W * |u| ^ 3 * (6 * R ^ 4)))))
      fun k => ?_
    have := hlam ((k : ℝ) + 1) (by positivity)
    calc L ≤ _ := this
      _ = _ := by ring
  have : L = 0 := le_antisymm hL0 (norm_nonneg _)
  rw [hL, norm_eq_zero, sub_eq_zero] at this
  exact this

end QSSEPtoKPZ
