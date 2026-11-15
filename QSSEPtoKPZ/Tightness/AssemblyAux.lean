/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.Tightness.ExpMoments
public import QSSEPtoKPZ.Tightness.AldousCondition
public import QSSEPtoKPZ.Tightness.Version
public import QSSEPtoKPZ.Tightness.CompactSets
public import QSSEPtoKPZ.Tightness.PathCompact
public import QSSEPtoKPZ.Martingales.Aldous

/-!
# Proposition 5.1, tightness: auxiliary results (task Q4)

* `tightAsm_lintegral_cosh`: `∫ cosh d𝖹_n(t) = 𝖹_n(t;cosh)` (integral in `[0, ∞]`) when the
  series `∑ₓ 𝔷_n(t,x) e^{±y_n(t,x)}` converge.
* `tightAsm_abs_integral_le`: `|∫ f_j dν| ≤ M` for `ν` in the `cosh`-ball `{∫ cosh dν ≤ M}`
  (since `|f_j| ≤ 1 ≤ cosh`).
* `tightAsmBound c C η s = c (C s / η + C² √s / η²)`, the bound of (5.2), and
  `tightAsm_choose`: the choice of the two scales `δ ≤ δ₁` and of `N ≥ 2T/δ₁` in Aldous'
  criterion making `6 a(δ₁) + 3 N a(δ)` small (deterministic, uniform in the realization).
* `tightAsmX`: the real process `X_t = ∫ f_j dZ'(ω)(t ∧ (T+2))` built from a version `Z'` of
  `(𝖹_n(t))_{t ∈ [0,T+2]}`; `tightAsm_modulus`: Aldous' criterion (`aldous_modulus`) applied to
  `X`, with the bound (5.2) (`aldous_condition` on the horizon `T + 1`) transferred from
  `𝖹_n(·;f_j)` to `X` (equal at all times almost surely).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-! ### Compact containment -/

/-- `∫ cosh d𝖹_n(t) = 𝖹_n(t;cosh) = ∑ₓ 𝔷_n(t,x) cosh(y_n(t,x))` (lower integral, in `[0, ∞]`),
when the series `∑ₓ 𝔷_n(t,x) e^{± y_n(t,x)}` converge. -/
theorem tightAsm_lintegral_cosh {n t : ℝ} {ω : Ω}
    (h1 : Summable fun x => zN n ψ ω t x * Real.exp (1 * rescaledPosition n t x))
    (h2 : Summable fun x => zN n ψ ω t x * Real.exp (-1 * rescaledPosition n t x)) :
    ∫⁻ y, ENNReal.ofReal (Real.cosh y) ∂(tiltedMeasure n ψ ω t) =
      ENNReal.ofReal (pairZ n ψ ω t Real.cosh) := by
  have hz : ∀ x, 0 ≤ zN n ψ ω t x := fun x => tiltZ_nonneg n ω t x
  have hs : Summable fun x => zN n ψ ω t x * Real.cosh (rescaledPosition n t x) := by
    refine ((h1.add h2).div_const 2).congr fun x => ?_
    rw [Real.cosh_eq]
    simp only [one_mul, neg_one_mul]
    ring
  rw [tiltedMeasure, lintegral_sum_measure, pairZ,
    ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (hz x) (Real.cosh_pos _).le) hs]
  congr 1
  funext x
  rw [lintegral_smul_measure, lintegral_dirac, ENNReal.ofReal_mul (hz x), smul_eq_mul]

/-- On the `cosh`-ball `{ν : ∫ cosh dν ≤ M}`, `|∫ f_j dν| ≤ ν(ℝ) ≤ M` (as `|f_j| ≤ 1 ≤ cosh`). -/
theorem tightAsm_abs_integral_le {M : ℝ} (hM : 0 ≤ M) {ν : FiniteMeasure ℝ}
    (hν : ν ∈ tightCoshBall (ENNReal.ofReal M)) (j : ℕ) :
    |∫ x, bumpTest j x ∂(ν : Measure ℝ)| ≤ M := by
  have hmass : (ν : Measure ℝ) univ ≤ ENNReal.ofReal M := by
    refine le_trans ?_ hν
    rw [← lintegral_one]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_cosh x)
  have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure ℝ)) (C := 1)
    (f := fun x => bumpTest j x) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, coe_bumpTest]; exact abs_bumpTestRaw_le j x)
  rw [Real.norm_eq_abs, one_mul] at h
  exact h.trans (ENNReal.toReal_le_of_le_ofReal hM hmass)

/-! ### The choice of the scales in Aldous' criterion -/

/-- The bound of (5.2): `c (C s / η + C² √s / η²)`. -/
def tightAsmBound (c C η s : ℝ) : ℝ := c * (C * s / η + C ^ 2 * Real.sqrt s / η ^ 2)

private lemma tightAsmBound_nonneg {c C η s : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hη : 0 < η)
    (hs : 0 ≤ s) : 0 ≤ tightAsmBound c C η s := by
  unfold tightAsmBound; positivity

/-- The bound of (5.2) is nondecreasing in `s`. -/
theorem tightAsmBound_mono {c C η s s' : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hη : 0 < η)
    (hss : s ≤ s') : tightAsmBound c C η s ≤ tightAsmBound c C η s' := by
  unfold tightAsmBound
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hss hC) hη.le
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hss) (sq_nonneg C)) (sq_nonneg η)

/-- The bound of (5.2) tends to `0` with `s`. -/
private lemma tightAsmBound_small {c C η e : ℝ} (he : 0 < e) :
    ∃ r > 0, ∀ s, 0 ≤ s → s ≤ r → tightAsmBound c C η s ≤ e := by
  have hcont : Continuous fun s => tightAsmBound c C η s := by
    unfold tightAsmBound; fun_prop
  obtain ⟨d, hd, hd'⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) e he
  refine ⟨d / 2, by positivity, fun s hs hsr => ?_⟩
  have h := hd' (x := s) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs]; linarith)
  have h0 : tightAsmBound c C η 0 = 0 := by simp [tightAsmBound]
  rw [Real.dist_eq, h0, sub_zero] at h
  exact (le_abs_self _).trans h.le

/-- **Choice of the scales** in Aldous' criterion: for `a(δ) = c (C 2δ / η + C² √(2δ) / η²)`
there are `0 < δ ≤ δ₁ ≤ 1/32` and `N` with `2T ≤ N δ₁` and `6 a(δ₁) + 3 N a(δ) ≤ e`. -/
theorem tightAsm_choose (T c C η : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ δ δ₁ : ℝ, ∃ N : ℕ, 0 < δ ∧ δ ≤ δ₁ ∧ δ₁ ≤ 1 / 32 ∧ 2 * T ≤ N * δ₁ ∧
      6 * tightAsmBound c C η (2 * δ₁) + 3 * N * tightAsmBound c C η (2 * δ) ≤ e := by
  obtain ⟨r₁, hr₁, h₁⟩ := tightAsmBound_small (c := c) (C := C) (η := η) (e := e / 12)
    (by positivity)
  set δ₁ : ℝ := min (1 / 32) (r₁ / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by norm_num) (by positivity)
  set N : ℕ := ⌈2 * T / δ₁⌉₊ with hN
  have hN' : 2 * T ≤ N * δ₁ := (div_le_iff₀ hδ₁0).1 (Nat.le_ceil _)
  obtain ⟨r₂, hr₂, h₂⟩ := tightAsmBound_small (c := c) (C := C) (η := η)
    (e := e / (6 * (N + 1))) (by positivity)
  set δ : ℝ := min δ₁ (r₂ / 2) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁0 (by positivity)
  refine ⟨δ, δ₁, N, hδ0, min_le_left _ _, min_le_left _ _, hN', ?_⟩
  have e1 := h₁ (2 * δ₁) (by positivity) (by linarith [min_le_right (1 / 32 : ℝ) (r₁ / 2)])
  have e2 := h₂ (2 * δ) (by positivity) (by linarith [min_le_right δ₁ (r₂ / 2)])
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have e3 : 3 * N * tightAsmBound c C η (2 * δ) ≤ 3 * N * (e / (6 * (N + 1))) :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  have e4 : 3 * N * (e / (6 * (N + 1))) ≤ e / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-! ### Aldous' criterion for the test paths -/

/-- The real process `X_t = ∫ f_j dZ'(ω)(t)` for `t ∈ [0, T+2]`, extended constantly outside
(`Set.IccExtend`), built from a path `Z'(ω) ∈ C([0,T+2], ℳ₊(ℝ))`. -/
def tightAsmX {T : ℝ} (hT : 0 ≤ T) (Zv' : Ω → C(Icc (0 : ℝ) (T + 2), FiniteMeasure ℝ)) (j : ℕ)
    (t : ℝ) (ω : Ω) : ℝ :=
  IccExtend (by linarith : (0 : ℝ) ≤ T + 2) (pathCptTest j (Zv' ω)) t

/-- `X_t = ∫ f_j dZ'(ω)(t)` for `t ∈ [0, T+2]`. -/
theorem tightAsmX_of_mem {T : ℝ} (hT : 0 ≤ T) (Zv' : Ω → C(Icc (0 : ℝ) (T + 2), FiniteMeasure ℝ))
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T + 2)) (ω : Ω) :
    tightAsmX hT Zv' j t ω = ∫ x, bumpTest j x ∂(Zv' ω ⟨t, ht⟩ : Measure ℝ) := by
  rw [tightAsmX, IccExtend_of_mem _ _ ht, pathCptTest_apply]

/-- **Aldous' criterion for the test path `𝖹_n(·;f_j)`.** Let `Z'` be a version of
`(𝖹_n(t))_{t ∈ [0,T+2]}` with all paths continuous and test integrals adapted to `𝓕ⁿ`
augmented by the null sets, `c ≥ 0` a constant for which (5.2) holds on the horizon `T + 1`, and
`‖f_j‖_{1,3} ≤ C`. For `η > 0`, `0 < δ ≤ δ₁ ≤ 1/32` and `2T ≤ N δ₁`, with
`a(δ) = c (C 2δ / (η/4) + C² √(2δ) / (η/4)²)`:
`ℙ(∃ s, t ∈ [0,T], |t - s| ≤ δ, |X_t - X_s| ≥ 3η) ≤ 6 a(δ₁) + 3 N a(δ)`. -/
theorem tightAsm_modulus [IsProbabilityMeasure μ] {n : ℝ} {T : ℝ} (hT : 0 ≤ T)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ {C : ℝ} {φ : ℝ → ℝ}, IsC13 1 (fun _ => φ) (fun _ _ => 0) C →
      ∀ {τ : Ω → ℝ≥0}, IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)) →
      (∀ ω, (τ ω : ℝ) ≤ T + 1) → ∀ {s η : ℝ}, 0 ≤ s → s ≤ 1 / 16 → 0 < η →
      μ {ω | η < |pairZ n ψ ω ((τ ω : ℝ) + s) φ - pairZ n ψ ω (τ ω) φ|} ≤
        ENNReal.ofReal (c * (C * s / η + C ^ 2 * Real.sqrt s / η ^ 2)))
    (Zv' : Ω → C(Icc (0 : ℝ) (T + 2), FiniteMeasure ℝ))
    (hZa : ∀ (t : Icc (0 : ℝ) (T + 2)) (j : ℕ), Measurable[nullAug μ (filtN n 𝓕) (t : ℝ).toNNReal]
        fun ω => ∫ x, bumpTest j x ∂(Zv' ω t : Measure ℝ))
    (hZe : ∀ᵐ ω ∂μ, ∀ t : Icc (0 : ℝ) (T + 2), (Zv' ω t : Measure ℝ) = tiltedMeasure n ψ ω t)
    (hsum : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t))
    {j : ℕ} {C : ℝ} (hC0 : 0 ≤ C) (hCj : IsC13 1 (fun _ => bumpTestRaw j) (fun _ _ => 0) C)
    {η δ δ₁ : ℝ} {N : ℕ} (hη : 0 < η) (hδ : 0 < δ) (hδδ₁ : δ ≤ δ₁) (hδ₁ : δ₁ ≤ 1 / 32)
    (hN : 2 * T ≤ N * δ₁) :
    μ {ω | ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) T, |t - s| ≤ δ ∧
      3 * η ≤ |tightAsmX hT Zv' j t ω - tightAsmX hT Zv' j s ω|} ≤
      ENNReal.ofReal (6 * tightAsmBound c C (η / 4) (2 * δ₁) +
        3 * N * tightAsmBound c C (η / 4) (2 * δ)) := by
  set 𝓖 := nullAug μ (filtN n 𝓕)
  set X := tightAsmX hT Zv' j
  have hT2 : (0 : ℝ) ≤ T + 2 := by linarith
  -- continuity and adaptedness of `X`
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω := fun ω =>
    ((pathCptTest j (Zv' ω)).continuous.Icc_extend' (h := hT2)).comp NNReal.continuous_coe
  have hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t) := by
    intro t
    set p := projIcc (0 : ℝ) (T + 2) hT2 t with hp
    have e : X t = fun ω => ∫ x, bumpTest j x ∂(Zv' ω p : Measure ℝ) := by
      funext ω
      simp only [X, tightAsmX, IccExtend_apply, pathCptTest_apply, hp]
      rfl
    rw [e]
    refine (hZa p j).mono (𝓖.mono ?_) le_rfl
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ p.2.1, hp, coe_projIcc]
    exact max_le (NNReal.coe_nonneg t) (min_le_right _ _)
  -- `X_u = 𝖹_n(u; f_j)` for `u ∈ [0, T+2]`, almost surely
  have hXeq : ∀ᵐ ω ∂μ, ∀ u ∈ Icc (0 : ℝ) (T + 2),
      X u ω = pairZ n ψ ω u (bumpTestRaw j) := by
    filter_upwards [hZe, hsum] with ω h1 h2 u hu
    simp only [X]
    rw [tightAsmX_of_mem hT Zv' j hu, h1 ⟨u, hu⟩]
    exact tiltVer_integral (h2 u hu.1) (bumpTest j)
  -- the hypotheses of `aldous_modulus`, from (5.2)
  have hA : ∀ d : ℝ, 0 < d → d ≤ 1 / 32 → ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) → (∀ ω, (ρ ω : ℝ) ≤ T + 1) →
      ∀ s ∈ Icc (0 : ℝ) (2 * d), μ {ω | η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤
        ENNReal.ofReal (tightAsmBound c C (η / 4) (2 * d)) := by
    intro d hd hd' ρ hρ hρT s hs
    have hs16 : s ≤ 1 / 16 := by linarith [hs.2]
    refine (measure_mono_ae ?_).trans ((hc hCj hρ hρT hs.1 hs16 (by positivity)).trans
      (ENNReal.ofReal_le_ofReal (tightAsmBound_mono hc0 hC0 (by positivity) hs.2)))
    filter_upwards [hXeq] with ω hω hmem
    have hρ0 : (0 : ℝ) ≤ ρ ω := NNReal.coe_nonneg _
    have hmem' : η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω| := hmem
    rw [hω _ ⟨by linarith [hs.1], by linarith [hρT ω]⟩,
      hω _ ⟨hρ0, by linarith [hρT ω]⟩] at hmem'
    show η / 4 < |pairZ n ψ ω ((ρ ω : ℝ) + s) (bumpTestRaw j) -
      pairZ n ψ ω (ρ ω) (bumpTestRaw j)|
    linarith
  exact aldous_modulus (μ := μ) (𝓖 := 𝓖) hXc hXa hT hη hδ hδδ₁ (by linarith)
    hN (tightAsmBound_nonneg hc0 hC0 (by positivity) (by linarith))
    (tightAsmBound_nonneg hc0 hC0 (by positivity) (by linarith))
    (hA δ₁ (hδ.trans_le hδδ₁) hδ₁) (hA δ hδ (hδδ₁.trans hδ₁))

end QSSEPtoKPZ
