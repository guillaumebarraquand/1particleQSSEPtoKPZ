/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorDefs
public import QSSEPtoKPZ.Replacement.Corrector
public import QSSEPtoKPZ.Replacement.SmoothedSum
public import QSSEPtoKPZ.Replacement.KappaRiemann
public import QSSEPtoKPZ.TiltedField.Martingales
public import QSSEPtoKPZ.SecondMoments.TotalMass
public import QSSEPtoKPZ.Martingales.Doob
public import QSSEPtoKPZ.Martingales.Stopping

/-!
# The convergence `b_m → 1` and Proposition 6.2 (the replacement lemma)

Statements: Stage 2, task T0; proofs: task G3.

The proof of Proposition 6.2 follows the article. For `ε ∈ (0,1)` and `n ≥ ε^{-2}`, let
`m = ⌊ε n^{1/2}⌋ ≥ 1` and `ε_n = m n^{-1/2}`. For `K ≥ 1` let `τ_K` be the first time `𝒲_n` reaches
`K`, capped at `T` (a stopping time of the augmented filtration, through a continuous adapted
version of `𝒲_n`). Then, by Lemma 6.4, on `{sup_{[0,T]} 𝒲_n < K}`, for `t ∈ [0,T]`,
`∫_0^t (ℰ_n - ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²) ds = 𝖥_n(t) - 𝖥_n(0) - N_n(t ∧ τ_K) - ∫_0^t 𝖱_n
  + ∫_0^t (𝖡_n(s;φ_s) - ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²) ds`,
and the four terms other than `N_n` are bounded by deterministic quantities times `K²`, which
are small for `ε` small and then `n` large (using (6.11), (6.1), `b_m → 1` and the continuity of
`ε ↦ κ_ε`). By Doob's inequality and (6.15),
`𝔼[sup_{t ≤ T} N_n(t ∧ τ_K)²] ≤ 4 𝔼[⟨N_n⟩_{τ_K}] ≤ 4 K' (m²/n + n^{-1/2}) C⁴ K² 𝔼[⟨𝒲_n⟩_T]`,
with `𝔼[⟨𝒲_n⟩_T] ≤ 2 · 2^{1+16T}` by (4.8), and `ℙ(sup_{[0,T]} 𝒲_n ≥ K) ≤ 1/K` by Doob's maximal
inequality. (The article bounds `𝔼[⟨𝒲_n⟩_{τ_K}]` by `K²`; bounding it by `𝔼[⟨𝒲_n⟩_T]` gives a
`K²` instead of `K⁴` in front of `ε²`, which changes nothing.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- **`b_m → 1`** (Section 6.1, sentence before (6.6)): `b_m` converges to `∫ κ = 1` as the integer
`m` tends to infinity. -/
theorem tendsto_bM {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) : Tendsto (bM ρ) atTop (𝓝 1) := by
  have hlim := (kappa_riemann_tendsto hρ).add
    ((tendsto_const_nhds (x := kappa ρ 0)).div_atTop tendsto_natCast_atTop_atTop)
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hs1 : Summable fun r : ℤ => kappa ρ (r / m) :=
    summable_of_eq_zero_of_le_abs (2 * m) fun r hr => hρ.kappa_div_eq_zero hm hr
  have hs2 : Summable fun r : ℤ => if r = 0 then kappa ρ 0 else 0 := (hasSum_ite_eq 0 _).summable
  have e : ∀ r : ℤ, chainPi r * kappa ρ (r / m) =
      kappa ρ (r / m) + if r = 0 then kappa ρ 0 else 0 := by
    intro r
    unfold chainPi
    by_cases h : r = 0
    · simp [h]; ring
    · simp [h]
  unfold bM
  simp only [e]
  rw [hs1.tsum_add hs2, tsum_ite_eq]
  ring

/-! ### Auxiliary facts -/

/-- `ℰ_n(t;1) ≥ 0`. -/
private lemma EN_one_nonneg {n : ℝ} (hn : 0 ≤ n) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) :
    0 ≤ EN n ψ ω t fun _ => 1 :=
  mul_nonneg (Real.rpow_nonneg hn _) (tsum_nonneg fun x => by
    simp only [mul_one]; exact mul_nonneg (replZN_nonneg _ _ _ _ _) (replZN_nonneg _ _ _ _ _))

/-- `a w² ⋯ ≤ a' k² ⋯` from `a ≤ a'`, `0 ≤ w ≤ k` and nonnegative factors. -/
private lemma prop62_mul_le {a a' b c w k : ℝ} (ha : a ≤ a') (ha' : 0 ≤ a') (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hwk : w ≤ k) : a * b * c * w ^ 2 ≤ a' * b * c * k ^ 2 :=
  calc a * b * c * w ^ 2 = a * (b * c * w ^ 2) := by ring
    _ ≤ a' * (b * c * w ^ 2) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = a' * b * c * w ^ 2 := by ring
    _ ≤ a' * b * c * k ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw hwk 2) (by positivity)

/-- `C ≥ 0` when `‖φ‖_{1,3} ≤ C` and `T ≥ 0`. -/
private lemma IsC13.const_nonneg {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    (hT : 0 ≤ T) : 0 ≤ C :=
  (abs_nonneg _).trans (hφ.replAbs_le (t := 0) ⟨le_rfl, hT⟩ 0)

/-- First item of Proposition 6.2: summability and integrability. -/
private lemma prop62_integrable (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T C : ℝ} (hT : 0 < T) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) {n : ℝ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => EN n ψ ω s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) volume 0 T := by
  obtain ⟨h31, -⟩ := prop_3_1 hB hψ hn hT hφ
  obtain ⟨-, hW, -⟩ := hasBracket_WN hB hψ hn hT
  filter_upwards [h31, hW.cont, hψ.continuous] with ω h1 h2 h3
  exact ⟨h1.1, h1.2.2.2.1, intervalIntegrable_smoothedNormSq_tilted hρ hT.le hφ
    (by linarith) hε h3 h1.1 h2⟩

/-- **Main estimate of the proof of Proposition 6.2.** There is `K' ≥ 0` (the constant of
Lemma 6.4) such that, for fixed `n ≥ 1`, `m ≥ 1`, `ε > 0`, a level `K ≥ 1` and `η > 0`: if
`|κ_{ε_n}/b_m - κ_ε| ≤ Δ` (with `ε_n = m n^{-1/2}`) and the deterministic bound
`2 (m/n^{1/2}) C² K² + T K' (m/n^{1/2} + n^{-1/4} + 1/m) C² K² + T Δ C² K² ≤ η/2` holds, then
`ℙ(∃ t ≤ T, |∫_0^t (ℰ_n - ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²) ds| > η)
  ≤ 1/K + 16 K' (m²/n + n^{-1/2}) C⁴ K² 2^{2+16T} / η²`. -/
private lemma prop62_main (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T C : ℝ} (hT : 0 < T) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) :
    ∃ Kρ : ℝ, 0 ≤ Kρ ∧ ∀ {n : ℝ} {m : ℕ} {ε Δ K η : ℝ}, 1 ≤ n → 1 ≤ m → 0 < ε → 1 ≤ K → 0 < η →
    (∀ x, |kappaEps ρ (m * n ^ (-1 / 2 : ℝ)) x / bM ρ m - kappaEps ρ ε x| ≤ Δ) →
    2 * (m / n ^ (1 / 2 : ℝ)) * C ^ 2 * K ^ 2 +
      T * (Kρ * (m / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m) * C ^ 2 * K ^ 2) +
      T * (Δ * C ^ 2 * K ^ 2) ≤ η / 2 →
    μ {ω | ∃ t ∈ Set.Icc 0 T, η < |∫ s in (0 : ℝ)..t,
        (EN n ψ ω s (φ s) - smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε)|} ≤
      ENNReal.ofReal (1 / K) + ENNReal.ofReal (16 * (Kρ *
        (m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * K ^ 2 * 2 ^ (2 + 16 * T)) / η ^ 2) := by
  obtain ⟨K0, hK0spec⟩ := lemma_6_4 hρ
  refine ⟨max K0 0, le_max_right _ _, fun {n m ε Δ K η} hn hm hε hK hη hΔ hdet => ?_⟩
  set Kρ := max K0 0 with hKρdef
  have hK0le : K0 ≤ Kρ := le_max_left _ _
  have hKρ0 : 0 ≤ Kρ := le_max_right _ _
  obtain ⟨R, q, -, -, hI, hBd, hN, -⟩ := hK0spec hB hψ hn hm hT hφ
  obtain ⟨-, hW, hW0⟩ := hasBracket_WN hB hψ hn hT
  obtain ⟨-, -, -, hEint, hEbound⟩ := prop_4_3_bounds hB hψ hn hT.le
  have hS := prop62_integrable hB hψ hρ hT hφ hn hε
  have hn0 : 0 < n := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hC : 0 ≤ C := hφ.const_nonneg hT.le
  have hK0 : 0 < K := by linarith
  obtain ⟨-, -, haN1, haN2, hcN1, hcosh⟩ := constants_bounds hn
  have haN : aN n ≤ 2 := by linarith
  set T' : ℝ≥0 := T.toNNReal with hT'def
  have hT' : (T' : ℝ) = T := Real.coe_toNNReal _ hT.le
  set 𝓖 := filtN n 𝓕 with h𝓖
  -- the processes `N_n` and `⟨N_n⟩`
  set NP : ℝ → Ω → ℝ := fun t ω => FN n ψ ρ m φ t ω - FN n ψ ρ m φ 0 ω - ∫ s in (0 : ℝ)..t,
    (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω + R s ω) with hNP
  set AP : ℝ → Ω → ℝ := fun t ω => ∫ s in (0 : ℝ)..t, q s ω with hAP
  -- a continuous adapted version of `𝒲_n` and the hitting time `τ_K`
  obtain ⟨W', hW'm, hW'c, hW'eq⟩ := exists_adapted_continuous_version (𝓕 := 𝓖) (μ := μ)
    hT.le hW.cont fun t ht => aestronglyMeasurable_of_condExp_eq_self (hW.condExp t t le_rfl ht)
  set X : ℝ → Ω → ℝ := fun t ω => W' t.toNNReal ω with hX
  have hXm : ∀ t : ℝ≥0, Measurable[nullAug μ 𝓖 t] (X t) := fun t => by
    simp only [X, Real.toNNReal_coe]; exact (hW'm t).measurable
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω := fun ω => by
    simp only [X, Real.toNNReal_coe]; exact hW'c ω
  set τ : Ω → ℝ≥0 := hitTime X K T' with hτdef
  have hτ : IsStoppingTime (nullAug μ 𝓖) (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_hitTime hXm hXc K T'
  have hτT : ∀ ω, (τ ω : ℝ) ≤ T := fun ω => hT' ▸ NNReal.coe_le_coe.2 (hitTime_le X K T' ω)
  set Nτ : ℝ → Ω → ℝ := fun t ω => NP (min t (τ ω)) ω with hNτdef
  set Aτ : ℝ → Ω → ℝ := fun t ω => AP (min t (τ ω)) ω with hAτdef
  have hNτ : HasBracket T 𝓖 Nτ Aτ μ := hN.stopped hτ hτT
  -- `𝒲_n ≤ K` up to `τ_K`
  have hWτ : ∀ᵐ ω ∂μ, ∀ s : ℝ, 0 ≤ s → s ≤ τ ω → WN n ψ s ω ≤ K := by
    filter_upwards [hW'eq, hW0] with ω h1 h2 s hs0 hsτ
    have hX0 : X 0 ω ≤ K := by
      simp only [X, Real.toNNReal_zero]
      rw [h1 0 (by simp; exact hT.le)]
      simp only [NNReal.coe_zero, h2]; exact hK
    have hle := le_of_le_hitTime (hXc ω) hX0 (t := s.toNNReal)
      (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hsτ)
    simp only [X, Real.toNNReal_coe] at hle
    rw [h1 s.toNNReal (by rw [Real.coe_toNNReal _ hs0]; exact hsτ.trans (hτT ω)),
      Real.coe_toNNReal _ hs0] at hle
    exact hle
  -- `𝔼[N_n(T ∧ τ_K)²] = 𝔼[⟨N_n⟩_{T ∧ τ_K}]`
  have hint2 : Integrable (fun ω => Nτ T ω ^ 2) μ := by
    have := (hNτ.memLp T' hT'.le).integrable_sq; rwa [hT'] at this
  have hintA : Integrable (Aτ T) μ := by
    have := hNτ.integrable_bracket T' hT'.le; rwa [hT'] at this
  have hEq : ∫ ω, Nτ T ω ^ 2 ∂μ = ∫ ω, Aτ T ω ∂μ := by
    have hcs := hNτ.condExp_sq 0 T' zero_le hT'.le
    rw [hT'] at hcs
    have h0 : ∫ ω, (Nτ T ω ^ 2 - Aτ T ω) ∂μ = 0 := by
      rw [← integral_condExp (𝓖.le 0), integral_congr_ae hcs]
      have e : ∀ ω, Nτ ((0 : ℝ≥0) : ℝ) ω ^ 2 - Aτ ((0 : ℝ≥0) : ℝ) ω = 0 := fun ω => by
        simp only [Nτ, Aτ, NP, AP, NNReal.coe_zero, min_eq_left (NNReal.coe_nonneg (τ ω)),
          intervalIntegral.integral_same]
        ring
      simp only [e, integral_zero]
    rw [integral_sub hint2 hintA] at h0
    linarith
  -- bound on `⟨N_n⟩_{T ∧ τ_K}`
  set c' := Kρ * (m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 with hc'
  have hc'0 : 0 ≤ c' := by positivity
  obtain ⟨hW1, -, -⟩ := hasBracket_WN hB hψ hn hT
  have hAbound : ∀ᵐ ω ∂μ, Aτ T ω ≤
      c' * K ^ 2 * (aN n * ∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) := by
    filter_upwards [hI, hBd, hWτ, hW1] with ω hI hBd hWτ hW1
    have hτT' := hτT ω
    simp only [Aτ, AP, min_eq_right hτT']
    have hq : IntervalIntegrable (fun s => q s ω) volume 0 (τ ω) :=
      hI.2.2.2.2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.2 (Or.inl ⟨(τ ω).2, hτT'⟩)))
    have hE1 : IntervalIntegrable (fun s => EN n ψ ω s fun _ => 1) volume 0 T := hW1.2
    have hE1' := hE1.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.2 (Or.inl ⟨(τ ω).2, hτT'⟩)))
    calc ∫ s in (0 : ℝ)..(τ ω), q s ω
        ≤ ∫ s in (0 : ℝ)..(τ ω), c' * K ^ 2 * (aN n * EN n ψ ω s fun _ => 1) := by
          refine intervalIntegral.integral_mono_on (τ ω).2 hq
            ((hE1'.const_mul (aN n)).const_mul (c' * K ^ 2)) fun s hs => ?_
          have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans hτT'⟩
          obtain ⟨-, -, -, hq2⟩ := hBd s hsT
          refine hq2.trans ?_
          have hE0 : 0 ≤ aN n * EN n ψ ω s fun _ => 1 :=
            mul_nonneg (by linarith) (EN_one_nonneg hn0.le _ _ _)
          have := prop62_mul_le (b := m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) (c := C ^ 4) hK0le hKρ0
            (by positivity) (by positivity) (replWN_nonneg n ψ s ω) (hWτ s hs.1 hs.2)
          calc _ ≤ Kρ * (m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * K ^ 2 *
                (aN n * EN n ψ ω s fun _ => 1) := mul_le_mul_of_nonneg_right this hE0
            _ = _ := by rw [hc']
      _ ≤ ∫ s in (0 : ℝ)..T, c' * K ^ 2 * (aN n * EN n ψ ω s fun _ => 1) := by
          refine intervalIntegral.integral_mono_interval le_rfl (τ ω).2 hτT'
            (ae_of_all _ fun s => ?_) ((hE1.const_mul (aN n)).const_mul (c' * K ^ 2))
          exact mul_nonneg (by positivity) (mul_nonneg (by linarith) (EN_one_nonneg hn0.le _ _ _))
      _ = c' * K ^ 2 * (aN n * ∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hEA : ∫ ω, Aτ T ω ∂μ ≤ c' * K ^ 2 * 2 ^ (2 + 16 * T) := by
    calc ∫ ω, Aτ T ω ∂μ
        ≤ ∫ ω, c' * K ^ 2 * (aN n * ∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) ∂μ :=
          integral_mono_ae hintA ((hEint.const_mul _).const_mul _) hAbound
      _ = c' * K ^ 2 * (aN n * ∫ ω, (∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) ∂μ) := by
          rw [integral_const_mul, integral_const_mul]
      _ ≤ c' * K ^ 2 * (2 * 2 ^ (1 + 16 * T)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h0 : 0 ≤ ∫ ω, (∫ s in (0 : ℝ)..T, EN n ψ ω s fun _ => 1) ∂μ :=
            integral_nonneg fun ω => intervalIntegral.integral_nonneg hT.le
              fun s _ => EN_one_nonneg hn0.le _ _ _
          exact mul_le_mul haN hEbound h0 (by norm_num)
      _ = c' * K ^ 2 * 2 ^ (2 + 16 * T) := by
          rw [show (2 : ℝ) ^ (2 + 16 * T) = 2 * 2 ^ (1 + 16 * T) by
            rw [show (2 : ℝ) + 16 * T = 1 + (1 + 16 * T) by ring, Real.rpow_add two_pos,
              Real.rpow_one]]
  -- Doob's `L²` inequality for the stopped martingale
  obtain ⟨hDm, hD⟩ := hNτ.toIsCL2Mart.lintegral_iSup_sq_le
  set V := c' * K ^ 2 * 2 ^ (2 + 16 * T) with hV
  have hsup : ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (Nτ t ω ^ 2) ∂μ ≤
      4 * ENNReal.ofReal V := by
    refine hD.trans ?_
    gcongr
    rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun ω => sq_nonneg _), hEq]
    exact ENNReal.ofReal_le_ofReal hEA
  -- the event `C = {∃ t ≤ T, |N_n(t ∧ τ_K)| > η/2}`
  have hCset : μ {ω | ∃ t ∈ Set.Icc 0 T, η / 2 < |Nτ t ω|} ≤
      ENNReal.ofReal (16 * (c' * K ^ 2 * 2 ^ (2 + 16 * T)) / η ^ 2) := by
    have hpos : (0 : ℝ) < (η / 2) ^ 2 := by positivity
    calc μ {ω | ∃ t ∈ Set.Icc 0 T, η / 2 < |Nτ t ω|}
        ≤ μ {ω | ENNReal.ofReal ((η / 2) ^ 2) ≤
            ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (Nτ t ω ^ 2)} := by
          refine measure_mono fun ω ⟨t, ht, hlt⟩ => ?_
          refine le_trans ?_ (le_iSup₂ (f := fun t _ => ENNReal.ofReal (Nτ t ω ^ 2)) t ht)
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← sq_abs (Nτ t ω)]
          exact pow_le_pow_left₀ (by positivity) hlt.le 2
      _ ≤ (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (Nτ t ω ^ 2) ∂μ) /
            ENNReal.ofReal ((η / 2) ^ 2) :=
          meas_ge_le_lintegral_div hDm (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top
      _ ≤ 4 * ENNReal.ofReal V / ENNReal.ofReal ((η / 2) ^ 2) := ENNReal.div_le_div_right hsup _
      _ = ENNReal.ofReal (16 * V / η ^ 2) := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_div_of_pos hpos]
          congr 1; field_simp; ring
  -- the event `B = {∃ t ≤ T, 𝒲_n(t) ≥ K}`
  have hBset : μ {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ WN n ψ t ω} ≤ ENNReal.ofReal (1 / K) := by
    have hint1 : ∫ ω, WN n ψ T ω ∂μ = 1 := by
      have h := hW.condExp 0 T' zero_le hT'.le
      rw [hT'] at h
      calc ∫ ω, WN n ψ T ω ∂μ = ∫ ω, (μ[WN n ψ T | 𝓖 0]) ω ∂μ :=
            (integral_condExp (𝓖.le 0)).symm
        _ = ∫ ω, WN n ψ ((0 : ℝ≥0) : ℝ) ω ∂μ := integral_congr_ae h
        _ = ∫ _, (1 : ℝ) ∂μ := integral_congr_ae (hW0.mono fun ω h => by simpa using h)
        _ = 1 := by simp
    have := hW.toIsCL2Mart.measure_exists_ge_le
      (ae_of_all _ fun ω t _ => replWN_nonneg n ψ t ω) hK0
    rwa [hint1] at this
  -- the inclusion
  have hincl : {ω | ∃ t ∈ Set.Icc 0 T, η < |∫ s in (0 : ℝ)..t,
      (EN n ψ ω s (φ s) - smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε)|} ≤ᵐ[μ]
      ({ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ WN n ψ t ω} ∪
        {ω | ∃ t ∈ Set.Icc 0 T, η / 2 < |Nτ t ω|} : Set Ω) := by
    filter_upwards [hI, hBd, hW'eq, hW0, hS] with ω hI hBd hW'eq hW0 hS
    rintro ⟨t, ht, hlt⟩
    by_contra hBC
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_le,
      not_lt] at hBC
    obtain ⟨hWK, hNη⟩ := hBC
    -- `τ_K = T`
    have hτeq : τ ω = T' := hitTime_eq_of_forall_lt fun s hs => by
      simp only [X, Real.toNNReal_coe]
      have hsT : (s : ℝ) ≤ T := by rw [← hT']; exact NNReal.coe_le_coe.2 hs.le
      rw [hW'eq s hsT]
      exact hWK s ⟨s.2, hsT⟩
    have hNt : Nτ t ω = NP t ω := by
      simp only [Nτ, hτeq, hT', min_eq_left ht.2]
    have hNη' := hNη t ht
    rw [hNt] at hNη'
    -- integrability on `[0, t]`
    have hsub : Set.uIcc 0 t ⊆ Set.uIcc 0 T :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ht))
    have iE := hI.2.1.mono_set hsub
    have iB := hI.2.2.1.mono_set hsub
    have iR := hI.2.2.2.1.mono_set hsub
    have iS := hS.2.2.mono_set hsub
    have hWsq : ∀ s ∈ Set.Icc 0 T, WN n ψ s ω ^ 2 ≤ K ^ 2 := fun s hs =>
      pow_le_pow_left₀ (replWN_nonneg n ψ s ω) (hWK s hs).le 2
    have hmn : 0 ≤ (m : ℝ) / n ^ (1 / 2 : ℝ) := by positivity
    have hP : 0 ≤ (m : ℝ) / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m := by positivity
    have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
    -- the bounds
    have hF : ∀ s ∈ Set.Icc 0 T, |FN n ψ ρ m φ s ω| ≤ m / n ^ (1 / 2 : ℝ) * C ^ 2 * K ^ 2 :=
      fun s hs => (hBd s hs).1.trans (mul_le_mul_of_nonneg_left (hWsq s hs) (by positivity))
    have hR : |∫ s in (0 : ℝ)..t, R s ω| ≤ T * (Kρ * (m / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) +
        1 / m) * C ^ 2 * K ^ 2) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
        (f := fun s => R s ω) (C := Kρ * (m / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m) *
          C ^ 2 * K ^ 2) fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        have hsT : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
        rw [Real.norm_eq_abs]
        exact (hBd s hsT).2.1.trans (prop62_mul_le hK0le hKρ0 hP (sq_nonneg _)
          (replWN_nonneg n ψ s ω) (hWK s hsT).le)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
      exact this.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht.2 (by positivity))
    have hBS : |∫ s in (0 : ℝ)..t, (BN n ψ ρ m s (φ s) ω -
        smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε)| ≤ T * (Δ * C ^ 2 * K ^ 2) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
        (C := Δ * C ^ 2 * K ^ 2) (f := fun s => BN n ψ ρ m s (φ s) ω -
          smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        have hsT : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
        rw [Real.norm_eq_abs, BN_eq hρ hn hm (hφ.replContinuous hsT) ⟨C, hφ.replAbs_le hsT⟩
          ψ ω s (hI.1 s hsT.1)]
        refine (abs_smoothedNormSq_tilted_sub_le hρ (hI.1 s hsT.1) (hφ.replContinuous hsT)
          (hφ.replAbs_le hsT) hε (by positivity) hΔ).trans ?_
        exact mul_le_mul_of_nonneg_left (hWsq s hsT) (by positivity)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
      exact this.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht.2 (by positivity))
    -- the decomposition
    have hdec : ∫ s in (0 : ℝ)..t, (EN n ψ ω s (φ s) -
        smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) =
        FN n ψ ρ m φ t ω - FN n ψ ρ m φ 0 ω - NP t ω - (∫ s in (0 : ℝ)..t, R s ω) +
          ∫ s in (0 : ℝ)..t, (BN n ψ ρ m s (φ s) ω -
            smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) := by
      have h1 : ∫ s in (0 : ℝ)..t, (EN n ψ ω s (φ s) -
          smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) = (∫ s in (0 : ℝ)..t, EN n ψ ω s (φ s))
            - ∫ s in (0 : ℝ)..t, smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε :=
        intervalIntegral.integral_sub iE iS
      have h2 : ∫ s in (0 : ℝ)..t, (BN n ψ ρ m s (φ s) ω -
          smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) = (∫ s in (0 : ℝ)..t, BN n ψ ρ m s (φ s) ω)
            - ∫ s in (0 : ℝ)..t, smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε :=
        intervalIntegral.integral_sub iB iS
      have h3 : ∫ s in (0 : ℝ)..t, (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω + R s ω) =
          (∫ s in (0 : ℝ)..t, (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω)) +
            ∫ s in (0 : ℝ)..t, R s ω :=
        intervalIntegral.integral_add (iE.sub iB) iR
      have h4 : ∫ s in (0 : ℝ)..t, (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω) =
          (∫ s in (0 : ℝ)..t, EN n ψ ω s (φ s)) - ∫ s in (0 : ℝ)..t, BN n ψ ρ m s (φ s) ω :=
        intervalIntegral.integral_sub iE iB
      have hNPt : NP t ω = FN n ψ ρ m φ t ω - FN n ψ ρ m φ 0 ω - ∫ s in (0 : ℝ)..t,
          (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω + R s ω) := rfl
      rw [hNPt]
      linarith [h1, h2, h3, h4]
    have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
    have htot : |∫ s in (0 : ℝ)..t, (EN n ψ ω s (φ s) -
        smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε)| ≤ η := by
      rw [hdec]
      have h1 := hF t ht
      have h2 := hF 0 h0T
      rw [abs_le]
      constructor <;> linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 h2).1,
        (abs_le.1 h2).2, (abs_le.1 hNη').1, (abs_le.1 hNη').2, (abs_le.1 hR).1, (abs_le.1 hR).2,
        (abs_le.1 hBS).1, (abs_le.1 hBS).2]
    exact absurd hlt (not_lt.2 htot)
  calc _ ≤ μ ({ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ WN n ψ t ω} ∪
        {ω | ∃ t ∈ Set.Icc 0 T, η / 2 < |Nτ t ω|}) := measure_mono_ae hincl
    _ ≤ μ {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ WN n ψ t ω} +
        μ {ω | ∃ t ∈ Set.Icc 0 T, η / 2 < |Nτ t ω|} := measure_union_le _ _
    _ ≤ _ := add_le_add hBset hCset

/-- **Proposition 6.2**, equation (6.3) (the replacement lemma). Let `T > 0` and
`φ ∈ C_b^{1,3}([0,T] × ℝ)` with `‖φ‖_{1,3} ≤ C`. Then:
* for all `n ≥ 1` and `ε > 0`, almost surely `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`, and
  `s ↦ ℰ_n(s;φ_s)` and `s ↦ ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²` are integrable on `[0,T]`;
* `lim_{ε → 0} limsup_{n → ∞} ℙ(sup_{t ∈ [0,T]} |∫_0^t (ℰ_n(s;φ_s) - ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²) ds| > η) = 0`
  for every `η > 0`, written in the equivalent form: for all `η, δ > 0` there is `ε₀ > 0` such that
  for every `ε ∈ (0, ε₀)` there is `N` with
  `ℙ(∃ t ∈ [0,T], |∫_0^t (ℰ_n(s;φ_s) - ‖(φ_s 𝒵_n(s)) ⋆ ρ_ε‖₂²) ds| > η) ≤ δ` for all `n ≥ N`
  (the probability is the outer measure, should this event not be measurable). -/
theorem prop_6_2 (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T C : ℝ} (hT : 0 < T) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) :
    (∀ n : ℝ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => EN n ψ ω s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε) volume 0 T) ∧
    ∀ η δ : ℝ, 0 < η → 0 < δ →
      ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ N : ℝ, ∀ n ≥ N,
        μ {ω | ∃ t ∈ Set.Icc 0 T, η < |∫ s in (0 : ℝ)..t,
          (EN n ψ ω s (φ s) - smoothedNormSq (tiltedMeasure n ψ ω s) (φ s) ρ ε)|} ≤
        ENNReal.ofReal δ := by
  refine ⟨fun n hn ε hε => prop62_integrable hB hψ hρ hT hφ hn hε, fun η δ hη hδ => ?_⟩
  obtain ⟨Kρ, hKρ0, hmain⟩ := prop62_main hB hψ hρ hT hφ
  have hC : 0 ≤ C := hφ.const_nonneg hT.le
  set D : ℝ := 2 ^ (2 + 16 * T) with hD
  have hD0 : 0 < D := by positivity
  set K : ℝ := max 1 (2 / δ) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hKδ : 1 / K ≤ δ / 2 := by
    rw [div_le_iff₀ hK0]
    have := le_max_right 1 (2 / δ)
    rw [← hKdef, div_le_iff₀ hδ] at this
    linarith
  set a : ℝ := C ^ 2 * K ^ 2 with ha
  set b : ℝ := C ^ 4 * K ^ 2 * D with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set A1 : ℝ := (2 + T * Kρ) * a + 1 with hA1
  set A2 : ℝ := 16 * Kρ * b / η ^ 2 + 1 with hA2
  have hA10 : 0 < A1 := by positivity
  have hA20 : 0 < A2 := by positivity
  refine ⟨min 1 (min (η / (8 * A1)) (δ / (4 * A2))), by positivity, fun ε hε => ?_⟩
  obtain ⟨hε0, hεlt⟩ := hε
  have hε1 : ε < 1 := hεlt.trans_le (min_le_left _ _)
  have hε2 : ε < η / (8 * A1) := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε < δ / (4 * A2) := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  -- `(2 + T K') ε C² K² ≤ η/8`
  have hdetε : (2 + T * Kρ) * ε * a ≤ η / 8 := by
    have h1 : (2 + T * Kρ) * a ≤ A1 := by linarith
    have h2 : ε * A1 ≤ η / 8 := by
      have := (lt_div_iff₀ (by positivity)).1 hε2
      linarith
    calc (2 + T * Kρ) * ε * a = ε * ((2 + T * Kρ) * a) := by ring
      _ ≤ ε * A1 := mul_le_mul_of_nonneg_left h1 hε0.le
      _ ≤ η / 8 := h2
  -- `16 K' ε² C⁴ K² D / η² ≤ δ/4`
  have hprobε : 16 * Kρ * ε ^ 2 * b / η ^ 2 ≤ δ / 4 := by
    have h1 : 16 * Kρ * b / η ^ 2 ≤ A2 := by linarith
    have h2 : ε * A2 ≤ δ / 4 := by
      have := (lt_div_iff₀ (by positivity)).1 hε3
      linarith
    have h3 : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε0.le hε1.le
    calc 16 * Kρ * ε ^ 2 * b / η ^ 2 = ε ^ 2 * (16 * Kρ * b / η ^ 2) := by ring
      _ ≤ ε * A2 := mul_le_mul h3 h1 (by positivity) hε0.le
      _ ≤ δ / 4 := h2
  -- asymptotics as `n → ∞`
  obtain ⟨L, hL0, hL⟩ := hρ.kappa_lipschitz
  set mf : ℝ → ℕ := fun n => ⌊ε * n ^ (1 / 2 : ℝ)⌋₊ with hmf
  set εf : ℝ → ℝ := fun n => (mf n : ℝ) * n ^ (-1 / 2 : ℝ) with hεf
  have hsqrt : Tendsto (fun n : ℝ => n ^ (1 / 2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hmlim : Tendsto mf atTop atTop :=
    tendsto_nat_floor_atTop.comp (hsqrt.const_mul_atTop hε0)
  have hblim : Tendsto (fun n => bM ρ (mf n)) atTop (𝓝 1) := (tendsto_bM hρ).comp hmlim
  have hinvm : Tendsto (fun n => 1 / (mf n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hmlim)
  have hinv2 : Tendsto (fun n : ℝ => 1 / n ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hinv4 : Tendsto (fun n : ℝ => 1 / n ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
  -- `ε - n^{-1/2} < ε_n ≤ ε`
  have hεn : ∀ n : ℝ, 0 < n → ε - 1 / n ^ (1 / 2 : ℝ) ≤ εf n ∧ εf n ≤ ε ∧
      εf n = mf n / n ^ (1 / 2 : ℝ) := by
    intro n hn
    have hs : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
    have e : εf n = mf n / n ^ (1 / 2 : ℝ) := by
      simp only [εf]
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hn.le]
      ring
    have h1 := Nat.floor_le (show 0 ≤ ε * n ^ (1 / 2 : ℝ) by positivity)
    have h2 := Nat.lt_floor_add_one (ε * n ^ (1 / 2 : ℝ))
    refine ⟨?_, ?_, e⟩
    · rw [e, sub_le_iff_le_add, ← add_div, le_div_iff₀ hs]
      simp only [mf] at h2 ⊢
      linarith
    · rw [e, div_le_iff₀ hs]; exact h1
  have hεlim : Tendsto εf atTop (𝓝 ε) := by
    have h0 : Tendsto (fun n : ℝ => ε - 1 / n ^ (1 / 2 : ℝ)) atTop (𝓝 ε) := by
      simpa using (tendsto_const_nhds (x := ε)).sub hinv2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn using (hεn n hn).1
    · filter_upwards [eventually_gt_atTop 0] with n hn using (hεn n hn).2.1
  set Δf : ℝ → ℝ := fun n => |1 / bM ρ (mf n) - 1| * (kappa ρ 0 / εf n) +
    (2 * L / εf n ^ 2 + kappa ρ 0 / (ε * εf n)) * (ε - εf n) with hΔf
  have hΔlim : Tendsto Δf atTop (𝓝 0) := by
    have h : Tendsto (fun n => |1 / bM ρ (mf n) - 1| * (kappa ρ 0 / εf n) +
        (2 * L / εf n ^ 2 + kappa ρ 0 / (ε * εf n)) * (ε - εf n)) atTop
        (𝓝 (|1 / 1 - 1| * (kappa ρ 0 / ε) + (2 * L / ε ^ 2 + kappa ρ 0 / (ε * ε)) * (ε - ε))) :=
      (((tendsto_const_nhds.div hblim one_ne_zero).sub_const 1).abs.mul
      (tendsto_const_nhds.div hεlim hε0.ne')).add
      (((tendsto_const_nhds.div (hεlim.pow 2) (by positivity)).add
        (tendsto_const_nhds.div (tendsto_const_nhds.mul hεlim) (by positivity))).mul
        (tendsto_const_nhds.sub hεlim))
    convert h using 2
    simp
  have hlim3 : Tendsto (fun n => T * Kρ * (1 / n ^ (1 / 4 : ℝ) + 1 / (mf n : ℝ)) * a) atTop
      (𝓝 0) := by
    simpa using ((hinv4.add hinvm).const_mul (T * Kρ)).mul_const a
  have hlim4 : Tendsto (fun n => T * Δf n * a) atTop (𝓝 0) := by
    simpa using (hΔlim.const_mul T).mul_const a
  have hlim5 : Tendsto (fun n : ℝ => 16 * Kρ * (1 / n ^ (1 / 2 : ℝ)) * b / η ^ 2) atTop (𝓝 0) := by
    simpa using ((hinv2.const_mul (16 * Kρ)).mul_const b).div_const (η ^ 2)
  have hev : ∀ᶠ n in atTop, 1 ≤ n ∧ 1 ≤ mf n ∧ ε / 2 ≤ εf n ∧
      T * Kρ * (1 / n ^ (1 / 4 : ℝ) + 1 / (mf n : ℝ)) * a ≤ η / 8 ∧
      T * Δf n * a ≤ η / 4 ∧ 16 * Kρ * (1 / n ^ (1 / 2 : ℝ)) * b / η ^ 2 ≤ δ / 4 :=
    (eventually_ge_atTop 1).and ((hmlim.eventually (eventually_ge_atTop 1)).and
      ((hεlim.eventually (eventually_ge_nhds (by linarith : ε / 2 < ε))).and
      ((hlim3.eventually (eventually_le_nhds (by positivity))).and
      ((hlim4.eventually (eventually_le_nhds (by positivity))).and
        (hlim5.eventually (eventually_le_nhds (by positivity)))))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hnN => ?_⟩
  obtain ⟨hn1, hm1, hεf2, h3, h4, h5⟩ := hN n hnN
  have hn0 : 0 < n := by linarith
  obtain ⟨-, hεle, hεeq⟩ := hεn n hn0
  have hεf0 : 0 < εf n := by linarith
  have hs : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hmn : (mf n : ℝ) / n ^ (1 / 2 : ℝ) ≤ ε := hεeq ▸ hεle
  have hmn0 : 0 ≤ (mf n : ℝ) / n ^ (1 / 2 : ℝ) := by positivity
  have hm2 : (mf n : ℝ) ^ 2 / n ≤ ε ^ 2 := by
    have hsq : n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) = n := by
      rw [← Real.rpow_add hn0]; norm_num
    have : (mf n : ℝ) ^ 2 / n = ((mf n : ℝ) / n ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [div_pow, sq (n ^ (1 / 2 : ℝ)), hsq]
    rw [this]
    exact pow_le_pow_left₀ hmn0 hmn 2
  -- the bound on `|κ_{ε_n}/b_m - κ_ε|`
  have hΔ : ∀ x, |kappaEps ρ ((mf n : ℝ) * n ^ (-1 / 2 : ℝ)) x / bM ρ (mf n) - kappaEps ρ ε x| ≤
      Δf n := by
    intro x
    have hk := replKappaEps_nonneg_le hρ hεf0 x
    have e : kappaEps ρ (εf n) x / bM ρ (mf n) - kappaEps ρ ε x =
        (1 / bM ρ (mf n) - 1) * kappaEps ρ (εf n) x + (kappaEps ρ (εf n) x - kappaEps ρ ε x) := by
      ring
    change |kappaEps ρ (εf n) x / bM ρ (mf n) - kappaEps ρ ε x| ≤ Δf n
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ (replKappaEps_sub_le hρ hL0 hL hεf0 hεle x))
    rw [abs_mul, abs_of_nonneg hk.1]
    exact mul_le_mul_of_nonneg_left hk.2 (abs_nonneg _)
  have hdet : 2 * ((mf n : ℝ) / n ^ (1 / 2 : ℝ)) * C ^ 2 * K ^ 2 +
      T * (Kρ * ((mf n : ℝ) / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / (mf n : ℝ)) * C ^ 2 *
        K ^ 2) + T * (Δf n * C ^ 2 * K ^ 2) ≤ η / 2 := by
    have e : 2 * ((mf n : ℝ) / n ^ (1 / 2 : ℝ)) * C ^ 2 * K ^ 2 +
        T * (Kρ * ((mf n : ℝ) / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / (mf n : ℝ)) * C ^ 2 *
          K ^ 2) + T * (Δf n * C ^ 2 * K ^ 2) =
        (2 + T * Kρ) * ((mf n : ℝ) / n ^ (1 / 2 : ℝ)) * a +
          T * Kρ * (1 / n ^ (1 / 4 : ℝ) + 1 / (mf n : ℝ)) * a + T * Δf n * a := by
      rw [ha]; ring
    rw [e]
    have : (2 + T * Kρ) * ((mf n : ℝ) / n ^ (1 / 2 : ℝ)) * a ≤ (2 + T * Kρ) * ε * a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmn (by positivity)) ha0
    linarith
  refine (hmain hn1 hm1 hε0 hK1 hη hΔ hdet).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 16 * (Kρ * ((mf n : ℝ) ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * K ^ 2 *
      2 ^ (2 + 16 * T)) / η ^ 2 ≤ 16 * Kρ * ε ^ 2 * b / η ^ 2 +
        16 * Kρ * (1 / n ^ (1 / 2 : ℝ)) * b / η ^ 2 := by
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have e : 16 * (Kρ * ((mf n : ℝ) ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * K ^ 2 *
        2 ^ (2 + 16 * T)) = 16 * Kρ * b * ((mf n : ℝ) ^ 2 / n) +
          16 * Kρ * (1 / n ^ (1 / 2 : ℝ)) * b := by
      rw [hb, hD]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ 16 * Kρ * b by positivity)
    linarith
  linarith

end QSSEPtoKPZ
