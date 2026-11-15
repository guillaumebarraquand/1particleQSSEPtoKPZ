/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorDefs
public import QSSEPtoKPZ.Replacement.CorrectorPathwise
public import QSSEPtoKPZ.Replacement.CorrectorTime
public import QSSEPtoKPZ.TiltedField.Quadratic
public import QSSEPtoKPZ.TiltedField.Martingales
public import QSSEPtoKPZ.Martingales.NullAug
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Lemma 6.4: the corrector

Statement: Stage 2, task T0; proof: task G1. Following decision D5 of
`docs/stage2-design.md`, the remainder `𝖱_n` is given by "there exists", with its bound (6.14),
instead of the explicit formula (6.16); likewise the martingale `N_n` is described by its bracket
`∫ q`, with the bound (6.15) on the density `q`.

Proof (task G1): Lemma 3.2 applied to `f_t = κ_n G Φ_t` (`corrF`, files `Corrector*.lean`);
the drift splits as `ℰ_n(t;φ_t) - 𝖡_n(t;φ_t) + 𝖱_n(t)` with `𝖱_n(t) = 𝒵_n^{⊗2}(t; corrRem_t)`, the
remainder (6.16); the bounds come from `abs_corrRem_le` and `abs_corrBracket_le`. The processes
`𝖱_n` and `q` are computed with the good version of `ψ` (all paths continuous), which makes them
jointly measurable, and agree almost surely with the article's ones on `[0,T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **Lemma 6.4**, equations (6.12)-(6.15). There is a constant `K`, depending only on `ρ`, such
that for every probability space, Brownian family and wave function (`L = ∞`), every `n ≥ 1`, every
integer `m ≥ 1`, `T > 0`, and `φ ∈ C_b^{1,3}([0,T] × ℝ)` with `‖φ‖_{1,3} ≤ C`, there are jointly
measurable processes `𝖱_n = R` and `q` such that:
* almost surely, `∑ₓ 𝔷_n(t,x)` converges for all `t ≥ 0`, and `s ↦ ℰ_n(s;φ_s)`, `s ↦ 𝖡_n(s;φ_s)`,
  `R` and `q` are integrable on `[0,T]`;
* almost surely, for all `t ∈ [0,T]`: `|𝖥_n(t)| ≤ (m/n^{1/2}) C² 𝒲_n(t)²` (6.13);
  `|𝖱_n(t)| ≤ K (m/n^{1/2} + 1/n^{1/4} + 1/m) C² 𝒲_n(t)²` (6.14); and
  `0 ≤ q(t) ≤ K (m²/n + 1/n^{1/2}) C⁴ 𝒲_n(t)² · a_n ℰ_n(t)` (6.15: `d⟨𝒲_n⟩_t = a_n ℰ_n(t) dt`);
* (6.12): `N_n(t) = 𝖥_n(t) - 𝖥_n(0) - ∫_0^t (ℰ_n(s;φ_s) - 𝖡_n(s;φ_s) + 𝖱_n(s)) ds` is a continuous
  square-integrable `(𝓕ⁿ_t)`-martingale on `[0,T]` with `⟨N_n⟩_t = ∫_0^t q(s) ds`;
* when `φ ≡ 1`: `𝖱_n ≡ 0`, and almost surely `𝖥_n(t) ≥ 0` for `t ∈ [0,T]`. -/
theorem lemma_6_4 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ K : ℝ, ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
      IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ →
      ∀ {n T C : ℝ} {m : ℕ} {φ φt : ℝ → ℝ → ℝ}, 1 ≤ n → 1 ≤ m → 0 < T → IsC13 T φ φt C →
      ∃ R q : ℝ → Ω → ℝ, Measurable (Function.uncurry R) ∧ Measurable (Function.uncurry q) ∧
        (∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
          IntervalIntegrable (fun s => EN n ψ ω s (φ s)) volume 0 T ∧
          IntervalIntegrable (fun s => BN n ψ ρ m s (φ s) ω) volume 0 T ∧
          IntervalIntegrable (fun s => R s ω) volume 0 T ∧
          IntervalIntegrable (fun s => q s ω) volume 0 T) ∧
        (∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
          |FN n ψ ρ m φ t ω| ≤ m / n ^ (1 / 2 : ℝ) * C ^ 2 * WN n ψ t ω ^ 2 ∧
          |R t ω| ≤ K * (m / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m) * C ^ 2 *
            WN n ψ t ω ^ 2 ∧
          0 ≤ q t ω ∧
          q t ω ≤ K * (m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * WN n ψ t ω ^ 2 *
            (aN n * EN n ψ ω t fun _ => 1)) ∧
        HasBracket T (filtN n 𝓕)
          (fun t ω => FN n ψ ρ m φ t ω - FN n ψ ρ m φ 0 ω - ∫ s in (0 : ℝ)..t,
            (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω + R s ω))
          (fun t ω => ∫ s in (0 : ℝ)..t, q s ω) μ ∧
        ((∀ t y, φ t y = 1) → (∀ t ω, R t ω = 0) ∧
          ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, 0 ≤ FN n ψ ρ m φ t ω) := by
  obtain ⟨Cρ, hCρ⟩ := hρ.exists_gM_zero_le
  refine ⟨24 + 2 * max Cρ 0, ?_⟩
  intro Ω mΩ 𝓕 μ _ B ψ hB hψ n T C m φ φt hn hm hT hφ
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hT0 : 0 ≤ T := hT.le
  have hC := hφ.corr_C_nonneg hT0
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  obtain ⟨-, hκ0, -, -⟩ := corrPref_props hn
  obtain ⟨ψ', hgood⟩ := hψ.exists_isGoodWave
  set ψc := corrWave ψ' with hψc
  set Cρ' := max Cρ 0 with hCρ'def
  have hCρ'0 : 0 ≤ Cρ' := le_max_right _ _
  have hCρ' : gM ρ m 0 ≤ Cρ' / m :=
    (hCρ m hm).trans (div_le_div_of_nonneg_right (le_max_left _ _) hm0.le)
  set X := (m : ℝ) / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m with hX
  have hX0 : 0 ≤ X := by positivity
  set Mk := kappa ρ 0 / (m * bM ρ m) with hMk
  have hS0 : 0 ≤ n ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0.le _
  -- bounds on `φ`
  have hφb : ∀ t ∈ Set.Icc 0 T, ∀ y, |φ t y| ≤ C := fun t ht y => (hφ.corr_abs_le_C hT0 ht y).1
  -- Lemma 3.2 applied to `f_t = κ_n G Φ_t`
  have hev := (hρ.gM_spec hm).1
  have hsymm : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, corrF n ρ m φ t x₁ x₂ = corrF n ρ m φ t x₂ x₁ := by
    intro t _ x₁ x₂
    simp only [corrF]
    rw [show x₁ - x₂ = -(x₂ - x₁) by ring, hev]
    ring
  obtain ⟨hae32, hbr32⟩ := lemma_3_2 hB hψ hn hT (f := fun t => corrF n ρ m φ t)
    (f' := fun t => corrF' n ρ m φ φt t) (C := corrPref n * m * (1 + n ^ (1 / 4 : ℝ)) * C ^ 2)
    hsymm (fun x₁ x₂ t ht => hasDerivWithinAt_corrF hn hφ ht x₁ x₂)
    (fun x₁ x₂ => continuousOn_corrF' hφ x₁ x₂)
    (fun t ht x₁ x₂ => abs_corrF_le hρ hm hn hφ hT0 ht x₁ x₂)
  obtain ⟨-, hbrW, -⟩ := hasBracket_WN hB hψ hn hT
  -- the processes `𝖱_n` and `q`
  set R : ℝ → Ω → ℝ := fun t ω => pairZ2 n ψc ω t (corrRem n ρ m φ φt (corrClamp T t)) with hR
  set q : ℝ → Ω → ℝ := fun t ω =>
    bracketDensN2 n ψc (fun s => corrF n ρ m φ (corrClamp T s)) t ω with hq
  have hZ := measurable_zN_corrWave hgood n
  have hRm : Measurable (Function.uncurry R) :=
    measurable_corrPair (Z := fun t ω => zN n ψc ω t) hZ
      (fun a b => (continuous_corrRem_clamp hφ hT0 a b).measurable)
  have hqm : Measurable (Function.uncurry q) :=
    corr_measurable_bracketDensN2 hgood n (fun a b => (continuous_corrF_clamp hφ hT0 a b).measurable)
  -- pointwise bounds on the integrands
  have hEd : ∀ t ∈ Set.Icc 0 T, ∀ a b, |corrEdens n φ t a b| ≤ n ^ (1 / 2 : ℝ) * C ^ 2 := by
    intro t ht a b
    have hi : |1 / 2 * (if |b - a| = 1 then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    have hU : |φ t (rescaledPosition n t a) * φ t (rescaledPosition n t b)| ≤ C * C := by
      rw [abs_mul]; exact mul_le_mul (hφb t ht _) (hφb t ht _) (abs_nonneg _) hC
    calc |corrEdens n φ t a b| = n ^ (1 / 2 : ℝ) * |1 / 2 * (if |b - a| = 1 then (1 : ℝ) else 0)| *
          |φ t (rescaledPosition n t a) * φ t (rescaledPosition n t b)| := by
          unfold corrEdens; rw [abs_mul, abs_mul, abs_of_nonneg hS0]
      _ ≤ n ^ (1 / 2 : ℝ) * 1 * (C * C) := by gcongr
      _ = _ := by ring
  have hMk0 : 0 ≤ Mk := by
    have := hρ.kappa_le_kappa_zero.2.2
    have := hρ.bM_pos hm
    positivity
  have hBNe : ∀ ω s, BN n ψ ρ m s (φ s) ω = corrPair (zN n ψ ω s) (corrBdens n ρ m φ s) := by
    intro ω s
    show _ = corrPair _ (fun a b => n ^ (1 / 2 : ℝ) * (kM ρ m (b - a) *
      φ s (rescaledPosition n s a) * φ s (rescaledPosition n s b)))
    rw [corrPair_const_mul]; rfl
  have hBd : ∀ t ∈ Set.Icc 0 T, ∀ a b, |corrBdens n ρ m φ t a b| ≤ n ^ (1 / 2 : ℝ) * (Mk * C ^ 2) := by
    intro t ht a b
    unfold corrBdens
    rw [abs_mul, abs_of_nonneg hS0]
    have := corr_abs_mul3_le (corr_abs_kM_le hρ hm (b - a)) (hφb t ht (rescaledPosition n t a))
      (hφb t ht (rescaledPosition n t b))
    calc _ ≤ n ^ (1 / 2 : ℝ) * (Mk * C * C) := by gcongr
      _ = _ := by ring
  have hRd : ∀ t ∈ Set.Icc 0 T, ∀ a b, |corrRem n ρ m φ φt t a b| ≤ (9 + 2 * Cρ') * X * C ^ 2 :=
    fun t ht a b => abs_corrRem_le hρ hm hn hφ hT0 ht hCρ'0 hCρ' a b
  -- the good event
  have hgoodω : ∀ᵐ ω ∂μ, (∀ s : ℝ, 0 ≤ s → zN n ψc ω s = zN n ψ ω s) ∧ ψ 0 ω = waveInit ∧
      (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => bracketDensN2 n ψ (fun t => corrF n ρ m φ t) s ω) volume 0 T ∧
      ContinuousOn (fun t => WN n ψ t ω) (Set.Icc 0 T) := by
    filter_upwards [hgood.ae_eq, hψ.ae_init, hae32, hbrW.cont] with ω h1 h2 h3 h4
    refine ⟨fun s hs => ?_, h2, h3.1, h3.2.2, h4⟩
    have hs' : 0 ≤ n * s / 2 := by positivity
    have e : ψc (n * s / 2) ω = ψ (n * s / 2) ω := by
      rw [hψc, corrWave_of_nonneg _ hs', ← Real.coe_toNNReal _ hs', h1]
    funext x
    simp only [zN, density, e]
  -- consequences on the good event
  have hRi : ∀ ω, (∀ s : ℝ, 0 ≤ s → zN n ψc ω s = zN n ψ ω s) → ∀ t ∈ Set.Icc 0 T,
      R t ω = pairZ2 n ψ ω t (corrRem n ρ m φ φt t) := by
    intro ω hz t ht
    simp only [hR, pairZ2_eq_corrPair, corrClamp_of_mem ht, hz t ht.1]
  have hqi : ∀ ω, (∀ s : ℝ, 0 ≤ s → zN n ψc ω s = zN n ψ ω s) → ∀ t ∈ Set.Icc 0 T,
      q t ω = bracketDensN2 n ψ (fun t => corrF n ρ m φ t) t ω := by
    intro ω hz t ht
    simp only [hq, bracketDensN2, corrClamp_of_mem ht, hz t ht.1]
  have hdrift : ∀ ω, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) → ∀ t ∈ Set.Icc 0 T,
      pairZ2 n ψ ω t (corrDrift n ρ m φ φt t) =
        EN n ψ ω t (φ t) - BN n ψ ρ m t (φ t) ω + pairZ2 n ψ ω t (corrRem n ρ m φ φt t) := by
    intro ω hsum t ht
    have hz := hsum t ht.1
    have hz0 := corr_zN_nonneg n ψ ω t
    have e1 : corrDrift n ρ m φ φt t = fun a b =>
        (corrEdens n φ t a b - corrBdens n ρ m φ t a b) + corrRem n ρ m φ φt t a b := by
      funext a b; simp only [corrRem]; ring
    have hEB : ∀ a b, |corrEdens n φ t a b - corrBdens n ρ m φ t a b| ≤
        n ^ (1 / 2 : ℝ) * C ^ 2 + n ^ (1 / 2 : ℝ) * (Mk * C ^ 2) := fun a b =>
      (abs_sub _ _).trans (add_le_add (hEd t ht a b) (hBd t ht a b))
    rw [pairZ2_eq_corrPair, e1, corrPair_add hz0 hz hEB (hRd t ht),
      corrPair_sub hz0 hz (hEd t ht) (hBd t ht), hBNe, pairZ2_eq_corrPair]
    congr 2
    -- the term `(1/2) 𝟙_{|r|=1}` gives `ℰ_n(t;φ_t)`
    · have e2 : corrEdens n φ t = fun a b => n ^ (1 / 2 : ℝ) *
          (1 / 2 * (if |b - a| = 1 then 1 else 0) *
            (φ t (rescaledPosition n t a) * φ t (rescaledPosition n t b))) := by
        funext a b; simp only [corrEdens]; ring
      rw [e2, corrPair_const_mul, corrPair_adjacent hz0 hz (fun a b => mul_comm _ _)
        (M := C * C) (fun a b => by
          rw [abs_mul]; exact mul_le_mul (hφb t ht _) (hφb t ht _) (abs_nonneg _) hC)]
      unfold EN
      congr 1
      exact tsum_congr fun x => by ring
  -- integrability on `[0,T]`
  have hII : ∀ᵐ ω ∂μ, (∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t)) ∧
      IntervalIntegrable (fun s => EN n ψ ω s (φ s)) volume 0 T ∧
      IntervalIntegrable (fun s => BN n ψ ρ m s (φ s) ω) volume 0 T ∧
      IntervalIntegrable (fun s => R s ω) volume 0 T ∧
      IntervalIntegrable (fun s => q s ω) volume 0 T := by
    filter_upwards [hgoodω] with ω hω
    obtain ⟨hzeq, -, hsum, hbI, hWc⟩ := hω
    obtain ⟨Wm, hWm⟩ := isCompact_Icc.exists_bound_of_continuousOn hWc
    have hW2 : ∀ t ∈ Set.Icc 0 T, WN n ψ t ω ^ 2 ≤ Wm ^ 2 := fun t ht => by
      have := hWm t ht
      rw [Real.norm_eq_abs] at this
      exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
    refine ⟨hsum, ?_, ?_, ?_, ?_⟩
    · -- `ℰ_n(s;φ_s)`
      have hG : Measurable fun s => EN n ψc ω s (φ (corrClamp T s)) :=
        (measurable_EN_corrWave hgood n (G := fun s => φ (corrClamp T s)) fun x =>
          (hφ.corr_continuous_clamp hT0 (corr_continuous_rescaledPosition n x)).1.measurable).of_uncurry_right
      refine corr_intervalIntegrable_of_bound hT0 hG (fun s hs => ?_)
        (M := n ^ (1 / 2 : ℝ) * C ^ 2 * Wm ^ 2) (fun s hs => ?_)
      · simp only [EN, corrClamp_of_mem hs, hzeq s hs.1]
      · exact (corr_abs_EN_le hn0.le (hsum s hs.1) fun x => hφb s hs _).trans
          (mul_le_mul_of_nonneg_left (hW2 s hs) (by positivity))
    · -- `𝖡_n(s;φ_s)`
      have hG : Measurable fun s => BN n ψc ρ m s (φ (corrClamp T s)) ω := by
        have h := measurable_corrPair (Z := fun t ω => zN n ψc ω t) hZ
          (F := fun s a b => kM ρ m (b - a) * φ (corrClamp T s) (rescaledPosition n s a) *
            φ (corrClamp T s) (rescaledPosition n s b)) fun a b =>
          ((continuous_const.mul (hφ.corr_continuous_clamp hT0
            (corr_continuous_rescaledPosition n a)).1).mul (hφ.corr_continuous_clamp hT0
            (corr_continuous_rescaledPosition n b)).1).measurable
        exact (h.of_uncurry_right).const_mul _
      refine corr_intervalIntegrable_of_bound hT0 hG (fun s hs => ?_)
        (M := n ^ (1 / 2 : ℝ) * (Mk * C ^ 2) * Wm ^ 2) (fun s hs => ?_)
      · simp only [BN, pairZ2_eq_corrPair, corrClamp_of_mem hs, hzeq s hs.1]
      · have h := abs_corrPair_le (corr_zN_nonneg n ψ ω s) (hsum s hs.1) (hBd s hs)
        rw [← corr_WN_eq_tsum] at h
        rw [hBNe]
        calc _ ≤ n ^ (1 / 2 : ℝ) * (Mk * C ^ 2) * WN n ψ s ω ^ 2 := h
          _ ≤ _ := mul_le_mul_of_nonneg_left (hW2 s hs) (mul_nonneg hS0 (mul_nonneg hMk0 (sq_nonneg C)))
    · -- `𝖱_n(s)`
      refine corr_intervalIntegrable_of_bound hT0 hRm.of_uncurry_right (fun s _ => rfl)
        (M := (9 + 2 * Cρ') * X * C ^ 2 * Wm ^ 2) (fun s hs => ?_)
      rw [hRi ω hzeq s hs]
      have h := abs_corrPair_le (corr_zN_nonneg n ψ ω s) (hsum s hs.1) (hRd s hs)
      rw [← corr_WN_eq_tsum] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hW2 s hs) (by positivity))
    · -- `q(s)`
      exact hbI.congr fun s hs => (hqi ω hzeq s
        (Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le hT0] at hs))).symm
  refine ⟨R, q, hRm, hqm, hII, ?_, ?_, ?_⟩
  · -- the bounds (6.13), (6.14), (6.15)
    filter_upwards [hgoodω] with ω hω
    obtain ⟨hzeq, -, hsum, -, -⟩ := hω
    intro t ht
    have hz := hsum t ht.1
    refine ⟨corr_abs_FN_le hρ hm hn hz (hφb t ht), ?_, ?_, ?_⟩
    · rw [hRi ω hzeq t ht]
      have h := abs_corrPair_le (corr_zN_nonneg n ψ ω t) hz (hRd t ht)
      rw [← corr_WN_eq_tsum] at h
      refine h.trans ?_
      have : (9 + 2 * Cρ') * X ≤ (24 + 2 * Cρ') * X := mul_le_mul_of_nonneg_right (by linarith) hX0
      have hW : 0 ≤ C ^ 2 * WN n ψ t ω ^ 2 := by positivity
      calc (9 + 2 * Cρ') * X * C ^ 2 * WN n ψ t ω ^ 2 = (9 + 2 * Cρ') * X * (C ^ 2 * WN n ψ t ω ^ 2) :=
            by ring
        _ ≤ (24 + 2 * Cρ') * X * (C ^ 2 * WN n ψ t ω ^ 2) := mul_le_mul_of_nonneg_right this hW
        _ = _ := by rw [hX]; ring
    · exact mul_nonneg (by positivity) (tsum_nonneg fun x => mul_nonneg (mul_nonneg
        (corr_zN_nonneg _ _ _ _ _) (corr_zN_nonneg _ _ _ _ _)) (sq_nonneg _))
    · rw [hqi ω hzeq t ht]
      have h1 := corr_bracketDensN2_le (f := fun t => corrF n ρ m φ t) hn0.le hz
        (abs_corrBracket_le hρ hm hn hφ hT0 ht)
      have h2 := corrBracket_sq_le (C := C) hn hm
      set M := corrPref n * C ^ 2 * ((Real.exp (thetaN n / 2) - Real.exp (-thetaN n / 2)) * m / 2 +
        1 / 4 + m * n ^ (-1 / 2 : ℝ) / 2)
      set P := ∑' x, zN n ψ ω t x * zN n ψ ω t (x + 1)
      have hP : 0 ≤ P := tsum_nonneg fun x => mul_nonneg (corr_zN_nonneg _ _ _ _ _) (corr_zN_nonneg _ _ _ _ _)
      have hE1 : aN n * EN n ψ ω t (fun _ => 1) = aN n * n ^ (1 / 2 : ℝ) * P := by
        simp only [EN, mul_one, P]; ring
      rw [hE1]
      have hW : 0 ≤ WN n ψ t ω ^ 2 * P := by positivity
      have hY : 0 ≤ (m : ℝ) ^ 2 / n + 1 / n ^ (1 / 2 : ℝ) := by positivity
      have ha : 0 ≤ aN n * n ^ (1 / 2 : ℝ) := by
        have := (constants_bounds hn).2.2.1; positivity
      calc _ ≤ 4 * n * M ^ 2 * WN n ψ t ω ^ 2 * P := h1
        _ = 4 * n * M ^ 2 * (WN n ψ t ω ^ 2 * P) := by ring
        _ ≤ 24 * ((m : ℝ) ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * (aN n * n ^ (1 / 2 : ℝ)) *
            (WN n ψ t ω ^ 2 * P) := mul_le_mul_of_nonneg_right h2 hW
        _ ≤ (24 + 2 * Cρ') * ((m : ℝ) ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 *
            (aN n * n ^ (1 / 2 : ℝ)) * (WN n ψ t ω ^ 2 * P) := by
          gcongr; linarith
        _ = _ := by ring
  · -- (6.12): the identity, from Lemma 3.2
    refine hbr32.congr hT0 ?_ ?_
    · filter_upwards [hgoodω] with ω hω
      obtain ⟨hzeq, h0, hsum, -, -⟩ := hω
      intro t ht
      have hF : ∀ s, pairZ2 n ψ ω s (corrF n ρ m φ s) = FN n ψ ρ m φ s ω := fun s => by
        have e : corrF n ρ m φ s = fun a b => corrPref n * (gM ρ m (b - a) *
            φ s (rescaledPosition n s a) * φ s (rescaledPosition n s b)) := rfl
        rw [e, pairZ2_eq_corrPair, corrPair_const_mul]
        rfl
      have hδ : ∀ x, zN n ψ ω 0 x = if x = 0 then 1 else 0 := fun x => by
        simp only [zN, density, mul_zero, zero_div, h0, waveInit_apply]
        split_ifs with hx
        · subst hx; simp
        · simp
      have h00 : corrF n ρ m φ 0 0 0 = FN n ψ ρ m φ 0 ω := by
        rw [← hF 0, pairZ2_eq_corrPair, corrPair_delta hδ]
      rw [hF t, h00]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht.1] at hs
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      show _ = _ - _ + R s ω
      rw [hRi ω hzeq s hsT]
      exact hdrift ω hsum s hsT
    · filter_upwards [hgoodω] with ω hω
      obtain ⟨hzeq, -, -, -, -⟩ := hω
      intro t ht
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht.1] at hs
      exact (hqi ω hzeq s ⟨hs.1, hs.2.trans ht.2⟩).symm
  · -- the case `φ ≡ 1`
    intro h1
    have hφt : ∀ s ∈ Set.Icc 0 T, ∀ y, φt s y = 0 := fun s hs y => by
      have hd := hφ.hasDerivWithinAt y s hs
      have hc : (fun t => φ t y) = fun _ => 1 := funext fun t => h1 t y
      rw [hc] at hd
      exact (uniqueDiffOn_Icc hT s hs).eq_deriv _ hd (hasDerivWithinAt_const _ _ _)
    refine ⟨fun t ω => ?_, ae_of_all _ fun ω t _ => ?_⟩
    · have h0 : ∀ a b, corrRem n ρ m φ φt (corrClamp T t) a b = 0 := fun a b =>
        corrRem_eq_zero_of_const hρ hm hn (h1 _) (hφt _ (corrClamp_mem hT0 t)) a b
      simp only [hR, pairZ2, h0, mul_zero, tsum_zero]
    · refine mul_nonneg (by unfold corrPref at hκ0; exact hκ0) (tsum_nonneg fun a =>
        tsum_nonneg fun b => ?_)
      simp only [h1, mul_one]
      exact mul_nonneg (mul_nonneg (corr_zN_nonneg _ _ _ _ _) (corr_zN_nonneg _ _ _ _ _))
        (hρ.gM_nonneg_le hm _).1

end QSSEPtoKPZ
