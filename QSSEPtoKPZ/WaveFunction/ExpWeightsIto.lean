/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.ExpWeights

/-!
# Linear functionals of `P` with exponentially growing weights (task D5)

Lemma 2.3 (1) for the unit-norm version `ψ'` of the wave function (`IsUnitWave`). Let `a ≥ 0`
and let `w_t(x)` be `C¹` in `t ∈ [0, N]` with `|w_t(x)|, |∂ₜw_t(x)| ≤ C e^{a|x|}`. With
`b = 2a` and `𝖭(ω) = sup_{t ≤ N} ∑ₓ e^{b|x|} P(t,x)`, which is integrable by (2.2)
(`moment_bound` with `k = 1`):

* `IsUnitWave.isItoProcessUpTo_expWeight`: `∑ₓ w_t(x) P(t,x)` is an Itô process up to `N`, with
  drift `∑ₓ (∂ₜw_t + Δw_t)(x) P(t,x)` and diffusion `weightCurrent ψ' w`. Proof: the boxes
  `|x| ≤ K` (`isItoProcessUpTo_weight_finset`) and `K → ∞` (`IsItoProcessUpTo.of_tendsto_const`),
  as in the article: on `{𝖭 < ∞}` the series converge and the drifts converge by dominated
  convergence (bound `C (3 + 2 e^b) 𝖭`); the energy of the difference of the diffusions is at most
  `8 C² 𝔼 ∫_0^N ∑_{|x| > K} e^{b|x|} P(s,x) ds`, which tends to `0` by dominated convergence
  (bound `8 C² N 𝖭`, integrable).
* `IsUnitWave.lemma_2_3_linear_unit`: the conclusion of `lemma_2_3_linear` for `ψ'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- If `𝖭 = sup_{t ∈ [0,T]} ∑ₓ e^{b|x|} P(t,x) < ∞`, then for `s ∈ [0, T]` the series
`∑ₓ e^{b|x|} P(s,x)` converges, with sum at most `𝖭`. -/
lemma linExp_of_iSup_lt_top {b T : ℝ} {ω : Ω}
    (h : (⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
      ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)) < ⊤)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    Summable (fun x : ℤ => Real.exp (b * |(x : ℝ)|) * density ψ' ω s x) ∧
    ∑' x : ℤ, Real.exp (b * |(x : ℝ)|) * density ψ' ω s x ≤
      (⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
        ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)).toReal := by
  have hnn : ∀ x : ℤ, 0 ≤ Real.exp (b * |(x : ℝ)|) * density ψ' ω s x := fun x =>
    mul_nonneg (Real.exp_pos _).le (IsUnitWave.density_nonneg ψ' ω s x)
  have hle : ∑' x : ℤ, ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω s x) ≤
      ⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
        ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x) :=
    le_iSup₂ (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) T) => ∑' x : ℤ,
      ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)) s hs
  have hfin := (hle.trans_lt h).ne
  have hsum := ENNReal.summable_toReal hfin
  simp only [ENNReal.toReal_ofReal (hnn _)] at hsum
  refine ⟨hsum, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum] at hle
  exact (ENNReal.ofReal_le_iff_le_toReal h.ne).1 hle

/-- **Interval integrability of a series.** If `s ↦ F(s,x)` is continuous on `[0, N]` for every
`x`, the series `∑ₓ F(s,x)` converges for `s ∈ [0, N]`, and its sum is bounded by `K` there, then
`s ↦ ∑ₓ F(s,x)` is integrable on `[0, N]`. -/
lemma linExp_intervalIntegrable_tsum {F : ℝ → ℤ → ℝ} {N K : ℝ} (hN : 0 ≤ N)
    (hc : ∀ x, ContinuousOn (fun s => F s x) (Set.Icc 0 N))
    (hs : ∀ s ∈ Set.Icc (0 : ℝ) N, Summable (F s))
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) N, |∑' x, F s x| ≤ K) :
    IntervalIntegrable (fun s => ∑' x, F s x) volume 0 N := by
  have hsub : Set.uIoc 0 N ⊆ Set.Icc 0 N := fun s hs => by
    rw [Set.uIoc_of_le hN] at hs; exact ⟨hs.1.le, hs.2⟩
  have hvol : volume (Set.uIoc (0 : ℝ) N) < ∞ := by
    rw [Set.uIoc_of_le hN, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound hvol ?_ K ?_
  · exact aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) s => ∑ x ∈ Finset.Icc (-(n : ℤ)) n, F s x)
      (fun n => ((continuousOn_finsetSum _ fun x _ => hc x).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
      ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hsI =>
        (hs s (hsub hsI)).hasSum.comp Finset.tendsto_Icc_neg))
  · exact (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => by
      rw [Real.norm_eq_abs]; exact hK s (hsub hs))

namespace IsUnitWave

/-- **(2.2) for `ψ'`, `k = 1`**: `𝖭 = sup_{t ∈ [0,T]} ∑ₓ e^{b|x|} P(t,x)` is integrable. -/
lemma linExp_moment [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (T : ℝ) :
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
      ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)) μ ∧
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
      ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)) ∂μ < ⊤ := by
  have h := moment_bound hB.nullAug hu.wave (a := b) (T := T) hb 1
  simpa using h

/-- **Linear functionals with exponentially growing weights are Itô processes.** Let `a ≥ 0`
and let `w_t(x)` be `C¹` in `t ∈ [0, N]` (derivative `w'_t(x)`, continuous in `t`) with
`|w_t(x)|, |w'_t(x)| ≤ C e^{a|x|}`. Then `∑ₓ w_t(x) P(t,x)` is an Itô process up to `N`:
`d ∑ₓ w_t(x) P(t,x) = ∑ₓ (∂ₜw_t + Δw_t)(x) P(t,x) dt + ∑_y (w_t(y+1) - w_t(y)) dJ_t(y)`,
the diffusion coefficients being `weightCurrent ψ' w`. -/
theorem isItoProcessUpTo_expWeight [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {w w' : ℝ → ℤ → ℝ} {a C : ℝ} (ha : 0 ≤ a)
    (hw : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt (w · x) (w' t x) (Set.Icc 0 N) t)
    (hw' : ∀ x, ContinuousOn (w' · x) (Set.Icc 0 N))
    (hbd : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, |w t x| ≤ C * Real.exp (a * |(x : ℝ)|) ∧
      |w' t x| ≤ C * Real.exp (a * |(x : ℝ)|)) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => ∑' x, w t x * density ψ' ω t x)
      (fun s ω => ∑' x, (w' s x + lap (w s) x) * density ψ' ω s x)
      (weightCurrent ψ' w) := by
  classical
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hbd 0 0 ⟨le_rfl, N.2⟩).1
    simpa using this
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 2 * a := ⟨_, rfl⟩
  have hb : 0 ≤ b := by rw [hbdef]; positivity
  have hEab : ∀ x : ℤ, Real.exp (a * |(x : ℝ)|) ≤ Real.exp (b * |(x : ℝ)|) := fun x => by
    rw [hbdef]; exact linExp_exp_le_two ha x
  have hbd2 : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, |w t x| ≤ C * Real.exp (b * |(x : ℝ)|) ∧
      |w' t x| ≤ C * Real.exp (b * |(x : ℝ)|) := fun x t ht =>
    ⟨(hbd x t ht).1.trans (mul_le_mul_of_nonneg_left (hEab x) hC),
      (hbd x t ht).2.trans (mul_le_mul_of_nonneg_left (hEab x) hC)⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Ω → ℝ≥0∞, M = fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) N, ∑' x : ℤ,
      ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x) := ⟨_, rfl⟩
  obtain ⟨hMm, hMi⟩ := linExp_moment hB hu hb (N : ℝ)
  rw [← hMdef] at hMm hMi
  have hMfin : ∀ᵐ ω ∂μ, M ω < ⊤ := ae_lt_top' hMm hMi.ne
  have hgood : ∀ ω, M ω < ⊤ → ∀ s ∈ Set.Icc (0 : ℝ) N,
      Summable (fun x : ℤ => Real.exp (b * |(x : ℝ)|) * density ψ' ω s x) ∧
      ∑' x : ℤ, Real.exp (b * |(x : ℝ)|) * density ψ' ω s x ≤ (M ω).toReal :=
    fun ω h s hs => by
    subst hMdef
    exact linExp_of_iSup_lt_top h hs
  have hbox := fun K : ℕ => hu.isItoProcessUpTo_weight_finset hB hw hw'
    (Finset.Icc (-(K : ℤ)) K)
  have hcw : ∀ x, ContinuousOn (w · x) (Set.Icc 0 N) := fun x t ht =>
    (hw x t ht).continuousWithinAt
  have hsubI : ∀ {t : ℝ}, 0 ≤ t → t ≤ N → Set.uIoc 0 t ⊆ Set.Icc 0 N := fun ht0 htN s hs => by
    rw [Set.uIoc_of_le ht0] at hs; exact ⟨hs.1.le, hs.2.trans htN⟩
  -- pointwise facts on the drifts
  have hdr := fun ω (hω : M ω < ⊤) s (hs : s ∈ Set.Icc (0 : ℝ) N) =>
    linExp_drift_facts hb (p := density ψ' ω s) (w := w s) (w' := w' s)
      (fun x => density_nonneg ψ' ω s x) (hgood ω hω s hs).1 (fun x => (hbd2 x s hs).1)
      (fun x => (hbd2 x s hs).2)
  have hdK : ∀ ω (hω : M ω < ⊤) s (hs : s ∈ Set.Icc (0 : ℝ) N) (S : Finset ℤ),
      |∑ x ∈ S, (w' s x * density ψ' ω s x + w s x * lap (density ψ' ω s) x)| ≤
        C * (3 + 2 * Real.exp b) * (M ω).toReal := fun ω hω s hs S =>
    ((hdr ω hω s hs).2.2 S).trans (mul_le_mul_of_nonneg_left (hgood ω hω s hs).2
      (mul_nonneg hC (by positivity)))
  have hdlim : ∀ ω, M ω < ⊤ → ∀ s, s ∈ Set.Icc (0 : ℝ) N → Tendsto (fun K : ℕ =>
      ∑ x ∈ Finset.Icc (-(K : ℤ)) K, (w' s x * density ψ' ω s x +
        w s x * lap (density ψ' ω s) x)) atTop
      (𝓝 (∑' x, (w' s x + lap (w s) x) * density ψ' ω s x)) := fun ω hω s hs => by
    rw [← (hdr ω hω s hs).2.1]
    exact (hdr ω hω s hs).1.hasSum.comp Finset.tendsto_Icc_neg
  have hsumd : ∀ ω, M ω < ⊤ → ∀ s ∈ Set.Icc (0 : ℝ) N,
      Summable (fun x => (w' s x + lap (w s) x) * density ψ' ω s x) := fun ω hω s hs =>
    linExp_summable_mul (C := C * (3 + 2 * Real.exp b)) (hgood ω hω s hs).1 (fun x => by
      have h1 := (hbd2 x s hs).2
      have h2 := linExp_abs_lap_le hb (fun y => (hbd2 y s hs).1) x
      calc |w' s x + lap (w s) x| ≤ |w' s x| + |lap (w s) x| := abs_add_le _ _
        _ ≤ _ := by linarith) (fun x => density_nonneg ψ' ω s x)
  have hdcont : ∀ ω (K : ℕ), ContinuousOn (fun s => ∑ x ∈ Finset.Icc (-(K : ℤ)) K,
      (w' s x * density ψ' ω s x + w s x * lap (density ψ' ω s) x)) (Set.Icc 0 N) :=
    fun ω K => continuousOn_finsetSum _ fun x _ =>
      ((hw' x).mul ((hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self)).add
        ((hcw x).mul ((hu.weight_continuousOn_lap_density ω x).mono Set.Icc_subset_Ici_self))
  -- joint measurability of the limit diffusion
  have hdm : ∀ i, Measurable fun p : ℝ × Ω =>
      if 0 < p.1 then (if p.1 ≤ (N : ℝ) then weightCurrent ψ' w i p.1 p.2 else 0) else 0 := by
    intro i
    have hwcl : ∀ x, Continuous fun s : ℝ => w (max 0 (min s N)) x := fun x =>
      (hcw x).comp_continuous (continuous_const.max (continuous_id.min continuous_const))
        fun s => ⟨le_max_left _ _, max_le N.2 (min_le_right _ _)⟩
    have hf : Measurable fun s : ℝ => if s ≤ (N : ℝ) then
        w (max 0 (min s N)) (i.1 + 1) - w (max 0 (min s N)) i.1 else 0 :=
      Measurable.ite (measurableSet_le measurable_id measurable_const)
        ((hwcl _).sub (hwcl _)).measurable measurable_const
    have hm := (hu.isItoIntegrable_waveCurrent i.1).meas i
    have e : (fun p : ℝ × Ω => if 0 < p.1 then
        (if p.1 ≤ (N : ℝ) then weightCurrent ψ' w i p.1 p.2 else 0) else 0) =
        fun p => (if p.1 ≤ (N : ℝ) then w (max 0 (min p.1 N)) (i.1 + 1) -
          w (max 0 (min p.1 N)) i.1 else 0) *
          (if 0 < p.1 then waveCurrent ψ' i.1 i p.1 p.2 else 0) := by
      funext p
      by_cases h0 : 0 < p.1
      · by_cases hN : p.1 ≤ N
        · simp [h0, hN, weightCurrent, max_eq_right h0.le]
        · simp [h0, hN]
      · simp [h0]
    rw [e]
    exact (hf.comp measurable_fst).mul hm
  refine IsItoProcessUpTo.of_tendsto_const hB.nullAug hbox hdm ?_ ?_ ?_ ?_
  · -- the energy of the difference of the diffusions tends to `0`
    set D : ℕ → ℤ × Fin 2 → ℝ → Ω → ℝ := fun K i s ω =>
      (if s ≤ (N : ℝ) then ∑ x ∈ Finset.Icc (-(K : ℤ)) K,
        w s x * (waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) else 0) -
      (if s ≤ (N : ℝ) then weightCurrent ψ' w i s ω else 0) with hDdef
    set G : ℕ → ℝ → Ω → ℝ≥0∞ := fun K s ω => ENNReal.ofReal (8 * C ^ 2) *
      ∑' y : ℤ, (if y ∈ Finset.Icc (-(K : ℤ)) K then 0 else
        ENNReal.ofReal (Real.exp (b * |(y : ℝ)|) * density ψ' ω s y)) with hGdef
    have hDG : ∀ K ω s, s ∈ Set.Ioc (0 : ℝ) N → ∑' i, ‖D K i s ω‖ₑ ^ 2 ≤ G K s ω := by
      intro K ω s hs
      have hsN : s ≤ (N : ℝ) := hs.2
      set S := Finset.Icc (-(K : ℤ)) K with hS
      set v : ℝ → ℤ → ℝ := fun s x => (if x ∈ S then w s x else 0) - w s x with hvdef
      have hDv : ∀ i, D K i s ω = weightCurrent ψ' v i s ω := fun i => by
        simp only [hDdef, hsN, ite_true]
        rw [sum_mul_waveCurrent_sub, weightCurrent_sub]
      set q : ℤ → ℝ := fun y => if y ∈ S then 0 else
        Real.exp (b * |(y : ℝ)|) * density ψ' ω s y with hqdef
      have hvq : ∀ x, v s x ^ 2 * density ψ' ω s x ≤ C ^ 2 * q x := fun x => by
        by_cases hx : x ∈ S
        · simp [hvdef, hqdef, hx]
        · simp only [hvdef, hqdef, hx, ite_false, zero_sub, neg_sq]
          rw [hbdef]
          exact linExp_sq_mul_le (fun y => density_nonneg ψ' ω s y)
            (fun y => (hbd y s ⟨hs.1.le, hsN⟩).1) x
      have hterm : ∀ y, (v s (y + 1) - v s y) ^ 2 *
          (2 * density ψ' ω s y * density ψ' ω s (y + 1)) ≤ 4 * C ^ 2 * (q (y + 1) + q y) :=
        linExp_bracket_term_le (fun y => density_nonneg ψ' ω s y)
          (fun y => hu.density_le_one ω hs.1.le y) hvq
      have hq0 : ∀ y, 0 ≤ q y := fun y => by
        simp only [hqdef]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (Real.exp_pos _).le (density_nonneg ψ' ω s y)
      have hqe : ∀ y, ENNReal.ofReal (q y) = if y ∈ S then 0 else
          ENNReal.ofReal (Real.exp (b * |(y : ℝ)|) * density ψ' ω s y) := fun y => by
        simp only [hqdef]
        split_ifs <;> simp
      simp only [hDv]
      rw [ENNReal.tsum_prod']
      have hfib : ∀ y, ∑' j : Fin 2, ‖weightCurrent ψ' v (y, j) s ω‖ₑ ^ 2 = ENNReal.ofReal
          ((v s (y + 1) - v s y) ^ 2 * (2 * density ψ' ω s y * density ψ' ω s (y + 1))) := by
        intro y
        rw [← tsum_weightCurrent_sq_fiber, tsum_fintype, tsum_fintype,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
        simp only [StochIntAux.enorm_sq_eq]
      simp only [hfib]
      calc ∑' y, ENNReal.ofReal ((v s (y + 1) - v s y) ^ 2 *
            (2 * density ψ' ω s y * density ψ' ω s (y + 1)))
          ≤ ∑' y, ENNReal.ofReal (4 * C ^ 2) *
              (ENNReal.ofReal (q (y + 1)) + ENNReal.ofReal (q y)) :=
            ENNReal.tsum_le_tsum fun y => by
              rw [← ENNReal.ofReal_add (hq0 _) (hq0 _), ← ENNReal.ofReal_mul (by positivity)]
              exact ENNReal.ofReal_le_ofReal (hterm y)
        _ = ENNReal.ofReal (4 * C ^ 2) *
              (∑' y, ENNReal.ofReal (q y) + ∑' y, ENNReal.ofReal (q y)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
            congr 2
            exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun y => ENNReal.ofReal (q y))
        _ = G K s ω := by
            simp only [hGdef, hqe]
            rw [← two_mul, ← mul_assoc, show (8 : ℝ) * C ^ 2 = 4 * C ^ 2 * 2 by ring,
              ENNReal.ofReal_mul (p := 4 * C ^ 2) (q := 2) (by positivity),
              ENNReal.ofReal_ofNat]
    have hGb : ∀ K ω s, s ∈ Set.Icc (0 : ℝ) N → G K s ω ≤ ENNReal.ofReal (8 * C ^ 2) * M ω :=
      fun K ω s hs => by
      refine mul_le_mul' le_rfl ((ENNReal.tsum_le_tsum (g := fun y : ℤ =>
        ENNReal.ofReal (Real.exp (b * |(y : ℝ)|) * density ψ' ω s y)) fun y => ?_).trans ?_)
      · exact (show (if y ∈ Finset.Icc (-(K : ℤ)) K then 0 else
            ENNReal.ofReal (Real.exp (b * |(y : ℝ)|) * density ψ' ω s y)) ≤
            ENNReal.ofReal (Real.exp (b * |(y : ℝ)|) * density ψ' ω s y) by
          split_ifs
          · exact zero_le
          · exact le_rfl)
      · rw [hMdef]
        exact le_iSup₂ (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) N) => ∑' x : ℤ,
          ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)) s hs
    have hpe : ∀ K ω, pathEnergy (D K) N ω ≤ ∫⁻ s in Set.Ioc (0 : ℝ) N, G K s ω :=
      fun K ω => setLIntegral_mono' measurableSet_Ioc fun s hs => hDG K ω s hs
    have hpe' : ∀ K ω, pathEnergy (D K) N ω ≤
        ENNReal.ofReal (8 * C ^ 2) * volume (Set.Ioc (0 : ℝ) N) * M ω := fun K ω => by
      refine (hpe K ω).trans ?_
      refine (setLIntegral_mono' measurableSet_Ioc fun s hs =>
        hGb K ω s ⟨hs.1.le, hs.2⟩).trans (le_of_eq ?_)
      rw [setLIntegral_const]
      ring
    have hvolN : volume (Set.Ioc (0 : ℝ) N) ≠ ∞ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hGlim : ∀ ω, M ω < ⊤ →
        Tendsto (fun K => ∫⁻ s in Set.Ioc (0 : ℝ) N, G K s ω) atTop (𝓝 0) := by
      intro ω hω
      have := tendsto_lintegral_of_dominated_convergence'
        (μ := volume.restrict (Set.Ioc (0 : ℝ) N))
        (F := fun K s => G K s ω) (f := fun _ => 0) (fun _ => ENNReal.ofReal (8 * C ^ 2) * M ω)
        (fun K => ?_)
        (fun K => (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs =>
          hGb K ω s ⟨hs.1.le, hs.2⟩))
        (by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.ne) hvolN)
        ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_))
      · simpa using this
      · refine AEMeasurable.const_mul (AEMeasurable.tsum fun y => ?_) _
        by_cases hy : y ∈ Finset.Icc (-(K : ℤ)) K
        · simp only [hy, ite_true]; exact aemeasurable_const
        · simp only [hy, ite_false]
          refine ContinuousOn.aemeasurable ?_ measurableSet_Ioc
          exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
            ((hu.weight_continuousOn_density ω y).mono fun s hs => le_of_lt hs.1))
      · have hfin : ∑' y : ℤ, ENNReal.ofReal (Real.exp (b * |(y : ℝ)|) * density ψ' ω s y) ≠ ⊤ :=
          by
          refine ne_top_of_le_ne_top hω.ne ?_
          rw [hMdef]
          exact le_iSup₂ (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) N) => ∑' x : ℤ,
            ENNReal.ofReal (Real.exp (b * |(x : ℝ)|) * density ψ' ω t x)) s ⟨hs.1.le, hs.2⟩
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (8 * C ^ 2))
          (linExp_tendsto_tail hfin) (Or.inr ENNReal.ofReal_ne_top)
        simpa [hGdef] using this
    have hEm : ∀ K, Measurable (pathEnergy (D K) N) := fun K => by
      have h1 : StochIntAux.EnergyMeas (fun (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) =>
          if s ≤ (N : ℝ) then ∑ x ∈ Finset.Icc (-(K : ℤ)) K,
            w s x * (waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) else 0) :=
        (hbox K).integrable.meas
      have h2 : StochIntAux.EnergyMeas (fun (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) =>
          if s ≤ (N : ℝ) then weightCurrent ψ' w i s ω else 0) := hdm
      exact StochIntAux.measurable_pathEnergy (h1.sub h2) N
    have := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun K ω => pathEnergy (D K) N ω) (f := fun _ => 0)
      (fun ω => ENNReal.ofReal (8 * C ^ 2) * volume (Set.Ioc (0 : ℝ) N) * M ω) hEm
      (fun K => ae_of_all _ fun ω => hpe' K ω)
      (by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolN)]
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolN) hMi.ne)
      (by
        filter_upwards [hMfin] with ω hω
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (hGlim ω hω) (fun _ => zero_le) fun K => hpe K ω)
    simpa [energy] using this
  · -- the limit drift is integrable on `[0, N]`
    filter_upwards [hMfin] with ω hω
    refine linExp_intervalIntegrable_tsum (K := C * (3 + 2 * Real.exp b) * (M ω).toReal)
      N.2 (fun x => ?_) (fun s hs => ?_) (fun s hs => ?_)
    · have hl : ContinuousOn (fun s => lap (w s) x) (Set.Icc 0 N) := by
        simp only [lap]
        exact ((hcw _).add (hcw _)).sub (continuousOn_const.mul (hcw _))
      exact ((hw' x).add hl).mul
        ((hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self)
    · exact hsumd ω hω s hs
    · exact le_of_tendsto ((continuous_abs.tendsto _).comp (hdlim ω hω s hs))
        (Eventually.of_forall fun K => hdK ω hω s hs _)
  · -- the processes converge
    filter_upwards [hMfin] with ω hω t ht0 htN
    exact (linExp_summable_mul (hgood ω hω t ⟨ht0, htN⟩).1
      (fun x => (hbd2 x t ⟨ht0, htN⟩).1) (fun x => density_nonneg ψ' ω t x)).hasSum.comp
        Finset.tendsto_Icc_neg
  · -- the integrated drifts converge (dominated convergence)
    filter_upwards [hMfin] with ω hω t ht0 htN
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => C * (3 + 2 * Real.exp b) * (M ω).toReal)
        (Eventually.of_forall fun K =>
          ((hdcont ω K).mono (hsubI ht0 htN)).aestronglyMeasurable measurableSet_uIoc)
        (Eventually.of_forall fun K => ae_of_all _ fun s hs => by
          rw [Real.norm_eq_abs]; exact hdK ω hω s (hsubI ht0 htN hs) _)
        intervalIntegrable_const
        (ae_of_all _ fun s hs => hdlim ω hω s (hsubI ht0 htN hs))

/-- **Lemma 2.3 (1) for the unit-norm version `ψ'`** (the conclusion of `lemma_2_3_linear`,
with `ψ'` in place of `ψ`). -/
theorem lemma_2_3_linear_unit [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ)
    {T a C : ℝ} (hT : 0 < T) (ha : 0 ≤ a) {α α' : ℝ → ℤ → ℝ}
    (hα : ∀ x, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (α · x) (α' t x) (Set.Icc 0 T) t)
    (hα' : ∀ x, ContinuousOn (α' · x) (Set.Icc 0 T))
    (hbd : ∀ x, ∀ t ∈ Set.Icc 0 T, |α t x| + |α' t x| ≤ C * Real.exp (a * |(x : ℝ)|)) :
    (∀ᵐ ω ∂μ, (∀ t ∈ Set.Icc 0 T,
        Summable (fun x => |α t x| * density ψ' ω t x) ∧
        Summable (fun x => |α' t x + lap (α t) x| * density ψ' ω t x) ∧
        Summable (fun x => (α t (x + 1) - α t x) ^ 2 * density ψ' ω t x *
          density ψ' ω t (x + 1))) ∧
      IntervalIntegrable (fun s => ∑' x, (α' s x + lap (α s) x) * density ψ' ω s x) volume 0 T ∧
      IntervalIntegrable (fun s => ∑' x,
        2 * (α s (x + 1) - α s x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1)) volume 0 T) ∧
    HasBracket T 𝓕
      (fun t ω => ∑' x, α t x * density ψ' ω t x - α 0 0 -
        ∫ s in (0 : ℝ)..t, ∑' x, (α' s x + lap (α s) x) * density ψ' ω s x)
      (fun t ω => ∫ s in (0 : ℝ)..t, ∑' x,
        2 * (α s (x + 1) - α s x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1)) μ := by
  obtain ⟨N, rfl⟩ : ∃ N : ℝ≥0, (N : ℝ) = T := ⟨⟨T, hT.le⟩, rfl⟩
  have hbd' : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, |α t x| ≤ C * Real.exp (a * |(x : ℝ)|) ∧
      |α' t x| ≤ C * Real.exp (a * |(x : ℝ)|) := fun x t ht => by
    have h := hbd x t ht
    have h1 := abs_nonneg (α t x)
    have h2 := abs_nonneg (α' t x)
    exact ⟨by linarith, by linarith⟩
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hbd' 0 0 ⟨le_rfl, N.2⟩).1
    simpa using this
  have h2a : 0 ≤ 2 * a := by positivity
  have hEab : ∀ x : ℤ, C * Real.exp (a * |(x : ℝ)|) ≤ C * Real.exp (2 * a * |(x : ℝ)|) :=
    fun x => mul_le_mul_of_nonneg_left (linExp_exp_le_two ha x) hC
  have hX := hu.isItoProcessUpTo_expWeight hB ha hα hα' hbd'
  obtain ⟨M, hMdef⟩ : ∃ M : Ω → ℝ≥0∞, M = fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) N, ∑' x : ℤ,
      ENNReal.ofReal (Real.exp (2 * a * |(x : ℝ)|) * density ψ' ω t x) := ⟨_, rfl⟩
  obtain ⟨hMm, hMi⟩ := linExp_moment hB hu h2a (N : ℝ)
  rw [← hMdef] at hMm hMi
  have hMfin : ∀ᵐ ω ∂μ, M ω < ⊤ := ae_lt_top' hMm hMi.ne
  have hgood : ∀ ω, M ω < ⊤ → ∀ s ∈ Set.Icc (0 : ℝ) N,
      Summable (fun x : ℤ => Real.exp (2 * a * |(x : ℝ)|) * density ψ' ω s x) ∧
      ∑' x : ℤ, Real.exp (2 * a * |(x : ℝ)|) * density ψ' ω s x ≤ (M ω).toReal :=
    fun ω h s hs => by
    subst hMdef
    exact linExp_of_iSup_lt_top h hs
  have hcα : ∀ x, ContinuousOn (α · x) (Set.Icc 0 N) := fun x t ht =>
    (hα x t ht).continuousWithinAt
  -- the bracket density
  have hbrt : ∀ ω, M ω < ⊤ → ∀ s ∈ Set.Icc (0 : ℝ) N,
      Summable (fun y => (α s (y + 1) - α s y) ^ 2 *
        (2 * density ψ' ω s y * density ψ' ω s (y + 1))) ∧
      ∑' y, (α s (y + 1) - α s y) ^ 2 * (2 * density ψ' ω s y * density ψ' ω s (y + 1)) ≤
        8 * C ^ 2 * (M ω).toReal := fun ω hω s hs => by
    set q : ℤ → ℝ := fun y => Real.exp (2 * a * |(y : ℝ)|) * density ψ' ω s y with hqdef
    have hq := (hgood ω hω s hs).1
    have hq1 : Summable fun y => q (y + 1) := (Equiv.addRight (1 : ℤ)).summable_iff.2 hq
    have hterm := linExp_bracket_term_le (K := C ^ 2) (q := q) (w := α s)
      (fun y => density_nonneg ψ' ω s y) (fun y => hu.density_le_one ω hs.1 y)
      (linExp_sq_mul_le (fun y => density_nonneg ψ' ω s y) fun y => (hbd' y s hs).1)
    have hnn : ∀ y, 0 ≤ (α s (y + 1) - α s y) ^ 2 *
        (2 * density ψ' ω s y * density ψ' ω s (y + 1)) := fun y => by
      have := density_nonneg ψ' ω s y
      have := density_nonneg ψ' ω s (y + 1)
      positivity
    have hsum := Summable.of_nonneg_of_le hnn hterm ((hq1.add hq).mul_left (4 * C ^ 2))
    refine ⟨hsum, (hsum.tsum_le_tsum hterm ((hq1.add hq).mul_left (4 * C ^ 2))).trans ?_⟩
    have e1 : ∑' y, q (y + 1) = ∑' y : ℤ, Real.exp (2 * a * |(y : ℝ)|) * density ψ' ω s y :=
      (Equiv.addRight (1 : ℤ)).tsum_eq q
    rw [tsum_mul_left, hq1.tsum_add hq, e1]
    have := (hgood ω hω s hs).2
    nlinarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hMfin, hX.drift] with ω hω hdrift
    refine ⟨fun t ht => ⟨?_, ?_, ?_⟩, hdrift, ?_⟩
    · exact linExp_summable_mul (hgood ω hω t ht).1 (w := fun x => |α t x|)
        (fun x => by rw [abs_abs]; exact (hbd' x t ht).1.trans (hEab x))
        (fun x => density_nonneg ψ' ω t x)
    · refine linExp_summable_mul (C := C * (3 + 2 * Real.exp (2 * a))) (hgood ω hω t ht).1
        (w := fun x => |α' t x + lap (α t) x|) (fun x => ?_) (fun x => density_nonneg ψ' ω t x)
      have h1 := (hbd' x t ht).2.trans (hEab x)
      have h2 := linExp_abs_lap_le h2a (fun y => (hbd' y t ht).1.trans (hEab y)) x
      rw [abs_abs]
      calc |α' t x + lap (α t) x| ≤ |α' t x| + |lap (α t) x| := abs_add_le _ _
        _ ≤ _ := by linarith
    · refine ((hbrt ω hω t ht).1.mul_left (1 / 2)).congr fun y => ?_
      ring
    · refine linExp_intervalIntegrable_tsum (K := 8 * C ^ 2 * (M ω).toReal) N.2
        (fun x => ?_) (fun s hs => ?_) (fun s hs => ?_)
      · exact ((continuousOn_const.mul (((hcα _).sub (hcα _)).pow 2)).mul
          ((hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self)).mul
          ((hu.weight_continuousOn_density ω _).mono Set.Icc_subset_Ici_self)
      · exact (hbrt ω hω s hs).1.congr fun y => by ring
      · have e : (fun x => 2 * (α s (x + 1) - α s x) ^ 2 * density ψ' ω s x *
            density ψ' ω s (x + 1)) = fun y => (α s (y + 1) - α s y) ^ 2 *
            (2 * density ψ' ω s y * density ψ' ω s (y + 1)) := by
          funext y; ring
        rw [e, abs_of_nonneg (tsum_nonneg fun y => by
          have := density_nonneg ψ' ω s y
          have := density_nonneg ψ' ω s (y + 1)
          positivity)]
        exact (hbrt ω hω s hs).2
  · have hbr := hasBracket_stochInt hB.nullAug hX.integrable N
    refine hasBracket_nullAug_iff.1 (hbr.congr (NNReal.coe_nonneg N) ?_ ?_)
    · filter_upwards [hX.eq] with ω hω t ht
      have e := hω ⟨t, ht.1⟩
      have hm : min (⟨t, ht.1⟩ : ℝ≥0) N = ⟨t, ht.1⟩ := min_eq_left ht.2
      erw [hm] at e
      have h0 : ∑' x, α 0 x * density ψ' ω 0 x = α 0 0 := by
        have : ∀ x, α 0 x * density ψ' ω 0 x = if x = 0 then α 0 0 else 0 := fun x => by
          rw [density, hu.init_apply ω x]
          split_ifs with h
          · subst h; simp
          · simp
        simp only [this, tsum_ite_eq]
      change ∑' x, α t x * density ψ' ω t x = (∑' x, α 0 x * density ψ' ω 0 x +
        ∫ s in (0 : ℝ)..t, ∑' x, (α' s x + lap (α s) x) * density ψ' ω s x) +
        stochInt (nullAug μ 𝓕) μ B (fun i s ω => if s ≤ (N : ℝ) then weightCurrent ψ' α i s ω
          else 0) t ω at e
      rw [e, h0]
      ring
    · filter_upwards [hMfin] with ω hω t ht
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht.1] at hs
      have hsI : s ∈ Set.Icc (0 : ℝ) N := ⟨hs.1, hs.2.trans ht.2⟩
      have hsN : s ≤ (N : ℝ) := hsI.2
      simp only [hsN, ite_true]
      rw [(hasSum_weightCurrent_sq ψ' α s ω (hbrt ω hω s hsI).1).tsum_eq]
      congr 1
      funext y
      ring

end IsUnitWave

end QSSEPtoKPZ
