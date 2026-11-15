/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.QuadPath
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The martingale part of a quadratic functional of `P` (task D6)

The diffusion of `∑_{(x₁,x₂) ∈ [-K,K]²} f(x₁,x₂) P(x₁) P(x₂)` (`quadBoxDiff`) is, for symmetric
`f`, `∑_{x ∈ [-K,K]} V_K(x) (c_{x-1} - c_x)` with `V_K(x) = 2 ∑_{x' ∈ [-K,K]} f(x,x') P(x')`,
that is `weightCurrent` of `V_K 𝟙_{[-K,K]}` (`quadBoxDiff_eq`). The limit is the family
`quadLimDiff`: `(2 D(y)) (c_y)ᵢ` with `D(y) = ∑_{x'} (f(y+1,x') - f(y,x')) P(x')`, i.e.
`weightCurrent` of `V = 2 ∑_{x'} f(·,x') P(x')` (`quadLimDiff_eq`), on the event `{N_T < ∞}`
(`0` outside, a null set).

* `IsUnitWave.measurable_quadLimDiff`: `quadLimDiff` is jointly measurable (limit of partial
  sums of the series `D`);
* `IsUnitWave.tendsto_energy_quadBoxDiff`: the energy `𝔼 ∫_0^T ∑ᵢ (·)² ds` of the difference
  tends to `0`: pathwise it is at most `∫_0^T 8 ∑_y (V_K 𝟙 - V)(y)² P(s,y) ds`, which tends to `0`
  by dominated convergence (twice), with the bound `128 C² σ³ T N_T³` integrable by (2.2) with
  `k = 3`. This is the `L²` convergence of the truncated martingales in the article.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The diffusion of the box sum `∑_{[-K,K]²} f P P`. -/
def quadBoxDiff (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (f : ℝ → ℤ → ℤ → ℝ) (K : ℕ) (i : ℤ × Fin 2) (s : ℝ)
    (ω : Ω) : ℝ :=
  ∑ p ∈ quadBox K, f s p.1 p.2 *
    (density ψ' ω s p.1 * (waveCurrent ψ' (p.2 - 1) i s ω - waveCurrent ψ' p.2 i s ω) +
      density ψ' ω s p.2 * (waveCurrent ψ' (p.1 - 1) i s ω - waveCurrent ψ' p.1 i s ω))

/-- The limit diffusion `(2 D(y)) (c_y)ᵢ`, `y = i.1`, on `{N_T < ∞}`. -/
def quadLimDiff (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (a T : ℝ) (f : ℝ → ℤ → ℤ → ℝ) (i : ℤ × Fin 2)
    (s : ℝ) (ω : Ω) : ℝ :=
  if quadSup ψ' a T ω ≠ ⊤ then 2 * quadD ψ' f s ω i.1 * waveCurrent ψ' i.1 i s ω else 0

/-- **The box diffusion is a `weightCurrent`** (summation by parts, `f` symmetric). -/
lemma quadBoxDiff_eq {f : ℝ → ℤ → ℤ → ℝ} {s : ℝ} (hs : ∀ x₁ x₂, f s x₁ x₂ = f s x₂ x₁)
    (K : ℕ) (i : ℤ × Fin 2) (ω : Ω) :
    quadBoxDiff ψ' f K i s ω = weightCurrent ψ' (fun _ x =>
      if x ∈ Finset.Icc (-(K : ℤ)) K then
        2 * ∑ x' ∈ Finset.Icc (-(K : ℤ)) K, f s x x' * density ψ' ω s x' else 0) i s ω := by
  set I := Finset.Icc (-(K : ℤ)) K with hI
  set dd : ℤ → ℝ := fun x => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω with hdd
  rw [← sum_mul_waveCurrent_sub ψ' (fun _ x => 2 * ∑ x' ∈ I, f s x x' * density ψ' ω s x') I]
  unfold quadBoxDiff quadBox
  rw [← hI, Finset.sum_product]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := I) (t := I) (f := fun x y => f s x y * (density ψ' ω s x *
    (waveCurrent ψ' (y - 1) i s ω - waveCurrent ψ' y i s ω)))]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hs y x]
  ring

namespace IsUnitWave

/-- On `{N_T < ∞}` and for `s ∈ [0,T]`, `quadLimDiff` is `weightCurrent` of
`V = 2 ∑_{x'} f(·,x') P(x')`. -/
lemma quadLimDiff_eq {a C T : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) {f : ℝ → ℤ → ℤ → ℝ}
    {ω : Ω} (hω : quadSup ψ' a T ω ≠ ⊤) {s : ℝ} (hs : s ∈ Set.Icc 0 T)
    (hfb : ∀ x₁ x₂, |f s x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂) (i : ℤ × Fin 2) :
    quadLimDiff ψ' a T f i s ω =
      weightCurrent ψ' (fun _ x => 2 * quadRow (f s) (density ψ' ω s) x) i s ω := by
  have hD := quadDecay_of_quadSup hω hs
  simp only [quadLimDiff, hω, ne_eq, not_false_eq_true, ite_true, weightCurrent, quadD]
  rw [hD.tsum_row_sub ha hC hfb]
  ring

/-- **Joint measurability of the limit diffusion.** `(s, ω) ↦ quadLimDiff` (cut to
`s ∈ (0, N]`) is measurable: on `{s ≤ N, N_N(ω) < ∞}` the series `D` is the limit of its
partial sums over `[-n, n]`, which are measurable. -/
theorem measurable_quadLimDiff (hu : IsUnitWave 𝓕 B ψ ψ' μ) [IsProbabilityMeasure μ]
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) {N : ℝ≥0} {f : ℝ → ℤ → ℤ → ℝ}
    (hc : ∀ x₁ x₂, ContinuousOn (f · x₁ x₂) (Set.Icc 0 N))
    (hfb : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    (hm : Measurable (quadSup ψ' a N)) (i : ℤ × Fin 2) :
    Measurable fun p : ℝ × Ω => if 0 < p.1 then
      (if p.1 ≤ (N : ℝ) then quadLimDiff ψ' a N f i p.1 p.2 else 0) else 0 := by
  obtain ⟨cl, hcl⟩ : ∃ cl : ℝ → ℝ, cl = fun s : ℝ => max 0 (min s (N : ℝ)) := ⟨_, rfl⟩
  have hclc : Continuous cl := by
    rw [hcl]; exact continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ s, cl s ∈ Set.Icc (0 : ℝ) N := fun s => by
    rw [hcl]; exact ⟨le_max_left _ _, max_le N.2 (min_le_right _ _)⟩
  have hg : ∀ x x', Continuous fun s => f (cl s) (x + 1) x' - f (cl s) x x' := fun x x' =>
    ((hc _ _).comp_continuous hclc hclm).sub ((hc _ _).comp_continuous hclc hclm)
  have hEm : MeasurableSet {p : ℝ × Ω | p.1 ≤ (N : ℝ) ∧ quadSup ψ' a N p.2 ≠ ⊤} :=
    (measurableSet_le measurable_fst measurable_const).inter
      ((hm (measurableSet_singleton ⊤)).compl.preimage measurable_snd)
  set Q : ℕ → ℝ × Ω → ℝ := fun n p =>
    if p.1 ≤ (N : ℝ) ∧ quadSup ψ' a N p.2 ≠ ⊤ then
      ∑ x' ∈ Finset.Icc (-(n : ℤ)) n, (f (cl p.1) (i.1 + 1) x' - f (cl p.1) i.1 x') *
        density ψ' p.2 (max p.1 0) x' else 0 with hQ
  set Q' : ℝ × Ω → ℝ := fun p =>
    if p.1 ≤ (N : ℝ) ∧ quadSup ψ' a N p.2 ≠ ⊤ then
      ∑' x', (f (cl p.1) (i.1 + 1) x' - f (cl p.1) i.1 x') *
        density ψ' p.2 (max p.1 0) x' else 0 with hQ'
  have hQm : ∀ n, Measurable (Q n) := fun n =>
    Measurable.ite hEm (Finset.measurable_sum _ fun x' _ =>
      ((hg _ _).measurable.comp measurable_fst).mul
        ((hu.weight_measurable_density_max x').comp measurable_swap)) measurable_const
  have hQ'm : Measurable Q' := by
    refine measurable_of_tendsto_metrizable hQm (tendsto_pi_nhds.2 fun p => ?_)
    by_cases hp : p.1 ≤ (N : ℝ) ∧ quadSup ψ' a N p.2 ≠ ⊤
    · simp only [hQ, hQ', hp.1, hp.2, ne_eq, not_false_eq_true, and_self, ite_true]
      have ht : max p.1 0 ∈ Set.Icc (0 : ℝ) N := ⟨le_max_right _ _, max_le hp.1 N.2⟩
      have hct : cl p.1 = max p.1 0 := by simp only [hcl]; rw [min_eq_left hp.1, max_comm]
      rw [hct]
      have hD := quadDecay_of_quadSup hp.2 ht
      have hs := ((hD.summable_row ha hC (hfb _ ht) (i.1 + 1)).sub
        (hD.summable_row ha hC (hfb _ ht) i.1)).congr fun x' => (sub_mul _ _ _).symm
      exact hs.hasSum.comp Finset.tendsto_Icc_neg
    · simp only [hQ, hQ', hp, ite_false]
      exact tendsto_const_nhds
  have hcm := (hu.isItoIntegrable_waveCurrent i.1).meas i
  have e : (fun p : ℝ × Ω => if 0 < p.1 then
      (if p.1 ≤ (N : ℝ) then quadLimDiff ψ' a N f i p.1 p.2 else 0) else 0) = fun p =>
      (if 0 < p.1 then waveCurrent ψ' i.1 i p.1 p.2 else 0) * (2 * Q' p) := by
    funext p
    by_cases h0 : 0 < p.1
    · by_cases hN : p.1 ≤ (N : ℝ)
      · have hct : cl p.1 = p.1 := by simp only [hcl]; rw [min_eq_left hN, max_eq_right h0.le]
        by_cases hω : quadSup ψ' a N p.2 ≠ ⊤
        · simp only [h0, hN, hω, ite_true, quadLimDiff, hQ', and_self, ne_eq,
            not_false_eq_true, hct, max_eq_left h0.le, quadD]
          ring
        · simp only [h0, hN, hω, ite_true, quadLimDiff, hQ', and_false, ite_false, ne_eq]
          simp
      · simp [h0, hN, hQ']
    · simp [h0]
  rw [e]
  exact hcm.mul (hQ'm.const_mul 2)

/-- **Pathwise energy estimate.** On `{N_T < ∞}`, for `s ∈ (0,T]`, with `R = N_T`, `P = P(s,·)`
and `v_K = V_K 𝟙_{[-K,K]} - V`: the energy density of the difference of the diffusions is at most
`8 ∑_y v_K(y)² P(y)`, this is at most `128 C² σ³ R³`, and it tends to `0` as `K → ∞`. -/
lemma quad_energy_pointwise (hu : IsUnitWave 𝓕 B ψ ψ' μ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    {T : ℝ} {f : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hfb : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    {ω : Ω} (hω : quadSup ψ' a T ω ≠ ⊤) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    ∃ G : ℕ → ℝ, (∀ K, ∑' i, ‖quadBoxDiff ψ' f K i s ω - quadLimDiff ψ' a T f i s ω‖ₑ ^ 2 ≤
        ENNReal.ofReal (8 * G K)) ∧
      (∀ K, 8 * G K ≤ 128 * C ^ 2 * quadSigma ^ 3 * (quadSup ψ' a T ω).toReal ^ 3) ∧
      Tendsto G atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ : ∃ R, R = (quadSup ψ' a T ω).toReal := ⟨_, rfl⟩
  have hD : QuadDecay a R (density ψ' ω s) := hR ▸ quadDecay_of_quadSup hω hs
  set P := density ψ' ω s with hP
  have hR0 := hD.R_nonneg
  have hσ := quadSigma_nonneg
  set v : ℕ → ℤ → ℝ := fun K y =>
    (if y ∈ Finset.Icc (-(K : ℤ)) K then
      2 * ∑ x' ∈ Finset.Icc (-(K : ℤ)) K, f s y x' * P x' else 0) -
      2 * quadRow (f s) P y with hv
  have hvb : ∀ K y, |v K y| ≤ 4 * C * R * quadSigma * quadW a y := fun K y => by
    have h1 := hD.abs_sum_row_le ha hC (hfb s hs) y (Finset.Icc (-(K : ℤ)) K)
    have h2 := hD.abs_row_le ha hC (hfb s hs) y
    have w : 0 ≤ C * R * quadSigma * quadW a y :=
      mul_nonneg (mul_nonneg (mul_nonneg hC hR0) hσ) (quadW_pos a y).le
    simp only [hv]
    split_ifs
    · calc _ ≤ |2 * ∑ x' ∈ Finset.Icc (-(K : ℤ)) K, f s y x' * P x'| +
            |2 * quadRow (f s) P y| := abs_sub _ _
        _ ≤ _ := by rw [abs_mul, abs_mul, abs_two]; linarith
    · rw [zero_sub, abs_neg, abs_mul, abs_two]; linarith
  have hP1 : ∀ x, P x ≤ 1 := fun x => hu.density_le_one ω hs.1 x
  refine ⟨fun K => ∑' y, v K y ^ 2 * P y, fun K => ?_, fun K => ?_, ?_⟩
  · have e : ∀ i, quadBoxDiff ψ' f K i s ω - quadLimDiff ψ' a T f i s ω =
        weightCurrent ψ' (fun _ y => v K y) i s ω := fun i => by
      rw [quadBoxDiff_eq (hsymm s hs), quadLimDiff_eq ha hC hω hs (hfb s hs), weightCurrent_sub]
    simp only [e]
    obtain ⟨h1, h2⟩ := quad_tsum_diff_sq_le hD.nonneg hP1 (hD.summable_sq_mul (hvb K))
    rw [tsum_enorm_weightCurrent_sq ψ' (fun _ y => v K y) s ω (by
      simpa only using h1)]
    exact ENNReal.ofReal_le_ofReal (by simpa only using h2)
  · have hb := fun y => hD.sq_mul_le (hvb K) y
    have hs1 := summable_quadRho.mul_left ((4 * C * R * quadSigma) ^ 2 * R)
    have := (hD.summable_sq_mul (hvb K)).tsum_le_tsum hb hs1
    rw [tsum_mul_left] at this
    have e : (4 * C * R * quadSigma) ^ 2 * R * quadSigma * 8 =
        128 * C ^ 2 * quadSigma ^ 3 * R ^ 3 := by ring
    rw [← hR, ← e]
    have : 0 ≤ (4 * C * R * quadSigma) ^ 2 * R := by positivity
    nlinarith [show ∑' x, quadRho x = quadSigma from rfl]
  · have hlim : ∀ y, Tendsto (fun K => v K y ^ 2 * P y) atTop (𝓝 0) := fun y => by
      have hr := ((hD.summable_row ha hC (hfb s hs) y).hasSum.comp
        Finset.tendsto_Icc_neg).const_mul 2
      have hv0 : Tendsto (fun K => v K y) atTop (𝓝 0) := by
        have h2 := hr.sub_const (2 * quadRow (f s) P y)
        rw [quadRow, sub_self] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_ge_atTop y.natAbs] with K hK
        have hy : y ∈ Finset.Icc (-(K : ℤ)) K := by
          simp only [Finset.mem_Icc]; omega
        simp only [hv, hy, ite_true, Function.comp_apply, quadRow]
      simpa using (hv0.pow 2).mul_const (P y)
    have := tendsto_tsum_of_dominated_convergence (f := fun K y => v K y ^ 2 * P y)
      (g := fun _ => (0 : ℝ))
      (bound := fun y => (4 * C * R * quadSigma) ^ 2 * R * quadRho y)
      (summable_quadRho.mul_left _) hlim (Eventually.of_forall fun K y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hD.nonneg y))]
        exact hD.sq_mul_le (hvb K) y)
    simpa using this

/-- **`L²` convergence of the martingale parts.** The energy on `[0,N]` of the difference of the
box diffusion and of `quadLimDiff` tends to `0`. -/
theorem tendsto_energy_quadBoxDiff [IsProbabilityMeasure μ] (hu : IsUnitWave 𝓕 B ψ ψ' μ)
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) {N : ℝ≥0} {f : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hfb : ∀ t ∈ Set.Icc (0 : ℝ) N, ∀ x₁ x₂, |f t x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    (hm : Measurable (quadSup ψ' a N)) (hint : ∫⁻ ω, quadSup ψ' a N ω ^ 3 ∂μ < ⊤)
    (hbm : ∀ K : ℕ, StochIntAux.EnergyMeas
      (fun i s ω => if s ≤ (N : ℝ) then quadBoxDiff ψ' f K i s ω else 0))
    (hdm : StochIntAux.EnergyMeas
      (fun i s ω => if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω else 0)) :
    Tendsto (fun K : ℕ => energy μ (fun i s ω =>
      (if s ≤ (N : ℝ) then quadBoxDiff ψ' f K i s ω else 0) -
        (if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω else 0)) N) atTop (𝓝 0) := by
  set c : ℝ := 128 * C ^ 2 * quadSigma ^ 3 with hc
  have hc0 : 0 ≤ c := by have := quadSigma_nonneg; positivity
  have hEm := fun K => (hbm K).sub hdm
  -- pathwise
  have hpath : ∀ ω, quadSup ψ' a N ω ≠ ⊤ → ∀ K,
      pathEnergy (fun i s ω => (if s ≤ (N : ℝ) then quadBoxDiff ψ' f K i s ω else 0) -
        (if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω else 0)) N ω ≤
        ENNReal.ofReal N * (ENNReal.ofReal c * quadSup ψ' a N ω ^ 3) ∧
      Tendsto (fun K => pathEnergy (fun i s ω =>
        (if s ≤ (N : ℝ) then quadBoxDiff ψ' f K i s ω else 0) -
        (if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω else 0)) N ω) atTop (𝓝 0) := by
    intro ω hω K
    have hR3 : ENNReal.ofReal (c * (quadSup ψ' a N ω).toReal ^ 3) =
        ENNReal.ofReal c * quadSup ψ' a N ω ^ 3 := by
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hω]
    have hpt := fun s (hs : s ∈ Set.Ioc (0 : ℝ) N) =>
      quad_energy_pointwise hu ha hC hsymm hfb hω ⟨hs.1.le, hs.2⟩
    have hle : ∀ K, ∀ s ∈ Set.Ioc (0 : ℝ) N, ∑' i,
        ‖(if s ≤ (N : ℝ) then quadBoxDiff ψ' f K i s ω else 0) -
          (if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω else 0)‖ₑ ^ 2 ≤
        ENNReal.ofReal c * quadSup ψ' a N ω ^ 3 := fun K s hs => by
      obtain ⟨G, h1, h2, -⟩ := hpt s hs
      simp only [hs.2, ite_true]
      rw [← hR3]
      exact (h1 K).trans (ENNReal.ofReal_le_ofReal (h2 K))
    refine ⟨?_, ?_⟩
    · calc _ ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) N, ENNReal.ofReal c * quadSup ψ' a N ω ^ 3 :=
            setLIntegral_mono' measurableSet_Ioc (hle K)
        _ = _ := by
            rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
              Real.volume_Ioc, sub_zero, mul_comm]
    · have hfin : ∫⁻ _ in Set.Ioc (0 : ℝ) N, ENNReal.ofReal c * quadSup ψ' a N ω ^ 3 ≠ ⊤ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc]
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.pow_ne_top hω)) ENNReal.ofReal_ne_top
      have := tendsto_lintegral_of_dominated_convergence'
        (μ := volume.restrict (Set.Ioc (0 : ℝ) N))
        (F := fun K s => ∑' i,
          ‖(if s ≤ (N : ℝ) then quadBoxDiff ψ' f K i s ω else 0) -
            (if s ≤ (N : ℝ) then quadLimDiff ψ' a N f i s ω else 0)‖ₑ ^ 2)
        (f := fun _ => 0) (fun _ => ENNReal.ofReal c * quadSup ψ' a N ω ^ 3)
        (fun K => StochIntAux.aemeasurable_tsum_sq (hEm K) N ω)
        (fun K => (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ (hle K))) hfin
        ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_))
      · simpa [pathEnergy] using this
      · obtain ⟨G, h1, -, h3⟩ := hpt s hs
        have h4 : Tendsto (fun K => ENNReal.ofReal (8 * G K)) atTop (𝓝 0) := by
          simpa using ENNReal.tendsto_ofReal (h3.const_mul 8)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4
          (fun _ => zero_le) fun K => ?_
        simp only [hs.2, ite_true]
        exact h1 K
  have hae : ∀ᵐ ω ∂μ, quadSup ψ' a N ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (hm.pow_const 3) hint.ne] with ω hω h
    rw [h, ENNReal.top_pow (by norm_num)] at hω
    exact lt_irrefl _ hω
  have := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (fun ω => ENNReal.ofReal N * (ENNReal.ofReal c * quadSup ψ' a N ω ^ 3))
    (fun K => StochIntAux.measurable_pathEnergy (hEm K) N)
    (fun K => hae.mono fun ω hω => (hpath ω hω K).1)
    (by
      rw [lintegral_const_mul _ ((hm.pow_const 3).const_mul _),
        lintegral_const_mul _ (hm.pow_const 3)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint.ne))
    (hae.mono fun ω hω => (hpath ω hω 0).2)
  simpa [energy] using this

end IsUnitWave

end QSSEPtoKPZ
