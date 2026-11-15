/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.WeightCurrent
public import QSSEPtoKPZ.WaveFunction.ItoLimit

/-!
# Linear functionals of `P` with bounded weights are Itô processes (task D4)

See `docs/stage2-design.md`, Section 1.2 (g), (h). Let `ψ'` be a unit-norm version of the wave
function (`IsUnitWave`), `N ≥ 0`, and let `w_t(x)` be a weight, `C¹` in `t ∈ [0, N]` (derivative
`w'_t(x)`, continuous in `t`, one-sided at `0` and `N`). Then:

* `IsUnitWave.isItoProcessUpTo_weight_finset`: for every finite `S ⊆ ℤ`,
  `d ∑_{x ∈ S} w_t(x) P(t,x) = ∑_{x ∈ S} (∂ₜw_t(x) P(t,x) + w_t(x) ΔP(t,x)) dt
    + ∑_{x ∈ S} w_t(x) (dJ(x-1) - dJ(x))`
  (product rule for `w_t(x) · P(t,x)`, then a finite sum);
* `IsUnitWave.isItoProcessUpTo_weight`: if moreover `|w_t(x)|, |∂ₜw_t(x)| ≤ C` on `[0, N]`,
  `d ∑ₓ w_t(x) P(t,x) = ∑ₓ (∂ₜw_t + Δw_t)(x) P(t,x) dt + ∑ᵢ (weightCurrent ψ' w)ᵢ dBᵢ`,
  where `weightCurrent ψ' w (y,j) = (w(y+1) - w(y)) (c_y)_{(y,j)}`, i.e. the martingale part is
  `∫ ∑_y (w_s(y+1) - w_s(y)) dJ_s(y)`, with bracket density
  `∑_y 2 (w_s(y+1) - w_s(y))² P(s,y) P(s,y+1)` (`hasSum_weightCurrent_sq`).

Proof of the second statement: take the boxes `S_K = [-K, K]` and let `K → ∞`
(`IsItoProcessUpTo.of_tendsto_const`): the processes and the drifts converge pathwise
(dominated convergence, `∑ₓ P = 1`, summation by parts `∑ w ΔP = ∑ (Δw) P`), and the energy of
the difference of the diffusions is at most `8 C² 𝔼 ∫_0^N ∑_{x ∉ S_K} P(s,x) ds → 0`
(conservation of the mass).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

namespace IsUnitWave

/-- `P(t,x)` is `𝓕ᵃ_t`-measurable. -/
lemma weight_measurable_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) :
    Measurable[nullAug μ 𝓕 t] fun ω => density ψ' ω t x :=
  (continuous_norm.pow 2).measurable.comp (hu.measurable_apply t x)

/-- Every path `t ↦ P(t,x)` is continuous on `[0, ∞)`. -/
lemma weight_continuous_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    Continuous fun t : ℝ≥0 => density ψ' ω t x :=
  (hu.continuous_apply ω x).norm.pow 2

/-- Every path `s ↦ P(s,x)` is continuous on `[0, ∞)`, as a function on `ℝ`. -/
lemma weight_continuousOn_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    ContinuousOn (fun s => density ψ' ω s x) (Set.Ici 0) :=
  (wavePath_continuousOn (hu.continuous_apply ω x)).norm.pow 2

/-- Every path `s ↦ ΔP(s,x)` is continuous on `[0, ∞)`. -/
lemma weight_continuousOn_lap_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) (x : ℤ) :
    ContinuousOn (fun s => lap (density ψ' ω s) x) (Set.Ici 0) := by
  simp only [lap]
  exact ((hu.weight_continuousOn_density ω _).add (hu.weight_continuousOn_density ω _)).sub
    (continuousOn_const.mul (hu.weight_continuousOn_density ω _))

/-- `∑ₓ P(s,x) = 1` for `s ≥ 0`. -/
lemma weight_tsum_density (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s) :
    ∑' x, density ψ' ω s x = 1 :=
  (hu.hasSum_density ω ⟨s, hs⟩).tsum_eq

/-- `‖ψ'_s‖ = 1` for `s ≥ 0`. -/
lemma weight_norm_eq_one (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s) :
    ‖ψ' s ω‖ = 1 :=
  hu.norm_eq_one ω ⟨s, hs⟩

/-- `∑_{x ∈ S} P(s, x + c) ≤ 1` for `s ≥ 0`. -/
lemma weight_sum_density_add_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s)
    (S : Finset ℤ) (c : ℤ) : ∑ x ∈ S, density ψ' ω s (x + c) ≤ 1 := by
  have h := (weight_summable_density_add ψ' ω s c).sum_le_tsum S
    (fun x _ => density_nonneg ψ' ω s _)
  have e : ∑' x, density ψ' ω s (x + c) = ∑' x, density ψ' ω s x :=
    (Equiv.addRight c).tsum_eq (density ψ' ω s)
  rwa [e, hu.weight_tsum_density ω hs] at h

/-- `|ΔP(s,x)| ≤ P(s,x+1) + P(s,x-1) + 2 P(s,x)`. -/
lemma weight_abs_lap_density_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) (x : ℤ) :
    |lap (density ψ ω s) x| ≤
      density ψ ω s (x + 1) + density ψ ω s (x + -1) + 2 * density ψ ω s x := by
  have h1 := density_nonneg ψ ω s (x + 1)
  have h2 := density_nonneg ψ ω s (x - 1)
  have h3 := density_nonneg ψ ω s x
  rw [lap, ← sub_eq_add_neg, abs_le]
  constructor <;> linarith

/-- **One site.** For a weight `w_t(x)`, `C¹` in `t ∈ [0, N]`, `w_t(x) P(t,x)` is an Itô process
up to `N`, with drift `∂ₜw_t(x) P(t,x) + w_t(x) ΔP(t,x)` and diffusion
`w_t(x) (c_{x-1} - c_x)` (product rule). -/
theorem isItoProcessUpTo_weight_site [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {w w' : ℝ → ℤ → ℝ}
    (hw : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt (w · x) (w' t x) (Set.Icc 0 N) t)
    (hw' : ∀ x, ContinuousOn (w' · x) (Set.Icc 0 N)) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N) (fun t ω => w t x * density ψ' ω t x)
      (fun s ω => w' s x * density ψ' ω s x + w s x * lap (density ψ' ω s) x)
      (fun i s ω => w s x * (waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω)) := by
  have hc : ContinuousOn (w · x) (Set.Icc 0 N) := fun t ht => (hw x t ht).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw' x)
  set α : ℝ → ℝ := fun t => w (min t N) x with hαdef
  have hα : ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt α (w' t x) (Set.Icc 0 N) t :=
    fun t ht => (hw x t ht).congr (fun y hy => by simp [α, min_eq_left hy.2])
      (by simp [α, min_eq_left ht.2])
  have hX := isItoProcessUpTo_deterministic (𝓖 := nullAug μ 𝓕) (μ := μ) (B := B) hB.nullAug
    (τ := fun _ => N) (T := N) (fun _ => le_rfl) hα (hw' x)
  have hY := hu.isItoProcessUpTo_density hB N x
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => (fun (t : ℝ) (_ : Ω) => α t) t ω := fun ω =>
    hc.comp_continuous (NNReal.continuous_coe.min continuous_const)
      fun t => ⟨le_min t.2 N.2, min_le_right _ _⟩
  have hP := hX.mul hB.nullAug (isStoppingTime_const _ N) ⟨N, fun _ => le_rfl⟩ hY hXc
    (hu.weight_continuous_density · x) (fun _ => measurable_const) (fun t => hu.weight_measurable_density t x)
    (K := max (max C₁ C₂) 4) (fun ω s hs0 hsN => by
      have hsN' : s ≤ N := hsN
      have hs : s ∈ Set.Icc (0 : ℝ) N := ⟨hs0, hsN'⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [α, min_eq_left hsN']
        exact (hC₁ s hs).trans ((le_max_left _ _).trans (le_max_left _ _))
      · rw [abs_of_nonneg (density_nonneg ψ' ω s x)]
        exact (hu.density_le_one ω hs0 x).trans (by norm_num)
      · exact (hC₂ s hs).trans ((le_max_right _ _).trans (le_max_left _ _))
      · refine (weight_abs_lap_density_le ψ' ω s x).trans ((le_trans ?_ (le_max_right _ _)))
        have := hu.density_le_one ω hs0 (x + 1)
        have := hu.density_le_one ω hs0 (x + -1)
        have := hu.density_le_one ω hs0 x
        have := density_nonneg ψ' ω s (x + 1)
        linarith
      · simp only [Pi.zero_apply]
        simp
      · exact (hu.tsum_waveCurrent_sub_succ_sq_le x hs0 ω).trans (le_max_right _ _))
  refine hP.congr_const (fun ω t _ htN => by simp [α, min_eq_left htN])
    (fun ω s _ hsN => ?_) (fun i s ω hsN => by simp [α, min_eq_left hsN])
  simp [α, min_eq_left hsN]
  ring

/-- **Finite sums.** For a weight `w_t(x)`, `C¹` in `t ∈ [0, N]`, and a finite `S ⊆ ℤ`,
`∑_{x ∈ S} w_t(x) P(t,x)` is an Itô process up to `N`, with drift
`∑_{x ∈ S} (∂ₜw_t(x) P(t,x) + w_t(x) ΔP(t,x))` and diffusion
`∑_{x ∈ S} w_t(x) (c_{x-1} - c_x)`. -/
theorem isItoProcessUpTo_weight_finset [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {w w' : ℝ → ℤ → ℝ}
    (hw : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt (w · x) (w' t x) (Set.Icc 0 N) t)
    (hw' : ∀ x, ContinuousOn (w' · x) (Set.Icc 0 N)) (S : Finset ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => ∑ x ∈ S, w t x * density ψ' ω t x)
      (fun s ω => ∑ x ∈ S, (w' s x * density ψ' ω s x + w s x * lap (density ψ' ω s) x))
      (fun i s ω => ∑ x ∈ S, w s x * (waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω)) :=
  IsItoProcessUpTo.finset_sum hB.nullAug S fun x _ =>
    hu.isItoProcessUpTo_weight_site hB hw hw' x

/-! ### Pointwise facts for bounded weights -/

/-- The drift series `∑ₓ (∂ₜw(x) P(x) + w(x) ΔP(x))` converges, equals `∑ₓ (∂ₜw + Δw)(x) P(x)`
(summation by parts), and its partial sums over finite sets are bounded by `5 C`, when
`|w|, |∂ₜw| ≤ C`. -/
lemma weight_drift_facts (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s)
    {w w' : ℤ → ℝ} {C : ℝ} (hb : ∀ x, |w x| ≤ C ∧ |w' x| ≤ C) :
    Summable (fun x => w' x * density ψ' ω s x + w x * lap (density ψ' ω s) x) ∧
    ∑' x, (w' x * density ψ' ω s x + w x * lap (density ψ' ω s) x) =
      ∑' x, (w' x + lap w x) * density ψ' ω s x ∧
    ∀ S : Finset ℤ,
      |∑ x ∈ S, (w' x * density ψ' ω s x + w x * lap (density ψ' ω s) x)| ≤ 5 * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0).1
  have hP := weight_summable_density ψ' ω s
  have hP1 := weight_summable_density_add ψ' ω s 1
  have hP2 := weight_summable_density_add ψ' ω s (-1)
  have hlapP : Summable fun x => lap (density ψ' ω s) x := by
    have := (hP1.add hP2).sub (hP.mul_left 2)
    refine this.congr fun x => ?_
    simp [lap, sub_eq_add_neg]
  have h1 := weight_summable_mul_of_abs_le (fun x => (hb x).2) hP
  have h2 := weight_summable_mul_of_abs_le (fun x => (hb x).1) hlapP
  have hlapw : ∀ x, |lap w x| ≤ 4 * C := fun x => by
    have a := (hb (x + 1)).1
    have b := (hb (x - 1)).1
    have c := (hb x).1
    rw [abs_le] at a b c ⊢
    simp only [lap]
    constructor <;> linarith
  refine ⟨h1.add h2, ?_, fun S => ?_⟩
  · rw [h1.tsum_add h2, tsum_mul_lap_eq (fun x => (hb x).1) hP,
      ← h1.tsum_add (weight_summable_mul_of_abs_le hlapw hP)]
    congr 1
    funext x
    ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ x, |w' x * density ψ' ω s x + w x * lap (density ψ' ω s) x| ≤
        C * density ψ' ω s x + C * (density ψ' ω s (x + 1) + density ψ' ω s (x + -1) +
          2 * density ψ' ω s x) := fun x => by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (density_nonneg ψ' ω s x)]
        exact mul_le_mul_of_nonneg_right (hb x).2 (density_nonneg ψ' ω s x)
      · rw [abs_mul]
        exact mul_le_mul (hb x).1 (weight_abs_lap_density_le ψ' ω s x) (abs_nonneg _) hC
    refine (Finset.sum_le_sum fun x _ => hterm x).trans ?_
    have e0 := hu.weight_sum_density_add_le ω hs S 0
    have e1 := hu.weight_sum_density_add_le ω hs S 1
    have e2 := hu.weight_sum_density_add_le ω hs S (-1)
    simp only [add_zero] at e0
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left e0 hC
    have := mul_le_mul_of_nonneg_left e1 hC
    have := mul_le_mul_of_nonneg_left e2 hC
    linarith

/-- **Tail bound for the diffusion.** If `|v| ≤ C` and `v = 0` on `S`, then
`∑_y (v(y+1) - v(y))² · 2 P(y) P(y+1) ≤ 8 C² (1 - ∑_{x ∈ S} P(x))`. -/
lemma weight_tail_le (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s)
    {v : ℤ → ℝ} {C : ℝ} (hb : ∀ x, |v x| ≤ C) (S : Finset ℤ) (hS : ∀ x ∈ S, v x = 0) :
    ∑' y, (v (y + 1) - v y) ^ 2 * (2 * density ψ' ω s y * density ψ' ω s (y + 1)) ≤
      8 * C ^ 2 * (1 - ∑ x ∈ S, density ψ' ω s x) := by
  set P := density ψ' ω s with hPdef
  obtain ⟨u, hudef⟩ : ∃ u : ℤ → ℝ, u = fun y => P y - (S : Set ℤ).indicator P y := ⟨_, rfl⟩
  have hP := weight_summable_density ψ' ω s
  have hind : Summable ((S : Set ℤ).indicator P) :=
    summable_of_ne_finset_zero (s := S) fun y hy =>
      Set.indicator_of_notMem (by rwa [Finset.mem_coe]) _
  have hu' : Summable u := by rw [hudef]; exact hP.sub hind
  have hu1 : Summable fun y => u (y + 1) := (Equiv.addRight (1 : ℤ)).summable_iff.2 hu'
  have hsumL := summable_weightCurrent_fiber ψ' (C := C) (s := s) (w := fun _ => v) hb ω
  -- `v(y)² P(y) ≤ C² u(y)`
  have hvu : ∀ y, v y ^ 2 * P y ≤ C ^ 2 * u y := by
    intro y
    have hp := density_nonneg ψ' ω s y
    by_cases hy : y ∈ S
    · simp [hudef, hS y hy, Set.indicator_of_mem (Finset.mem_coe.2 hy)]
    · have hv2 : v y ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb y) 2
      simp only [hudef, Set.indicator_of_notMem (show y ∉ (S : Set ℤ) from hy), sub_zero]
      exact mul_le_mul_of_nonneg_right hv2 hp
  have hterm : ∀ y, (v (y + 1) - v y) ^ 2 * (2 * P y * P (y + 1)) ≤
      4 * C ^ 2 * (u (y + 1) + u y) := by
    intro y
    have hp0 := density_nonneg ψ' ω s y
    have hp1 := density_nonneg ψ' ω s (y + 1)
    have hq0 := hu.density_le_one ω hs y
    have hq1 := hu.density_le_one ω hs (y + 1)
    have h1 := hvu y
    have h2 := hvu (y + 1)
    have hd : (v (y + 1) - v y) ^ 2 ≤ 2 * v (y + 1) ^ 2 + 2 * v y ^ 2 := by
      nlinarith [sq_nonneg (v (y + 1) + v y)]
    have hpq : 0 ≤ P y * P (y + 1) := mul_nonneg hp0 hp1
    have k1 : v (y + 1) ^ 2 * (P y * P (y + 1)) ≤ v (y + 1) ^ 2 * P (y + 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    have k2 : v y ^ 2 * (P y * P (y + 1)) ≤ v y ^ 2 * P y :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hd hpq]
  have htu : ∑' y, u y = 1 - ∑ x ∈ S, P x := by
    rw [hudef, hP.tsum_sub hind, hu.weight_tsum_density ω hs,
      tsum_eq_sum (s := S) fun y hy =>
        Set.indicator_of_notMem (by rwa [Finset.mem_coe]) _]
    congr 1
    exact Finset.sum_congr rfl fun y hy =>
      Set.indicator_of_mem (by rwa [Finset.mem_coe]) _
  have htu1 : ∑' y, u (y + 1) = ∑' y, u y := (Equiv.addRight (1 : ℤ)).tsum_eq u
  calc _ ≤ ∑' y, 4 * C ^ 2 * (u (y + 1) + u y) :=
        hsumL.tsum_le_tsum hterm ((hu1.add hu').mul_left _)
    _ = 8 * C ^ 2 * (1 - ∑ x ∈ S, P x) := by
        rw [tsum_mul_left, hu1.tsum_add hu', htu1, htu]
        ring

/-- **Linear functionals with bounded weights are Itô processes.** Let `w_t(x)` be `C¹` in
`t ∈ [0, N]` (derivative `w'_t(x)`, continuous in `t`, one-sided at `0` and `N`) with
`|w_t(x)|, |w'_t(x)| ≤ C`. Then `∑ₓ w_t(x) P(t,x)` is an Itô process up to `N`:
`d ∑ₓ w_t(x) P(t,x) = ∑ₓ (∂ₜw_t + Δw_t)(x) P(t,x) dt + ∑_y (w_t(y+1) - w_t(y)) dJ_t(y)`,
the diffusion coefficients being `weightCurrent ψ' w`. -/
theorem isItoProcessUpTo_weight [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {w w' : ℝ → ℤ → ℝ} {C : ℝ}
    (hw : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt (w · x) (w' t x) (Set.Icc 0 N) t)
    (hw' : ∀ x, ContinuousOn (w' · x) (Set.Icc 0 N))
    (hbd : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, |w t x| ≤ C ∧ |w' t x| ≤ C) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => ∑' x, w t x * density ψ' ω t x)
      (fun s ω => ∑' x, (w' s x + lap (w s) x) * density ψ' ω s x)
      (weightCurrent ψ' w) := by
  classical
  have hbox := fun K : ℕ => hu.isItoProcessUpTo_weight_finset hB hw hw'
    (Finset.Icc (-(K : ℤ)) K)
  have hcw : ∀ x, ContinuousOn (w · x) (Set.Icc 0 N) := fun x t ht =>
    (hw x t ht).continuousWithinAt
  have hsubI : ∀ {t : ℝ}, 0 ≤ t → t ≤ N → Set.uIoc 0 t ⊆ Set.Icc 0 N := fun ht0 htN s hs => by
    rw [Set.uIoc_of_le ht0] at hs; exact ⟨hs.1.le, hs.2.trans htN⟩
  -- pointwise facts on the drifts
  have hdr := fun ω s (hs : s ∈ Set.Icc (0 : ℝ) N) =>
    hu.weight_drift_facts ω hs.1 (w := w s) (w' := w' s) (fun x => hbd x s hs)
  have hdlim : ∀ ω s, s ∈ Set.Icc (0 : ℝ) N → Tendsto (fun K : ℕ =>
      ∑ x ∈ Finset.Icc (-(K : ℤ)) K, (w' s x * density ψ' ω s x +
        w s x * lap (density ψ' ω s) x)) atTop
      (𝓝 (∑' x, (w' s x + lap (w s) x) * density ψ' ω s x)) := fun ω s hs => by
    rw [← (hdr ω s hs).2.1]
    exact (hdr ω s hs).1.hasSum.comp Finset.tendsto_Icc_neg
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
    set G : ℕ → ℝ → Ω → ℝ≥0∞ := fun K s ω => ENNReal.ofReal
      (8 * C ^ 2 * (1 - ∑ x ∈ Finset.Icc (-(K : ℤ)) K, density ψ' ω s x)) with hGdef
    have hDG : ∀ K ω s, s ∈ Set.Ioc (0 : ℝ) N → ∑' i, ‖D K i s ω‖ₑ ^ 2 ≤ G K s ω := by
      intro K ω s hs
      have hsN : s ≤ (N : ℝ) := hs.2
      set v : ℝ → ℤ → ℝ := fun s x =>
        (if x ∈ Finset.Icc (-(K : ℤ)) K then w s x else 0) - w s x with hvdef
      have hDv : ∀ i, D K i s ω = weightCurrent ψ' v i s ω := fun i => by
        simp only [hDdef, hsN, ite_true]
        rw [sum_mul_waveCurrent_sub, weightCurrent_sub]
      have hvb : ∀ x, |v s x| ≤ C := fun x => by
        by_cases hx : x ∈ Finset.Icc (-(K : ℤ)) K
        · simp only [hvdef, hx, ↓reduceIte, sub_self, abs_zero]
          exact (abs_nonneg _).trans (hbd x s ⟨hs.1.le, hsN⟩).1
        · simp only [hvdef, hx, ↓reduceIte, zero_sub, abs_neg]
          exact (hbd x s ⟨hs.1.le, hsN⟩).1
      simp only [hDv]
      rw [tsum_enorm_weightCurrent_sq ψ' v s ω (summable_weightCurrent_fiber ψ' hvb ω)]
      exact ENNReal.ofReal_le_ofReal (hu.weight_tail_le ω hs.1.le hvb _ fun x hx => by
        simp only [hvdef, hx, ↓reduceIte, sub_self])
    have hGb : ∀ K s ω, G K s ω ≤ ENNReal.ofReal (8 * C ^ 2) := fun K s ω =>
      ENNReal.ofReal_le_ofReal (by
        have : 0 ≤ ∑ x ∈ Finset.Icc (-(K : ℤ)) K, density ψ' ω s x :=
          Finset.sum_nonneg fun x _ => density_nonneg ψ' ω s x
        nlinarith [sq_nonneg C])
    have hpe : ∀ K ω, pathEnergy (D K) N ω ≤ ∫⁻ s in Set.Ioc (0 : ℝ) N, G K s ω :=
      fun K ω => setLIntegral_mono' measurableSet_Ioc fun s hs => hDG K ω s hs
    have hfin : ∫⁻ _ in Set.Ioc (0 : ℝ) N, ENNReal.ofReal (8 * C ^ 2) ≠ ∞ := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hGlim : ∀ ω, Tendsto (fun K => ∫⁻ s in Set.Ioc (0 : ℝ) N, G K s ω) atTop (𝓝 0) := by
      intro ω
      have := tendsto_lintegral_of_dominated_convergence'
        (μ := volume.restrict (Set.Ioc (0 : ℝ) N))
        (F := fun K s => G K s ω) (f := fun _ => 0) (fun _ => ENNReal.ofReal (8 * C ^ 2))
        (fun K => ?_) (fun K => ae_of_all _ fun s => hGb K s ω) hfin
        ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_))
      · simpa using this
      · refine ContinuousOn.aemeasurable ?_ measurableSet_Ioc
        exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
          (continuousOn_const.sub (continuousOn_finsetSum _ fun x _ =>
            (hu.weight_continuousOn_density ω x).mono fun s hs => le_of_lt hs.1)))
      · have h1 := tendsto_sum_Icc_density ψ' ω s
        rw [hu.weight_norm_eq_one ω hs.1.le, one_pow] at h1
        have := ENNReal.tendsto_ofReal ((h1.const_sub 1).const_mul (8 * C ^ 2))
        simpa using this
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
      (fun _ => ∫⁻ _ in Set.Ioc (0 : ℝ) N, ENNReal.ofReal (8 * C ^ 2)) hEm
      (fun K => ae_of_all _ fun ω => (hpe K ω).trans (lintegral_mono fun s => hGb K s ω))
      (by rw [lintegral_const, measure_univ, mul_one]; exact hfin)
      (ae_of_all _ fun ω => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hGlim ω) (fun _ => zero_le) fun K => hpe K ω)
    simpa [energy] using this
  · -- the limit drift is integrable on `[0, N]`
    refine ae_of_all _ fun ω => ?_
    have hsub := hsubI (t := N) N.2 le_rfl
    have hvol : volume (Set.uIoc (0 : ℝ) N) < ∞ := by
      rw [Set.uIoc_of_le (NNReal.coe_nonneg N), Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound hvol ?_ (5 * C) ?_
    · exact aestronglyMeasurable_of_tendsto_ae atTop
        (fun K => ((hdcont ω K).mono hsub).aestronglyMeasurable measurableSet_uIoc)
        ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs =>
          hdlim ω s (hsub hs)))
    · refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => ?_)
      exact le_of_tendsto ((continuous_norm.tendsto _).comp (hdlim ω s (hsub hs)))
        (Eventually.of_forall fun K => by
          rw [Function.comp_apply, Real.norm_eq_abs]; exact (hdr ω s (hsub hs)).2.2 _)
  · -- the processes converge
    exact ae_of_all _ fun ω t ht0 htN =>
      (weight_summable_mul_of_abs_le (fun x => (hbd x t ⟨ht0, htN⟩).1)
        (weight_summable_density ψ' ω t)).hasSum.comp Finset.tendsto_Icc_neg
  · -- the integrated drifts converge (dominated convergence)
    exact ae_of_all _ fun ω t ht0 htN =>
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 5 * C)
        (Eventually.of_forall fun K =>
          ((hdcont ω K).mono (hsubI ht0 htN)).aestronglyMeasurable measurableSet_uIoc)
        (Eventually.of_forall fun K => ae_of_all _ fun s hs => by
          rw [Real.norm_eq_abs]; exact (hdr ω s (hsubI ht0 htN hs)).2.2 _)
        intervalIntegrable_const
        (ae_of_all _ fun s hs => hdlim ω s (hsubI ht0 htN hs))

/-- **Bracket of the martingale part, bounded weights** (Lemma 2.3 (1) for bounded weights and
the unit-norm version `ψ'`). Under the hypotheses of `isItoProcessUpTo_weight`,
`M_t = ∑ₓ w_t(x) P(t,x) - w_0(0) - ∫_0^t ∑ₓ (∂ₛw_s + Δw_s)(x) P(s,x) ds` is a continuous `L²`
martingale on `[0, N]` for `𝓕` with
`⟨M⟩_t = ∫_0^t ∑ₓ 2 (w_s(x+1) - w_s(x))² P(s,x) P(s,x+1) ds`. -/
theorem hasBracket_weight [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {w w' : ℝ → ℤ → ℝ} {C : ℝ}
    (hw : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt (w · x) (w' t x) (Set.Icc 0 N) t)
    (hw' : ∀ x, ContinuousOn (w' · x) (Set.Icc 0 N))
    (hbd : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) N, |w t x| ≤ C ∧ |w' t x| ≤ C) :
    HasBracket N 𝓕
      (fun t ω => ∑' x, w t x * density ψ' ω t x - w 0 0 -
        ∫ s in (0 : ℝ)..t, ∑' x, (w' s x + lap (w s) x) * density ψ' ω s x)
      (fun t ω => ∫ s in (0 : ℝ)..t, ∑' x,
        2 * (w s (x + 1) - w s x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1)) μ := by
  have hX := hu.isItoProcessUpTo_weight hB hw hw' hbd
  have hbr := hasBracket_stochInt hB.nullAug hX.integrable N
  refine hasBracket_nullAug_iff.1 (hbr.congr (NNReal.coe_nonneg N) ?_ ?_)
  · filter_upwards [hX.eq] with ω hω t ht
    have e := hω ⟨t, ht.1⟩
    have hm : min (⟨t, ht.1⟩ : ℝ≥0) N = ⟨t, ht.1⟩ := min_eq_left ht.2
    erw [hm] at e
    have h0 : ∑' x, w 0 x * density ψ' ω 0 x = w 0 0 := by
      have : ∀ x, w 0 x * density ψ' ω 0 x = if x = 0 then w 0 0 else 0 := fun x => by
        rw [density, hu.init_apply ω x]
        split_ifs with h
        · subst h; simp
        · simp
      simp only [this, tsum_ite_eq]
    change ∑' x, w t x * density ψ' ω t x = (∑' x, w 0 x * density ψ' ω 0 x +
      ∫ s in (0 : ℝ)..t, ∑' x, (w' s x + lap (w s) x) * density ψ' ω s x) +
      stochInt (nullAug μ 𝓕) μ B (fun i s ω => if s ≤ (N : ℝ) then weightCurrent ψ' w i s ω
        else 0) t ω at e
    rw [e, h0]
    ring
  · refine ae_of_all _ fun ω t ht => intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    have hsN : s ≤ (N : ℝ) := hs.2.trans ht.2
    have hb : ∀ y, |w s y| ≤ C := fun y => (hbd y s ⟨hs.1, hsN⟩).1
    simp only [hsN, ite_true]
    rw [(hasSum_weightCurrent_sq ψ' w s ω (summable_weightCurrent_fiber ψ' hb ω)).tsum_eq]
    congr 1
    funext y
    ring

end IsUnitWave

end QSSEPtoKPZ
