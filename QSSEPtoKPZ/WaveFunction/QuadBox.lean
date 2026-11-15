/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.BoundedWeights
public import QSSEPtoKPZ.WaveFunction.QuadDrift

/-!
# Quadratic functionals of `P` on a box (task D6)

The first step of the proof of Lemma 2.3 (2): for a weight `f_t(x₁,x₂)`, `C¹` in time,

* `quad_tsum_currentDiff_mul`: the covariation density of `P(x₁)` and `P(x₂)`,
  `∑ᵢ (c_{x₁-1} - c_{x₁})ᵢ (c_{x₂-1} - c_{x₂})ᵢ = X(x₁,x₂)` (`quadCross`, by (2.5));
* `IsUnitWave.isItoProcessUpTo_quad_pair`: `f_t(x₁,x₂) P(t,x₁) P(t,x₂)` is an Itô process up to
  `N`, with drift `quadDriftTerm` and diffusion
  `f (P(x₁) (c_{x₂-1} - c_{x₂}) + P(x₂) (c_{x₁-1} - c_{x₁}))` (product rule, twice);
* `IsUnitWave.isItoProcessUpTo_quad_finset`: the sum over a finite set of pairs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `∑ᵢ (c_x)ᵢ (c_y)ᵢ = 𝟙_{x=y} 2 P(x) P(x+1)` ((2.5)). -/
lemma quad_tsum_waveCurrent_mul (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x y : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, waveCurrent ψ x i s ω * waveCurrent ψ y i s ω =
      if x = y then 2 * density ψ ω s x * density ψ ω s (x + 1) else 0 := by
  split_ifs with h
  · subst h; simp only [← sq]; exact tsum_waveCurrent_sq ψ x s ω
  · exact tsum_waveCurrent_mul_waveCurrent ψ h s ω

/-- **Covariation of `P(x₁)` and `P(x₂)`**:
`∑ᵢ (c_{x₁-1} - c_{x₁})ᵢ (c_{x₂-1} - c_{x₂})ᵢ = X(x₁,x₂)`. -/
lemma quad_tsum_currentDiff_mul (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x₁ x₂ : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, (waveCurrent ψ (x₁ - 1) i s ω - waveCurrent ψ x₁ i s ω) *
      (waveCurrent ψ (x₂ - 1) i s ω - waveCurrent ψ x₂ i s ω) =
      quadCross (density ψ ω s) x₁ x₂ := by
  have hs : ∀ x y, Summable fun i => waveCurrent ψ x i s ω * waveCurrent ψ y i s ω :=
    fun x y => summable_waveCurrent_mul ψ x _ s ω
  have e : (fun i => (waveCurrent ψ (x₁ - 1) i s ω - waveCurrent ψ x₁ i s ω) *
      (waveCurrent ψ (x₂ - 1) i s ω - waveCurrent ψ x₂ i s ω)) = fun i =>
      waveCurrent ψ (x₁ - 1) i s ω * waveCurrent ψ (x₂ - 1) i s ω -
        waveCurrent ψ (x₁ - 1) i s ω * waveCurrent ψ x₂ i s ω -
        waveCurrent ψ x₁ i s ω * waveCurrent ψ (x₂ - 1) i s ω +
        waveCurrent ψ x₁ i s ω * waveCurrent ψ x₂ i s ω := by
    funext i; ring
  rw [e, ((hs _ _).sub (hs _ _) |>.sub (hs _ _)).tsum_add (hs _ _),
    ((hs _ _).sub (hs _ _)).tsum_sub (hs _ _), (hs _ _).tsum_sub (hs _ _)]
  simp only [quad_tsum_waveCurrent_mul, quadCross]
  rcases (by omega : x₂ = x₁ ∨ x₂ = x₁ - 1 ∨ x₂ = x₁ + 1 ∨
      (x₂ ≠ x₁ ∧ x₂ ≠ x₁ - 1 ∧ x₂ ≠ x₁ + 1)) with rfl | rfl | rfl | ⟨h1, h2, h3⟩ <;>
    split_ifs <;> first
      | (exfalso; omega)
      | (simp only [sub_add_cancel]; ring)
      | ring

namespace IsUnitWave

/-- `|X(x₁,x₂)| ≤ 36` for the unit-norm version. -/
lemma abs_quadCross_le_unit (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s)
    (x₁ x₂ : ℤ) : |quadCross (density ψ' ω s) x₁ x₂| ≤ 36 := by
  have h := QSSEPtoKPZ.abs_quadCross_le (density_nonneg ψ' ω s) x₁ x₂
  have b : ∀ x, quadP3 (density ψ' ω s) x ≤ 3 := fun x => by
    unfold quadP3
    have := hu.density_le_one ω hs (x - 1); have := hu.density_le_one ω hs x
    have := hu.density_le_one ω hs (x + 1)
    linarith
  have p1 := quadP3_nonneg (density_nonneg ψ' ω s) x₁
  have p2 := quadP3_nonneg (density_nonneg ψ' ω s) x₂
  nlinarith [b x₁, b x₂, mul_le_mul (b x₁) (b x₂) p2 (by norm_num)]

/-- `|ΔP(s,x)| ≤ 4` for the unit-norm version. -/
lemma abs_lap_density_le_four (hu : IsUnitWave 𝓕 B ψ ψ' μ) (ω : Ω) {s : ℝ} (hs : 0 ≤ s)
    (x : ℤ) : |lap (density ψ' ω s) x| ≤ 4 := by
  refine (weight_abs_lap_density_le ψ' ω s x).trans ?_
  have := hu.density_le_one ω hs (x + 1)
  have := hu.density_le_one ω hs (x + -1)
  have := hu.density_le_one ω hs x
  linarith

/-- **One pair of sites.** For a weight `f_t(x₁,x₂)`, `C¹` in `t ∈ [0, N]`,
`f_t(x₁,x₂) P(t,x₁) P(t,x₂)` is an Itô process up to `N` with drift `quadDriftTerm` and
diffusion `f (P(x₁) (c_{x₂-1} - c_{x₂}) + P(x₂) (c_{x₁-1} - c_{x₁}))`. -/
theorem isItoProcessUpTo_quad_pair [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {f f' : ℝ → ℤ → ℤ → ℝ}
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc (0 : ℝ) N,
      HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 N) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 N)) (x₁ x₂ : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => f t x₁ x₂ * density ψ' ω t x₁ * density ψ' ω t x₂)
      (fun s ω => quadDriftTerm (f s) (f' s) (density ψ' ω s) x₁ x₂)
      (fun i s ω => f s x₁ x₂ *
        (density ψ' ω s x₁ * (waveCurrent ψ' (x₂ - 1) i s ω - waveCurrent ψ' x₂ i s ω) +
          density ψ' ω s x₂ * (waveCurrent ψ' (x₁ - 1) i s ω - waveCurrent ψ' x₁ i s ω))) := by
  -- the product `Z = P(x₁) P(x₂)`
  have hZ := (hu.isItoProcessUpTo_density hB N x₁).mul hB.nullAug (isStoppingTime_const _ N)
    ⟨N, fun _ => le_rfl⟩ (hu.isItoProcessUpTo_density hB N x₂)
    (hu.weight_continuous_density · x₁) (hu.weight_continuous_density · x₂)
    (fun t => hu.weight_measurable_density t x₁) (fun t => hu.weight_measurable_density t x₂)
    (K := 4) (fun ω s hs0 _ => by
      refine ⟨?_, ?_, hu.abs_lap_density_le_four ω hs0 x₁, hu.abs_lap_density_le_four ω hs0 x₂,
        hu.tsum_waveCurrent_sub_succ_sq_le x₁ hs0 ω, hu.tsum_waveCurrent_sub_succ_sq_le x₂ hs0 ω⟩
      · rw [abs_of_nonneg (density_nonneg ψ' ω s x₁)]
        exact (hu.density_le_one ω hs0 x₁).trans (by norm_num)
      · rw [abs_of_nonneg (density_nonneg ψ' ω s x₂)]
        exact (hu.density_le_one ω hs0 x₂).trans (by norm_num))
  -- the deterministic factor
  have hc : ContinuousOn (f · x₁ x₂) (Set.Icc 0 N) := fun t ht =>
    (hf x₁ x₂ t ht).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf' x₁ x₂)
  set α : ℝ → ℝ := fun t => f (min t N) x₁ x₂ with hαdef
  have hα : ∀ t ∈ Set.Icc (0 : ℝ) N, HasDerivWithinAt α (f' t x₁ x₂) (Set.Icc 0 N) t :=
    fun t ht => (hf x₁ x₂ t ht).congr (fun y hy => by simp [α, min_eq_left hy.2])
      (by simp [α, min_eq_left ht.2])
  have hX := isItoProcessUpTo_deterministic (𝓖 := nullAug μ 𝓕) (μ := μ) (B := B) hB.nullAug
    (τ := fun _ => N) (T := N) (fun _ => le_rfl) hα (hf' x₁ x₂)
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => (fun (t : ℝ) (_ : Ω) => α t) t ω := fun ω =>
    hc.comp_continuous (NNReal.continuous_coe.min continuous_const)
      fun t => ⟨le_min t.2 N.2, min_le_right _ _⟩
  have hZc : ∀ ω, Continuous fun t : ℝ≥0 => density ψ' ω t x₁ * density ψ' ω t x₂ := fun ω =>
    (hu.weight_continuous_density ω x₁).mul (hu.weight_continuous_density ω x₂)
  have hZm : ∀ t : ℝ≥0, Measurable[nullAug μ 𝓕 t]
      (fun ω => density ψ' ω t x₁ * density ψ' ω t x₂) := fun t =>
    (hu.weight_measurable_density t x₁).mul (hu.weight_measurable_density t x₂)
  have hP := hX.mul hB.nullAug (isStoppingTime_const _ N) ⟨N, fun _ => le_rfl⟩ hZ hXc hZc
    (fun _ => measurable_const) hZm (K := max (max C₁ C₂) 50) (fun ω s hs0 hsN => by
      have hsN' : s ≤ N := hsN
      have hs : s ∈ Set.Icc (0 : ℝ) N := ⟨hs0, hsN'⟩
      have p1 := density_nonneg ψ' ω s x₁; have p2 := density_nonneg ψ' ω s x₂
      have q1 := hu.density_le_one ω hs0 x₁; have q2 := hu.density_le_one ω hs0 x₂
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [α, min_eq_left hsN']
        exact (hC₁ s hs).trans ((le_max_left _ _).trans (le_max_left _ _))
      · rw [abs_of_nonneg (mul_nonneg p1 p2)]
        exact (mul_le_mul q1 q2 p2 zero_le_one).trans (by norm_num : (1:ℝ) * 1 ≤ 1) |>.trans ((by norm_num : (1 : ℝ) ≤ 50).trans (le_max_right _ _))
      · exact (hC₂ s hs).trans ((le_max_right _ _).trans (le_max_left _ _))
      · refine le_trans ?_ (le_max_right _ _)
        rw [quad_tsum_currentDiff_mul]
        have l1 := hu.abs_lap_density_le_four ω hs0 x₁
        have l2 := hu.abs_lap_density_le_four ω hs0 x₂
        have l3 := hu.abs_quadCross_le_unit ω hs0 x₁ x₂
        calc |density ψ' ω s x₁ * lap (density ψ' ω s) x₂ +
              density ψ' ω s x₂ * lap (density ψ' ω s) x₁ + quadCross (density ψ' ω s) x₁ x₂|
            ≤ |density ψ' ω s x₁ * lap (density ψ' ω s) x₂| +
              |density ψ' ω s x₂ * lap (density ψ' ω s) x₁| +
              |quadCross (density ψ' ω s) x₁ x₂| :=
              (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
          _ ≤ 4 + 4 + 36 := by
              rw [abs_mul, abs_mul, abs_of_nonneg p1, abs_of_nonneg p2]
              gcongr
              · exact (mul_le_mul q1 l2 (abs_nonneg _) zero_le_one).trans (by norm_num)
              · exact (mul_le_mul q2 l1 (abs_nonneg _) zero_le_one).trans (by norm_num)
          _ ≤ 50 := by norm_num
      · simp
      · refine le_trans ?_ (le_max_right _ _)
        set d₁ := fun i => waveCurrent ψ' (x₁ - 1) i s ω - waveCurrent ψ' x₁ i s ω with hd₁
        set d₂ := fun i => waveCurrent ψ' (x₂ - 1) i s ω - waveCurrent ψ' x₂ i s ω with hd₂
        have sd : ∀ x, Summable fun i =>
            (waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) ^ 2 := fun x => by
          have h1 := summable_waveCurrent_mul ψ' (x - 1)
            (fun i => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) s ω
          have h2 := summable_waveCurrent_mul ψ' x
            (fun i => waveCurrent ψ' (x - 1) i s ω - waveCurrent ψ' x i s ω) s ω
          exact (h1.sub h2).congr fun i => by ring
        have hle : ∀ i, (density ψ' ω s x₁ * d₂ i + density ψ' ω s x₂ * d₁ i) ^ 2 ≤
            2 * d₂ i ^ 2 + 2 * d₁ i ^ 2 := fun i => by
          have a1 : (density ψ' ω s x₁ * d₂ i) ^ 2 ≤ d₂ i ^ 2 := by
            rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ p1 q1)
          have a2 : (density ψ' ω s x₂ * d₁ i) ^ 2 ≤ d₁ i ^ 2 := by
            rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ p2 q2)
          nlinarith [sq_nonneg (density ψ' ω s x₁ * d₂ i - density ψ' ω s x₂ * d₁ i)]
        have s2 : Summable fun i => 2 * d₂ i ^ 2 + 2 * d₁ i ^ 2 :=
          ((sd x₂).mul_left 2).add ((sd x₁).mul_left 2)
        calc ∑' i, (density ψ' ω s x₁ * d₂ i + density ψ' ω s x₂ * d₁ i) ^ 2
            ≤ ∑' i, (2 * d₂ i ^ 2 + 2 * d₁ i ^ 2) :=
              (s2.of_nonneg_of_le (fun i => sq_nonneg _) hle).tsum_le_tsum hle s2
          _ = 2 * ∑' i, d₂ i ^ 2 + 2 * ∑' i, d₁ i ^ 2 := by
              rw [((sd x₂).mul_left 2).tsum_add ((sd x₁).mul_left 2), tsum_mul_left,
                tsum_mul_left]
          _ ≤ 2 * 4 + 2 * 4 := by
              gcongr
              · exact hu.tsum_waveCurrent_sub_succ_sq_le x₂ hs0 ω
              · exact hu.tsum_waveCurrent_sub_succ_sq_le x₁ hs0 ω
          _ ≤ 50 := by norm_num)
  refine hP.congr_const (fun ω t _ htN => by simp [α, min_eq_left htN]; ring)
    (fun ω s hs0 hsN => ?_) (fun i s ω hsN => by simp [α, min_eq_left hsN])
  simp only [α, min_eq_left hsN, quadDriftTerm, quad_tsum_currentDiff_mul, Pi.zero_apply,
    zero_mul, tsum_zero, add_zero]
  ring

/-- **Finite sets of pairs.** `∑_{(x₁,x₂) ∈ S} f_t(x₁,x₂) P(t,x₁) P(t,x₂)` is an Itô process up
to `N`. -/
theorem isItoProcessUpTo_quad_finset [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ≥0} {f f' : ℝ → ℤ → ℤ → ℝ}
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc (0 : ℝ) N,
      HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 N) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 N)) (S : Finset (ℤ × ℤ)) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => N)
      (fun t ω => ∑ p ∈ S, f t p.1 p.2 * density ψ' ω t p.1 * density ψ' ω t p.2)
      (fun s ω => ∑ p ∈ S, quadDriftTerm (f s) (f' s) (density ψ' ω s) p.1 p.2)
      (fun i s ω => ∑ p ∈ S, f s p.1 p.2 *
        (density ψ' ω s p.1 * (waveCurrent ψ' (p.2 - 1) i s ω - waveCurrent ψ' p.2 i s ω) +
          density ψ' ω s p.2 * (waveCurrent ψ' (p.1 - 1) i s ω - waveCurrent ψ' p.1 i s ω))) :=
  IsItoProcessUpTo.finset_sum hB.nullAug S fun p _ =>
    hu.isItoProcessUpTo_quad_pair hB hf hf' p.1 p.2

end IsUnitWave

end QSSEPtoKPZ
