/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.UnitNorm

/-!
# The diffusion coefficients of a linear functional of `P` (task D4)

For a weight `w_s(x)`, the linear functional `∑ₓ w_s(x) P(s,x)` has diffusion coefficients
`∑ₓ w_s(x) (c_{x-1} - c_x)`, where `c_x = waveCurrent ψ x` are the coefficients of the current
`J(x)` (`dP(x) = ΔP(x) ds + dJ(x-1) - dJ(x)`). Since `c_y` lives on the two indices `(y,0)`,
`(y,1)`, summation by parts gives the closed form

`weightCurrent ψ w (y,j) s ω = (w_s(y+1) - w_s(y)) (c_y)_{(y,j)}`,

that is `∑ₓ w(x) (dJ(x-1) - dJ(x)) = ∑_y (w(y+1) - w(y)) dJ(y)`. Results:

* `sum_mul_waveCurrent_sub`: over a finite set `S`, `∑_{x ∈ S} w(x) (c_{x-1} - c_x)` is
  `weightCurrent` of the weight `w 𝟙_S`;
* `hasSum_weightCurrent_sq`, `tsum_enorm_weightCurrent_sq`: the bracket density
  `∑ᵢ (weightCurrent)ᵢ² = ∑_y 2 (w(y+1) - w(y))² P(y) P(y+1)` (the bracket of
  `∫ ∑_y (w(y+1) - w(y)) dJ(y)`, by (2.5));
* elementary facts on series `∑ₓ w(x) P(x)` with bounded `w`: summability, summation by parts
  `∑ w ΔP = ∑ (Δw) P` (`tsum_mul_lap_eq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*}

/-- **Diffusion coefficients of a linear functional.** For a weight `w_s(x)`, the coefficient
of `dB_i`, `i = (y, j)`, in `d ∑ₓ w_s(x) P(s,x)`:
`(w_s(y+1) - w_s(y)) (c_y)ᵢ`, with `c_y = waveCurrent ψ y` the coefficients of `J(y)`. -/
def weightCurrent (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (w : ℝ → ℤ → ℝ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    ℝ :=
  (w s (i.1 + 1) - w s i.1) * waveCurrent ψ i.1 i s ω

/-- `(c_x)ᵢ = 𝟙_{x = i.1} (c_{i.1})ᵢ`. -/
lemma weight_waveCurrent_eq_ite (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    waveCurrent ψ x i s ω = if x = i.1 then waveCurrent ψ i.1 i s ω else 0 := by
  split_ifs with h
  · rw [h]
  · refine waveCurrent_of_ne ψ (fun e => h ?_) (fun e => h ?_) s ω <;> rw [e]

/-- `∑_{x ∈ S} w(x) ((c_{x-1})ᵢ - (c_x)ᵢ) = weightCurrent` of `w 𝟙_S` (summation by parts on a
finite set). -/
lemma sum_mul_waveCurrent_sub (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (w : ℝ → ℤ → ℝ) (S : Finset ℤ)
    (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    ∑ x ∈ S, w s x * (waveCurrent ψ (x - 1) i s ω - waveCurrent ψ x i s ω) =
      weightCurrent ψ (fun s x => if x ∈ S then w s x else 0) i s ω := by
  have h1 : ∀ x, waveCurrent ψ (x - 1) i s ω =
      if i.1 + 1 = x then waveCurrent ψ i.1 i s ω else 0 := fun x => by
    rw [weight_waveCurrent_eq_ite]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  have h2 : ∀ x, waveCurrent ψ x i s ω = if i.1 = x then waveCurrent ψ i.1 i s ω else 0 :=
    fun x => by
    rw [weight_waveCurrent_eq_ite]
    congr 1
    exact propext eq_comm
  rw [Finset.sum_congr rfl fun x _ => by rw [h1 x, h2 x]]
  simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    weightCurrent]
  split_ifs <;> ring

/-- `(c_y)_{(y,0)}² + (c_y)_{(y,1)}² = 2 P(y) P(y+1)`. -/
lemma weight_waveCurrent_sq_add_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (y : ℤ) (s : ℝ) (ω : Ω) :
    waveCurrent ψ y (y, 0) s ω ^ 2 + waveCurrent ψ y (y, 1) s ω ^ 2 =
      2 * density ψ ω s y * density ψ ω s (y + 1) := by
  rw [← tsum_waveCurrent_sq]
  simp only [sq]
  rw [tsum_waveCurrent_mul ψ y (fun i => waveCurrent ψ y i s ω)]

/-- The sum over the fibre `{y} × Fin 2`:
`∑ⱼ (weightCurrent)_{(y,j)}² = (w(y+1) - w(y))² · 2 P(y) P(y+1)`. -/
lemma tsum_weightCurrent_sq_fiber (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (w : ℝ → ℤ → ℝ) (y : ℤ) (s : ℝ)
    (ω : Ω) : ∑' j : Fin 2, weightCurrent ψ w (y, j) s ω ^ 2 =
      (w s (y + 1) - w s y) ^ 2 * (2 * density ψ ω s y * density ψ ω s (y + 1)) := by
  rw [tsum_fintype, Fin.sum_univ_two, ← weight_waveCurrent_sq_add_sq]
  simp only [weightCurrent, mul_pow]
  ring

/-- `P(s,y) ≤ ‖ψ_s‖²`. -/
lemma weight_density_le_norm_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) (y : ℤ) :
    density ψ ω s y ≤ ‖ψ s ω‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm two_ne_zero _ y) 2

/-- `y ↦ P(s,y)` is summable. -/
lemma weight_summable_density (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) :
    Summable (density ψ ω s) :=
  (hasSum_density_norm_sq ψ ω s).summable

/-- `y ↦ P(s, y + c)` is summable. -/
lemma weight_summable_density_add (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (s : ℝ) (c : ℤ) :
    Summable fun y => density ψ ω s (y + c) :=
  (Equiv.addRight c).summable_iff.2 (weight_summable_density ψ ω s)

/-- A bounded weight times a summable family is summable. -/
lemma weight_summable_mul_of_abs_le {f g : ℤ → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) (hg : Summable g) :
    Summable fun x => f x * g x :=
  Summable.of_norm_bounded (hg.abs.mul_left C) fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)

/-- For a bounded weight, `y ↦ (w(y+1) - w(y))² · 2 P(y) P(y+1)` is summable. -/
lemma summable_weightCurrent_fiber (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {w : ℝ → ℤ → ℝ} {s : ℝ} {C : ℝ}
    (hw : ∀ y, |w s y| ≤ C) (ω : Ω) :
    Summable fun y => (w s (y + 1) - w s y) ^ 2 *
      (2 * density ψ ω s y * density ψ ω s (y + 1)) := by
  refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => ?_)
    ((weight_summable_density ψ ω s).mul_left (4 * C ^ 2 * (2 * ‖ψ s ω‖ ^ 2)))
  · have := IsUnitWave.density_nonneg ψ ω s y
    have := IsUnitWave.density_nonneg ψ ω s (y + 1)
    positivity
  · have h1 := hw y
    have h2 := hw (y + 1)
    have hC : 0 ≤ C := (abs_nonneg _).trans h1
    have hd : (w s (y + 1) - w s y) ^ 2 ≤ 4 * C ^ 2 := by
      rw [abs_le] at h1 h2
      nlinarith
    have hp0 := IsUnitWave.density_nonneg ψ ω s y
    have hp1 := IsUnitWave.density_nonneg ψ ω s (y + 1)
    have hp := weight_density_le_norm_sq ψ ω s (y + 1)
    calc (w s (y + 1) - w s y) ^ 2 * (2 * density ψ ω s y * density ψ ω s (y + 1))
        ≤ 4 * C ^ 2 * (2 * density ψ ω s y * ‖ψ s ω‖ ^ 2) := by
          gcongr
    _ = _ := by ring

/-- **Bracket density of a linear functional.** If the series
`∑_y (w(y+1) - w(y))² · 2 P(y) P(y+1)` converges, it is the sum of the squares of the
coefficients `weightCurrent ψ w`. -/
lemma hasSum_weightCurrent_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (w : ℝ → ℤ → ℝ) (s : ℝ) (ω : Ω)
    (hs : Summable fun y => (w s (y + 1) - w s y) ^ 2 *
      (2 * density ψ ω s y * density ψ ω s (y + 1))) :
    HasSum (fun i => weightCurrent ψ w i s ω ^ 2)
      (∑' y, (w s (y + 1) - w s y) ^ 2 * (2 * density ψ ω s y * density ψ ω s (y + 1))) := by
  have hsum : Summable fun i => weightCurrent ψ w i s ω ^ 2 := by
    refine (summable_prod_of_nonneg (fun i => sq_nonneg _)).2
      ⟨fun y => (hasSum_fintype _).summable, ?_⟩
    simp only [tsum_weightCurrent_sq_fiber]
    exact hs
  convert hsum.hasSum using 1
  rw [hsum.tsum_prod' (fun y => (hasSum_fintype _).summable)]
  simp only [tsum_weightCurrent_sq_fiber]

/-- **Bracket density, in `[0, ∞]`**:
`∑ᵢ ‖(weightCurrent)ᵢ‖ₑ² = ofReal (∑_y (w(y+1) - w(y))² · 2 P(y) P(y+1))`. -/
lemma tsum_enorm_weightCurrent_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (w : ℝ → ℤ → ℝ) (s : ℝ) (ω : Ω)
    (hs : Summable fun y => (w s (y + 1) - w s y) ^ 2 *
      (2 * density ψ ω s y * density ψ ω s (y + 1))) :
    ∑' i, ‖weightCurrent ψ w i s ω‖ₑ ^ 2 = ENNReal.ofReal
      (∑' y, (w s (y + 1) - w s y) ^ 2 * (2 * density ψ ω s y * density ψ ω s (y + 1))) := by
  have h := hasSum_weightCurrent_sq ψ w s ω hs
  simp_rw [StochIntAux.enorm_sq_eq]
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable]

/-- `weightCurrent` is linear in the weight: difference. -/
lemma weightCurrent_sub (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (u w : ℝ → ℤ → ℝ) (i : ℤ × Fin 2) (s : ℝ)
    (ω : Ω) : weightCurrent ψ u i s ω - weightCurrent ψ w i s ω =
      weightCurrent ψ (fun s x => u s x - w s x) i s ω := by
  simp only [weightCurrent]
  ring

/-- **Summation by parts on `ℤ`**: `∑ₓ f(x) Δg(x) = ∑ₓ Δf(x) g(x)` for `f` bounded and `g`
summable. -/
lemma tsum_mul_lap_eq {f g : ℤ → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) (hg : Summable g) :
    ∑' x, f x * lap g x = ∑' x, lap f x * g x := by
  have hg1 : Summable fun x => g (x + 1) := (Equiv.addRight (1 : ℤ)).summable_iff.2 hg
  have hg2 : Summable fun x => g (x - 1) := by
    simpa [sub_eq_add_neg, Function.comp_def] using (Equiv.addRight (-1 : ℤ)).summable_iff.2 hg
  have hf1 : ∀ x, |f (x + 1)| ≤ C := fun x => hf _
  have hf2 : ∀ x, |f (x - 1)| ≤ C := fun x => hf _
  have s1 := weight_summable_mul_of_abs_le hf hg1
  have s2 := weight_summable_mul_of_abs_le hf hg2
  have s3 := weight_summable_mul_of_abs_le hf hg
  have t1 := weight_summable_mul_of_abs_le hf1 hg
  have t2 := weight_summable_mul_of_abs_le hf2 hg
  -- reindexing
  have r1 : ∑' x, f x * g (x + 1) = ∑' x, f (x - 1) * g x := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun x => f (x - 1) * g x)]
    simp
  have r2 : ∑' x, f x * g (x - 1) = ∑' x, f (x + 1) * g x := by
    rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq (fun x => f (x + 1) * g x)]
    simp [sub_eq_add_neg]
  have e1 : (fun x => f x * lap g x) = fun x =>
      f x * g (x + 1) + f x * g (x - 1) - 2 * (f x * g x) := by
    funext x; simp only [lap]; ring
  have e2 : (fun x => lap f x * g x) = fun x =>
      f (x - 1) * g x + f (x + 1) * g x - 2 * (f x * g x) := by
    funext x; simp only [lap]; ring
  rw [e1, e2, (s1.add s2).tsum_sub (s3.mul_left 2), s1.tsum_add s2, (t2.add t1).tsum_sub
    (s3.mul_left 2), t2.tsum_add t1, r1, r2]

end QSSEPtoKPZ
