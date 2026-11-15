/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Frame
public import QSSEPtoKPZ.FiniteSystems.PicardAux
public import QSSEPtoKPZ.FiniteSystems.RandomWalkTail

/-!
# Auxiliary results for Lemma 8.2 (task L6)

`docs/stage5-design.md`, Section 1.2 (d). Deterministic estimates, for a fixed `ω`, behind the
proof of Lemma 8.2 in `FiniteSystems/Lemma82.lean`:

* `lemma82_sq_sum_abs_sub_le`: `(∑_{x ∈ Λ_L} | |a(x)|² - |b(x)|² |)² ≤ 4 ∑_{x ∈ Λ_L} |a(x) - b(x)|²`
  for `‖a‖, ‖b‖ ≤ 1` (the article's `∑_{Λ_L} |P^∞ - P^L| ≤ 2 ‖φ - ψ^L‖`);
* `lemma82_rows`: the rows of the unitary matrix `U_t` are unit vectors,
  `∑_{y ∈ Λ_L} |U_t(x, y)|² = 1` for `x ∈ Λ_L` (Parseval with `v = e_x`);
* `lemma82_tsum_boundaryCoef`: `∑ᵢ |c_i|² = |a(L)|² |ψ(L+1)|² + |a(-L)|² |ψ(-L-1)|²` for the
  boundary coefficients `c = pairingBoundaryCoef L a ψ` of the Duhamel formula (8.2);
* `lemma82_pointwise`: for a fixed `ω` and `t ∈ [0, S]`, the square of `∑_{Λ_L} |P - P^L|` at
  time `t` is bounded by the finite-variation part `2 S ∫_0^S 2 (P(s,L) + P(s,-L)) ds`
  (Cauchy–Schwarz in time) plus `8 ∑_y (N^re_t(y)² + N^im_t(y)²)` (the martingale part), given
  the Duhamel formula `⟨U_t e_y, φ_t - ψ^L_t⟩ = V_t(y) + N_t(y)`;
* `lemma82_lintegral_density_le`: `𝔼 ∫_0^S (P(s,x₁) + P(s,x₂)) ds ≤ ∫_0^S 𝖯(|X_s| ≥ L) ds` for
  two distinct sites with `|xᵢ| ≥ L` (Tonelli and `𝔼 P(s,x) = p_s(x)`, Proposition 2.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate InnerProductSpace

noncomputable section

namespace QSSEPtoKPZ

/-! ### Finite sums and lower integrals -/

/-- `∑_{i ∈ S} ∫⁻ fᵢ ≤ ∫⁻ ∑_{i ∈ S} fᵢ` (superadditivity of the lower integral; no measurability
is needed). -/
private lemma lemma82_sum_lintegral_le {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α}
    (S : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ S, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ S, f i a ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj]
    refine (add_le_add le_rfl ih).trans ?_
    refine (le_lintegral_add _ _).trans (lintegral_mono fun a => ?_)
    rw [Finset.sum_insert hj]

/-! ### Deterministic estimates -/

/-- `∑_{x ∈ Λ_L} |a(x)|² ≤ ‖a‖²` for `a ∈ ℓ²(ℤ)`. -/
private lemma lemma82_sum_sq_le_norm_sq (L : ℕ) (a : ℓ²(ℤ, ℂ)) :
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L, ‖a x‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) a (Finset.Icc (-(L : ℤ)) L)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- **`∑_{Λ_L} |P - P^L| ≤ 2 ‖φ - ψ^L‖`**, squared: for `‖a‖, ‖b‖ ≤ 1`,
`(∑_{x ∈ Λ_L} | |a(x)|² - |b(x)|² |)² ≤ 4 ∑_{x ∈ Λ_L} |a(x) - b(x)|²` (Cauchy–Schwarz). -/
theorem lemma82_sq_sum_abs_sub_le (L : ℕ) (a b : ℓ²(ℤ, ℂ)) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    (∑ x ∈ Finset.Icc (-(L : ℤ)) L, |‖a x‖ ^ 2 - ‖b x‖ ^ 2|) ^ 2 ≤
      4 * ∑ x ∈ Finset.Icc (-(L : ℤ)) L, ‖a x - b x‖ ^ 2 := by
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have hsa : ∑ x ∈ S, ‖a x‖ ^ 2 ≤ 1 := by
    have := lemma82_sum_sq_le_norm_sq L a
    nlinarith [norm_nonneg a]
  have hsb : ∑ x ∈ S, ‖b x‖ ^ 2 ≤ 1 := by
    have := lemma82_sum_sq_le_norm_sq L b
    nlinarith [norm_nonneg b]
  have hpt : ∀ x, |‖a x‖ ^ 2 - ‖b x‖ ^ 2| ≤ ‖a x - b x‖ * (‖a x‖ + ‖b x‖) := by
    intro x
    rw [show ‖a x‖ ^ 2 - ‖b x‖ ^ 2 = (‖a x‖ - ‖b x‖) * (‖a x‖ + ‖b x‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖a x‖ + ‖b x‖)]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
  have h2 : ∑ x ∈ S, (‖a x‖ + ‖b x‖) ^ 2 ≤ 4 := by
    calc ∑ x ∈ S, (‖a x‖ + ‖b x‖) ^ 2 ≤ ∑ x ∈ S, (2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2) :=
          Finset.sum_le_sum fun x _ => by nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
      _ = 2 * ∑ x ∈ S, ‖a x‖ ^ 2 + 2 * ∑ x ∈ S, ‖b x‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 := by linarith
  calc (∑ x ∈ S, |‖a x‖ ^ 2 - ‖b x‖ ^ 2|) ^ 2
      ≤ (∑ x ∈ S, ‖a x - b x‖ * (‖a x‖ + ‖b x‖)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.sum_le_sum fun x _ => hpt x) 2
    _ ≤ (∑ x ∈ S, ‖a x - b x‖ ^ 2) * ∑ x ∈ S, (‖a x‖ + ‖b x‖) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ x ∈ S, ‖a x - b x‖ ^ 2) * 4 :=
        mul_le_mul_of_nonneg_left h2 (Finset.sum_nonneg fun _ _ => by positivity)
    _ = 4 * ∑ x ∈ S, ‖a x - b x‖ ^ 2 := mul_comm _ _

/-- **The rows of `U_t` are unit vectors.** If `(w_y)_{y ∈ Λ_L}` is an orthonormal family of
vectors supported in `Λ_L`, then `∑_{y ∈ Λ_L} |w_y(x)|² = 1` for every `x ∈ Λ_L`. -/
theorem lemma82_rows {L : ℕ} (w : ℤ → ℓ²(ℤ, ℂ))
    (hw : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ x, x ∉ box L → w y x = 0)
    (hon : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ z ∈ Finset.Icc (-(L : ℤ)) L,
      ⟪w y, w z⟫_ℂ = if y = z then 1 else 0)
    {x : ℤ} (hx : x ∈ Finset.Icc (-(L : ℤ)) L) :
    ∑ y ∈ Finset.Icc (-(L : ℤ)) L, ‖w y x‖ ^ 2 = 1 := by
  classical
  have h := frame_parseval w hw hon (lp.single 2 x 1)
  have e1 : ∀ y, ‖⟪w y, lp.single 2 x (1 : ℂ)⟫_ℂ‖ = ‖w y x‖ := fun y => by
    rw [lp.inner_single_right, RCLike.inner_apply', mul_one, Complex.norm_conj]
  have e2 : ∑ x' ∈ Finset.Icc (-(L : ℤ)) L, ‖(lp.single 2 x (1 : ℂ) : ℤ → ℂ) x'‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single x (fun x' _ hx' => by simp [lp.single_apply, hx'])
      (fun h => absurd hx h)]
    simp [lp.single_apply]
  simp only [e1] at h
  rw [h, e2]

/-- `|z w / √2|² = |z|² |w|² / 2`. -/
private lemma lemma82_norm_div_sqrt_two_sq (z w : ℂ) :
    ‖z * w / (Real.sqrt 2 : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * ‖w‖ ^ 2 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_mul,
    div_pow, mul_pow, Real.sq_sqrt (by norm_num)]

/-- **Energy of the boundary coefficients** of the Duhamel formula (8.2):
`∑ᵢ |c_i(s)|² = |a_s(L)|² |ψ_s(L+1)|² + |a_s(-L)|² |ψ_s(-L-1)|²`. -/
theorem lemma82_tsum_boundaryCoef {Ω : Type*} (L : ℕ) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ)
    (ω : Ω) :
    ∑' i, ENNReal.ofReal (‖pairingBoundaryCoef L a ψ i s ω‖ ^ 2) =
      ENNReal.ofReal (‖a s ω L‖ ^ 2 * ‖ψ s ω (L + 1)‖ ^ 2 +
        ‖a s ω (-L)‖ ^ 2 * ‖ψ s ω (-L - 1)‖ ^ 2) := by
  classical
  set T : Finset (ℤ × Fin 2) := {((L : ℤ), 0), ((L : ℤ), 1), (-(L : ℤ) - 1, 0),
    (-(L : ℤ) - 1, 1)} with hT
  have hL : (-(L : ℤ) - 1) ≠ L := by omega
  have hz : ∀ i ∉ T, ENNReal.ofReal (‖pairingBoundaryCoef L a ψ i s ω‖ ^ 2) = 0 := by
    intro i hi
    simp only [hT, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [pairingBoundaryCoef, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
  rw [tsum_eq_sum hz, ← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  congr 1
  have h1 : ((L : ℤ), (0 : Fin 2)) ∉ ({((L : ℤ), 1), (-(L : ℤ) - 1, 0), (-(L : ℤ) - 1, 1)} :
      Finset (ℤ × Fin 2)) := by
    simp [Prod.ext_iff, hL.symm]
  have h2 : ((L : ℤ), (1 : Fin 2)) ∉ ({(-(L : ℤ) - 1, 0), (-(L : ℤ) - 1, 1)} :
      Finset (ℤ × Fin 2)) := by
    simp [Prod.ext_iff, hL.symm]
  have h3 : (-(L : ℤ) - 1, (0 : Fin 2)) ∉ ({(-(L : ℤ) - 1, 1)} : Finset (ℤ × Fin 2)) := by
    simp [Prod.ext_iff]
  rw [hT, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  simp only [pairingBoundaryCoef, Prod.mk.injEq, hL, and_false, and_true, one_ne_zero,
    zero_ne_one, ↓reduceIte]
  rw [lemma82_norm_div_sqrt_two_sq, lemma82_norm_div_sqrt_two_sq, lemma82_norm_div_sqrt_two_sq,
    lemma82_norm_div_sqrt_two_sq]
  simp only [Complex.norm_conj, norm_mul, Complex.norm_I, one_mul, norm_neg]
  ring

/-- `|\bar a b + \bar c d|² ≤ 2 |a|² |b|² + 2 |c|² |d|²`. -/
private lemma lemma82_norm_sq_le (a b c d : ℂ) :
    ‖conj a * b + conj c * d‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 * ‖b‖ ^ 2) + 2 * (‖c‖ ^ 2 * ‖d‖ ^ 2) := by
  have h := norm_add_le (conj a * b) (conj c * d)
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj] at h
  have h0 : 0 ≤ ‖conj a * b + conj c * d‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ * ‖b‖ - ‖c‖ * ‖d‖), mul_nonneg (norm_nonneg a) (norm_nonneg b),
    mul_nonneg (norm_nonneg c) (norm_nonneg d)]

/-- `|-(1/2) V + (I₁ + i I₂)|² ≤ (1/2) |V|² + 2 (I₁² + I₂²)`. -/
private lemma lemma82_norm_sq_drift_mart_le (V : ℂ) (I1 I2 : ℝ) :
    ‖-(1 / 2 : ℂ) * V + ((I1 : ℂ) + Complex.I * (I2 : ℂ))‖ ^ 2 ≤
      2 * ‖V‖ ^ 2 / 4 + 2 * (I1 ^ 2 + I2 ^ 2) := by
  have hN : ‖(I1 : ℂ) + Complex.I * (I2 : ℂ)‖ ^ 2 = I1 ^ 2 + I2 ^ 2 := by
    rw [Complex.sq_norm, mul_comm, Complex.normSq_add_mul_I]
  have hV : ‖-(1 / 2 : ℂ) * V‖ = ‖V‖ / 2 := by
    rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_two]; ring
  have h := norm_add_le (-(1 / 2 : ℂ) * V) ((I1 : ℂ) + Complex.I * (I2 : ℂ))
  rw [hV] at h
  have h0 : 0 ≤ ‖-(1 / 2 : ℂ) * V + ((I1 : ℂ) + Complex.I * (I2 : ℂ))‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖V‖ / 2 - ‖(I1 : ℂ) + Complex.I * (I2 : ℂ)‖), norm_nonneg V,
    norm_nonneg ((I1 : ℂ) + Complex.I * (I2 : ℂ))]

/-- **Pointwise form of Lemma 8.2.** Fix `ω` and `t ∈ [0, S]`. Let `w_y(s)` (`y ∈ Λ_L`) be
orthonormal vectors supported in `Λ_L` for every `s ≥ 0` (the columns `U_s e_y`), `p(s)` a path
(`ψ^∞_s`), `q` a vector (`ψ^L_t`) with `‖p(t)‖, ‖q‖ ≤ 1`, and suppose the Duhamel formula
`⟨w_y(t), p(t) - q⟩ = -(1/2) ∫_0^t (\bar w_y(s)(L) p(s)(L) + \bar w_y(s)(-L) p(s)(-L)) ds
+ (I₁(y) + i I₂(y))`. Then `(∑_{x ∈ Λ_L} | |p(t)(x)|² - |q(x)|² |)²` is at most
`2 S ∫_0^S 2 (|p(s)(L)|² + |p(s)(-L)|²) ds + 8 ∑_{y ∈ Λ_L} (I₁(y)² + I₂(y)²)`. -/
theorem lemma82_pointwise {L : ℕ} {S t : ℝ} (ht0 : 0 ≤ t) (htS : t ≤ S)
    (w : ℤ → ℝ → ℓ²(ℤ, ℂ)) (p : ℝ → ℓ²(ℤ, ℂ)) (q : ℓ²(ℤ, ℂ)) (I1 I2 : ℤ → ℝ)
    (hsupp : ∀ s, 0 ≤ s → ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ x, x ∉ box L → w y s x = 0)
    (hon : ∀ s, 0 ≤ s → ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ z ∈ Finset.Icc (-(L : ℤ)) L,
      ⟪w y s, w z s⟫_ℂ = if y = z then 1 else 0)
    (hp : ‖p t‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hcont : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ContinuousOn
      (fun s => conj (w y s L) * p s L + conj (w y s (-L)) * p s (-L)) (Set.Icc 0 t))
    (hid : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ⟪w y t, p t⟫_ℂ - ⟪w y t, q⟫_ℂ =
      -(1 / 2 : ℂ) * (∫ s in (0 : ℝ)..t, (conj (w y s L) * p s L + conj (w y s (-L)) * p s (-L)))
        + ((I1 y : ℂ) + Complex.I * (I2 y : ℂ))) :
    ENNReal.ofReal ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |‖p t x‖ ^ 2 - ‖q x‖ ^ 2|) ^ 2) ≤
      2 * ENNReal.ofReal S *
          (∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2))) +
        8 * ∑ y ∈ Finset.Icc (-(L : ℤ)) L,
          (ENNReal.ofReal (I1 y ^ 2) + ENNReal.ofReal (I2 y ^ 2)) := by
  set Sb := Finset.Icc (-(L : ℤ)) L with hSb
  set f : ℤ → ℝ → ℂ := fun y s => conj (w y s L) * p s L + conj (w y s (-L)) * p s (-L)
    with hf
  have hLm : (L : ℤ) ∈ Sb := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hLm' : -(L : ℤ) ∈ Sb := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  -- the real estimate at time `t`
  have hreal : (∑ x ∈ Sb, |‖p t x‖ ^ 2 - ‖q x‖ ^ 2|) ^ 2 ≤
      ∑ y ∈ Sb, (2 * ‖∫ s in (0 : ℝ)..t, f y s‖ ^ 2 + 8 * (I1 y ^ 2 + I2 y ^ 2)) := by
    have hpar := frame_parseval (fun y => w y t) (hsupp t ht0) (hon t ht0) (p t - q)
    have e : ∀ x, ((p t - q : ℓ²(ℤ, ℂ)) : ℤ → ℂ) x = p t x - q x := fun x => rfl
    simp only [e] at hpar
    calc (∑ x ∈ Sb, |‖p t x‖ ^ 2 - ‖q x‖ ^ 2|) ^ 2 ≤ 4 * ∑ x ∈ Sb, ‖p t x - q x‖ ^ 2 :=
          lemma82_sq_sum_abs_sub_le L (p t) q hp hq
      _ = ∑ y ∈ Sb, 4 * ‖⟪w y t, p t - q⟫_ℂ‖ ^ 2 := by rw [← hpar, Finset.mul_sum]
      _ ≤ ∑ y ∈ Sb, (2 * ‖∫ s in (0 : ℝ)..t, f y s‖ ^ 2 + 8 * (I1 y ^ 2 + I2 y ^ 2)) := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [inner_sub_right, hid y hy]
          have := lemma82_norm_sq_drift_mart_le (∫ s in (0 : ℝ)..t, f y s) (I1 y) (I2 y)
          linarith
  -- the finite-variation part, by Cauchy–Schwarz in time and the rows of `U_s`
  have hrow : ∀ s ∈ Set.Ioc (0 : ℝ) t, ∑ y ∈ Sb, ENNReal.ofReal (‖f y s‖ ^ 2) ≤
      ENNReal.ofReal (2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2)) := by
    intro s hs
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    refine ENNReal.ofReal_le_ofReal ?_
    have r1 := lemma82_rows (fun y => w y s) (hsupp s hs.1.le) (hon s hs.1.le) hLm
    have r2 := lemma82_rows (fun y => w y s) (hsupp s hs.1.le) (hon s hs.1.le) hLm'
    calc ∑ y ∈ Sb, ‖f y s‖ ^ 2 ≤ ∑ y ∈ Sb, (2 * (‖w y s L‖ ^ 2 * ‖p s L‖ ^ 2) +
          2 * (‖w y s (-L)‖ ^ 2 * ‖p s (-L)‖ ^ 2)) :=
          Finset.sum_le_sum fun y _ => lemma82_norm_sq_le _ _ _ _
      _ = 2 * ‖p s L‖ ^ 2 * (∑ y ∈ Sb, ‖w y s L‖ ^ 2) +
          2 * ‖p s (-L)‖ ^ 2 * (∑ y ∈ Sb, ‖w y s (-L)‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun y _ => by ring
      _ = 2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2) := by rw [r1, r2]; ring
  have hV : ∑ y ∈ Sb, ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, f y s‖ ^ 2) ≤
      ENNReal.ofReal S *
        ∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2)) := by
    calc ∑ y ∈ Sb, ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, f y s‖ ^ 2)
        ≤ ∑ y ∈ Sb, ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (‖f y s‖ ^ 2) :=
          Finset.sum_le_sum fun y hy => picardAux_sq_integral_le ht0 (hcont y hy)
      _ = ENNReal.ofReal t * ∑ y ∈ Sb, ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (‖f y s‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal t * ∫⁻ s in Set.Ioc 0 t, ∑ y ∈ Sb, ENNReal.ofReal (‖f y s‖ ^ 2) :=
          mul_le_mul' le_rfl (lemma82_sum_lintegral_le _ _)
      _ ≤ ENNReal.ofReal t *
          ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2)) :=
          mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc hrow)
      _ ≤ ENNReal.ofReal S *
          ∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal htS)
            (lintegral_mono_set (Set.Ioc_subset_Ioc_right htS))
  calc ENNReal.ofReal ((∑ x ∈ Sb, |‖p t x‖ ^ 2 - ‖q x‖ ^ 2|) ^ 2)
      ≤ ENNReal.ofReal (∑ y ∈ Sb, (2 * ‖∫ s in (0 : ℝ)..t, f y s‖ ^ 2 +
          8 * (I1 y ^ 2 + I2 y ^ 2))) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * ∑ y ∈ Sb, ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, f y s‖ ^ 2) +
        8 * ∑ y ∈ Sb, (ENNReal.ofReal (I1 y ^ 2) + ENNReal.ofReal (I2 y ^ 2)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, Finset.mul_sum,
          Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
    _ ≤ 2 * (ENNReal.ofReal S *
          ∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (2 * (‖p s L‖ ^ 2 + ‖p s (-L)‖ ^ 2))) +
        8 * ∑ y ∈ Sb, (ENNReal.ofReal (I1 y ^ 2) + ENNReal.ofReal (I2 y ^ 2)) := by
        gcongr
    _ = _ := by rw [mul_assoc]

/-- `|Re z|² + |Im z|² = |z|²` in `[0, ∞]`. -/
theorem lemma82_enorm_re_im (z : ℂ) :
    ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, sq_abs,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  ring

/-- A path continuous on `[0, ∞)` has coordinates continuous on `[0, ∞) ⊆ ℝ`. -/
theorem lemma82_continuousOn_apply {φ : ℝ → ℓ²(ℤ, ℂ)} (hc : Continuous fun t : ℝ≥0 => φ t)
    (x : ℤ) : ContinuousOn (fun s => φ s x) (Set.Ici 0) :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp
    (hc.comp continuous_real_toNNReal)).continuousOn.congr fun r hr => by
      simp only [Function.comp_apply, Real.coe_toNNReal _ (Set.mem_Ici.1 hr)]; rfl

/-! ### Expectations of time integrals of the densities -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- Joint measurability of `(s, ω) ↦ c (|φ_{s⁺}(ω)(x₁)|² + |φ_{s⁺}(ω)(x₂)|²)` for a process
with measurable values and continuous paths. -/
private lemma lemma82_measurable_sq {φ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hm : ∀ (t : ℝ≥0) (x : ℤ), Measurable fun ω => φ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => φ t ω) (c : ℝ) (x1 x2 : ℤ) :
    Measurable fun p : ℝ × Ω => ENNReal.ofReal
      (c * (‖φ (p.1.toNNReal : ℝ) p.2 x1‖ ^ 2 + ‖φ (p.1.toNNReal : ℝ) p.2 x2‖ ^ 2)) := by
  have h : ∀ x, Measurable fun p : ℝ × Ω => φ (p.1.toNNReal : ℝ) p.2 x := fun x =>
    picardAux_measurable_uncurry (X := fun t ω => φ t ω x) (fun t => hm t x)
      (fun ω => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).continuous.comp (hc ω))
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (((h x1).norm.pow_const 2).add ((h x2).norm.pow_const 2)))

/-- `ω ↦ ∫_0^S c (|φ_s(ω)(x₁)|² + |φ_s(ω)(x₂)|²) ds` (in `[0, ∞]`) is measurable. -/
theorem lemma82_measurable_lintegral {φ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hm : ∀ (t : ℝ≥0) (x : ℤ), Measurable fun ω => φ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => φ t ω) (c : ℝ) (x1 x2 : ℤ) (S : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Ioc 0 S,
      ENNReal.ofReal (c * (‖φ s ω x1‖ ^ 2 + ‖φ s ω x2‖ ^ 2)) := by
  have h := (lemma82_measurable_sq hm hc c x1 x2).lintegral_prod_left'
    (μ := volume.restrict (Set.Ioc (0 : ℝ) S))
  convert h using 1
  funext ω
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  simp only [Real.coe_toNNReal _ hs.1.le]

/-- `p_s(x₁) + p_s(x₂) ≤ 𝖯(|X_s| ≥ L)` for two distinct sites with `|xᵢ| ≥ L`, `s ≥ 0`. -/
private lemma lemma82_rwKernel_add_le (hB : IsBrownianFamily 𝓕 B μ) {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) {L : ℕ} {x1 x2 : ℤ} (hx : x1 ≠ x2) (h1 : (L : ℤ) ≤ |x1|)
    (h2 : (L : ℤ) ≤ |x2|) {s : ℝ} (hs : 0 ≤ s) :
    rwKernel s x1 + rwKernel s x2 ≤ rwTail s L := by
  classical
  have hle := Summable.sum_le_tsum ({x1, x2} : Finset ℤ)
    (fun x _ => by split_ifs <;> [exact rwKernel_nonneg hB hψ hs x; exact le_rfl])
    (summable_rwTail hB hψ hs L)
  rw [Finset.sum_pair hx] at hle
  simpa [h1, h2, rwTail] using hle

/-- **Expected time integral of two densities** (Tonelli and `𝔼 P(s,x) = p_s(x)`,
Proposition 2.2): if `φ` is indistinguishable from a wave function `ψ` on `ℤ` and has measurable
values and continuous paths, then for distinct sites `x₁, x₂` with `|xᵢ| ≥ L` and `c ≥ 0`,
`𝔼 ∫_0^S c (|φ_s(x₁)|² + |φ_s(x₂)|²) ds ≤ c ∫_0^S 𝖯(|X_s| ≥ L) ds`. -/
theorem lemma82_lintegral_density_le [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {ψ φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    (hm : ∀ (t : ℝ≥0) (x : ℤ), Measurable fun ω => φ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => φ t ω) (heq : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, φ t ω = ψ t ω)
    {c : ℝ} (hc0 : 0 ≤ c) {L : ℕ} {x1 x2 : ℤ} (hx : x1 ≠ x2) (h1 : (L : ℤ) ≤ |x1|)
    (h2 : (L : ℤ) ≤ |x2|) {S : ℝ} (hS : 0 ≤ S) :
    ∫⁻ ω, (∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (c * (‖φ s ω x1‖ ^ 2 + ‖φ s ω x2‖ ^ 2))) ∂μ ≤
      ENNReal.ofReal (c * ∫ s in (0 : ℝ)..S, rwTail s L) := by
  set F : ℝ × Ω → ℝ≥0∞ := fun p => ENNReal.ofReal
    (c * (‖φ (p.1.toNNReal : ℝ) p.2 x1‖ ^ 2 + ‖φ (p.1.toNNReal : ℝ) p.2 x2‖ ^ 2)) with hFdef
  have hF : Measurable F := lemma82_measurable_sq hm hc c x1 x2
  have e1 : ∀ ω, ∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (c * (‖φ s ω x1‖ ^ 2 + ‖φ s ω x2‖ ^ 2)) =
      ∫⁻ s in Set.Ioc 0 S, F (s, ω) := fun ω =>
    setLIntegral_congr_fun measurableSet_Ioc fun s hs => by
      simp only [hFdef, Real.coe_toNNReal _ hs.1.le]
  simp_rw [e1]
  rw [lintegral_lintegral_swap (f := fun ω s => F (s, ω)) (hF.comp measurable_swap).aemeasurable]
  have hE := (prop_2_2 hB hψ).choose_spec.2.2.2.2
  have hJ := intervalIntegrable_rwTail hB hψ L hS
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hS,
    ofReal_integral_eq_lintegral_ofReal (hJ.1.const_mul c)
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs =>
        mul_nonneg hc0 (rwTail_nonneg hB hψ hs.1.le L)))]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  set τ := s.toNNReal with hτ
  have hτs : (τ : ℝ) = s := Real.coe_toNNReal _ hs.1.le
  have e2 : ∫⁻ ω, F (s, ω) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (c * (density ψ ω τ x1 + density ψ ω τ x2)) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [heq] with ω hω
    simp only [hFdef, density, ← hτ, hω τ]
  have hint : Integrable (fun ω => c * (density ψ ω τ x1 + density ψ ω τ x2)) μ :=
    ((hE τ x1).1.add (hE τ x2).1).const_mul c
  have e3 := ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun ω => by simp only [density]; positivity)
  rw [e2, ← e3, integral_const_mul, integral_add (hE τ x1).1 (hE τ x2).1, (hE τ x1).2,
    (hE τ x2).2, hτs]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (lemma82_rwKernel_add_le hB hψ hx h1 h2 hs.1.le) hc0)

end QSSEPtoKPZ
