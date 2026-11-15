/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.WaveIto

/-!
# The algebra of the pairing identity on a box (task L4)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L4.
`docs/stage5-design.md`, Section 1.2 (c) and note on L4 (cancellations as pointwise identities,
one per bond, then summed).

Fix `s`, `ω`, write `a = a_s(ω)`, `b = b_s(ω)` and `c^a_{x,i} = waveDiffC a x i s ω` (the complex
coefficient of `dB_i` in `da(x)`). By the product rule (`IsCItoProcessUpTo.conj_mul`),
`d(\bar a(x) b(x))` has diffusion coefficients `\bar a(x) c^b_{x,i} + b(x) \bar c^a_{x,i}` and
drift `\bar a(x) β(x) + b(x) \bar α(x) + ∑ᵢ \bar c^a_{x,i} c^b_{x,i}` (`α`, `β` the drifts).

* `pairing_coef_sum_box`, `pairing_drift_sum_box` (`a`, `b` supported in `Λ_L`): summed over
  `x ∈ Λ_L`, the diffusion coefficients cancel bond by bond and the drift vanishes:
  `d⟨a, b⟩ = 0`.
* `pairing_coef_sum_restrict`, `pairing_drift_sum_restrict` (`a` supported in `Λ_L`, `ψ` on `ℤ`
  with drift `-ψ`): what is left is the boundary source of Section 8,
  `-(1/2)(\bar a(L) ψ(L) + \bar a(-L) ψ(-L)) ds` plus the noise `pairingBoundaryCoef`
  (`\bar a(L) i ψ(L+1) dW⁽ᴸ⁾ + \bar a(-L) i ψ(-L-1) d\bar W⁽⁻ᴸ⁻¹⁾` in real form).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Auxiliary lemmas -/

/-- For finite `L`, `x ∈ Λ_L` iff `-L ≤ x ≤ L`. -/
theorem pairing_mem_box_iff {L : ℕ} {x : ℤ} :
    x ∈ box (L : ℕ∞) ↔ x ∈ Finset.Icc (-(L : ℤ)) L := by
  simp only [box, Set.mem_ofPred_eq, Nat.cast_le, Finset.mem_Icc]
  omega

/-- The degree `D_L(x,x)` as the number of neighbours of `x` in `Λ_L` (finite `L`). -/
theorem pairing_degree_eq {L : ℕ} (x : ℤ) :
    (degree L x : ℂ) = (if -(L : ℤ) ≤ x + 1 ∧ x + 1 ≤ L then 1 else 0) +
      (if -(L : ℤ) ≤ x - 1 ∧ x - 1 ≤ L then 1 else 0) := by
  have h : ∀ y : ℤ, ((box (L : ℕ∞)).indicator 1 y : ℕ) =
      if -(L : ℤ) ≤ y ∧ y ≤ L then 1 else 0 := by
    intro y
    by_cases hy : y ∈ box (L : ℕ∞)
    · have h' := Finset.mem_Icc.1 (pairing_mem_box_iff.1 hy)
      simp [Set.indicator_of_mem hy, h']
    · have h' : ¬ (-(L : ℤ) ≤ y ∧ y ≤ L) := fun h' => hy (pairing_mem_box_iff.2
        (Finset.mem_Icc.2 h'))
      simp [Set.indicator_of_notMem hy, h']
  simp only [degree, h]
  split_ifs <;> norm_num

/-- `waveDiffC ψ j (j,k)`: the coefficients of the bond `(j, j+1)` in `dψ(j)`. -/
private lemma pairing_waveDiffC_self (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (j : ℤ) (k : Fin 2) (s : ℝ)
    (ω : Ω) : waveDiffC ψ j (j, k) s ω =
      if k = 0 then Complex.I * ψ s ω (j + 1) / Real.sqrt 2 else -ψ s ω (j + 1) / Real.sqrt 2 := by
  rw [waveDiffC_eq]
  fin_cases k <;> simp

/-- `waveDiffC ψ (j+1) (j,k)`: the coefficients of the bond `(j, j+1)` in `dψ(j+1)`. -/
private lemma pairing_waveDiffC_succ (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (j : ℤ) (k : Fin 2) (s : ℝ)
    (ω : Ω) : waveDiffC ψ (j + 1) (j, k) s ω =
      if k = 0 then Complex.I * ψ s ω j / Real.sqrt 2 else ψ s ω j / Real.sqrt 2 := by
  have h1 : j ≠ j + 1 := by omega
  rw [waveDiffC_eq]
  fin_cases k <;> simp [h1]

/-- `waveDiffC ψ x (x-1,k)`: the coefficients of the bond `(x-1, x)` in `dψ(x)`. -/
private lemma pairing_waveDiffC_pred (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (k : Fin 2) (s : ℝ)
    (ω : Ω) : waveDiffC ψ x (x - 1, k) s ω =
      if k = 0 then Complex.I * ψ s ω (x - 1) / Real.sqrt 2 else ψ s ω (x - 1) / Real.sqrt 2 := by
  have h := pairing_waveDiffC_succ ψ (x - 1) k s ω
  rwa [sub_add_cancel] at h

/-- `waveDiffC ψ x (j,k) = 0` unless `x = j` or `x = j + 1`. -/
private lemma pairing_waveDiffC_other (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x j : ℤ} (h1 : x ≠ j)
    (h2 : x ≠ j + 1) (k : Fin 2) (s : ℝ) (ω : Ω) : waveDiffC ψ x (j, k) s ω = 0 := by
  have h3 : j ≠ x - 1 := by omega
  rw [waveDiffC_eq]
  simp [Ne.symm h1, h3]

/-- A sum over a finset of a function supported in `{j, j+1}`. -/
private lemma pairing_sum_two (S : Finset ℤ) (f : ℤ → ℂ) (j : ℤ)
    (hf : ∀ x, x ≠ j → x ≠ j + 1 → f x = 0) :
    ∑ x ∈ S, f x = (if j ∈ S then f j else 0) + (if j + 1 ∈ S then f (j + 1) else 0) := by
  have h : ∀ x, f x = (if x = j then f x else 0) + (if x = j + 1 then f x else 0) := by
    intro x
    by_cases h1 : x = j
    · subst h1
      have : x ≠ x + 1 := by omega
      simp [this]
    · by_cases h2 : x = j + 1
      · simp [h2]
      · simp [h1, h2, hf x h1 h2]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']

/-- `conj (√2) = √2`, `√2 √2 = 2`, `√2 ≠ 0` in `ℂ`. -/
private lemma pairing_sqrt_two :
    conj (Real.sqrt 2 : ℂ) = Real.sqrt 2 ∧ (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 ∧
      (Real.sqrt 2 : ℂ) ≠ 0 := by
  refine ⟨Complex.conj_ofReal _, ?_, ?_⟩
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  · exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

/-- **The bracket term** `∑ᵢ \bar c^a_{x,i} c^b_{x,i} = \bar a(x+1) b(x+1) + \bar a(x-1) b(x-1)`. -/
theorem pairing_tsum_conj_mul (a b : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, conj (waveDiffC a x i s ω) * waveDiffC b x i s ω =
      conj (a s ω (x + 1)) * b s ω (x + 1) + conj (a s ω (x - 1)) * b s ω (x - 1) := by
  have hz : ∀ (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) i, i ∉ waveSites x → waveDiffC ψ x i s ω = 0 :=
    fun ψ i hi => by simp [waveDiffC, waveDiffRe_of_notMem ψ hi, waveDiffIm_of_notMem ψ hi]
  rw [tsum_eq_sum (s := waveSites x) fun i hi => by rw [hz b i hi, mul_zero], sum_waveSites]
  simp only [pairing_waveDiffC_self, pairing_waveDiffC_pred]
  simp only [↓reduceIte, one_ne_zero]
  obtain ⟨hc, hm, h0⟩ := pairing_sqrt_two
  have hm2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by rw [sq, hm]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_I, hc]
  field_simp
  rw [hm2, Complex.I_sq]
  ring

/-- `∑_{x ∈ S} ∑_{y ∈ S} K(x,y) = 0` for an antisymmetric kernel `K`. -/
private lemma pairing_sum_antisymm (S : Finset ℤ) (K : ℤ → ℤ → ℂ)
    (hK : ∀ x y, K y x = -K x y) : ∑ x ∈ S, ∑ y ∈ S, K x y = 0 := by
  have h : ∑ x ∈ S, ∑ y ∈ S, K x y = -∑ x ∈ S, ∑ y ∈ S, K x y := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => hK y x
  exact self_eq_neg.1 h

/-- **The discrete Laplacian sums to zero on a box**: if `p` vanishes outside `Λ_L`, then
`∑_{x ∈ Λ_L} (-D_L(x) p(x) + p(x+1) + p(x-1)) = 0`. -/
private lemma pairing_laplacian_sum {L : ℕ} (p : ℤ → ℂ)
    (hp : ∀ x, x ∉ Finset.Icc (-(L : ℤ)) L → p x = 0) :
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L, (-(degree L x : ℂ) * p x + p (x + 1) + p (x - 1)) = 0 := by
  set S := Finset.Icc (-(L : ℤ)) L with hS
  set K : ℤ → ℤ → ℂ := fun x y =>
    (if y = x + 1 then p y - p x else 0) + (if y = x - 1 then p y - p x else 0) with hKdef
  have hK : ∀ x y, K y x = -K x y := by
    intro x y
    simp only [hKdef]
    by_cases h1 : y = x + 1
    · subst h1
      have h3 : x ≠ x + 1 + 1 := by omega
      have h4 : x + 1 ≠ x - 1 := by omega
      simp only [h3, h4, add_sub_cancel_right, ↓reduceIte]
      ring
    · by_cases h5 : y = x - 1
      · subst h5
        have h3 : x ≠ x - 1 - 1 := by omega
        simp only [h1, h3, sub_add_cancel, ↓reduceIte]
        ring
      · have h2 : x ≠ y + 1 := by omega
        have h3 : x ≠ y - 1 := by omega
        simp only [h1, h5, h2, h3, ↓reduceIte]
        ring
  have hrow : ∀ x ∈ S, ∑ y ∈ S, K x y = -(degree L x : ℂ) * p x + p (x + 1) + p (x - 1) := by
    intro x hx
    simp only [hKdef, Finset.sum_add_distrib, Finset.sum_ite_eq', pairing_degree_eq]
    have hx' := Finset.mem_Icc.1 hx
    by_cases h1 : x + 1 ∈ S <;> by_cases h2 : x - 1 ∈ S
    · simp only [h1, h2, Finset.mem_Icc.1 h1, Finset.mem_Icc.1 h2, and_self, ↓reduceIte]
      ring
    · have h2' : ¬ (-(L : ℤ) ≤ x - 1 ∧ x - 1 ≤ L) := fun h => h2 (Finset.mem_Icc.2 h)
      simp only [h1, h2, Finset.mem_Icc.1 h1, h2', and_self, ↓reduceIte, hp _ h2]
      ring
    · have h1' : ¬ (-(L : ℤ) ≤ x + 1 ∧ x + 1 ≤ L) := fun h => h1 (Finset.mem_Icc.2 h)
      simp only [h1, h2, h1', Finset.mem_Icc.1 h2, and_self, ↓reduceIte, hp _ h1]
      ring
    · have h1' : ¬ (-(L : ℤ) ≤ x + 1 ∧ x + 1 ≤ L) := fun h => h1 (Finset.mem_Icc.2 h)
      have h2' : ¬ (-(L : ℤ) ≤ x - 1 ∧ x - 1 ≤ L) := fun h => h2 (Finset.mem_Icc.2 h)
      simp only [h1, h2, h1', h2', ↓reduceIte, hp _ h1, hp _ h2]
      ring
  rw [← Finset.sum_congr rfl hrow]
  exact pairing_sum_antisymm S K hK

/-- The drift summand, rewritten with `p(y) = \bar a(y) b(y)`. -/
private lemma pairing_drift_summand (a b : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω) (x : ℤ) (D E : ℕ) :
    conj (a s ω x) * (-((E : ℂ) / 2) * b s ω x) + b s ω x * conj (-((D : ℂ) / 2) * a s ω x)
      + ∑' i, conj (waveDiffC a x i s ω) * waveDiffC b x i s ω =
    (-(D : ℂ) * (conj (a s ω x) * b s ω x) + conj (a s ω (x + 1)) * b s ω (x + 1) +
      conj (a s ω (x - 1)) * b s ω (x - 1)) + ((D : ℂ) / 2 - (E : ℂ) / 2) *
        (conj (a s ω x) * b s ω x) := by
  rw [pairing_tsum_conj_mul]
  simp only [map_mul, map_neg, map_div₀, map_natCast, map_ofNat]
  ring

/-- The complex coefficients of the boundary source `\bar a(±L) dΥ(±L)` on the real Brownian
motions: `\bar a(L) i ψ(L+1)/√2`, `-\bar a(L) ψ(L+1)/√2` on `(L,0)`, `(L,1)`;
`\bar a(-L) i ψ(-L-1)/√2`, `\bar a(-L) ψ(-L-1)/√2` on `(-L-1,0)`, `(-L-1,1)`; `0` elsewhere
(design: `boundaryCoef`). -/
def pairingBoundaryCoef (L : ℕ) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) : ℂ :=
  if i = ((L : ℤ), 0) then conj (a s ω L) * (Complex.I * ψ s ω (L + 1)) / Real.sqrt 2
  else if i = ((L : ℤ), 1) then conj (a s ω L) * (-ψ s ω (L + 1)) / Real.sqrt 2
  else if i = (-(L : ℤ) - 1, 0) then
    conj (a s ω (-L)) * (Complex.I * ψ s ω (-L - 1)) / Real.sqrt 2
  else if i = (-(L : ℤ) - 1, 1) then conj (a s ω (-L)) * ψ s ω (-L - 1) / Real.sqrt 2
  else 0

/-- **Noise cancellation on a box.** If `a_s(ω)` and `b_s(ω)` vanish outside `Λ_L`, then for
every index `i`, `∑_{x ∈ Λ_L} (\bar a(x) c^b_{x,i} + b(x) \bar c^a_{x,i}) = 0`. -/
theorem pairing_coef_sum_box (L : ℕ) (a b : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω)
    (ha : ∀ x, x ∉ box L → a s ω x = 0) (hb : ∀ x, x ∉ box L → b s ω x = 0) (i : ℤ × Fin 2) :
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L,
      (conj (a s ω x) * waveDiffC b x i s ω + b s ω x * conj (waveDiffC a x i s ω)) = 0 := by
  obtain ⟨j, k⟩ := i
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have hS : ∀ x, x ∉ S → x ∉ box L := fun x hx h => hx (pairing_mem_box_iff.1 h)
  rw [pairing_sum_two S _ j fun x h1 h2 => by simp [pairing_waveDiffC_other _ h1 h2]]
  rw [pairing_waveDiffC_self, pairing_waveDiffC_self, pairing_waveDiffC_succ,
    pairing_waveDiffC_succ]
  obtain ⟨hc, -, -⟩ := pairing_sqrt_two
  by_cases h1 : j ∈ S <;> by_cases h2 : j + 1 ∈ S
  · simp only [h1, h2, ↓reduceIte]
    fin_cases k <;> simp [hc] <;> ring
  · simp only [h1, h2, ↓reduceIte, ha _ (hS _ h2), hb _ (hS _ h2)]
    fin_cases k <;> simp
  · simp only [h1, h2, ↓reduceIte, ha _ (hS _ h1), hb _ (hS _ h1)]
    fin_cases k <;> simp
  · simp only [h1, h2, ↓reduceIte, add_zero]

set_option linter.unusedVariables false in
/-- **Drift cancellation on a box.** If `a_s(ω)` and `b_s(ω)` vanish outside `Λ_L`, then
`∑_{x ∈ Λ_L} (\bar a(x) (-(D_L(x)/2) b(x)) + b(x) \overline{(-(D_L(x)/2) a(x))}
  + ∑ᵢ \bar c^a_{x,i} c^b_{x,i}) = 0`. -/
theorem pairing_drift_sum_box (L : ℕ) (a b : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω)
    (ha : ∀ x, x ∉ box L → a s ω x = 0) (hb : ∀ x, x ∉ box L → b s ω x = 0) :
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L,
      (conj (a s ω x) * (-((degree L x : ℂ) / 2) * b s ω x)
        + b s ω x * conj (-((degree L x : ℂ) / 2) * a s ω x)
        + ∑' i, conj (waveDiffC a x i s ω) * waveDiffC b x i s ω) = 0 := by
  have hp : ∀ x, x ∉ Finset.Icc (-(L : ℤ)) L → conj (a s ω x) * b s ω x = 0 := fun x hx => by
    rw [ha x fun h => hx (pairing_mem_box_iff.1 h), map_zero, zero_mul]
  simp only [pairing_drift_summand, sub_self, zero_mul, add_zero]
  exact pairing_laplacian_sum _ hp

/-- **Noise of the pairing with the restriction of a solution on `ℤ`.** If `a_s(ω)` vanishes
outside `Λ_L`, then for every index `i`,
`∑_{x ∈ Λ_L} (\bar a(x) c^ψ_{x,i} + ψ(x) \bar c^a_{x,i}) = pairingBoundaryCoef L a ψ i s ω`. -/
theorem pairing_coef_sum_restrict (L : ℕ) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ) (ω : Ω)
    (ha : ∀ x, x ∉ box L → a s ω x = 0) (i : ℤ × Fin 2) :
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L,
      (conj (a s ω x) * waveDiffC ψ x i s ω + ψ s ω x * conj (waveDiffC a x i s ω)) =
      pairingBoundaryCoef L a ψ i s ω := by
  obtain ⟨j, k⟩ := i
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have hS : ∀ x, x ∉ S → x ∉ box L := fun x hx h => hx (pairing_mem_box_iff.1 h)
  rw [pairing_sum_two S _ j fun x h1 h2 => by simp [pairing_waveDiffC_other _ h1 h2]]
  rw [pairing_waveDiffC_self, pairing_waveDiffC_self, pairing_waveDiffC_succ,
    pairing_waveDiffC_succ]
  obtain ⟨hc, -, -⟩ := pairing_sqrt_two
  have hLS : -(L : ℤ) - 1 ≠ L := by omega
  by_cases h1 : j ∈ S <;> by_cases h2 : j + 1 ∈ S
  · have h1' := Finset.mem_Icc.1 h1
    have h2' := Finset.mem_Icc.1 h2
    have e1 : j ≠ L := by omega
    have e2 : j ≠ -(L : ℤ) - 1 := by omega
    simp only [h1, h2, ↓reduceIte, pairingBoundaryCoef, Prod.mk.injEq, e1, e2, false_and]
    fin_cases k <;> simp [hc] <;> ring
  · have h1' := Finset.mem_Icc.1 h1
    have e1 : j = L := by
      by_contra h
      exact h2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    subst e1
    simp only [h1, h2, ↓reduceIte, ha _ (hS _ h2), pairingBoundaryCoef, Prod.mk.injEq]
    fin_cases k <;> simp <;> ring
  · have h2' := Finset.mem_Icc.1 h2
    have e1 : j = -(L : ℤ) - 1 := by
      by_contra h
      exact h1 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    subst e1
    have e3 : -(L : ℤ) - 1 + 1 = -L := by ring
    have h3 : -(L : ℤ) ∈ S := by rwa [e3] at h2
    simp only [h1, ↓reduceIte, ha _ (hS _ h1), pairingBoundaryCoef, Prod.mk.injEq, e3,
      hLS, false_and, h3]
    fin_cases k <;> simp <;> ring
  · have e1 : j ≠ L := fun h => h1 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have e2 : j ≠ -(L : ℤ) - 1 := fun h => h2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simp only [h1, h2, ↓reduceIte, add_zero, pairingBoundaryCoef, Prod.mk.injEq, e1, e2,
      false_and]

/-- **Drift of the pairing with the restriction of a solution on `ℤ`.** If `L ≥ 1` and `a_s(ω)`
vanishes outside `Λ_L`, then (the drift of `ψ(x)` being `-(D_∞(x)/2) ψ(x) = -ψ(x)`)
`∑_{x ∈ Λ_L} (\bar a(x) (-(D_∞(x)/2) ψ(x)) + ψ(x) \overline{(-(D_L(x)/2) a(x))}
  + ∑ᵢ \bar c^a_{x,i} c^ψ_{x,i}) = -(1/2)(\bar a(L) ψ(L) + \bar a(-L) ψ(-L))`. -/
theorem pairing_drift_sum_restrict {L : ℕ} (hL : 1 ≤ L) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (s : ℝ)
    (ω : Ω) (ha : ∀ x, x ∉ box L → a s ω x = 0) :
    ∑ x ∈ Finset.Icc (-(L : ℤ)) L,
      (conj (a s ω x) * (-((degree ⊤ x : ℂ) / 2) * ψ s ω x)
        + ψ s ω x * conj (-((degree L x : ℂ) / 2) * a s ω x)
        + ∑' i, conj (waveDiffC a x i s ω) * waveDiffC ψ x i s ω) =
      -(1 / 2 : ℂ) * (conj (a s ω L) * ψ s ω L + conj (a s ω (-L)) * ψ s ω (-L)) := by
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have hp : ∀ x, x ∉ S → conj (a s ω x) * ψ s ω x = 0 := fun x hx => by
    rw [ha x fun h => hx (pairing_mem_box_iff.1 h), map_zero, zero_mul]
  simp only [pairing_drift_summand]
  rw [Finset.sum_add_distrib, pairing_laplacian_sum _ hp, zero_add]
  have hL0 : (L : ℤ) ∈ S := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hL1 : -(L : ℤ) ∈ S := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hpt : ∀ x ∈ S, ((degree L x : ℂ) / 2 - (degree ⊤ x : ℂ) / 2) * (conj (a s ω x) * ψ s ω x)
      = -(1 / 2 : ℂ) * ((if x = L then conj (a s ω x) * ψ s ω x else 0) +
        (if x = -(L : ℤ) then conj (a s ω x) * ψ s ω x else 0)) := by
    intro x hx
    have hx' := Finset.mem_Icc.1 hx
    rw [pairing_degree_eq, waveDegree_top]
    have e : (L : ℤ) ≠ -(L : ℤ) := by omega
    by_cases h1 : x = L
    · subst h1
      have e1 : ¬ ((L : ℤ) + 1 ≤ L) := by omega
      have e2 : (-(L : ℤ) ≤ L - 1 ∧ (L : ℤ) - 1 ≤ L) := ⟨by omega, by omega⟩
      simp only [e1, and_false, e2, e, and_self, ↓reduceIte]
      push_cast
      ring
    · by_cases h2 : x = -(L : ℤ)
      · subst h2
        have e1 : ¬ (-(L : ℤ) ≤ -(L : ℤ) - 1) := by omega
        have e2 : (-(L : ℤ) ≤ -(L : ℤ) + 1 ∧ -(L : ℤ) + 1 ≤ L) := ⟨by omega, by omega⟩
        simp only [e1, false_and, e2, h1, and_self, ↓reduceIte]
        push_cast
        ring
      · have e1 : (-(L : ℤ) ≤ x + 1 ∧ x + 1 ≤ L) := ⟨by omega, by omega⟩
        have e2 : (-(L : ℤ) ≤ x - 1 ∧ x - 1 ≤ L) := ⟨by omega, by omega⟩
        simp only [e1, e2, h1, h2, and_self, ↓reduceIte]
        push_cast
        ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [hL0, hL1, ↓reduceIte]

end QSSEPtoKPZ
