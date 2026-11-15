/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Levy
public import QSSEPtoKPZ.Martingales.Covariation

/-!
# Brackets of linear combinations of interval martingales (task G7b)

Let `S : ℝ → ℝ → Ω → ℝ` be such that the processes `M_i(t) = S(t, b_i) - S(t, a_i)` (`a_i ≤ b_i`)
have covariations `⟨M_i, M_j⟩_t = t C_{ij}`, with `C_{ij} = |(a_i, b_i] ∩ (a_j, b_j]|`
(`levyMultiCov`). For `u ∈ ℝ^ι`, the linear combination `N = ∑ᵢ uᵢ Mᵢ` (`levyMultiN`) has bracket
`Q(u) t`, with `Q(u) = ∑ᵢⱼ uᵢ uⱼ C_{ij}` (`levyMultiQ`): bilinearity of the covariation, done by
hand on the conditional expectations. `Q(u) ≥ 0` since `Q(u) = 𝔼 N_1²` when `S(0, ·) = 0`.

Then Lévy's characterization (`levy_setIntegral`, task G7a) gives the conditional characteristic
function of the rectangle masses `ξ((s, t] × (aᵢ, bᵢ])`:
`∫_A exp(i ∑ᵢ uᵢ ξ((s,t] × (aᵢ,bᵢ])) dℙ = exp(-Q(u) (t - s) / 2) ℙ(A)` for `A ∈ 𝓖_s`
(`levyMulti_setIntegral`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The covariance matrix `C_{ij} = |(a_i, b_i] ∩ (a_j, b_j]|` of the white noise masses of the
intervals `(a_i, b_i]`. -/
def levyMultiCov {ι : Type*} (a b : ι → ℝ) (i j : ι) : ℝ :=
  (volume (Set.Ioc (a i) (b i) ∩ Set.Ioc (a j) (b j))).toReal

/-- The quadratic form `Q(u) = ∑ᵢⱼ uᵢ uⱼ C_{ij}`. -/
def levyMultiQ {ι : Type*} [Fintype ι] (a b u : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * u j * levyMultiCov a b i j

/-- The linear combination `N_t = ∑ᵢ uᵢ (S(t, bᵢ) - S(t, aᵢ))`. -/
def levyMultiN {ι : Type*} [Fintype ι] (S : ℝ → ℝ → Ω → ℝ) (a b u : ι → ℝ) (r : ℝ) (ω : Ω) :
    ℝ :=
  ∑ i, u i * (S r (b i) ω - S r (a i) ω)

/-- Conditional expectation of a finite sum, termwise. -/
private lemma levyMulti_condExp_sum {μ : Measure Ω} {m : MeasurableSpace Ω} {ι : Type*}
    [Fintype ι] {f g : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (h : ∀ i, μ[f i | m] =ᵐ[μ] g i) :
    μ[fun ω => ∑ i, f i ω | m] =ᵐ[μ] fun ω => ∑ i, g i ω := by
  have h1 := condExp_finsetSum (s := Finset.univ) (fun i _ => hf i) m
  have e1 : (fun ω => ∑ i, f i ω) = ∑ i, f i := by ext ω; simp [Finset.sum_apply]
  rw [e1]
  have h2 : ∀ᵐ ω ∂μ, ∀ i, μ[f i | m] ω = g i ω := ae_all_iff.2 h
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h2 i

/-- Conditional expectation of a constant multiple. -/
private lemma levyMulti_condExp_const_mul {μ : Measure Ω} {m : MeasurableSpace Ω} (c : ℝ)
    {f g : Ω → ℝ} (h : μ[f | m] =ᵐ[μ] g) :
    μ[fun ω => c * f ω | m] =ᵐ[μ] fun ω => c * g ω := by
  have h1 : μ[c • f | m] =ᵐ[μ] c • μ[f | m] := condExp_smul c f m
  filter_upwards [h1, h] with ω h1 h2
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  rw [show (fun ω => c * f ω) = c • f from rfl, h1, h2]

variable {μ : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]
  {a b : ι → ℝ}

/-- `N_t` is square integrable. -/
theorem levyMulti_memLp {T : ℝ}
    (hcov : ∀ i j, HasCovariation T 𝓖 (fun t ω => S t (b i) ω - S t (a i) ω)
      (fun t ω => S t (b j) ω - S t (a j) ω) (fun t _ => t * levyMultiCov a b i j) μ)
    (u : ι → ℝ) {t : ℝ≥0} (htT : (t : ℝ) ≤ T) : MemLp (levyMultiN S a b u t) 2 μ :=
  memLp_finsetSum _ fun i _ => ((hcov i i).left.memLp t htT).const_mul (u i)

/-- `N_t² - Q(u) t` is a martingale on `[0, T]`. -/
theorem levyMulti_condExp_sq [IsFiniteMeasure μ] {T : ℝ}
    (hcov : ∀ i j, HasCovariation T 𝓖 (fun t ω => S t (b i) ω - S t (a i) ω)
      (fun t ω => S t (b j) ω - S t (a j) ω) (fun t _ => t * levyMultiCov a b i j) μ)
    (u : ι → ℝ) {s t : ℝ≥0} (hst : s ≤ t) (htT : (t : ℝ) ≤ T) :
    μ[fun ω => levyMultiN S a b u t ω ^ 2 - levyMultiQ a b u * t | 𝓖 s] =ᵐ[μ]
      fun ω => levyMultiN S a b u s ω ^ 2 - levyMultiQ a b u * s := by
  set M : ι → ℝ → Ω → ℝ := fun i r ω => S r (b i) ω - S r (a i) ω with hM
  have hexp : ∀ r : ℝ, (fun ω => levyMultiN S a b u r ω ^ 2 - levyMultiQ a b u * r) =
      fun ω => ∑ i, ∑ j, u i * (u j * (M i r ω * M j r ω - r * levyMultiCov a b i j)) := by
    intro r; ext ω
    simp only [levyMultiN, levyMultiQ, hM]
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp t, hexp s]
  have hint : ∀ i j, Integrable
      (fun ω => M i t ω * M j t ω - t * levyMultiCov a b i j) μ := by
    intro i j
    have h1 := ((hcov i j).left.memLp t htT).integrable_mul ((hcov i j).right.memLp t htT)
    exact h1.sub (integrable_const _)
  refine levyMulti_condExp_sum (fun i => integrable_finsetSum _ fun j _ =>
    ((hint i j).const_mul (u j)).const_mul (u i)) fun i => ?_
  refine levyMulti_condExp_sum (fun j => ((hint i j).const_mul (u j)).const_mul (u i))
    fun j => ?_
  exact levyMulti_condExp_const_mul _ (levyMulti_condExp_const_mul _
    ((hcov i j).condExp_mul s t hst htT))

/-- `N_0 = 0` when `S(0, ·) = 0`. -/
lemma levyMultiN_zero (h0 : ∀ x ω, S 0 x ω = 0) (u : ι → ℝ) (ω : Ω) :
    levyMultiN S a b u 0 ω = 0 := by
  simp [levyMultiN, h0]

/-- `Q(u) ≥ 0`, since `Q(u) = 𝔼 N_1²`. -/
theorem levyMultiQ_nonneg [IsProbabilityMeasure μ] (h0 : ∀ x ω, S 0 x ω = 0)
    (hcov : ∀ i j, HasCovariation 1 𝓖 (fun t ω => S t (b i) ω - S t (a i) ω)
      (fun t ω => S t (b j) ω - S t (a j) ω) (fun t _ => t * levyMultiCov a b i j) μ)
    (u : ι → ℝ) : 0 ≤ levyMultiQ a b u := by
  have h := levyMulti_condExp_sq hcov u (s := 0) (t := 1) zero_le (by simp)
  have hi := integral_congr_ae h
  rw [integral_condExp (𝓖.le 0)] at hi
  have hN1 : Integrable (fun ω => levyMultiN S a b u ((1 : ℝ≥0) : ℝ) ω ^ 2) μ :=
    (levyMulti_memLp hcov u (t := 1) (by simp)).integrable_sq
  rw [integral_sub hN1 (integrable_const _)] at hi
  simp only [NNReal.coe_zero, levyMultiN_zero h0, mul_zero, sub_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, integral_const,
    probReal_univ, one_smul, NNReal.coe_one, mul_one] at hi
  have : 0 ≤ ∫ ω, levyMultiN S a b u 1 ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  linarith

/-- **Bracket of a linear combination.** `⟨N⟩_t = Q(u) t` on `[0, T]`. -/
theorem levyMulti_hasBracket [IsFiniteMeasure μ] {T : ℝ}
    (hcov : ∀ i j, HasCovariation T 𝓖 (fun t ω => S t (b i) ω - S t (a i) ω)
      (fun t ω => S t (b j) ω - S t (a j) ω) (fun t _ => t * levyMultiCov a b i j) μ)
    (u : ι → ℝ) (hQ : 0 ≤ levyMultiQ a b u) :
    HasBracket T 𝓖 (levyMultiN S a b u) (fun r _ => levyMultiQ a b u * r) μ where
  cont := by
    have h : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun t => S t (b i) ω - S t (a i) ω) (Set.Icc 0 T) :=
      ae_all_iff.2 fun i => (hcov i i).left.cont
    filter_upwards [h] with ω hω
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hω i)
  memLp t htT := levyMulti_memLp hcov u htT
  condExp s t hst htT := by
    refine levyMulti_condExp_sum (fun i =>
      (((hcov i i).left.memLp t htT).integrable one_le_two).const_mul (u i)) fun i => ?_
    exact levyMulti_condExp_const_mul _ ((hcov i i).left.condExp s t hst htT)
  integrable_bracket _ _ := integrable_const _
  zero := ae_of_all _ fun _ => by simp
  mono := ae_of_all _ fun _ x _ y _ hxy => mul_le_mul_of_nonneg_left hxy hQ
  cont_bracket := ae_of_all _ fun _ => (continuousOn_const.mul continuousOn_id)
  condExp_sq s t hst htT := levyMulti_condExp_sq hcov u hst htT

/-- **Conditional characteristic function of the rectangle masses.** For `A ∈ 𝓖_s`,
`∫_A exp(i ∑ᵢ uᵢ ξ((s,t] × (aᵢ,bᵢ])) dℙ = exp(-Q(u) (t - s) / 2) ℙ(A)`. -/
theorem levyMulti_setIntegral [IsProbabilityMeasure μ] (h0 : ∀ x ω, S 0 x ω = 0)
    (hcov : ∀ (T : ℝ) (a b a' b' : ℝ), a ≤ b → a' ≤ b' →
      HasCovariation T 𝓖 (fun t ω => S t b ω - S t a ω) (fun t ω => S t b' ω - S t a' ω)
        (fun t _ => t * (volume (Set.Ioc a b ∩ Set.Ioc a' b')).toReal) μ)
    (hab : ∀ i, a i ≤ b i) (u : ι → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Complex.exp (((∑ i, u i * rectMass S s t (a i) (b i) ω : ℝ) : ℂ) * Complex.I) ∂μ =
      (Real.exp (-(levyMultiQ a b u * ((t : ℝ) - s) / 2)) : ℂ) * (μ.real A : ℂ) := by
  have hc : ∀ T : ℝ, ∀ i j, HasCovariation T 𝓖 (fun t ω => S t (b i) ω - S t (a i) ω)
      (fun t ω => S t (b j) ω - S t (a j) ω) (fun t _ => t * levyMultiCov a b i j) μ :=
    fun T i j => hcov T _ _ _ _ (hab i) (hab j)
  have hQ := levyMultiQ_nonneg h0 (hc 1) u
  have key := levy_setIntegral hQ (levyMulti_hasBracket (hc t) u hQ) hst le_rfl 1 hA
  have e : ∀ ω, (∑ i, u i * rectMass S s t (a i) (b i) ω) =
      1 * (levyMultiN S a b u t ω - levyMultiN S a b u s ω) := by
    intro ω
    simp only [levyMultiN, rectMass, one_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [key]
  congr 4
  ring

end QSSEPtoKPZ
