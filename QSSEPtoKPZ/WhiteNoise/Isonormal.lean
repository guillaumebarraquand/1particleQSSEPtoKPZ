/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# An isonormal Gaussian process on a separable Hilbert space (task E2a)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proof is task E2a.
`docs/stage5-design.md`, Section 1.2 (g), decision D4‴.

`exists_isonormal`: on a separable real Hilbert space `H` there is, on some probability space
(in `Type`), a family `(W(h))_{h ∈ H}` of measurable real random variables which is a Gaussian
process (Mathlib's `IsGaussianProcess`), with `W(h) ~ N(0, ‖h‖²)`, `Cov(W(h), W(g)) = ⟨h, g⟩`,
and `W` linear up to null sets. (Construction: a Hilbert basis `(e_i)_{i ∈ I}`, `I` countable;
`Ω = ℝ^I` with the product of standard Gaussians (`Measure.infinitePi`), `W(h) = ∑ᵢ ⟨eᵢ, h⟩ ξᵢ`
in `L²`, each partial sum Gaussian, limits by characteristic functions.)

## Proof

* The coordinates `ξᵢ(ω) = ωᵢ` under `P = ⊗ᵢ N(0,1)` are independent standard Gaussians, hence
  orthonormal in `L²(P)`; `T : H → L²(P)`, `T h = ∑ᵢ ⟨eᵢ, h⟩ ξᵢ`, is the composite of the
  coordinate isometry `H ≃ ℓ²(I)` of the Hilbert basis with the isometry `ℓ²(I) → L²(P)` of the
  orthonormal family `(ξᵢ)` (`OrthogonalFamily.linearIsometry`). `W(h)` is the (strongly
  measurable) representative of `T h`.
* A finite partial sum `∑_{i ∈ F} cᵢ ξᵢ` is a linear form of the Gaussian vector `(ξᵢ)_{i ∈ F}`
  (`iIndepFun.hasGaussianLaw`), centred, with variance its squared `L²` norm.
* If `fₐ → g` in `L²(P)` and each `fₐ` has law `N(0, ‖fₐ‖²)`, then `g` has law `N(0, ‖g‖²)`:
  `|φ_{fₐ}(t) - φ_g(t)| ≤ |t| E|fₐ - g| ≤ |t| ‖fₐ - g‖₂`, and Lévy's uniqueness theorem
  (`Measure.ext_of_charFun`). Hence `W(h) ~ N(0, ‖h‖²)`.
* Every linear form of `(W(h))_{h ∈ J}` (`J` finite) is a.s. `W(∑ cⱼ hⱼ)`, hence Gaussian:
  `W` is a Gaussian process. The covariance is `⟨T h, T g⟩_{L²} = ⟨h, g⟩`.

The separability of `H` is not needed for this construction (`Measure.infinitePi` exists for
any index set); it is kept in the statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace QSSEPtoKPZ

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `E|k| ≤ ‖k‖_{L²}` on a probability space. -/
private lemma isonormal_integral_abs_le [IsProbabilityMeasure P] (k : Lp ℝ 2 P) :
    ∫ ω, |k ω| ∂P ≤ ‖k‖ := by
  have h1 : eLpNorm k 1 P ≤ eLpNorm k 2 P := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have h2 : ∫ ω, |k ω| ∂P = (eLpNorm k 1 P).toReal := by
    have := integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable k)
    rw [eLpNorm_one_eq_lintegral_enorm, ← this]
    · rfl
    · exact Lp.aestronglyMeasurable k
  rw [h2, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top k) h1

/-- The variance of a centred element of `L²(P)` is its squared norm. -/
private lemma isonormal_variance_eq (k : Lp ℝ 2 P) (h0 : ∫ ω, k ω ∂P = 0) :
    Var[k; P] = ‖k‖ ^ 2 := by
  rw [variance_of_integral_eq_zero (Lp.aestronglyMeasurable k).aemeasurable h0,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [sq]

/-- `|e^{itx} - e^{ity}| ≤ |t| |x - y|`. -/
private lemma isonormal_norm_cexp_sub_le (t x y : ℝ) :
    ‖cexp (t * x * I) - cexp (t * y * I)‖ ≤ |t| * |x - y| := by
  have : cexp (t * x * I) - cexp (t * y * I) =
      cexp (↑(t * y) * I) * (cexp (I * ↑(t * (x - y))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]

/-- `ω ↦ e^{i t f(ω)}` is integrable on a probability space. -/
private lemma isonormal_integrable_cexp [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) (t : ℝ) : Integrable (fun ω => cexp (t * f ω * I)) P :=
  Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => by
    rw [show (t : ℂ) * f ω = ((t * f ω : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I])

/-- Characteristic functions of two elements of `L²(P)`:
`|φ_f(t) - φ_g(t)| ≤ |t| ‖f - g‖₂`. -/
private lemma isonormal_norm_charFun_sub_le [IsProbabilityMeasure P] (f g : Lp ℝ 2 P) (t : ℝ) :
    ‖charFun (P.map f) t - charFun (P.map g) t‖ ≤ |t| * ‖f - g‖ := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  rw [charFun_apply_real, charFun_apply_real, integral_map hf.aemeasurable (by fun_prop),
    integral_map hg.aemeasurable (by fun_prop),
    ← integral_sub (isonormal_integrable_cexp hf t) (isonormal_integrable_cexp hg t)]
  have hfg : Integrable (fun ω => |(f - g : Lp ℝ 2 P) ω|) P :=
    ((Lp.memLp (f - g)).integrable (by norm_num)).abs
  calc ‖∫ ω, (cexp (t * f ω * I) - cexp (t * g ω * I)) ∂P‖
      ≤ ∫ ω, ‖cexp (t * f ω * I) - cexp (t * g ω * I)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |(f - g : Lp ℝ 2 P) ω| ∂P := by
        refine integral_mono_ae
          ((isonormal_integrable_cexp hf t).sub (isonormal_integrable_cexp hg t)).norm
          (hfg.const_mul _) ?_
        filter_upwards [Lp.coeFn_sub f g] with ω hω
        rw [hω]
        exact isonormal_norm_cexp_sub_le t _ _
    _ = |t| * ∫ ω, |(f - g : Lp ℝ 2 P) ω| ∂P := integral_const_mul _ _
    _ ≤ |t| * ‖f - g‖ := mul_le_mul_of_nonneg_left (isonormal_integral_abs_le _) (abs_nonneg t)

/-- A limit in `L²(P)` of centred Gaussian variables `fₐ ~ N(0, ‖fₐ‖²)` is `N(0, ‖g‖²)`. -/
private lemma isonormal_map_eq_of_tendsto [IsProbabilityMeasure P] {α : Type*} {l : Filter α}
    [l.NeBot] {f : α → Lp ℝ 2 P} {g : Lp ℝ 2 P} (hfg : Tendsto f l (𝓝 g))
    (hlaw : ∀ a, P.map (f a) = gaussianReal 0 (‖f a‖ ^ 2).toNNReal) :
    P.map g = gaussianReal 0 (‖g‖ ^ 2).toNNReal := by
  have hg := (Lp.stronglyMeasurable g).measurable
  have : IsProbabilityMeasure (P.map g) := 
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  refine Measure.ext_of_charFun (funext fun t => ?_)
  refine tendsto_nhds_unique (l := l) (f := fun a => charFun (P.map (f a)) t) ?_ ?_
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun a => norm_nonneg _)
      (fun a => isonormal_norm_charFun_sub_le (f a) g t) ?_
    have : Tendsto (fun a => ‖f a - g‖) l (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hfg
    simpa using this.const_mul |t|
  · simp_rw [hlaw, charFun_gaussianReal]
    have hc : Continuous fun r : ℝ =>
        cexp (t * ((0 : ℝ) : ℂ) * I - ((r ^ 2).toNNReal : ℂ) * t ^ 2 / 2) := by
      fun_prop
    exact (hc.tendsto ‖g‖).comp ((continuous_norm.tendsto g).comp hfg)

end General

section Construction

variable {ι : Type*}

/-- The product `⊗_{i ∈ ι} N(0,1)` of standard Gaussians on `ℝ^ι`. -/
private abbrev isonormalP (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi fun _ : ι => gaussianReal 0 1

/-- The coordinate `ξᵢ(ω) = ωᵢ` has law `N(0,1)`. -/
private lemma isonormal_map_eval (i : ι) :
    (isonormalP ι).map (fun ω => ω i) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ i

/-- `E ξᵢ = 0`. -/
private lemma isonormal_integral_eval (i : ι) : ∫ ω, ω i ∂isonormalP ι = 0 := by
  calc ∫ ω, ω i ∂isonormalP ι = ∫ x, x ∂((isonormalP ι).map (fun ω => ω i)) :=
        (integral_map (φ := fun ω : ι → ℝ => ω i) (measurable_pi_apply i).aemeasurable
          measurable_id.aestronglyMeasurable).symm
    _ = 0 := by rw [isonormal_map_eval, integral_id_gaussianReal]

/-- `E ξᵢ² = 1`. -/
private lemma isonormal_integral_eval_sq (i : ι) : ∫ ω, (ω i) ^ 2 ∂isonormalP ι = 1 := by
  calc ∫ ω, (ω i) ^ 2 ∂isonormalP ι = ∫ x, x ^ 2 ∂((isonormalP ι).map (fun ω => ω i)) :=
        (integral_map (φ := fun ω : ι → ℝ => ω i) (f := fun x : ℝ => x ^ 2)
          (measurable_pi_apply i).aemeasurable
          (by fun_prop)).symm
    _ = 1 := by
        rw [isonormal_map_eval]
        have := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := id) aemeasurable_id
          (by simp [integral_id_gaussianReal])
        rw [variance_id_gaussianReal] at this
        simpa using this.symm

/-- `ξᵢ ∈ L²`. -/
private lemma isonormal_memLp_eval (i : ι) :
    MemLp (fun ω : ι → ℝ => ω i) 2 (isonormalP ι) := by
  simpa using (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ι => gaussianReal 0 1) i)

/-- The coordinates are independent. -/
private lemma isonormal_iIndepFun :
    iIndepFun (fun (i : ι) (ω : ι → ℝ) => ω i) (isonormalP ι) :=
  iIndepFun_infinitePi (P := fun _ : ι => gaussianReal 0 1) (X := fun _ x => x)
    (fun _ => measurable_id)

/-- The coordinate `ξᵢ` as an element of `L²(P)`. -/
private def isonormalXi (ι : Type*) (i : ι) : Lp ℝ 2 (isonormalP ι) :=
  (isonormal_memLp_eval i).toLp _

private lemma isonormalXi_ae (i : ι) : isonormalXi ι i =ᵐ[isonormalP ι] fun ω => ω i :=
  (isonormal_memLp_eval i).coeFn_toLp

/-- The coordinates are orthonormal in `L²(P)`. -/
private lemma isonormal_orthonormal : Orthonormal ℝ (isonormalXi ι) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_def]
  have hij : ∫ ω, ⟪isonormalXi ι i ω, isonormalXi ι j ω⟫_ℝ ∂isonormalP ι =
      ∫ ω, ω i * ω j ∂isonormalP ι := by
    refine integral_congr_ae ?_
    filter_upwards [isonormalXi_ae i, isonormalXi_ae j] with ω hi hj
    simp [hi, hj, mul_comm]
  rw [hij]
  split_ifs with h
  · subst h
    simp_rw [← sq]
    exact isonormal_integral_eval_sq i
  · have hind := (isonormal_iIndepFun (ι := ι)).indepFun h
    have := hind.integral_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, isonormal_integral_eval, zero_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The isometry `T : H → L²(P)`, `T h = ∑ᵢ ⟨eᵢ, h⟩ ξᵢ`. -/
private def isonormalT (b : HilbertBasis ι ℝ H) : H →ₗᵢ[ℝ] Lp ℝ 2 (isonormalP ι) :=
  (isonormal_orthonormal (ι := ι)).orthogonalFamily.linearIsometry.comp
    b.repr.toLinearIsometry

private lemma isonormalT_hasSum (b : HilbertBasis ι ℝ H) (h : H) :
    HasSum (fun i => ⟪b i, h⟫_ℝ • isonormalXi ι i) (isonormalT b h) := by
  have := (isonormal_orthonormal (ι := ι)).orthogonalFamily.hasSum_linearIsometry (b.repr h)
  simpa [isonormalT, HilbertBasis.repr_apply_apply] using this

/-- A finite partial sum `∑_{i ∈ F} cᵢ ξᵢ` has law `N(0, ‖∑_{i ∈ F} cᵢ ξᵢ‖₂²)`. -/
private lemma isonormal_map_partialSum (F : Finset ι) (c : ι → ℝ) :
    (isonormalP ι).map (∑ i ∈ F, c i • isonormalXi ι i : Lp ℝ 2 (isonormalP ι)) =
      gaussianReal 0 (‖∑ i ∈ F, c i • isonormalXi ι i‖ ^ 2).toNNReal := by
  set S : Lp ℝ 2 (isonormalP ι) := ∑ i ∈ F, c i • isonormalXi ι i with hS_def
  have hS : (S : (ι → ℝ) → ℝ) =ᵐ[isonormalP ι] fun ω => ∑ i ∈ F, c i * ω i := by
    filter_upwards [Lp.coeFn_fun_finsetSum F (fun i => c i • isonormalXi ι i),
      (eventually_all_finset F).2 (fun i _ => Lp.coeFn_smul (c i) (isonormalXi ι i)),
      (eventually_all_finset F).2 (fun i _ => isonormalXi_ae (ι := ι) i)] with ω h1 h2 h3
    rw [h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h2 i hi, Pi.smul_apply, h3 i hi, smul_eq_mul]
  -- the Gaussian vector `(ξᵢ)_{i ∈ F}`
  have hV : HasGaussianLaw (fun ω (j : F) => ω (j : ι)) (isonormalP ι) := by
    refine iIndepFun.hasGaussianLaw (X := fun (j : F) (ω : ι → ℝ) => ω (j : ι))
      (fun j => ?_) ((isonormal_iIndepFun (ι := ι)).precomp Subtype.val_injective)
    exact HasLaw.hasGaussianLaw ⟨(measurable_pi_apply _).aemeasurable, isonormal_map_eval (j : ι)⟩
  let L : (F → ℝ) →L[ℝ] ℝ := ∑ j : F, c j • ContinuousLinearMap.proj j
  have hZ : HasGaussianLaw (fun ω => ∑ i ∈ F, c i * ω i) (isonormalP ι) := by
    have := hV.map L
    convert this using 1
    funext ω
    simp only [L, Function.comp_apply, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul]
    exact (Finset.sum_coe_sort F (fun i => c i * ω i)).symm
  have hSG : HasGaussianLaw S (isonormalP ι) := hZ.congr hS.symm
  have h0 : ∫ ω, S ω ∂isonormalP ι = 0 := by
    rw [integral_congr_ae hS, integral_finsetSum]
    · simp [integral_const_mul, isonormal_integral_eval]
    · intro i _
      exact ((isonormal_memLp_eval i).integrable (by norm_num)).const_mul _
  rw [hSG.map_eq_gaussianReal, h0, isonormal_variance_eq S h0]

/-- `T h` has law `N(0, ‖h‖²)`. -/
private lemma isonormalT_map (b : HilbertBasis ι ℝ H) (h : H) :
    (isonormalP ι).map (isonormalT b h) = gaussianReal 0 (‖h‖ ^ 2).toNNReal := by
  rw [← (isonormalT b).norm_map h]
  exact isonormal_map_eq_of_tendsto (isonormalT_hasSum b h)
    (fun F => isonormal_map_partialSum F _)

/-- `T` commutes with finite linear combinations, almost surely. -/
private lemma isonormalT_sum (b : HilbertBasis ι ℝ H) {α : Type*} (s : Finset α) (a : α → ℝ)
    (v : α → H) :
    (isonormalT b (∑ x ∈ s, a x • v x) : (ι → ℝ) → ℝ) =ᵐ[isonormalP ι]
      fun ω => ∑ x ∈ s, a x * isonormalT b (v x) ω := by
  rw [map_sum]
  simp_rw [map_smul]
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun x => a x • isonormalT b (v x)),
    (eventually_all_finset s).2 (fun x _ => Lp.coeFn_smul (a x) (isonormalT b (v x)))]
    with ω h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun x hx => by rw [h2 x hx]; rfl

/-- `E[T h] = 0`. -/
private lemma isonormalT_integral (b : HilbertBasis ι ℝ H) (h : H) :
    ∫ ω, isonormalT b h ω ∂isonormalP ι = 0 := by
  calc ∫ ω, isonormalT b h ω ∂isonormalP ι
      = ∫ x, x ∂((isonormalP ι).map (isonormalT b h)) :=
        (integral_map (Lp.stronglyMeasurable _).measurable.aemeasurable
          measurable_id.aestronglyMeasurable).symm
    _ = 0 := by rw [isonormalT_map, integral_id_gaussianReal]

end Construction

/-- **Isonormal Gaussian process** on a separable real Hilbert space `H`. -/
theorem exists_isonormal (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : H → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ h, Measurable (W h)) ∧ IsGaussianProcess W P ∧
      (∀ h, HasLaw (W h) (gaussianReal 0 (‖h‖ ^ 2).toNNReal) P) ∧
      (∀ h g, cov[W h, W g; P] = ⟪h, g⟫_ℝ) ∧
      ∀ (a b : ℝ) (h g : H), W (a • h + b • g) =ᵐ[P] fun ω => a * W h ω + b * W g ω := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ H
  have hmeas : ∀ h, Measurable (isonormalT b h : (w → ℝ) → ℝ) :=
    fun h => (Lp.stronglyMeasurable _).measurable
  refine ⟨w → ℝ, inferInstance, isonormalP w, fun h => isonormalT b h, inferInstance, hmeas,
    ?_, fun h => ⟨(hmeas h).aemeasurable, isonormalT_map b h⟩, ?_, ?_⟩
  · -- Gaussian process: every linear form of `(W h)_{h ∈ J}` is a.s. some `W k`
    refine ⟨fun J => ⟨((Finset.measurable_restrict J).comp
      (measurable_pi_iff.2 hmeas)).aemeasurable, ?_⟩⟩
    refine isGaussian_of_map_eq_gaussianReal fun L => ?_
    classical
    set c : J → ℝ := fun j => L fun j' => if j = j' then 1 else 0
    refine ⟨0, (‖∑ j : J, c j • (j : H)‖ ^ 2).toNNReal, ?_⟩
    rw [Measure.map_map L.continuous.measurable (by fun_prop),
      ← isonormalT_map b (∑ j : J, c j • (j : H))]
    refine Measure.map_congr ?_
    filter_upwards [isonormalT_sum b Finset.univ c (fun j : J => (j : H))] with ω hω
    have hL := L.toLinearMap.pi_apply_eq_sum_univ (J.restrict fun x => isonormalT b x ω)
    simp only [ContinuousLinearMap.coe_coe] at hL
    rw [hω, Function.comp_apply, hL]
    simp [c, mul_comm]
  · intro h g
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), isonormalT_integral, isonormalT_integral,
      mul_zero, sub_zero, ← (isonormalT b).inner_map_map h g, L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [mul_comm]
  · intro a c h g
    have := isonormalT_sum b (Finset.univ : Finset (Fin 2)) ![a, c] ![h, g]
    simpa [Fin.sum_univ_two] using this

end QSSEPtoKPZ
