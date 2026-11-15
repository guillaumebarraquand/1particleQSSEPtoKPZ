/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.WhiteNoise.Isonormal
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Construction of a space-time white noise from an isonormal process (task E2b)

Let `H = L²(ℝ²)` and `W` an isonormal Gaussian process on `H` (`exists_isonormal`). With the
signed indicator `φₓ = 𝟙_{(0,x]} - 𝟙_{(x,0]}` and `Gₜₓ(r, y) = 𝟙_{(0,t]}(r) φₓ(y)` (an element of
`H`, difference of two `indicatorConstLp`), put `S(t, x) = W(Gₜₓ)` and
`𝓖_t = σ(S(r, x) : 0 ≤ r ≤ t, x ∈ ℝ)`.

* By linearity of `W` (up to null sets), the rectangle mass `rectMass S s t a b` equals
  `W(Rₛₜₐᵦ)` almost surely, where `Rₛₜₐᵦ(r, y) = (𝟙_{(0,t]} - 𝟙_{(0,s]})(r) (φ_b - φ_a)(y)`.
* For `0 ≤ s ≤ t`, `a ≤ b`: `Rₛₜₐᵦ = 𝟙_{(s,t]} ⊗ 𝟙_{(a,b]}`, so `‖Rₛₜₐᵦ‖² = (t - s)(b - a)`.
* The pointwise products `Rₛₜₐᵦ · G_{r x}` (`r ≤ s`) and `R_{s t aᵢ aᵢ₊₁} · R_{s t aⱼ aⱼ₊₁}`
  (`i ≠ j`, `a` monotone) vanish, so the corresponding covariances vanish, and Mathlib's
  `IsGaussianProcess.indepFun_of_covariance_eq_zero` and `iIndepFun_of_covariance_eq_zero` give
  the independence clauses of `IsWhiteNoise`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace QSSEPtoKPZ

/-- `L²(ℝ²)` is separable (Mathlib's `Lp.SecondCountableTopology`). -/
instance wnExist_separableSpace :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume : Measure (ℝ × ℝ))) :=
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  inferInstance

/-- The signed indicator `φₓ(y) = 𝟙_{(0,x]}(y) - 𝟙_{(x,0]}(y)`, so that
`φ_b - φ_a = 𝟙_{(a,b]}` for `a ≤ b`. -/
def wnExistSgn (x y : ℝ) : ℝ := (Set.Ioc 0 x).indicator 1 y - (Set.Ioc x 0).indicator 1 y

/-- `φ_b - φ_a = 𝟙_{(a,b]}` for `a ≤ b`. -/
lemma wnExistSgn_sub {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    wnExistSgn b y - wnExistSgn a y = (Set.Ioc a b).indicator 1 y := by
  simp only [wnExistSgn, Set.indicator, Set.mem_Ioc, Pi.one_apply]
  split_ifs <;> grind

/-- `𝟙_{(0,t]} - 𝟙_{(0,s]} = 𝟙_{(s,t]}` for `0 ≤ s ≤ t`. -/
lemma wnExist_ind_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (y : ℝ) :
    (Set.Ioc 0 t).indicator (1 : ℝ → ℝ) y - (Set.Ioc 0 s).indicator 1 y =
      (Set.Ioc s t).indicator 1 y := by
  simp only [Set.indicator, Set.mem_Ioc, Pi.one_apply]
  split_ifs <;> grind

/-- Rectangles `(a,b] × (c,d]` have finite Lebesgue measure in `ℝ²`. -/
lemma wnExist_volume_rect_ne_top (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)) (Set.Ioc a b ×ˢ Set.Ioc c d) ≠ ∞ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne

/-- `G_{t x} = 𝟙_{(0,t] × (0,x]} - 𝟙_{(0,t] × (x,0]} ∈ L²(ℝ²)`. -/
def wnExistG (t x : ℝ) : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  indicatorConstLp 2 (measurableSet_Ioc.prod measurableSet_Ioc)
      (wnExist_volume_rect_ne_top 0 t 0 x) (1 : ℝ) -
    indicatorConstLp 2 (measurableSet_Ioc.prod measurableSet_Ioc)
      (wnExist_volume_rect_ne_top 0 t x 0) (1 : ℝ)

/-- A representative of `G_{t x}`: `(r, y) ↦ 𝟙_{(0,t]}(r) φₓ(y)`. -/
lemma wnExistG_ae (t x : ℝ) :
    (wnExistG t x : ℝ × ℝ → ℝ) =ᵐ[volume]
      fun p => (Set.Ioc 0 t).indicator 1 p.1 * wnExistSgn x p.2 := by
  unfold wnExistG
  filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 (measurableSet_Ioc.prod measurableSet_Ioc)
      (wnExist_volume_rect_ne_top 0 t 0 x) (1 : ℝ))
      (indicatorConstLp 2 (measurableSet_Ioc.prod measurableSet_Ioc)
      (wnExist_volume_rect_ne_top 0 t x 0) (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc.prod measurableSet_Ioc)
      (hμs := wnExist_volume_rect_ne_top 0 t 0 x) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc.prod measurableSet_Ioc)
      (hμs := wnExist_volume_rect_ne_top 0 t x 0) (c := (1 : ℝ))] with p h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  obtain ⟨r, y⟩ := p
  have e1 := Set.indicator_prod_one (M₀ := ℝ) (s := Set.Ioc 0 t) (t := Set.Ioc 0 x) (i := r)
    (j := y)
  have e2 := Set.indicator_prod_one (M₀ := ℝ) (s := Set.Ioc 0 t) (t := Set.Ioc x 0) (i := r)
    (j := y)
  simp only [Pi.one_def] at e1 e2
  rw [e1, e2, wnExistSgn, mul_sub]
  rfl

/-- `R_{s t a b} = G_{t b} - G_{t a} - G_{s b} + G_{s a}`, the element of `L²(ℝ²)` whose image
under `W` is the mass of the rectangle `(s,t] × (a,b]`. -/
def wnExistR (s t a b : ℝ) : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  wnExistG t b - wnExistG t a - wnExistG s b + wnExistG s a

/-- A representative of `R_{s t a b}`. -/
lemma wnExistR_ae (s t a b : ℝ) :
    (wnExistR s t a b : ℝ × ℝ → ℝ) =ᵐ[volume]
      fun p => ((Set.Ioc 0 t).indicator 1 p.1 - (Set.Ioc 0 s).indicator 1 p.1) *
        (wnExistSgn b p.2 - wnExistSgn a p.2) := by
  unfold wnExistR
  filter_upwards [Lp.coeFn_add (wnExistG t b - wnExistG t a - wnExistG s b) (wnExistG s a),
    Lp.coeFn_sub (wnExistG t b - wnExistG t a) (wnExistG s b),
    Lp.coeFn_sub (wnExistG t b) (wnExistG t a), wnExistG_ae t b, wnExistG_ae t a,
    wnExistG_ae s b, wnExistG_ae s a] with p h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, Pi.sub_apply, h4, h5, h6, h7]
  ring

/-- The `L²` inner product computed on representatives. -/
lemma wnExist_inner_eq {u v : Lp ℝ 2 (volume : Measure (ℝ × ℝ))} {f g : ℝ × ℝ → ℝ}
    (hu : (u : ℝ × ℝ → ℝ) =ᵐ[volume] f) (hv : (v : ℝ × ℝ → ℝ) =ᵐ[volume] g) :
    ⟪u, v⟫_ℝ = ∫ p, f p * g p := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with p h1 h2
  rw [h1, h2, real_inner_eq_re_inner]
  simp [mul_comm]

/-- `⟨R_{s t a b}, G_{r x}⟩ = 0` for `r ≤ s ≤ t`: the time intervals `(0,r]` and `(s,t]` are
disjoint. -/
lemma wnExist_inner_R_G {s t r : ℝ} (hst : s ≤ t) (hrs : r ≤ s) (a b x : ℝ) :
    ⟪wnExistR s t a b, wnExistG r x⟫_ℝ = 0 := by
  rw [wnExist_inner_eq (wnExistR_ae s t a b) (wnExistG_ae r x)]
  refine (integral_congr_ae (Eventually.of_forall fun p => ?_)).trans (integral_zero _ ℝ)
  simp only [Set.indicator, Set.mem_Ioc, Pi.one_apply]
  split_ifs <;> grind

/-- `⟨R_{s t a b}, R_{s t c d}⟩ = 0` if `a ≤ b ≤ c ≤ d`: the space intervals are disjoint. -/
lemma wnExist_inner_R_R {s t a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ⟪wnExistR s t a b, wnExistR s t c d⟫_ℝ = 0 := by
  rw [wnExist_inner_eq (wnExistR_ae s t a b) (wnExistR_ae s t c d)]
  refine (integral_congr_ae (Eventually.of_forall fun p => ?_)).trans (integral_zero _ ℝ)
  simp only [wnExistSgn_sub hab, wnExistSgn_sub hcd]
  simp only [Set.indicator, Set.mem_Ioc, Pi.one_apply]
  split_ifs <;> grind

/-- `‖R_{s t a b}‖² = (t - s)(b - a)` for `0 ≤ s ≤ t`, `a ≤ b`. -/
lemma wnExist_norm_R_sq {s t a b : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hab : a ≤ b) :
    ‖wnExistR s t a b‖ ^ 2 = (t - s) * (b - a) := by
  rw [← real_inner_self_eq_norm_sq, wnExist_inner_eq (wnExistR_ae s t a b) (wnExistR_ae s t a b)]
  have key : ∀ p : ℝ × ℝ, (((Set.Ioc 0 t).indicator 1 p.1 - (Set.Ioc 0 s).indicator 1 p.1) *
        (wnExistSgn b p.2 - wnExistSgn a p.2)) *
      (((Set.Ioc 0 t).indicator 1 p.1 - (Set.Ioc 0 s).indicator 1 p.1) *
        (wnExistSgn b p.2 - wnExistSgn a p.2)) =
      (Set.Ioc s t).indicator (1 : ℝ → ℝ) p.1 * (Set.Ioc a b).indicator (1 : ℝ → ℝ) p.2 := by
    intro p
    rw [wnExist_ind_sub hs hst, wnExistSgn_sub hab]
    simp only [Set.indicator, Set.mem_Ioc, Pi.one_apply]
    split_ifs <;> ring
  simp_rw [key]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun r => (Set.Ioc s t).indicator (1 : ℝ → ℝ) r)
    (fun y => (Set.Ioc a b).indicator (1 : ℝ → ℝ) y), integral_indicator_one measurableSet_Ioc,
    integral_indicator_one measurableSet_Ioc, Real.volume_real_Ioc_of_le hst,
    Real.volume_real_Ioc_of_le hab]

/-! ### The white noise built from an isonormal process -/

section Noise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {W : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) → Ω → ℝ}

/-- Covariances only depend on the almost-everywhere classes of the random variables. -/
private lemma wnExist_cov_congr {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- The random field `S(t, x) = W(G_{t x})`, distribution function of the white noise. -/
def wnExistS (W : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) → Ω → ℝ) (t x : ℝ) (ω : Ω) : ℝ :=
  W (wnExistG t x) ω

/-- `rectMass S s t a b` is measurable when each `W(h)` is. -/
lemma wnExist_measurable_rectMass (hW : ∀ h, Measurable (W h)) (s t a b : ℝ) :
    Measurable (rectMass (wnExistS W) s t a b) :=
  (((hW _).sub (hW _)).sub (hW _)).add (hW _)

/-- By linearity of `W` (up to null sets), `rectMass S s t a b = W(R_{s t a b})` a.s. -/
lemma wnExist_rectMass_ae
    (hlin : ∀ (a b : ℝ) (h g : Lp ℝ 2 (volume : Measure (ℝ × ℝ))),
      W (a • h + b • g) =ᵐ[P] fun ω => a * W h ω + b * W g ω) (s t a b : ℝ) :
    rectMass (wnExistS W) s t a b =ᵐ[P] W (wnExistR s t a b) := by
  have hadd : ∀ h g, W (h + g) =ᵐ[P] fun ω => W h ω + W g ω := fun h g => by
    simpa using hlin 1 1 h g
  have hsub : ∀ h g, W (h - g) =ᵐ[P] fun ω => W h ω - W g ω := fun h g => by
    simpa [sub_eq_add_neg] using hlin 1 (-1) h g
  unfold wnExistR
  filter_upwards [hadd (wnExistG t b - wnExistG t a - wnExistG s b) (wnExistG s a),
    hsub (wnExistG t b - wnExistG t a) (wnExistG s b),
    hsub (wnExistG t b) (wnExistG t a)] with ω h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- The filtration `𝓖_t = σ(S(r, x) : 0 ≤ r ≤ t, x ∈ ℝ)` generated by a random field `S`. -/
def wnExistFilt (S : ℝ → ℝ → Ω → ℝ) (hS : ∀ t x, Measurable (S t x)) :
    Filtration ℝ≥0 mΩ where
  seq t := ⨆ (p : ℝ≥0 × ℝ) (_ : p.1 ≤ t), MeasurableSpace.comap (S p.1 p.2) inferInstance
  mono' _ _ hst := iSup₂_mono' fun p hp => ⟨p, hp.trans hst, le_rfl⟩
  le' _ := iSup₂_le fun _ _ => (hS _ _).comap_le

/-- **Construction of a white noise.** If `W` is an isonormal Gaussian process on `L²(ℝ²)`
(measurable, Gaussian process, `W(h) ~ N(0, ‖h‖²)`, `Cov(W(h), W(g)) = ⟨h, g⟩`, linear a.s.),
then `S(t, x) = W(𝟙_{(0,t]} ⊗ φₓ)` is the distribution function of a space-time white noise
with respect to the filtration it generates. -/
theorem wnExist_isWhiteNoise [IsProbabilityMeasure P] (hW : ∀ h, Measurable (W h))
    (hGP : IsGaussianProcess W P)
    (hlaw : ∀ h, HasLaw (W h) (gaussianReal 0 (‖h‖ ^ 2).toNNReal) P)
    (hcov : ∀ h g, cov[W h, W g; P] = ⟪h, g⟫_ℝ)
    (hlin : ∀ (a b : ℝ) (h g : Lp ℝ 2 (volume : Measure (ℝ × ℝ))),
      W (a • h + b • g) =ᵐ[P] fun ω => a * W h ω + b * W g ω) :
    IsWhiteNoise (wnExistFilt (wnExistS W) fun _ _ => hW _) (wnExistS W) P where
  adapted t x := measurable_iff_comap_le.2 (le_iSup₂_of_le (t, x) le_rfl le_rfl)
  gaussian s t a b hst hab := by
    have hn := wnExist_norm_R_sq (s := s) (t := t) s.2 (by exact_mod_cast hst) hab
    have hv : (‖wnExistR s t a b‖ ^ 2).toNNReal = (t - s) * (b - a).toNNReal := by
      rw [hn]
      ext
      rw [Real.coe_toNNReal _ (mul_nonneg (sub_nonneg.2 (by exact_mod_cast hst))
        (sub_nonneg.2 hab)), NNReal.coe_mul, NNReal.coe_sub hst,
        Real.coe_toNNReal _ (sub_nonneg.2 hab)]
    have h := hlaw (wnExistR s t a b)
    rw [hv] at h
    exact h.congr (wnExist_rectMass_ae hlin s t a b)
  indep s t hst k a ha := by
    let X : (i : Fin k) → Unit → Ω → ℝ := fun i _ =>
      rectMass (wnExistS W) s t (a i.castSucc) (a i.succ)
    have hX : IsGaussianProcess (fun p : (i : Fin k) × Unit => X p.1 p.2) P :=
      (hGP.comp_right (fun p : (i : Fin k) × Unit =>
        wnExistR s t (a p.1.castSucc) (a p.1.succ))).congr
        fun p => (wnExist_rectMass_ae hlin _ _ _ _).symm
    have h := IsGaussianProcess.iIndepFun_of_covariance_eq_zero (S := fun _ : Fin k => Unit)
      (X := X) hX
      (fun _ _ => (wnExist_measurable_rectMass hW _ _ _ _).aemeasurable) (by
        intro i j hij _ _
        rw [wnExist_cov_congr (wnExist_rectMass_ae hlin _ _ _ _)
          (wnExist_rectMass_ae hlin _ _ _ _), hcov]
        rcases lt_or_gt_of_ne hij with h | h
        · exact wnExist_inner_R_R (ha (Fin.castSucc_le_succ i))
            (ha (Fin.succ_le_castSucc_iff.2 h)) (ha (Fin.castSucc_le_succ j))
        · rw [real_inner_comm]
          exact wnExist_inner_R_R (ha (Fin.castSucc_le_succ j))
            (ha (Fin.succ_le_castSucc_iff.2 h)) (ha (Fin.castSucc_le_succ i)))
    exact h.comp (fun _ f => f ()) (fun _ => measurable_pi_apply ())
  indep_past s t hst := by
    let X : ℝ × ℝ → Ω → ℝ := fun q => rectMass (wnExistS W) s t q.1 q.2
    let Y : {p : ℝ≥0 × ℝ // p.1 ≤ s} → Ω → ℝ := fun p => wnExistS W p.1.1 p.1.2
    have hXY : IsGaussianProcess (Sum.elim X Y) P :=
      (hGP.comp_right (Sum.elim (fun q : ℝ × ℝ => wnExistR s t q.1 q.2)
        (fun p : {p : ℝ≥0 × ℝ // p.1 ≤ s} => wnExistG p.1.1 p.1.2))).congr (by
          rintro (q | p)
          · exact (wnExist_rectMass_ae hlin _ _ _ _).symm
          · exact EventuallyEq.rfl)
    have h := IsGaussianProcess.indepFun_of_covariance_eq_zero (X := X) (Y := Y) hXY
      (fun _ => (wnExist_measurable_rectMass hW _ _ _ _).aemeasurable)
      (fun _ => (hW _).aemeasurable) (by
        intro q p
        rw [wnExist_cov_congr (wnExist_rectMass_ae hlin _ _ _ _) EventuallyEq.rfl]
        change cov[W _, W (wnExistG (p.1.1 : ℝ) p.1.2); P] = 0
        rw [hcov]
        exact wnExist_inner_R_G (by exact_mod_cast hst) (by exact_mod_cast p.2) _ _ _)
    rw [IndepFun_iff_Indep] at h
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
    · exact iSup₂_le fun a b => MeasurableSpace.comap_le_comap_pi (g := X) (a, b)
    · exact iSup₂_le fun p hp => MeasurableSpace.comap_le_comap_pi (g := Y) ⟨p, hp⟩

end Noise

end QSSEPtoKPZ
