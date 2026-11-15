/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.NoiseFunctionalAux
public import QSSEPtoKPZ.WhiteNoise.Transfer

/-!
# Uniqueness in law for (7.13): new solutions from old (task K4)

Let `Z ∈ ℋ_T` solve the weak mild equation (7.13) (`IsWeakMild`).

* `IsWeakMild.noiseFun_congr`: a measurable `Y` equal to `Z` a.e. on `Ω × [0,T] × ℝ` solves
  (7.13).
* `IsWeakMild.noiseFun_mono`: (7.13) for a filtration gives (7.13) for any larger filtration.
* `IsWeakMild.noiseFun_proj`: the projection `Ẑ = noiseProj S ν (Z 𝟙_{[0,T]}(t))` onto the
  noise solves (7.13), for the filtration `𝓖` augmented by the null sets (which contains the
  noise filtration `𝒩`): `𝔼[· | 𝒩_∞]` maps the Walsh integral of (7.13) to the Walsh integral of
  the projected integrand (`IsWalshIntegral.condExp_noise`), the deterministic bounded factor
  `𝟙_{0<s<t} (g_{t-s} ⋆ f)(y)` comes out of the projection (`noiseProj_mul_left`), and
  `𝔼[∫ Z(t,x) f(x) dx | 𝒩_∞] = ∫ Ẑ(t,x) f(x) dx` (`noiseFun_condExp_integral`).
* `IsWeakMild.noiseFun_transfer`: if `G(N, t, x)` solves (7.13) on one space carrying a white
  noise (`N` the noise coordinates), then `G(N₂, t, x)` solves (7.13) on any other
  (`IsWalshIntegral.transfer`, and `noiseFun_lintegral_transfer` for `ℋ_T`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `Z 𝟙_{[0,T]}(s)`: the field `Z` cut off outside the times `[0,T]`. -/
def noiseFunCut (T : ℝ) (Z : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ :=
  fun s y ω => if s ∈ Set.Icc (0 : ℝ) T then Z s y ω else 0

/-- **(7.13) for a larger filtration.** -/
theorem IsWeakMild.noiseFun_mono {T : ℝ} {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsWeakMild T 𝓖 S Z ν) (h : 𝓖 ≤ 𝓖') :
    IsWeakMild T 𝓖' S Z ν :=
  ⟨hZ.measurable, hZ.sq_integrable,
    hZ.weak.mono fun _ ht f hf hfc => (ht f hf hfc).mono_filtration h⟩

/-- `∫ (Z 𝟙_{[0,T]})² d(ν ⊗ Leb²) = 𝔼 ∫_0^T ∫ Z²` for a measurable field. -/
private lemma noiseFun_lintegral_cut {T : ℝ} {ν : Measure Ω} [SFinite ν] {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : Measurable (uncurryField Z)) :
    ∫⁻ p, ENNReal.ofReal (uncurryField (noiseFunCut T Z) p ^ 2) ∂(ν.prod volume) =
      ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂ν := by
  have hs : MeasurableSet (Set.univ ×ˢ (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)) :
      Set (Ω × ℝ × ℝ)) := MeasurableSet.univ.prod (measurableSet_Icc.prod MeasurableSet.univ)
  have e : (fun p => ENNReal.ofReal (uncurryField (noiseFunCut T Z) p ^ 2)) =
      (Set.univ ×ˢ (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ))).indicator
        fun p : Ω × ℝ × ℝ => ENNReal.ofReal (Z p.2.1 p.2.2 p.1 ^ 2) := by
    funext p
    by_cases h : p.2.1 ∈ Set.Icc (0 : ℝ) T
    · have h' : p ∈ Set.univ ×ˢ (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)) :=
        ⟨Set.mem_univ _, h, Set.mem_univ _⟩
      simp only [uncurryField, noiseFunCut, h, ite_true, Set.indicator_of_mem h']
    · have h' : p ∉ Set.univ ×ˢ (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)) :=
        fun hp => h hp.2.1
      simp only [uncurryField, noiseFunCut, h, ite_false, Set.indicator_of_notMem h']
      simp
  rw [e, lintegral_indicator hs, ← noiseFun_prod_restrict_eq]
  exact noiseFun_lintegral_eq ν _ (F := fun p : Ω × ℝ × ℝ => ENNReal.ofReal (Z p.2.1 p.2.2 p.1 ^ 2))
    (hZ.pow_const 2).ennreal_ofReal

/-- `Z 𝟙_{[0,T]}(t) ∈ L²(ν ⊗ Leb²)` for `Z ∈ ℋ_T`. -/
theorem IsWeakMild.noiseFun_memLp {T : ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} [SFinite ν] {Z : ℝ → ℝ → Ω → ℝ} (hZ : IsWeakMild T 𝓖 S Z ν) :
    MemLp (uncurryField (noiseFunCut T Z)) 2 (ν.prod volume) := by
  have hm : Measurable (uncurryField (noiseFunCut T Z)) := by
    change Measurable fun p : Ω × ℝ × ℝ =>
      if p.2.1 ∈ Set.Icc (0 : ℝ) T then Z p.2.1 p.2.2 p.1 else 0
    exact Measurable.ite (measurableSet_Icc.preimage (by fun_prop)) hZ.measurable
      measurable_const
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _), noiseFun_lintegral_cut
    hZ.measurable]
  exact hZ.sq_integrable

/-- `𝔼 ∫_0^T ∫ Y² < ∞` for `Y ∈ L²(ν ⊗ Leb²)`. -/
private lemma noiseFun_sq_integrable_of_memLp {T : ℝ} {ν : Measure Ω} [SFinite ν]
    {Y : ℝ → ℝ → Ω → ℝ} (hYm : Measurable (uncurryField Y))
    (hY : MemLp (uncurryField Y) 2 (ν.prod volume)) :
    ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Y t x ω ^ 2)) ∂ν < ⊤ := by
  rw [← noiseFun_lintegral_eq ν _ (F := fun p : Ω × ℝ × ℝ => ENNReal.ofReal (Y p.2.1 p.2.2 p.1 ^ 2))
    (hYm.pow_const 2).ennreal_ofReal, noiseFun_prod_restrict_eq]
  exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hY.integrable_sq.lintegral_lt_top

/-- **(7.13) is stable under modification on a null set** of `Ω × [0,T] × ℝ`. -/
theorem IsWeakMild.noiseFun_congr {T : ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) {Z Y : ℝ → ℝ → Ω → ℝ}
    (hZ : IsWeakMild T 𝓖 S Z ν) (hY : Measurable (uncurryField Y))
    (hZY : ∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
      Z p.2.1 p.2.2 p.1 = Y p.2.1 p.2.2 p.1) :
    IsWeakMild T 𝓖 S Y ν := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  refine ⟨hY, ?_, ?_⟩
  · calc ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Y t x ω ^ 2)) ∂ν
        = ∫⁻ p, ENNReal.ofReal (Y p.2.1 p.2.2 p.1 ^ 2)
            ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)) :=
          (noiseFun_lintegral_eq ν _ (F := fun p : Ω × ℝ × ℝ =>
            ENNReal.ofReal (Y p.2.1 p.2.2 p.1 ^ 2)) (hY.pow_const 2).ennreal_ofReal).symm
      _ = ∫⁻ p, ENNReal.ofReal (Z p.2.1 p.2.2 p.1 ^ 2)
            ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)) :=
          lintegral_congr_ae (hZY.mono fun p hp => by simp only [hp])
      _ = ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂ν :=
          noiseFun_lintegral_eq ν _ (F := fun p : Ω × ℝ × ℝ =>
            ENNReal.ofReal (Z p.2.1 p.2.2 p.1 ^ 2)) (hZ.measurable.pow_const 2).ennreal_ofReal
      _ < ⊤ := hZ.sq_integrable
  · have hre := noiseFun_rearrange (volume.restrict (Set.Icc (0 : ℝ) T)) ν (volume : Measure ℝ)
    have h1 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ q ∂(ν.prod volume),
        Z t q.2 q.1 = Y t q.2 q.1 :=
      Measure.ae_ae_of_ae_prod (p := fun r : ℝ × Ω × ℝ => Z r.1 r.2.2 r.2.1 = Y r.1 r.2.2 r.2.1)
        (hre.quasiMeasurePreserving.ae hZY)
    have h2 : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ᵐ ω ∂ν, ∀ᵐ x,
        Z t x ω = Y t x ω :=
      ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
        (h1.mono fun t ht => Measure.ae_ae_of_ae_prod
          (p := fun q : Ω × ℝ => Z t q.2 q.1 = Y t q.2 q.1) ht)
    have hint := noiseFun_ae_of_ae_restrict measurableSet_Icc hZY
    filter_upwards [hZ.weak, h2, ae_restrict_mem measurableSet_Ioc] with t hw ht htI f hf hfc
    refine (hw f hf hfc).congr_ae hS ?_ ?_
    · filter_upwards [hint] with p hp
      simp only [uncurryField]
      by_cases hs : 0 < p.2.1 ∧ p.2.1 < t
      · simp only [hs, and_self, ite_true]
        rw [hp ⟨hs.1.le, hs.2.le.trans htI.2⟩]
      · simp only [hs, ite_false]
    · filter_upwards [ht] with ω hω
      rw [integral_congr_ae (g := fun x => Y t x ω * f x) (hω.mono fun x hx => by simp only [hx])]

/-- **The projection onto the noise solves (7.13)**: for `Z ∈ ℋ_T` solving (7.13),
`Ẑ = noiseProj S ν (Z 𝟙_{[0,T]})` solves (7.13), for the augmented filtration. -/
theorem IsWeakMild.noiseFun_proj {T : ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
    {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsWeakMild T 𝓖 S Z ν) :
    IsWeakMild T (nullAug ν 𝓖) S (noiseProj S ν (noiseFunCut T Z)) ν := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hL2 := hZ.noiseFun_memLp
  obtain ⟨hhat, -⟩ := noiseProj_memLp S hL2
  have hm : Measurable (uncurryField (noiseProj S ν (noiseFunCut T Z))) :=
    ((stronglyMeasurable_noiseProj S ν _).mono (noiseProdSigma_le S ν)).measurable
  refine ⟨hm, noiseFun_sq_integrable_of_memLp hm hhat, ?_⟩
  have hce := noiseFun_condExp_integral S hL2
  filter_upwards [hZ.weak, ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hce]
    with t hw ht hct f hf hfc
  have hfm : Measurable f := hf.continuous.measurable
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hf2 : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hfc
  set g : ℝ → ℝ → ℝ := fun s y => if 0 < s ∧ s < t then heatConv (t - s) f y else 0 with hg
  have hgm : Measurable (Function.uncurry g) :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)) (noiseFun_measurable_heatConv hfm t)
      measurable_const
  have hgb : ∃ C, ∀ s y, |g s y| ≤ C := ⟨C, fun s y => by
    simp only [g]
    split_ifs with hs
    · exact abs_heatConv_le (sub_pos.2 hs.2) hfm (fun x => by rw [← Real.norm_eq_abs]; exact hC x) y
    · rw [abs_zero]; exact (norm_nonneg _).trans (hC 0)⟩
  have e1 : (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω else 0) =
      fun s y ω => g s y * noiseFunCut T Z s y ω := by
    funext s y ω
    simp only [g, noiseFunCut]
    by_cases h1 : 0 < s ∧ s < t
    · have h2 : s ∈ Set.Icc (0 : ℝ) T := ⟨h1.1.le, h1.2.le.trans ht.2⟩
      simp only [h1, h2, and_self, ite_true]
    · simp only [h1, ite_false, zero_mul]
  have W := hw f hf hfc
  rw [e1] at W
  have W1 := (IsWalshIntegral.condExp_noise hS W).mono_filtration
    (fun u => hS.noiseFiltration_le u)
  refine W1.congr_ae hS.nullAug ?_ ?_
  · refine (noiseProj_mul_left S hgm hgb hL2).trans (Eventually.of_forall fun p => ?_)
    simp only [uncurryField, g]
    split_ifs <;> simp
  · set c := ∫ x, heatKernel t x * f x with hc
    have hXi : Integrable (fun ω => (∫ x, Z t x ω * f x) - c) ν :=
      ((IsWalshIntegral.isometry_lib hS (hw f hf hfc)).2.1).integrable one_le_two
    have hAi : Integrable (fun ω => ∫ x, Z t x ω * f x) ν := by
      refine (hXi.add (integrable_const c)).congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.add_apply, sub_add_cancel]
    have hcut : (fun ω => ∫ x, noiseFunCut T Z t x ω * f x) = fun ω => ∫ x, Z t x ω * f x := by
      funext ω
      simp only [noiseFunCut, Set.Ioc_subset_Icc_self ht, ite_true]
    have hA := hct f hf2
    rw [hcut] at hA
    have h𝒢 := noiseProj_iSup_le (mΩ := mΩ) S ν
    filter_upwards [condExp_sub (m := ⨆ t, noiseFiltration S ν t) hAi (integrable_const c), hA]
      with ω h1 h2
    rw [show (fun ω => (∫ x, Z t x ω * f x) - c) = (fun ω => ∫ x, Z t x ω * f x) - fun _ => c
      from rfl, h1, Pi.sub_apply, h2, condExp_const h𝒢 c]

/-- **Transfer of (7.13) between white noises**: if `G(N₁, t, x)` solves (7.13) on a space
carrying a white noise with coordinates `N₁`, then `G(N₂, t, x)` solves (7.13) on any other
space carrying a white noise with coordinates `N₂`. -/
theorem IsWeakMild.noiseFun_transfer {T : ℝ} {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂}
    {S₁ : ℝ → ℝ → Ω₁ → ℝ} {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₁ : Measure Ω₁} {ν₂ : Measure Ω₂}
    (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂)
    {G : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ} (hG : Measurable G)
    (hY : IsWeakMild T 𝓖₁ S₁ (fun s y ω => G (noiseMap S₁ ω, s, y)) ν₁) :
    IsWeakMild T 𝓖₂ S₂ (fun s y ω => G (noiseMap S₂ ω, s, y)) ν₂ := by
  have : IsProbabilityMeasure ν₁ := h₁.isProbabilityMeasure
  have : IsProbabilityMeasure ν₂ := h₂.isProbabilityMeasure
  have hF : Measurable (fun q : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => ENNReal.ofReal (G q ^ 2)) :=
    (hG.pow_const 2).ennreal_ofReal
  have hN₁ := h₁.measurable_noiseMap.prodMap (measurable_id (α := ℝ × ℝ))
  have hN₂ := h₂.measurable_noiseMap.prodMap (measurable_id (α := ℝ × ℝ))
  refine ⟨hG.comp hN₂, ?_, ?_⟩
  · calc ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
          ENNReal.ofReal (G (noiseMap S₂ ω, t, x) ^ 2)) ∂ν₂
        = ∫⁻ p, ENNReal.ofReal (G (noiseMap S₂ p.1, p.2) ^ 2)
            ∂(ν₂.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)) :=
          (noiseFun_lintegral_eq ν₂ _ (hF.comp hN₂)).symm
      _ = ∫⁻ p, ENNReal.ofReal (G (noiseMap S₁ p.1, p.2) ^ 2)
            ∂(ν₁.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)) :=
          noiseFun_lintegral_transfer h₁ h₂ _ hF
      _ = ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
          ENNReal.ofReal (G (noiseMap S₁ ω, t, x) ^ 2)) ∂ν₁ :=
          noiseFun_lintegral_eq ν₁ _ (hF.comp hN₁)
      _ < ⊤ := hY.sq_integrable
  · filter_upwards [hY.weak] with t ht f hf hfc
    have hfm : Measurable f := hf.continuous.measurable
    refine IsWalshIntegral.transfer h₁ h₂
      (H := fun w s y => if 0 < s ∧ s < t then heatConv (t - s) f y * G (w, s, y) else 0)
      (Ξ := fun w => (∫ x, G (w, t, x) * f x) - ∫ x, heatKernel t x * f x) ?_ ?_ (ht f hf hfc)
    · refine Measurable.ite ?_ (((noiseFun_measurable_heatConv hfm t).comp measurable_snd).mul
        hG) measurable_const
      exact (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
        (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
    · have hm : Measurable fun q : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ => G (q.1, t, q.2) * f q.2 :=
        (hG.comp (by fun_prop)).mul (hfm.comp measurable_snd)
      exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.sub_const _

end QSSEPtoKPZ
