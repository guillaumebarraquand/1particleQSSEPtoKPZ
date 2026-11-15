/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.SecondMoment
public import QSSEPtoKPZ.Uniqueness.StochFubiniKernel

/-!
# Mild solutions solve the weak mild equation: stochastic Fubini (task K3)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task K3
(13 November 2026). See `docs/stage4-design.md`, Sections 1.2 (h) and 4 (note on K3), and
`docs/stage4-interfaces.md`.

`heatMild_isWeakMild` is the statement `IsMildSolution.isWeakMild` of
`Uniqueness/MildSolution.lean` (same statement). Proof: the jointly measurable version of
`heatMild_exists_version`; `ℋ_T` from `heatMild_integral_sq_le` and `∫ g_t² = (4πt)^{-1/2}`;
(7.13) for every `t ∈ (0,T]` by Riemann sums in `x` and the `L²` closure rule
(`IsWalshIntegral.exists_limit`), with the bound
`∫ (∑ᵢ cᵢ g_{t-s}(xᵢ - y))² dy ≲ Δx ‖f‖₂² (t-s)^{-1/2}` near `s = t`.

Proof as written (task K3). Fix `t ∈ (0,T]` and `f` continuous with support in `(-R, R)`,
`|f| ≤ M`. With `a_k = -R + kΔ`, `Δ = 2R/(n+1)`, `c_k = Δ f(a_k)`:
* `X_n = ∑_k c_k (Z(t,a_k) - g_t(a_k))` is the Walsh integral of
  `h_n(s,y) = 𝟙_{0<s<t} (∑_k c_k g_{t-s}(a_k - y)) Z(s,y)` (the mild equation at the points
  `a_k`, `IsWalshIntegral.finset_sum`, `const_mul`);
* `‖h_n - h‖²_{L²(ν ⊗ ds ⊗ dy)} ≤ ∫_0^t ∫ D_n(s,y)² C g_s(y)² dy ds → 0`
  (`𝔼 Z(s,y)² ≤ C g_s(y)²`, `stochFub_lintegral_field_le`, `stochFub_err_tendsto`), where
  `h(s,y) = 𝟙_{0<s<t} (g_{t-s} ⋆ f)(y) Z(s,y)`; the bound of the note on K3 is replaced by
  `∫ (∑_k c_k g_r(a_k - y))² dy ≤ (∑_k |c_k|)² (4πr)^{-1/2} ≤ (2RM)² (4πr)^{-1/2}`
  (Cauchy–Schwarz), also integrable near `r = 0`;
* `IsWalshIntegral.exists_limit` gives `X = ∫ h dξ` with `X_n → X` in `L²(ν)`, and `X_n → `
  `∫ Z(t,x) f(x) dx - ∫ g_t(x) f(x) dx` for every `ω` (Riemann sums of continuous functions);
  an almost surely convergent subsequence identifies the two limits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- `‖F‖₂² = ∫ F²`, as `eLpNorm F 2 μ = (∫⁻ ofReal (F²))^{1/2}` (`F` a.e. strongly measurable). -/
private lemma stochFub_eLpNorm_two {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {F : α → ℝ} (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ = (∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hF,
    ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    Real.rpow_two, sq_abs]

/-- The field `𝟙_{0<s<t} D(s,y) Z(s,y)` is measurable on `Ω × ℝ × ℝ`. -/
private lemma stochFub_measurable_field {Z : ℝ → ℝ → Ω → ℝ} (hZm : Measurable (uncurryField Z))
    {D : ℝ → ℝ → ℝ} (hD : Measurable (fun q : ℝ × ℝ => D q.1 q.2)) (t : ℝ) :
    Measurable (uncurryField (fun s y ω => if 0 < s ∧ s < t then D s y * Z s y ω else 0)) := by
  change Measurable (fun p : Ω × ℝ × ℝ =>
    if 0 < p.2.1 ∧ p.2.1 < t then D p.2.1 p.2.2 * uncurryField Z p else 0)
  refine Measurable.ite ?_ ((hD.comp measurable_snd).mul hZm) measurable_const
  exact (measurableSet_lt measurable_const measurable_snd.fst).inter
    (measurableSet_lt measurable_snd.fst measurable_const)

/-- **Tonelli and the moment bound**: if `𝔼 Z(s,y)² ≤ C g_s(y)²` on `(0,t) × ℝ`, then
`𝔼 ∫∫ (𝟙_{0<s<t} D(s,y) Z(s,y))² ds dy ≤ ∫_0^t ∫ D(s,y)² C g_s(y)² dy ds`. -/
private lemma stochFub_lintegral_field_le [SFinite ν] {Z : ℝ → ℝ → Ω → ℝ}
    (hZm : Measurable (uncurryField Z)) {D : ℝ → ℝ → ℝ}
    (hD : Measurable (fun q : ℝ × ℝ => D q.1 q.2)) {t C : ℝ}
    (hmom : ∀ s ∈ Set.Ioo 0 t, ∀ y, ∫⁻ ω, ENNReal.ofReal (Z s y ω ^ 2) ∂ν ≤
      ENNReal.ofReal (C * heatKernel s y ^ 2)) :
    ∫⁻ p, ENNReal.ofReal (uncurryField
        (fun s y ω => if 0 < s ∧ s < t then D s y * Z s y ω else 0) p ^ 2) ∂(ν.prod volume) ≤
      ∫⁻ s in Set.Ioo 0 t, ∫⁻ y,
        ENNReal.ofReal (D s y ^ 2) * ENNReal.ofReal (C * heatKernel s y ^ 2) := by
  have hFm := stochFub_measurable_field hZm hD t
  set K : ℝ × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (D q.1 q.2 ^ 2) * ENNReal.ofReal (C * heatKernel q.1 q.2 ^ 2) with hK
  have hKm : Measurable K := ((hD.pow_const 2).ennreal_ofReal).mul
    ((measurable_const.mul (stochFub_measurable_heatKernel.pow_const 2)).ennreal_ofReal)
  rw [lintegral_prod_symm _ (hFm.pow_const 2).ennreal_ofReal.aemeasurable]
  calc _ ≤ ∫⁻ q, (Set.Ioo 0 t ×ˢ Set.univ).indicator K q := lintegral_mono fun q => ?_
    _ = ∫⁻ q in Set.Ioo 0 t ×ˢ Set.univ, K q := lintegral_indicator
        (measurableSet_Ioo.prod MeasurableSet.univ) _
    _ = _ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
          lintegral_prod _ hKm.aemeasurable]
  by_cases hq : 0 < q.1 ∧ q.1 < t
  · rw [Set.indicator_of_mem (show q ∈ Set.Ioo 0 t ×ˢ Set.univ from ⟨hq, trivial⟩)]
    simp only [uncurryField, hq, and_self, ↓reduceIte, hK]
    simp_rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    exact hmom q.1 hq q.2
  · simp [uncurryField, hq]

variable [SFinite ν] in
/-- **(7.13) at a fixed time** (stochastic Fubini by Riemann sums): for a jointly measurable mild
solution `Z`, continuous on `(0,∞) × ℝ` for every `ω`, with `𝔼 Z(s,y)² ≤ C g_s(y)²` on
`(0,t) × ℝ`, and `f` continuous with compact support,
`∫ Z(t,x) f(x) dx - ∫ g_t(x) f(x) dx = ∫∫ 𝟙_{0<s<t} (g_{t-s} ⋆ f)(y) Z(s,y) ξ(ds dy)`. -/
theorem stochFub_isWalshIntegral (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) (hZm : Measurable (uncurryField Z))
    (hZc : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Z p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ))
    {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hmom : ∀ s ∈ Set.Ioo 0 t, ∀ y, ∫⁻ ω, ENNReal.ofReal (Z s y ω ^ 2) ∂ν ≤
      ENNReal.ofReal (C * heatKernel s y ^ 2))
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω else 0)
      (fun ω => (∫ x, Z t x ω * f x) - ∫ x, heatKernel t x * f x) := by
  -- the support and the bound of `f`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R := max R₀ 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hsupp : ∀ x, R ≤ |x| → f x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR₀ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    have : R₀ ≤ max R₀ 0 := le_max_left _ _
    linarith
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ x, |f x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using hM x
  -- the Riemann sums
  set hs : ℕ → ℝ → ℝ → Ω → ℝ := fun n s y ω => ∑ k ∈ Finset.range (n + 1),
    2 * R / (n + 1) * f (stochFubPt R n k) *
      (if 0 < s ∧ s < t then heatKernel (t - s) (stochFubPt R n k - y) * Z s y ω else 0)
    with hhs
  set Xs : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range (n + 1),
    2 * R / (n + 1) * f (stochFubPt R n k) *
      (Z t (stochFubPt R n k) ω - heatKernel t (stochFubPt R n k)) with hXsdef
  have hXs : ∀ n, IsWalshIntegral 𝓖 S ν (hs n) (Xs n) := fun n =>
    IsWalshIntegral.finset_sum _ fun k _ =>
      (hZ.mild t (stochFubPt R n k) ht).const_mul (2 * R / (n + 1) * f (stochFubPt R n k))
  set h : ℝ → ℝ → Ω → ℝ :=
    fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω else 0 with hhdef
  have hdiff : ∀ n, uncurryField (hs n) - uncurryField h = uncurryField
      (fun s y ω => if 0 < s ∧ s < t then stochFubErr f R t n s y * Z s y ω else 0) := by
    intro n
    funext p
    simp only [Pi.sub_apply, uncurryField, hhs, hhdef, stochFubErr, stochFubSum]
    split_ifs with hp
    · rw [sub_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp
  -- `L²` convergence of the integrands
  have hconv : Tendsto (fun n => eLpNorm (uncurryField (hs n) - uncurryField h) 2
      (ν.prod volume)) atTop (𝓝 0) := by
    have h0 := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (stochFub_err_tendsto hf hR hsupp hM' ht hC) (fun n => zero_le)
      (fun n => stochFub_lintegral_field_le hZm (stochFub_measurable_err hf.measurable R t n) hmom)
    have h1 := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp h0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
    refine h1.congr fun n => ?_
    rw [hdiff, stochFub_eLpNorm_two (stochFub_measurable_field hZm
      (stochFub_measurable_err hf.measurable R t n) t).aestronglyMeasurable]
    rfl
  -- `h ∈ L²`
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  have hmem : MemLp (uncurryField (hs n)) 2 (ν.prod volume) :=
    (IsWalshIntegral.isometry_lib hS (hXs n)).1
  have hd : MemLp (uncurryField (hs n) - uncurryField h) 2 (ν.prod volume) := hn
  have hh2 : MemLp (uncurryField h) 2 (ν.prod volume) := by
    simpa using hmem.sub hd
  -- the limit of the values
  obtain ⟨X', hX', hlimX⟩ := IsWalshIntegral.exists_limit hS hXs hh2 hconv
  have hpw : ∀ ω, Tendsto (fun n => Xs n ω) atTop
      (𝓝 ((∫ x, Z t x ω * f x) - ∫ x, heatKernel t x * f x)) := by
    intro ω
    have hz : Continuous (fun x => Z t x ω) :=
      (hZc ω).comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨ht, trivial⟩)
    have h1 := stochFub_riemann (hz.mul hf) hR (fun x hx => by simp [hsupp x hx])
    have h2 := stochFub_riemann ((stochFub_continuous_heatKernel t).mul hf) hR
      (fun x hx => by simp [hsupp x hx])
    simp only [Pi.mul_apply] at h1 h2
    refine (h1.sub h2).congr fun n => ?_
    simp only [hXsdef]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hae : X' =ᵐ[ν] fun ω => (∫ x, Z t x ω * f x) - ∫ x, heatKernel t x * f x := by
    obtain ⟨ns, hns, hns_ae⟩ :=
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hlimX).exists_seq_tendsto_ae
    filter_upwards [hns_ae] with ω hω
    exact tendsto_nhds_unique hω ((hpw ω).comp hns.tendsto_atTop)
  exact IsWalshIntegral.congr_ae hS hX' EventuallyEq.rfl hae

/-- After (7.15) (same statement as `IsMildSolution.isWeakMild`): a solution of (1.13) has a
jointly measurable version which belongs to `ℋ_T` and satisfies (7.13) for every `t ∈ (0,T]`. -/
theorem heatMild_isWeakMild (hS : IsWhiteNoise 𝓖 S ν) {Z : ℝ → ℝ → Ω → ℝ}
    (hZ : IsMildSolution 𝓖 S Z ν) {T : ℝ} (hT : 0 < T) :
    ∃ Z' : ℝ → ℝ → Ω → ℝ, (∀ᵐ ω ∂ν, ∀ t x, 0 < t → Z' t x ω = Z t x ω) ∧
      IsWeakMild T 𝓖 S Z' ν ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        IsWalshIntegral 𝓖 S ν
          (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z' s y ω else 0)
          (fun ω => (∫ x, Z' t x ω * f x) - ∫ x, heatKernel t x * f x) := by
  have := hS.isProbabilityMeasure
  obtain ⟨Z', hae, hZm, hZc, hZ'⟩ := heatMild_exists_version hS hZ
  obtain ⟨C₀, hC₀⟩ := heatMild_integral_sq_le hS hZ' T
  set C := max C₀ 0 with hCdef
  have hmomT : ∀ s ∈ Set.Ioc 0 T, ∀ y, ∫⁻ ω, ENNReal.ofReal (Z' s y ω ^ 2) ∂ν ≤
      ENNReal.ofReal (C * heatKernel s y ^ 2) := by
    intro s hs y
    rw [← ofReal_integral_eq_lintegral_ofReal (secondMom_memLp hS hZ' hs.1 y).integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((hC₀ s hs y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  have hweak : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      HasCompactSupport f → IsWalshIntegral 𝓖 S ν
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z' s y ω else 0)
        (fun ω => (∫ x, Z' t x ω * f x) - ∫ x, heatKernel t x * f x) :=
    fun t ht f hf hfc => stochFub_isWalshIntegral hS hZ' hZm hZc ht.1 (le_max_right _ _)
      (fun s hs y => hmomT s ⟨hs.1, hs.2.le.trans ht.2⟩ y) hf.continuous hfc
  refine ⟨Z', hae, ⟨hZm, ?_, (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hweak)⟩, hweak⟩
  -- `𝔼 ∫_0^T ∫ Z² ≤ ∫_0^T C (4πt)^{-1/2} dt < ∞`
  set F : Ω × ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (uncurryField Z' p ^ 2) with hF
  have hFm : Measurable F := (hZm.pow_const 2).ennreal_ofReal
  have hswap : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z' t x ω ^ 2)) ∂ν =
      ∫⁻ t in Set.Ioc (0 : ℝ) T, ∫⁻ x, ∫⁻ ω, F (ω, t, x) ∂ν := by
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := T)).symm]
    have hm1 : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) => ∫⁻ x, F (ω, t, x)) :=
      Measurable.lintegral_prod_right' (f := fun q : (Ω × ℝ) × ℝ => F (q.1.1, q.1.2, q.2))
        (hFm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
    change ∫⁻ ω, (∫⁻ t in Set.Ioc (0 : ℝ) T, ∫⁻ x, F (ω, t, x)) ∂ν = _
    rw [lintegral_lintegral_swap (μ := ν) (ν := volume.restrict (Set.Ioc (0 : ℝ) T))
      hm1.aemeasurable]
    refine lintegral_congr fun t => ?_
    exact lintegral_lintegral_swap
      (hFm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).aemeasurable
  rw [hswap]
  have hbd : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∫⁻ x, ∫⁻ ω, F (ω, t, x) ∂ν ≤
      ENNReal.ofReal (C / Real.sqrt (4 * Real.pi) * (1 / Real.sqrt t)) := by
    intro t ht
    calc ∫⁻ x, ∫⁻ ω, F (ω, t, x) ∂ν ≤ ∫⁻ x, ENNReal.ofReal (C * heatKernel t x ^ 2) :=
          lintegral_mono fun x => hmomT t ht x
      _ = _ := by
          rw [stochFub_lintegral_heatKernel_sq ht.1 (le_max_right _ _),
            Real.sqrt_mul (by positivity) t]
          congr 1; ring
  have hint : IntegrableOn (fun t => C / Real.sqrt (4 * Real.pi) * (1 / Real.sqrt t))
      (Set.Ioc 0 T) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (stochFub_integrableOn_inv_sqrt hT).const_mul _
  exact (setLIntegral_mono' measurableSet_Ioc hbd).trans_lt hint.lintegral_lt_top

end QSSEPtoKPZ
