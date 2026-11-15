/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.ConvQAux

/-!
# The fourth term of (7.6) (task Q3)

For a path `γ` with `∫_0^T ∫ Z(t,x)² dx dt < ∞` (`Z = limDensity` of `γ(t)`) and
`γ(t) = Z(t,x) dx` for almost every `t ∈ [0,T]`:
* `q(γ, ·) = ∫ Z(·,x)² φ_·(x)² dx` is integrable on `[0,T]`, and for almost every `s`,
  `0 ≤ H_ε(γ, s) ≤ q(γ, s)` and `H_ε(γ, s) → q(γ, s)` as `ε → 0⁺` (`convQDens_good`, from Young's
  inequality and the approximation of the identity in `L²`, task G3);
* hence `∫_0^T |H_ε(𝒵, s) - q(𝒵, s)| ds → 0` almost surely along `ε_k → 0` (dominated
  convergence), so in probability (`convQ_term4`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Interval

noncomputable section

namespace QSSEPtoKPZ

variable {T C : ℝ} {φ φt : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ}

/-- **The density of a good path** (Proposition 7.1 (2) and (7.1) for one path): `q(γ, ·)` is
integrable on `[0,T]`, and for almost every `s ∈ [0,T]`, `H_ε(γ, s) ≤ q(γ, s)` for every `ε > 0`
and `H_ε(γ, s) → q(γ, s)` as `ε → 0⁺`. -/
theorem convQDens_good (hT : 0 ≤ T) (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ)
    {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hfin : ∫⁻ t in Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ t) x ^ 2) < ⊤)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), (pathAt γ t : Measure ℝ) =
      volume.withDensity fun x => ENNReal.ofReal (limDensity ρ (pathAt γ t) x)) :
    IntervalIntegrable (convQDens hT ρ φ γ) volume 0 T ∧
      ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
        (∀ ε, 0 < ε → convQSmooth hT φ ρ ε γ s ≤ convQDens hT ρ φ γ s) ∧
        Tendsto (fun ε => convQSmooth hT φ ρ ε γ s) (𝓝[>] 0) (𝓝 (convQDens hT ρ φ γ s)) := by
  obtain ⟨c, hc0, hc⟩ := hφ.pathFun_bound
  have hZ2m : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (limDensity ρ (pathAt γ p.1) p.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp ((((measurable_limDensity_pathAt hρ (T := T)).comp
      (f := fun p : ℝ × ℝ => (γ, p.1, p.2)) (by fun_prop) :)).pow_const 2)
  have hZm : ∀ s, Measurable fun x => limDensity ρ (pathAt γ s) x := fun s =>
    ((measurable_limDensity_pathAt hρ (T := T)).comp
      (f := fun x : ℝ => (γ, s, x)) (by fun_prop) :)
  have hLm : Measurable fun s => ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) :=
    hZ2m.lintegral_prod_right'
  have hfin_s : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) < ⊤ := ae_lt_top hLm hfin.ne
  have hmem : ∀ s, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) < ⊤ →
      MemLp (fun x => limDensity ρ (pathAt γ s) x) 2 volume := fun s h =>
    (memLp_two_iff_integrable_sq (hZm s).aestronglyMeasurable).2
      ⟨((hZm s).pow_const 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2 h⟩
  -- the bound `0 ≤ q ≤ c² ‖Z(s)‖₂²`
  have hqb : ∀ s ∈ Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2) < ⊤ →
      0 ≤ convQDens hT ρ φ γ s ∧ convQDens hT ρ φ γ s ≤
        c ^ 2 * (∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2)).toReal := by
    intro s hs h
    rw [convQDens_of_mem hT ρ φ γ hs]
    have hi := (hmem s h).integrable_sq
    refine ⟨integral_nonneg fun x => by positivity, ?_⟩
    rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      ((hZm s).pow_const 2).aestronglyMeasurable, ← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (hi.const_mul _)
      (ae_of_all _ fun x => ?_)
    have : φ s x ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc s hs x) 2
    simp only
    nlinarith [sq_nonneg (limDensity ρ (pathAt γ s) x)]
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    have hg : Integrable (fun s => c ^ 2 *
        (∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ s) x ^ 2)).toReal)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      (integrable_toReal_of_lintegral_ne_top hLm.aemeasurable hfin.ne).const_mul _
    refine hg.mono' (((measurable_convQDens hT hφ hρ).comp
      (f := fun s : ℝ => (γ, s)) (by fun_prop) :)).aestronglyMeasurable ?_
    filter_upwards [hfin_s, ae_restrict_mem measurableSet_Icc] with s h1 h2
    obtain ⟨b0, b1⟩ := hqb s h2 h1
    rw [Real.norm_eq_abs, abs_of_nonneg b0]
    exact b1
  · filter_upwards [hfin_s, hd, ae_restrict_mem measurableSet_Icc] with s h1 h2 h3
    have hφm : Measurable (φ s) := (hφ.contDiff s h3).continuous.measurable
    have hq : convQDens hT ρ φ γ s =
        ∫ x, φ s x ^ 2 * limDensity ρ (pathAt γ s) x ^ 2 := by
      rw [convQDens_of_mem hT ρ φ γ h3]
      exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    refine ⟨fun ε hε => ?_, ?_⟩
    · rw [convQSmooth_of_mem hT φ ρ ε γ h3, h2, hq]
      exact smoothedNormSq_withDensity_le hρ (fun x => limDensity_nonneg ρ _ x) (hmem s h1) hφm
        ⟨c, hc s h3⟩ hε
    · rw [hq]
      refine (tendsto_smoothedNormSq_withDensity hρ (fun x => limDensity_nonneg ρ _ x)
        (hmem s h1) hφm ⟨c, hc s h3⟩).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [convQSmooth_of_mem hT φ ρ ε γ h3, h2]

/-- **Term 4 of (7.6)**: `∫_0^T |H_ε(𝒵, s) - q(𝒵, s)| ds → 0` in probability as `ε → 0`; in
the form used: for `δ > 0` and `ε₀ > 0`, some `ε ∈ (0, ε₀)` makes the probability that it
exceeds `η` at most `δ`. -/
theorem convQ_term4 {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} [IsProbabilityMeasure Pr]
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hXl : Measurable Xl) (hT : 0 ≤ T)
    (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ)
    (hgood : ∀ᵐ ω ∂Pr,
      ∫⁻ t in Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt (Xl ω) t) x ^ 2) < ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), (pathAt (Xl ω) t : Measure ℝ) =
        volume.withDensity fun x => ENNReal.ofReal (limDensity ρ (pathAt (Xl ω) t) x))
    {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε ∈ Ioo 0 ε₀, Pr {ω | η ≤ ∫ s in (0 : ℝ)..T,
      |convQSmooth hT φ ρ ε (Xl ω) s - convQDens hT ρ φ (Xl ω) s|} ≤ ENNReal.ofReal δ := by
  set εk : ℕ → ℝ := fun k => ε₀ / ((k : ℝ) + 2) with hεk
  have hεk0 : ∀ k, 0 < εk k := fun k => by positivity
  have hεk1 : ∀ k, εk k < ε₀ := fun k => by
    rw [hεk, div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hεlim : Tendsto εk atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hεk0⟩
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hqm := measurable_convQDens hT hφ hρ
  set D : ℕ → Ωs → ℝ := fun k ω => ∫ s in (0 : ℝ)..T,
    |convQSmooth hT φ ρ (εk k) (Xl ω) s - convQDens hT ρ φ (Xl ω) s| with hD
  have hDm : ∀ k, Measurable (D k) := by
    intro k
    have hH := continuous_convQSmooth hT hφ hρ (hεk0 k)
    have hf : Measurable fun p : Ωs × ℝ =>
        |convQSmooth hT φ ρ (εk k) (Xl p.1) p.2 - convQDens hT ρ φ (Xl p.1) p.2| :=
      continuous_abs.measurable.comp
        (((hH.measurable.comp (f := fun p : Ωs × ℝ => (Xl p.1, p.2))
          ((hXl.comp measurable_fst).prodMk measurable_snd) :)).sub
        ((hqm.comp (f := fun p : Ωs × ℝ => (Xl p.1, p.2))
          ((hXl.comp measurable_fst).prodMk measurable_snd) :)))
    exact prelimAux_measurable_intervalIntegral hf hT fun _ _ _ => rfl
  have hlim : ∀ᵐ ω ∂Pr, Tendsto (fun k => D k ω) atTop (𝓝 0) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hqi, hae⟩ := convQDens_good hT hφ hρ hω.1 hω.2
    have hae' := (ae_restrict_iff' measurableSet_Icc).1 hae
    have hqmeas : Measurable fun s => convQDens hT ρ φ (Xl ω) s :=
      (hqm.comp (f := fun s : ℝ => (Xl ω, s)) (by fun_prop) :)
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := T) (l := atTop) (f := fun _ => (0 : ℝ))
      (F := fun k s => |convQSmooth hT φ ρ (εk k) (Xl ω) s - convQDens hT ρ φ (Xl ω) s|)
      (fun s => 2 * |convQDens hT ρ φ (Xl ω) s|)
      (Eventually.of_forall fun k => (continuous_abs.measurable.comp
        ((((continuous_convQSmooth hT hφ hρ (hεk0 k)).comp
          (continuous_const.prodMk continuous_id :
            Continuous fun s : ℝ => (Xl ω, s))).measurable).sub hqmeas)).aestronglyMeasurable)
      (Eventually.of_forall fun k => by
        filter_upwards [hae'] with s hs hsI
        rw [uIoc_of_le hT] at hsI
        obtain ⟨h1, -⟩ := hs (Ioc_subset_Icc_self hsI)
        have a := h1 (εk k) (hεk0 k)
        have b := convQSmooth_nonneg hT φ ρ (εk k) (Xl ω) s
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        have : 0 ≤ convQDens hT ρ φ (Xl ω) s := b.trans a
        rw [abs_of_nonneg this]
        constructor <;> linarith)
      ((hqi.abs).const_mul 2)
      (by
        filter_upwards [hae'] with s hs hsI
        rw [uIoc_of_le hT] at hsI
        obtain ⟨-, h2⟩ := hs (Ioc_subset_Icc_self hsI)
        have := ((h2.comp hεlim).sub_const (convQDens hT ρ φ (Xl ω) s)).abs
        simpa using this)
    simpa using h
  have hm := convQ_tendsto_measure_of_ae hDm hlim hη
  obtain ⟨k, hk⟩ := (hm.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ))).exists
  exact ⟨εk k, ⟨hεk0 k, hεk1 k⟩, hk⟩

end QSSEPtoKPZ
