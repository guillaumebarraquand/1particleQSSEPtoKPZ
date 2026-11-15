/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71Mart
public import QSSEPtoKPZ.LimitPoints.Mollify

/-!
# The four terms of (7.6) (task Q3)

Section 7.1 of the article writes `Q_n - Q` as the sum of four terms. With
`H_ε(γ, s) = ‖(φ_s γ(s)) ⋆ ρ_ε‖₂²` (`convQSmooth`, with `φ_s` extended continuously outside
`[0,T]`) and `q(γ, s) = ∫ Z(s,x)² φ_s(x)² dx` (`convQDens`, `Z = limDensity` of `γ(s)`):
* term 1, `Q_n(t) - a_n ∫_0^t ℰ_n(s;φ_s) ds`, is at most `5 n^{-1/4} C² ∫_0^T ℰ_n(s;1) ds`, which
  tends to `0` in probability by (4.8) and Markov's inequality (`convQ_term1`);
* term 2 is Proposition 6.2 (`pathPrelim_replacement`, used in `ConvQ.lean`);
* term 3 is at most `∫_0^T |a_n H_ε(𝖹_n, s) - H_ε(𝒵, s)| ds`, which tends to `0` almost surely,
  hence in probability (`convQ_term3`): `H_ε` is jointly continuous;
* term 4 is at most `∫_0^T |H_ε(𝒵, s) - q(𝒵, s)| ds`, which tends to `0` almost surely as `ε → 0`
  (dominated convergence, `smoothedNormSq_withDensity_le`, `tendsto_smoothedNormSq_withDensity`
  and (7.1)), hence in probability (`convQ_term4`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Interval

noncomputable section

namespace QSSEPtoKPZ

universe u

variable {T : ℝ}

/-- `H_ε(γ, s) = ‖(φ̃_s γ(s)) ⋆ ρ_ε‖₂²`, with `φ̃_s = φ_{proj_{[0,T]} s}`. -/
def convQSmooth (hT : 0 ≤ T) (φ : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ) (ε : ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (s : ℝ) : ℝ :=
  smoothedNormSq (pathAt γ s : Measure ℝ) (prelimExt hT φ s) ρ ε

/-- `q(γ, s) = ∫ Z(s,x)² φ̃_s(x)² dx` with `Z(s,·) = limDensity ρ (γ(s))`. -/
def convQDens (hT : 0 ≤ T) (ρ : ℝ → ℝ) (φ : ℝ → ℝ → ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (s : ℝ) : ℝ :=
  ∫ x, limDensity ρ (pathAt γ s) x ^ 2 * prelimExt hT φ s x ^ 2

variable {C : ℝ} {φ φt : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ}

theorem convQSmooth_of_mem (hT : 0 ≤ T) (φ : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ) (ε : ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    convQSmooth hT φ ρ ε γ s = smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε := by
  rw [convQSmooth, prelimExt_of_mem hT φ hs]

theorem convQDens_of_mem (hT : 0 ≤ T) (ρ : ℝ → ℝ) (φ : ℝ → ℝ → ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    convQDens hT ρ φ γ s = ∫ x, limDensity ρ (pathAt γ s) x ^ 2 * φ s x ^ 2 := by
  rw [convQDens, prelimExt_of_mem hT φ hs]

theorem convQSmooth_nonneg (hT : 0 ≤ T) (φ : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ) (ε : ℝ)
    (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (s : ℝ) : 0 ≤ convQSmooth hT φ ρ ε γ s :=
  integral_nonneg fun _ => sq_nonneg _

/-- `(γ, s) ↦ H_ε(γ, s)` is continuous for `ε > 0`. -/
theorem continuous_convQSmooth (hT : 0 ≤ T) (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => convQSmooth hT φ ρ ε p.1 p.2 := by
  have h := prelimMeas_continuous_smoothedNormSq (T := T) hρ (G := prelimExt hT φ)
    (prelimExt_continuous hT hφ) (prelimExt_abs_le hT hφ) hε
  exact h

/-- `(γ, s) ↦ q(γ, s)` is measurable. -/
theorem measurable_convQDens (hT : 0 ≤ T) (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ) :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => convQDens hT ρ φ p.1 p.2 := by
  have m1 : Measurable fun q : (C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ) × ℝ =>
      limDensity ρ (pathAt q.1.1 q.1.2) q.2 :=
    ((measurable_limDensity_pathAt hρ (T := T)).comp
      (f := fun q : (C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
      (by fun_prop) :)
  have m2 : Measurable fun q : (C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ) × ℝ =>
      prelimExt hT φ q.1.2 q.2 :=
    (prelimExt_continuous hT hφ).measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact (((m1.pow_const 2).mul (m2.pow_const 2)).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable

/-- `γ ↦ ∫_0^T ∫ Z(t,x)² dx dt` (lower integrals) is measurable. -/
theorem measurable_convQ_lintegral_sq (hρ : IsMollifier ρ) :
    Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) =>
      ∫⁻ t in Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt γ t) x ^ 2) := by
  have m1 : Measurable fun q : (C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ) × ℝ =>
      ENNReal.ofReal (limDensity ρ (pathAt q.1.1 q.1.2) q.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp ((((measurable_limDensity_pathAt hρ (T := T)).comp
      (f := fun q : (C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ) × ℝ => (q.1.1, q.1.2, q.2))
      (by fun_prop) :)).pow_const 2)
  exact m1.lintegral_prod_right'.lintegral_prod_right'

/-- A sequence of nonnegative measurable functions tending to `0` almost surely tends to `0` in
probability. -/
theorem convQ_tendsto_measure_of_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {G : ℕ → Ω → ℝ} (hG : ∀ j, Measurable (G j))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun j => G j ω) atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun j => μ {ω | η ≤ G j ω}) atTop (𝓝 0) := by
  have h := tendstoInMeasure_iff_dist.1
    (tendstoInMeasure_of_tendsto_ae (fun j => (hG j).aestronglyMeasurable) hlim) η hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun j => measure_mono fun ω (hω : η ≤ G j ω) => ?_
  show η ≤ dist (G j ω) 0
  rw [Real.dist_eq, sub_zero]
  exact hω.trans (le_abs_self _)

/-! ### Term 1 -/

/-- **Term 1 of (7.6)**: `5 n^{-1/4} C² ∫_0^T ℰ_n(s;1) ds → 0` in probability along the coupling
((4.8) and Markov's inequality). -/
theorem convQ_term1 {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} {n : ℕ → ℝ}
    {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    (C : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun j => Pr {ω | η < 5 * n j ^ (-1 / 4 : ℝ) * C ^ 2 *
      ∫ s in (0 : ℝ)..T, ENpath (n j) (X j ω) s fun _ => 1}) atTop (𝓝 0) := by
  have hT0 := hc.pos.le
  set K : ℝ := 2 ^ (1 + 16 * T)
  have hbound : ∀ j, Pr {ω | η < 5 * n j ^ (-1 / 4 : ℝ) * C ^ 2 *
      ∫ s in (0 : ℝ)..T, ENpath (n j) (X j ω) s fun _ => 1} ≤
      ENNReal.ofReal (5 * n j ^ (-1 / 4 : ℝ) * C ^ 2 * K / η) := by
    intro j
    have hnj : 0 < n j := zero_lt_one.trans_le (hc.one_le j)
    set a := 5 * n j ^ (-1 / 4 : ℝ) * C ^ 2
    have ha : 0 ≤ a := by positivity
    obtain ⟨-, -, hm, hint⟩ := (hc.law j).prop_4_3_path (hc.one_le j) hT0
    set f : Ωs → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (∫ s in (0 : ℝ)..T, ENpath (n j) (X j ω) s fun _ => 1)
    have hfm : Measurable f := hm.comp (hc.measurable j)
    have hfi : ∫⁻ ω, f ω ∂Pr ≤ ENNReal.ofReal K := by
      refine le_of_eq_of_le (lintegral_map (f := fun γ => ENNReal.ofReal
        (∫ s in (0 : ℝ)..T, ENpath (n j) γ s fun _ => 1)) hm (hc.measurable j)).symm hint
    calc Pr {ω | η < a * ∫ s in (0 : ℝ)..T, ENpath (n j) (X j ω) s fun _ => 1}
        ≤ Pr {ω | ENNReal.ofReal η ≤ ENNReal.ofReal a * f ω} := by
          refine measure_mono fun ω (hω : η < _) => ?_
          show ENNReal.ofReal η ≤ ENNReal.ofReal a * f ω
          rw [← ENNReal.ofReal_mul ha]
          exact ENNReal.ofReal_le_ofReal hω.le
      _ ≤ (∫⁻ ω, ENNReal.ofReal a * f ω ∂Pr) / ENNReal.ofReal η :=
          meas_ge_le_lintegral_div (measurable_const.mul hfm).aemeasurable
            (by simpa using hη) ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal a * (∫⁻ ω, f ω ∂Pr) / ENNReal.ofReal η := by
          rw [lintegral_const_mul _ hfm]
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal K / ENNReal.ofReal η := by gcongr
      _ = ENNReal.ofReal (a * K / η) := by
          rw [← ENNReal.ofReal_mul ha, ENNReal.ofReal_div_of_pos hη]
  have hlim : Tendsto (fun j => ENNReal.ofReal (5 * n j ^ (-1 / 4 : ℝ) * C ^ 2 * K / η)) atTop
      (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)).comp hc.tendsto_atTop)
    have h2 : Tendsto (fun j => 5 * n j ^ (-1 / 4 : ℝ) * C ^ 2 * K / η) atTop (𝓝 0) := by
      have := ((h.const_mul 5).mul_const (C ^ 2 * K)).div_const η
      simp only [mul_zero, zero_mul, zero_div] at this
      refine this.congr fun j => ?_
      simp only [Function.comp_apply]
      norm_num
      ring
    simpa using ENNReal.tendsto_ofReal h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound

/-! ### Term 3 -/

/-- **Term 3 of (7.6)**: for fixed `ε > 0`, `∫_0^T |a_n H_ε(𝖹_n, s) - H_ε(𝒵, s)| ds → 0` in
probability along the coupling (almost surely, by joint continuity of `H_ε` and `a_n → 1`). -/
theorem convQ_term3 {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} {n : ℕ → ℝ}
    {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    (hT : 0 ≤ T) (hφ : IsC13 T φ φt C) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {η : ℝ}
    (hη : 0 < η) :
    Tendsto (fun j => Pr {ω | η ≤ ∫ s in (0 : ℝ)..T,
      |aN (n j) * convQSmooth hT φ ρ ε (X j ω) s - convQSmooth hT φ ρ ε (Xl ω) s|}) atTop
      (𝓝 0) := by
  have hPr := hc.isProbabilityMeasure
  have hH := continuous_convQSmooth hT hφ hρ hε
  set H := convQSmooth hT φ ρ ε with hHdef
  refine convQ_tendsto_measure_of_ae (fun j => ?_) ?_ hη
  · have hf : Measurable fun p : Ωs × ℝ => |aN (n j) * H (X j p.1) p.2 - H (Xl p.1) p.2| :=
      continuous_abs.measurable.comp ((measurable_const.mul (hH.measurable.comp
        (((hc.measurable j).comp measurable_fst).prodMk measurable_snd))).sub
        (hH.measurable.comp ((hc.measurable_lim.comp measurable_fst).prodMk measurable_snd)))
    exact prelimAux_measurable_intervalIntegral hf hT fun _ _ _ => rfl
  filter_upwards [hc.tendsto] with ω hω
  obtain ⟨Hm, hHm⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hH.comp (continuous_const.prodMk continuous_id)).continuousOn (s := Icc 0 T))
  have hHm' : ∀ s ∈ Icc 0 T, |H (Xl ω) s| ≤ Hm := fun s hs => by
    simpa [Real.norm_eq_abs] using hHm s hs
  rw [Metric.tendsto_nhds]
  intro e he
  have e1 := limMart_unif_of_continuousOn (F := fun γ s => H γ s) (a := 0) (b := T) hH.continuousOn hω
    (by positivity : 0 < e / (4 * (T + 1)))
  have ha : Tendsto (fun j => |aN (n j) - 1| * Hm) atTop (𝓝 0) := by
    have := ((limMart_tendsto_aN hc.tendsto_atTop).sub_const 1).abs.mul_const Hm
    simpa using this
  have e2 := ha.eventually (gt_mem_nhds (by positivity : 0 < e / (4 * (T + 1))))
  filter_upwards [e1, e2] with j h1 h2
  have haN := constants_bounds (hc.one_le j)
  have hpt : ∀ s ∈ Ι (0 : ℝ) T, ‖|aN (n j) * H (X j ω) s - H (Xl ω) s|‖ ≤ 3 * (e / (4 * (T + 1))) := by
    intro s hs
    rw [uIoc_of_le hT] at hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_abs]
    have hd := h1 s hsT
    have hb := hHm' s hsT
    calc |aN (n j) * H (X j ω) s - H (Xl ω) s|
        = |aN (n j) * (H (X j ω) s - H (Xl ω) s) + (aN (n j) - 1) * H (Xl ω) s| := by ring_nf
      _ ≤ |aN (n j) * (H (X j ω) s - H (Xl ω) s)| + |(aN (n j) - 1) * H (Xl ω) s| :=
          abs_add_le _ _
      _ = aN (n j) * |H (X j ω) s - H (Xl ω) s| + |aN (n j) - 1| * |H (Xl ω) s| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith [haN.2.2.1])]
      _ ≤ 2 * (e / (4 * (T + 1))) + |aN (n j) - 1| * Hm := by
          gcongr
          · linarith [haN.2.2.2.1, haN.2.2.2.2.1, haN.2.2.2.2.2]
      _ ≤ 3 * (e / (4 * (T + 1))) := by linarith
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [sub_zero, abs_of_nonneg hT] at hint
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  calc _ ≤ 3 * (e / (4 * (T + 1))) * T := hint
    _ = 3 * e * T / (4 * (T + 1)) := by ring
    _ < e := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

end QSSEPtoKPZ
