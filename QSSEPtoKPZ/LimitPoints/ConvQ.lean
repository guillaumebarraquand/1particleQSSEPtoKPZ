/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Prop71Mart
public import QSSEPtoKPZ.LimitPoints.Mollify
public import QSSEPtoKPZ.LimitPoints.ConvQTerm4

/-!
# Convergence of the brackets, (7.6) (task Q3)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task Q3.
See `docs/stage4-design.md`, Section 4 (note on Q3), and `docs/stage4-interfaces.md`.

`sup_{t ≤ T} |⟨M_n^φ⟩_t - Q(t)| → 0` in probability along the coupling, with
`Q(t) = ∫_0^t ∫ Z(s,x)² φ_s(x)² dx ds` and `Z = limField ρ Xl`. The four terms of the article
are separate lemmas of the task: (1) Proposition 3.1 (3) and (4.8) (`IsPathPrelimLaw.prop_3_1_path`,
`IsPathPrelimLaw.prop_4_3_path`); (2) Proposition 6.2 (`pathPrelim_replacement`,
`measurableSet_pathReplEvent`); (3) continuity of `‖(φμ) ⋆ ρ_ε‖₂²` in `μ`
(`continuousOn_smoothedNormSq`) and dominated convergence; (4) `smoothedNormSq_withDensity_le`,
`tendsto_smoothedNormSq_withDensity` and (7.1). The density of the limit (Proposition 7.1 (2),
from task Q2) is a hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp Interval

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- **The decomposition of `Q_n - Q` into four terms** (Section 7.1), for one path `γ = 𝖹_n` with
the conclusions of Proposition 3.1 (3), one path `γl = 𝒵`, and an integrable `q`: for
`t ∈ [0,T]`, `|Q_n(t) - ∫_0^t q| ≤ 5 n^{-1/4} C² ∫_0^T ℰ_n(s;1) ds + 2 |∫_0^t (ℰ_n(s;φ_s) -
H_ε(𝖹_n, s)) ds| + ∫_0^T |a_n H_ε(𝖹_n, s) - H_ε(𝒵, s)| ds + ∫_0^T |H_ε(𝒵, s) - q(s)| ds`. -/
private lemma convQ_decomp {T C : ℝ} (hT : 0 ≤ T) {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {n ε : ℝ} (hn : 1 ≤ n) (hε : 0 < ε)
    {γ γl : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume 0 T)
    (hE : IntervalIntegrable (fun s => ENpath n γ s (φ s)) volume 0 T)
    (hE1 : IntervalIntegrable (fun s => ENpath n γ s fun _ => 1) volume 0 T)
    (h31 : ∀ t ∈ Icc 0 T, |QNpath n φ t γ - aN n * ∫ s in (0 : ℝ)..t, ENpath n γ s (φ s)| ≤
      5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..t, ENpath n γ s fun _ => 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    |QNpath n φ t γ - ∫ s in (0 : ℝ)..t, q s| ≤
      5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) +
      2 * |∫ s in (0 : ℝ)..t,
        (ENpath n γ s (φ s) - smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε)| +
      (∫ s in (0 : ℝ)..T, |aN n * convQSmooth hT φ ρ ε γ s - convQSmooth hT φ ρ ε γl s|) +
      ∫ s in (0 : ℝ)..T, |convQSmooth hT φ ρ ε γl s - q s| := by
  have hH := continuous_convQSmooth hT hφ hρ hε
  set Hj : ℝ → ℝ := fun s => convQSmooth hT φ ρ ε γ s with hHj
  set Hl : ℝ → ℝ := fun s => convQSmooth hT φ ρ ε γl s with hHl
  have hHjc : Continuous Hj := hH.comp (continuous_const.prodMk continuous_id)
  have hHlc : Continuous Hl := hH.comp (continuous_const.prodMk continuous_id)
  have hsub : [[(0 : ℝ), t]] ⊆ [[(0 : ℝ), T]] := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2
  have hEt := hE.mono_set hsub
  have hqt := hq.mono_set hsub
  have hSt : IntervalIntegrable (fun s => smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε)
      volume 0 t :=
    prelimAux_intervalIntegrable_congr (hHjc.intervalIntegrable 0 t) fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact convQSmooth_of_mem hT φ ρ ε γ ⟨hs.1, hs.2.trans ht.2⟩
  have hSH : ∫ s in (0 : ℝ)..t, smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε =
      ∫ s in (0 : ℝ)..t, Hj s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    exact (convQSmooth_of_mem hT φ ρ ε γ ⟨hs.1, hs.2.trans ht.2⟩).symm
  set IE := ∫ s in (0 : ℝ)..t, ENpath n γ s (φ s)
  set R := ∫ s in (0 : ℝ)..t,
    (ENpath n γ s (φ s) - smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε)
  have hR : R = IE - ∫ s in (0 : ℝ)..t, Hj s := by
    rw [← hSH]
    exact intervalIntegral.integral_sub hEt hSt
  have haN := constants_bounds hn
  have hn0 : 0 ≤ n := by linarith
  -- term 1
  have h1 : |QNpath n φ t γ - aN n * IE| ≤
      5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * (∫ s in (0 : ℝ)..T, ENpath n γ s fun _ => 1) := by
    refine (h31 t ht).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ fun s => limMart_ENpath_one_nonneg n γ s hn0) hE1
  -- term 3
  have h3 : |aN n * (∫ s in (0 : ℝ)..t, Hj s) - ∫ s in (0 : ℝ)..t, Hl s| ≤
      ∫ s in (0 : ℝ)..T, |aN n * Hj s - Hl s| := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hHjc.intervalIntegrable 0 t).const_mul _) (hHlc.intervalIntegrable 0 t)]
    refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ fun s => abs_nonneg _)
      (((continuous_const.mul hHjc).sub hHlc).abs.intervalIntegrable 0 T)
  -- term 4
  have h4 : |(∫ s in (0 : ℝ)..t, Hl s) - ∫ s in (0 : ℝ)..t, q s| ≤
      ∫ s in (0 : ℝ)..T, |Hl s - q s| := by
    rw [← intervalIntegral.integral_sub (hHlc.intervalIntegrable 0 t) hqt]
    refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ fun s => abs_nonneg _) (((hHlc.intervalIntegrable 0 T).sub hq).abs)
  have e : QNpath n φ t γ - ∫ s in (0 : ℝ)..t, q s =
      (QNpath n φ t γ - aN n * IE) + aN n * R +
        (aN n * (∫ s in (0 : ℝ)..t, Hj s) - ∫ s in (0 : ℝ)..t, Hl s) +
        ((∫ s in (0 : ℝ)..t, Hl s) - ∫ s in (0 : ℝ)..t, q s) := by
    rw [hR]
    ring
  have h2 : |aN n * R| ≤ 2 * |R| := by
    rw [abs_mul, abs_of_pos (by linarith [haN.2.2.1])]
    exact mul_le_mul_of_nonneg_right (by linarith [haN.2.2.2.1, haN.2.2.2.2.1, haN.2.2.2.2.2])
      (abs_nonneg _)
  rw [e]
  calc _ ≤ |QNpath n φ t γ - aN n * IE| + |aN n * R| +
        |aN n * (∫ s in (0 : ℝ)..t, Hj s) - ∫ s in (0 : ℝ)..t, Hl s| +
        |(∫ s in (0 : ℝ)..t, Hl s) - ∫ s in (0 : ℝ)..t, q s| :=
        (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
          (add_le_add_left (abs_add_le _ _) _)) _)
    _ ≤ _ := by linarith

/-- **(7.6)**, in probability (outer probability of the events). -/
theorem IsLimCoupling.tendsto_QN {Ωs : Type*} [MeasurableSpace Ωs] {Pr : Measure Ωs} {T : ℝ}
    {n : ℕ → ℝ} {X : ℕ → Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Xl : Ωs → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hc : IsLimCoupling.{u} Pr T n X Xl)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x,
      ENNReal.ofReal (limField ρ Xl t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Xl ω) t : Measure ℝ) =
        volume.withDensity fun x => ENNReal.ofReal (limField ρ Xl t x ω))
    {C : ℝ} {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun j => Pr {ω | ∃ t ∈ Set.Icc 0 T,
      η < |QNpath (n j) φ t (X j ω) - limBracket (limField ρ Xl) φ t ω|}) atTop (𝓝 0) := by
  have hPr := hc.isProbabilityMeasure
  have hT := hc.pos
  have hT0 := hT.le
  -- almost every limit path has a density with (7.1)
  have hgood : ∀ᵐ ω ∂Pr,
      ∫⁻ t in Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt (Xl ω) t) x ^ 2) < ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), (pathAt (Xl ω) t : Measure ℝ) =
        volume.withDensity fun x => ENNReal.ofReal (limDensity ρ (pathAt (Xl ω) t) x) := by
    have hm : AEMeasurable (fun ω => ∫⁻ t in Icc (0 : ℝ) T,
        ∫⁻ x, ENNReal.ofReal (limDensity ρ (pathAt (Xl ω) t) x ^ 2)) Pr :=
      ((measurable_convQ_lintegral_sq hρ).comp hc.measurable_lim :).aemeasurable
    filter_upwards [ae_lt_top' hm hZ2.ne, hdens] with ω h1 h2
    exact ⟨h1, h2⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ 4 * ENNReal.ofReal δ ≤ e := by
    by_cases het : e = ⊤
    · exact ⟨1, one_pos, by simp [het]⟩
    · refine ⟨e.toReal / 4, by have := ENNReal.toReal_pos he.ne' het; positivity, le_of_eq ?_⟩
      calc 4 * ENNReal.ofReal (e.toReal / 4) = ENNReal.ofReal (4 * (e.toReal / 4)) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
        _ = e := by rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0), ENNReal.ofReal_toReal het]
  obtain ⟨ε₀, hε₀, hrepl⟩ := pathPrelim_replacement.{u} hρ hT hφ (η / 8) δ (by positivity) hδ
  obtain ⟨ε, hεI, h4⟩ := convQ_term4 hc.measurable_lim hT0 hφ hρ hgood (η := η / 4)
    (by positivity) hδ hε₀
  have hε : 0 < ε := hεI.1
  obtain ⟨N, hN⟩ := hrepl ε hεI
  have e1 := (convQ_term1 hc C (η := η / 4) (by positivity)).eventually
    (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ))
  have e3 := (convQ_term3 hc hT0 hφ hρ hε (η := η / 4) (by positivity)).eventually
    (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ))
  have eN := hc.tendsto_atTop.eventually_ge_atTop N
  filter_upwards [e1, e3, eN] with j h1 h3 hNj
  have hnj := hc.one_le j
  set A1 := {ω | η / 4 < 5 * n j ^ (-1 / 4 : ℝ) * C ^ 2 *
    ∫ s in (0 : ℝ)..T, ENpath (n j) (X j ω) s fun _ => 1} with hA1
  set R := {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) | ∃ t ∈ Set.Icc 0 T, η / 8 <
    |∫ s in (0 : ℝ)..t, (ENpath (n j) γ s (φ s) -
      smoothedNormSq (pathAt γ s : Measure ℝ) (φ s) ρ ε)|} with hR
  set A3 := {ω | η / 4 ≤ ∫ s in (0 : ℝ)..T,
    |aN (n j) * convQSmooth hT0 φ ρ ε (X j ω) s - convQSmooth hT0 φ ρ ε (Xl ω) s|} with hA3
  set A4 := {ω | η / 4 ≤ ∫ s in (0 : ℝ)..T,
    |convQSmooth hT0 φ ρ ε (Xl ω) s - convQDens hT0 ρ φ (Xl ω) s|} with hA4
  have h2 : Pr (X j ⁻¹' R) ≤ ENNReal.ofReal δ := by
    rw [← Measure.map_apply (hc.measurable j)
      (measurableSet_pathReplEvent hρ hφ (n j) ε (η / 8) hnj hε)]
    exact hN (n j) hNj hnj _ (hc.law j)
  have h31 := ae_of_ae_map (hc.measurable j).aemeasurable
    ((hc.law j).prop_3_1_path hnj hT hφ)
  have hsub : {ω | ∃ t ∈ Set.Icc 0 T,
      η < |QNpath (n j) φ t (X j ω) - limBracket (limField ρ Xl) φ t ω|} ≤ᵐ[Pr]
      (A1 ∪ X j ⁻¹' R ∪ A3 ∪ A4 : Set Ωs) := by
    filter_upwards [h31, hgood] with ω hω1 hω2
    intro hEv
    obtain ⟨t, ht, hlt⟩ := hEv
    obtain ⟨hE, hE1, -, h31'⟩ := hω1
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hnot
    simp only [hA1, hA3, hA4, mem_ofPred_eq, not_lt, not_le] at n1 n3 n4
    simp only [hR, mem_preimage, mem_ofPred_eq, not_exists, not_and, not_lt] at n2
    have hq := (convQDens_good hT0 hφ hρ hω2.1 hω2.2).1
    have hdec := convQ_decomp hT0 hφ hρ hnj hε (γl := Xl ω) hq hE hE1 h31' ht
    have hLB : limBracket (limField ρ Xl) φ t ω =
        ∫ s in (0 : ℝ)..t, convQDens hT0 ρ φ (Xl ω) s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      exact (convQDens_of_mem hT0 ρ φ (Xl ω) ⟨hs.1, hs.2.trans ht.2⟩).symm
    rw [hLB] at hlt
    have := n2 t ht
    linarith
  calc Pr {ω | ∃ t ∈ Set.Icc 0 T,
        η < |QNpath (n j) φ t (X j ω) - limBracket (limField ρ Xl) φ t ω|}
      ≤ Pr (A1 ∪ X j ⁻¹' R ∪ A3 ∪ A4) := measure_mono_ae hsub
    _ ≤ Pr A1 + Pr (X j ⁻¹' R) + Pr A3 + Pr A4 :=
        (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
          (add_le_add_left (measure_union_le _ _) _)) _)
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ := by
        gcongr
    _ = 4 * ENNReal.ofReal δ := by ring
    _ ≤ e := hδe

end QSSEPtoKPZ
