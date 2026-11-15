/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Mollify
public import QSSEPtoKPZ.LimitPoints.Skorokhod

/-!
# Fatou's lemma under convergence in law (task Q2)

Auxiliary results for Proposition 7.1 (1)–(2) and (7.4) (`LimitPoints/Prop71Density.lean`).

* `limPt_lintegral_le_of_tendsto`: if `P_k → P` weakly on a separable metrizable space, and
  nonnegative functionals satisfy `G₀(γ) ≤ liminf_k G_{φ(k)}(γ_k)` whenever `γ_k → γ` and
  `φ(k) → ∞`, then `∫ G₀ dP ≤ c` as soon as `∫ G_k dP_k ≤ c` for all large `k`. Proof: Skorokhod's
  representation along a subsequence (`skorokhod_subseq`) and Fatou's lemma, as in the proof of
  Proposition 7.1 (2) in the article.
* `limPt_continuousOn_smoothedNormSq`, `limPt_measurable_smoothedNormSq`: the map
  `(γ, t, ε) ↦ ‖γ(t) ⋆ ρ_ε‖₂²` is continuous on `C([0,T], ℳ₊) × ℝ × (0, ∞)`.
* `limPt_tendsto_epsN`: `ε_n = ⌊ε n^{1/2}⌋ n^{-1/2} → ε` as `n → ∞`, with `⌊ε n^{1/2}⌋ ≥ 1`
  eventually.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- **Fatou's lemma under convergence in law** (proof of Proposition 7.1 (2)). Let `P_k → P`
weakly on a separable metrizable space `S`, and `G_k, G₀ : S → [0, ∞]` measurable with
`G₀(γ) ≤ liminf_k G_{φ(k)}(γ_k)` whenever `γ_k → γ` and `φ(k) → ∞`. If `∫ G_k dP_k ≤ c` for all
large `k`, then `∫ G₀ dP ≤ c`. -/
theorem limPt_lintegral_le_of_tendsto {S : Type*} [TopologicalSpace S]
    [TopologicalSpace.MetrizableSpace S] [TopologicalSpace.SeparableSpace S] [MeasurableSpace S]
    [BorelSpace S] {P : ℕ → ProbabilityMeasure S} {Plim : ProbabilityMeasure S}
    (h : Tendsto P atTop (𝓝 Plim)) {G : ℕ → S → ℝ≥0∞} {G₀ : S → ℝ≥0∞}
    (hG : ∀ k, Measurable (G k)) (hG₀ : Measurable G₀)
    (hlsc : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ (γs : ℕ → S) (γ : S),
      Tendsto γs atTop (𝓝 γ) → G₀ γ ≤ liminf (fun k => G (φ k) (γs k)) atTop)
    {c : ℝ≥0∞} (hc : ∀ᶠ k in atTop, ∫⁻ γ, G k γ ∂(P k : Measure S) ≤ c) :
    ∫⁻ γ, G₀ γ ∂(Plim : Measure S) ≤ c := by
  obtain ⟨φ, hφ, Ω, _, Pr, _, X, Y, hX, hY, hXmap, hYmap, hconv⟩ := skorokhod_subseq h
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  calc ∫⁻ γ, G₀ γ ∂(Plim : Measure S) = ∫⁻ ω, G₀ (Y ω) ∂Pr := by
        rw [← hYmap, lintegral_map hG₀ hY]
    _ ≤ ∫⁻ ω, liminf (fun k => G (φ k) (X k ω)) atTop ∂Pr := by
        refine lintegral_mono_ae ?_
        filter_upwards [hconv] with ω hω using hlsc φ hφt _ _ hω
    _ ≤ liminf (fun k => ∫⁻ ω, G (φ k) (X k ω) ∂Pr) atTop :=
        lintegral_liminf_le fun k => (hG (φ k)).comp (hX k)
    _ = liminf (fun k => ∫⁻ γ, G (φ k) γ ∂(P (φ k) : Measure S)) atTop := by
        congr 1
        funext k
        rw [← hXmap k, lintegral_map (hG (φ k)) (hX k)]
    _ ≤ c := liminf_le_of_frequently_le' (hφt.eventually hc).frequently

/-- `(γ, t, ε) ↦ ‖γ(t) ⋆ ρ_ε‖₂²` is continuous on `C([0,T], ℳ₊) × ℝ × (0, ∞)`. -/
theorem limPt_continuousOn_smoothedNormSq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T : ℝ} :
    ContinuousOn (fun q : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ × ℝ =>
        smoothedNormSq (pathAt q.1 q.2.1 : Measure ℝ) (fun _ => 1) ρ q.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Ioi 0) := by
  have hc := continuousOn_smoothedNormSq hρ (φ := fun _ => 1) continuous_const
    ⟨1, fun _ => by simp⟩
  have hm : Continuous fun q : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ × ℝ =>
      (pathAt q.1 q.2.1, q.2.2) :=
    (continuous_pathAt_prod.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)
  refine hc.comp hm.continuousOn ?_
  rintro ⟨γ, t, ε⟩ ⟨-, -, hε⟩
  exact ⟨Set.mem_univ _, hε⟩

/-- For `ε > 0`, `(γ, t) ↦ ‖γ(t) ⋆ ρ_ε‖₂²` is continuous on `C([0,T], ℳ₊) × ℝ`. -/
theorem limPt_continuous_smoothedNormSq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T ε : ℝ}
    (hε : 0 < ε) :
    Continuous fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      smoothedNormSq (pathAt p.1 p.2 : Measure ℝ) (fun _ => 1) ρ ε := by
  have h := limPt_continuousOn_smoothedNormSq hρ (T := T)
  refine continuous_iff_continuousAt.2 fun p => ?_
  have hcont : ContinuousAt (fun q : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ × ℝ =>
      smoothedNormSq (pathAt q.1 q.2.1 : Measure ℝ) (fun _ => 1) ρ q.2.2) (p.1, p.2, ε) :=
    h.continuousAt ((isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi)).mem_nhds
      ⟨Set.mem_univ _, Set.mem_univ _, hε⟩)
  exact hcont.comp (f := fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ => (p.1, p.2, ε))
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousAt

/-- For `ε > 0`, `(γ, t) ↦ ‖γ(t) ⋆ ρ_ε‖₂²` (in `[0, ∞]`) is measurable. -/
theorem limPt_measurable_smoothedNormSq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T ε : ℝ}
    (hε : 0 < ε) :
    Measurable fun p : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ =>
      ENNReal.ofReal (smoothedNormSq (pathAt p.1 p.2 : Measure ℝ) (fun _ => 1) ρ ε) :=
  ENNReal.measurable_ofReal.comp (limPt_continuous_smoothedNormSq hρ hε).measurable

/-- If `γ_k → γ` in `C([0,T], ℳ₊)` and `ε_k → ε > 0`, then
`‖γ_k(t) ⋆ ρ_{ε_k}‖₂² → ‖γ(t) ⋆ ρ_ε‖₂²` for every `t`. -/
theorem limPt_tendsto_smoothedNormSq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T ε : ℝ} (hε : 0 < ε)
    {γs : ℕ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hγ : Tendsto γs atTop (𝓝 γ)) {εs : ℕ → ℝ} (hεs : Tendsto εs atTop (𝓝 ε)) (t : ℝ) :
    Tendsto (fun k => smoothedNormSq (pathAt (γs k) t : Measure ℝ) (fun _ => 1) ρ (εs k)) atTop
      (𝓝 (smoothedNormSq (pathAt γ t : Measure ℝ) (fun _ => 1) ρ ε)) := by
  have h := limPt_continuousOn_smoothedNormSq hρ (T := T)
  have hcont : ContinuousAt (fun q : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) × ℝ × ℝ =>
      smoothedNormSq (pathAt q.1 q.2.1 : Measure ℝ) (fun _ => 1) ρ q.2.2) (γ, t, ε) :=
    h.continuousAt ((isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi)).mem_nhds
      ⟨Set.mem_univ _, Set.mem_univ _, hε⟩)
  have hlim : Tendsto (fun k => (γs k, t, εs k)) atTop (𝓝 (γ, t, ε)) :=
    hγ.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hεs)
  exact (hcont.tendsto.comp hlim :)

/-- `ε_n = ⌊ε n^{1/2}⌋ n^{-1/2} → ε` along `n_k → ∞`, and `⌊ε n_k^{1/2}⌋ ≥ 1` for all large `k`
(proof of Proposition 7.1 (2)). -/
theorem limPt_tendsto_epsN {n : ℕ → ℝ} (hn : Tendsto n atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (⌊ε * n k ^ (1 / 2 : ℝ)⌋₊ : ℝ) * n k ^ (-1 / 2 : ℝ)) atTop (𝓝 ε) ∧
      ∀ᶠ k in atTop, 1 ≤ ⌊ε * n k ^ (1 / 2 : ℝ)⌋₊ := by
  have hs : Tendsto (fun k => n k ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hn
  refine ⟨?_, ?_⟩
  · have h := (tendsto_nat_floor_mul_div_atTop hε.le).comp hs
    refine h.congr' ?_
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    simp only [Function.comp_apply, div_eq_mul_inv]
    congr 1
    rw [← Real.rpow_neg hk.le]
    norm_num
  · filter_upwards [(hs.const_mul_atTop hε).eventually_ge_atTop 1] with k hk
    exact Nat.one_le_floor_iff _ |>.2 hk

end QSSEPtoKPZ
