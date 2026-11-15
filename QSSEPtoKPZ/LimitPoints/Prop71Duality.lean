/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Mollify

/-!
# A duality bound from bounded smoothed norms (task Q2)

Proof of Proposition 7.1 (2), in the form of `docs/stage4-design.md`, 1.2 (e): if
`liminf_k ‖μ ⋆ ρ_{1/(k+1)}‖₂² < ∞` for a finite measure `μ` on `ℝ`, then there is `C` with
`|μ(f)| ≤ C ‖f‖₂` for every continuous compactly supported `f`
(`limPt_bound_of_liminf`). This is the hypothesis of the `L²` density criterion
`withDensity_limDensity_of_bound`.

Proof: with `g_ε(x) = ∫ ρ_ε(y - x) f(y) dy`, Fubini gives `μ(g_ε) = ∫ (μ ⋆ ρ_ε) f`, hence
`|μ(g_ε)| ≤ ‖μ ⋆ ρ_ε‖₂ ‖f‖₂` (Cauchy–Schwarz), and `g_ε → f` uniformly (uniform continuity of
`f`), so `|μ(f) - μ(g_ε)| ≤ μ(ℝ) sup |f - g_ε| → 0`. Along the `k` with `‖μ ⋆ ρ_{1/(k+1)}‖₂² < c`
(infinitely many), `|μ(f)| ≤ c^{1/2} ‖f‖₂`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {ρ : ℝ → ℝ}

/-- The mollified test function `g_ε(x) = ∫ ρ_ε(y - x) f(y) dy` approximates a continuous
compactly supported `f` uniformly as `ε → 0`. -/
private lemma prop71Dens_unif_approx (hρ : IsMollifier ρ) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ ε, 0 < ε → ε < η → ∀ x, |(∫ y, rhoEps ρ ε (y - x) * f y) - f x| ≤ δ := by
  obtain ⟨η, hη, hu⟩ :=
    Metric.uniformContinuous_iff.1 (hfc.uniformContinuous_of_continuous hf) δ hδ
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  refine ⟨η, hη, fun ε hε hεη x => ?_⟩
  have hr : Integrable fun y => rhoEps ρ ε (y - x) :=
    (mollif_rhoEps_integrable hρ hε).comp_sub_right x
  have hrf : Integrable fun y => rhoEps ρ ε (y - x) * f y :=
    hr.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hB)
  have h1 : ∫ y, rhoEps ρ ε (y - x) = 1 := (mollif_integral_rhoEps_sub hρ hε x).2
  have heq : (∫ y, rhoEps ρ ε (y - x) * f y) - f x =
      ∫ y, rhoEps ρ ε (y - x) * (f y - f x) := by
    simp_rw [mul_sub]
    rw [integral_sub hrf (hr.mul_const _), integral_mul_const, h1, one_mul]
  rw [heq]
  have hb : ∀ y, ‖rhoEps ρ ε (y - x) * (f y - f x)‖ ≤ rhoEps ρ ε (y - x) * δ := by
    intro y
    have h0 := mollif_rhoEps_nonneg hρ hε.le (y - x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    by_cases hy : |y - x| < ε
    · refine mul_le_mul_of_nonneg_left ?_ h0
      have := hu (a := y) (b := x) (by rw [Real.dist_eq]; linarith)
      rw [Real.dist_eq] at this
      exact this.le
    · rw [mollif_rhoEps_eq_zero hρ hε (not_lt.1 hy)]
      simp
  calc |∫ y, rhoEps ρ ε (y - x) * (f y - f x)|
      = ‖∫ y, rhoEps ρ ε (y - x) * (f y - f x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, rhoEps ρ ε (y - x) * δ :=
        norm_integral_le_of_norm_le (hr.mul_const _) (ae_of_all _ hb)
    _ = δ := by rw [integral_mul_const, h1, one_mul]

/-- **Fubini**: `∫ (μ ⋆ ρ_ε)(y) f(y) dy = ∫ g_ε dμ`, `g_ε(x) = ∫ ρ_ε(y - x) f(y) dy`. -/
private lemma prop71Dens_fubini (hρ : IsMollifier ρ) (μ : FiniteMeasure ℝ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ y, (∫ x, rhoEps ρ ε (y - x) ∂(μ : Measure ℝ)) * f y =
      ∫ x, (∫ y, rhoEps ρ ε (y - x) * f y) ∂(μ : Measure ℝ) := by
  have hF : Integrable (Function.uncurry fun y x => rhoEps ρ ε (y - x) * f y)
      (volume.prod (μ : Measure ℝ)) := by
    refine Integrable.mono'
      (((hf.integrable_of_hasCompactSupport hfc).norm.const_mul (mollifSup ρ / ε)).comp_fst
        (μ : Measure ℝ)) ?_ ?_
    · exact (((mollif_rhoEps_continuous hρ ε).comp (continuous_fst.sub continuous_snd)).mul
        (hf.comp continuous_fst)).aestronglyMeasurable
    · refine ae_of_all _ fun p => ?_
      simp only [Function.uncurry, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by rw [Real.norm_eq_abs]; exact mollif_abs_rhoEps_le hρ hε _) (norm_nonneg _)
  calc ∫ y, (∫ x, rhoEps ρ ε (y - x) ∂(μ : Measure ℝ)) * f y
      = ∫ y, ∫ x, rhoEps ρ ε (y - x) * f y ∂(μ : Measure ℝ) := by
        congr 1
        funext y
        rw [integral_mul_const]
    _ = ∫ x, (∫ y, rhoEps ρ ε (y - x) * f y) ∂(μ : Measure ℝ) := integral_integral_swap hF

/-- **Cauchy–Schwarz**: `|∫ (μ ⋆ ρ_ε) f| ≤ ‖μ ⋆ ρ_ε‖₂ ‖f‖₂`. -/
private lemma prop71Dens_cauchySchwarz (hρ : IsMollifier ρ) (μ : FiniteMeasure ℝ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    |∫ y, (∫ x, rhoEps ρ ε (y - x) ∂(μ : Measure ℝ)) * f y| ≤
      smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ ε ^ (1 / 2 : ℝ) *
        (∫ x, f x ^ 2) ^ (1 / 2 : ℝ) := by
  set u : ℝ → ℝ := fun y => ∫ x, rhoEps ρ ε (y - x) ∂(μ : Measure ℝ) with hu
  have hS := (smoothedNormSq_eq hρ (μ : Measure ℝ) (φ := fun _ => 1) continuous_const
    ⟨1, fun _ => by simp⟩ hε).1
  simp only [one_mul] at hS
  have hSu : smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ ε = ∫ y, u y ^ 2 := by
    simp only [smoothedNormSq, one_mul, hu]
  have hu0 : ∀ y, 0 ≤ u y := fun y =>
    integral_nonneg fun _ => mollif_rhoEps_nonneg hρ hε.le _
  have huc : Continuous u :=
    (densFM_continuous_conv hρ hε).comp (continuous_const.prodMk continuous_id)
  have hum : MemLp u (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq huc.aestronglyMeasurable]
    exact hS
  have hfm : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) volume :=
    (hf.memLp_of_hasCompactSupport hfc).norm
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ hu0) (ae_of_all _ fun x => norm_nonneg (f x)) hum hfm
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hH
  rw [hSu]
  calc |∫ y, u y * f y| ≤ ∫ y, |u y * f y| := abs_integral_le_integral_abs
    _ = ∫ y, u y * |f y| := by
        congr 1
        funext y
        rw [abs_mul, abs_of_nonneg (hu0 y)]
    _ ≤ _ := hH

/-- **Duality bound** (proof of Proposition 7.1 (2)): if `liminf_k ‖μ ⋆ ρ_{1/(k+1)}‖₂² < ∞`, then
`|μ(f)| ≤ C ‖f‖₂` for some `C` and every continuous compactly supported `f`. -/
theorem limPt_bound_of_liminf (hρ : IsMollifier ρ) {μ : FiniteMeasure ℝ}
    (h : liminf (fun k : ℕ => ENNReal.ofReal
      (smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ (1 / ((k : ℝ) + 1)))) atTop < ⊤) :
    ∃ C : ℝ, ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ) := by
  set L := liminf (fun k : ℕ => ENNReal.ofReal
    (smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ (1 / ((k : ℝ) + 1)))) atTop with hL
  set c : ℝ := L.toReal + 1 with hc
  have hc0 : 0 < c := by positivity
  have hLc : L < ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_toReal h.ne, ENNReal.ofReal_lt_ofReal_iff hc0]
    linarith
  have hfreq : ∃ᶠ k : ℕ in atTop,
      smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ (1 / ((k : ℝ) + 1)) < c :=
    (frequently_lt_of_liminf_lt (by isBoundedDefault) hLc).mono fun k hk =>
      (ENNReal.ofReal_lt_ofReal_iff hc0).1 hk
  refine ⟨c ^ (1 / 2 : ℝ), fun f hf hfc => ?_⟩
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  set M := (μ : Measure ℝ).real Set.univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set δ' := δ / (M + 1) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  obtain ⟨η, hη, happ⟩ := prop71Dens_unif_approx hρ hf hfc hδ'0
  have hev : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < η :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hη)
  obtain ⟨k, hkS, hkη⟩ := (hfreq.and_eventually hev).exists
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  set g : ℝ → ℝ := fun x => ∫ y, rhoEps ρ ε (y - x) * f y with hg
  have hgm : StronglyMeasurable g := by
    refine StronglyMeasurable.integral_prod_right (f := fun x y => rhoEps ρ ε (y - x) * f y) ?_
    exact (((mollif_rhoEps_continuous hρ ε).comp (continuous_snd.sub continuous_fst)).mul
      (hf.comp continuous_snd)).stronglyMeasurable
  have hgf : ∀ x, |g x - f x| ≤ δ' := happ ε hε hkη
  have hfi : Integrable f (μ : Measure ℝ) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hB)
  have hgi : Integrable g (μ : Measure ℝ) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (B + δ') (ae_of_all _ fun x => ?_)
    have h1 := hgf x
    have h2 := hB x
    rw [Real.norm_eq_abs] at h2 ⊢
    calc |g x| = |(g x - f x) + f x| := by ring_nf
      _ ≤ |g x - f x| + |f x| := abs_add_le _ _
      _ ≤ B + δ' := by linarith
  -- `|μ(g)| ≤ c^{1/2} ‖f‖₂`
  have hS0 : 0 ≤ smoothedNormSq (μ : Measure ℝ) (fun _ => 1) ρ ε :=
    integral_nonneg fun _ => sq_nonneg _
  have hg_le : |∫ x, g x ∂(μ : Measure ℝ)| ≤ c ^ (1 / 2 : ℝ) * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [hg, ← prop71Dens_fubini hρ μ hε hf hfc]
    refine (prop71Dens_cauchySchwarz hρ μ hε hf hfc).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (integral_nonneg fun _ =>
      sq_nonneg _) _)
    exact Real.rpow_le_rpow hS0 hkS.le (by norm_num)
  -- `|μ(f - g)| ≤ δ' μ(ℝ) ≤ δ`
  have hfg_le : |∫ x, (f x - g x) ∂(μ : Measure ℝ)| ≤ δ := by
    have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure ℝ)) (f := fun x => f x - g x)
      (C := δ') (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_sub_comm]; exact hgf x)
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [← hM, hδ', div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hsplit : ∫ x, f x ∂(μ : Measure ℝ) =
      (∫ x, g x ∂(μ : Measure ℝ)) + ∫ x, (f x - g x) ∂(μ : Measure ℝ) := by
    rw [integral_sub hfi hgi]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hg_le hfg_le)

end QSSEPtoKPZ
