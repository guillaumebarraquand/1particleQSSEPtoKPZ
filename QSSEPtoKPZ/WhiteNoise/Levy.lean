/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Martingales.Stopping
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import QSSEPtoKPZ.WhiteNoise.LevyCore

/-!
# Lévy's characterization, one dimension (task G7a)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G7a.
See `docs/stage4-design.md`, Sections 1.2 (f) and 3.3, and `docs/stage4-interfaces.md`.

A continuous square-integrable martingale with bracket `c t` has conditionally Gaussian
increments: `∫_A e^{iu(N_t - N_s)} dℙ = e^{-c u² (t-s)/2} ℙ(A)` for `A ∈ 𝓖_s`. Proof by
discretization (`DEVIATIONS.md`, Section 7): stop at the first time `|N - N_s| ≥ R` (library
`hitTime`), cut `[s,t]` into `m` pieces, expand `exp(iuΔN_k + c u² Δt_k / 2)` to third order; the
remainders are bounded by `𝔼[max_k |ΔN_k| ∑_k ΔN_k²] → 0`, using
`𝔼[(∑_k ΔN_k²)²] ≤ C R² 𝔼 ∑_k ΔN_k²` for a martingale with increments bounded by `2R`; then `R → ∞`.

Proof (task G7a). The bounded case is `HasBracket.levy_setIntegral_bdd` (`LevyCore.lean`, with
`LevyAux.lean`, `LevyQV.lean`). Here: pass to the version of `N` with all paths continuous on
`[0, t]` (`IsCL2Mart.exists_version`), stop it at `τ_R`, the first time
`X_r = |N_{s ∨ (r ∧ t)} - N_s|` reaches `R` (`hitTime`, a stopping time of `𝓖ᵃ`), so that the
stopped process has bracket `c (r ∧ τ_R)` (`HasBracket.stopped`); the bounded case gives
`∫_A exp(i u (N_{t ∧ τ_R} - N_s) + c u² (t ∧ τ_R - s)/2) = ℙ(A)`, and `τ_R = t` for `R` large
(bounded continuous path), so dominated convergence as `R → ∞` gives the result.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


/-- The distance `X_r = |N_{s ∨ (r ∧ t)} - N_s|` of the path to its value at `s`, clamped to
`[s, t]`. -/
private def levyDist (N : ℝ → Ω → ℝ) (s t : ℝ≥0) (r : ℝ) (ω : Ω) : ℝ :=
  |N (max (s : ℝ) (min r t)) ω - N s ω|

/-- On `[s, t]`, `X_r = |N_r - N_s|`. -/
private lemma levyDist_of_mem {N : ℝ → Ω → ℝ} {s t : ℝ≥0} {r : ℝ} (hsr : (s : ℝ) ≤ r)
    (hrt : r ≤ t) (ω : Ω) : levyDist N s t r ω = |N r ω - N s ω| := by
  simp [levyDist, min_eq_left hrt, max_eq_right hsr]

/-- Before `s`, `X_r = 0`. -/
private lemma levyDist_of_le {N : ℝ → Ω → ℝ} {s t : ℝ≥0} {r : ℝ}
    (hrs : r ≤ s) (ω : Ω) : levyDist N s t r ω = 0 := by
  have : max (s : ℝ) (min r t) = s := max_eq_left ((min_le_left _ _).trans hrs)
  simp [levyDist, this]

/-- `X` has continuous paths on `[0, ∞)` if `N` has continuous paths on `[0, t]`. -/
private lemma levyDist_continuous {N : ℝ → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t) {ω : Ω}
    (hc : ContinuousOn (fun r => N r ω) (Set.Icc 0 (t : ℝ))) :
    Continuous fun r : ℝ≥0 => levyDist N s t r ω := by
  have hmap : Continuous fun r : ℝ≥0 => max (s : ℝ) (min (r : ℝ) t) :=
    continuous_const.max (NNReal.continuous_coe.min continuous_const)
  have hin : ∀ r : ℝ≥0, max (s : ℝ) (min (r : ℝ) t) ∈ Set.Icc 0 (t : ℝ) := fun r =>
    ⟨le_max_of_le_left s.2, max_le (NNReal.coe_le_coe.2 hst) (min_le_right _ _)⟩
  exact ((hc.comp_continuous hmap hin).sub continuous_const).abs

/-- `X` is adapted if `N` is. -/
private lemma levyDist_measurable {𝓕 : Filtration ℝ≥0 mΩ} {N : ℝ → Ω → ℝ} {s t : ℝ≥0}
    (hm : ∀ r : ℝ≥0, StronglyMeasurable[𝓕 r] (N r)) (r : ℝ≥0) :
    Measurable[𝓕 r] (levyDist N s t r) := by
  rcases le_total r s with hrs | hsr
  · have : levyDist N s t r = fun _ => 0 := funext (levyDist_of_le (NNReal.coe_le_coe.2 hrs))
    rw [this]; exact measurable_const
  · set q : ℝ≥0 := max s (min r t)
    have hq : (q : ℝ) = max (s : ℝ) (min (r : ℝ) t) := by simp [q]
    have hqr : q ≤ r := max_le hsr (min_le_left _ _)
    have : levyDist N s t r = fun ω => |N q ω - N s ω| := by
      ext ω; simp only [levyDist, hq]
    rw [this]
    exact continuous_abs.measurable.comp
      (((hm q).mono (𝓕.mono hqr)).measurable.sub ((hm s).mono (𝓕.mono hsr)).measurable)

/-- The hitting time of level `R > 0` by `X` is at least `s`, since `X = 0` on `[0, s]`. -/
private lemma le_hitTime_levyDist {N : ℝ → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t) {R : ℝ}
    (hR : 0 < R) (ω : Ω) : s ≤ hitTime (levyDist N s t) R t ω := by
  refine le_inf (le_csInf ⟨t, Or.inr rfl⟩ ?_) hst
  rintro r (hr | hr)
  · by_contra hlt
    have h0 := levyDist_of_le (N := N) (t := t) (NNReal.coe_le_coe.2 (not_le.1 hlt).le) ω
    have : R ≤ levyDist N s t r ω := hr
    linarith
  · rw [Set.mem_singleton_iff.1 hr]; exact hst

/-- **The stopped identity.** For a version `N` of the martingale with all paths continuous on
`[0, t]` and adapted to `𝓖ᵃ`, and `τ = τ_R`,
`∫_A exp(i u (N_{t ∧ τ} - N_s) + u² (c (t ∧ τ) - c s) / 2) = ℙ(A)`. -/
private lemma levy_stopped_eq [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    {N : ℝ → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) {s t : ℝ≥0} (hst : s ≤ t)
    (hB : HasBracket t (nullAug μ 𝓖) N (fun r _ => c * r) μ)
    (hm : ∀ r : ℝ≥0, StronglyMeasurable[nullAug μ 𝓖 r] (N r))
    (hcont : ∀ ω, ContinuousOn (fun r => N r ω) (Set.Icc 0 (t : ℝ))) {R : ℝ} (hR : 0 < R)
    (u : ℝ) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Complex.exp (((u * (N (min (t : ℝ) (hitTime (levyDist N s t) R t ω)) ω -
        N s ω) : ℝ) : ℂ) * Complex.I + ((u ^ 2 / 2 *
          (c * min (t : ℝ) (hitTime (levyDist N s t) R t ω) - c * s) : ℝ) : ℂ)) ∂μ =
      μ.real A ∧
    AEStronglyMeasurable (fun ω => N (min (t : ℝ) (hitTime (levyDist N s t) R t ω)) ω) μ ∧
    AEStronglyMeasurable (fun ω => c * min (t : ℝ) (hitTime (levyDist N s t) R t ω)) μ := by
  set τ := hitTime (levyDist N s t) R t with hτdef
  have hτ : IsStoppingTime (nullAug μ 𝓖) (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_hitTime (levyDist_measurable hm) (fun ω => levyDist_continuous hst (hcont ω))
      R t
  have hτ' : IsStoppingTime (nullAug μ (nullAug μ 𝓖)) (fun ω => (τ ω : WithTop ℝ≥0)) :=
    fun i => le_nullAug μ (nullAug μ 𝓖) i _ (hτ i)
  have hτt : ∀ ω, (τ ω : ℝ) ≤ t := fun ω => NNReal.coe_le_coe.2 (hitTime_le _ _ _ ω)
  have hsτ : ∀ ω, (s : ℝ) ≤ τ ω := fun ω => NNReal.coe_le_coe.2 (le_hitTime_levyDist hst hR ω)
  have hS := hB.stopped hτ' hτt
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  have key := hS.levy_setIntegral_bdd hst le_rfl hc (R := R) ?_ ?_ ?_ u
    (le_nullAug μ 𝓖 s _ hA)
  · refine ⟨by simpa [min_eq_left (hsτ _)] using key, (hS.memLp t le_rfl).aestronglyMeasurable,
      (hS.integrable_bracket t le_rfl).aestronglyMeasurable⟩
  · -- continuity of the stopped paths
    intro ω
    refine (hcont ω).comp (continuous_id.min continuous_const).continuousOn fun r hr => ?_
    exact ⟨le_min (s.2.trans hr.1) (τ ω).2, (min_le_left _ _).trans hr.2⟩
  · -- the stopped paths stay within `R` of `N_s`
    intro ω r hsr hrt
    simp only [min_eq_left (hsτ ω)]
    set q : ℝ≥0 := min r (τ ω)
    have hq : (q : ℝ) = min (r : ℝ) (τ ω) := by simp [q]
    have hsq : (s : ℝ) ≤ q := by rw [hq]; exact le_min (NNReal.coe_le_coe.2 hsr) (hsτ ω)
    have hqt : (q : ℝ) ≤ t := by
      rw [hq]; exact (min_le_left _ _).trans (NNReal.coe_le_coe.2 hrt)
    rw [← hq, ← levyDist_of_mem hsq hqt]
    have h0 : levyDist N s t ((0 : ℝ≥0) : ℝ) ω ≤ R := by
      rw [levyDist_of_le (by simp)]; exact hR.le
    exact le_of_le_hitTime (levyDist_continuous hst (hcont ω)) h0 (min_le_right r (τ ω))
  · -- the stopped bracket is `c`-Lipschitz
    intro ω r r' _ hrr' _
    have h1 : min (r : ℝ) (τ ω) ≤ min (r' : ℝ) (τ ω) :=
      min_le_min_right _ (NNReal.coe_le_coe.2 hrr')
    have h2 : min (r' : ℝ) (τ ω) - min (r : ℝ) (τ ω) ≤ r' - r := by
      rcases le_total (r' : ℝ) (τ ω) with h | h
      · rw [min_eq_left h, min_eq_left ((NNReal.coe_le_coe.2 hrr').trans h)]
      · rw [min_eq_right h]
        have : (r : ℝ) ≤ r' := NNReal.coe_le_coe.2 hrr'
        have := min_le_left (r : ℝ) (τ ω)
        rcases le_total (r : ℝ) (τ ω) with h' | h'
        · rw [min_eq_left h']; linarith
        · rw [min_eq_right h']; linarith
    constructor
    · nlinarith
    · nlinarith

/-- **Lévy's characterization** (one dimension, set-integral form). -/
theorem levy_setIntegral {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    {N : ℝ → Ω → ℝ} {c T : ℝ} (hc : 0 ≤ c)
    (hN : HasBracket T 𝓖 N (fun t _ => c * t) μ) {s t : ℝ≥0} (hst : s ≤ t) (htT : (t : ℝ) ≤ T)
    (u : ℝ) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Complex.exp (((u * (N t ω - N s ω) : ℝ) : ℂ) * Complex.I) ∂μ =
      (Real.exp (-(c * u ^ 2 * ((t : ℝ) - s) / 2)) : ℂ) * (μ.real A : ℂ) := by
  -- a version of `N` with all paths continuous on `[0, t]`, adapted to `𝓖ᵃ`
  have hN' := hN.mono_horizon htT
  obtain ⟨N', hN'm, hN'c, hN'eq, -⟩ := hN'.toIsCL2Mart.exists_version
  have hB : HasBracket t (nullAug μ 𝓖) N' (fun r _ => c * r) μ :=
    hasBracket_nullAug_iff.2 (hN'.congr t.2
      (by filter_upwards [hN'eq] with ω hω r hr using (hω r hr).symm)
      (ae_of_all _ fun _ _ _ => rfl))
  have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
  -- the stopped identities, `R = j + 1`
  set τ : ℕ → Ω → ℝ≥0 := fun j => hitTime (levyDist N' s t) ((j : ℝ) + 1) t with hτ
  have hstop := fun j : ℕ => levy_stopped_eq hc hst hB hN'm hN'c
    (by positivity : (0 : ℝ) < (j : ℝ) + 1) u hA
  -- `τ_j = t` eventually, for every `ω`
  have hev : ∀ ω, ∀ᶠ j in atTop, τ j ω = t := by
    intro ω
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hN'c ω)
    obtain ⟨j0, hj0⟩ := exists_nat_gt (2 * C)
    filter_upwards [eventually_ge_atTop j0] with j hj
    refine hitTime_eq_of_forall_lt fun r _ => ?_
    have hq : max (s : ℝ) (min (r : ℝ) t) ∈ Set.Icc 0 (t : ℝ) :=
      ⟨le_max_of_le_left s.2, max_le hst' (min_le_right _ _)⟩
    have h1 := hC _ hq
    have h2 := hC s ⟨s.2, hst'⟩
    have hj' : (j0 : ℝ) ≤ j := by exact_mod_cast hj
    simp only [Real.norm_eq_abs] at h1 h2
    calc levyDist N' s t r ω ≤ |N' (max (s : ℝ) (min (r : ℝ) t)) ω| + |N' s ω| := abs_sub _ _
      _ < (j : ℝ) + 1 := by linarith
  -- dominated convergence as `j → ∞`
  set K : ℝ := Real.exp (u ^ 2 / 2 * (c * t - c * s)) with hK
  set F : ℕ → Ω → ℂ := fun j ω => Complex.exp (((u * (N' (min (t : ℝ) (τ j ω)) ω - N' s ω) : ℝ) :
    ℂ) * Complex.I + ((u ^ 2 / 2 * (c * min (t : ℝ) (τ j ω) - c * s) : ℝ) : ℂ)) with hF
  set G : Ω → ℂ := fun ω => Complex.exp (((u * (N' t ω - N' s ω) : ℝ) : ℂ) * Complex.I +
    ((u ^ 2 / 2 * (c * t - c * s) : ℝ) : ℂ)) with hG
  have hNs : AEStronglyMeasurable (N' s) μ :=
    ((hN'm s).mono ((nullAug μ 𝓖).le s)).aestronglyMeasurable
  have hFm : ∀ j, AEStronglyMeasurable (F j) (μ.restrict A) := fun j => by
    have h1 : AEStronglyMeasurable (fun ω => N' (min (t : ℝ) (τ j ω)) ω) μ := (hstop j).2.1
    have h2 : AEStronglyMeasurable (fun ω => c * min (t : ℝ) (τ j ω)) μ := (hstop j).2.2
    have h3 : AEStronglyMeasurable (fun ω => u * (N' (min (t : ℝ) (τ j ω)) ω - N' s ω)) μ :=
      (h1.sub hNs).const_mul u
    have h4 : AEStronglyMeasurable (fun ω => u ^ 2 / 2 * (c * min (t : ℝ) (τ j ω) - c * s)) μ :=
      (h2.sub aestronglyMeasurable_const).const_mul _
    exact (Complex.continuous_exp.comp_aestronglyMeasurable
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable h3).mul_const _).add
        (Complex.continuous_ofReal.comp_aestronglyMeasurable h4))).restrict
  have hFb : ∀ j ω, ‖F j ω‖ ≤ K := fun j ω => by
    simp only [hF, Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := min_le_left (t : ℝ) (τ j ω)
    nlinarith
  have hlim : Tendsto (fun j => ∫ ω in A, F j ω ∂μ) atTop (𝓝 (∫ ω in A, G ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K) hFm (integrable_const _)
      (fun j => ae_of_all _ (hFb j)) (ae_of_all _ fun ω => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev ω] with j hj
    simp only [hF, hG, hj, min_self]
  have hGA : ∫ ω in A, G ω ∂μ = μ.real A :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun j => ((hstop j).1).symm)
  -- factor out the deterministic exponential
  have hfac : ∀ ω, G ω = Complex.exp (((u * (N' t ω - N' s ω) : ℝ) : ℂ) * Complex.I) * (K : ℂ) :=
    fun ω => by simp only [hG, hK, Complex.exp_add, Complex.ofReal_exp]
  simp_rw [hfac] at hGA
  rw [integral_mul_const] at hGA
  have hK0 : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  have hI : ∫ ω in A, Complex.exp (((u * (N' t ω - N' s ω) : ℝ) : ℂ) * Complex.I) ∂μ =
      (Real.exp (-(c * u ^ 2 * ((t : ℝ) - s) / 2)) : ℂ) * (μ.real A : ℂ) := by
    have hx : -(c * u ^ 2 * ((t : ℝ) - s) / 2) = -(u ^ 2 / 2 * (c * t - c * s)) := by ring
    rw [hx, Real.exp_neg, ← hK, Complex.ofReal_inv, ← hGA, eq_inv_mul_iff_mul_eq₀ hK0, mul_comm]
  -- back to `N`
  rw [← hI]
  refine setIntegral_congr_ae ((𝓖.le s) _ hA) ?_
  filter_upwards [hN'eq] with ω hω _
  rw [hω t ⟨t.2, le_rfl⟩, hω s ⟨s.2, hst'⟩]

end QSSEPtoKPZ
