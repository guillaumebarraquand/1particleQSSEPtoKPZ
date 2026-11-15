/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Identification
public import QSSEPtoKPZ.WaveFunction.Good
public import QSSEPtoKPZ.ItoIntegral.Product
public import QSSEPtoKPZ.Martingales.NullAug
public import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Itô form of the equation of the wave function on `Λ_L` (task L1)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L1.
`docs/stage5-design.md`, Section 3.2.

* `IsWaveIto L 𝓖 B ψ₀ ψ μ`: `ψ` is adapted, has continuous paths in `ℓ²(ℤ)` for **every** `ω`,
  vanishes outside `Λ_L` for every `ω`, starts from `ψ₀` for every `ω`, and for `x ∈ Λ_L` the
  real and imaginary parts of `ψ(x)` are Itô processes (up to every deterministic time `N`) with
  drift `-(D_L(x,x)/2) ψ(x)` and the diffusion coefficients `waveDiffRe`, `waveDiffIm` of Stage 2:
  `dψ_t(x) = i ψ_t(x+1) dW⁽ˣ⁾_t + i ψ_t(x-1) d\bar W⁽ˣ⁻¹⁾_t - (D_L(x,x)/2) ψ_t(x) dt`.
* `waveDiffC ψ x i = waveDiffRe ψ x i + i waveDiffIm ψ x i`: the complex coefficient of
  `dB_i` in `dψ(x)`.
* `IsWaveIto.isWaveFunction`: an Itô solution started from `e₀` is a wave function.
* `IsBrownianFamily.isProbabilityMeasure`, linearity of the coefficients, and
  `isStoppingTime_waveStop_of_continuous` (the localizing time `τ_R ∧ N` of any adapted process
  with continuous `ℓ²` paths is a stopping time).

Proofs (task L1): `IsWaveIto.isWaveFunction` localizes at `τ_{n+1} ∧ N` (`waveStop`): on
`{τ_{n+1} ∧ N = N}` the Riemann sums are those of the bounded integrand `b 𝟙_{[0,τ_{n+1}]}`,
which converge in `L²` to `I_N(b 𝟙_{[0,τ_{n+1}]}) = I_{τ_{n+1}}(b 𝟙_{[0,N]})`
(`tendsto_riemann_stochInt_finset`, `stochInt_indicator_stoppingTime`), and
`μ(τ_{n+1} ∧ N ≠ N) → 0` by continuity of the paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- **Itô form of the wave equation on `Λ_L`** with initial condition `ψ0`: `ψ` is adapted to
`𝓖`, all its paths are continuous from `[0, ∞)` to `ℓ²(ℤ)`, it vanishes outside `Λ_L` and starts
from `ψ0` (for every `ω`), and for every `x ∈ Λ_L` and every deterministic time `N`,
`Re ψ(x)` and `Im ψ(x)` are Itô processes up to `N` with drifts `-(D_L(x,x)/2) Re ψ(x)`,
`-(D_L(x,x)/2) Im ψ(x)` and diffusion coefficients `waveDiffRe ψ x`, `waveDiffIm ψ x`. -/
structure IsWaveIto (L : ℕ∞) (𝓖 : Filtration ℝ≥0 mΩ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ)
    (ψ0 : ℓ²(ℤ, ℂ)) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop where
  adapted : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x
  continuous : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω
  support : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0
  init : ∀ ω, ψ 0 ω = ψ0
  re : ∀ x ∈ box L, ∀ N : ℝ≥0, IsItoProcessUpTo 𝓖 μ B (fun _ => N)
    (fun t ω => (ψ t ω x).re) (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).re)
    (waveDiffRe ψ x)
  im : ∀ x ∈ box L, ∀ N : ℝ≥0, IsItoProcessUpTo 𝓖 μ B (fun _ => N)
    (fun t ω => (ψ t ω x).im) (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).im)
    (waveDiffIm ψ x)

/-- The complex diffusion coefficient of `dB_i` in `dψ(x)`:
`waveDiffC ψ x = (i ψ(x+1), -ψ(x+1), i ψ(x-1), ψ(x-1)) / √2` on the indices
`(x,0), (x,1), (x-1,0), (x-1,1)`, and `0` on the other indices. -/
def waveDiffC (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) : ℂ :=
  (waveDiffRe ψ x i s ω : ℂ) + Complex.I * (waveDiffIm ψ x i s ω : ℂ)

@[simp] lemma waveDiffC_re (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    (waveDiffC ψ x i s ω).re = waveDiffRe ψ x i s ω := by
  simp [waveDiffC]

@[simp] lemma waveDiffC_im (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    (waveDiffC ψ x i s ω).im = waveDiffIm ψ x i s ω := by
  simp [waveDiffC]

/-- The values of `waveDiffC`: `i ψ(x+1)/√2`, `-ψ(x+1)/√2`, `i ψ(x-1)/√2`, `ψ(x-1)/√2` on
`(x,0), (x,1), (x-1,0), (x-1,1)`, and `0` elsewhere. -/
theorem waveDiffC_eq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    waveDiffC ψ x i s ω =
      if i = (x, 0) then Complex.I * ψ s ω (x + 1) / Real.sqrt 2
      else if i = (x, 1) then -ψ s ω (x + 1) / Real.sqrt 2
      else if i = (x - 1, 0) then Complex.I * ψ s ω (x - 1) / Real.sqrt 2
      else if i = (x - 1, 1) then ψ s ω (x - 1) / Real.sqrt 2
      else 0 := by
  have h1 : x - 1 ≠ x := by omega
  unfold waveDiffC waveDiffRe waveDiffIm
  split_ifs <;> apply Complex.ext <;>
    simp [Complex.div_ofReal_re, Complex.div_ofReal_im, neg_div]

/-- A Brownian family with a nonempty index set lives on a probability space (the increments
have a Gaussian law). -/
theorem IsBrownianFamily.isProbabilityMeasure {ι : Type*} [Nonempty ι] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ι → ℝ → Ω → ℝ} (hB : IsBrownianFamily 𝓕 W μ) : IsProbabilityMeasure μ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hB.gaussian i 0 0 le_rfl).isProbabilityMeasure

/-- Linearity of `waveDiffRe` in `ψ`. -/
theorem waveDiffRe_sub (ψ φ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    waveDiffRe (fun s ω => ψ s ω - φ s ω) x i s ω =
      waveDiffRe ψ x i s ω - waveDiffRe φ x i s ω := by
  unfold waveDiffRe
  split_ifs <;>
    (try simp only [lp.coeFn_sub, Pi.sub_apply, Complex.sub_re, Complex.sub_im]) <;> ring

/-- Linearity of `waveDiffIm` in `ψ`. -/
theorem waveDiffIm_sub (ψ φ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) :
    waveDiffIm (fun s ω => ψ s ω - φ s ω) x i s ω =
      waveDiffIm ψ x i s ω - waveDiffIm φ x i s ω := by
  unfold waveDiffIm
  split_ifs <;>
    (try simp only [lp.coeFn_sub, Pi.sub_apply, Complex.sub_re, Complex.sub_im]) <;> ring

/-- The norm `‖ψ_t‖` of an adapted `ℓ²`-valued process is adapted (auxiliary form of
`measurable_norm_of_adapted`). -/
private lemma waveIto_measurable_norm {𝓖 : Filtration ℝ≥0 mΩ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x) (t : ℝ≥0) :
    Measurable[𝓖 t] fun ω => ‖ψ t ω‖ := by
  simp only [lp2_norm_eq_sqrt_tsum]
  have hm : ∀ x, Measurable[𝓖 t] fun ω => ‖ψ t ω x‖ ^ 2 := fun x =>
    (continuous_norm.pow 2).measurable.comp (hadapt t x)
  exact Real.continuous_sqrt.measurable.comp
    (@Measurable.tsum Ω ℝ ℤ (𝓖 t) _ _ _ _ _ _ _ _ _ _ _ _ hm)

/-- **Localizing times.** For a process `ψ` with coordinates adapted to `𝓖` and all paths
continuous in `ℓ²(ℤ)`, `τ_R ∧ N` (`waveStop`, the first time `‖ψ_t‖ ≥ R`, capped at `N`) is a
stopping time of `𝓖`. -/
theorem isStoppingTime_waveStop_of_continuous {𝓖 : Filtration ℝ≥0 mΩ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) (R : ℝ) (N : ℝ≥0) :
    IsStoppingTime 𝓖 (fun ω => (waveStop ψ R N ω : WithTop ℝ≥0)) :=
  isStoppingTime_hitTime (X := fun t ω => ‖ψ t ω‖)
    (fun t => waveIto_measurable_norm hadapt t) (fun ω => (hc ω).norm) R N

/-- The norm `‖ψ_t‖` of an adapted `ℓ²`-valued process is adapted. -/
theorem measurable_norm_of_adapted {𝓖 : Filtration ℝ≥0 mΩ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x) (t : ℝ≥0) :
    Measurable[𝓖 t] fun ω => ‖ψ t ω‖ :=
  waveIto_measurable_norm hadapt t

/-! ### Localization of the Riemann sums -/

section Localize

/-- **Localization of convergence in measure.** If for every `δ > 0` there are sequences
`f^δ_m → g^δ` in measure and an event `A` with `μ(Aᶜ) ≤ δ` such that, almost surely on `A`,
`f^δ_m = f_m` for all `m` and `g^δ = g`, then `f_m → g` in measure. -/
private lemma waveIto_tendstoInMeasure_of_localize {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : ∀ δ : ℝ≥0∞, 0 < δ → ∃ (fR : ℕ → Ω → ℝ) (gR : Ω → ℝ) (A : Set Ω),
      TendstoInMeasure μ fR atTop gR ∧ μ Aᶜ ≤ δ ∧
        ∀ᵐ ω ∂μ, ω ∈ A → (∀ m, fR m ω = f m ω) ∧ gR ω = g ω) :
    TendstoInMeasure μ f atTop g := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨fR, gR, A, hconv, hA, hae⟩ := h (δ / 2) (ENNReal.half_pos hδ.ne')
  have hev := ENNReal.tendsto_nhds_zero.1 (hconv ε hε) (δ / 2) (ENNReal.half_pos hδ.ne')
  rw [ae_iff] at hae
  set E : Set Ω := {ω | ¬(ω ∈ A → (∀ m, fR m ω = f m ω) ∧ gR ω = g ω)} with hE
  filter_upwards [hev] with m hm
  calc μ {ω | ε ≤ edist (f m ω) (g ω)}
      ≤ μ (Aᶜ ∪ E ∪ {ω | ε ≤ edist (fR m ω) (gR ω)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωA : ω ∈ A
        · by_cases hωE : ω ∈ E
          · exact Or.inl (Or.inr hωE)
          · have h' : (∀ m, fR m ω = f m ω) ∧ gR ω = g ω := by
              simp only [hE, Set.mem_ofPred_eq, not_not] at hωE
              exact hωE hωA
            refine Or.inr ?_
            simp only [Set.mem_ofPred_eq, h'.1 m, h'.2]
            exact hω
        · exact Or.inl (Or.inl hωA)
    _ ≤ μ Aᶜ + μ E + μ {ω | ε ≤ edist (fR m ω) (gR ω)} :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ δ / 2 + 0 + δ / 2 := by
        rw [hae]
        exact add_le_add (add_le_add hA le_rfl) hm
    _ = δ := by rw [add_zero, ENNReal.add_halves]

/-- The grid points `k t / m`, `k < m`, of the Riemann sums lie in `[0, t]`. -/
private lemma waveIto_grid_le {t : ℝ} (ht : 0 ≤ t) {m k : ℕ} (hk : k ∈ Finset.range m) :
    (k : ℝ) * t / m ≤ t := by
  have hkm : k < m := Finset.mem_range.1 hk
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le k).trans_lt hkm
  rw [div_le_iff₀ hm]
  have : (k : ℝ) ≤ m := by exact_mod_cast hkm.le
  nlinarith

/-- A function continuous on `[0, ∞)` (as a function of `t : ℝ≥0`) is continuous at every
`s > 0`. -/
private lemma waveIto_continuousAt {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) {s : ℝ} (hs : 0 < s) : ContinuousAt f s := by
  have h1 : ContinuousAt (fun r : ℝ => f (r.toNNReal : ℝ)) s :=
    (hf.comp continuous_real_toNNReal).continuousAt
  refine h1.congr ?_
  filter_upwards [eventually_gt_nhds hs] with r hr
  simp [Real.coe_toNNReal _ hr.le]

variable {ι : Type*} [Countable ι] {𝓖 : Filtration ℝ≥0 mΩ} {ν : Measure Ω}
  [IsProbabilityMeasure ν] {W : ι → ℝ → Ω → ℝ}

/-- **Riemann sums of a localized integrand.** Let `b` be a family of real processes vanishing
outside a finite set `S`, adapted, with all paths continuous on `[0, ∞)`, such that
`b 𝟙_{[0,N]}` is Itô-integrable. Let `τ_n ≤ N` be stopping times with `|b| ≤ K_n` on `[0, τ_n]`
and `ν(τ_n ≠ N) → 0`. Then the left-point Riemann sums `∑_{i ∈ S} R(bᵢ, Wᵢ)` on `[0, N]`
converge in measure to `I_N(b 𝟙_{[0,N]})`. (On `{τ_n = N}` they are those of the bounded
integrand `b 𝟙_{[0,τ_n]}`, which converge in `L²` to
`I_N(b 𝟙_{[0,τ_n]}) = I_{τ_n}(b 𝟙_{[0,N]})`.) -/
private lemma waveIto_tendstoInMeasure_riemann [DecidableEq ι] (hB : IsBrownianFamily 𝓖 W ν)
    (S : Finset ι) {b : ι → ℝ → Ω → ℝ} {N : ℝ≥0}
    (hbS : ∀ i ∉ S, ∀ s ω, b i s ω = 0)
    (hba : ∀ i (t : ℝ≥0), Measurable[𝓖 t] (b i t))
    (hbc : ∀ i ω, Continuous fun t : ℝ≥0 => b i t ω)
    (hint : IsItoIntegrable 𝓖 ν (fun i (s : ℝ) ω => if s ≤ (N : ℝ) then b i s ω else 0))
    {τ : ℕ → Ω → ℝ≥0} (hτ : ∀ n, IsStoppingTime 𝓖 (fun ω => (τ n ω : WithTop ℝ≥0)))
    (hτN : ∀ n ω, τ n ω ≤ N) {K : ℕ → ℝ}
    (hbd : ∀ n i ω (s : ℝ), 0 ≤ s → s ≤ τ n ω → |b i s ω| ≤ K n)
    (hlim : Tendsto (fun n => ν {ω | τ n ω ≠ N}) atTop (𝓝 0)) :
    TendstoInMeasure ν (fun m ω => ∑ i ∈ S, realRiemann (b i) (W i) N m ω) atTop
      (stochInt 𝓖 ν W (fun i (s : ℝ) ω => if s ≤ (N : ℝ) then b i s ω else 0) N) := by
  classical
  apply waveIto_tendstoInMeasure_of_localize
  intro δ hδ
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim δ hδ).exists
  set F : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ n ω then b i s ω else 0 with hFdef
  have hFb : ∀ i ∈ S, ∀ s : ℝ, 0 ≤ s → ∀ ω, |F i s ω| ≤ |K n| := by
    intro i _ s hs ω
    simp only [hFdef]
    split_ifs with h
    · exact (hbd n i ω s hs h).trans (le_abs_self _)
    · simp
  have hFa : ∀ i ∈ S, ∀ t : ℝ≥0, Measurable[𝓖 t] (F i t) := by
    intro i _ t
    have hset : MeasurableSet[𝓖 t] {ω | ((t : ℝ≥0) : ℝ) ≤ τ n ω} := by
      have : {ω | ((t : ℝ≥0) : ℝ) ≤ τ n ω} = {ω | (τ n ω : WithTop ℝ≥0) < t}ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, NNReal.coe_le_coe]
        exact ⟨fun h => not_lt.2 (WithTop.coe_le_coe.2 h),
          fun h => WithTop.coe_le_coe.1 (not_lt.1 h)⟩
      rw [this]
      exact ((hτ n).measurableSet_lt t).compl
    exact Measurable.ite hset (hba i t) measurable_const
  have hFlc : ∀ i ∈ S, ∀ ω (s : ℝ), 0 < s →
      ContinuousWithinAt (fun r => F i r ω) (Set.Iic s) s := by
    intro i _ ω s hs
    by_cases hsτ : s ≤ τ n ω
    · refine (waveIto_continuousAt (f := fun r => b i r ω) (hbc i ω)
        hs).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≤ s)
        simp [hFdef, hr.trans hsτ]
      · simp [hFdef, hsτ]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [(eventually_gt_nhds (not_le.1 hsτ)).filter_mono nhdsWithin_le_nhds]
          with r hr
        simp [hFdef, not_le.2 hr]
      · simp [hFdef, hsτ]
  have hL := tendsto_riemann_stochInt_finset hB S hFb hFa hFlc N
  have hFS : (fun j s ω => if j ∈ S then F j s ω else 0) =
      fun j (s : ℝ) ω => if s ≤ τ n ω then (if s ≤ (N : ℝ) then b j s ω else 0) else 0 := by
    funext j s ω
    by_cases hj : j ∈ S
    · by_cases hs : s ≤ τ n ω
      · have hsN : s ≤ (N : ℝ) := hs.trans (NNReal.coe_le_coe.2 (hτN n ω))
        simp [hFdef, hj, hs, hsN]
      · simp [hFdef, hj, hs]
    · simp [hj, hbS j hj]
  rw [hFS] at hL
  refine ⟨fun m ω => ∑ i ∈ S, realRiemann (F i) (W i) N m ω, _, {ω | τ n ω = N},
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL.2, ?_, ?_⟩
  · exact hn
  · filter_upwards [stochInt_indicator_stoppingTime hB hint (hτ n)] with ω hω hA
    refine ⟨fun m => Finset.sum_congr rfl fun i _ => ?_, ?_⟩
    · simp only [realRiemann]
      refine Finset.sum_congr rfl fun k hk => ?_
      have : (k : ℝ) * N / m ≤ τ n ω := by rw [hA]; exact waveIto_grid_le N.2 hk
      simp [hFdef, this]
    · rw [hω N, hA, min_self]

end Localize

/-! ### The wave equation: localization at `τ_{n+1} ∧ N` -/

section WaveLocal

variable {𝓖 : Filtration ℝ≥0 mΩ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- For a process with continuous `ℓ²` paths, `τ_{n+1} ∧ N = N` for all `n` large enough
(`‖ψ‖` is bounded on `[0, N]`), so `μ(τ_{n+1} ∧ N ≠ N) → 0`. -/
private lemma waveIto_tendsto_measure_waveStop [IsFiniteMeasure μ]
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) (N : ℝ≥0) :
    Tendsto (fun n : ℕ => μ {ω | waveStop ψ ((n : ℝ) + 1) N ω ≠ N}) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | waveStop ψ ((n : ℝ) + 1) N ω ≠ N} := by
    intro n
    have hlt := (isStoppingTime_waveStop_of_continuous hadapt hc ((n : ℝ) + 1) N).measurableSet_lt N
    have e : {ω | waveStop ψ ((n : ℝ) + 1) N ω ≠ N} =
        {ω | (waveStop ψ ((n : ℝ) + 1) N ω : WithTop ℝ≥0) < N} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_lt_coe]
      exact ⟨fun h => lt_of_le_of_ne (waveStop_le ψ _ N ω) h, fun h => h.ne⟩
    rw [e]
    exact 𝓖.le N _ hlt
  have h := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure (A := (∅ : Set Ω)) atTop μ hmeas
    (fun ω => ?_)
  · simpa using h
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := N)).exists_bound_of_continuousOn
    ((hc ω).norm.continuousOn)
  obtain ⟨n0, hn0⟩ := exists_nat_ge M
  filter_upwards [eventually_ge_atTop n0] with n hn
  simp only [Set.mem_empty_iff_false, iff_false, not_not]
  refine hitTime_eq_of_forall_lt fun t ht => ?_
  have h1 := hM t ⟨zero_le, ht.le⟩
  rw [Real.norm_eq_abs, abs_norm] at h1
  have h2 : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  show ‖ψ t ω‖ < (n : ℝ) + 1
  linarith

/-- `|Re z / √2| ≤ ‖z‖` and `|Im z / √2| ≤ ‖z‖`. -/
private lemma waveIto_abs_div_sqrt_le (z : ℂ) :
    |z.re / Real.sqrt 2| ≤ ‖z‖ ∧ |z.im / Real.sqrt 2| ≤ ‖z‖ := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  simp only [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2)]
  exact ⟨(div_le_self (abs_nonneg _) h2).trans (Complex.abs_re_le_norm z),
    (div_le_self (abs_nonneg _) h2).trans (Complex.abs_im_le_norm z)⟩

/-- `|waveDiffRe ψ x i s ω| ≤ ‖ψ_s‖` and `|waveDiffIm ψ x i s ω| ≤ ‖ψ_s‖`. -/
private lemma waveIto_abs_waveDiff_le (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ)
    (ω : Ω) : |waveDiffRe ψ x i s ω| ≤ ‖ψ s ω‖ ∧ |waveDiffIm ψ x i s ω| ≤ ‖ψ s ω‖ := by
  have hb : ∀ y, ‖ψ s ω y‖ ≤ ‖ψ s ω‖ := fun y => lp.norm_apply_le_norm two_ne_zero _ y
  have h := fun y => waveIto_abs_div_sqrt_le (ψ s ω y)
  constructor
  · unfold waveDiffRe
    split_ifs
    · rw [neg_div, abs_neg]; exact (h _).2.trans (hb _)
    · rw [neg_div, abs_neg]; exact (h _).1.trans (hb _)
    · rw [neg_div, abs_neg]; exact (h _).2.trans (hb _)
    · exact (h _).1.trans (hb _)
    · rw [abs_zero]; exact norm_nonneg _
  · unfold waveDiffIm
    split_ifs
    · exact (h _).1.trans (hb _)
    · rw [neg_div, abs_neg]; exact (h _).2.trans (hb _)
    · exact (h _).1.trans (hb _)
    · exact (h _).2.trans (hb _)
    · rw [abs_zero]; exact norm_nonneg _

/-- Before `τ_{n+1} ∧ N`, `‖ψ_s‖ ≤ n + 1`, if `‖ψ_0‖ ≤ 1` and the paths are continuous. -/
private lemma waveIto_norm_le_of_le_waveStop (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω)
    (h0 : ∀ ω, ‖ψ 0 ω‖ ≤ 1) {n : ℕ} {N : ℝ≥0} {ω : Ω} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ waveStop ψ ((n : ℝ) + 1) N ω) : ‖ψ s ω‖ ≤ (n : ℝ) + 1 := by
  have hle : s.toNNReal ≤ waveStop ψ ((n : ℝ) + 1) N ω := Real.toNNReal_le_iff_le_coe.2 hs
  have h1 : ‖ψ ((0 : ℝ≥0) : ℝ) ω‖ ≤ (n : ℝ) + 1 := by
    rw [NNReal.coe_zero]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [h0 ω]
  have := le_of_le_hitTime (X := fun t ω => ‖ψ t ω‖) (hc ω).norm h1 hle
  rwa [Real.coe_toNNReal _ hs0] at this

/-- **Riemann sums of an Itô solution.** If `X` is an Itô process up to the deterministic time
`N` with coefficients `b` (one of `waveDiffRe ψ x`, `waveDiffIm ψ x` for a process `ψ` with
continuous adapted `ℓ²` paths and `‖ψ_0‖ ≤ 1`), the Riemann sums `∑_{i} R(bᵢ, Bᵢ)` on `[0, N]`
converge in measure to `X_N - X_0 - ∫_0^N a` (localization at `τ_{n+1} ∧ N`). -/
private lemma waveIto_tendstoInMeasure_of_itoProcess [IsProbabilityMeasure μ]
    (hB : IsBrownianFamily 𝓖 B μ)
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω) (h0 : ∀ ω, ‖ψ 0 ω‖ ≤ 1) (x : ℤ)
    {b : ℤ × Fin 2 → ℝ → Ω → ℝ} (hbS : ∀ i ∉ waveSites x, ∀ s ω, b i s ω = 0)
    (hba : ∀ i (t : ℝ≥0), Measurable[𝓖 t] (b i t))
    (hbc : ∀ i ω, Continuous fun t : ℝ≥0 => b i t ω)
    (hbd : ∀ i s ω, |b i s ω| ≤ ‖ψ s ω‖) {X a : ℝ → Ω → ℝ} (N : ℝ≥0)
    (hX : IsItoProcessUpTo 𝓖 μ B (fun _ => N) X a b) :
    TendstoInMeasure μ (fun m ω => ∑ i ∈ waveSites x, realRiemann (b i) (B i) N m ω) atTop
      (fun ω => X N ω - X 0 ω - ∫ s in (0 : ℝ)..N, a s ω) := by
  classical
  have hconv := waveIto_tendstoInMeasure_riemann hB (waveSites x) hbS hba hbc hX.integrable
    (τ := fun n => waveStop ψ ((n : ℝ) + 1) N)
    (fun n => isStoppingTime_waveStop_of_continuous hadapt hc _ N)
    (fun n ω => waveStop_le ψ _ N ω) (K := fun n => (n : ℝ) + 1)
    (fun n i ω s hs0 hs => (hbd i s ω).trans (waveIto_norm_le_of_le_waveStop hc h0 hs0 hs))
    (waveIto_tendsto_measure_waveStop hadapt hc N)
  refine hconv.congr (fun m => ae_of_all _ fun ω => rfl) ?_
  filter_upwards [hX.eq] with ω hω
  have := hω N
  simp only [min_self] at this
  linarith

end WaveLocal

/-- **An Itô solution started from `e₀` is a wave function** (every `L`): the left-point
Riemann sums of the frozen definition converge in measure to the Itô integrals
(`tendsto_riemann_stochInt`, Stage 2), which identifies the field `sde` of `IsWaveFunction`. -/
theorem IsWaveIto.isWaveFunction [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ∞} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsWaveIto L 𝓖 B waveInit ψ μ) : IsWaveFunction L 𝓖 B ψ μ := by
  classical
  have hψ0 : ∀ ω, ‖ψ 0 ω‖ ≤ 1 := fun ω => by rw [h.init ω, norm_waveInit]
  have hca : ∀ ω y, Continuous fun t : ℝ≥0 => ψ t ω y := fun ω y =>
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 y).continuous.comp (h.continuous ω)
  have hma : ∀ (t : ℝ≥0) (y : ℤ), Measurable[𝓖 t] fun ω => ψ t ω y := h.adapted
  -- adaptedness and continuity of the coefficients
  have hRa : ∀ y i (t : ℝ≥0), Measurable[𝓖 t] (waveDiffRe ψ y i t) := by
    intro y i t
    unfold waveDiffRe
    split_ifs
    · exact (Complex.measurable_im.comp (hma t _)).neg.div_const _
    · exact (Complex.measurable_re.comp (hma t _)).neg.div_const _
    · exact (Complex.measurable_im.comp (hma t _)).neg.div_const _
    · exact (Complex.measurable_re.comp (hma t _)).div_const _
    · exact measurable_const
  have hIa : ∀ y i (t : ℝ≥0), Measurable[𝓖 t] (waveDiffIm ψ y i t) := by
    intro y i t
    unfold waveDiffIm
    split_ifs
    · exact (Complex.measurable_re.comp (hma t _)).div_const _
    · exact (Complex.measurable_im.comp (hma t _)).neg.div_const _
    · exact (Complex.measurable_re.comp (hma t _)).div_const _
    · exact (Complex.measurable_im.comp (hma t _)).div_const _
    · exact measurable_const
  have hRc : ∀ y i ω, Continuous fun t : ℝ≥0 => waveDiffRe ψ y i t ω := by
    intro y i ω
    simp only [waveDiffRe]
    split_ifs
    · exact (Complex.continuous_im.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_re.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_im.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_re.comp (hca ω _)).div_const _
    · exact continuous_const
  have hIc : ∀ y i ω, Continuous fun t : ℝ≥0 => waveDiffIm ψ y i t ω := by
    intro y i ω
    simp only [waveDiffIm]
    split_ifs
    · exact (Complex.continuous_re.comp (hca ω _)).div_const _
    · exact (Complex.continuous_im.comp (hca ω _)).neg.div_const _
    · exact (Complex.continuous_re.comp (hca ω _)).div_const _
    · exact (Complex.continuous_im.comp (hca ω _)).div_const _
    · exact continuous_const
  refine ⟨h.adapted, ae_of_all _ h.continuous, ae_of_all _ fun ω => h.support ω,
    fun t x hx => ?_⟩
  -- the time integral commutes with `Re`, `Im`
  have hii : ∀ ω, IntervalIntegrable (fun s => ψ s ω x) volume 0 t := fun ω => by
    have hcr : Continuous fun r : ℝ => ψ (r.toNNReal : ℝ) ω x :=
      (hca ω x).comp continuous_real_toNNReal
    refine (hcr.continuousOn (s := Set.uIcc 0 (t : ℝ))).congr (fun r hr => ?_)
      |>.intervalIntegrable
    rw [Set.uIcc_of_le (NNReal.coe_nonneg _)] at hr
    simp [Real.coe_toNNReal _ hr.1]
  have hD : ∀ z : ℂ, (degree L x : ℂ) / 2 * z = (((degree L x : ℝ) / 2 : ℝ) : ℂ) * z := by
    intro z; push_cast; ring
  rw [tendstoInMeasure_complex_iff]
  constructor
  · have hc := waveIto_tendstoInMeasure_of_itoProcess hB hma h.continuous hψ0 x
      (fun i hi s ω => waveDiffRe_of_notMem ψ hi s ω) (hRa x) (hRc x)
      (fun i s ω => (waveIto_abs_waveDiff_le ψ x i s ω).1) t (h.re x hx t)
    refine hc.congr (fun m => ae_of_all _ fun ω => sum_realRiemann_waveDiffRe ψ B x t m ω)
      (ae_of_all _ fun ω => ?_)
    have hre : (∫ s in (0 : ℝ)..t, (ψ s ω x).re) = (∫ s in (0 : ℝ)..t, ψ s ω x).re :=
      Complex.reCLM.intervalIntegral_comp_comm (hii ω)
    simp only [intervalIntegral.integral_const_mul, hre, hD, Complex.re_ofReal_mul,
      Complex.add_re, Complex.sub_re, h.init ω, waveInit_apply]
    split_ifs <;> simp
  · have hc := waveIto_tendstoInMeasure_of_itoProcess hB hma h.continuous hψ0 x
      (fun i hi s ω => waveDiffIm_of_notMem ψ hi s ω) (hIa x) (hIc x)
      (fun i s ω => (waveIto_abs_waveDiff_le ψ x i s ω).2) t (h.im x hx t)
    refine hc.congr (fun m => ae_of_all _ fun ω => sum_realRiemann_waveDiffIm ψ B x t m ω)
      (ae_of_all _ fun ω => ?_)
    have him : (∫ s in (0 : ℝ)..t, (ψ s ω x).im) = (∫ s in (0 : ℝ)..t, ψ s ω x).im :=
      Complex.imCLM.intervalIntegral_comp_comm (hii ω)
    simp only [intervalIntegral.integral_const_mul, him, hD, Complex.im_ofReal_mul,
      Complex.add_im, Complex.sub_im, h.init ω, waveInit_apply]
    split_ifs <;> simp

end QSSEPtoKPZ
