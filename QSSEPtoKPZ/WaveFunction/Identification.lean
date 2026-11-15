/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.Good
public import QSSEPtoKPZ.ItoIntegral.Product
public import QSSEPtoKPZ.ItoIntegral.Complex

/-!
# The wave function as an Itô process up to `τ_R ∧ N` (package D, task D1)

See `docs/stage2-design.md`, Section 1.2 (e). Write `ψ̃(y) = u_y + i v_y` for a good version
`ψ̃` of the wave function on `ℤ` (`IsGoodWave`), and `τ = τ_R ∧ N = waveStop ψ̃ R N`. Then, for
every `x ∈ ℤ`, `u_x` and `v_x` are Itô processes up to `τ` (`IsItoProcessUpTo`) against the
family `B = (B_{y,j})_{(y,j) ∈ ℤ × {0,1}}`:

`du_x = -u_x dt + (1/√2)(-v_{x+1} dB_{x,0} - u_{x+1} dB_{x,1} - v_{x-1} dB_{x-1,0} + u_{x-1} dB_{x-1,1})`,
`dv_x = -v_x dt + (1/√2)( u_{x+1} dB_{x,0} - v_{x+1} dB_{x,1} + u_{x-1} dB_{x-1,0} + v_{x-1} dB_{x-1,1})`.

These are the real and imaginary parts of the equation (2.1) of the article,
`dψ(x) = -ψ(x) dt + i ψ(x+1) dW⁽ˣ⁾ + i ψ(x-1) dW̄⁽ˣ⁻¹⁾` with `W⁽ˣ⁾ = (B_{x,0} + i B_{x,1})/√2`
(the drift `-½ D(x,x) ψ(x) = -ψ(x)`, since `D(x,x) = 2` on `ℤ`); the coefficients are those of
the design and agree with `itoSum_sde_eq_realRiemann`.

* `isItoProcessUpTo_of_riemann`: a general criterion. If the coefficients `b_i` (finitely many
  nonzero) are bounded before `τ`, adapted and continuous, and the left-point Riemann sums
  `∑ᵢ R(bᵢ, Bᵢ)` converge in measure, at every fixed `t`, to `X_t - X_0 - ∫_0^t a`, then `X` is an
  Itô process up to `τ` with drift `a` and diffusion `b`. (Proof: on `{t ≤ τ}` these Riemann sums
  are those of the bounded left-continuous integrand `b 𝟙_{[0,τ]}`, which converge in `L²` to
  `I_t(b 𝟙_{[0,τ]})`; limits in measure are unique; a countable dense set of times and continuity
  give the identity for all `t ≤ τ`; stopping gives it at `t ∧ τ`.)
* `waveDiffRe`, `waveDiffIm`, `waveSites`: the diffusion coefficients above, supported by the four
  indices `(x,0), (x,1), (x-1,0), (x-1,1)`; `tsum_waveDiffRe_sq`, `tsum_waveDiffIm_sq`:
  `∑ᵢ (bᵢ)² = (|ψ(x+1)|² + |ψ(x-1)|²)/2` for both.
* `IsGoodWave.isItoProcessUpTo_re`, `IsGoodWave.isItoProcessUpTo_im`: the identification.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### A general criterion -/

section Generic

/-- A function continuous on `[0, ∞)` (as a function of `t : ℝ≥0`) is continuous at every
`s > 0`. -/
private lemma ident_continuousAt {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) {s : ℝ} (hs : 0 < s) : ContinuousAt f s := by
  have h1 : ContinuousAt (fun r : ℝ => f (r.toNNReal : ℝ)) s :=
    (hf.comp continuous_real_toNNReal).continuousAt
  refine h1.congr ?_
  filter_upwards [eventually_gt_nhds hs] with r hr
  simp [Real.coe_toNNReal _ hr.le]

/-- A function continuous on `[0, ∞)` (as a function of `t : ℝ≥0`) is continuous on `Ici 0`. -/
private lemma ident_continuousOn {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous fun t : ℝ≥0 => f t) : ContinuousOn f (Set.Ici 0) :=
  (hf.comp continuous_real_toNNReal).continuousOn.congr fun r hr => by
    simp [Real.coe_toNNReal _ (Set.mem_Ici.1 hr)]

/-- If `f` is continuous on `[0, ∞)`, so is `s ↦ ∫_0^s f`. -/
private lemma ident_continuous_primitive {f : ℝ → ℝ} (hf : Continuous fun t : ℝ≥0 => f t) :
    Continuous fun s : ℝ≥0 => ∫ r in (0 : ℝ)..(s : ℝ), f r := by
  have hc : Continuous fun r : ℝ => f (r.toNNReal : ℝ) := hf.comp continuous_real_toNNReal
  have h1 := (intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hc.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr0 : 0 ≤ r := by
    rcases Set.mem_uIcc.1 hr with h | h
    · exact h.1
    · exact s.2.trans h.1
  simp [Real.coe_toNNReal _ hr0]

/-- Convergence in measure is preserved by multiplication by the indicator of a set. -/
private lemma ident_indicator {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (A : Set Ω)
    (h : TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ (fun m => A.indicator (f m)) atTop (A.indicator g) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) fun m => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_cases hA : ω ∈ A
  · simpa [Set.indicator_of_mem hA] using hω
  · simp only [Set.indicator_of_notMem hA, edist_self] at hω
    exact absurd hω (not_le.2 hε)

/-- The grid points `k t / m`, `k < m`, of the Riemann sums lie in `[0, t]`. -/
private lemma ident_grid_le {t : ℝ} (ht : 0 ≤ t) {m k : ℕ} (hk : k ∈ Finset.range m) :
    (k : ℝ) * t / m ≤ t := by
  have hkm : k < m := Finset.mem_range.1 hk
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le k).trans_lt hkm
  rw [div_le_iff₀ hm]
  have : (k : ℝ) ≤ m := by exact_mod_cast hkm.le
  nlinarith

variable {ι : Type*} [Countable ι] {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-- **Identification of an Itô process from Riemann sums.** Let `τ` be a stopping time of `𝓖`,
`S` a finite set of indices, and `b` a family of real processes vanishing outside `S`, adapted,
with all paths continuous on `[0, ∞)` and bounded by `K` on `[0, τ]`. Let `X`, `a` have all paths
continuous on `[0, ∞)`. If, for every `t ≥ 0`, the left-point Riemann sums
`∑_{i ∈ S} ∑_{k < m} bᵢ(t_k)(Bᵢ(t_{k+1}) - Bᵢ(t_k))` converge in measure to
`X_t - X_0 - ∫_0^t a(s) ds` as `m → ∞`, then `X` is an Itô process up to `τ`:
`X_{t∧τ} = X_0 + ∫_0^{t∧τ} a(s) ds + ∑ᵢ ∫_0^t bᵢ(s) 𝟙_{s ≤ τ} dBᵢ(s)` for all `t`, a.s. -/
theorem isItoProcessUpTo_of_riemann (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) (S : Finset ι)
    {X a : ℝ → Ω → ℝ} {b : ι → ℝ → Ω → ℝ} {K : ℝ}
    (hbS : ∀ i ∉ S, ∀ s ω, b i s ω = 0)
    (hbK : ∀ i ω (s : ℝ), 0 ≤ s → s ≤ τ ω → |b i s ω| ≤ K)
    (hba : ∀ i (t : ℝ≥0), Measurable[𝓖 t] (b i t))
    (hbc : ∀ i ω, Continuous fun t : ℝ≥0 => b i t ω)
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω)
    (hac : ∀ ω, Continuous fun t : ℝ≥0 => a t ω)
    (hsde : ∀ t : ℝ≥0, TendstoInMeasure μ
      (fun m ω => ∑ i ∈ S, realRiemann (b i) (B i) t m ω) atTop
      (fun ω => X t ω - X 0 ω - ∫ s in (0 : ℝ)..t, a s ω)) :
    IsItoProcessUpTo 𝓖 μ B τ X a b := by
  classical
  set F : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ ω then b i s ω else 0 with hFdef
  -- the integrand `F = b 𝟙_{[0,τ]}` is bounded, adapted and left-continuous
  have hFb : ∀ i ∈ S, ∀ s : ℝ, 0 ≤ s → ∀ ω, |F i s ω| ≤ |K| := by
    intro i _ s hs ω
    simp only [hFdef]
    split_ifs with h
    · exact (hbK i ω s hs h).trans (le_abs_self K)
    · simp
  have hFa : ∀ i ∈ S, ∀ t : ℝ≥0, Measurable[𝓖 t] (F i t) := by
    intro i _ t
    have hset : MeasurableSet[𝓖 t] {ω | ((t : ℝ≥0) : ℝ) ≤ τ ω} := by
      have : {ω | ((t : ℝ≥0) : ℝ) ≤ τ ω} = {ω | (τ ω : WithTop ℝ≥0) < t}ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, NNReal.coe_le_coe]
        exact ⟨fun h => not_lt.2 (WithTop.coe_le_coe.2 h),
          fun h => WithTop.coe_le_coe.1 (not_lt.1 h)⟩
      rw [this]
      exact (hτ.measurableSet_lt t).compl
    exact Measurable.ite hset (hba i t) measurable_const
  have hFlc : ∀ i ∈ S, ∀ ω (s : ℝ), 0 < s →
      ContinuousWithinAt (fun r => F i r ω) (Set.Iic s) s := by
    intro i _ ω s hs
    by_cases hsτ : s ≤ τ ω
    · refine (ident_continuousAt (f := fun r => b i r ω) (hbc i ω) hs).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≤ s)
        simp [hFdef, hr.trans hsτ]
      · simp [hFdef, hsτ]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [(eventually_gt_nhds (not_le.1 hsτ)).filter_mono nhdsWithin_le_nhds]
          with r hr
        simp [hFdef, not_le.2 hr]
      · simp [hFdef, hsτ]
  have hFS : (fun j s ω => if j ∈ S then F j s ω else 0) = F := by
    funext j s ω
    split_ifs with hj
    · rfl
    · simp [hFdef, hbS j hj]
  have hint : IsItoIntegrable 𝓖 μ F := by
    have := (tendsto_riemann_stochInt_finset hB S hFb hFa hFlc 0).1
    rwa [hFS] at this
  -- fixed times: `X_t - X_0 - ∫_0^t a = I_t(F)` a.s. on `{t ≤ τ}`
  have hfix : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, ((t : ℝ) ≤ τ ω) →
      X t ω - X 0 ω - (∫ s in (0 : ℝ)..t, a s ω) = stochInt 𝓖 μ B F t ω := by
    intro t
    have hL := (tendsto_riemann_stochInt_finset hB S hFb hFa hFlc t).2
    rw [hFS] at hL
    have hρ : TendstoInMeasure μ (fun m ω => ∑ i ∈ S, realRiemann (F i) (B i) t m ω) atTop
        (stochInt 𝓖 μ B F t) := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL
    set A : Set Ω := {ω | (t : ℝ) ≤ τ ω} with hA
    have h1 := ident_indicator A hρ
    have h2 := ident_indicator A (hsde t)
    have heq : (fun m => A.indicator fun ω => ∑ i ∈ S, realRiemann (F i) (B i) t m ω) =
        fun m => A.indicator fun ω => ∑ i ∈ S, realRiemann (b i) (B i) t m ω := by
      funext m ω
      by_cases hω : ω ∈ A
      · simp only [Set.indicator_of_mem hω]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [realRiemann]
        refine Finset.sum_congr rfl fun k hk => ?_
        have : (k : ℝ) * t / m ≤ τ ω := (ident_grid_le t.2 hk).trans hω
        simp [hFdef, this]
      · simp [Set.indicator_of_notMem hω]
    rw [heq] at h1
    filter_upwards [tendstoInMeasure_ae_unique h1 h2] with ω hω hAω
    simp only [Set.indicator_of_mem (show ω ∈ A from hAω)] at hω
    exact hω.symm
  -- all times `s ≤ τ`, by density and continuity
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD : ∀ᵐ ω ∂μ, ∀ t ∈ D, ((t : ℝ) ≤ τ ω) →
      X t ω - X 0 ω - (∫ s in (0 : ℝ)..t, a s ω) = stochInt 𝓖 μ B F t ω :=
    (ae_ball_iff hDc).2 fun t _ => hfix t
  have hall : ∀ᵐ ω ∂μ, ∀ s : ℝ≥0, s ≤ τ ω →
      X s ω - X 0 ω - (∫ r in (0 : ℝ)..s, a r ω) = stochInt 𝓖 μ B F s ω := by
    filter_upwards [hD, stochInt_continuous hB hint] with ω hDω hIω
    set g : ℝ≥0 → ℝ := fun s =>
      X s ω - X 0 ω - (∫ r in (0 : ℝ)..s, a r ω) - stochInt 𝓖 μ B F s ω with hg
    have hgc : Continuous g :=
      (((hXc ω).sub continuous_const).sub (ident_continuous_primitive (hac ω))).sub hIω
    have hcl : IsClosed {s | g s = 0} := isClosed_eq hgc continuous_const
    intro s hs
    suffices g s = 0 by simp only [hg] at this; linarith
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ τ ω) with h0 | hpos
    · have : s = 0 := le_antisymm (h0 ▸ hs) zero_le
      subst this
      simp [hg, stochInt_of_nonpos B F (le_refl (0 : ℝ))]
    · have hsub : Set.Iio (τ ω) ∩ D ⊆ {s | g s = 0} := fun r ⟨hr, hrD⟩ => by
        have := hDω r hrD (NNReal.coe_le_coe.2 hr.le)
        simp only [hg, Set.mem_ofPred_eq]
        linarith
      have hIic : Set.Iic (τ ω) ⊆ closure (Set.Iio (τ ω) ∩ D) := by
        rw [← closure_Iio' (a := τ ω) ⟨0, hpos⟩]
        exact closure_minimal (hDd.open_subset_closure_inter isOpen_Iio) isClosed_closure
      exact closure_minimal hsub hcl (hIic hs)
  -- stopping: `I_t(F) = I_{t∧τ}(F)`
  have hstop := stochInt_indicator_stoppingTime hB hint hτ
  have hFF : (fun i (s : ℝ) ω => if s ≤ τ ω then F i s ω else 0) = F := by
    funext i s ω
    simp only [hFdef]
    split_ifs <;> rfl
  rw [hFF] at hstop
  refine ⟨hint, ae_of_all _ fun ω => ?_, ?_⟩
  · refine ContinuousOn.intervalIntegrable ((ident_continuousOn (hac ω)).mono ?_)
    rw [Set.uIcc_of_le (NNReal.coe_nonneg _)]
    exact Set.Icc_subset_Ici_self
  · filter_upwards [hall, hstop] with ω h1 h2 t
    have := h1 (min t (τ ω)) (min_le_right _ _)
    rw [h2 t]
    linarith

end Generic

/-! ### The coefficients of the equation of the wave function -/

/-- The four indices `(x,0), (x,1), (x-1,0), (x-1,1)` of the Brownian motions driving `ψ(x)`
(those of the bonds `(x, x+1)` and `(x-1, x)`). -/
def waveSites (x : ℤ) : Finset (ℤ × Fin 2) := {(x, 0), (x, 1), (x - 1, 0), (x - 1, 1)}

/-- The diffusion coefficients of `u_x = Re ψ(x)`:
`du_x = … + (1/√2)(-v_{x+1} dB_{x,0} - u_{x+1} dB_{x,1} - v_{x-1} dB_{x-1,0} + u_{x-1} dB_{x-1,1})`,
where `ψ(y) = u_y + i v_y`. -/
def waveDiffRe (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) : ℝ :=
  if i = (x, 0) then -(ψ s ω (x + 1)).im / Real.sqrt 2
  else if i = (x, 1) then -(ψ s ω (x + 1)).re / Real.sqrt 2
  else if i = (x - 1, 0) then -(ψ s ω (x - 1)).im / Real.sqrt 2
  else if i = (x - 1, 1) then (ψ s ω (x - 1)).re / Real.sqrt 2
  else 0

/-- The diffusion coefficients of `v_x = Im ψ(x)`:
`dv_x = … + (1/√2)(u_{x+1} dB_{x,0} - v_{x+1} dB_{x,1} + u_{x-1} dB_{x-1,0} + v_{x-1} dB_{x-1,1})`,
where `ψ(y) = u_y + i v_y`. -/
def waveDiffIm (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) : ℝ :=
  if i = (x, 0) then (ψ s ω (x + 1)).re / Real.sqrt 2
  else if i = (x, 1) then -(ψ s ω (x + 1)).im / Real.sqrt 2
  else if i = (x - 1, 0) then (ψ s ω (x - 1)).re / Real.sqrt 2
  else if i = (x - 1, 1) then (ψ s ω (x - 1)).im / Real.sqrt 2
  else 0

/-- Membership in `waveSites x`. -/
lemma mem_waveSites {x : ℤ} {i : ℤ × Fin 2} :
    i ∈ waveSites x ↔ i = (x, 0) ∨ i = (x, 1) ∨ i = (x - 1, 0) ∨ i = (x - 1, 1) := by
  simp [waveSites]

/-- The coefficients of `Re ψ(x)` vanish outside `waveSites x`. -/
lemma waveDiffRe_of_notMem (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x : ℤ} {i : ℤ × Fin 2}
    (hi : i ∉ waveSites x) (s : ℝ) (ω : Ω) : waveDiffRe ψ x i s ω = 0 := by
  simp only [mem_waveSites, not_or] at hi
  simp [waveDiffRe, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

/-- The coefficients of `Im ψ(x)` vanish outside `waveSites x`. -/
lemma waveDiffIm_of_notMem (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) {x : ℤ} {i : ℤ × Fin 2}
    (hi : i ∉ waveSites x) (s : ℝ) (ω : Ω) : waveDiffIm ψ x i s ω = 0 := by
  simp only [mem_waveSites, not_or] at hi
  simp [waveDiffIm, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

/-- Sums over `waveSites x`, written out. -/
lemma sum_waveSites {M : Type*} [AddCommMonoid M] (x : ℤ) (f : ℤ × Fin 2 → M) :
    ∑ i ∈ waveSites x, f i = f (x, 0) + f (x, 1) + f (x - 1, 0) + f (x - 1, 1) := by
  have h1 : x ≠ x - 1 := by omega
  rw [waveSites, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · simp only [add_assoc]
  all_goals simp [h1]

/-- `∑ᵢ (waveDiffRe)ᵢ gᵢ` is a finite sum over `waveSites x`. -/
lemma tsum_waveDiffRe_mul (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (g : ℤ × Fin 2 → ℝ) (s : ℝ) (ω : Ω) :
    ∑' i, waveDiffRe ψ x i s ω * g i = ∑ i ∈ waveSites x, waveDiffRe ψ x i s ω * g i :=
  tsum_eq_sum fun i hi => by rw [waveDiffRe_of_notMem ψ hi, zero_mul]

/-- `∑ᵢ (waveDiffIm)ᵢ gᵢ` is a finite sum over `waveSites x`. -/
lemma tsum_waveDiffIm_mul (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (g : ℤ × Fin 2 → ℝ) (s : ℝ) (ω : Ω) :
    ∑' i, waveDiffIm ψ x i s ω * g i = ∑ i ∈ waveSites x, waveDiffIm ψ x i s ω * g i :=
  tsum_eq_sum fun i hi => by rw [waveDiffIm_of_notMem ψ hi, zero_mul]

/-- The values of `waveDiffRe` on `waveSites x`. -/
private lemma waveDiffRe_vals (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) :
    waveDiffRe ψ x (x, 0) = (fun s ω => -(ψ s ω (x + 1)).im / Real.sqrt 2) ∧
    waveDiffRe ψ x (x, 1) = (fun s ω => -(ψ s ω (x + 1)).re / Real.sqrt 2) ∧
    waveDiffRe ψ x (x - 1, 0) = (fun s ω => -(ψ s ω (x - 1)).im / Real.sqrt 2) ∧
    waveDiffRe ψ x (x - 1, 1) = (fun s ω => (ψ s ω (x - 1)).re / Real.sqrt 2) := by
  have h1 : x - 1 ≠ x := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext s ω <;> simp [waveDiffRe, h1]

/-- The values of `waveDiffIm` on `waveSites x`. -/
private lemma waveDiffIm_vals (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) :
    waveDiffIm ψ x (x, 0) = (fun s ω => (ψ s ω (x + 1)).re / Real.sqrt 2) ∧
    waveDiffIm ψ x (x, 1) = (fun s ω => -(ψ s ω (x + 1)).im / Real.sqrt 2) ∧
    waveDiffIm ψ x (x - 1, 0) = (fun s ω => (ψ s ω (x - 1)).re / Real.sqrt 2) ∧
    waveDiffIm ψ x (x - 1, 1) = (fun s ω => (ψ s ω (x - 1)).im / Real.sqrt 2) := by
  have h1 : x - 1 ≠ x := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext s ω <;> simp [waveDiffIm, h1]

/-- `∑ᵢ (waveDiffRe)ᵢ² = (|ψ(x+1)|² + |ψ(x-1)|²)/2`. -/
lemma tsum_waveDiffRe_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, waveDiffRe ψ x i s ω ^ 2 = (‖ψ s ω (x + 1)‖ ^ 2 + ‖ψ s ω (x - 1)‖ ^ 2) / 2 := by
  have e := tsum_waveDiffRe_mul ψ x (fun i => waveDiffRe ψ x i s ω) s ω
  simp only [← sq] at e
  obtain ⟨h0, h1, h2, h3⟩ := waveDiffRe_vals ψ x
  rw [e, sum_waveSites, h0, h1, h2, h3]
  simp only [div_pow, neg_sq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- `∑ᵢ (waveDiffIm)ᵢ² = (|ψ(x+1)|² + |ψ(x-1)|²)/2`. -/
lemma tsum_waveDiffIm_sq (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (x : ℤ) (s : ℝ) (ω : Ω) :
    ∑' i, waveDiffIm ψ x i s ω ^ 2 = (‖ψ s ω (x + 1)‖ ^ 2 + ‖ψ s ω (x - 1)‖ ^ 2) / 2 := by
  have e := tsum_waveDiffIm_mul ψ x (fun i => waveDiffIm ψ x i s ω) s ω
  simp only [← sq] at e
  obtain ⟨h0, h1, h2, h3⟩ := waveDiffIm_vals ψ x
  rw [e, sum_waveSites, h0, h1, h2, h3]
  simp only [div_pow, neg_sq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- `realRiemann` is linear in the integrand: constant factors. -/
private lemma realRiemann_div_const (f W : ℝ → Ω → ℝ) (c : ℝ) (t : ℝ) (m : ℕ) (ω : Ω) :
    realRiemann (fun s ω => f s ω / c) W t m ω = realRiemann f W t m ω / c := by
  simp only [realRiemann, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `realRiemann` is linear in the integrand: sign. -/
private lemma realRiemann_neg (f W : ℝ → Ω → ℝ) (t : ℝ) (m : ℕ) (ω : Ω) :
    realRiemann (fun s ω => -f s ω) W t m ω = -realRiemann f W t m ω := by
  simp only [realRiemann, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The noise term of the frozen equation (field `sde` of `IsWaveFunction`), real part: it is the
sum of the real Riemann sums of the coefficients `waveDiffRe` against the `Bᵢ`. -/
lemma sum_realRiemann_waveDiffRe (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ)
    (t : ℝ) (m : ℕ) (ω : Ω) :
    ∑ i ∈ waveSites x, realRiemann (waveDiffRe ψ x i) (B i) t m ω =
      (Complex.I * itoSum (fun s ω => ψ s ω (x + 1)) (complexBM B x) t m ω +
        Complex.I * itoSum (fun s ω => ψ s ω (x - 1))
          (fun s ω => (starRingEnd ℂ) (complexBM B (x - 1) s ω)) t m ω).re := by
  obtain ⟨h0, h1, h2, h3⟩ := waveDiffRe_vals ψ x
  rw [itoSum_sde_eq_realRiemann, sum_waveSites, h0, h1, h2, h3]
  simp only [realRiemann_div_const, realRiemann_neg, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  ring

/-- The noise term of the frozen equation (field `sde` of `IsWaveFunction`), imaginary part: it is
the sum of the real Riemann sums of the coefficients `waveDiffIm` against the `Bᵢ`. -/
lemma sum_realRiemann_waveDiffIm (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ)
    (t : ℝ) (m : ℕ) (ω : Ω) :
    ∑ i ∈ waveSites x, realRiemann (waveDiffIm ψ x i) (B i) t m ω =
      (Complex.I * itoSum (fun s ω => ψ s ω (x + 1)) (complexBM B x) t m ω +
        Complex.I * itoSum (fun s ω => ψ s ω (x - 1))
          (fun s ω => (starRingEnd ℂ) (complexBM B (x - 1) s ω)) t m ω).im := by
  obtain ⟨h0, h1, h2, h3⟩ := waveDiffIm_vals ψ x
  rw [itoSum_sde_eq_realRiemann, sum_waveSites, h0, h1, h2, h3]
  simp only [realRiemann_div_const, realRiemann_neg, Complex.add_im, Complex.ofReal_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  ring

/-! ### Identification -/

variable {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

omit [IsProbabilityMeasure μ] in
/-- The limit in the frozen equation, for a good version: `∫_0^t ψ'(x)` commutes with `Re`, `Im`,
and `D(x,x)/2 = 1`. -/
private lemma ident_limit (hg : IsGoodWave 𝓕 B ψ ψ' μ) (t : ℝ≥0) (x : ℤ) (ω : Ω) :
    (ψ' t ω x - (if x = 0 then 1 else 0) +
        (degree ⊤ x : ℂ) / 2 * ∫ s in (0 : ℝ)..t, ψ' s ω x) =
      ((ψ' t ω x).re - (ψ' 0 ω x).re + ∫ s in (0 : ℝ)..t, (ψ' s ω x).re : ℝ) +
        Complex.I * ((ψ' t ω x).im - (ψ' 0 ω x).im + ∫ s in (0 : ℝ)..t, (ψ' s ω x).im : ℝ) := by
  have hii : IntervalIntegrable (fun s => ψ' s ω x) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ((ident_continuousOn (hg.continuous_apply ω x)).mono ?_)
    rw [Set.uIcc_of_le (NNReal.coe_nonneg _)]
    exact Set.Icc_subset_Ici_self
  have hre : (∫ s in (0 : ℝ)..t, (ψ' s ω x).re) = (∫ s in (0 : ℝ)..t, ψ' s ω x).re :=
    Complex.reCLM.intervalIntegral_comp_comm hii
  have him : (∫ s in (0 : ℝ)..t, (ψ' s ω x).im) = (∫ s in (0 : ℝ)..t, ψ' s ω x).im :=
    Complex.imCLM.intervalIntegral_comp_comm hii
  rw [hre, him, hg.init_apply ω x, waveDegree_top]
  apply Complex.ext <;> split_ifs <;> simp

/-- **Identification, real part.** Let `ψ'` be a good version of the wave function on `ℤ`
(`IsGoodWave`) and `τ = τ_R ∧ N` (`waveStop`). For every `x ∈ ℤ`, `u_x = Re ψ'(x)` is an Itô
process up to `τ` for `𝓕ᵃ`, with drift `-u_x` and diffusion coefficients `waveDiffRe ψ' x`:
`du_x = -u_x dt + (1/√2)(-v_{x+1} dB_{x,0} - u_{x+1} dB_{x,1} - v_{x-1} dB_{x-1,0} + u_{x-1} dB_{x-1,1})`.
-/
theorem IsGoodWave.isItoProcessUpTo_re (hB : IsBrownianFamily 𝓕 B μ)
    (hg : IsGoodWave 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (waveStop ψ' R N) (fun t ω => (ψ' t ω x).re)
      (fun s ω => -(ψ' s ω x).re) (waveDiffRe ψ' x) := by
  have hdiv : ∀ z : ℂ, |z.re / Real.sqrt 2| ≤ ‖z‖ ∧ |z.im / Real.sqrt 2| ≤ ‖z‖ := fun z => by
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
    simp only [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2)]
    exact ⟨(div_le_self (abs_nonneg _) h2).trans (Complex.abs_re_le_norm z),
      (div_le_self (abs_nonneg _) h2).trans (Complex.abs_im_le_norm z)⟩
  refine isItoProcessUpTo_of_riemann hB.nullAug (hg.isStoppingTime_waveStop R N) (waveSites x)
    (K := max R 1) (fun i hi s ω => waveDiffRe_of_notMem ψ' hi s ω) ?_ ?_ ?_
    (fun ω => hg.continuous_re ω x) (fun ω => (hg.continuous_re ω x).neg) fun t => ?_
  · intro i ω s hs0 hs
    have hb := fun y => hg.norm_apply_le_of_le_waveStop hs0 hs y
    simp only [waveDiffRe]
    split_ifs
    · rw [neg_div, abs_neg]; exact (hdiv _).2.trans (hb _)
    · rw [neg_div, abs_neg]; exact (hdiv _).1.trans (hb _)
    · rw [neg_div, abs_neg]; exact (hdiv _).2.trans (hb _)
    · exact (hdiv _).1.trans (hb _)
    · rw [abs_zero]; exact zero_le_one.trans (le_max_right _ _)
  · intro i t
    unfold waveDiffRe
    split_ifs
    · exact ((hg.measurable_im t _).neg).div_const _
    · exact ((hg.measurable_re t _).neg).div_const _
    · exact ((hg.measurable_im t _).neg).div_const _
    · exact (hg.measurable_re t _).div_const _
    · exact measurable_const
  · intro i ω
    simp only [waveDiffRe]
    split_ifs
    · exact ((hg.continuous_im ω _).neg).div_const _
    · exact ((hg.continuous_re ω _).neg).div_const _
    · exact ((hg.continuous_im ω _).neg).div_const _
    · exact (hg.continuous_re ω _).div_const _
    · exact continuous_const
  · have h := (tendstoInMeasure_complex_iff μ).1 (hg.wave.sde t x (waveBox_top_mem x)) |>.1
    refine h.congr (fun m => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (sum_realRiemann_waveDiffRe ψ' B x t m ω).symm
    · rw [ident_limit hg t x ω]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, intervalIntegral.integral_neg]
      ring

/-- **Identification, imaginary part.** Let `ψ'` be a good version of the wave function on `ℤ`
(`IsGoodWave`) and `τ = τ_R ∧ N` (`waveStop`). For every `x ∈ ℤ`, `v_x = Im ψ'(x)` is an Itô
process up to `τ` for `𝓕ᵃ`, with drift `-v_x` and diffusion coefficients `waveDiffIm ψ' x`:
`dv_x = -v_x dt + (1/√2)(u_{x+1} dB_{x,0} - v_{x+1} dB_{x,1} + u_{x-1} dB_{x-1,0} + v_{x-1} dB_{x-1,1})`.
-/
theorem IsGoodWave.isItoProcessUpTo_im (hB : IsBrownianFamily 𝓕 B μ)
    (hg : IsGoodWave 𝓕 B ψ ψ' μ) (R : ℝ) (N : ℝ≥0) (x : ℤ) :
    IsItoProcessUpTo (nullAug μ 𝓕) μ B (waveStop ψ' R N) (fun t ω => (ψ' t ω x).im)
      (fun s ω => -(ψ' s ω x).im) (waveDiffIm ψ' x) := by
  have hdiv : ∀ z : ℂ, |z.re / Real.sqrt 2| ≤ ‖z‖ ∧ |z.im / Real.sqrt 2| ≤ ‖z‖ := fun z => by
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
    simp only [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2)]
    exact ⟨(div_le_self (abs_nonneg _) h2).trans (Complex.abs_re_le_norm z),
      (div_le_self (abs_nonneg _) h2).trans (Complex.abs_im_le_norm z)⟩
  refine isItoProcessUpTo_of_riemann hB.nullAug (hg.isStoppingTime_waveStop R N) (waveSites x)
    (K := max R 1) (fun i hi s ω => waveDiffIm_of_notMem ψ' hi s ω) ?_ ?_ ?_
    (fun ω => hg.continuous_im ω x) (fun ω => (hg.continuous_im ω x).neg) fun t => ?_
  · intro i ω s hs0 hs
    have hb := fun y => hg.norm_apply_le_of_le_waveStop hs0 hs y
    simp only [waveDiffIm]
    split_ifs
    · exact (hdiv _).1.trans (hb _)
    · rw [neg_div, abs_neg]; exact (hdiv _).2.trans (hb _)
    · exact (hdiv _).1.trans (hb _)
    · exact (hdiv _).2.trans (hb _)
    · rw [abs_zero]; exact zero_le_one.trans (le_max_right _ _)
  · intro i t
    unfold waveDiffIm
    split_ifs
    · exact (hg.measurable_re t _).div_const _
    · exact ((hg.measurable_im t _).neg).div_const _
    · exact (hg.measurable_re t _).div_const _
    · exact (hg.measurable_im t _).div_const _
    · exact measurable_const
  · intro i ω
    simp only [waveDiffIm]
    split_ifs
    · exact (hg.continuous_re ω _).div_const _
    · exact ((hg.continuous_im ω _).neg).div_const _
    · exact (hg.continuous_re ω _).div_const _
    · exact (hg.continuous_im ω _).div_const _
    · exact continuous_const
  · have h := (tendstoInMeasure_complex_iff μ).1 (hg.wave.sde t x (waveBox_top_mem x)) |>.2
    refine h.congr (fun m => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (sum_realRiemann_waveDiffIm ψ' B x t m ω).symm
    · rw [ident_limit hg t x ω]
      simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, intervalIntegral.integral_neg]
      ring

end QSSEPtoKPZ
