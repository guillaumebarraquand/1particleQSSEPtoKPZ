/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.FourthMoment
public import QSSEPtoKPZ.ItoIntegral.Riemann
public import QSSEPtoKPZ.ItoIntegral.Stopping
public import QSSEPtoKPZ.ItoIntegral.ProductRiemann
public import QSSEPtoKPZ.ItoIntegral.ProductBracket

/-!
# Itô processes stopped at a stopping time; the product rule (package C, task C6)

INTERFACE FILE (task I0 of Stage 2): the definition below is complete; the theorems are frozen
interfaces, proved by task C6. See `docs/stage2-design.md`, Section 1.2 (d) and Section 2.2
(design decision C-4), and `docs/stage2-interfaces.md`.

* `IsItoProcessUpTo 𝓖 μ B τ X a b`: almost surely, for all `t ≥ 0`,
  `X_{t∧τ} = X_0 + ∫_0^{t∧τ} a(s) ds + I_t(b 𝟙_{[0,τ]})`, with `b 𝟙_{[0,τ]}` Itô-integrable and
  `a` integrable on `[0, τ]`.
* `IsItoProcessUpTo.mul`: the product rule
  `d(XY) = (X c + Y a + ∑ᵢ bᵢ dᵢ) dt + (X d + Y b) dB`, for processes bounded (with their
  coefficients) up to a bounded stopping time.
* Linear combinations, deterministic `C¹` functions of time, smaller stopping times.

Proof of the product rule (task C6): at a fixed time `t`, the discrete product rule on the grid
`t_k = k t / m` (`itoProd_telescope`) splits `X_{t∧τ} Y_{t∧τ} - X_0 Y_0` into drift Riemann sums
(pathwise limits, `ItoIntegral/ProductPathwise.lean`), Riemann sums against `I(b)`, `I(d)`
(`L²` limits, `ItoIntegral/ProductRiemann.lean`) and the quadratic covariation
`∑ ΔI(b) ΔI(d) → ∫ ∑ᵢ bᵢ dᵢ` (`L²` limit, `ItoIntegral/ProductBracket.lean`); an almost surely
convergent subsequence identifies the limit; continuity in `t` gives all times at once.

The only Itô formula of the project is the product rule (every quantity in Sections 2 to 6 of
the article is polynomial in `ψ`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Itô process up to a stopping time.** `IsItoProcessUpTo 𝓖 μ B τ X a b` means:
* the family `b 𝟙_{s ≤ τ}` is Itô-integrable;
* almost surely, `s ↦ a(s)` is integrable on `[0, τ]`;
* almost surely, for all `t ≥ 0`,
  `X_{t∧τ} = X_0 + ∫_0^{t∧τ} a(s) ds + ∑ᵢ ∫_0^t bᵢ(s) 𝟙_{s ≤ τ} dBᵢ(s)`. -/
structure IsItoProcessUpTo (𝓖 : Filtration ℝ≥0 mΩ) {ι : Type*} (μ : Measure Ω)
    (B : ι → ℝ → Ω → ℝ) (τ : Ω → ℝ≥0) (X a : ℝ → Ω → ℝ) (b : ι → ℝ → Ω → ℝ) : Prop where
  integrable : IsItoIntegrable 𝓖 μ (fun i s ω => if s ≤ τ ω then b i s ω else 0)
  drift : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => a s ω) volume 0 (τ ω)
  eq : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, X (min t (τ ω) : ℝ≥0) ω =
    X 0 ω + (∫ s in (0 : ℝ)..((min t (τ ω) : ℝ≥0) : ℝ), a s ω) +
      stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then b i s ω else 0) t ω

variable {ι : Type*} [Countable ι] {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-! ### Auxiliary lemmas -/

/-- `[0, t ∧ r] ⊆ [0, r]`. -/
private lemma uIcc_min_subset (t r : ℝ≥0) :
    Set.uIcc (0 : ℝ) ((min t r : ℝ≥0) : ℝ) ⊆ Set.uIcc 0 (r : ℝ) :=
  Set.uIcc_subset_uIcc Set.left_mem_uIcc
    (Set.mem_uIcc.2 (Or.inl ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩))

/-- `∫_0^t g 𝟙_{s ≤ r} ds = ∫_0^{t ∧ r} g ds` (no integrability needed). -/
private lemma integral_cut (g : ℝ → ℝ) (t r : ℝ≥0) :
    ∫ s in (0 : ℝ)..t, (if s ≤ r then g s else 0) = ∫ s in (0 : ℝ)..((min t r : ℝ≥0) : ℝ), g s := by
  have h1 : (fun s : ℝ => if s ≤ r then g s else 0) = (Set.Iic (r : ℝ)).indicator g := by
    funext s
    simp [Set.indicator_apply]
  rw [h1, intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg _), setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioc (0 : ℝ) t ∩ Set.Iic (r : ℝ) = Set.Ioc 0 ((min t r : ℝ≥0) : ℝ) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, NNReal.coe_min, le_min_iff]
    tauto
  rw [hset]

/-- Before `r`, `F(x ∧ r) Δ = F(x) 𝟙_{x ≤ r} Δ` for an increment `Δ = G(y ∧ r) - G(x ∧ r)`,
`x ≤ y` (after `r` the increment vanishes). -/
private lemma stopped_step (F G : ℝ → ℝ) (r : ℝ≥0) {x y : ℝ≥0} (hxy : x ≤ y) :
    F ((min x r : ℝ≥0) : ℝ) * (G ((min y r : ℝ≥0) : ℝ) - G ((min x r : ℝ≥0) : ℝ)) =
      (if (x : ℝ) ≤ r then F x else 0) * (G ((min y r : ℝ≥0) : ℝ) - G ((min x r : ℝ≥0) : ℝ)) := by
  by_cases h : (x : ℝ) ≤ r
  · simp only [h, ↓reduceIte]
    rw [min_eq_left (NNReal.coe_le_coe.1 h)]
  · have hrx : r < x := by exact_mod_cast not_le.1 h
    rw [min_eq_right hrx.le, min_eq_right (hrx.le.trans hxy)]
    simp

/-- The algebra of one step of the discrete product rule. -/
private lemma prod_step {u0 u1 v0 v1 zx zy A0 A1 C0 C1 M0 M1 N0 N1 X0 Y0 : ℝ}
    (hu0 : u0 = X0 + A0 + M0) (hu1 : u1 = X0 + A1 + M1) (hv0 : v0 = Y0 + C0 + N0)
    (hv1 : v1 = Y0 + C1 + N1) (hzx : u0 * (v1 - v0) = zx * (v1 - v0))
    (hzy : v0 * (u1 - u0) = zy * (u1 - u0)) :
    u0 * (v1 - v0) + v0 * (u1 - u0) + (u1 - u0) * (v1 - v0) =
      zx * (C1 - C0) + zy * (A1 - A0) +
        ((u1 - u0) * (v1 - v0) - ((u1 - u0) - (A1 - A0)) * ((v1 - v0) - (C1 - C0))) +
        zx * (N1 - N0) + zy * (M1 - M0) + (M1 - M0) * (N1 - N0) := by
  rw [hzx, hzy]
  subst hu0 hu1 hv0 hv1
  ring

omit [IsProbabilityMeasure μ] in
/-- From `L²` to almost sure convergence along a subsequence, for a sum of three sequences. -/
private lemma exists_subseq_ae {F₁ F₂ F₃ : ℕ → Ω → ℝ}
    (hm₁ : ∀ m, AEStronglyMeasurable (F₁ m) μ) (hm₂ : ∀ m, AEStronglyMeasurable (F₂ m) μ)
    (hm₃ : ∀ m, AEStronglyMeasurable (F₃ m) μ)
    (h₁ : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F₁ m ω ^ 2) ∂μ) atTop (𝓝 0))
    (h₂ : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F₂ m ω ^ 2) ∂μ) atTop (𝓝 0))
    (h₃ : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F₃ m ω ^ 2) ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun m => F₁ (φ m) ω + F₂ (φ m) ω + F₃ (φ m) ω) atTop (𝓝 0) := by
  have key : ∀ F : Ω → ℝ, AEStronglyMeasurable F μ →
      eLpNorm F 2 μ = (∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro F hF
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hF]
    simp only [ENNReal.toReal_ofNat]
    congr 2
    funext ω
    rw [ENNReal.rpow_two, itoEnergy_enorm_sq]
  have hlim : ∀ F : ℕ → Ω → ℝ, (∀ m, AEStronglyMeasurable (F m) μ) →
      Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F m ω ^ 2) ∂μ) atTop (𝓝 0) →
      Tendsto (fun m => eLpNorm (F m) 2 μ) atTop (𝓝 0) := by
    intro F hF h
    have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.congr fun m => (key _ (hF m)).symm
  have hsum : Tendsto (fun m => eLpNorm (fun ω => F₁ m ω + F₂ m ω + F₃ m ω) 2 μ) atTop (𝓝 0) := by
    have hup := ((hlim F₁ hm₁ h₁).add (hlim F₂ hm₂ h₂)).add (hlim F₃ hm₃ h₃)
    simp only [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
      fun m => ?_
    refine (eLpNorm_add_le (f := F₁ m + F₂ m) (g := F₃ m) one_le_two).trans ?_
    gcongr
    exact eLpNorm_add_le one_le_two
  have hin : TendstoInMeasure μ (fun m ω => F₁ m ω + F₂ m ω + F₃ m ω) atTop 0 :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (by simpa using hsum)
  obtain ⟨φ, hφ, hae⟩ := hin.exists_seq_tendsto_ae
  exact ⟨φ, hφ, by simpa using hae⟩

omit [IsProbabilityMeasure μ] in
/-- Two processes with almost surely continuous paths that agree almost surely at each fixed
time are indistinguishable. -/
private lemma ae_forall_of_continuous {P Q : ℝ≥0 → Ω → ℝ}
    (hP : ∀ᵐ ω ∂μ, Continuous fun t => P t ω) (hQ : ∀ᵐ ω ∂μ, Continuous fun t => Q t ω)
    (h : ∀ t, ∀ᵐ ω ∂μ, P t ω = Q t ω) : ∀ᵐ ω ∂μ, ∀ t, P t ω = Q t ω := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hS : ∀ᵐ ω ∂μ, ∀ t ∈ S, P t ω = Q t ω := (ae_ball_iff hSc).2 fun t _ => h t
  filter_upwards [hP, hQ, hS] with ω h1 h2 h3 t
  exact congrFun (Continuous.ext_on hSd h1 h2 fun t ht => h3 t ht) t

/-- The factor `Z_s = X_s 𝟙_{s ≤ τ}` of the product rule: bounded, adapted, left-continuous. -/
private lemma stoppedFactor_props {X : ℝ → Ω → ℝ} {τ : Ω → ℝ≥0} {K : ℝ}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    (hXK : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω → |X s ω| ≤ K) (hK : 0 ≤ K) :
    (∀ ω (s : ℝ), 0 ≤ s → |(if s ≤ τ ω then X s ω else 0)| ≤ K) ∧
    (∀ t : ℝ≥0, Measurable[𝓖 t] (fun ω => if (t : ℝ) ≤ τ ω then X t ω else 0)) ∧
    (∀ ω (s : ℝ), 0 < s →
      ContinuousWithinAt (fun r : ℝ => if r ≤ τ ω then X r ω else 0) (Set.Iic s) s) := by
  refine ⟨fun ω s hs => ?_, fun t => ?_, fun ω s hs => ?_⟩
  · split_ifs with h
    · exact hXK ω s hs h
    · simpa using hK
  · refine Measurable.ite ?_ (hXa t) measurable_const
    have : {ω | ((t : ℝ≥0) : ℝ) ≤ τ ω} = {ω | (τ ω : WithTop ℝ≥0) < t}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, NNReal.coe_le_coe]
      exact ⟨fun h => not_lt.2 (WithTop.coe_le_coe.2 h), fun h => WithTop.coe_le_coe.1 (not_lt.1 h)⟩
    rw [this]
    exact (hτ.measurableSet_lt t).compl
  · have hXr : ContinuousOn (fun s : ℝ => X s ω) (Set.Ici 0) :=
      ((hXc ω).comp continuous_real_toNNReal).continuousOn.congr fun s hs => by
        rw [Function.comp_apply, Real.coe_toNNReal _ hs]
    by_cases h : s ≤ τ ω
    · have hc : ContinuousWithinAt (fun r => X r ω) (Set.Iic s) s :=
        (hXr.continuousAt (Ici_mem_nhds hs)).continuousWithinAt
      refine hc.congr (fun y hy => ?_) ?_
      · have hy' : y ≤ τ ω := (Set.mem_Iic.1 hy).trans h
        simp only [hy', ↓reduceIte]
      · simp only [h, ↓reduceIte]
    · have hlt : (τ ω : ℝ) < s := not_le.1 h
      have hev : ∀ᶠ r in 𝓝[≤] s, (fun r : ℝ => if r ≤ τ ω then X r ω else 0) r =
          (fun r : ℝ => if r ≤ τ ω then X r ω else 0) s := by
        filter_upwards [(eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr
        simp only [not_le.2 hr, h, ↓reduceIte]
      exact tendsto_const_nhds.congr' (hev.mono fun _ hr => hr.symm)

/-- **Product rule (Itô's formula for a product).** Let `τ` be a bounded stopping time, and let
`X = X_0 + ∫ a ds + ∫ b dB`, `Y = Y_0 + ∫ c ds + ∫ d dB` be Itô processes up to `τ`, with all
paths continuous and adapted, such that `|X|, |Y|, |a|, |c|, ∑ᵢ bᵢ², ∑ᵢ dᵢ² ≤ K` on `[0, τ]`.
Then `XY` is an Itô process up to `τ`:
`d(XY) = (X c + Y a + ∑ᵢ bᵢ dᵢ) ds + ∑ᵢ (X dᵢ + Y bᵢ) dBᵢ`. -/
theorem IsItoProcessUpTo.mul (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T)
    {X Y a c : ℝ → Ω → ℝ} {b d : ι → ℝ → Ω → ℝ} {K : ℝ}
    (hX : IsItoProcessUpTo 𝓖 μ B τ X a b) (hY : IsItoProcessUpTo 𝓖 μ B τ Y c d)
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hYc : ∀ ω, Continuous fun t : ℝ≥0 => Y t ω)
    (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t)) (hYa : ∀ t : ℝ≥0, Measurable[𝓖 t] (Y t))
    (hbd : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω →
      |X s ω| ≤ K ∧ |Y s ω| ≤ K ∧ |a s ω| ≤ K ∧ |c s ω| ≤ K ∧
      ∑' i, b i s ω ^ 2 ≤ K ∧ ∑' i, d i s ω ^ 2 ≤ K) :
    IsItoProcessUpTo 𝓖 μ B τ (fun t ω => X t ω * Y t ω)
      (fun s ω => X s ω * c s ω + Y s ω * a s ω + ∑' i, b i s ω * d i s ω)
      (fun i s ω => X s ω * d i s ω + Y s ω * b i s ω) := by
  classical
  obtain ⟨T₀, hT₀⟩ := hτb
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hK : 0 ≤ K := (abs_nonneg _).trans (hbd ω₀ 0 le_rfl (NNReal.coe_nonneg _)).1
  -- the stopped families `b 𝟙_{s ≤ τ}`, `d 𝟙_{s ≤ τ}`
  set b' : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ ω then b i s ω else 0 with hb'
  set d' : ι → ℝ → Ω → ℝ := fun i s ω => if s ≤ τ ω then d i s ω else 0 with hd'
  have hbi : IsItoIntegrable 𝓖 μ b' := hX.integrable
  have hdi : IsItoIntegrable 𝓖 μ d' := hY.integrable
  have hb'K : ∀ ω (s : ℝ), 0 < s → ∑' i, b' i s ω ^ 2 ≤ K := by
    intro ω s hs
    by_cases h : s ≤ τ ω
    · simpa [hb', h] using (hbd ω s hs.le h).2.2.2.2.1
    · simp [hb', h, hK]
  have hd'K : ∀ ω (s : ℝ), 0 < s → ∑' i, d' i s ω ^ 2 ≤ K := by
    intro ω s hs
    by_cases h : s ≤ τ ω
    · simpa [hd', h] using (hbd ω s hs.le h).2.2.2.2.2
    · simp [hd', h, hK]
  -- the factors `X 𝟙_{s ≤ τ}`, `Y 𝟙_{s ≤ τ}`
  set ZX : ℝ → Ω → ℝ := fun s ω => if s ≤ τ ω then X s ω else 0 with hZX
  set ZY : ℝ → Ω → ℝ := fun s ω => if s ≤ τ ω then Y s ω else 0 with hZY
  obtain ⟨hZXb, hZXa, hZXlc⟩ := stoppedFactor_props (𝓖 := 𝓖) hτ hXc hXa
    (fun ω s hs h => (hbd ω s hs h).1) hK
  obtain ⟨hZYb, hZYa, hZYlc⟩ := stoppedFactor_props (𝓖 := 𝓖) hτ hYc hYa
    (fun ω s hs h => (hbd ω s hs h).2.1) hK
  have hXr : ∀ ω, ContinuousOn (fun s : ℝ => X s ω) (Set.Ici 0) := fun ω =>
    ((hXc ω).comp continuous_real_toNNReal).continuousOn.congr fun s hs => by
      rw [Function.comp_apply, Real.coe_toNNReal _ hs]
  have hYr : ∀ ω, ContinuousOn (fun s : ℝ => Y s ω) (Set.Ici 0) := fun ω =>
    ((hYc ω).comp continuous_real_toNNReal).continuousOn.congr fun s hs => by
      rw [Function.comp_apply, Real.coe_toNNReal _ hs]
  -- integrability of the diffusion coefficient
  have h1 : IsItoIntegrable 𝓖 μ (fun i s ω => ZX s ω * d' i s ω) :=
    hdi.mul_leftContinuous (K := K) (fun ω s hs => hZXb ω s hs.le) hZXa hZXlc
  have h2 : IsItoIntegrable 𝓖 μ (fun i s ω => ZY s ω * b' i s ω) :=
    hbi.mul_leftContinuous (K := K) (fun ω s hs => hZYb ω s hs.le) hZYa hZYlc
  have heq : (fun (i : ι) (s : ℝ) (ω : Ω) =>
      if s ≤ τ ω then X s ω * d i s ω + Y s ω * b i s ω else 0) =
      fun (i : ι) (s : ℝ) (ω : Ω) => ZX s ω * d' i s ω + ZY s ω * b' i s ω := by
    funext i s ω
    by_cases h : s ≤ τ ω <;> simp [hZX, hZY, hb', hd', h]
  have hint : IsItoIntegrable 𝓖 μ (fun (i : ι) (s : ℝ) (ω : Ω) =>
      if s ≤ τ ω then X s ω * d i s ω + Y s ω * b i s ω else 0) := by
    rw [heq]
    exact h1.add h2
  -- integrability of the drift
  have hcross := itoProd_ae_abs_tsum_mul_le hbi hdi hb'K hd'K T₀ T₀.2
  have hdr : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s => X s ω * c s ω) volume 0 (τ ω) ∧
      IntervalIntegrable (fun s => Y s ω * a s ω) volume 0 (τ ω) ∧
      IntervalIntegrable (fun s => ∑' i, b i s ω * d i s ω) volume 0 (τ ω) := by
    filter_upwards [hX.drift, hY.drift, hcross] with ω ha hc hbdω
    have hsub : Set.uIcc (0 : ℝ) (τ ω) ⊆ Set.Ici 0 := fun x hx => by
      rw [Set.uIcc_of_le (NNReal.coe_nonneg _)] at hx
      exact hx.1
    refine ⟨hc.continuousOn_mul ((hXr ω).mono hsub), ha.continuousOn_mul ((hYr ω).mono hsub), ?_⟩
    have h3 := hbdω.2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.2 (Or.inl ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (hT₀ ω)⟩)))
    refine h3.congr fun s hs => ?_
    rw [Set.uIoc_of_le (NNReal.coe_nonneg _)] at hs
    simp only [hb', hd', hs.2, ↓reduceIte]
  -- measurability of the Itô integrals
  have hmSI : ∀ (h : ι → ℝ → Ω → ℝ) (u : ℝ≥0), Measurable (stochInt 𝓖 μ B h u) :=
    fun h u => (stochInt_adapted hB h u).mono (𝓖.le u) le_rfl
  -- the identity at a fixed time
  have hfix : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ,
      X ((min t (τ ω) : ℝ≥0) : ℝ) ω * Y ((min t (τ ω) : ℝ≥0) : ℝ) ω =
        X 0 ω * Y 0 ω + (∫ s in (0 : ℝ)..((min t (τ ω) : ℝ≥0) : ℝ),
          (X s ω * c s ω + Y s ω * a s ω + ∑' i, b i s ω * d i s ω)) +
        stochInt 𝓖 μ B (fun (i : ι) (s : ℝ) (ω : Ω) =>
          if s ≤ τ ω then X s ω * d i s ω + Y s ω * b i s ω else 0) t ω := by
    intro t
    set F₁ : ℕ → Ω → ℝ := fun m ω => ∑ k ∈ Finset.range m,
        ZX (itoProdGrid t m k) ω * (stochInt 𝓖 μ B d' (itoProdGrid t m (k + 1)) ω -
          stochInt 𝓖 μ B d' (itoProdGrid t m k) ω) -
        stochInt 𝓖 μ B (fun i s ω => ZX s ω * d' i s ω) t ω with hF₁
    set F₂ : ℕ → Ω → ℝ := fun m ω => ∑ k ∈ Finset.range m,
        ZY (itoProdGrid t m k) ω * (stochInt 𝓖 μ B b' (itoProdGrid t m (k + 1)) ω -
          stochInt 𝓖 μ B b' (itoProdGrid t m k) ω) -
        stochInt 𝓖 μ B (fun i s ω => ZY s ω * b' i s ω) t ω with hF₂
    set F₃ : ℕ → Ω → ℝ := fun m ω => ∑ k ∈ Finset.range m,
        (stochInt 𝓖 μ B b' (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B b' (itoProdGrid t m k) ω) *
          (stochInt 𝓖 μ B d' (itoProdGrid t m (k + 1)) ω -
            stochInt 𝓖 μ B d' (itoProdGrid t m k) ω) -
        ∫ s in (0 : ℝ)..t, ∑' i, b' i s ω * d' i s ω with hF₃
    have hL₁ : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F₁ m ω ^ 2) ∂μ) atTop (𝓝 0) :=
      itoProd_tendsto_riemann hB hdi hZXb hZXa hZXlc t
    have hL₂ : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F₂ m ω ^ 2) ∂μ) atTop (𝓝 0) :=
      itoProd_tendsto_riemann hB hbi hZYb hZYa hZYlc t
    have hL₃ : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (F₃ m ω ^ 2) ∂μ) atTop (𝓝 0) :=
      itoProd_tendsto_covariation hB hbi hdi hb'K hd'K t
    have hJm : Measurable fun ω => ∫ s in (0 : ℝ)..t, ∑' i, b' i s ω * d' i s ω := by
      set G : ℝ × Ω → ℝ := fun p =>
        ∑' i, (if 0 < p.1 then b' i p.1 p.2 else 0) * (if 0 < p.1 then d' i p.1 p.2 else 0)
        with hG
      have hGm : Measurable G := Measurable.tsum fun i => (hbi.meas i).mul (hdi.meas i)
      have hS : StronglyMeasurable fun ω =>
          ∫ s, (fun ω s => G (s, ω)) ω s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) :=
        StronglyMeasurable.integral_prod_right (f := fun ω s => G (s, ω))
          (hGm.comp measurable_swap).stronglyMeasurable
      have e : (fun ω => ∫ s in (0 : ℝ)..t, ∑' i, b' i s ω * d' i s ω) = fun ω =>
          ∫ s, (fun ω s => G (s, ω)) ω s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
        funext ω
        rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        simp only [hG, hs.1, ↓reduceIte]
      rw [e]
      exact hS.measurable
    have hm₁ : ∀ m, AEStronglyMeasurable (F₁ m) μ := fun m =>
      ((Finset.measurable_sum _ fun k _ => ((hZXa _).mono (𝓖.le _) le_rfl).mul
        ((hmSI _ _).sub (hmSI _ _))).sub (hmSI _ _)).aestronglyMeasurable
    have hm₂ : ∀ m, AEStronglyMeasurable (F₂ m) μ := fun m =>
      ((Finset.measurable_sum _ fun k _ => ((hZYa _).mono (𝓖.le _) le_rfl).mul
        ((hmSI _ _).sub (hmSI _ _))).sub (hmSI _ _)).aestronglyMeasurable
    have hm₃ : ∀ m, AEStronglyMeasurable (F₃ m) μ := fun m =>
      ((Finset.measurable_sum _ fun k _ => ((hmSI _ _).sub (hmSI _ _)).mul
        ((hmSI _ _).sub (hmSI _ _))).sub hJm).aestronglyMeasurable
    obtain ⟨φ, hφ, hae⟩ := exists_subseq_ae hm₁ hm₂ hm₃ hL₁ hL₂ hL₃
    filter_upwards [hX.eq, hY.eq, hX.drift, hY.drift, hdr, hae, stochInt_add hB h1 h2]
      with ω hXe hYe ha hc hdrω hφω hadd
    rw [← hb'] at hXe
    rw [← hd'] at hYe
    -- the pathwise limits (drift Riemann sums, drift parts of the covariation)
    have hfX : ContinuousOn (fun s : ℝ => X s ω) (Set.Icc 0 (τ ω)) :=
      (hXr ω).mono Set.Icc_subset_Ici_self
    have hfY : ContinuousOn (fun s : ℝ => Y s ω) (Set.Icc 0 (τ ω)) :=
      (hYr ω).mono Set.Icc_subset_Ici_self
    have hP₁ := itoProd_tendsto_drift_riemann (t := t) hfX hc
      (fun s hs h => (hbd ω s hs h).2.2.2.1)
    have hP₂ := itoProd_tendsto_drift_riemann (t := t) hfY ha
      (fun s hs h => (hbd ω s hs h).2.2.1)
    have hUc : Continuous fun u : ℝ≥0 => X ((min u (τ ω) : ℝ≥0) : ℝ) ω :=
      (hXc ω).comp (continuous_id.min continuous_const)
    have hVc : Continuous fun u : ℝ≥0 => Y ((min u (τ ω) : ℝ≥0) : ℝ) ω :=
      (hYc ω).comp (continuous_id.min continuous_const)
    have hP₃ := itoProd_tendsto_cross (t := t) hUc hVc ha hc
      (fun s hs h => (hbd ω s hs h).2.2.1) (fun s hs h => (hbd ω s hs h).2.2.2.1)
    have hlim := ((((hP₁.comp hφ.tendsto_atTop).add (hP₂.comp hφ.tendsto_atTop)).add
      (hP₃.comp hφ.tendsto_atTop)).add hφω).add_const
      (stochInt 𝓖 μ B (fun i s ω => ZX s ω * d' i s ω) t ω +
        stochInt 𝓖 μ B (fun i s ω => ZY s ω * b' i s ω) t ω +
        ∫ s in (0 : ℝ)..t, ∑' i, b' i s ω * d' i s ω)
    -- the discrete product rule, for `n = φ m ≥ 1` cells
    have heqv : ∀ᶠ m in atTop, (fun m =>
        ((((fun m => ∑ k ∈ Finset.range m,
          (if (itoProdGrid t m k : ℝ) ≤ τ ω then X (itoProdGrid t m k) ω else 0) *
            ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ), c s ω) -
              ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ), c s ω)) ∘ φ) m +
        ((fun m => ∑ k ∈ Finset.range m,
          (if (itoProdGrid t m k : ℝ) ≤ τ ω then Y (itoProdGrid t m k) ω else 0) *
            ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ), a s ω) -
              ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ), a s ω)) ∘ φ) m) +
        ((fun m => ∑ k ∈ Finset.range m,
          ((X ((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ) ω -
                X ((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ) ω) *
              (Y ((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ) ω -
                Y ((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ) ω) -
            ((X ((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ) ω -
                X ((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ) ω) -
              ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ), a s ω) -
                ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ), a s ω)) *
            ((Y ((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ) ω -
                Y ((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ) ω) -
              ((∫ s in (0 : ℝ)..((min (itoProdGrid t m (k + 1)) (τ ω) : ℝ≥0) : ℝ), c s ω) -
                ∫ s in (0 : ℝ)..((min (itoProdGrid t m k) (τ ω) : ℝ≥0) : ℝ), c s ω)))) ∘ φ) m +
        (F₁ (φ m) ω + F₂ (φ m) ω + F₃ (φ m) ω)) +
        (stochInt 𝓖 μ B (fun i s ω => ZX s ω * d' i s ω) t ω +
          stochInt 𝓖 μ B (fun i s ω => ZY s ω * b' i s ω) t ω +
          ∫ s in (0 : ℝ)..t, ∑' i, b' i s ω * d' i s ω)) m =
        X ((min t (τ ω) : ℝ≥0) : ℝ) ω * Y ((min t (τ ω) : ℝ≥0) : ℝ) ω - X 0 ω * Y 0 ω := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      have hn : φ m ≠ 0 := by
        have := hφ.id_le m
        simp only [id] at this
        omega
      have htel := itoProd_telescope
        (fun k => X ((min (itoProdGrid t (φ m) k) (τ ω) : ℝ≥0) : ℝ) ω)
        (fun k => Y ((min (itoProdGrid t (φ m) k) (τ ω) : ℝ≥0) : ℝ) ω) (φ m)
      have h0 : min (0 : ℝ≥0) (τ ω) = 0 := min_eq_left zero_le
      simp only [itoProdGrid_self t hn, itoProdGrid_zero, h0, NNReal.coe_zero] at htel
      rw [htel, Finset.sum_congr rfl fun k _ => prod_step (hXe _) (hXe _) (hYe _) (hYe _)
        (stopped_step (fun s => X s ω) (fun s => Y s ω) (τ ω)
          (itoProdGrid_mono t (φ m) (Nat.le_succ k)))
        (stopped_step (fun s => Y s ω) (fun s => X s ω) (τ ω)
          (itoProdGrid_mono t (φ m) (Nat.le_succ k)))]
      simp only [Function.comp_apply, Finset.sum_add_distrib, hF₁, hF₂, hF₃, hZX, hZY]
      ring
    have hval := tendsto_nhds_unique (hlim.congr' heqv) tendsto_const_nhds
    -- conclusion
    have hJ : ∫ s in (0 : ℝ)..t, ∑' i, b' i s ω * d' i s ω =
        ∫ s in (0 : ℝ)..((min t (τ ω) : ℝ≥0) : ℝ), ∑' i, b i s ω * d i s ω := by
      have e : (fun s => ∑' i, b' i s ω * d' i s ω) =
          fun s : ℝ => if s ≤ τ ω then ∑' i, b i s ω * d i s ω else 0 := by
        funext s
        by_cases h : s ≤ τ ω <;> simp [hb', hd', h]
      rw [e]
      exact integral_cut _ t (τ ω)
    have hsub := uIcc_min_subset t (τ ω)
    rw [heq, hadd t, intervalIntegral.integral_add
      ((hdrω.1.mono_set hsub).add (hdrω.2.1.mono_set hsub)) (hdrω.2.2.mono_set hsub),
      intervalIntegral.integral_add (hdrω.1.mono_set hsub) (hdrω.2.1.mono_set hsub), ← hJ]
    linarith
  refine ⟨hint, ?_, ?_⟩
  · filter_upwards [hdr] with ω h using (h.1.add h.2.1).add h.2.2
  · refine ae_forall_of_continuous
      (P := fun t ω => X ((min t (τ ω) : ℝ≥0) : ℝ) ω * Y ((min t (τ ω) : ℝ≥0) : ℝ) ω)
      (Q := fun t ω => X 0 ω * Y 0 ω + (∫ s in (0 : ℝ)..((min t (τ ω) : ℝ≥0) : ℝ),
          (X s ω * c s ω + Y s ω * a s ω + ∑' i, b i s ω * d i s ω)) +
        stochInt 𝓖 μ B (fun (i : ι) (s : ℝ) (ω : Ω) =>
          if s ≤ τ ω then X s ω * d i s ω + Y s ω * b i s ω else 0) t ω)
      (ae_of_all _ fun ω => ?_) ?_ hfix
    · exact ((hXc ω).comp (continuous_id.min continuous_const)).mul
        ((hYc ω).comp (continuous_id.min continuous_const))
    · filter_upwards [hdr, stochInt_continuous hB hint] with ω hD hcont
      have hDi : IntervalIntegrable
          (fun s => X s ω * c s ω + Y s ω * a s ω + ∑' i, b i s ω * d i s ω) volume 0 (τ ω) :=
        (hD.1.add hD.2.1).add hD.2.2
      have hIo : IntegrableOn
          (fun s => X s ω * c s ω + Y s ω * a s ω + ∑' i, b i s ω * d i s ω)
          (Set.uIcc 0 (τ ω)) := by
        rw [Set.uIcc_of_le (NNReal.coe_nonneg _)]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le (NNReal.coe_nonneg _)).1 hDi
      have hprim := (intervalIntegral.continuousOn_primitive_interval hIo).comp_continuous
        (NNReal.continuous_coe.comp
          (continuous_id.min continuous_const : Continuous fun u : ℝ≥0 => min u (τ ω)))
        (fun u => Set.mem_uIcc.2
          (Or.inl ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩))
      exact (continuous_const.add hprim).add hcont

/-- **Sum** of two Itô processes up to the same `τ`. -/
theorem IsItoProcessUpTo.add (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {X Y a c : ℝ → Ω → ℝ} {b d : ι → ℝ → Ω → ℝ}
    (hX : IsItoProcessUpTo 𝓖 μ B τ X a b) (hY : IsItoProcessUpTo 𝓖 μ B τ Y c d) :
    IsItoProcessUpTo 𝓖 μ B τ (fun t ω => X t ω + Y t ω) (fun s ω => a s ω + c s ω)
      (fun i s ω => b i s ω + d i s ω) := by
  have heq : (fun (i : ι) (s : ℝ) (ω : Ω) => if s ≤ τ ω then b i s ω + d i s ω else 0) = fun (i : ι) (s : ℝ) (ω : Ω) =>
      (if s ≤ τ ω then b i s ω else 0) + (if s ≤ τ ω then d i s ω else 0) := by
    funext i s ω
    split_ifs <;> simp
  refine ⟨by rw [heq]; exact hX.integrable.add hY.integrable, ?_, ?_⟩
  · filter_upwards [hX.drift, hY.drift] with ω h1 h2 using h1.add h2
  · filter_upwards [hX.eq, hY.eq, hX.drift, hY.drift,
      stochInt_add hB hX.integrable hY.integrable] with ω h1 h2 ha hc hs t
    rw [heq, hs t, h1 t, h2 t, intervalIntegral.integral_add
      (ha.mono_set (uIcc_min_subset t (τ ω))) (hc.mono_set (uIcc_min_subset t (τ ω)))]
    ring

/-- **Constant multiple** of an Itô process. -/
theorem IsItoProcessUpTo.const_mul (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {X a : ℝ → Ω → ℝ} {b : ι → ℝ → Ω → ℝ} (hX : IsItoProcessUpTo 𝓖 μ B τ X a b) (r : ℝ) :
    IsItoProcessUpTo 𝓖 μ B τ (fun t ω => r * X t ω) (fun s ω => r * a s ω)
      (fun i s ω => r * b i s ω) := by
  have heq : (fun (i : ι) (s : ℝ) (ω : Ω) => if s ≤ τ ω then r * b i s ω else 0) = fun (i : ι) (s : ℝ) (ω : Ω) =>
      r * (if s ≤ τ ω then b i s ω else 0) := by
    funext i s ω
    split_ifs <;> simp
  refine ⟨by rw [heq]; exact hX.integrable.const_mul r, ?_, ?_⟩
  · filter_upwards [hX.drift] with ω h1 using h1.const_mul r
  · filter_upwards [hX.eq, stochInt_const_mul hB hX.integrable r] with ω h1 hs t
    rw [heq, hs t, h1 t, intervalIntegral.integral_const_mul]
    ring

/-- **Finite sum** of Itô processes up to the same `τ` (for instance over a box
`|x| ≤ K` of `ℤ`). -/
theorem IsItoProcessUpTo.finset_sum (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {κ : Type*} (S : Finset κ) {X a : κ → ℝ → Ω → ℝ} {b : κ → ι → ℝ → Ω → ℝ}
    (hX : ∀ k ∈ S, IsItoProcessUpTo 𝓖 μ B τ (X k) (a k) (b k)) :
    IsItoProcessUpTo 𝓖 μ B τ (fun t ω => ∑ k ∈ S, X k t ω) (fun s ω => ∑ k ∈ S, a k s ω)
      (fun i s ω => ∑ k ∈ S, b k i s ω) := by
  have heq : (fun (i : ι) (s : ℝ) (ω : Ω) => if s ≤ τ ω then ∑ k ∈ S, b k i s ω else 0) = fun (i : ι) (s : ℝ) (ω : Ω) =>
      ∑ k ∈ S, (fun k (i : ι) (s : ℝ) (ω : Ω) => if s ≤ τ ω then b k i s ω else 0) k i s ω := by
    funext i s ω
    by_cases h : s ≤ τ ω <;> simp [h]
  refine ⟨by rw [heq]; exact IsItoIntegrable.finset_sum S fun k hk => (hX k hk).integrable, ?_, ?_⟩
  · filter_upwards [(eventually_all_finset S).2 fun k hk => (hX k hk).drift] with ω h
    have := IntervalIntegrable.sum S h
    convert this using 1
    funext s
    simp
  · filter_upwards [(eventually_all_finset S).2 fun k hk => (hX k hk).drift,
      (eventually_all_finset S).2 fun k hk => (hX k hk).eq,
      stochInt_finset_sum hB S fun k hk => (hX k hk).integrable] with ω hd he hs t
    rw [heq, hs t, intervalIntegral.integral_finsetSum
      fun k hk => (hd k hk).mono_set (uIcc_min_subset t (τ ω))]
    rw [Finset.sum_congr rfl fun k hk => he k hk t]
    simp only [Finset.sum_add_distrib]

/-- **Deterministic `C¹` functions of time** are Itô processes without diffusion term, up to any
`τ ≤ T`: if `α` has derivative `α'` (one-sided at the ends) on `[0, T]` and `α'` is continuous
on `[0, T]`, then `α_{t∧τ} = α_0 + ∫_0^{t∧τ} α'(s) ds`. -/
theorem isItoProcessUpTo_deterministic (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0} {T : ℝ}
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) {α α' : ℝ → ℝ}
    (hα : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt α (α' t) (Set.Icc 0 T) t)
    (hα' : ContinuousOn α' (Set.Icc 0 T)) :
    IsItoProcessUpTo 𝓖 μ B τ (fun t _ => α t) (fun t _ => α' t) (0 : ι → ℝ → Ω → ℝ) := by
  have hzero : (fun (i : ι) (s : ℝ) (ω : Ω) => if s ≤ τ ω then (0 : ι → ℝ → Ω → ℝ) i s ω else 0) = 0 := by
    funext i s ω
    simp
  have hsub : ∀ ω, Set.uIcc (0 : ℝ) (τ ω) ⊆ Set.Icc 0 T := fun ω =>
    Set.uIcc_subset_Icc ⟨le_rfl, (NNReal.coe_nonneg _).trans (hτT ω)⟩
      ⟨NNReal.coe_nonneg _, hτT ω⟩
  refine ⟨by rw [hzero]; exact isItoIntegrable_zero, ae_of_all _ fun ω => (hα'.mono (hsub ω)).intervalIntegrable,
    ?_⟩
  filter_upwards [stochInt_zero hB] with ω h t
  rw [hzero, h t, add_zero]
  set u : ℝ := ((min t (τ ω) : ℝ≥0) : ℝ) with hu
  have hu0 : 0 ≤ u := NNReal.coe_nonneg _
  have huT : u ≤ T := (NNReal.coe_le_coe.2 (min_le_right _ _)).trans (hτT ω)
  have hsubu : Set.Icc 0 u ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl huT
  have hcont : ContinuousOn α (Set.Icc 0 T) := fun x hx => (hα x hx).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hu0 (hcont.mono hsubu)
    (fun x hx => ((hα x (hsubu (Set.Ioo_subset_Icc_self hx))).hasDerivAt
      (Icc_mem_nhds (hx.1) (lt_of_lt_of_le hx.2 huT))).hasDerivWithinAt)
    ((hα'.mono (by rw [Set.uIcc_of_le hu0]; exact hsubu)).intervalIntegrable)
  rw [hFTC]
  ring

/-- **Smaller stopping time.** An Itô process up to `τ` is an Itô process up to every stopping
time `σ ≤ τ`. -/
theorem IsItoProcessUpTo.mono (hB : IsBrownianFamily 𝓖 B μ) {τ σ : Ω → ℝ≥0}
    {X a : ℝ → Ω → ℝ} {b : ι → ℝ → Ω → ℝ} (hX : IsItoProcessUpTo 𝓖 μ B τ X a b)
    (hσ : IsStoppingTime 𝓖 (fun ω => (σ ω : WithTop ℝ≥0))) (hστ : ∀ ω, σ ω ≤ τ ω) :
    IsItoProcessUpTo 𝓖 μ B σ X a b := by
  have heq : (fun (i : ι) (s : ℝ) (ω : Ω) => if s ≤ σ ω then (if s ≤ τ ω then b i s ω else 0) else 0) =
      (fun (i : ι) (s : ℝ) (ω : Ω) => if s ≤ σ ω then b i s ω else 0) := by
    funext i s ω
    by_cases h : s ≤ σ ω
    · have : s ≤ τ ω := h.trans (NNReal.coe_le_coe.2 (hστ ω))
      simp [h, this]
    · simp [h]
  refine ⟨by rw [← heq]; exact hX.integrable.indicator_stoppingTime hσ, ?_, ?_⟩
  · filter_upwards [hX.drift] with ω h
    exact h.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.2 (Or.inl ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (hστ ω)⟩)))
  · filter_upwards [hX.eq, stochInt_indicator_stoppingTime hB hX.integrable hσ] with ω h1 h2 t
    have hm : min (min t (σ ω)) (τ ω) = min t (σ ω) :=
      min_eq_left ((min_le_right _ _).trans (hστ ω))
    have := h1 (min t (σ ω))
    rw [hm] at this
    rw [this, ← h2 t, heq]

end QSSEPtoKPZ
