/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Elementary
public import QSSEPtoKPZ.Martingales.Doob
public import QSSEPtoKPZ.ItoIntegral.FastLimit

/-!
# The Itô integral against a Brownian family (package C, task C3)

INTERFACE FILE (task I0 of Stage 2): the definitions below are complete; the theorems are
frozen interfaces, proved by task C3. See `docs/stage2-design.md`, Section 2.2 (design decision
C-3), and `docs/stage2-interfaces.md`.

* `IsItoIntegrable 𝓖 μ h`: `h` is jointly measurable on `(0, ∞) × Ω` and is the limit, for the
  energy on every `[0, T]`, of one sequence of elementary integrands.
* `stochInt 𝓖 μ B h t ω = ∑ᵢ ∫_0^t hᵢ(s) dBᵢ(s)`: the pathwise limit of the elementary integrals
  along a fast approximating sequence (`0` if `h` is not Itô-integrable). By Doob's `L²`
  inequality and Borel–Cantelli the limit is almost surely uniform on compacts.
* Interfaces: adaptedness (for every `ω`), continuity, agreement with the elementary integral,
  linearity, dependence on the integrand only through its energy class, isometry,
  martingale property and bracket, cross bracket, Doob's inequality, `L²` convergence.

Only the values of the integrand at times `s > 0` matter (`IsItoIntegrable` asks measurability of
`h` restricted to `s > 0`; the energy is an integral over `(0, T]`).

Proofs (task C3; auxiliary results in `Energy.lean`, `Convergence.lean`, `FastLimit.lean`).
Along the fast sequence `e_k`, `𝔼 sup_{[0,k]} (I(e_{k+1}) - I(e_k))² ≤ 16 · 8⁻ᵏ` (Doob), so
`∑ₖ 4ᵏ sup_{[0,k]} (I(e_{k+1}) - I(e_k))²` is integrable, hence finite almost surely: the
elementary integrals converge uniformly on compacts, to a continuous limit. Fatou's lemma then
gives `𝔼 sup_{[0,T]} (I(f) - I(h))² ≤ 8 𝔼 ∫_0^T ∑ᵢ (fᵢ - hᵢ)²` for every elementary `f`, whence
`L²` convergence `I_t(f_k) → I_t(h)` whenever `f_k → h` for the energy. Linearity and locality
follow at each fixed `t`, and for all `t` at once by continuity. The martingale property and
the cross bracket pass to the limit in `L¹` (`condExp_ae_eq_of_tendsto`), using
`|x y| ≤ λ x² + λ⁻¹ y²` for the products and the brackets; the isometry is the cross bracket at
`s = 0`, and Doob's inequality for `I(h)` follows from `IsCL2Mart.lintegral_iSup_sq_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Definitions -/

/-- `h` is Itô-integrable: for every `i`, `(s, ω) ↦ hᵢ(s, ω)` is jointly measurable on
`(0, ∞) × Ω` (extended by `0` for `s ≤ 0`), and `h` is the limit, for the energy
`𝔼 ∫_0^T ∑ᵢ (·)² ds` on every `[0, T]`, of a single sequence of elementary integrands. -/
structure IsItoIntegrable (𝓖 : Filtration ℝ≥0 mΩ) {ι : Type*} (μ : Measure Ω)
    (h : ι → ℝ → Ω → ℝ) : Prop where
  meas : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h i p.1 p.2 else 0
  approx : ∃ e : ℕ → ElemIntegrand 𝓖 ι, ∀ T : ℝ,
    Tendsto (fun k => energy μ (fun i s ω => (e k).toFun i s ω - h i s ω) T) atTop (𝓝 0)

/-- A fast approximating sequence: `energy (e_k - h) k ≤ 8⁻ᵏ`. -/
lemma IsItoIntegrable.exists_fast {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} {μ : Measure Ω}
    {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) :
    ∃ e : ℕ → ElemIntegrand 𝓖 ι, ∀ k : ℕ,
      energy μ (fun i s ω => (e k).toFun i s ω - h i s ω) k ≤ (8 : ℝ≥0∞)⁻¹ ^ k := by
  obtain ⟨e, he⟩ := hh.approx
  have hpos : ∀ k : ℕ, (0 : ℝ≥0∞) < (8 : ℝ≥0∞)⁻¹ ^ k := fun k =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) k
  have : ∀ k : ℕ, ∃ N, energy μ (fun i s ω => (e N).toFun i s ω - h i s ω) k ≤
      (8 : ℝ≥0∞)⁻¹ ^ k := fun k =>
    ((he k).eventually (ge_mem_nhds (hpos k))).exists
  choose N hN using this
  exact ⟨fun k => e (N k), hN⟩

open Classical in
/-- **The Itô integral** `∑ᵢ ∫_0^t hᵢ(s) dBᵢ(s)`: the pathwise limit of the elementary integrals
along the fast approximating sequence chosen by `IsItoIntegrable.exists_fast` (`0` if `h` is not
Itô-integrable, junk value of `limUnder` where the limit does not exist; by the interface
theorems below, the limit exists for all `t` almost surely). -/
def stochInt (𝓖 : Filtration ℝ≥0 mΩ) {ι : Type*} (μ : Measure Ω) (B : ι → ℝ → Ω → ℝ)
    (h : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if hh : IsItoIntegrable 𝓖 μ h then
    limUnder atTop fun k => (hh.exists_fast.choose k).integral B t ω
  else 0

/-- The Itô integral vanishes at times `t ≤ 0`, for every `ω`. -/
lemma stochInt_of_nonpos {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} {μ : Measure Ω}
    (B : ι → ℝ → Ω → ℝ) (h : ι → ℝ → Ω → ℝ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    stochInt 𝓖 μ B h t ω = 0 := by
  unfold stochInt
  split_ifs with hh
  · simp only [ElemIntegrand.integral_of_nonpos _ B ht]
    exact tendsto_const_nhds.limUnder_eq
  · rfl

/-! ### Interfaces (task C3) -/

variable {ι : Type*} [Countable ι] {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

open StochIntAux

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- A pointwise limit of measurable real functions (`limUnder`, junk value where the limit does
not exist) is measurable. -/
private lemma measurable_limUnder_nat {X : Type*} [MeasurableSpace X] {f : ℕ → X → ℝ}
    (hf : ∀ k, Measurable (f k)) : Measurable fun x => limUnder atTop (f · x) :=
  (StronglyMeasurable.limUnder fun k => (hf k).stronglyMeasurable).measurable

set_option linter.unusedSectionVars false in
/-- **Adaptedness.** For every `t ≥ 0`, `I_t(h)` is `𝓖_t`-measurable (for every `ω`; no
completeness of `𝓖` is needed, since `limUnder` of measurable functions is measurable). -/
theorem stochInt_adapted (hB : IsBrownianFamily 𝓖 B μ) (h : ι → ℝ → Ω → ℝ) (t : ℝ≥0) :
    Measurable[𝓖 t] (stochInt 𝓖 μ B h t) := by
  unfold stochInt
  split_ifs with hh
  · exact @measurable_limUnder_nat Ω (𝓖 t) _ fun k =>
      (hh.exists_fast.choose k).integral_adapted hB t
  · exact measurable_const

/-! #### Auxiliary results (task C3): the pathwise limit -/

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- `stochInt` is the limit along the fast sequence. -/
private lemma stochInt_eq_limUnder {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) (t : ℝ)
    (ω : Ω) : stochInt 𝓖 μ B h t ω =
      limUnder atTop fun k => (hh.exists_fast.choose k).integral B t ω := by
  unfold stochInt
  split_ifs
  rfl

/-- `I_t(h)` is measurable for every real `t`. -/
private lemma measurable_stochInt (hB : IsBrownianFamily 𝓖 B μ) (h : ι → ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (stochInt 𝓖 μ B h t) := by
  rcases le_or_gt t 0 with ht | ht
  · have : stochInt 𝓖 μ B h t = fun _ => 0 := funext (stochInt_of_nonpos B h ht)
    rw [this]
    exact measurable_const
  · have := (stochInt_adapted hB h t.toNNReal).mono (𝓖.le _) le_rfl
    rwa [Real.coe_toNNReal t ht.le] at this

omit [IsProbabilityMeasure μ] in
/-- Consecutive terms of the fast sequence: `𝔼 ∫_0^k ∑ᵢ (e_{k+1} - e_k)² ≤ 4 · 8⁻ᵏ`. -/
private lemma fast_step {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) (k : ℕ) :
    energy μ (fun i s ω => (hh.exists_fast.choose (k + 1)).toFun i s ω -
      (hh.exists_fast.choose k).toFun i s ω) k ≤ 4 * (8 : ℝ≥0∞)⁻¹ ^ k := by
  have he := hh.exists_fast.choose_spec
  calc _ ≤ 2 * energy μ (fun i s ω => (hh.exists_fast.choose (k + 1)).toFun i s ω - h i s ω) k +
        2 * energy μ (fun i s ω => h i s ω - (hh.exists_fast.choose k).toFun i s ω) k :=
        energy_add_le ((ElemIntegrand.energyMeas_toFun _).sub hh.meas) (fun i s ω => by ring) _
    _ ≤ 2 * (8 : ℝ≥0∞)⁻¹ ^ k + 2 * (8 : ℝ≥0∞)⁻¹ ^ k := by
        gcongr
        · refine (energy_mono _ (by push_cast; linarith)).trans ((he (k + 1)).trans ?_)
          rw [pow_succ]
          exact mul_le_of_le_one_right' (by norm_num)
        · rw [energy_sub_comm]
          exact he k
    _ = 4 * (8 : ℝ≥0∞)⁻¹ ^ k := by ring

/-- Almost surely, `t ↦ I_t(h)` is continuous on `ℝ` and is the pointwise limit of the
elementary integrals along the fast sequence. -/
private lemma ae_good (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) :
    ∀ᵐ ω ∂μ, Continuous (fun t : ℝ => stochInt 𝓖 μ B h t ω) ∧
      ∀ t, Tendsto (fun k => (hh.exists_fast.choose k).integral B t ω) atTop
        (𝓝 (stochInt 𝓖 μ B h t ω)) := by
  filter_upwards [elemInt_ae_tendsto hB _ (fast_step hh)] with ω hω
  obtain ⟨L, hLc, hL⟩ := hω
  have hE : ∀ t, stochInt 𝓖 μ B h t ω = L t := fun t => by
    rw [stochInt_eq_limUnder hh, (hL t).limUnder_eq]
  have : (fun t => stochInt 𝓖 μ B h t ω) = L := funext hE
  refine ⟨by rw [this]; exact hLc, fun t => by rw [hE]; exact hL t⟩

/-- **Continuity.** Almost surely, `t ↦ I_t(h)` is continuous on `[0, ∞)`. -/
theorem stochInt_continuous (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => stochInt 𝓖 μ B h t ω := by
  filter_upwards [ae_good hB hh] with ω hω
  exact hω.1.comp NNReal.continuous_coe

/-- The energy of an Itô-integrable family is finite on every `[0, T]`. -/
theorem IsItoIntegrable.energy_lt_top {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    (T : ℝ) : energy μ h T < ∞ := by
  obtain ⟨e, he⟩ := hh.approx
  obtain ⟨k, hk⟩ := ((he T).eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  calc energy μ h T ≤ 2 * energy μ (fun i s ω => h i s ω - (e k).toFun i s ω) T +
        2 * energy μ (e k).toFun T :=
        energy_add_le (EnergyMeas.sub hh.meas (ElemIntegrand.energyMeas_toFun _))
          (fun i s ω => by ring) T
    _ < ∞ := by
        rw [energy_sub_comm]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
          (hk.trans ENNReal.one_lt_top), ENNReal.mul_lt_top (by norm_num) (energy_elem_lt_top _ T)⟩

set_option linter.unusedSectionVars false in
/-- An elementary integrand is Itô-integrable. -/
theorem isItoIntegrable_elem (e : ElemIntegrand 𝓖 ι) : IsItoIntegrable 𝓖 μ e.toFun := by
  refine ⟨ElemIntegrand.energyMeas_toFun e, ⟨fun _ => e, fun T => ?_⟩⟩
  simp [energy, pathEnergy]

/-! #### Auxiliary results (task C3): `L²` estimates -/

/-- `𝔼 sup_{[0,T]} (I(f) - I(h))² ≤ 8 𝔼 ∫_0^T ∑ᵢ (fᵢ - hᵢ)²` for an elementary `f` (Doob's
inequality for `I(f) - I(e_j)` and Fatou's lemma along the fast sequence `e_j`). -/
private lemma lintegral_iSup_elem_sub_le (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (f : ElemIntegrand 𝓖 ι) (T : ℝ) :
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((f.integral B t ω - stochInt 𝓖 μ B h t ω) ^ 2) ∂μ ≤
      8 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T := by
  have he := hh.exists_fast.choose_spec
  set G : ℕ → Ω → ℝ≥0∞ := fun j ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal ((f.integral B t ω - (hh.exists_fast.choose j).integral B t ω) ^ 2)
    with hG_def
  have hG : ∀ j, AEMeasurable (G j) μ ∧ ∫⁻ ω, G j ω ∂μ ≤
      4 * energy μ (fun i s ω => f.toFun i s ω - (hh.exists_fast.choose j).toFun i s ω) T :=
    fun j => elemInt_sub_doob hB f _ T
  have h1 : ∀ᵐ ω ∂μ, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((f.integral B t ω - stochInt 𝓖 μ B h t ω) ^ 2)) ≤
      liminf (fun j => G j ω) atTop := by
    filter_upwards [ae_good hB hh] with ω hω
    refine iSup₂_le fun t ht => ?_
    have hlim : Tendsto (fun j => ENNReal.ofReal
        ((f.integral B t ω - (hh.exists_fast.choose j).integral B t ω) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((f.integral B t ω - stochInt 𝓖 μ B h t ω) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_const_nhds.sub (hω.2 t)).pow 2)
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun j => le_iSup₂ (f := fun t
      (_ : t ∈ Set.Icc (0 : ℝ) T) => ENNReal.ofReal
        ((f.integral B t ω - (hh.exists_fast.choose j).integral B t ω) ^ 2)) t ht)
  have h2 : ∀ᶠ j in atTop, ∫⁻ ω, G j ω ∂μ ≤
      8 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T + 8 * (8 : ℝ≥0∞)⁻¹ ^ j := by
    filter_upwards [eventually_ge_atTop ⌈T⌉₊] with j hj
    calc ∫⁻ ω, G j ω ∂μ
        ≤ 4 * energy μ (fun i s ω => f.toFun i s ω - (hh.exists_fast.choose j).toFun i s ω) T :=
          (hG j).2
      _ ≤ 4 * (2 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T +
          2 * energy μ (fun i s ω => h i s ω - (hh.exists_fast.choose j).toFun i s ω) T) := by
          gcongr
          exact energy_add_le ((ElemIntegrand.energyMeas_toFun f).sub hh.meas)
            (fun i s ω => by ring) T
      _ ≤ 4 * (2 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T +
          2 * (8 : ℝ≥0∞)⁻¹ ^ j) := by
          gcongr
          rw [energy_sub_comm]
          exact (energy_mono _ ((Nat.le_ceil T).trans (by exact_mod_cast hj))).trans (he j)
      _ = _ := by ring
  have hlim2 : Tendsto (fun j : ℕ => 8 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T +
      8 * (8 : ℝ≥0∞)⁻¹ ^ j) atTop
      (𝓝 (8 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T)) := by
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (8 : ℝ≥0∞)⁻¹ < 1))
      (Or.inr (by norm_num)))
  calc _ ≤ ∫⁻ ω, liminf (fun j => G j ω) atTop ∂μ := lintegral_mono_ae h1
    _ ≤ liminf (fun j => ∫⁻ ω, G j ω ∂μ) atTop := lintegral_liminf_le' fun j => (hG j).1
    _ ≤ liminf (fun j : ℕ => 8 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) T +
          8 * (8 : ℝ≥0∞)⁻¹ ^ j) atTop := liminf_le_liminf h2
    _ = _ := hlim2.liminf_eq

/-- Fixed-time version: `𝔼 (I_t(f) - I_t(h))² ≤ 8 𝔼 ∫_0^t ∑ᵢ (fᵢ - hᵢ)²`. -/
private lemma lintegral_elem_sub_sq_le (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (f : ElemIntegrand 𝓖 ι) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ‖f.integral B t ω - stochInt 𝓖 μ B h t ω‖ₑ ^ 2 ∂μ ≤
      8 * energy μ (fun i s ω => f.toFun i s ω - h i s ω) t :=
  (lintegral_mono fun ω => by
    rw [enorm_sq_eq]
    exact le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0 : ℝ) t) =>
      ENNReal.ofReal ((f.integral B s ω - stochInt 𝓖 μ B h s ω) ^ 2)) t ⟨ht, le_rfl⟩).trans
    (lintegral_iSup_elem_sub_le hB hh f t)

/-- If `f_k → h` for the energy on `[0, t]`, then `I_t(f_k) → I_t(h)` in `L²`. -/
private lemma tendsto_lintegral_elem_sub_sq (hB : IsBrownianFamily 𝓖 B μ)
    {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) {f : ℕ → ElemIntegrand 𝓖 ι} {t : ℝ}
    (ht : 0 ≤ t)
    (hf : Tendsto (fun k => energy μ (fun i s ω => (f k).toFun i s ω - h i s ω) t) atTop
      (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ‖(f k).integral B t ω - stochInt 𝓖 μ B h t ω‖ₑ ^ 2 ∂μ) atTop
      (𝓝 0) := by
  have h8 : Tendsto (fun k => 8 * energy μ (fun i s ω => (f k).toFun i s ω - h i s ω) t)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hf (Or.inr (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h8 (fun _ => zero_le)
    fun k => lintegral_elem_sub_sq_le hB hh (f k) ht

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- `𝔼 (X + Y)² ≤ 2 𝔼 X² + 2 𝔼 Y²`. -/
private lemma lintegral_sq_add_le {X Y : Ω → ℝ} (hX : AEMeasurable X μ) :
    ∫⁻ ω, ‖X ω + Y ω‖ₑ ^ 2 ∂μ ≤ 2 * ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ + 2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂μ := by
  rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_left' (by exact (hX.enorm.pow_const 2).const_mul 2 :
      AEMeasurable (fun ω => 2 * ‖X ω‖ₑ ^ 2) μ)]
  exact lintegral_mono fun ω => enorm_add_sq_le _ _

/-- `c a_k + c b_k → 0` if `a_k, b_k → 0`. -/
private lemma tendsto_const_mul_add {a b : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    Tendsto (fun k => c * a k + c * b k) atTop (𝓝 0) := by
  simpa using (ENNReal.Tendsto.const_mul ha (Or.inr hc)).add
    (ENNReal.Tendsto.const_mul hb (Or.inr hc))

/-- `I_t(h) ∈ L²`. -/
private lemma memLp_stochInt (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (t : ℝ) : MemLp (stochInt 𝓖 μ B h t) 2 μ := by
  rcases le_or_gt t 0 with ht | ht
  · have : stochInt 𝓖 μ B h t = fun _ => 0 := funext (stochInt_of_nonpos B h ht)
    rw [this]
    exact MemLp.zero
  set e := hh.exists_fast.choose ⌈t⌉₊
  have hk : energy μ (fun i s ω => e.toFun i s ω - h i s ω) t < ∞ :=
    ((energy_mono _ (Nat.le_ceil t)).trans (hh.exists_fast.choose_spec ⌈t⌉₊)).trans_lt
      (by finiteness)
  have h1 := lintegral_elem_sub_sq_le hB hh e ht.le
  have hIe : MemLp (e.integral B t) 2 μ := QSSEPtoKPZ.ElemIntegrand.memLp_integral hB e t (by simp)
  have hm := measurable_stochInt hB h t
  refine memLp_two_of_lintegral hm.aestronglyMeasurable (ne_top_of_le_ne_top
    (b := 2 * ∫⁻ ω, ‖stochInt 𝓖 μ B h t ω - e.integral B t ω‖ₑ ^ 2 ∂μ +
      2 * ∫⁻ ω, ‖e.integral B t ω‖ₑ ^ 2 ∂μ) ?_ ?_)
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) ?_,
      ENNReal.mul_ne_top (by norm_num) (lintegral_sq_ne_top hIe)⟩
    simp_rw [enorm_sub_rev (stochInt 𝓖 μ B h t _)]
    exact (h1.trans_lt (ENNReal.mul_lt_top (by norm_num) hk)).ne
  · have := lintegral_sq_add_le (μ := μ) (Y := fun ω => e.integral B t ω)
      (hm.aemeasurable.sub hIe.aestronglyMeasurable.aemeasurable)
    simpa using this

/-- **Identification of `I_t(h)`.** If `f_k → h` for the energy on `[0, t]` and
`I_t(f_k) → Y` in `L²`, then `I_t(h) = Y` almost surely. -/
private lemma stochInt_ae_eq_of_tendsto (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) {t : ℝ} (ht : 0 ≤ t) {f : ℕ → ElemIntegrand 𝓖 ι}
    (hf : Tendsto (fun k => energy μ (fun i s ω => (f k).toFun i s ω - h i s ω) t) atTop (𝓝 0))
    {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (hYl : Tendsto (fun k => ∫⁻ ω, ‖(f k).integral B t ω - Y ω‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    stochInt 𝓖 μ B h t =ᵐ[μ] Y := by
  have hm := measurable_stochInt hB h t
  have hbound : ∀ k, ∫⁻ ω, ‖stochInt 𝓖 μ B h t ω - Y ω‖ₑ ^ 2 ∂μ ≤
      2 * ∫⁻ ω, ‖(f k).integral B t ω - stochInt 𝓖 μ B h t ω‖ₑ ^ 2 ∂μ +
        2 * ∫⁻ ω, ‖(f k).integral B t ω - Y ω‖ₑ ^ 2 ∂μ := by
    intro k
    have hIf := (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (f k) t (p := 2)
      (by simp)).aestronglyMeasurable.aemeasurable
    have := lintegral_sq_add_le (μ := μ) (X := fun ω => stochInt 𝓖 μ B h t ω -
      (f k).integral B t ω) (Y := fun ω => (f k).integral B t ω - Y ω) (hm.aemeasurable.sub hIf)
    simp only [sub_add_sub_cancel] at this
    have hrev : ∫⁻ ω, ‖stochInt 𝓖 μ B h t ω - (f k).integral B t ω‖ₑ ^ 2 ∂μ =
        ∫⁻ ω, ‖(f k).integral B t ω - stochInt 𝓖 μ B h t ω‖ₑ ^ 2 ∂μ :=
      lintegral_congr fun ω => by rw [enorm_sub_rev]
    rwa [hrev] at this
  have hlim := tendsto_const_mul_add (tendsto_lintegral_elem_sub_sq hB hh ht hf) hYl
    (c := 2) (by norm_num)
  have h0 : ∫⁻ ω, ‖stochInt 𝓖 μ B h t ω - Y ω‖ₑ ^ 2 ∂μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  have hm2 : AEMeasurable (fun ω => ‖stochInt 𝓖 μ B h t ω - Y ω‖ₑ ^ 2) μ :=
    (hm.aemeasurable.sub hY).enorm.pow_const 2
  rw [lintegral_eq_zero_iff' hm2] at h0
  filter_upwards [h0] with ω hω
  simpa [sub_eq_zero] using hω

/-- The Itô integral of an elementary integrand is its elementary integral, for all `t`,
almost surely. -/
theorem stochInt_elem (hB : IsBrownianFamily 𝓖 B μ) (e : ElemIntegrand 𝓖 ι) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B e.toFun t ω = e.integral B t ω := by
  have hh := isItoIntegrable_elem (μ := μ) e
  refine ae_forall_eq_of_continuous (stochInt_continuous hB hh)
    (QSSEPtoKPZ.ElemIntegrand.integral_continuous hB e) fun t => ?_
  exact stochInt_ae_eq_of_tendsto hB hh t.coe_nonneg (f := fun _ => e)
    (by simp [energy, pathEnergy])
    (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB e t (p := 2)
      (by simp)).aestronglyMeasurable.aemeasurable (by simp)

omit [Countable ι] in
/-- The zero family is Itô-integrable. -/
theorem isItoIntegrable_zero : IsItoIntegrable 𝓖 μ (0 : ι → ℝ → Ω → ℝ) := by
  refine ⟨fun i => by simp, ⟨fun _ => [], fun T => ?_⟩⟩
  simp [energy, pathEnergy, ElemIntegrand.toFun_nil]

/-- The Itô integral of the zero family vanishes, for all `t`, almost surely. -/
theorem stochInt_zero (hB : IsBrownianFamily 𝓖 B μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (0 : ι → ℝ → Ω → ℝ) t ω = 0 := by
  have h0 : (0 : ι → ℝ → Ω → ℝ) = QSSEPtoKPZ.ElemIntegrand.toFun ([] : ElemIntegrand 𝓖 ι) := by
    funext i s ω
    simp [QSSEPtoKPZ.ElemIntegrand.toFun_nil]
  rw [h0]
  filter_upwards [stochInt_elem hB []] with ω hω t
  rw [hω t, QSSEPtoKPZ.ElemIntegrand.integral_nil]

/-! #### Linearity -/

omit [IsProbabilityMeasure μ] in
/-- Approximation of a sum. -/
private lemma tendsto_energy_append {h g : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    {a b : ℕ → ElemIntegrand 𝓖 ι} {T : ℝ}
    (ha : Tendsto (fun k => energy μ (fun i s ω => (a k).toFun i s ω - h i s ω) T) atTop (𝓝 0))
    (hb : Tendsto (fun k => energy μ (fun i s ω => (b k).toFun i s ω - g i s ω) T) atTop (𝓝 0)) :
    Tendsto (fun k => energy μ (fun i s ω => (a k ++ b k).toFun i s ω - (h i s ω + g i s ω)) T)
      atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_mul_add ha hb (c := 2) (by norm_num)) (fun _ => zero_le) fun k =>
    energy_add_le ((ElemIntegrand.energyMeas_toFun _).sub hh.meas) (fun i s ω => by
      rw [QSSEPtoKPZ.ElemIntegrand.toFun_append]; ring) T

set_option linter.unusedSectionVars false in
/-- The sum of two Itô-integrable families is Itô-integrable. -/
theorem IsItoIntegrable.add {h g : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    (hg : IsItoIntegrable 𝓖 μ g) : IsItoIntegrable 𝓖 μ (fun i s ω => h i s ω + g i s ω) := by
  obtain ⟨a, ha⟩ := hh.approx
  obtain ⟨b, hb⟩ := hg.approx
  exact ⟨EnergyMeas.add hh.meas hg.meas,
    ⟨fun k => a k ++ b k, fun T => tendsto_energy_append hh (ha T) (hb T)⟩⟩

/-- `I(h + g) = I(h) + I(g)`, for all `t`, almost surely. -/
theorem stochInt_add (hB : IsBrownianFamily 𝓖 B μ) {h g : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (hg : IsItoIntegrable 𝓖 μ g) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (fun i s ω => h i s ω + g i s ω) t ω =
      stochInt 𝓖 μ B h t ω + stochInt 𝓖 μ B g t ω := by
  obtain ⟨a, ha⟩ := hh.approx
  obtain ⟨b, hb⟩ := hg.approx
  have hhg := hh.add hg
  refine ae_forall_eq_of_continuous (Y := fun t ω => stochInt 𝓖 μ B h t ω +
    stochInt 𝓖 μ B g t ω) (stochInt_continuous hB hhg) ?_ fun t => ?_
  · filter_upwards [stochInt_continuous hB hh, stochInt_continuous hB hg] with ω h1 h2
    exact h1.add h2
  refine stochInt_ae_eq_of_tendsto hB hhg t.coe_nonneg (f := fun k => a k ++ b k)
    (tendsto_energy_append hh (ha t) (hb t))
    ((measurable_stochInt hB h t).add (measurable_stochInt hB g t)).aemeasurable ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_mul_add (tendsto_lintegral_elem_sub_sq hB hh t.coe_nonneg (ha t))
      (tendsto_lintegral_elem_sub_sq hB hg t.coe_nonneg (hb t)) (c := 2) (by norm_num))
    (fun _ => zero_le) fun k => ?_
  have hIa := (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (a k) t (p := 2)
    (by simp)).aestronglyMeasurable.aemeasurable
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (lintegral_sq_add_le (μ := μ)
    (X := fun ω => (a k).integral B t ω - stochInt 𝓖 μ B h t ω)
    (Y := fun ω => (b k).integral B t ω - stochInt 𝓖 μ B g t ω)
    (hIa.sub (measurable_stochInt hB h t).aemeasurable))
  simp only [QSSEPtoKPZ.ElemIntegrand.integral_append]
  rw [show ∀ x y z w : ℝ, x + y - (z + w) = (x - z) + (y - w) from fun x y z w => by ring]

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- Approximation of a constant multiple. -/
private lemma energy_smul_sub (c : ℝ) (e : ElemIntegrand 𝓖 ι) (h : ι → ℝ → Ω → ℝ) (T : ℝ) :
    energy μ (fun i s ω => (QSSEPtoKPZ.ElemIntegrand.smul c e).toFun i s ω - c * h i s ω) T =
      ‖c‖ₑ ^ 2 * energy μ (fun i s ω => e.toFun i s ω - h i s ω) T := by
  rw [← energy_const_mul]
  congr 1
  funext i s ω
  rw [QSSEPtoKPZ.ElemIntegrand.toFun_smul]
  ring

set_option linter.unusedSectionVars false in
/-- A constant multiple of an Itô-integrable family is Itô-integrable. -/
theorem IsItoIntegrable.const_mul {h : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h) (c : ℝ) :
    IsItoIntegrable 𝓖 μ (fun i s ω => c * h i s ω) := by
  obtain ⟨a, ha⟩ := hh.approx
  refine ⟨EnergyMeas.const_mul hh.meas c,
    ⟨fun k => QSSEPtoKPZ.ElemIntegrand.smul c (a k), fun T => ?_⟩⟩
  simp only [energy_smul_sub]
  simpa using ENNReal.Tendsto.const_mul (ha T) (Or.inr (by finiteness))

/-- `I(c h) = c I(h)`, for all `t`, almost surely. -/
theorem stochInt_const_mul (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (c : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (fun i s ω => c * h i s ω) t ω =
      c * stochInt 𝓖 μ B h t ω := by
  obtain ⟨a, ha⟩ := hh.approx
  have hch := hh.const_mul c
  refine ae_forall_eq_of_continuous (Y := fun t ω => c * stochInt 𝓖 μ B h t ω)
    (stochInt_continuous hB hch) ?_ fun t => ?_
  · filter_upwards [stochInt_continuous hB hh] with ω h1
    exact continuous_const.mul h1
  refine stochInt_ae_eq_of_tendsto hB hch t.coe_nonneg
    (f := fun k => QSSEPtoKPZ.ElemIntegrand.smul c (a k)) ?_
    ((measurable_stochInt hB h t).const_mul c).aemeasurable ?_
  · simp only [energy_smul_sub]
    simpa using ENNReal.Tendsto.const_mul (ha t) (Or.inr (by finiteness))
  · have := ENNReal.Tendsto.const_mul (tendsto_lintegral_elem_sub_sq hB hh t.coe_nonneg (ha t))
      (Or.inr (by finiteness : ‖c‖ₑ ^ 2 ≠ ∞))
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    refine lintegral_congr fun ω => ?_
    rw [QSSEPtoKPZ.ElemIntegrand.integral_smul, ← mul_sub, enorm_mul, mul_pow]

/-- A finite sum of Itô-integrable families is Itô-integrable. -/
theorem IsItoIntegrable.finset_sum {κ : Type*} (S : Finset κ) {h : κ → ι → ℝ → Ω → ℝ}
    (hh : ∀ k ∈ S, IsItoIntegrable 𝓖 μ (h k)) :
    IsItoIntegrable 𝓖 μ (fun i s ω => ∑ k ∈ S, h k i s ω) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isItoIntegrable_zero
  | insert a S ha ih =>
    have e : (fun i s ω => ∑ k ∈ insert a S, h k i s ω) =
        fun i s ω => h a i s ω + ∑ k ∈ S, h k i s ω := by
      funext i s ω
      rw [Finset.sum_insert ha]
    rw [e]
    exact (hh a (Finset.mem_insert_self a S)).add
      (ih fun k hk => hh k (Finset.mem_insert_of_mem hk))

/-- `I(∑_{k ∈ S} h_k) = ∑_{k ∈ S} I(h_k)`, for all `t`, almost surely. -/
theorem stochInt_finset_sum (hB : IsBrownianFamily 𝓖 B μ) {κ : Type*} (S : Finset κ)
    {h : κ → ι → ℝ → Ω → ℝ} (hh : ∀ k ∈ S, IsItoIntegrable 𝓖 μ (h k)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (fun i s ω => ∑ k ∈ S, h k i s ω) t ω =
      ∑ k ∈ S, stochInt 𝓖 μ B (h k) t ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun i s ω => ∑ k ∈ (∅ : Finset κ), h k i s ω) = 0 := by
      funext i s ω
      simp
    rw [e]
    filter_upwards [stochInt_zero hB] with ω hω t
    simp [hω t]
  | insert a S ha ih =>
    have hS : ∀ k ∈ S, IsItoIntegrable 𝓖 μ (h k) := fun k hk =>
      hh k (Finset.mem_insert_of_mem hk)
    have e : (fun i s ω => ∑ k ∈ insert a S, h k i s ω) =
        fun i s ω => h a i s ω + ∑ k ∈ S, h k i s ω := by
      funext i s ω
      rw [Finset.sum_insert ha]
    rw [e]
    filter_upwards [stochInt_add hB (hh a (Finset.mem_insert_self a S))
      (IsItoIntegrable.finset_sum S hS), ih hS] with ω h1 h2 t
    rw [h1 t, h2 t, Finset.sum_insert ha]

/-! #### Dependence on the integrand through its energy class -/

set_option linter.unusedSectionVars false in
/-- If `h` is Itô-integrable and `h'` is jointly measurable on `(0, ∞) × Ω` and has zero energy
distance to `h` on every `[0, T]` (e.g. `h' = h` at all times `s > 0`), then `h'` is
Itô-integrable. -/
theorem IsItoIntegrable.congr {h h' : ι → ℝ → Ω → ℝ} (hh : IsItoIntegrable 𝓖 μ h)
    (hmeas : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h' i p.1 p.2 else 0)
    (heq : ∀ T : ℝ, energy μ (fun i s ω => h i s ω - h' i s ω) T = 0) :
    IsItoIntegrable 𝓖 μ h' := by
  obtain ⟨a, ha⟩ := hh.approx
  refine ⟨hmeas, ⟨a, fun T => ?_⟩⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_mul_add (ha T) (tendsto_const_nhds (x := (0 : ℝ≥0∞))) (c := 2)
      (by norm_num)) (fun _ => zero_le) fun k => ?_
  have := energy_add_le (μ := μ) ((ElemIntegrand.energyMeas_toFun (a k)).sub hh.meas)
    (g := fun i s ω => h i s ω - h' i s ω)
    (F := fun i s ω => (a k).toFun i s ω - h' i s ω) (fun i s ω => by ring) T
  rwa [heq T] at this

/-- **Locality.** If two Itô-integrable families have zero energy distance on `[0, T]`, their
Itô integrals agree on `[0, T]`, almost surely. -/
theorem stochInt_congr (hB : IsBrownianFamily 𝓖 B μ) {h h' : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (hh' : IsItoIntegrable 𝓖 μ h') {T : ℝ}
    (heq : energy μ (fun i s ω => h i s ω - h' i s ω) T = 0) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ) ≤ T → stochInt 𝓖 μ B h t ω = stochInt 𝓖 μ B h' t ω := by
  obtain ⟨b, hb⟩ := hh'.approx
  refine ae_forall_le_eq_of_continuous (stochInt_continuous hB hh) (stochInt_continuous hB hh')
    fun t ht => ?_
  have h0 : energy μ (fun i s ω => h' i s ω - h i s ω) t = 0 := by
    rw [energy_sub_comm]
    exact le_antisymm ((energy_mono _ ht).trans heq.le) zero_le
  refine stochInt_ae_eq_of_tendsto hB hh t.coe_nonneg (f := b) ?_
    (measurable_stochInt hB h' t).aemeasurable
    (tendsto_lintegral_elem_sub_sq hB hh' t.coe_nonneg (hb t))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_mul_add (hb t) (tendsto_const_nhds (x := (0 : ℝ≥0∞))) (c := 2)
      (by norm_num)) (fun _ => zero_le) fun k => ?_
  have := energy_add_le (μ := μ) ((ElemIntegrand.energyMeas_toFun (b k)).sub hh'.meas)
    (g := fun i s ω => h' i s ω - h i s ω)
    (F := fun i s ω => (b k).toFun i s ω - h i s ω) (fun i s ω => by ring) t
  rwa [h0] at this

/-! #### Isometry, martingale property, brackets -/

/-- `I_t(f_k) I_t(g_k) - ∫_0^t ∑ᵢ f_k g_k → I_t(h) I_t(g) - ∫_0^t ∑ᵢ hᵢ gᵢ` in `L¹`. -/
private lemma tendsto_mul_sub_bracket (hB : IsBrownianFamily 𝓖 B μ) {h g : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (hg : IsItoIntegrable 𝓖 μ g) {a b : ℕ → ElemIntegrand 𝓖 ι}
    (ha : ∀ T : ℝ, Tendsto (fun k => energy μ (fun i s ω => (a k).toFun i s ω - h i s ω) T)
      atTop (𝓝 0))
    (hb : ∀ T : ℝ, Tendsto (fun k => energy μ (fun i s ω => (b k).toFun i s ω - g i s ω) T)
      atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => ∫⁻ ω, ‖((a k).integral B t ω * (b k).integral B t ω -
        pathBracket (a k).toFun (b k).toFun t ω) -
      (stochInt 𝓖 μ B h t ω * stochInt 𝓖 μ B g t ω - pathBracket h g t ω)‖ₑ ∂μ)
      atTop (𝓝 0) := by
  have hIa : ∀ k, AEMeasurable ((a k).integral B t) μ := fun k =>
    (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (a k) t (p := 2)
      (by simp)).aestronglyMeasurable.aemeasurable
  have hIb : ∀ k, AEMeasurable ((b k).integral B t) μ := fun k =>
    (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (b k) t (p := 2)
      (by simp)).aestronglyMeasurable.aemeasurable
  have h1 := tendsto_lintegral_mul_sub hIa hIb (measurable_stochInt hB h t).aemeasurable
    (measurable_stochInt hB g t).aemeasurable (lintegral_sq_ne_top (memLp_stochInt hB hh t))
    (lintegral_sq_ne_top (memLp_stochInt hB hg t)) (tendsto_lintegral_elem_sub_sq hB hh ht (ha t))
    (tendsto_lintegral_elem_sub_sq hB hg ht (hb t))
  have h2 := tendsto_lintegral_pathBracket_sub (μ := μ) (fs := fun k => (a k).toFun)
    (gs := fun k => (b k).toFun) (fun k => ElemIntegrand.energyMeas_toFun _)
    (fun k => ElemIntegrand.energyMeas_toFun _) hh.meas hg.meas ht
    (fun k => (energy_elem_lt_top _ t).ne) (fun k => (energy_elem_lt_top _ t).ne)
    (hh.energy_lt_top t).ne (hg.energy_lt_top t).ne (ha t) (hb t)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h1.add h2)
    (fun _ => zero_le) fun k => ?_
  calc _ ≤ ∫⁻ ω, (‖(a k).integral B t ω * (b k).integral B t ω -
          stochInt 𝓖 μ B h t ω * stochInt 𝓖 μ B g t ω‖ₑ +
        ‖pathBracket (a k).toFun (b k).toFun t ω - pathBracket h g t ω‖ₑ) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [show ∀ x y z w : ℝ, (x - y) - (z - w) = (x - z) - (y - w) from
          fun x y z w => by ring]
        exact enorm_sub_le
    _ = _ := lintegral_add_left' (((hIa k).mul (hIb k)).sub
          ((measurable_stochInt hB h t).mul (measurable_stochInt hB g t)).aemeasurable).enorm _

/-- Core of the cross bracket, with `pathBracket`. -/
private lemma condExp_mul_core (hB : IsBrownianFamily 𝓖 B μ) {h g : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (hg : IsItoIntegrable 𝓖 μ g) {s t : ℝ≥0} (hst : s ≤ t) :
    μ[fun ω => stochInt 𝓖 μ B h t ω * stochInt 𝓖 μ B g t ω - pathBracket h g t ω | 𝓖 s] =ᵐ[μ]
      fun ω => stochInt 𝓖 μ B h s ω * stochInt 𝓖 μ B g s ω - pathBracket h g s ω := by
  obtain ⟨a, ha⟩ := hh.approx
  obtain ⟨b, hb⟩ := hg.approx
  refine condExp_ae_eq_of_tendsto s
    (Xs := fun k ω => (a k).integral B t ω * (b k).integral B t ω -
      pathBracket (a k).toFun (b k).toFun t ω)
    (Zs := fun k ω => (a k).integral B s ω * (b k).integral B s ω -
      pathBracket (a k).toFun (b k).toFun s ω) (fun k => ?_) ?_ ?_
    (fun k => QSSEPtoKPZ.ElemIntegrand.condExp_integral_mul hB (a k) (b k) hst)
    (tendsto_mul_sub_bracket hB hh hg ha hb t.coe_nonneg)
    (tendsto_mul_sub_bracket hB hh hg ha hb s.coe_nonneg)
  · exact ((QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (a k) t (p := 2) (by simp)).integrable_mul
      (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (b k) t (p := 2) (by simp))).sub
      (QSSEPtoKPZ.ElemIntegrand.integrable_bracket (a k) (b k) t.coe_nonneg)
  · exact ((memLp_stochInt hB hh t).integrable_mul (memLp_stochInt hB hg t)).sub
      (integrable_pathBracket hh.meas hg.meas t.coe_nonneg (hh.energy_lt_top t).ne
        (hg.energy_lt_top t).ne)
  · exact (((measurable_stochInt hB h s).mul (measurable_stochInt hB g s)).sub
      (measurable_pathBracket hh.meas hg.meas s.coe_nonneg)).aestronglyMeasurable

/-- **Itô isometry**, in `[0, ∞]`: `𝔼[I_t(h)²] = 𝔼 ∫_0^t ∑ᵢ hᵢ(s)² ds` (both sides vanish for
`t ≤ 0`). -/
theorem lintegral_stochInt_sq (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (stochInt 𝓖 μ B h t ω ^ 2) ∂μ = energy μ h t := by
  rcases le_or_gt t 0 with ht | ht
  · simp [stochInt_of_nonpos B h ht, energy, pathEnergy, Set.Ioc_eq_empty (not_lt.2 ht)]
  obtain ⟨tn, rfl⟩ : ∃ tn : ℝ≥0, (tn : ℝ) = t := ⟨t.toNNReal, Real.coe_toNNReal t ht.le⟩
  have hc := condExp_mul_core hB hh hh (zero_le (a := tn))
  have hint := integral_congr_ae hc
  rw [integral_condExp (𝓖.le 0)] at hint
  have hpb0 : ∀ ω, pathBracket h h 0 ω = 0 := fun ω => by
    simp [pathBracket]
  have hI2 := memLp_stochInt hB hh tn
  have hP := integrable_pathBracket hh.meas hh.meas tn.coe_nonneg (hh.energy_lt_top tn).ne
    (hh.energy_lt_top tn).ne
  have h3 : ∫ ω, (stochInt 𝓖 μ B h tn ω * stochInt 𝓖 μ B h tn ω - pathBracket h h tn ω) ∂μ
      = 0 := by
    refine hint.trans ?_
    simp [hpb0, stochInt_of_nonpos B h le_rfl]
  rw [integral_sub (f := fun ω => stochInt 𝓖 μ B h tn ω * stochInt 𝓖 μ B h tn ω)
    (hI2.integrable_mul hI2) hP, sub_eq_zero] at h3
  have hpb : ∀ᵐ ω ∂μ, ENNReal.ofReal (pathBracket h h tn ω) = pathEnergy h tn ω := by
    filter_upwards [ae_pathEnergy_ne_top hh.meas (hh.energy_lt_top tn).ne] with ω hω
    exact ofReal_pathBracket_self hh.meas tn.coe_nonneg ω hω
  have hPnn : 0 ≤ᵐ[μ] pathBracket h h tn := ae_of_all _ fun ω =>
    intervalIntegral.integral_nonneg tn.coe_nonneg fun r _ => tsum_nonneg fun i => mul_self_nonneg _
  rw [energy, ← lintegral_congr_ae hpb, ← ofReal_integral_eq_lintegral_ofReal hP hPnn,
    ← ofReal_integral_eq_lintegral_ofReal hI2.integrable_sq (ae_of_all _ fun ω => sq_nonneg _)]
  simp_rw [sq]
  exact congrArg ENNReal.ofReal h3

/-- **Martingale property and bracket.** For every `T`, `I(h)` is a continuous `L²` martingale on
`[0, T]` for `𝓖`, with bracket `⟨I(h)⟩_t = ∫_0^t ∑ᵢ hᵢ(s)² ds`. (The bracket contains the
isometry; the series and the time integral converge almost surely, so the Lean conventions for
non-summable series and non-integrable functions play no role.) -/
theorem hasBracket_stochInt (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (T : ℝ) :
    HasBracket T 𝓖 (stochInt 𝓖 μ B h) (fun t ω => ∫ s in (0 : ℝ)..t, ∑' i, h i s ω ^ 2) μ := by
  obtain ⟨a, ha⟩ := hh.approx
  have hL1 : ∀ t : ℝ≥0, Tendsto (fun k => ∫⁻ ω,
      ‖(a k).integral B t ω - stochInt 𝓖 μ B h t ω‖ₑ ∂μ) atTop (𝓝 0) := fun t =>
    tendsto_lintegral_enorm_of_sq (Z := fun k ω => (a k).integral B t ω - stochInt 𝓖 μ B h t ω)
      (fun k => ((QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (a k) t (p := 2)
        (by simp)).aestronglyMeasurable.aemeasurable).sub
        (measurable_stochInt hB h t).aemeasurable)
      (tendsto_lintegral_elem_sub_sq hB hh t.coe_nonneg (ha t))
  have hsq : ∀ t ω, ∫ s in (0 : ℝ)..t, ∑' i, h i s ω ^ 2 = pathBracket h h t ω := fun t ω => by
    simp only [pathBracket, sq]
  refine
    { cont := ?_
      memLp := fun t _ => memLp_stochInt hB hh t
      condExp := fun s t hst _ => ?_
      integrable_bracket := fun t _ => ?_
      zero := ae_of_all _ fun ω => by simp
      mono := ?_
      cont_bracket := ?_
      condExp_sq := fun s t hst _ => ?_ }
  · filter_upwards [ae_good hB hh] with ω hω
    exact hω.1.continuousOn
  · exact condExp_ae_eq_of_tendsto s (Xs := fun k => (a k).integral B t)
      (Zs := fun k => (a k).integral B s)
      (fun k => (QSSEPtoKPZ.ElemIntegrand.memLp_integral hB (a k) t (p := 2)
        (by simp)).integrable one_le_two)
      ((memLp_stochInt hB hh t).integrable one_le_two)
      (measurable_stochInt hB h s).aestronglyMeasurable
      (fun k => (QSSEPtoKPZ.ElemIntegrand.hasBracket_integral hB (a k) t).condExp s t hst le_rfl)
      (hL1 t) (hL1 s)
  · simp_rw [hsq]
    exact integrable_pathBracket hh.meas hh.meas t.coe_nonneg (hh.energy_lt_top t).ne
      (hh.energy_lt_top t).ne
  · rcases lt_or_ge T 0 with hT | hT
    · exact ae_of_all _ fun ω x hx => absurd (hx.1.trans hx.2) (not_le.2 hT)
    filter_upwards [ae_pathEnergy_ne_top hh.meas (hh.energy_lt_top T).ne] with ω hω
    have hI : MeasureTheory.IntegrableOn (fun s => ∑' i, h i s ω ^ 2) (Set.Ioc 0 T) := by
      simpa only [sq] using (integrableOn_tsum_mul hh.meas hh.meas T ω hω hω).1
    intro x hx y hy hxy
    have ix : IntervalIntegrable (fun s => ∑' i, h i s ω ^ 2) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2
        (hI.mono_set (Set.Ioc_subset_Ioc_right hx.2))
    have iy : IntervalIntegrable (fun s => ∑' i, h i s ω ^ 2) volume x y :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).2
        (hI.mono_set (Set.Ioc_subset_Ioc hx.1 hy.2))
    simp only
    rw [← intervalIntegral.integral_add_adjacent_intervals ix iy]
    exact le_add_of_nonneg_right
      (intervalIntegral.integral_nonneg hxy fun r _ => tsum_nonneg fun i => sq_nonneg _)
  · rcases lt_or_ge T 0 with hT | hT
    · exact ae_of_all _ fun ω x hx => absurd (hx.1.trans hx.2) (not_le.2 hT)
    filter_upwards [ae_pathEnergy_ne_top hh.meas (hh.energy_lt_top T).ne] with ω hω
    have hI : MeasureTheory.IntegrableOn (fun s => ∑' i, h i s ω ^ 2) (Set.Ioc 0 T) := by
      simpa only [sq] using (integrableOn_tsum_mul hh.meas hh.meas T ω hω hω).1
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
      (f := fun s => ∑' i, h i s ω ^ 2) (by
        rw [Set.uIcc_of_le hT, integrableOn_Icc_iff_integrableOn_Ioc]
        exact hI)
    rwa [Set.uIcc_of_le hT] at this
  · simp only [sq]
    exact condExp_mul_core hB hh hh hst

/-- **Cross bracket.** `⟨I(h), I(g)⟩_t = ∫_0^t ∑ᵢ hᵢ(s) gᵢ(s) ds`: for `s ≤ t`,
`𝔼[I_t(h) I_t(g) - ∫_0^t ∑ᵢ hᵢ gᵢ | 𝓖_s] = I_s(h) I_s(g) - ∫_0^s ∑ᵢ hᵢ gᵢ` almost surely. (With
`h`, `g` supported by single indices `i ≠ j` this says `⟨∫ f dBᵢ, ∫ g dBⱼ⟩ = 0`.) -/
theorem condExp_stochInt_mul (hB : IsBrownianFamily 𝓖 B μ) {h g : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (hg : IsItoIntegrable 𝓖 μ g) {s t : ℝ≥0} (hst : s ≤ t) :
    μ[fun ω => stochInt 𝓖 μ B h t ω * stochInt 𝓖 μ B g t ω -
        ∫ r in (0 : ℝ)..t, ∑' i, h i r ω * g i r ω | 𝓖 s] =ᵐ[μ]
      fun ω => stochInt 𝓖 μ B h s ω * stochInt 𝓖 μ B g s ω -
        ∫ r in (0 : ℝ)..s, ∑' i, h i r ω * g i r ω :=
  condExp_mul_core hB hh hg hst

/-- **Doob's inequality for the Itô integral:**
`𝔼[sup_{t ∈ [0, T]} I_t(h)²] ≤ 4 𝔼 ∫_0^T ∑ᵢ hᵢ(s)² ds`. -/
theorem lintegral_iSup_stochInt_sq_le (hB : IsBrownianFamily 𝓖 B μ) {h : ι → ℝ → Ω → ℝ}
    (hh : IsItoIntegrable 𝓖 μ h) (T : ℝ) :
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (stochInt 𝓖 μ B h t ω ^ 2) ∂μ ≤
      4 * energy μ h T := by
  have := (hasBracket_stochInt hB hh T).toIsCL2Mart.lintegral_iSup_sq_le
  rw [lintegral_stochInt_sq hB hh T] at this
  exact this.2

/-- **`L²` convergence, uniformly in time.** If `h_k → g` for the energy on `[0, T]`, then
`𝔼[sup_{t ∈ [0, T]} (I_t(h_k) - I_t(g))²] → 0`. -/
theorem tendsto_lintegral_iSup_stochInt_sub (hB : IsBrownianFamily 𝓖 B μ)
    {h : ℕ → ι → ℝ → Ω → ℝ} {g : ι → ℝ → Ω → ℝ} (hh : ∀ k, IsItoIntegrable 𝓖 μ (h k))
    (hg : IsItoIntegrable 𝓖 μ g) {T : ℝ}
    (hlim : Tendsto (fun k => energy μ (fun i s ω => h k i s ω - g i s ω) T) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((stochInt 𝓖 μ B (h k) t ω - stochInt 𝓖 μ B g t ω) ^ 2) ∂μ)
      atTop (𝓝 0) := by
  have e : ∀ k, (fun i s ω => h k i s ω + (-1) * g i s ω) = fun i s ω => h k i s ω - g i s ω :=
    fun k => by funext i s ω; ring
  have hk : ∀ k, IsItoIntegrable 𝓖 μ (fun i s ω => h k i s ω - g i s ω) := fun k => by
    have := (hh k).add (hg.const_mul (-1))
    rwa [e k] at this
  have hlin : ∀ k, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, stochInt 𝓖 μ B (fun i s ω => h k i s ω - g i s ω) t ω =
      stochInt 𝓖 μ B (h k) t ω - stochInt 𝓖 μ B g t ω := fun k => by
    have h1 := stochInt_add hB (hh k) (hg.const_mul (-1)) (B := B)
    rw [e k] at h1
    filter_upwards [h1, stochInt_const_mul hB hg (-1)] with ω h1 h2 t
    rw [h1 t, h2 t]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun k => 4 * energy μ (fun i s ω => h k i s ω - g i s ω) T)
    (by simpa using ENNReal.Tendsto.const_mul hlim (Or.inr (by norm_num)))
    (fun _ => zero_le) fun k => ?_
  calc _ = ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal
        (stochInt 𝓖 μ B (fun i s ω => h k i s ω - g i s ω) t ω ^ 2) ∂μ := by
        refine lintegral_congr_ae ((hlin k).mono fun ω hω => ?_)
        refine iSup_congr fun t => iSup_congr fun ht => ?_
        rw [← Real.coe_toNNReal t ht.1, hω]
    _ ≤ _ := lintegral_iSup_stochInt_sq_le hB (hk k) T

end QSSEPtoKPZ
