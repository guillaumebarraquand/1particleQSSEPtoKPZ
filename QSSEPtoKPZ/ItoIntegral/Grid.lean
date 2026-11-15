/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Elementary

/-!
# Energy estimates and left-point step approximations (package C, task C4)

Auxiliary material for `ItoIntegral/Integrands.lean` and `ItoIntegral/Riemann.lean`.

* Estimates on the energy `𝔼 ∫_0^T ∑ᵢ hᵢ(s)² ds`: monotonicity in the horizon, comparison,
  `energy (a + b) ≤ 2 energy a + 2 energy b`, and dominated convergence
  (`itoEnergy_tendsto_zero_of_dominated`).
* `itoGridStep ξ δ N`: the left-point step function `∑_{k < N} ξ_k 𝟙_{(kδ, (k+1)δ]}` on the grid
  `kδ`; its value at `s > 0` is `ξ_k` with `k = ⌈s/δ⌉ - 1`, and it converges to `f(s)` when
  `ξ_k = f(kδ)`, `δ → 0` and `f` is left-continuous at `s` (`tendsto_itoGridStep`).
* `itoGridElem i δ N ξ`: the same step function, as an elementary integrand on the index `i`;
  if its values converge pointwise on `(0, T]` to a bounded `f`, its energy distance to
  `f 𝟙_{j = i}` on `[0, T]` tends to `0` (`tendsto_energy_itoGridElem_sub`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*}

/-! ### Energy estimates -/

/-- `‖x‖ₑ² = x²` in `[0, ∞]`. -/
lemma itoEnergy_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- For a square-summable real family, `∑ᵢ ‖xᵢ‖ₑ² = ∑ᵢ xᵢ²` in `[0, ∞]`. -/
lemma itoEnergy_tsum_enorm_sq {x : ι → ℝ} (hx : Summable fun i => x i ^ 2) :
    ∑' i, ‖x i‖ₑ ^ 2 = ENNReal.ofReal (∑' i, x i ^ 2) := by
  simp_rw [itoEnergy_enorm_sq]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx).symm

/-- `∑ⱼ ‖x 𝟙_{j = i}‖ₑ² = ‖x‖ₑ²`. -/
lemma itoEnergy_tsum_enorm_sq_ite [DecidableEq ι] (i : ι) (x : ℝ) :
    ∑' j : ι, ‖(if j = i then x else 0)‖ₑ ^ 2 = ‖x‖ₑ ^ 2 := by
  rw [← tsum_ite_eq i (fun _ => ‖x‖ₑ ^ 2)]
  congr 1
  funext j
  split_ifs <;> simp

/-- Only times `s > 0` enter the path energy. -/
lemma itoEnergy_pathEnergy_eq_pos (h : ι → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    pathEnergy h T ω =
      ∫⁻ s in Set.Ioc 0 T, ∑' i, ‖(if 0 < s then h i s ω else 0)‖ₑ ^ 2 := by
  unfold pathEnergy
  refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  simp [hs.1]

/-- Joint measurability of `(s, ω) ↦ ∑ᵢ hᵢ(s, ω)²` (restricted to `s > 0`). -/
lemma itoEnergy_measurable_tsum [Countable ι] {h : ι → ℝ → Ω → ℝ}
    (hm : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h i p.1 p.2 else 0) :
    Measurable fun p : ℝ × Ω => ∑' i, ‖(if 0 < p.1 then h i p.1 p.2 else 0)‖ₑ ^ 2 :=
  Measurable.tsum fun i => ((hm i).enorm).pow_const 2

/-- Measurability of the path energy `ω ↦ ∫_0^T ∑ᵢ hᵢ(s, ω)² ds`. -/
lemma itoEnergy_measurable_pathEnergy [Countable ι] {h : ι → ℝ → Ω → ℝ}
    (hm : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then h i p.1 p.2 else 0) (T : ℝ) :
    Measurable (pathEnergy h T) := by
  have := (itoEnergy_measurable_tsum hm).lintegral_prod_left' (μ := volume.restrict (Set.Ioc 0 T))
  convert this using 1
  funext ω
  exact itoEnergy_pathEnergy_eq_pos h T ω

/-- The energy is nondecreasing in the horizon. -/
lemma itoEnergy_mono_horizon (μ : Measure Ω) (h : ι → ℝ → Ω → ℝ) {T T' : ℝ} (hTT' : T ≤ T') :
    energy μ h T ≤ energy μ h T' :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Ioc_subset_Ioc_right hTT')

/-- Comparison: a pointwise bound `∑ᵢ hᵢ² ≤ c ∑ᵢ gᵢ²` on `(0, T]` gives
`energy h ≤ c energy g`. -/
lemma itoEnergy_le_mul {μ : Measure Ω} {h g : ι → ℝ → Ω → ℝ} {T : ℝ} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hle : ∀ ω (s : ℝ), 0 < s → s ≤ T → ∑' i, ‖h i s ω‖ₑ ^ 2 ≤ c * ∑' i, ‖g i s ω‖ₑ ^ 2) :
    energy μ h T ≤ c * energy μ g T := by
  unfold energy pathEnergy
  rw [← lintegral_const_mul' _ _ hc]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ hc]
  exact setLIntegral_mono' measurableSet_Ioc fun s hs => hle ω s hs.1 hs.2

/-- `energy (a + b) ≤ 2 energy a + 2 energy b`, when `a` is jointly measurable on
`(0, ∞) × Ω`. -/
lemma itoEnergy_add_le [Countable ι] {μ : Measure Ω} {a b : ι → ℝ → Ω → ℝ}
    (ha : ∀ i, Measurable fun p : ℝ × Ω => if 0 < p.1 then a i p.1 p.2 else 0) (T : ℝ) :
    energy μ (fun i s ω => a i s ω + b i s ω) T ≤ 2 * energy μ a T + 2 * energy μ b T := by
  have hpt : ∀ x y : ℝ, ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
    intro x y
    rw [itoEnergy_enorm_sq, itoEnergy_enorm_sq, itoEnergy_enorm_sq, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])
  have hsum : ∀ ω s, ∑' i, ‖a i s ω + b i s ω‖ₑ ^ 2 ≤
      2 * ∑' i, ‖a i s ω‖ₑ ^ 2 + 2 * ∑' i, ‖b i s ω‖ₑ ^ 2 := by
    intro ω s
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun i => hpt _ _
  have hPE : ∀ ω, pathEnergy (fun i s ω => a i s ω + b i s ω) T ω ≤
      2 * pathEnergy a T ω + 2 * pathEnergy b T ω := by
    intro ω
    have hm : Measurable fun s => 2 * ∑' i, ‖(if 0 < s then a i s ω else 0)‖ₑ ^ 2 :=
      ((itoEnergy_measurable_tsum ha).comp measurable_prodMk_right).const_mul 2
    calc pathEnergy (fun i s ω => a i s ω + b i s ω) T ω
        ≤ ∫⁻ s in Set.Ioc 0 T, (2 * ∑' i, ‖(if 0 < s then a i s ω else 0)‖ₑ ^ 2 +
            2 * ∑' i, ‖b i s ω‖ₑ ^ 2) := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          simpa [hs.1] using hsum ω s
      _ = 2 * pathEnergy a T ω + 2 * pathEnergy b T ω := by
          rw [lintegral_add_left hm, lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num), itoEnergy_pathEnergy_eq_pos a]
          rfl
  unfold energy
  calc ∫⁻ ω, pathEnergy (fun i s ω => a i s ω + b i s ω) T ω ∂μ
      ≤ ∫⁻ ω, 2 * pathEnergy a T ω + 2 * pathEnergy b T ω ∂μ := lintegral_mono hPE
    _ = _ := by
        rw [lintegral_add_left ((itoEnergy_measurable_pathEnergy ha T).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

/-- **Dominated convergence for the energy.** If the families `D n` are jointly measurable on
`(0, ∞) × Ω`, `∑ᵢ (D n)ᵢ(s, ω)² ≤ C` on `(0, T]` and `∑ᵢ (D n)ᵢ(s, ω)² → 0` for every
`s ∈ (0, T]` and `ω`, then `energy (D n) T → 0`. -/
theorem itoEnergy_tendsto_zero_of_dominated [Countable ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : ℕ → ι → ℝ → Ω → ℝ} {T : ℝ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hm : ∀ n i, Measurable fun p : ℝ × Ω => if 0 < p.1 then D n i p.1 p.2 else 0)
    (hbd : ∀ n ω (s : ℝ), 0 < s → s ≤ T → ∑' i, ‖D n i s ω‖ₑ ^ 2 ≤ C)
    (hlim : ∀ ω (s : ℝ), 0 < s → s ≤ T →
      Tendsto (fun n => ∑' i, ‖D n i s ω‖ₑ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => energy μ (D n) T) atTop (𝓝 0) := by
  set Ψ : ℕ → ℝ × Ω → ℝ≥0∞ :=
    fun n p => ∑' i, ‖(if 0 < p.1 then D n i p.1 p.2 else 0)‖ₑ ^ 2 with hΨ
  have hΨm : ∀ n, Measurable (Ψ n) := fun n => itoEnergy_measurable_tsum (hm n)
  have hΨs : ∀ n ω s, s ∈ Set.Ioc 0 T → Ψ n (s, ω) = ∑' i, ‖D n i s ω‖ₑ ^ 2 := by
    intro n ω s hs
    simp [hΨ, hs.1]
  have hvol : volume (Set.Ioc 0 T) ≠ ∞ := by simp [Real.volume_Ioc]
  have hin : ∀ ω, Tendsto (fun n => ∫⁻ s in Set.Ioc 0 T, Ψ n (s, ω)) atTop (𝓝 0) := by
    intro ω
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Ioc 0 T))
      (F := fun n s => Ψ n (s, ω)) (f := fun _ => 0) (fun _ => C)
      (fun n => (hΨm n).comp measurable_prodMk_right)
      (fun n => ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => by
        show Ψ n (s, ω) ≤ C
        rw [hΨs n ω s hs]; exact hbd n ω s hs.1 hs.2)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top hC (by simp))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => by
        simp only [hΨs _ ω s hs]; exact hlim ω s hs.1 hs.2)
    simpa using this
  have hE : ∀ n, energy μ (D n) T = ∫⁻ ω, (∫⁻ s in Set.Ioc 0 T, Ψ n (s, ω)) ∂μ :=
    fun n => lintegral_congr fun ω => itoEnergy_pathEnergy_eq_pos (D n) T ω
  simp_rw [hE]
  have := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun n ω => ∫⁻ s in Set.Ioc 0 T, Ψ n (s, ω)) (f := fun _ => 0)
    (fun _ => C * volume (Set.Ioc 0 T))
    (fun n => (hΨm n).lintegral_prod_left')
    (fun n => ae_of_all _ fun ω =>
      (setLIntegral_mono' measurableSet_Ioc fun s hs =>
        (hΨs n ω s hs).trans_le (hbd n ω s hs.1 hs.2)).trans_eq (setLIntegral_const _ _))
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hvol) (measure_ne_top _ _))
    (ae_of_all _ hin)
  simpa using this

/-! ### Left-point step functions on a grid -/

/-- The left-point step function `∑_{k < N} ξ_k 𝟙_{(kδ, (k+1)δ]}(s)` on the grid `kδ`. -/
def itoGridStep (ξ : ℕ → Ω → ℝ) (δ : ℝ) (N : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, if (k : ℝ) * δ < s ∧ s ≤ ((k : ℝ) + 1) * δ then ξ k ω else 0

/-- For `δ, s > 0`, `s ∈ (kδ, (k+1)δ]` iff `k = ⌈s/δ⌉ - 1`. -/
lemma itoGridStep_cell_iff {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (k : ℕ) :
    ((k : ℝ) * δ < s ∧ s ≤ ((k : ℝ) + 1) * δ) ↔ k = ⌈s / δ⌉₊ - 1 := by
  have hpos : 0 < ⌈s / δ⌉₊ := Nat.ceil_pos.2 (div_pos hs hδ)
  rw [← lt_div_iff₀ hδ, ← div_le_iff₀ hδ]
  constructor
  · rintro ⟨h1, h2⟩
    have : ⌈s / δ⌉₊ = k + 1 :=
      (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2 ⟨by simpa using h1, by push_cast; exact h2⟩
    omega
  · intro hk
    have := (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).1 (by omega : ⌈s / δ⌉₊ = k + 1)
    exact ⟨by simpa using this.1, by exact_mod_cast this.2⟩

/-- The step function vanishes unless `δ > 0` and `s > 0`. -/
lemma itoGridStep_eq_zero {ξ : ℕ → Ω → ℝ} {δ : ℝ} {N : ℕ} {s : ℝ} (h : ¬ (0 < δ ∧ 0 < s))
    (ω : Ω) : itoGridStep ξ δ N s ω = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [ite_eq_right_iff]
  rintro ⟨h1, h2⟩
  exfalso
  apply h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hδ : 0 < δ := by nlinarith
  exact ⟨hδ, by nlinarith⟩

/-- The value of the step function at `s > 0`: `ξ_k` with `k = ⌈s/δ⌉ - 1`, if `k < N`. -/
lemma itoGridStep_eq {ξ : ℕ → Ω → ℝ} {δ : ℝ} {N : ℕ} {s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (ω : Ω) :
    itoGridStep ξ δ N s ω = if ⌈s / δ⌉₊ - 1 < N then ξ (⌈s / δ⌉₊ - 1) ω else 0 := by
  unfold itoGridStep
  simp only [itoGridStep_cell_iff hδ hs, Finset.sum_ite_eq', Finset.mem_range]

/-- A bound on the coefficients bounds the step function. -/
lemma abs_itoGridStep_le {ξ : ℕ → Ω → ℝ} {C : ℝ} (hξ : ∀ k ω, |ξ k ω| ≤ C) (δ : ℝ) (N : ℕ)
    (s : ℝ) (ω : Ω) : |itoGridStep ξ δ N s ω| ≤ |C| := by
  by_cases h : 0 < δ ∧ 0 < s
  · rw [itoGridStep_eq h.1 h.2]
    split_ifs
    · exact (hξ _ _).trans (le_abs_self C)
    · simp
  · rw [itoGridStep_eq_zero h]
    simp

/-- Joint measurability of the step function. -/
lemma measurable_itoGridStep {ξ : ℕ → Ω → ℝ} (hξ : ∀ k, Measurable (ξ k)) (δ : ℝ) (N : ℕ) :
    Measurable fun p : ℝ × Ω => itoGridStep ξ δ N p.1 p.2 := by
  unfold itoGridStep
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.ite ?_ ((hξ k).comp measurable_snd) measurable_const
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

/-- **Convergence of left-point step functions.** If `δ_n → 0⁺`, `s ≤ N_n δ_n` eventually, and
`r ↦ f(r, ω)` is left-continuous at `s > 0`, then the step functions with coefficients
`φ(f(kδ_n, ω))` converge at `s` to `φ(f(s, ω))`, for every continuous `φ`. -/
lemma tendsto_itoGridStep {f : ℝ → Ω → ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) {δ : ℕ → ℝ}
    {N : ℕ → ℕ} {s : ℝ} {ω : Ω} (hs : 0 < s) (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hN : ∀ᶠ n in atTop, s ≤ N n * δ n)
    (hlc : ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s) :
    Tendsto (fun n => itoGridStep (fun k ω => φ (f (k * δ n) ω)) (δ n) (N n) s ω) atTop
      (𝓝 (φ (f s ω))) := by
  set x : ℕ → ℝ := fun n => ((⌈s / δ n⌉₊ - 1 : ℕ) : ℝ) * δ n with hx
  have hcell : ∀ᶠ n in atTop, x n < s ∧ s ≤ x n + δ n := hδ.mono fun n hn => by
    have := (itoGridStep_cell_iff hn hs (⌈s / δ n⌉₊ - 1)).2 rfl
    exact ⟨this.1, by simp only [hx]; linarith [this.2]⟩
  have hxl : Tendsto x atTop (𝓝[≤] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hcell.mono fun n hn => hn.1.le⟩
    have hlow : Tendsto (fun n => s - δ n) atTop (𝓝 s) := by
      simpa using (tendsto_const_nhds (x := s)).sub hδ0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
      (hcell.mono fun n hn => by linarith [hn.2]) (hcell.mono fun n hn => hn.1.le)
  have hlim := hφ.continuousAt.tendsto.comp (hlc.tendsto.comp hxl)
  refine hlim.congr' ?_
  filter_upwards [hδ, hN, hcell] with n hn hNn hc
  have hk : ⌈s / δ n⌉₊ - 1 < N n := by
    have : (((⌈s / δ n⌉₊ - 1 : ℕ)) : ℝ) < N n := by
      by_contra hcon
      replace hcon := not_lt.1 hcon
      have : (N n : ℝ) * δ n ≤ x n := by
        simp only [hx]; exact mul_le_mul_of_nonneg_right hcon hn.le
      linarith [hc.1]
    exact_mod_cast this
  rw [itoGridStep_eq hn hs]
  simp only [hk, ↓reduceIte]
  rfl

/-- `((List.range N).map g).sum = ∑_{k < N} g k`. -/
lemma itoGrid_list_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ((List.range N).map g).sum = ∑ k ∈ Finset.range N, g k := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

/-! ### The step function as an elementary integrand -/

variable {𝓖 : Filtration ℝ≥0 mΩ}

/-- An adapted process sampled at the grid point `kδ` is `𝓖_{kδ}`-measurable. -/
lemma itoGrid_measurable_point {f : ℝ → Ω → ℝ} (hfa : ∀ t : ℝ≥0, Measurable[𝓖 t] (f t))
    (δ : ℝ≥0) (k : ℕ) : Measurable[𝓖 ((k : ℝ≥0) * δ)] (f (k * (δ : ℝ))) := by
  have := hfa ((k : ℝ≥0) * δ)
  rwa [NNReal.coe_mul, NNReal.coe_natCast] at this

/-- The elementary integrand `∑_{k < N} ξ_k 𝟙_{(kδ, (k+1)δ]}(s) e_i` (with `ξ_k` bounded and
`𝓖_{kδ}`-measurable). -/
def itoGridElem (i : ι) (δ : ℝ≥0) (N : ℕ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ k : ℕ, Measurable[𝓖 ((k : ℝ≥0) * δ)] (ξ k)) (C : ℝ) (hC : ∀ k ω, |ξ k ω| ≤ C) :
    ElemIntegrand 𝓖 ι :=
  (List.range N).map fun k : ℕ =>
    { a := (k : ℝ≥0) * δ
      b := ((k : ℝ≥0) + 1) * δ
      le := by gcongr; exact le_self_add
      i := i
      ξ := ξ k
      meas := hξ k
      bdd := ⟨C, hC k⟩ }

/-- The family represented by `itoGridElem i δ N ξ` is the step function on the index `i`. -/
lemma itoGridElem_toFun [DecidableEq ι] (i : ι) (δ : ℝ≥0) (N : ℕ) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ k : ℕ, Measurable[𝓖 ((k : ℝ≥0) * δ)] (ξ k)) (C : ℝ) (hC : ∀ k ω, |ξ k ω| ≤ C)
    (j : ι) (s : ℝ) (ω : Ω) :
    (itoGridElem i δ N ξ hξ C hC).toFun j s ω =
      if j = i then itoGridStep ξ δ N s ω else 0 := by
  unfold ElemIntegrand.toFun itoGridElem itoGridStep
  rw [List.map_map, itoGrid_list_sum_range]
  split_ifs with hji
  · subst hji
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    simp [Ne.symm hji]

/-- **Energy convergence of grid approximations.** Let `f` be bounded on `(0, ∞)`, jointly
measurable on `(0, ∞) × Ω`, and let the step functions with coefficients `ξ n` converge to `f`
at every `s ∈ (0, T]`. Then the energy distance on `[0, T]` between `itoGridElem i (δ n) (N n)
(ξ n)` and `f 𝟙_{j = i}` tends to `0`. -/
theorem tendsto_energy_itoGridElem_sub [Countable ι] [DecidableEq ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] (i : ι) {f : ℝ → Ω → ℝ} {C : ℝ} (hbd : ∀ ω (s : ℝ), 0 < s → |f s ω| ≤ C)
    (hfm : Measurable fun p : ℝ × Ω => if 0 < p.1 then f p.1 p.2 else 0)
    (δ : ℕ → ℝ≥0) (N : ℕ → ℕ) (ξ : ℕ → ℕ → Ω → ℝ)
    (hξ : ∀ n (k : ℕ), Measurable[𝓖 ((k : ℝ≥0) * δ n)] (ξ n k)) (C' : ℝ)
    (hC' : ∀ n k ω, |ξ n k ω| ≤ C') {T : ℝ}
    (hlim : ∀ ω (s : ℝ), 0 < s → s ≤ T →
      Tendsto (fun n => itoGridStep (ξ n) (δ n) (N n) s ω) atTop (𝓝 (f s ω))) :
    Tendsto (fun n => energy μ (fun j s ω =>
        (itoGridElem i (δ n) (N n) (ξ n) (hξ n) C' (hC' n)).toFun j s ω -
          (if j = i then f s ω else 0)) T) atTop (𝓝 0) := by
  have hD : ∀ n j s ω, (itoGridElem i (δ n) (N n) (ξ n) (hξ n) C' (hC' n)).toFun j s ω -
      (if j = i then f s ω else 0) =
      if j = i then itoGridStep (ξ n) (δ n) (N n) s ω - f s ω else 0 := by
    intro n j s ω
    rw [itoGridElem_toFun]
    split_ifs <;> simp
  simp_rw [hD]
  refine itoEnergy_tendsto_zero_of_dominated (C := ENNReal.ofReal ((|C'| + |C|) ^ 2))
    ENNReal.ofReal_ne_top ?_ ?_ ?_
  · intro n j
    by_cases hji : j = i
    · subst hji
      have : (fun p : ℝ × Ω => if 0 < p.1 then
            (if j = j then itoGridStep (ξ n) (δ n) (N n) p.1 p.2 - f p.1 p.2 else 0) else 0) =
          fun p => itoGridStep (ξ n) (δ n) (N n) p.1 p.2 -
            (if 0 < p.1 then f p.1 p.2 else 0) := by
        funext p
        by_cases hp : 0 < p.1
        · simp [hp]
        · rw [itoGridStep_eq_zero (fun h => hp h.2)]
          simp [hp]
      rw [this]
      exact (measurable_itoGridStep (fun k => (hξ n k).mono (𝓖.le _) le_rfl) _ _).sub hfm
    · simp [hji]
  · intro n ω s hs _
    rw [itoEnergy_tsum_enorm_sq_ite, itoEnergy_enorm_sq]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := abs_itoGridStep_le (hC' n) (δ n) (N n) s ω
    have h2 := (hbd ω s hs).trans (le_abs_self C)
    have h3 : |itoGridStep (ξ n) (δ n) (N n) s ω - f s ω| ≤ |C'| + |C| :=
      (abs_sub _ _).trans (add_le_add h1 h2)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  · intro ω s hs hsT
    simp_rw [itoEnergy_tsum_enorm_sq_ite, itoEnergy_enorm_sq]
    have h := ((hlim ω s hs hsT).sub_const (f s ω)).pow 2
    rw [sub_self] at h
    have := (ENNReal.continuous_ofReal.tendsto _).comp h
    have h0 : ENNReal.ofReal ((0 : ℝ) ^ 2) = 0 := by simp
    rw [h0] at this
    exact this

end QSSEPtoKPZ
