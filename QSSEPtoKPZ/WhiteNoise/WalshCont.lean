/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshBrownian

/-!
# A continuous version of the Walsh integral process (task G9)

If `Z_t = ∫ 𝟙_{0 < r ≤ t} g dξ` for `t ∈ [0, T]`, then `Z` has a version with all paths
continuous on `[0, T]` (`walshProc_exists_cont_version`). Proof:

* an elementary integrand `e` truncated at `t` is elementary (`walshProc_elemTrunc`), and its
  integral process has the continuous version `walshProc_elemCont`, built from the continuous
  versions of `u ↦ ξ((0,u] × (a,b])` (`walshProc_exists_cont_rect`); it is a continuous `L²`
  martingale;
* approximating `𝟙_{(0,T]} g` by elementary integrands `eⱼ` in `L²`, Doob's inequality gives
  `𝔼 sup_{t ≤ T} |Yʲ_t - Yˡ_t|² ≤ 4 𝔼 |Yʲ_T - Yˡ_T|²`; along a fast subsequence the continuous
  processes converge uniformly on `[0, T]` almost surely (Borel–Cantelli), and the limit is a
  version of `Z` (Fatou).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- `‖f‖₂² = ∫ f²` in `[0, ∞]`. -/
private lemma walshProc_eLpNorm_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  have e : ∀ x, ‖f x‖ₑ ^ ((2 : ℝ≥0) : ℝ) = ENNReal.ofReal (f x ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, NNReal.coe_ofNat, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e] at h
  rw [← h, NNReal.coe_ofNat, ENNReal.rpow_two]
  rfl

/-- A block condition, truncated at time `t`. -/
private lemma walshProc_block_iff {s u t r : ℝ} (hs : 0 ≤ s) :
    (s < r ∧ r ≤ max s (min u t)) ↔ ((0 < r ∧ r ≤ t) ∧ s < r ∧ r ≤ u) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_max_iff.1 h2 with h | h
    · exact absurd h (not_le.2 h1)
    · exact ⟨⟨lt_of_le_of_lt hs h1, (le_min_iff.1 h).2⟩, h1, (le_min_iff.1 h).1⟩
  · rintro ⟨⟨_, h2⟩, h1, h3⟩
    exact ⟨h1, le_max_of_le_right (le_min h3 h2)⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- The elementary integrand `e` truncated at time `t`: blocks `(sᵢ, max(sᵢ, min(tᵢ, t))]`. -/
def walshProc_elemTrunc (e : WalshElem Ω) (t : ℝ) : WalshElem Ω :=
  ⟨e.k, e.s, fun i => max (e.s i) (min (e.t i) t.toNNReal), e.a, e.b, e.c⟩

private lemma walshProc_elemTrunc_adapted {e : WalshElem Ω} (he : e.IsAdapted 𝓖) (t : ℝ) :
    (walshProc_elemTrunc e t).IsAdapted 𝓖 :=
  ⟨fun _ => le_max_left _ _, he.le_b, he.meas, he.bdd⟩

private lemma walshProc_elemTrunc_field (e : WalshElem Ω) {t : ℝ} (ht : 0 ≤ t) :
    (walshProc_elemTrunc e t).field =
      fun r y ω => if 0 < r ∧ r ≤ t then e.field r y ω else 0 := by
  funext r y ω
  simp only [WalshElem.field, walshProc_elemTrunc, NNReal.coe_max, NNReal.coe_min,
    Real.coe_toNNReal _ ht]
  have hiff : ∀ i : Fin e.k, ((e.s i : ℝ) < r ∧ r ≤ max (e.s i : ℝ) (min (e.t i : ℝ) t) ∧
      e.a i < y ∧ y ≤ e.b i) ↔
      ((0 < r ∧ r ≤ t) ∧ ((e.s i : ℝ) < r ∧ r ≤ e.t i ∧ e.a i < y ∧ y ≤ e.b i)) := by
    intro i
    have key := walshProc_block_iff (s := e.s i) (u := e.t i) (t := t) (r := r) (e.s i).2
    rw [← and_assoc, key]
    tauto
  by_cases hP : 0 < r ∧ r ≤ t
  · simp only [hP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_congr (hiff i) rfl rfl, ite_and]
    simp [hP]
  · simp only [hP, ite_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_congr (hiff i) rfl rfl, ite_and]
    simp [hP]

/-- The continuous version of the integral process of an elementary integrand, built from
continuous versions `W a b` of `u ↦ ξ((0,u] × (a,b])`. -/
def walshProc_elemCont (W : ℝ → ℝ → ℝ → Ω → ℝ) (T : ℝ) (e : WalshElem Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, e.c i ω * (W (e.a i) (e.b i) (min (max (min (e.t i : ℝ) t) (e.s i)) T) ω -
    W (e.a i) (e.b i) (min (e.s i : ℝ) T) ω)

private lemma walshProc_elemCont_cont {W : ℝ → ℝ → ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ a b ω, ContinuousOn (fun u => W a b u ω) (Set.Icc 0 T)) (e : WalshElem Ω) (ω : Ω) :
    ContinuousOn (fun t => walshProc_elemCont W T e t ω) (Set.Icc 0 T) := by
  unfold walshProc_elemCont
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (ContinuousOn.sub ?_
    continuousOn_const)
  refine (hW _ _ ω).comp (Continuous.continuousOn (by fun_prop)) fun t _ => ⟨?_, min_le_right _ _⟩
  exact le_min (le_max_of_le_right (e.s i).2) hT

private lemma walshProc_elemCont_ae {W : ℝ → ℝ → ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ a b, a ≤ b → ∀ u ∈ Set.Icc (0 : ℝ) T, W a b u =ᵐ[ν] rectMass S 0 u a b)
    {e : WalshElem Ω} (he : e.IsAdapted 𝓖) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    walshProc_elemCont W T e t =ᵐ[ν] (walshProc_elemTrunc e t).value S := by
  have hmem1 : ∀ i : Fin e.k, min (max (min (e.t i : ℝ) t) (e.s i)) T ∈ Set.Icc (0 : ℝ) T :=
    fun i => ⟨le_min (le_max_of_le_right (e.s i).2) hT, min_le_right _ _⟩
  have hmem2 : ∀ i : Fin e.k, min (e.s i : ℝ) T ∈ Set.Icc (0 : ℝ) T :=
    fun i => ⟨le_min (e.s i).2 hT, min_le_right _ _⟩
  have hall : ∀ᵐ ω ∂ν, ∀ i : Fin e.k,
      W (e.a i) (e.b i) (min (max (min (e.t i : ℝ) t) (e.s i)) T) ω =
        rectMass S 0 (min (max (min (e.t i : ℝ) t) (e.s i)) T) (e.a i) (e.b i) ω ∧
      W (e.a i) (e.b i) (min (e.s i : ℝ) T) ω = rectMass S 0 (min (e.s i : ℝ) T) (e.a i) (e.b i) ω :=
    ae_all_iff.2 fun i => (hW _ _ (he.le_b i) _ (hmem1 i)).and (hW _ _ (he.le_b i) _ (hmem2 i))
  filter_upwards [hall] with ω hω
  simp only [walshProc_elemCont, WalshElem.value, walshProc_elemTrunc, NNReal.coe_max,
    NNReal.coe_min, Real.coe_toNNReal _ ht.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hω i).1, (hω i).2]
  congr 1
  rcases le_or_gt (e.s i : ℝ) T with hs | hs
  · have h1 : max (min (e.t i : ℝ) t) (e.s i) ≤ T :=
      max_le ((min_le_right _ _).trans ht.2) hs
    rw [min_eq_left h1, min_eq_left hs, max_comm]
    simp only [rectMass]
    ring
  · have h1 : T ≤ max (min (e.t i : ℝ) t) (e.s i) := (le_max_right _ _).trans' hs.le
    have h2 : max (e.s i : ℝ) (min (e.t i : ℝ) t) = e.s i :=
      max_eq_left ((min_le_right _ _).trans (ht.2.trans hs.le))
    rw [min_eq_right h1, min_eq_right hs.le, h2]
    simp only [rectMass]
    ring

/-- The continuous version of an elementary integral process is a continuous `L²`
martingale. -/
private lemma walshProc_elemCont_isCL2Mart (hS : IsWhiteNoise 𝓖 S ν)
    {W : ℝ → ℝ → ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hWc : ∀ a b ω, ContinuousOn (fun u => W a b u ω) (Set.Icc 0 T))
    (hW : ∀ a b, a ≤ b → ∀ u ∈ Set.Icc (0 : ℝ) T, W a b u =ᵐ[ν] rectMass S 0 u a b)
    {e : WalshElem Ω} (he : e.IsAdapted 𝓖) :
    IsCL2Mart T 𝓖 (walshProc_elemCont W T e) ν := by
  have hwi : ∀ t : ℝ≥0, IsWalshIntegral 𝓖 S ν
      (fun r y ω => if 0 < r ∧ r ≤ t then e.field r y ω else 0)
      ((walshProc_elemTrunc e t).value S) := by
    intro t
    rw [← walshProc_elemTrunc_field e t.coe_nonneg]
    exact (walshProc_elemTrunc_adapted he t).isWalshIntegral
  refine ⟨ae_of_all _ (walshProc_elemCont_cont hT hWc e), fun t ht => ?_, fun s t hst ht => ?_⟩
  · exact (IsWalshIntegral.isometry_lib hS (hwi t)).2.1.ae_eq
      (walshProc_elemCont_ae hT hW he ⟨t.2, ht⟩).symm
  · have hs : (s : ℝ) ≤ T := (NNReal.coe_le_coe.2 hst).trans ht
    exact (condExp_congr_ae (walshProc_elemCont_ae hT hW he ⟨t.2, ht⟩)).trans
      ((walshProc_condExp hS hst (hwi s) (hwi t)).trans
        (walshProc_elemCont_ae hT hW he ⟨s.2, hs⟩).symm)

/-- Itô's isometry, as an equality of `L²` norms. -/
theorem walshProc_eLpNorm_eq (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) :
    eLpNorm X 2 ν = eLpNorm (uncurryField h) 2 (ν.prod volume) := by
  obtain ⟨h2, X2, hiso⟩ := IsWalshIntegral.isometry_lib hS hX
  apply (ENNReal.pow_right_strictMono two_ne_zero).injective
  simp only
  rw [walshProc_eLpNorm_sq X2.aestronglyMeasurable, walshProc_eLpNorm_sq h2.aestronglyMeasurable,
    ← ofReal_integral_eq_lintegral_ofReal X2.integrable_sq (ae_of_all _ fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal h2.integrable_sq (ae_of_all _ fun _ => sq_nonneg _),
    hiso]

/-- **Continuous version of the Walsh integral process**: if `Z_t = ∫ 𝟙_{0 < r ≤ t} g dξ` for
`t ∈ [0, T]`, there is `X` with all paths continuous on `[0, T]` and `X_t = Z_t` almost surely
for each `t ∈ [0, T]`. -/
theorem walshProc_exists_cont_version (hS : IsWhiteNoise 𝓖 S ν) {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℝ → Ω → ℝ} {Z : ℝ → Ω → ℝ}
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsWalshIntegral 𝓖 S ν (fun r y ω => if 0 < r ∧ r ≤ t then g r y ω else 0) (Z t)) :
    ∃ X : ℝ → Ω → ℝ, (∀ ω, ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, X t =ᵐ[ν] Z t := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  -- continuous versions of the rectangle masses
  have hWex : ∀ a b : ℝ, ∃ W : ℝ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun u => W u ω) (Set.Icc 0 T)) ∧
      (a ≤ b → ∀ u ∈ Set.Icc (0 : ℝ) T, W u =ᵐ[ν] rectMass S 0 u a b) := by
    intro a b
    by_cases hab : a ≤ b
    · obtain ⟨W, h1, h2⟩ := walshProc_exists_cont_rect hS T a b hab
      exact ⟨W, h1, fun _ => h2⟩
    · exact ⟨fun _ _ => 0, fun _ => continuousOn_const, fun h => absurd h hab⟩
  choose W hWc hW using hWex
  -- elementary approximations
  obtain ⟨e, he, hlim, -⟩ := (hZ T ⟨hT, le_rfl⟩).exists_elem_tendsto hS
  set δ : ℕ → ℝ≥0∞ := fun j => eLpNorm (uncurryField (e j).field -
    uncurryField (fun r y ω => if 0 < r ∧ r ≤ T then g r y ω else 0)) 2 (ν.prod volume) with hδ
  set Y : ℕ → ℝ → Ω → ℝ := fun j => walshProc_elemCont W T (e j) with hY
  have hYm : ∀ j, IsCL2Mart T 𝓖 (Y j) ν := fun j =>
    walshProc_elemCont_isCL2Mart hS hT hWc hW (he j)
  have hYmem : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (Y j t) 2 ν := by
    intro j t ht
    have := (hYm j).memLp t.toNNReal (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    rwa [Real.coe_toNNReal _ ht.1] at this
  have hZmem : ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (Z t) 2 ν := fun t ht =>
    (IsWalshIntegral.isometry_lib hS (hZ t ht)).2.1
  -- `‖Yʲ_t - Z_t‖₂ ≤ δⱼ`
  have hYZ : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (Y j t - Z t) 2 ν ≤ δ j := by
    intro j t ht
    have hwi : IsWalshIntegral 𝓖 S ν
        (fun r y ω => if 0 < r ∧ r ≤ t then (e j).field r y ω else 0)
        ((walshProc_elemTrunc (e j) t).value S) := by
      rw [← walshProc_elemTrunc_field (e j) ht.1]
      exact (walshProc_elemTrunc_adapted (he j) t).isWalshIntegral
    have hd := hwi.sub (hZ t ht)
    have hd2 := (IsWalshIntegral.isometry_lib hS hd).1
    calc eLpNorm (Y j t - Z t) 2 ν
        = eLpNorm (fun ω => (walshProc_elemTrunc (e j) t).value S ω - Z t ω) 2 ν :=
          eLpNorm_congr_ae ((walshProc_elemCont_ae hT hW (he j) ht).sub EventuallyEq.rfl)
      _ = _ := walshProc_eLpNorm_eq hS hd
      _ ≤ δ j := by
          refine eLpNorm_mono hd2.aestronglyMeasurable fun p => ?_
          simp only [uncurryField, Pi.sub_apply]
          by_cases h1 : 0 < p.2.1 ∧ p.2.1 ≤ t
          · have h2 : 0 < p.2.1 ∧ p.2.1 ≤ T := ⟨h1.1, h1.2.trans ht.2⟩
            simp [h1, h2]
          · simp [h1]
  -- a fast subsequence
  have hJex : ∀ n : ℕ, ∃ j, δ j ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ n) := fun n =>
    (hlim.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))).exists
  choose J hJ using hJex
  set D : ℕ → ℝ → Ω → ℝ := fun n t ω => Y (J (n + 1)) t ω + (-1) * Y (J n) t ω with hD
  have hDm : ∀ n, IsCL2Mart T 𝓖 (D n) ν := fun n =>
    (hYm _).add ((hYm _).const_mul (-1))
  -- Doob and Markov
  set F : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal ((1 / 4 : ℝ) ^ n) ≤
    ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (D n t ω ^ 2)} with hF
  have hFn : ∀ n, ν (F n) ≤ ENNReal.ofReal (16 * (1 / 16 : ℝ) ^ n) := by
    intro n
    obtain ⟨hmeas, hdoob⟩ := (hDm n).lintegral_iSup_sq_le
    have hTT : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    have hDT : eLpNorm (D n T) 2 ν ≤ ENNReal.ofReal (2 * (1 / 8 : ℝ) ^ n) := by
      have e : D n T = (Y (J (n + 1)) T - Z T) - (Y (J n) T - Z T) := by
        funext ω
        simp only [hD, Pi.sub_apply]
        ring
      rw [e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      refine (add_le_add ((hYZ _ T hTT).trans (hJ _)) ((hYZ _ T hTT).trans (hJ _))).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : (1 / 8 : ℝ) ^ (n + 1) ≤ (1 / 8) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
      linarith
    have hint : ∫⁻ ω, ENNReal.ofReal (D n T ω ^ 2) ∂ν ≤
        ENNReal.ofReal (4 * (1 / 64 : ℝ) ^ n) := by
      have hDmem : MemLp (D n T) 2 ν :=
        (hYmem _ T hTT).add ((hYmem _ T hTT).const_mul (-1))
      rw [← walshProc_eLpNorm_sq hDmem.aestronglyMeasurable]
      refine (ENNReal.pow_le_pow_left hDT).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    refine (meas_ge_le_lintegral_div hmeas (ENNReal.ofReal_pos.2 (by positivity)).ne'
      ENNReal.ofReal_ne_top).trans ?_
    refine (ENNReal.div_le_div_right (hdoob.trans (by gcongr : 4 * ∫⁻ ω, ENNReal.ofReal
      (D n T ω ^ 2) ∂ν ≤ 4 * ENNReal.ofReal (4 * (1 / 64 : ℝ) ^ n))) _).trans
      (le_of_eq ?_)
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    rw [div_eq_iff (by positivity), mul_assoc, ← mul_pow]
    norm_num
    ring
  have hsum : ∑' n, ν (F n) ≠ ∞ := by
    have hs : Summable fun n : ℕ => 16 * (1 / 16 : ℝ) ^ n :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hFn)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  -- the good event
  set G : Set Ω := {ω | ∃ N, ∀ n ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) T, |D n t ω| ≤ (1 / 2 : ℝ) ^ n}
    with hG
  have hGae : ∀ᵐ ω ∂ν, ω ∈ G := by
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    refine ⟨N, fun n hn t ht => ?_⟩
    have hnot := hN n hn
    simp only [hF, Set.mem_ofPred_eq, not_le] at hnot
    have h1 : ENNReal.ofReal (D n t ω ^ 2) < ENNReal.ofReal ((1 / 4 : ℝ) ^ n) :=
      lt_of_le_of_lt (le_iSup₂ (f := fun t _ => ENNReal.ofReal (D n t ω ^ 2)) t ht) hnot
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
    have h2 : D n t ω ^ 2 < ((1 / 2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num at h1 ⊢
      exact h1
    exact (abs_lt_of_sq_lt_sq h2 (by positivity)).le
  -- uniform Cauchy property on `G`
  have htele : ∀ ω ∈ G, ∃ N, ∀ n ≥ N, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      |Y (J (n + i)) t ω - Y (J n) t ω| ≤ 2 * (1 / 2 : ℝ) ^ n - 2 * (1 / 2 : ℝ) ^ (n + i) := by
    intro ω hω
    obtain ⟨N, hN⟩ := hω
    refine ⟨N, fun n hn i => ?_⟩
    induction i with
    | zero => intro t _; simp
    | succ i ih =>
      intro t ht
      have h1 := hN (n + i) (by omega) t ht
      have h2 := ih t ht
      simp only [hD] at h1
      have e : Y (J (n + i)) t ω + -1 * Y (J (n + i)) t ω = 0 := by ring
      calc |Y (J (n + (i + 1))) t ω - Y (J n) t ω|
          ≤ |Y (J (n + i + 1)) t ω + -1 * Y (J (n + i)) t ω| +
            |Y (J (n + i)) t ω - Y (J n) t ω| := by
            rw [show n + (i + 1) = n + i + 1 by ring]
            have := abs_add_le (Y (J (n + i + 1)) t ω + -1 * Y (J (n + i)) t ω)
              (Y (J (n + i)) t ω - Y (J n) t ω)
            convert this using 2
            ring
        _ ≤ (1 / 2 : ℝ) ^ (n + i) + (2 * (1 / 2 : ℝ) ^ n - 2 * (1 / 2 : ℝ) ^ (n + i)) :=
            add_le_add h1 h2
        _ = 2 * (1 / 2 : ℝ) ^ n - 2 * (1 / 2 : ℝ) ^ (n + (i + 1)) := by
            rw [show n + (i + 1) = n + i + 1 by ring, pow_succ]
            ring
  have hconv : ∀ ω ∈ G, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ L, Tendsto (fun n => Y (J n) t ω) atTop (𝓝 L) := by
    intro ω hω t ht
    obtain ⟨N, hN⟩ := htele ω hω
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨max N m, fun n hn => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Real.dist_eq]
    have h := hN (max N m) (le_max_left N m) i t ht
    have : (1 / 2 : ℝ) ^ max N m ≤ (1 / 2) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    have : 0 ≤ (1 / 2 : ℝ) ^ (max N m + i) := by positivity
    linarith
  classical
  set X : ℝ → Ω → ℝ := fun t ω => if ω ∈ G ∧ t ∈ Set.Icc (0 : ℝ) T then
    limUnder atTop (fun n => Y (J n) t ω) else 0 with hX
  have hXlim : ∀ ω ∈ G, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun n => Y (J n) t ω) atTop (𝓝 (X t ω)) := by
    intro ω hω t ht
    obtain ⟨L, hL⟩ := hconv ω hω t ht
    simp only [hX, hω, ht, and_self, ite_true]
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  refine ⟨X, fun ω => ?_, fun t ht => ?_⟩
  · by_cases hω : ω ∈ G
    · obtain ⟨N, hN⟩ := htele ω hω
      have hunif : TendstoUniformlyOn (fun n t => Y (J n) t ω) (fun t => X t ω) atTop
          (Set.Icc 0 T) := by
        refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
        obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
          (show (1 / 2 : ℝ) < 1 by norm_num)
        refine eventually_atTop.2 ⟨max N m, fun n hn t ht => ?_⟩
        have hb : |X t ω - Y (J n) t ω| ≤ 2 * (1 / 2 : ℝ) ^ n := by
          have hl := (hXlim ω hω t ht).comp (tendsto_add_atTop_nat n)
          refine le_of_tendsto ((continuous_abs.tendsto _).comp
            (hl.sub tendsto_const_nhds)) (Eventually.of_forall fun i => ?_)
          simp only [Function.comp_apply]
          rw [add_comm i n]
          have := hN n (le_of_max_le_left hn) i t ht
          have : 0 ≤ (1 / 2 : ℝ) ^ (n + i) := by positivity
          linarith
        rw [Real.dist_eq]
        have : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ m :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_max_le_right hn)
        linarith
      exact hunif.continuousOn (Eventually.of_forall fun n =>
        walshProc_elemCont_cont hT hWc (e (J n)) ω).frequently
    · have : (fun t => X t ω) = fun _ => 0 := by
        funext t
        simp [hX, hω]
      rw [this]
      exact continuousOn_const
  · -- `X_t = Z_t` almost surely, by Fatou
    have hconv' : ∀ᵐ ω ∂ν, Tendsto (fun n => Y (J n) t ω) atTop (𝓝 (X t ω)) := by
      filter_upwards [hGae] with ω hω
      exact hXlim ω hω t ht
    have hXm : AEMeasurable (X t) ν := aemeasurable_of_tendsto_metrizable_ae'
      (fun n => (hYmem _ t ht).aestronglyMeasurable.aemeasurable) hconv'
    have hZm := (hZmem t ht).aestronglyMeasurable.aemeasurable
    have hmeas_n : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ((Y (J n) t ω - Z t ω) ^ 2)) ν :=
      fun n => (((hYmem _ t ht).aestronglyMeasurable.aemeasurable.sub hZm).pow_const 2).ennreal_ofReal
    have hlim0 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal ((Y (J n) t ω - Z t ω) ^ 2) ∂ν)
        atTop (𝓝 0) := by
      have hb : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Y (J n) t ω - Z t ω) ^ 2) ∂ν ≤
          ENNReal.ofReal ((1 / 64 : ℝ) ^ n) := by
        intro n
        have := walshProc_eLpNorm_sq ((hYmem (J n) t ht).sub (hZmem t ht)).aestronglyMeasurable
        simp only [Pi.sub_apply] at this
        rw [← this]
        refine (ENNReal.pow_le_pow_left ((hYZ _ t ht).trans (hJ n))).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul, mul_comm n 2, pow_mul]
        norm_num
      have h0 : Tendsto (fun n => ENNReal.ofReal ((1 / 64 : ℝ) ^ n)) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
          (by norm_num))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hb
    have hfatou := lintegral_liminf_le' (u := atTop) hmeas_n
    have hcongr : (fun ω => liminf (fun n => ENNReal.ofReal ((Y (J n) t ω - Z t ω) ^ 2)) atTop)
        =ᵐ[ν] fun ω => ENNReal.ofReal ((X t ω - Z t ω) ^ 2) := by
      filter_upwards [hconv'] with ω hω
      exact ((ENNReal.continuous_ofReal.tendsto _).comp
        (((hω.sub tendsto_const_nhds).pow 2))).liminf_eq
    rw [lintegral_congr_ae hcongr, hlim0.liminf_eq] at hfatou
    have h0 : ∫⁻ ω, ENNReal.ofReal ((X t ω - Z t ω) ^ 2) ∂ν = 0 := le_antisymm hfatou zero_le
    have hae : AEMeasurable (fun ω => ENNReal.ofReal ((X t ω - Z t ω) ^ 2)) ν :=
      ((hXm.sub hZm).pow_const 2).ennreal_ofReal
    rw [lintegral_eq_zero_iff' hae] at h0
    filter_upwards [h0] with ω hω
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
    have : (X t ω - Z t ω) ^ 2 = 0 := le_antisymm hω (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

end QSSEPtoKPZ
