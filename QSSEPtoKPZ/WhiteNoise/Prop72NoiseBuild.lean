/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Prop72NoiseCalc
public import QSSEPtoKPZ.WhiteNoise.MMExists
public import QSSEPtoKPZ.WhiteNoise.LevyMulti

/-!
# Proposition 7.2, Step 2: construction of the white noise (task J1)

On `Ω × Ω''` with the product measure and the product filtration `𝒢̄` (with null sets), for every
`x` let `I_x = (0, x]` (or `(x, 0]` with a minus sign, `e_x` = `prop72NoiseE x`) and

  `ξ_t(I_x) = ((𝟙_{Z>0}/Z) e_x) · M (t ∧ T) + ∫_0^t ∫ (1 - 𝟙_{0<s≤T, Z>0}) e_x ξ'(ds dy)`,

the first term being the martingale-measure integral of Step 1 (`IsMMIntegral`, intensity
`Z²`), the second a Walsh integral against the auxiliary noise `ξ'` (which alone drives `ξ` after
`T`, since the frozen `IsWhiteNoise` concerns all times). The Walsh integrals are taken on the
horizons `n ∈ ℕ` and glued (`t ↦ W_{⌈t⌉}(t)`); then a version adapted to `𝒢̄` and vanishing at
`0` is chosen. By (7.10), the orthogonality of the two parts and the isometry of the Walsh
integral, `⟨ξ(a,b], ξ(a',b']⟩_t = t |(a,b] ∩ (a',b']|`, and Lévy's characterization
(`isWhiteNoise_of_martingales`) shows that `ξ` is a white noise for `𝒢̄`.

`prop72Noise_build` also records the covariation of `ξ((a,b])` with any stopped integral
`(h · M)_{· ∧ T}`: `∫_0^{t ∧ T} ∫ 𝟙_{Z>0} 𝟙_{(a,b]}(y) Z h`, which gives (7.11).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `𝟙_{(a,b]}(y) 𝟙_{(a',b']}(y) = 𝟙_{(a,b] ∩ (a',b']}(y)`. -/
private lemma prop72Noise_ind_mul (a b a' b' y : ℝ) :
    (if a < y ∧ y ≤ b then (1 : ℝ) else 0) * (if a' < y ∧ y ≤ b' then 1 else 0) =
      (Set.Ioc a b ∩ Set.Ioc a' b').indicator 1 y := by
  by_cases h1 : a < y ∧ y ≤ b <;> by_cases h2 : a' < y ∧ y ≤ b' <;>
    simp [Set.indicator, Set.mem_inter_iff, Set.mem_Ioc, h1, h2]

/-- `𝟙_{Z>0} e_b / Z - 𝟙_{Z>0} e_a / Z = 𝟙_{Z>0} 𝟙_{(a,b]} / Z`. -/
private lemma prop72Noise_H_sub (Z : ℝ → ℝ → Ω → ℝ) {a b : ℝ} (hab : a ≤ b) (r y : ℝ) (ω : Ω) :
    prop72NoiseH Z b r y ω + -1 * prop72NoiseH Z a r y ω =
      if 0 < prop72NoiseZp Z r y ω then
        (if a < y ∧ y ≤ b then 1 else 0) / prop72NoiseZp Z r y ω else 0 := by
  unfold prop72NoiseH
  by_cases hz : 0 < prop72NoiseZp Z r y ω
  · simp only [hz, ↓reduceIte]
    rw [← prop72NoiseE_sub hab]
    ring
  · simp [hz]

/-- `Z² (𝟙_{Z>0} 𝟙_{(a,b]} / Z) = 𝟙_{Z>0} 𝟙_{(a,b]} Z`. -/
private lemma prop72Noise_qH (Z : ℝ → ℝ → Ω → ℝ) {a b : ℝ} (hab : a ≤ b) (r y : ℝ) (ω : Ω) :
    prop72NoiseZp Z r y ω ^ 2 * (prop72NoiseH Z b r y ω + -1 * prop72NoiseH Z a r y ω) =
      if 0 < prop72NoiseZp Z r y ω ∧ a < y ∧ y ≤ b then prop72NoiseZp Z r y ω else 0 := by
  rw [prop72Noise_H_sub Z hab]
  by_cases hz : 0 < prop72NoiseZp Z r y ω
  · by_cases hy : a < y ∧ y ≤ b
    · simp only [hz, hy, and_self, ↓reduceIte]
      field_simp
    · simp [hz, hy]
  · simp [hz]

/-- `Z² (𝟙_{Z>0} 𝟙_{(a,b]} / Z)(𝟙_{Z>0} 𝟙_{(a',b']} / Z) = 𝟙_{Z>0} 𝟙_{(a,b] ∩ (a',b']}`. -/
private lemma prop72Noise_qHH (Z : ℝ → ℝ → Ω → ℝ) {a b a' b' : ℝ} (hab : a ≤ b)
    (hab' : a' ≤ b') (r y : ℝ) (ω : Ω) :
    prop72NoiseZp Z r y ω ^ 2 * (prop72NoiseH Z b r y ω + -1 * prop72NoiseH Z a r y ω) *
      (prop72NoiseH Z b' r y ω + -1 * prop72NoiseH Z a' r y ω) =
      if 0 < prop72NoiseZp Z r y ω then (Set.Ioc a b ∩ Set.Ioc a' b').indicator 1 y else 0 := by
  rw [prop72Noise_H_sub Z hab, prop72Noise_H_sub Z hab', ← prop72Noise_ind_mul]
  by_cases hz : 0 < prop72NoiseZp Z r y ω
  · simp only [hz, ↓reduceIte]
    field_simp
  · simp [hz]

/-- `(K_b - K_a)(K_{b'} - K_{a'}) = (1 - 𝟙_{0<r≤T, Z>0}) 𝟙_{(a,b] ∩ (a',b']}`. -/
private lemma prop72Noise_KK {Ω'' : Type*} (Z : ℝ → ℝ → Ω → ℝ) (T : ℝ) {a b a' b' : ℝ}
    (hab : a ≤ b) (hab' : a' ≤ b') (r y : ℝ) (ω : Ω × Ω'') :
    (prop72NoiseK Z T b r y ω - prop72NoiseK Z T a r y ω) *
      (prop72NoiseK Z T b' r y ω - prop72NoiseK Z T a' r y ω) =
      if 0 < r ∧ r ≤ T ∧ 0 < prop72NoiseZp Z r y ω.1 then 0
        else (Set.Ioc a b ∩ Set.Ioc a' b').indicator 1 y := by
  unfold prop72NoiseK
  by_cases hg : 0 < r ∧ r ≤ T ∧ 0 < prop72NoiseZp Z r y ω.1
  · simp [hg]
  · simp only [hg, ↓reduceIte]
    rw [prop72NoiseE_sub hab, prop72NoiseE_sub hab', prop72Noise_ind_mul]

/-- **Step 2 of the proof of Proposition 7.2**: the white noise `ξ` on `Ω × Ω''`, for the
product filtration, and its covariation with the stopped martingale-measure integrals. -/
theorem prop72Noise_build {Pr : Measure Ω} [IsProbabilityMeasure Pr] {𝒢 : Filtration ℝ≥0 mΩ}
    {T : ℝ} (hT : 0 < T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Z : ℝ → ℝ → Ω → ℝ}
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
    {𝓖'' : Filtration ℝ≥0 m''} {S'' : ℝ → ℝ → Ω'' → ℝ} (hS'' : IsWhiteNoise 𝓖'' S'' ν'') :
    ∃ S : ℝ → ℝ → Ω × Ω'' → ℝ,
      IsWhiteNoise (prodFiltration 𝒢 𝓖'' (Pr.prod ν'')) S (Pr.prod ν'') ∧
      ∀ {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ},
        IsMMIntegral T 𝒢 (fun r x ω => prop72NoiseZp Z r x ω ^ 2)
          (fun φ => limMart Y (fun _ => φ) (fun _ _ => 0)) Pr h X →
        ∀ n : ℝ, T ≤ n → ∀ a b : ℝ, a ≤ b →
        HasCovariation n (prodFiltration 𝒢 𝓖'' (Pr.prod ν'')) (fun t ω => S t b ω - S t a ω)
          (fun t ω => X (min t T) ω.1)
          (fun t ω => ∫ r in (0 : ℝ)..(min t T), ∫ y,
            (if 0 < prop72NoiseZp Z r y ω.1 ∧ a < y ∧ y ≤ b then prop72NoiseZp Z r y ω.1
              else 0) * h r y ω.1) (Pr.prod ν'') := by
  classical
  set P := Pr.prod ν'' with hPdef
  set 𝒢b := prodFiltration 𝒢 𝓖'' P with h𝒢b
  set q : ℝ → ℝ → Ω → ℝ := fun r x ω => prop72NoiseZp Z r x ω ^ 2 with hqdef
  set M : (ℝ → ℝ) → ℝ → Ω → ℝ := fun φ => limMart Y (fun _ => φ) (fun _ _ => 0) with hMdef
  have hq : Measurable[(𝒢.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × Ω) × ℝ => q p.1.1 p.2 p.1.2 := (prop72NoiseZp_pred hZp).pow_const 2
  have hq0 : ∀ r x ω, 0 ≤ q r x ω := fun _ _ _ => sq_nonneg _
  have hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂Pr < ⊤ :=
    prop72Noise_hq1 hZ2
  have hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ)
        (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) Pr :=
    fun hφ hψ => prop72Noise_hMZ hT hZp hZ2 hmart hφ hψ
  have hS' : IsWhiteNoise 𝒢b (fun t x ω => S'' t x ω.2) P := hS''.prod_snd
  -- the martingale-measure parts
  have hXex : ∀ x : ℝ, ∃ X : ℝ → Ω → ℝ, IsMMIntegral T 𝒢 q M Pr (prop72NoiseH Z x) X :=
    fun x => exists_isMMIntegral hq hq0 hq1 hM (prop72NoiseH_pred hZp x)
      (prop72NoiseH_energy T x)
  choose X hX using hXex
  -- the parts driven by the auxiliary noise, on the horizons `n ∈ ℕ`
  have hWex : ∀ (x : ℝ) (n : ℕ), ∃ W : ℝ → Ω × Ω'' → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) n, IsWalshIntegral 𝒢b (fun t x ω => S'' t x ω.2) P
        (fun s y ω => if 0 < s ∧ s ≤ t then prop72NoiseK Z T x s y ω else 0) (W t)) ∧
      HasBracket n 𝒢b W (fun t ω => ∫ s in (0 : ℝ)..t, ∫ y, prop72NoiseK Z T x s y ω ^ 2) P :=
    fun x n => exists_walshProcess hS' (Nat.cast_nonneg n) (prop72NoiseK_pred P hZp hT.le x)
      (prop72NoiseK_energy T x n)
  choose W hW using hWex
  -- the horizons are consistent
  have hind : ∀ (x : ℝ) (n : ℕ), ∀ᵐ ω ∂P, ∀ m : ℕ, m ≤ n →
      ∀ t ∈ Set.Icc (0 : ℝ) m, W x m t ω = W x n t ω := by
    intro x n
    refine ae_all_iff.2 fun m => ?_
    by_cases hmn : m ≤ n
    swap
    · exact ae_of_all _ fun ω h => absurd h hmn
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have hcm : ∀ k : ℕ, (m : ℝ) ≤ k →
        ∀ᵐ ω ∂P, Continuous fun t : ℝ≥0 => W x k (min (t : ℝ) m) ω := by
      intro k hk
      filter_upwards [(hW x k).2.cont] with ω hω
      exact hω.comp_continuous (NNReal.continuous_coe.min continuous_const)
        fun t => ⟨le_min t.coe_nonneg (Nat.cast_nonneg m), (min_le_right _ _).trans hk⟩
    have h := StochIntAux.ae_forall_le_eq_of_continuous (μ := P) (T := m)
      (X := fun t ω => W x m (min t m) ω) (Y := fun t ω => W x n (min t m) ω)
      (hcm m le_rfl) (hcm n hmn') fun t ht => by
        simp only [min_eq_left ht]
        exact ((hW x m).1 t ⟨t.coe_nonneg, ht⟩).ae_eq_lib hS'
          ((hW x n).1 t ⟨t.coe_nonneg, ht.trans hmn'⟩) EventuallyEq.rfl
    filter_upwards [h] with ω hω _ t ht
    have := hω t.toNNReal (by rw [Real.coe_toNNReal t ht.1]; exact ht.2)
    simpa only [Real.coe_toNNReal t ht.1, min_eq_left ht.2] using this
  -- gluing
  set Wg : ℝ → ℝ → Ω × Ω'' → ℝ := fun x t ω => W x ⌈t⌉₊ t ω with hWg
  have hglue : ∀ (x : ℝ) (n : ℕ), ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) n, Wg x t ω = W x n t ω := by
    intro x n
    filter_upwards [hind x n] with ω hω t ht
    exact hω ⌈t⌉₊ (Nat.ceil_le.2 ht.2) t ⟨ht.1, Nat.le_ceil t⟩
  -- the processes `ξ_t(I_x)` before the choice of a version
  set N : ℝ → ℝ → Ω × Ω'' → ℝ := fun x t ω => X x (min t T) ω.1 + Wg x t ω with hN
  have hNcl : ∀ (x : ℝ) (n : ℕ),
      IsCL2Mart n 𝒢b (fun t ω => X x (min t T) ω.1 + W x n t ω) P := fun x n =>
    (prop72Noise_covMM hT.le hq hq0 hq1 hM (hX x) (hX x) n).left.add (hW x n).2.toIsCL2Mart
  have hNae : ∀ (x : ℝ) (t : ℝ≥0), AEStronglyMeasurable[𝒢b t] (N x t) P := fun x t =>
    aestronglyMeasurable_of_condExp_eq_self
      ((hNcl x ⌈(t : ℝ)⌉₊).condExp t t le_rfl (Nat.le_ceil _))
  have hNc : ∀ x, ∀ᵐ ω ∂P, ∀ m : ℕ, ContinuousOn (fun t => N x t ω) (Set.Icc 0 m) := by
    intro x
    refine ae_all_iff.2 fun m => ?_
    filter_upwards [(hNcl x m).cont, hglue x m] with ω hc hg
    refine hc.congr fun t ht => ?_
    show X x (min t T) ω.1 + Wg x t ω = _
    rw [hg t ht]
  have hN0 : ∀ x, ∀ᵐ ω ∂P, N x 0 ω = 0 := by
    intro x
    have h1 : ∀ᵐ ω ∂P, X x 0 ω.1 = 0 := prodNoise_ae_fst (prop72Noise_mm_zero hT.le (hX x))
    have h2 : W x 0 0 =ᵐ[P] 0 := ((hW x 0).1 0 ⟨le_rfl, by simp⟩).ae_eq_lib hS'
      (IsWalshIntegral.zero _ _ _) (ae_of_all _ fun p => by simp [uncurryField])
    filter_upwards [h1, h2] with ω e1 e2
    show X x (min 0 T) ω.1 + W x ⌈(0 : ℝ)⌉₊ 0 ω = 0
    rw [min_eq_left hT.le, Nat.ceil_zero, e1, zero_add]
    exact e2
  -- adapted versions vanishing at `0`
  have h0 : nullSets P ≤ 𝒢b 0 := by
    rw [h𝒢b, prodFiltration_apply]; exact le_sup_right
  have hver : ∀ x, ∃ N' : ℝ → Ω × Ω'' → ℝ, (∀ t : ℝ, Measurable[𝒢b t.toNNReal] (N' t)) ∧
      (∀ ω, N' 0 ω = 0) ∧ ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → N' t ω = N x t ω :=
    fun x => prop72Noise_exists_version h0 (hNae x) (hNc x) (hN0 x)
  choose Sv hSm hS0 hSeq using hver
  set S : ℝ → ℝ → Ω × Ω'' → ℝ := fun t x ω => Sv x t ω with hSdef
  have hSD : ∀ (x : ℝ) (n : ℕ), ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) n,
      X x (min t T) ω.1 + W x n t ω = S t x ω := by
    intro x n
    filter_upwards [hSeq x, hglue x n] with ω h1 h2 t ht
    show _ = Sv x t ω
    rw [h1 t ht.1]
    show _ = X x (min t T) ω.1 + Wg x t ω
    rw [h2 t ht]
  -- the pieces of `ξ((a,b]) = ξ(I_b) - ξ(I_a)` on the horizon `n`
  have hXd : ∀ a b, IsMMIntegral T 𝒢 q M Pr
      (fun r x ω => prop72NoiseH Z b r x ω + -1 * prop72NoiseH Z a r x ω)
      (fun r ω => X b r ω + -1 * X a r ω) := fun a b =>
    IsMMIntegral.add _ _ _ _ (hX b) ((hX a).const_mul (-1))
  have hWd : ∀ (a b : ℝ) (n : ℕ),
      (∀ t ∈ Set.Icc (0 : ℝ) n, IsWalshIntegral 𝒢b (fun t x ω => S'' t x ω.2) P
        (fun s y ω => if 0 < s ∧ s ≤ t then
          prop72NoiseK Z T b s y ω - prop72NoiseK Z T a s y ω else 0)
        (fun ω => W b n t ω - W a n t ω)) ∧
      IsCL2Mart n 𝒢b (fun t ω => W b n t ω - W a n t ω) P := by
    intro a b n
    refine ⟨fun t ht => ?_, ?_⟩
    · have e : (fun (s y : ℝ) (ω : Ω × Ω'') => if 0 < s ∧ s ≤ t then
            prop72NoiseK Z T b s y ω - prop72NoiseK Z T a s y ω else 0) =
          fun s y ω => (if 0 < s ∧ s ≤ t then prop72NoiseK Z T b s y ω else 0) -
            (if 0 < s ∧ s ≤ t then prop72NoiseK Z T a s y ω else 0) := by
        funext s y ω; split_ifs <;> simp
      rw [e]
      exact ((hW b n).1 t ht).sub ((hW a n).1 t ht)
    · exact ((hW b n).2.toIsCL2Mart.add ((hW a n).2.toIsCL2Mart.const_mul (-1))).congr
        (ae_of_all _ fun ω t _ => by ring)
  have hDS : ∀ (a b : ℝ) (n : ℕ), ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) n,
      (X b (min t T) ω.1 + -1 * X a (min t T) ω.1) + (W b n t ω - W a n t ω) =
        S t b ω - S t a ω := by
    intro a b n
    filter_upwards [hSD a n, hSD b n] with ω ha hb t ht
    rw [← ha t ht, ← hb t ht]; ring
  -- `ξ` is a white noise
  have hwn : IsWhiteNoise 𝒢b S P := by
    refine isWhiteNoise_of_martingales (fun t x => hSm x t) (fun x ω => hS0 x ω) ?_
    intro T' a b a' b' hab hab'
    set n : ℕ := ⌈max T' T⌉₊ with hn
    have hT'n : T' ≤ n := (le_max_left _ _).trans (Nat.le_ceil _)
    have h4 := prop72Noise_cov_add4
      (prop72Noise_covMM hT.le hq hq0 hq1 hM (hXd a b) (hXd a' b') n)
      (prop72Noise_covCross hT.le hq hq0 hq1 hM (hXd a b) hS'' (hWd a' b' n).1 (hWd a' b' n).2)
      (prop72Noise_covCross hT.le hq hq0 hq1 hM (hXd a' b') hS'' (hWd a b n).1
        (hWd a b n).2).symm
      (walshProcess_hasCovariation hS' (hWd a b n).1 (hWd a' b' n).1 (hWd a b n).2
        (hWd a' b' n).2)
    refine prop72Noise_cov_mono (prop72Noise_cov_congr (Nat.cast_nonneg n) h4 (hDS a b n)
      (hDS a' b' n) (ae_of_all _ fun ω t ht => ?_)) hT'n
    simp only [hqdef, prop72Noise_qHH Z hab hab', prop72Noise_KK Z T hab hab', add_zero, zero_add]
    exact prop72Noise_calc (measurableSet_Ioc.inter measurableSet_Ioc)
      (measure_ne_top_of_subset Set.inter_subset_left measure_Ioc_lt_top.ne)
      ((prop72NoiseZp_measurable hZp).comp measurable_prodMk_left) hT.le ht.1
  refine ⟨S, hwn, ?_⟩
  intro h Xh hXh n hn a b hab
  set N' : ℕ := ⌈n⌉₊ with hN'
  have h2 := (prop72Noise_covMM hT.le hq hq0 hq1 hM (hXd a b) hXh N').add_left
    (prop72Noise_covCross hT.le hq hq0 hq1 hM hXh hS'' (hWd a b N').1 (hWd a b N').2).symm
  refine prop72Noise_cov_mono (prop72Noise_cov_congr (Nat.cast_nonneg N') h2 (hDS a b N')
    (ae_of_all _ fun _ _ _ => rfl) (ae_of_all _ fun ω t _ => ?_)) (Nat.le_ceil n)
  simp only [hqdef, prop72Noise_qH Z hab, add_zero]

end QSSEPtoKPZ
