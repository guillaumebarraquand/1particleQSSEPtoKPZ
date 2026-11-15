/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Assembly.Slutsky
public import QSSEPtoKPZ.Assembly.BoxVersion
public import QSSEPtoKPZ.FiniteSystems.Statements
public import QSSEPtoKPZ.Uniqueness.Theorem12

/-!
# Proof of Theorem 1.2 for all sizes `L_k` (task M3)

The end of Section 8 of the article (`docs/stage5-design.md`, Section 1.2 (f)). For each `k`:

* `ψ^∞_k` is the given `ψ_k` if `L_k = ∞`, and otherwise the wave function on `ℤ` constructed on
  `Ω_k` from the given Brownian family `B_k` (`prop_2_1_existence`), adapted to the augmented
  filtration `𝓕_k^a` (`thmMain_exists_top`);
* `main_theorem_top` (for the filtrations `𝓕_k^a`) gives versions `Y_k` of `𝒵^∞_{n_k}` converging
  in distribution to the version `𝒵` of the solution of (1.13);
* the version `X_k` of `𝒵_{n_k} = 𝒵^{L_k}_{n_k}` is `Y_k` if `L_k = ∞` and
  `exists_rescaledPath_version_box` otherwise (`thmMain_exists_version`);
* for finite `L_k` with `n_k^{3/4} T < L_k`, the probability that
  `|X_k(t)(f) - Y_k(t)(f)| > ε ‖f‖_∞` for some `t ≤ T` and some bounded continuous `f` is at most
  `prop81Rhs n_k T (ε e^{-T}) L_k` (`thmMain_close`: the closeness bound
  `abs_integral_rescaledMeasure_box_sub_le`, `ϱ_n(t) ≤ e^{t n^{-1/2}} ≤ e^T` (3.9), and the
  quantitative Proposition 8.1 `prop81_bound`), which tends to `0` (`prop81Rhs_tendsto_enat`);
* `tendstoInDistribution_of_close` (Slutsky with one space per `k`) concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- **The wave function on `ℤ` coupled to a given one.** On a space carrying a Brownian family
and a wave function `ψ` on `Λ_L`, there is a wave function `φ` on `ℤ` driven by the same family,
for the augmented filtration `𝓕^a`, with `φ = ψ` when `L = ∞` (otherwise Proposition 2.1,
existence). -/
private lemma thmMain_exists_top (hB : IsBrownianFamily 𝓕 B μ) {L : ℕ∞}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    ∃ φ : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveFunction ⊤ (nullAug μ 𝓕) B φ μ ∧ (L = ⊤ → φ = ψ) := by
  by_cases hL : L = ⊤
  · subst hL
    exact ⟨ψ, hψ.nullAug, fun _ => rfl⟩
  · obtain ⟨φ, hφ⟩ := prop_2_1_existence hB ⊤
    exact ⟨φ, hφ, fun h => absurd h hL⟩

/-- **Version of `𝒵^L_n` in `C([0,T], ℳ₊)`.** Given a version `Y` of `𝒵^∞_n` built from a wave
function `φ` on `ℤ` equal to `ψ` when `L = ∞`, the process `𝒵^L_n` built from `ψ` has an almost
everywhere measurable version `X`, equal to `Y` when `L = ∞`
(`exists_rescaledPath_version_box` for finite `L`). -/
private lemma thmMain_exists_version [IsProbabilityMeasure μ] {L : ℕ∞}
    {ψ φ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) {T : ℝ}
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hYm : AEMeasurable Y μ)
    (hY : ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T,
      (Y ω t : Measure ℝ) = rescaledMeasure ⊤ n (density φ ω) t)
    (hφψ : L = ⊤ → φ = ψ) :
    ∃ X : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), AEMeasurable X μ ∧
      (∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T,
        (X ω t : Measure ℝ) = rescaledMeasure L n (density ψ ω) t) ∧ (L = ⊤ → X = Y) := by
  by_cases hL : L = ⊤
  · subst hL
    obtain rfl := hφψ rfl
    exact ⟨Y, hYm, hY, fun _ => rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = L := ⟨_, ENat.natCast_toNat hL⟩
    obtain ⟨X, hXm, hX⟩ := exists_rescaledPath_version_box hψ hn T
    exact ⟨X, hXm, hX, fun h => absurd h hL⟩

/-- `ϱ_n(t) ≤ e^T` for `n ≥ 1` and `0 ≤ t ≤ T` (from (3.9), `ϱ_n(t) ≤ e^{t n^{-1/2}}`). -/
private lemma thmMain_varrhoN_le {n t T : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) (htT : t ≤ T) :
    varrhoN n t ≤ Real.exp T := by
  refine (varrhoN_bounds hn ht).2.trans (Real.exp_le_exp.2 ?_)
  have h1 : n ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have h0 : 0 ≤ n ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hn) _
  nlinarith

/-- **Closeness of the finite and infinite systems** (proof of Theorem 1.2, end of Section 8).
Let `φ` (on `ℤ`) and `ψ` (on `Λ_m`, `m ≥ 1`) be wave functions driven by the same Brownian family
for the same filtration, `n ≥ 1`, `T, ε > 0`, `n^{3/4} T < m`, and `X`, `Y` versions of
`𝒵^m_n`, `𝒵^∞_n`. Then the outer probability that `|X(t)(f) - Y(t)(f)| > ε ‖f‖_∞` for some
`t ∈ [0,T]` and some bounded continuous `f` is at most `prop81Rhs n T (ε e^{-T}) m`. -/
private lemma thmMain_close [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {φ ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hφ : IsWaveFunction ⊤ 𝓕 B φ μ) {L : ℕ∞} {m : ℕ}
    (hm : (m : ℕ∞) = L) (hm1 : 1 ≤ m) (hψ : IsWaveFunction L 𝓕 B ψ μ)
    {n T ε : ℝ} (hn : 1 ≤ n) (hT : 0 < T) (hε : 0 < ε) (hℓ : n ^ (3 / 4 : ℝ) * T < m)
    {X Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hX : ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T,
      (X ω t : Measure ℝ) = rescaledMeasure L n (density ψ ω) t)
    (hY : ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T,
      (Y ω t : Measure ℝ) = rescaledMeasure ⊤ n (density φ ω) t) :
    μ {ω | ¬ ∀ (t : Set.Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
        |(∫ x, f x ∂(X ω t : Measure ℝ)) - ∫ x, f x ∂(Y ω t : Measure ℝ)| ≤ ε * ‖f‖} ≤
      prop81Rhs n T (ε * Real.exp (-T)) m := by
  subst hm
  set δ := ε * Real.exp (-T) with hδ_def
  have hδ : 0 < δ := mul_pos hε (Real.exp_pos _)
  have hsum := (lemma_5_2 hB hφ hn).1
  have hsupp := hψ.support
  set A : Set Ω := {ω | ENNReal.ofReal δ < ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal (∑' x : ℤ, |zN n ψ ω t x - zN n φ ω t x|)} with hA
  have hgood : ∀ᵐ ω ∂μ, ω ∉ A → ∀ (t : Set.Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
      |(∫ x, f x ∂(X ω t : Measure ℝ)) - ∫ x, f x ∂(Y ω t : Measure ℝ)| ≤ ε * ‖f‖ := by
    filter_upwards [hX, hY, hsum, hsupp] with ω hXω hYω hsω hsuppω hωA t f
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have htT : (t : ℝ) ≤ T := t.2.2
    -- the sum `∑ₓ |𝔷^m_n(t,x) - 𝔷_n(t,x)|` is at most `δ`
    have hle : (∑' x : ℤ, |zN n ψ ω t x - zN n φ ω t x|) ≤ δ := by
      have h1 : ENNReal.ofReal (∑' x : ℤ, |zN n ψ ω t x - zN n φ ω t x|) ≤ ENNReal.ofReal δ :=
        (le_iSup₂ (f := fun (s : ℝ) (_ : s ∈ Set.Icc (0 : ℝ) T) =>
          ENNReal.ofReal (∑' x : ℤ, |zN n ψ ω s x - zN n φ ω s x|)) (t : ℝ) t.2).trans
          (not_lt.1 hωA)
      exact (ENNReal.ofReal_le_ofReal_iff hδ.le).1 h1
    have hs : Summable (zN n φ ω t) := by
      have := hsω t ht0 0 (by norm_num)
      simpa using this
    have hsupp' : ∀ x, x ∉ box (m : ℕ∞) → ψ (n * t / 2) ω x = 0 := fun x hx =>
      hsuppω ⟨n * t / 2, by have := zero_le_one.trans hn; positivity⟩ x hx
    rw [hXω t, hYω t]
    refine (abs_integral_rescaledMeasure_box_sub_le hn m ψ φ ω t hs hsupp' f).trans ?_
    have hS0 : 0 ≤ ∑' x : ℤ, |zN n ψ ω t x - zN n φ ω t x| :=
      tsum_nonneg fun _ => abs_nonneg _
    have hv : varrhoN n t * (∑' x : ℤ, |zN n ψ ω t x - zN n φ ω t x|) ≤ ε := by
      calc varrhoN n t * (∑' x : ℤ, |zN n ψ ω t x - zN n φ ω t x|)
          ≤ Real.exp T * δ :=
            mul_le_mul (thmMain_varrhoN_le hn ht0 htT) hle hS0 (Real.exp_pos _).le
        _ = ε := by
            rw [hδ_def, mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [mul_comm ε]
    exact mul_le_mul_of_nonneg_left hv (norm_nonneg f)
  obtain ⟨N, hN, hNgood⟩ : ∃ N : Set Ω, μ N = 0 ∧ ∀ ω ∉ N, ω ∉ A → ∀ (t : Set.Icc (0 : ℝ) T)
      (f : ℝ →ᵇ ℝ),
      |(∫ x, f x ∂(X ω t : Measure ℝ)) - ∫ x, f x ∂(Y ω t : Measure ℝ)| ≤ ε * ‖f‖ := by
    rw [ae_iff] at hgood
    exact ⟨_, hgood, fun ω hω => not_not.1 hω⟩
  calc μ {ω | ¬ ∀ (t : Set.Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
        |(∫ x, f x ∂(X ω t : Measure ℝ)) - ∫ x, f x ∂(Y ω t : Measure ℝ)| ≤ ε * ‖f‖}
      ≤ μ (N ∪ A) := measure_mono fun ω hω => by
        by_contra h
        simp only [Set.mem_union, not_or] at h
        exact hω (hNgood ω h.1 h.2)
    _ ≤ μ N + μ A := measure_union_le _ _
    _ = μ A := by rw [hN, zero_add]
    _ ≤ prop81Rhs n T δ m := prop81_bound hB hφ hm1 hψ hn hT hδ hℓ

/-- **Theorem 1.2** (all sizes `L_k ∈ ℤ_{≥1} ∪ {∞}`): the statement of `main_theorem`, proved as
at the end of Section 8 of the article (see the module docstring). `main_theorem_lib` quotes it. -/
theorem thmMain_proof
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ∞) (hL₁ : ∀ k, 1 ≤ L k)
    (hL : Tendsto (fun k => (L k : ℝ≥0∞) / ENNReal.ofReal (n k ^ (3 / 4 : ℝ))) atTop (𝓝 ⊤))
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction (L k) (𝓕 k) (B k) (ψ k) (μ k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ')
    (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝒵n : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
      (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵n k ω t : Measure ℝ) = rescaledMeasure (L k) (n k) (density (ψ k) ω) t) ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν := by
  classical
  -- the wave functions on `ℤ`, coupled to the given ones
  choose φ hφ hφψ using fun k => thmMain_exists_top (hB k) (hψ k)
  obtain ⟨Y, 𝒵, hY, h𝒵, hconv⟩ := main_theorem_top n hn₁ hn μ
    (fun k => nullAug (μ k) (𝓕 k)) B (fun k => (hB k).nullAug) φ hφ ν 𝓖 S hS Z hZ T hT
  -- the versions of `𝒵_{n_k}`
  choose X hXm hX hXY using fun k =>
    thmMain_exists_version (hψ k) (hn₁ k) (hconv.forall_aemeasurable k) (hY k) (hφψ k)
  refine ⟨X, 𝒵, hX, h𝒵, tendstoInDistribution_of_close hXm hconv fun ε hε => ?_⟩
  have hδ : 0 < ε * Real.exp (-T) := mul_pos hε (Real.exp_pos _)
  obtain ⟨hev, hlim⟩ := prop81Rhs_tendsto_enat n hn₁ hn L hL hT hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev] with k hk
  by_cases hLk : L k = ⊤
  · simp only [hLk, ↓reduceIte]
    rw [hXY k hLk]
    refine (measure_mono_null (t := (∅ : Set (Ω k))) (fun ω hω => (hω fun t f => ?_).elim)
      measure_empty).le
    rw [sub_self, abs_zero]
    exact mul_nonneg hε.le (norm_nonneg f)
  · simp only [hLk, ↓reduceIte]
    have hm : ((L k).toNat : ℕ∞) = L k := ENat.natCast_toNat hLk
    have hm1 : 1 ≤ (L k).toNat := by
      have := hL₁ k
      rw [← hm] at this
      exact_mod_cast this
    exact thmMain_close (hB k).nullAug (hφ k) hm hm1 (hψ k).nullAug (hn₁ k) hT hε
      (hk.resolve_left hLk) (hX k) (hY k)

end QSSEPtoKPZ
