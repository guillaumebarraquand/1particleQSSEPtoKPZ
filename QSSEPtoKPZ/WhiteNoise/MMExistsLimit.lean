/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.MMIntegral
public import QSSEPtoKPZ.Martingales.Doob

/-!
# Closure of martingale-measure integrals under energy limits (task G8b, auxiliary)

If `h_k · M` exists for every `k`, `h` is predictable and `𝔼 ∫_0^T ∫ (h_k - h)² q → 0`, then
`h · M` exists (`mmEx_of_tendsto`). Proof: by (7.10) and Doob's `L²` inequality,
`𝔼 sup_{[0,T]} (h · M)² ≤ 4 𝔼 ∫_0^T ∫ h² q` (`mmEx_doob`); along a subsequence with
`𝔼 ∫_0^T ∫ (h_{k_j} - h)² q ≤ 64⁻ʲ`, the series `∑ⱼ 4ʲ sup_{[0,T]} (X_{j+1} - X_j)²` has finite
expectation, so on an event `G` of full (outer) measure the processes converge uniformly on
`[0,T]` (Weierstrass test). The limit is `X = X_0 + ∑ⱼ (X_{j+1} - X_j)` on `G` and `0` off `G`:
continuous for every `ω`, almost everywhere strongly measurable at each time (an almost sure
limit), and `𝔼 sup_{[0,T]} (X_j - X)² → 0` by Fatou's lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {T : ℝ} {𝒢 : Filtration ℝ≥0 mΩ}
  {q : ℝ → ℝ → Ω → ℝ} {M : (ℝ → ℝ) → ℝ → Ω → ℝ}

/-- A martingale-measure integral vanishes at time `0` (`T ≥ 0`). -/
theorem mmEx_zero_at (hT : 0 ≤ T) {h : ℝ → ℝ → Ω → ℝ} {X : ℝ → Ω → ℝ}
    (hX : IsMMIntegral T 𝒢 q M μ h X) : X 0 =ᵐ[μ] 0 := by
  induction hX with
  | block s t hst a φ C hφ ha hab =>
    refine ae_of_all _ fun ω => ?_
    simp
  | add h h' X X' _ _ ih ih' =>
    filter_upwards [ih, ih'] with ω h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  | limit h X hs Xs _ hpred hcont hmeas hconv hsup ih =>
    exact mm_ae_zero_limit hT ih (hmeas 0 ⟨le_rfl, hT⟩) hsup

/-- The values at real times `r ∈ [0, T]` of a continuous `L²` martingale are in `L²`. -/
theorem mmEx_memLp {Y : ℝ → Ω → ℝ} (hY : IsCL2Mart T 𝒢 Y μ) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) : MemLp (Y r) 2 μ := by
  have := hY.memLp r.toNNReal (by rw [Real.coe_toNNReal r hr.1]; exact hr.2)
  rwa [Real.coe_toNNReal r hr.1] at this

/-- **Doob's inequality for martingale-measure integrals**:
`𝔼 sup_{[0,T]} (d · M)² ≤ 4 𝔼 ∫_0^T ∫ d² q`. -/
theorem mmEx_doob [IsProbabilityMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {d : ℝ → ℝ → Ω → ℝ} {D : ℝ → Ω → ℝ} (hD : IsMMIntegral T 𝒢 q M μ d D) :
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (D t ω ^ 2)) μ ∧
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (D t ω ^ 2) ∂μ ≤ 4 * mmEnergy μ T q d := by
  have hc := IsMMIntegral.hasCovariation hq hq0 hq1 hM hD hD
  obtain ⟨h1, h2⟩ := hc.left.lintegral_iSup_sq_le
  refine ⟨h1, h2.trans (mul_le_mul_right ?_ 4)⟩
  set τ : ℝ≥0 := T.toNNReal with hτdef
  have hτ : (τ : ℝ) = T := Real.coe_toNNReal T hT
  have hmem := hc.left.memLp τ hτ.le
  have hint1 : Integrable (fun ω => D τ ω * D τ ω) μ := hmem.integrable_mul hmem
  have hint2 := hc.integrable_cov τ hτ.le
  have hce := hc.condExp_mul 0 τ zero_le hτ.le
  have hE : ∫ ω, (D τ ω * D τ ω - (∫ r in (0 : ℝ)..τ, ∫ x, q r x ω * d r x ω * d r x ω)) ∂μ
      = 0 := by
    rw [← integral_condExp (𝒢.le 0), integral_congr_ae hce]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [mmEx_zero_at hT hD, hc.zero] with ω e1 e2
    simp only [Pi.zero_apply] at e1
    simp only [NNReal.coe_zero, e1, e2, mul_zero, sub_zero, Pi.zero_apply]
  rw [integral_sub hint1 hint2, sub_eq_zero] at hE
  rw [← hτ]
  calc ∫⁻ ω, ENNReal.ofReal (D τ ω ^ 2) ∂μ = ENNReal.ofReal (∫ ω, D τ ω ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
          (ae_of_all _ fun ω => sq_nonneg _)).symm
    _ = ENNReal.ofReal (∫ ω, (∫ r in (0 : ℝ)..τ, ∫ x, q r x ω * d r x ω * d r x ω) ∂μ) := by
        rw [← hE]; simp_rw [sq]
    _ ≤ ‖∫ ω, (∫ r in (0 : ℝ)..τ, ∫ x, q r x ω * d r x ω * d r x ω) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ ω, ‖∫ r in (0 : ℝ)..τ, ∫ x, q r x ω * d r x ω * d r x ω‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (τ : ℝ), ∫⁻ x, ‖q r x ω * d r x ω * d r x ω‖ₑ) ∂μ :=
        lintegral_mono fun ω => mm_enorm_mmBr_le (q := q) (T := (τ : ℝ)) d d ⟨τ.2, le_rfl⟩ ω
    _ = mmEnergy μ τ q d := by
        unfold mmEnergy
        congr 1; funext ω; congr 1; funext r; congr 1; funext x
        rw [Real.enorm_eq_ofReal_abs]
        congr 1
        rw [show q r x ω * d r x ω * d r x ω = d r x ω ^ 2 * q r x ω by ring,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (hq0 r x ω))]

/-- **Closure under energy limits**: if every `h_k · M` exists, `h` is predictable and
`𝔼 ∫_0^T ∫ (h_k - h)² q → 0`, then `h · M` exists. -/
theorem mmEx_of_tendsto [IsProbabilityMeasure μ] (hT : 0 ≤ T) (hq : MMPred 𝒢 q)
    (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (q r x ω)) ∂μ < ⊤)
    (hM : ∀ {φ ψ : ℝ → ℝ} {C C' : ℝ}, IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    {hs : ℕ → ℝ → ℝ → Ω → ℝ} {Xs : ℕ → ℝ → Ω → ℝ}
    (hXs : ∀ k, IsMMIntegral T 𝒢 q M μ (hs k) (Xs k)) (hhs : ∀ k, MMPred 𝒢 (hs k))
    {h : ℝ → ℝ → Ω → ℝ} (hh : MMPred 𝒢 h)
    (hlim : Tendsto (fun k => mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω)) atTop (𝓝 0)) :
    ∃ X : ℝ → Ω → ℝ, IsMMIntegral T 𝒢 q M μ h X := by
  classical
  -- a fast subsequence
  set ε : ℕ → ℝ := fun j => (1 / 64 : ℝ) ^ j with hεdef
  have hε0 : ∀ j, 0 < ε j := fun j => by positivity
  obtain ⟨φ, hφmono, hφ⟩ := Filter.extraction_forall_of_eventually
    (P := fun j k => mmEnergy μ T q (fun r x ω => hs k r x ω - h r x ω) ≤ ENNReal.ofReal (ε j))
    (fun j => (ENNReal.tendsto_nhds_zero.1 hlim) _ (ENNReal.ofReal_pos.2 (hε0 j)))
  set Y : ℕ → ℝ → Ω → ℝ := fun j => Xs (φ j) with hYdef
  -- Doob bounds for the differences
  have hdiff : ∀ j m, AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((Y j t ω - Y m t ω) ^ 2)) μ ∧
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal ((Y j t ω - Y m t ω) ^ 2) ∂μ ≤
        8 * (ENNReal.ofReal (ε j) + ENNReal.ofReal (ε m)) := by
    intro j m
    have hI := IsMMIntegral.add _ _ _ _ (hXs (φ j)) ((hXs (φ m)).const_mul (-1))
    obtain ⟨hA, hB⟩ := mmEx_doob hT hq hq0 hq1 hM hI
    have e : ∀ t ω, Xs (φ j) t ω + -1 * Xs (φ m) t ω = Y j t ω - Y m t ω := by
      intro t ω; simp only [hYdef]; ring
    simp only [e] at hA hB
    refine ⟨hA, hB.trans ?_⟩
    have hE := mmEnergy_lincomb_le (μ := μ) (T := T) hq hq0 ((hhs (φ j)).sub hh)
      ((hhs (φ m)).sub hh) 1 (-1)
    have e2 : (fun r x ω => 1 * (hs (φ j) r x ω - h r x ω) + -1 * (hs (φ m) r x ω - h r x ω)) =
        fun r x ω => hs (φ j) r x ω + -1 * hs (φ m) r x ω := by
      funext r x ω; ring
    rw [e2] at hE
    calc 4 * mmEnergy μ T q (fun r x ω => hs (φ j) r x ω + -1 * hs (φ m) r x ω)
        ≤ 4 * (ENNReal.ofReal (2 * 1 ^ 2) * ENNReal.ofReal (ε j) +
            ENNReal.ofReal (2 * (-1) ^ 2) * ENNReal.ofReal (ε m)) := by
          gcongr
          exact hE.trans (add_le_add (mul_le_mul_right (hφ j) _) (mul_le_mul_right (hφ m) _))
      _ = 8 * (ENNReal.ofReal (ε j) + ENNReal.ofReal (ε m)) := by
          norm_num
          ring
  have hY : ∀ j, IsCL2Mart T 𝒢 (Y j) μ := fun j =>
    (IsMMIntegral.hasCovariation hq hq0 hq1 hM (hXs (φ j)) (hXs (φ j))).left
  -- the weighted series of squared increments has finite expectation
  set Δ : ℕ → Ω → ℝ≥0∞ := fun j ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal ((Y (j + 1) t ω - Y j t ω) ^ 2) with hΔdef
  set S : Ω → ℝ≥0∞ := fun ω => ∑' j, ENNReal.ofReal (4 ^ j) * Δ j ω with hSdef
  have hΔm : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal (4 ^ j) * Δ j ω) μ := fun j =>
    (hdiff (j + 1) j).1.const_mul _
  have hSm : AEMeasurable S μ := AEMeasurable.tsum hΔm
  have hSint : ∫⁻ ω, S ω ∂μ ≠ ⊤ := by
    rw [hSdef, lintegral_tsum hΔm]
    have hu : Summable (fun j : ℕ => (8 * (1 / 64) + 8) * (1 / 16 : ℝ) ^ j) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := ∑' j : ℕ, (8 * (1 / 64) + 8) * (1 / 16 : ℝ) ^ j)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hu]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (hdiff (j + 1) j).2 _).trans (le_of_eq ?_)
    have h8 : (8 : ℝ≥0∞) = ENNReal.ofReal 8 := by norm_num
    rw [h8, ← ENNReal.ofReal_add (hε0 _).le (hε0 _).le, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h4 : (4 : ℝ) ^ j * (1 / 64) ^ j = (1 / 16) ^ j := by rw [← mul_pow]; norm_num
    simp only [hεdef, pow_succ]
    linear_combination (8 * (1 / 64) + 8) * h4
  -- the good event
  set G : Set Ω := {ω | S ω < ⊤ ∧ ∀ j, ContinuousOn (fun t => Y j t ω) (Set.Icc 0 T)} with hGdef
  have hG : ∀ᵐ ω ∂μ, ω ∈ G := by
    filter_upwards [ae_lt_top' hSm hSint, ae_all_iff.2 fun j => (hY j).cont] with ω h1 h2
    exact ⟨h1, h2⟩
  have hbd : ∀ ω ∈ G, ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖Y (j + 1) t ω - Y j t ω‖ ≤ Real.sqrt (S ω).toReal * (1 / 2) ^ j := by
    intro ω hω j t ht
    have h1 : ENNReal.ofReal (4 ^ j) * ENNReal.ofReal ((Y (j + 1) t ω - Y j t ω) ^ 2) ≤ S ω :=
      (mul_le_mul_right (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal ((Y (j + 1) t ω - Y j t ω) ^ 2)) t ht) _).trans
        (ENNReal.le_tsum (f := fun j => ENNReal.ofReal (4 ^ j) * Δ j ω) j)
    rw [← ENNReal.ofReal_mul (by positivity)] at h1
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hω.1.ne).1 h1
    have h3 : (2 ^ j * |Y (j + 1) t ω - Y j t ω|) ^ 2 ≤ (S ω).toReal := by
      rw [mul_pow, sq_abs, ← pow_mul, mul_comm j 2, pow_mul]
      norm_num
      exact h2
    have h4 := Real.abs_le_sqrt h3
    rw [abs_of_nonneg (by positivity)] at h4
    rw [Real.norm_eq_abs]
    have h5 : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    calc |Y (j + 1) t ω - Y j t ω| = (1 / 2 : ℝ) ^ j * (2 ^ j * |Y (j + 1) t ω - Y j t ω|) := by
          rw [← mul_assoc, h5, one_mul]
      _ ≤ (1 / 2 : ℝ) ^ j * Real.sqrt (S ω).toReal := by gcongr
      _ = _ := mul_comm _ _
  have hsum : ∀ ω, Summable (fun j : ℕ => Real.sqrt (S ω).toReal * (1 / 2 : ℝ) ^ j) := fun ω =>
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  -- the limit process
  set X : ℝ → Ω → ℝ := fun t ω =>
    if ω ∈ G then Y 0 t ω + ∑' j, (Y (j + 1) t ω - Y j t ω) else 0 with hXdef
  have hconvY : ∀ ω ∈ G, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun j => Y j t ω) atTop (𝓝 (X t ω)) := by
    intro ω hω t ht
    have hs := (Summable.of_norm_bounded (hsum ω) (fun j => hbd ω hω j t ht)).hasSum.tendsto_sum_nat
    have e : ∀ N, Y 0 t ω + ∑ j ∈ Finset.range N, (Y (j + 1) t ω - Y j t ω) = Y N t ω := by
      intro N
      have := Finset.sum_range_sub (fun j => Y j t ω) N
      rw [this]; ring
    simp only [hXdef, hω, ↓reduceIte]
    exact (tendsto_const_nhds.add hs).congr e
  have hcont : ∀ ω, ContinuousOn (fun r => X r ω) (Set.Icc 0 T) := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hXdef, hω, ↓reduceIte]
      exact (hω.2 0).add (continuousOn_tsum (fun j => (hω.2 (j + 1)).sub (hω.2 j)) (hsum ω)
        (fun j t ht => hbd ω hω j t ht))
    · simp only [hXdef, hω, ↓reduceIte]
      exact continuousOn_const
  have hmeas : ∀ r ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (X r) μ := by
    intro r hr
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun j => Y j r)
      (fun j => (mmEx_memLp (hY j) hr).aestronglyMeasurable) ?_
    filter_upwards [hG] with ω hω
    exact hconvY ω hω r hr
  -- convergence in `L²(ℙ; sup_{[0,T]})`, by Fatou's lemma
  have hsup : Tendsto (fun j => ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal ((Y j r ω - X r ω) ^ 2)) ∂μ) atTop (𝓝 0) := by
    have hb : ∀ j, ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal ((Y j r ω - X r ω) ^ 2)) ∂μ ≤
        16 * ENNReal.ofReal (ε j) := by
      intro j
      calc ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal ((Y j r ω - X r ω) ^ 2)) ∂μ
          ≤ ∫⁻ ω, liminf (fun m => ⨆ r ∈ Set.Icc (0 : ℝ) T,
              ENNReal.ofReal ((Y j r ω - Y m r ω) ^ 2)) atTop ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hG] with ω hω
            refine iSup₂_le fun r hr => ?_
            have ht : Tendsto (fun m => ENNReal.ofReal ((Y j r ω - Y m r ω) ^ 2)) atTop
                (𝓝 (ENNReal.ofReal ((Y j r ω - X r ω) ^ 2))) :=
              (ENNReal.continuous_ofReal.tendsto _).comp
                ((tendsto_const_nhds.sub (hconvY ω hω r hr)).pow 2)
            rw [← ht.liminf_eq]
            exact liminf_le_liminf (Eventually.of_forall fun m =>
              le_iSup₂ (f := fun r (_ : r ∈ Set.Icc (0 : ℝ) T) =>
                ENNReal.ofReal ((Y j r ω - Y m r ω) ^ 2)) r hr)
        _ ≤ liminf (fun m => ∫⁻ ω, ⨆ r ∈ Set.Icc (0 : ℝ) T,
              ENNReal.ofReal ((Y j r ω - Y m r ω) ^ 2) ∂μ) atTop :=
            lintegral_liminf_le' fun m => (hdiff j m).1
        _ ≤ 16 * ENNReal.ofReal (ε j) := by
            refine liminf_le_of_frequently_le' ((eventually_ge_atTop j).frequently.mono
              fun m hm => (hdiff j m).2.trans ?_)
            have : ENNReal.ofReal (ε m) ≤ ENNReal.ofReal (ε j) :=
              ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm)
            calc 8 * (ENNReal.ofReal (ε j) + ENNReal.ofReal (ε m))
                ≤ 8 * (ENNReal.ofReal (ε j) + ENNReal.ofReal (ε j)) := by gcongr
              _ = 16 * ENNReal.ofReal (ε j) := by ring
    have hε : Tendsto (fun j => 16 * ENNReal.ofReal (ε j)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (1 / 64 : ℝ)) (by norm_num) (by norm_num))
      rw [ENNReal.ofReal_zero] at this
      have h2 := ENNReal.Tendsto.const_mul this (Or.inr (by norm_num : (16 : ℝ≥0∞) ≠ ⊤))
      rw [mul_zero] at h2
      exact h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun _ => zero_le) hb
  exact ⟨X, IsMMIntegral.limit h X (fun j => hs (φ j)) Y (fun j => hXs (φ j)) hh hcont hmeas
    (hlim.comp hφmono.tendsto_atTop) hsup⟩

end QSSEPtoKPZ
