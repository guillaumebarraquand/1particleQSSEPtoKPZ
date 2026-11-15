/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.Martingales.CovariationAlgebra
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pairing of Walsh integrals with a martingale (task J1, auxiliary)

Used in Step 2 of the proof of Proposition 7.2 ("since both sides are isometries, this remains
true for all predictable `k`"), to identify `∫∫ 𝟙_{(u,v]}(s) φ(y) Z(s,y) ξ(ds dy)` with
`M^φ(v) - M^φ(u)`.

* `prop72Noise_integral_iter`: `𝔼 ∫_0^t ∫ F(r,y) dy dr = ∫ F d(ℙ ⊗ Leb²)` for `F` integrable
  vanishing for `r ∉ (0,t]`.
* `prop72Noise_pairing`: let `V` be a process, constant after `T₀`, whose covariation with every
  `ξ_t((a,b])` is `∫_0^t ∫_a^b κ` on every horizon `n ≥ T₀`, with `κ ∈ L²(ℙ ⊗ Leb²)`. Then for
  every Walsh integral `X = ∫ g dξ`, `𝔼[X V_{T₀}] = 𝔼 ∫∫ g κ`. Proof by induction on the
  derivation of `X`: for an elementary integrand `c 𝟙_{(s,t] × (a,b]}`, the martingale property
  of `V` and the covariation give `𝔼[c (ξ_t - ξ_s)((a,b]) V] = 𝔼[c (A_t - A_s)]`; sums are
  linear; `L²` limits pass to the limit on both sides.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- `∫ ω, ∫_0^t ∫ F(r,y,ω) dy dr = ∫ F d(μ ⊗ Leb²)` for `F` integrable, vanishing for
`r ∉ (0,t]`. -/
theorem prop72Noise_integral_iter {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [SFinite μ] {F : ℝ → ℝ → Ω → ℝ} (hF : Integrable (uncurryField F) (μ.prod volume)) {t : ℝ}
    (ht : 0 ≤ t) (hz : ∀ r y ω, r ∉ Set.Ioc 0 t → F r y ω = 0) :
    ∫ ω, (∫ r in (0 : ℝ)..t, ∫ y, F r y ω) ∂μ = ∫ p, uncurryField F p ∂(μ.prod volume) := by
  rw [integral_prod _ hF]
  refine integral_congr_ae ?_
  filter_upwards [hF.prod_right_ae] with ω hω
  have hω' : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ω) ((volume : Measure ℝ).prod volume) := hω
  change ∫ r in (0 : ℝ)..t, ∫ y, F r y ω =
    ∫ z : ℝ × ℝ, F z.1 z.2 ω ∂((volume : Measure ℝ).prod volume)
  rw [integral_prod _ hω', intervalIntegral.integral_of_le ht,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro r hr
  simp only [hz r _ _ hr, integral_zero]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `L²` continuity of `f ↦ ∫ f w` for a fixed `w ∈ L²`. -/
private lemma pairing_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ}
    {f0 w : α → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (hf0 : MemLp f0 2 μ) (hw : MemLp w 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - f0) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x * w x ∂μ) atTop (𝓝 (∫ x, f0 x * w x ∂μ)) := by
  have hF : Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hf0.toLp f0)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ hf0).2 hlim
  have hI := Filter.Tendsto.inner (𝕜 := ℝ) hF (tendsto_const_nhds (x := hw.toLp w))
  have e : ∀ (g : α → ℝ) (hg : MemLp g 2 μ),
      inner ℝ (hg.toLp g) (hw.toLp w) = ∫ x, g x * w x ∂μ := by
    intro g hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hw.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  simpa only [e] using hI

/-- Tower property in the form `𝔼[f U] = 𝔼[f U']` when `𝔼[U | m] = U'` and `f` is
`m`-measurable. -/
private lemma pairing_pull {ν : Measure Ω} [IsFiniteMeasure ν] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {f U U' : Ω → ℝ} (hf : AEStronglyMeasurable[m] f ν)
    (hfU : Integrable (fun ω => f ω * U ω) ν) (hU : Integrable U ν)
    (hce : ν[U | m] =ᵐ[ν] U') : ∫ ω, f ω * U ω ∂ν = ∫ ω, f ω * U' ω ∂ν := by
  have h1 : ν[(fun ω => f ω * U ω) | m] =ᵐ[ν] fun ω => f ω * ν[U | m] ω :=
    condExp_mul_of_aestronglyMeasurable_left hf hfU hU
  rw [← integral_condExp hm]
  refine integral_congr_ae ?_
  filter_upwards [h1, hce] with ω e1 e2
  rw [e1, e2]

/-- The box term: `𝔼[c ∫_0^τ ∫_a^b κ] = ∫ 𝟙_{(0,τ] × (a,b]} c κ d(ν ⊗ Leb²)`, with
integrability. -/
private lemma pairing_box {ν : Measure Ω} [IsFiniteMeasure ν] {c : Ω → ℝ} (hc : Measurable c)
    {C : ℝ} (hC : ∀ ω, |c ω| ≤ C) {κ : ℝ → ℝ → Ω → ℝ}
    (hκ : MemLp (uncurryField κ) 2 (ν.prod volume)) (a b : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun p => ((Set.univ : Set Ω) ×ˢ (Set.Ioc 0 τ ×ˢ Set.Ioc a b)).indicator
      (fun p => c p.1) p * uncurryField κ p) (ν.prod volume) ∧
    ∫ ω, c ω * (∫ r in (0 : ℝ)..τ, ∫ y, (if a < y ∧ y ≤ b then κ r y ω else 0)) ∂ν =
      ∫ p, ((Set.univ : Set Ω) ×ˢ (Set.Ioc 0 τ ×ˢ Set.Ioc a b)).indicator
        (fun p => c p.1) p * uncurryField κ p ∂(ν.prod volume) := by
  set E : Set (Ω × ℝ × ℝ) := (Set.univ : Set Ω) ×ˢ (Set.Ioc 0 τ ×ˢ Set.Ioc a b) with hEdef
  have hE : MeasurableSet E := MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hEfin : (ν.prod volume) E ≠ ∞ := by
    rw [hEdef, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top ν _)
      (ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne)
  set B : Ω × ℝ × ℝ → ℝ := E.indicator fun p => c p.1 with hBdef
  have hB : MemLp B 2 (ν.prod volume) := by
    refine (memLp_indicator_const 2 hE.nullMeasurableSet C (Or.inr hEfin)).of_le
      ((hc.comp measurable_fst).indicator hE).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    by_cases hp : p ∈ E
    · simp only [hBdef, Set.indicator_of_mem hp, Real.norm_eq_abs]
      exact (hC p.1).trans (le_abs_self C)
    · simp [hBdef, Set.indicator_of_notMem hp]
  have hint : Integrable (fun p => B p * uncurryField κ p) (ν.prod volume) :=
    hB.integrable_mul hκ
  refine ⟨hint, ?_⟩
  have hit := prop72Noise_integral_iter (F := fun r y ω => B (ω, r, y) * κ r y ω) hint hτ
    fun r y ω hr => by simp [hBdef, hEdef, Set.indicator_of_notMem, hr]
  refine Eq.trans ?_ hit
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only
  rw [intervalIntegral.integral_of_le hτ, intervalIntegral.integral_of_le hτ,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [← integral_const_mul]
  congr 1
  funext y
  by_cases hy : a < y ∧ y ≤ b
  · have hm : (ω, r, y) ∈ E := by
      simp only [hEdef, Set.mem_prod, Set.mem_univ, true_and]
      exact ⟨hr, hy⟩
    simp [hBdef, Set.indicator_of_mem hm, hy]
  · have hm : (ω, r, y) ∉ E := by
      simp only [hEdef, Set.mem_prod, Set.mem_univ, true_and, not_and]
      exact fun _ => hy
    simp [hBdef, Set.indicator_of_notMem hm, hy]

/-- Pairing of Walsh integrals with a martingale `V` whose covariation with every
`ξ_t((a,b])` is `∫_0^t ∫_a^b κ`: `𝔼[X V_{T0}] = 𝔼 ∫∫ g κ` for `X = ∫ g dξ`. -/
theorem prop72Noise_pairing {𝓖 : Filtration ℝ≥0 mΩ}
    {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω} (hS : IsWhiteNoise 𝓖 S ν) {V : ℝ → Ω → ℝ}
    {κ : ℝ → ℝ → Ω → ℝ} {T0 : ℝ} (hT0 : 0 ≤ T0) (hκ : MemLp (uncurryField κ) 2 (ν.prod volume))
    (hV : ∀ t, T0 ≤ t → V t = V T0)
    (hcov : ∀ n : ℝ, T0 ≤ n → ∀ a b : ℝ, a ≤ b →
      HasCovariation n 𝓖 (fun t ω => S t b ω - S t a ω) V
        (fun t ω => ∫ r in (0 : ℝ)..t, ∫ y, (if a < y ∧ y ≤ b then κ r y ω else 0)) ν)
    {g : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν g X) :
    ∫ ω, X ω * V T0 ω ∂ν = ∫ p, uncurryField g p * uncurryField κ p ∂(ν.prod volume) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hV2 : MemLp (V T0) 2 ν := by
    have h := (hcov T0 le_rfl 0 0 le_rfl).right.memLp T0.toNNReal
      (by rw [Real.coe_toNNReal _ hT0])
    rwa [Real.coe_toNNReal _ hT0] at h
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    obtain ⟨C, hC⟩ := hbdd
    set N : ℝ≥0 := max t T0.toNNReal with hNdef
    have hTN : T0 ≤ (N : ℝ) := by
      rw [hNdef, NNReal.coe_max, Real.coe_toNNReal _ hT0]
      exact le_max_right _ _
    have htN : t ≤ N := le_max_left _ _
    have hsN : s ≤ N := hst.trans htN
    have cov := hcov N hTN a b hab
    set D : ℝ → Ω → ℝ := fun τ ω => S τ b ω - S τ a ω with hDdef
    set A : ℝ → Ω → ℝ := fun τ ω =>
      ∫ r in (0 : ℝ)..τ, ∫ y, (if a < y ∧ y ≤ b then κ r y ω else 0) with hAdef
    have hVN : V T0 = V N := (hV N hTN).symm
    have hD : ∀ τ : ℝ≥0, τ ≤ N → MemLp (D τ) 2 ν := fun τ h =>
      cov.left.memLp τ (NNReal.coe_le_coe.2 h)
    have hVm : ∀ τ : ℝ≥0, τ ≤ N → MemLp (V τ) 2 ν := fun τ h =>
      cov.right.memLp τ (NNReal.coe_le_coe.2 h)
    have hAi : ∀ τ : ℝ≥0, τ ≤ N → Integrable (A τ) ν := fun τ h =>
      cov.integrable_cov τ (NNReal.coe_le_coe.2 h)
    have hcm : Measurable c := hc.mono (𝓖.le s) le_rfl
    have hcg : AEStronglyMeasurable c ν := hcm.aestronglyMeasurable
    have hcb : ∀ᵐ ω ∂ν, ‖c ω‖ ≤ C := ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω
    have hci : ∀ {F : Ω → ℝ}, Integrable F ν → Integrable (fun ω => c ω * F ω) ν :=
      fun hF => hF.bdd_mul hcg hcb
    have hDV : ∀ τ σ : ℝ≥0, τ ≤ N → σ ≤ N → Integrable (fun ω => D τ ω * V σ ω) ν :=
      fun τ σ h1 h2 => (hD τ h1).integrable_mul (hVm σ h2)
    have hcDV : ∀ τ σ : ℝ≥0, τ ≤ N → σ ≤ N →
        Integrable (fun ω => c ω * D τ ω * V σ ω) ν := fun τ σ h1 h2 => by
      simpa only [mul_assoc] using hci (hDV τ σ h1 h2)
    -- the martingale property of `V`
    have hpull : ∀ τ : ℝ≥0, s ≤ τ → τ ≤ N →
        ∫ ω, c ω * D τ ω * V N ω ∂ν = ∫ ω, c ω * D τ ω * V τ ω ∂ν := by
      intro τ hsτ hτN
      have hf : AEStronglyMeasurable[𝓖 τ] (fun ω => c ω * D τ ω) ν :=
        ⟨_, ((hc.mono (𝓖.mono hsτ) le_rfl).mul
          ((hS.adapted τ b).sub (hS.adapted τ a))).stronglyMeasurable, EventuallyEq.rfl⟩
      exact pairing_pull (𝓖.le τ) hf (hcDV τ N hτN le_rfl)
        ((hVm N le_rfl).integrable one_le_two) (cov.right.condExp τ N hτN le_rfl)
    -- the covariation
    have h3 : ν[fun ω => D t ω * V t ω - A t ω | 𝓖 s] =ᵐ[ν]
        fun ω => D s ω * V s ω - A s ω := cov.condExp_mul s t hst (NNReal.coe_le_coe.2 htN)
    have hX3 : ∀ τ : ℝ≥0, τ ≤ N → Integrable (fun ω => D τ ω * V τ ω - A τ ω) ν :=
      fun τ h => (hDV τ τ h h).sub (hAi τ h)
    have e3 : ∫ ω, c ω * (D t ω * V t ω - A t ω) ∂ν =
        ∫ ω, c ω * (D s ω * V s ω - A s ω) ∂ν :=
      pairing_pull (𝓖.le s) ⟨c, hc.stronglyMeasurable, EventuallyEq.rfl⟩
        (hci (hX3 t htN)) (hX3 t htN) h3
    have hsplit : ∀ τ : ℝ≥0, τ ≤ N → ∫ ω, c ω * D τ ω * V τ ω ∂ν =
        ∫ ω, c ω * (D τ ω * V τ ω - A τ ω) ∂ν + ∫ ω, c ω * A τ ω ∂ν := by
      intro τ h
      rw [← integral_add (hci (hX3 τ h)) (hci (hAi τ h))]
      congr 1
      funext ω
      ring
    -- the box terms
    obtain ⟨hit, bt⟩ := pairing_box hcm hC hκ a b t.coe_nonneg
    obtain ⟨his, bs⟩ := pairing_box hcm hC hκ a b s.coe_nonneg
    have key : ∀ p : Ω × ℝ × ℝ,
        uncurryField (fun r y ω => if (s : ℝ) < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then c ω else 0) p *
          uncurryField κ p =
        ((Set.univ : Set Ω) ×ˢ (Set.Ioc 0 (t : ℝ) ×ˢ Set.Ioc a b)).indicator
          (fun p => c p.1) p * uncurryField κ p -
        ((Set.univ : Set Ω) ×ˢ (Set.Ioc 0 (s : ℝ) ×ˢ Set.Ioc a b)).indicator
          (fun p => c p.1) p * uncurryField κ p := by
      rintro ⟨ω, r, y⟩
      rw [← sub_mul]
      congr 1
      simp only [uncurryField, Set.indicator_apply, Set.mem_prod, Set.mem_univ, true_and,
        Set.mem_Ioc]
      by_cases hy : a < y ∧ y ≤ b
      · rcases lt_or_ge (s : ℝ) r with h1 | h1
        · have h0 : 0 < r := lt_of_le_of_lt s.2 h1
          by_cases h2 : r ≤ (t : ℝ)
          · simp [h1, h2, h0, not_le.2 h1, hy]
          · simp [h1, h2, h0, not_le.2 h1, hy]
        · have h2 : r ≤ (t : ℝ) := h1.trans (NNReal.coe_le_coe.2 hst)
          by_cases h0 : 0 < r
          · simp [not_lt.2 h1, h1, h2, h0, hy]
          · simp [not_lt.2 h1, h1, h2, h0, hy]
      · simp [hy]
    -- assembly
    have hL : ∀ ω, c ω * rectMass S s t a b ω * V T0 ω =
        c ω * D t ω * V N ω - c ω * D s ω * V N ω := by
      intro ω
      rw [hVN]
      simp only [rectMass, hDdef]
      ring
    have eR : ∫ p, uncurryField (fun r y ω => if (s : ℝ) < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then
        c ω else 0) p * uncurryField κ p ∂(ν.prod volume) =
        ∫ p, ((Set.univ : Set Ω) ×ˢ (Set.Ioc 0 (t : ℝ) ×ˢ Set.Ioc a b)).indicator
          (fun p => c p.1) p * uncurryField κ p ∂(ν.prod volume) -
        ∫ p, ((Set.univ : Set Ω) ×ˢ (Set.Ioc 0 (s : ℝ) ×ˢ Set.Ioc a b)).indicator
          (fun p => c p.1) p * uncurryField κ p ∂(ν.prod volume) := by
      rw [← integral_sub hit his]
      exact integral_congr_ae (ae_of_all _ key)
    refine Eq.trans ?_ eR.symm
    simp only [hL]
    rw [integral_sub (hcDV t N htN le_rfl) (hcDV s N hsN le_rfl),
      hpull t hst htN, hpull s le_rfl hsN, hsplit t htN, hsplit s hsN, e3, ← bt, ← bs]
    ring
  | add h h' X X' hX hX' ih ih' =>
    have hXm := (IsWalshIntegral.isometry_lib hS hX)
    have hXm' := (IsWalshIntegral.isometry_lib hS hX')
    have e1 : ∫ ω, (X ω + X' ω) * V T0 ω ∂ν =
        ∫ ω, X ω * V T0 ω ∂ν + ∫ ω, X' ω * V T0 ω ∂ν := by
      have i1 : Integrable (fun ω => X ω * V T0 ω) ν := hXm.2.1.integrable_mul hV2
      have i2 : Integrable (fun ω => X' ω * V T0 ω) ν := hXm'.2.1.integrable_mul hV2
      rw [← integral_add i1 i2]
      congr 1
      funext ω
      ring
    have e2 : ∫ p, uncurryField (fun r y ω => h r y ω + h' r y ω) p * uncurryField κ p
        ∂(ν.prod volume) = ∫ p, uncurryField h p * uncurryField κ p ∂(ν.prod volume) +
          ∫ p, uncurryField h' p * uncurryField κ p ∂(ν.prod volume) := by
      have i1 : Integrable (fun p => uncurryField h p * uncurryField κ p) (ν.prod volume) :=
        hXm.1.integrable_mul hκ
      have i2 : Integrable (fun p => uncurryField h' p * uncurryField κ p) (ν.prod volume) :=
        hXm'.1.integrable_mul hκ
      rw [← integral_add i1 i2]
      congr 1
      funext p
      simp only [uncurryField]
      ring
    rw [e1, e2, ih, ih']
  | limit h X hs Xs hXs hh2 hX2 hlimh hlimX ih =>
    have h1 := pairing_tendsto (fun k => (IsWalshIntegral.isometry_lib hS (hXs k)).2.1) hX2
      hV2 hlimX
    have h2 := pairing_tendsto (fun k => (IsWalshIntegral.isometry_lib hS (hXs k)).1) hh2
      hκ hlimh
    simp only [ih] at h1
    exact tendsto_nhds_unique h1 h2

end QSSEPtoKPZ
