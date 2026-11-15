/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.LimitPoints.Defs
public import QSSEPtoKPZ.WhiteNoise.MMExists
public import QSSEPtoKPZ.WhiteNoise.LevyMulti
public import QSSEPtoKPZ.WhiteNoise.Product
public import QSSEPtoKPZ.WhiteNoise.WalshProcess
public import QSSEPtoKPZ.WhiteNoise.Prop72NoiseBuild
public import QSSEPtoKPZ.WhiteNoise.Prop72NoisePairing

/-!
# Proposition 7.2, Steps 1 and 2: the white noise and (7.11) for simple integrands (task J1)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task J1.
See `docs/stage4-design.md`, Section 1.2 (f), and `docs/stage4-interfaces.md`.

Hypotheses: those of `prop_7_2` (the conclusions of Proposition 7.1 for a filtration `𝒢`, and an
auxiliary white noise `S''` on `Ω''`). Step 1: the martingale measure `φ ↦ M^φ` (time-independent
`φ ∈ C_b³`) with intensity `Z²`, (7.9) by polarization, `h · M` (`IsMMIntegral`), (7.10).
Step 2: on `Ω × Ω''` with `prodFiltration`, `ξ_t(A) = ((𝟙_{Z>0}/Z) 𝟙_A) · M(t) +
∫_0^t ∫_A 𝟙_{Z=0} ξ'(ds dy)` for `t ≤ T`, extended after `T` by the increments of `ξ'`;
`isWhiteNoise_of_martingales`. Conclusion: a white noise `S` for a filtration `𝒢̄ ⊇ 𝒢` with
(7.11) for the simple integrands `h = 𝟙_{(u,v]}(s) φ(y)`:
`∫∫ 𝟙_{(u,v]}(s) φ(y) Z(s,y) ξ(ds dy) = M^φ(v) - M^φ(u)`, which is what Step 3 (task J2) uses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `(𝟙_{Z>0, a<y≤b} Z) (𝟙_{(u,v]}(r) φ(y)) = 𝟙_{(a,b]}(y) 𝟙_{(u,v]}(r) φ(y) Z(r,y)`, using
`Z ≥ 0`. -/
private lemma prop72Noise_kappa_id {Z : ℝ → ℝ → Ω → ℝ} (hZ0 : ∀ t x ω, 0 ≤ Z t x ω) {u v : ℝ}
    (hu : 0 ≤ u) (φ : ℝ → ℝ) (a b r y : ℝ) (ω : Ω) :
    (if 0 < prop72NoiseZp Z r y ω ∧ a < y ∧ y ≤ b then prop72NoiseZp Z r y ω else 0) *
      (if u < r ∧ r ≤ v then 1 * φ y else 0) =
      if a < y ∧ y ≤ b then (if u < r ∧ r ≤ v then φ y * Z r y ω else 0) else 0 := by
  by_cases hr : u < r ∧ r ≤ v
  · rw [prop72NoiseZp_of_nonneg Z (hu.trans hr.1.le)]
    by_cases hy : a < y ∧ y ≤ b
    · by_cases hz : 0 < Z r y ω
      · simp only [hr, hy, hz, and_self, ↓reduceIte]; ring
      · have h0 : Z r y ω = 0 := le_antisymm (not_lt.1 hz) (hZ0 r y ω)
        simp [hr, hy, h0]
    · simp [hy]
  · simp [hr]

/-- `Z² (𝟙_{(u,v]} φ)² = (𝟙_{(u,v]} φ Z)²`. -/
private lemma prop72Noise_kappa_sq (Z : ℝ → ℝ → Ω → ℝ) {u v : ℝ} (hu : 0 ≤ u) (φ : ℝ → ℝ)
    (r y : ℝ) (ω : Ω) :
    prop72NoiseZp Z r y ω ^ 2 * (if u < r ∧ r ≤ v then 1 * φ y else 0) *
      (if u < r ∧ r ≤ v then 1 * φ y else 0) =
      (if u < r ∧ r ≤ v then φ y * Z r y ω else 0) ^ 2 := by
  by_cases hr : u < r ∧ r ≤ v
  · rw [prop72NoiseZp_of_nonneg Z (hu.trans hr.1.le)]
    simp only [hr, and_self, ↓reduceIte]; ring
  · simp [hr]

set_option linter.unusedVariables false in
/-- **Proposition 7.2, Steps 1–2.** -/
theorem prop72_noise {Pr : Measure Ω} [IsProbabilityMeasure Pr] {𝒢 : Filtration ℝ≥0 mΩ}
    {T : ℝ} (hT : 0 < T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    {Z : ℝ → ℝ → Ω → ℝ}
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (hZ0 : ∀ t x ω, 0 ≤ Z t x ω)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z t x ω))
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
    {𝓖'' : Filtration ℝ≥0 m''} {S'' : ℝ → ℝ → Ω'' → ℝ} (hS'' : IsWhiteNoise 𝓖'' S'' ν'') :
    ∃ (𝒢b : Filtration ℝ≥0 (mΩ.prod m'')) (S : ℝ → ℝ → Ω × Ω'' → ℝ),
      (∀ t, (𝒢 t).comap Prod.fst ≤ 𝒢b t) ∧ IsWhiteNoise 𝒢b S (Pr.prod ν'') ∧
      ∀ (φ : ℝ → ℝ) (C : ℝ), IsC13 T (fun _ => φ) (fun _ _ => 0) C →
        ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ T →
        IsWalshIntegral 𝒢b S (Pr.prod ν'')
          (fun s y ω => if u < s ∧ s ≤ v then φ y * Z s y ω.1 else 0)
          (fun ω => limMart Y (fun _ => φ) (fun _ _ => 0) v ω.1 -
            limMart Y (fun _ => φ) (fun _ _ => 0) u ω.1) := by
  classical
  obtain ⟨S, hS, hcovS⟩ := prop72Noise_build hT hZp hZ2 hmart hS''
  refine ⟨prodFiltration 𝒢 𝓖'' (Pr.prod ν''), S, fun t => comap_fst_le_prodFiltration _ t, hS, ?_⟩
  intro φ C hφ u v hu huv hvT
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
  have hv0 : 0 ≤ v := hu.trans huv
  -- `M^φ(· ∧ v) - M^φ(· ∧ u)` is the integral of the simple integrand `𝟙_{(u,v]} φ`
  set Vb : ℝ → Ω → ℝ := fun r ω => 1 * (M φ (min r v) ω - M φ (min r u) ω) with hVb
  have hb : IsMMIntegral T 𝒢 q M Pr (fun r x ω => if u < r ∧ r ≤ v then 1 * φ x else 0) Vb :=
    IsMMIntegral.block ⟨u, hu⟩ ⟨v, hv0⟩ (by exact_mod_cast huv) (fun _ => 1) φ C hφ
      measurable_const ⟨1, fun _ => by simp⟩
  set κ : ℝ → ℝ → Ω × Ω'' → ℝ := fun s y ω => if u < s ∧ s ≤ v then φ y * Z s y ω.1 else 0
    with hκ
  obtain ⟨c, -, hc⟩ := hφ.bound
  have hφb : ∀ x, |φ x| ≤ c 0 := fun x => (hc 0 ⟨le_rfl, hT.le⟩ x).1
  have hφm : Measurable φ := (hφ.contDiff 0 ⟨le_rfl, hT.le⟩).continuous.measurable
  -- `κ = 𝟙_{(u,v]} φ Z` is predictable, with finite energy
  have hκp : Measurable[(𝒢b.predictable).prod (borel ℝ)]
      fun p : (ℝ≥0 × (Ω × Ω'')) × ℝ => κ p.1.1 p.2 p.1.2 := by
    have hz := measurable_predictable_prod_fst (𝒢₂ := 𝓖'') P hZp
    have he : Measurable[(𝒢b.predictable).prod (borel ℝ)]
        fun p : (ℝ≥0 × (Ω × Ω'')) × ℝ => φ p.2 :=
      hφm.comp (measurable_snd.mono le_rfl BorelSpace.measurable_eq.le)
    have hI : MeasurableSet[(𝒢b.predictable).prod (borel ℝ)]
        (Prod.fst ⁻¹' (Set.Ioc u.toNNReal v.toNNReal ×ˢ Set.univ) :
          Set ((ℝ≥0 × (Ω × Ω'')) × ℝ)) :=
      (@measurable_fst _ _ (𝒢b.predictable) (borel ℝ))
        (measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ)
    have e : {p : (ℝ≥0 × (Ω × Ω'')) × ℝ | u < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) ≤ v} =
        Prod.fst ⁻¹' (Set.Ioc u.toNNReal v.toNNReal ×ˢ Set.univ) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioc, Set.mem_univ,
        and_true, Real.toNNReal_lt_iff_lt_coe hu, Real.le_toNNReal_iff_coe_le hv0]
    refine Measurable.ite ?_ (he.mul hz) measurable_const
    rw [e]; exact hI
  have hκ2 : ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ y, ENNReal.ofReal (κ s y ω ^ 2)) ∂P < ⊤ := by
    have hle : ∀ s y (ω : Ω × Ω''), ENNReal.ofReal (κ s y ω ^ 2) ≤
        ENNReal.ofReal (c 0 ^ 2) * ENNReal.ofReal (Z s y ω.1 ^ 2) := by
      intro s y ω
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [hκ]
      split_ifs
      · rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.1 (hφb y)).1 (abs_le.1 (hφb y)).2)
          (sq_nonneg _)
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    have hG : Measurable fun ω₁ : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ y,
        ENNReal.ofReal (Z s y ω₁ ^ 2) :=
      mm_measurable_lintegral (fun s y ω₁ => ENNReal.ofReal (Z s y ω₁ ^ 2))
        ((prop72NoiseZp_measurable hZp).pow_const 2).ennreal_ofReal
    refine lt_of_le_of_lt (mm_lintegral3_mono hle) ?_
    rw [mm_lintegral3_const_mul _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [show (∫⁻ ω : Ω × Ω'', (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ y,
        ENNReal.ofReal (Z s y ω.1 ^ 2)) ∂P) = ∫⁻ ω₁, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ y,
        ENNReal.ofReal (Z s y ω₁ ^ 2)) ∂Pr from measurePreserving_fst.lintegral_comp hG]
    exact hZ2
  -- the Walsh integral `∫∫ κ dξ`
  obtain ⟨Xp, hXp, -⟩ := exists_walshProcess hS hT.le hκp hκ2
  have htrunc : (fun s y ω => if 0 < s ∧ s ≤ T then κ s y ω else 0) = κ := by
    funext s y ω
    by_cases h : u < s ∧ s ≤ v
    · simp [hκ, h, show 0 < s ∧ s ≤ T from ⟨hu.trans_lt h.1, h.2.trans hvT⟩]
    · simp [hκ, h]
  have hX' : IsWalshIntegral 𝒢b S P κ (Xp T) := htrunc ▸ hXp T ⟨hT.le, le_rfl⟩
  obtain ⟨hκL2, hXL2, hiso⟩ := hX'.isometry_lib hS
  -- the covariation of `ξ((a,b])` with `V = M^φ(· ∧ v) - M^φ(· ∧ u)` is `∫_0^t ∫_a^b κ`
  set V : ℝ → Ω × Ω'' → ℝ := fun t ω => Vb (min t T) ω.1 with hV
  have hcov : ∀ n : ℝ, T ≤ n → ∀ a b : ℝ, a ≤ b →
      HasCovariation n 𝒢b (fun t ω => S t b ω - S t a ω) V
        (fun t ω => ∫ r in (0 : ℝ)..t, ∫ y, (if a < y ∧ y ≤ b then κ r y ω else 0)) P := by
    intro n hn a b hab
    refine prop72Noise_cov_congr (hT.le.trans hn) (hcovS hb n hn a b hab)
      (ae_of_all _ fun _ _ _ => rfl) (ae_of_all _ fun _ _ _ => rfl)
      (ae_of_all _ fun ω t ht => ?_)
    simp only [prop72Noise_kappa_id hZ0 hu φ]
    rcases le_total t T with htT | hTt
    · rw [min_eq_left htT]
    · rw [min_eq_right hTt, intervalIntegral.integral_of_le hT.le,
        intervalIntegral.integral_of_le (hT.le.trans hTt)]
      symm
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
        (Set.Ioc_subset_Ioc_right hTt) fun r hr => ?_
      have hr' : v < r := hvT.trans_lt (lt_of_not_ge fun h => hr.2 ⟨hr.1.1, h⟩)
      have hn' : ¬ (u < r ∧ r ≤ v) := fun h => absurd h.2 (not_le.2 hr')
      simp [hκ, hn']
  have hVT : ∀ t, T ≤ t → V t = V T := fun t ht => by
    funext ω; simp only [hV, min_eq_right ht, min_self]
  have hpair := prop72Noise_pairing hS hT.le hκL2 hVT hcov hX'
  -- `𝔼[V_T²] = 𝔼 ∫∫ κ²`
  have hVV := (IsMMIntegral.hasCovariation hq hq0 hq1 hM hb hb).prod_fst (𝒢₂ := 𝓖'') (μ₂ := ν'')
  set τ : ℝ≥0 := ⟨T, hT.le⟩ with hτ
  have hVTeq : V T = fun ω => Vb T ω.1 := by funext ω; simp only [hV, min_self]
  have hVbT : MemLp (fun ω : Ω × Ω'' => Vb T ω.1) 2 P := hVV.left.memLp τ le_rfl
  have hVL2 : MemLp (V T) 2 P := by rw [hVTeq]; exact hVbT
  have hV2 : ∫ ω, V T ω ^ 2 ∂P = ∫ p, uncurryField κ p ^ 2 ∂(P.prod volume) := by
    have hint : Integrable (fun ω : Ω × Ω'' => ∫ r in (0 : ℝ)..T, ∫ x,
        q r x ω.1 * (if u < r ∧ r ≤ v then 1 * φ x else 0) *
          (if u < r ∧ r ≤ v then 1 * φ x else 0)) P := hVV.integrable_cov τ le_rfl
    have hi2 : Integrable (fun ω : Ω × Ω'' => Vb T ω.1 * Vb T ω.1) P :=
      hVbT.integrable_mul hVbT
    have hce := hVV.condExp_mul 0 τ (zero_le : (0 : ℝ≥0) ≤ τ) le_rfl
    have h1 : ∫ ω, (Vb T ω.1 * Vb T ω.1 - (∫ r in (0 : ℝ)..T, ∫ x,
        q r x ω.1 * (if u < r ∧ r ≤ v then 1 * φ x else 0) *
          (if u < r ∧ r ≤ v then 1 * φ x else 0))) ∂P = 0 := by
      have h := integral_congr_ae hce
      rw [integral_condExp (𝒢b.le 0)] at h
      refine h.trans (integral_eq_zero_of_ae (ae_of_all _ fun ω => ?_))
      simp [hVb, min_eq_left hu, min_eq_left hv0]
    rw [integral_sub hi2 hint, sub_eq_zero] at h1
    rw [hVTeq]
    simp only [sq]
    rw [h1]
    have hint' : Integrable (uncurryField fun r y ω => κ r y ω * κ r y ω) (P.prod volume) := by
      have := hκL2.integrable_mul hκL2
      exact this
    refine Eq.trans ?_ (prop72Noise_integral_iter (F := fun r y ω => κ r y ω * κ r y ω)
      hint' hT.le ?_)
    · refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      refine intervalIntegral.integral_congr fun r _ => ?_
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [hqdef, hκ, ← sq]
      exact prop72Noise_kappa_sq Z hu φ r y ω.1
    · intro r y ω hr
      have hn' : ¬ (u < r ∧ r ≤ v) := fun h =>
        hr ⟨hu.trans_lt h.1, h.2.trans hvT⟩
      simp [hκ, hn']
  -- conclusion: `𝔼[(∫∫ κ dξ - V_T)²] = 0`
  have hsq : ∫ ω, (Xp T ω - V T ω) ^ 2 ∂P = 0 := by
    have e : (fun ω => (Xp T ω - V T ω) ^ 2) =
        fun ω => Xp T ω ^ 2 - 2 * (Xp T ω * V T ω) + V T ω ^ 2 := by funext ω; ring
    have i1 : Integrable (fun ω => Xp T ω ^ 2) P := hXL2.integrable_sq
    have i2 : Integrable (fun ω => Xp T ω * V T ω) P := hXL2.integrable_mul hVL2
    have i3 : Integrable (fun ω => V T ω ^ 2) P := hVL2.integrable_sq
    have i12 : Integrable (fun ω => Xp T ω ^ 2 - 2 * (Xp T ω * V T ω)) P :=
      i1.sub (i2.const_mul 2)
    have i22 : Integrable (fun ω => 2 * (Xp T ω * V T ω)) P := i2.const_mul 2
    rw [e, integral_add i12 i3, integral_sub i1 i22,
      integral_const_mul, hiso, hpair, hV2]
    simp only [← sq]
    ring
  have i4 : Integrable (fun ω => (Xp T ω - V T ω) ^ 2) P := (hXL2.sub hVL2).integrable_sq
  rw [integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) i4] at hsq
  refine hX'.congr_ae hS EventuallyEq.rfl ?_
  filter_upwards [hsq] with ω hω
  have h0 : Xp T ω = V T ω := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hω)
  rw [h0]
  simp only [hV, hVb, hMdef, min_self, min_eq_right hvT, min_eq_right (huv.trans hvT), one_mul]

end QSSEPtoKPZ
