/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.WaveFunction.QuadBox
public import QSSEPtoKPZ.WaveFunction.QuadRow
public import QSSEPtoKPZ.WaveFunction.MomentBound

/-!
# Pathwise limits for quadratic functionals of `P` (task D6)

Let `N_T(ω) = sup_{t ∈ [0,T]} ∑ₓ e^{(2a+1)|x|} P(t,x)` (`quadSup`). By (2.2) with `k = 3`,
`𝔼 N_T³ < ∞` (`IsUnitWave.quadSup_moment`), so `N_T < ∞` almost surely, and on this event
`P(t,·)` satisfies `QuadDecay a N_T` for all `t ∈ [0,T]` (`quadDecay_of_quadSup`): this is the
article's `e^{a|x|} P(t,x) ≤ e^{-|x|} N_{a+1}`, uniformly in `t`.

On such a path, with `|f_t|, |∂ₜf_t| ≤ C W W` on `[0,T]`:
* the box sums over `[-K,K]²` converge (`quad_tendsto_box_sum`);
* the box drifts are continuous, bounded uniformly in `K` and `t`, and converge to
  `∑_{x₁,x₂} (∂ₜf + 𝒬f) P P` (`quad_path_drift`), hence the integrated drifts converge and the
  limit drift is integrable (`quad_path_integral_drift`);
* the rows `∑_{x'} (f(x+1,x') - f(x,x')) P(x')` and the bracket density are continuous in time
  (`quad_path_continuousOn_bracket`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- The series `D_s(x) = ∑_{x'} (f_s(x+1,x') - f_s(x,x')) P(s,x')` of the last term of (2.8)
(the same as `quadDiff` of `Quadratic.lean`, which imports this file). -/
def quadD (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (f : ℝ → ℤ → ℤ → ℝ) (s : ℝ) (ω : Ω) (x : ℤ) : ℝ :=
  ∑' x' : ℤ, (f s (x + 1) x' - f s x x') * density ψ ω s x'

/-- `N_T(ω) = sup_{t ∈ [0,T]} ∑ₓ e^{(2a+1)|x|} P(t,x)`, in `[0, ∞]`. -/
def quadSup (ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)) (a T : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
    ENNReal.ofReal (Real.exp ((2 * a + 1) * |(x : ℝ)|) * density ψ' ω t x)

/-- On `{N_T < ∞}`, `P(t,·)` decays exponentially, uniformly in `t ∈ [0,T]`. -/
lemma quadDecay_of_quadSup {a T : ℝ} {ω : Ω} (hω : quadSup ψ' a T ω ≠ ⊤) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : QuadDecay a (quadSup ψ' a T ω).toReal (density ψ' ω t) where
  nonneg x := IsUnitWave.density_nonneg ψ' ω t x
  le x := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hω]
    refine le_trans ?_ (le_iSup₂ (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) T) => ∑' x : ℤ,
      ENNReal.ofReal (Real.exp ((2 * a + 1) * |(x : ℝ)|) * density ψ' ω t x)) t ht)
    exact ENNReal.le_tsum (f := fun x : ℤ =>
      ENNReal.ofReal (Real.exp ((2 * a + 1) * |(x : ℝ)|) * density ψ' ω t x)) x

/-- **(2.2) with `k = 3`**: `N_T` is measurable and `𝔼 N_T³ < ∞`. -/
theorem IsUnitWave.quadSup_moment [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (hu : IsUnitWave 𝓕 B ψ ψ' μ) {a : ℝ} (ha : 0 ≤ a)
    (T : ℝ) : Measurable (quadSup ψ' a T) ∧ ∫⁻ ω, quadSup ψ' a T ω ^ 3 ∂μ < ⊤ := by
  have hm : Measurable (quadSup ψ' a T) := by
    refine measurable_iSup_Icc_tsum (fun x ω => ?_) (fun x t ht => ?_)
    · exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
        ((hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self))
    · exact (((hu.weight_measurable_density ⟨t, ht.1⟩ x).mono ((nullAug μ 𝓕).le _)
        le_rfl).const_mul _).ennreal_ofReal
  refine ⟨hm, ?_⟩
  have h := (moment_bound hB hψ (a := 2 * a + 1) (T := T) (by positivity) 3).2
  have hGG : ∀ᵐ ω ∂μ, (⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x : ℤ,
      ENNReal.ofReal (Real.exp ((2 * a + 1) * |(x : ℝ)|) * density ψ ω t x)) =
        quadSup ψ' a T ω := by
    filter_upwards [hu.ae_eq] with ω hω
    unfold quadSup
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    have h := hω ⟨t, ht.1⟩
    simp only [density]
    rw [show ψ t ω = ψ' t ω from h.symm]
  rwa [lintegral_congr_ae (hGG.mono fun ω h => by rw [h])] at h

/-- `N_T < ∞` almost surely. -/
lemma IsUnitWave.ae_quadSup_ne_top [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ) (hu : IsUnitWave 𝓕 B ψ ψ' μ) {a : ℝ} (ha : 0 ≤ a)
    (T : ℝ) : ∀ᵐ ω ∂μ, quadSup ψ' a T ω ≠ ⊤ := by
  obtain ⟨hm, hi⟩ := hu.quadSup_moment hB hψ ha T
  filter_upwards [ae_lt_top (hm.pow_const 3) hi.ne] with ω hω
  intro h
  rw [h, ENNReal.top_pow (by norm_num)] at hω
  exact lt_irrefl _ hω

/-! ### Boxes -/

/-- The box `[-K, K]²`. -/
def quadBox (K : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K

lemma quad_tendsto_box : Tendsto quadBox atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun K L hKL => ?_) fun p => ?_
  · have h : Finset.Icc (-(K : ℤ)) K ⊆ Finset.Icc (-(L : ℤ)) L := by
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      have : (K : ℤ) ≤ L := by exact_mod_cast hKL
      omega
    exact Finset.product_subset_product h h
  · refine ⟨p.1.natAbs + p.2.natAbs, ?_⟩
    simp only [quadBox, Finset.mem_product, Finset.mem_Icc]
    omega

/-- Box sums of a summable family on `ℤ²` converge to its sum. -/
lemma quad_tendsto_box_sum {g : ℤ × ℤ → ℝ} (hg : Summable g) :
    Tendsto (fun K : ℕ => ∑ p ∈ quadBox K, g p) atTop (𝓝 (∑' p, g p)) :=
  hg.hasSum.comp quad_tendsto_box

/-! ### Pathwise facts -/

/-- Continuity in time of the drift of a pair. -/
lemma IsUnitWave.continuousOn_quadDriftTerm (hu : IsUnitWave 𝓕 B ψ ψ' μ) {N : ℝ}
    {f f' : ℝ → ℤ → ℤ → ℝ} (hc : ∀ x₁ x₂, ContinuousOn (f · x₁ x₂) (Set.Icc 0 N))
    (hc' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 N)) (ω : Ω) (x₁ x₂ : ℤ) :
    ContinuousOn (fun s => quadDriftTerm (f s) (f' s) (density ψ' ω s) x₁ x₂)
      (Set.Icc 0 N) := by
  have hP : ∀ x, ContinuousOn (fun s => density ψ' ω s x) (Set.Icc 0 N) := fun x =>
    (hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self
  have hL : ∀ x, ContinuousOn (fun s => lap (density ψ' ω s) x) (Set.Icc 0 N) := fun x =>
    (hu.weight_continuousOn_lap_density ω x).mono Set.Icc_subset_Ici_self
  have hX : ContinuousOn (fun s => quadCross (density ψ' ω s) x₁ x₂) (Set.Icc 0 N) := by
    unfold quadCross
    split_ifs <;> first
      | exact continuousOn_const
      | fun_prop (disch := assumption)
  unfold quadDriftTerm
  exact (((hc' x₁ x₂).mul (hP x₁)).mul (hP x₂)).add ((hc x₁ x₂).mul
    ((((hP x₁).mul (hL x₂)).add ((hP x₂).mul (hL x₁))).add hX))

/-- The uniform bound `9 C (3 e^a R)² ∑_{x₁,x₂} ρ₃(x₁) ρ₃(x₂)` of the box drifts. -/
def quadDriftBound (a C R : ℝ) : ℝ :=
  9 * C * (3 * Real.exp a * R) ^ 2 * ∑' p : ℤ × ℤ, quadRho3 p.1 * quadRho3 p.2

lemma summable_quadRho3_prod : Summable fun p : ℤ × ℤ => quadRho3 p.1 * quadRho3 p.2 :=
  summable_quadRho3.mul_of_nonneg summable_quadRho3 (fun x => quadRho3_nonneg x)
    (fun x => quadRho3_nonneg x)

/-- **Drifts on a good path, at a fixed time.** The box drifts converge to
`∑_{x₁,x₂} (∂ₜf + 𝒬f) P P` and are bounded by `quadDriftBound`. -/
lemma quad_path_drift {a C R : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) {f f' : ℤ → ℤ → ℝ} {P : ℤ → ℝ}
    (hD : QuadDecay a R P) (hfb : ∀ x₁ x₂, |f x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    (hfb' : ∀ x₁ x₂, |f' x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂) :
    Tendsto (fun K : ℕ => ∑ p ∈ quadBox K, quadDriftTerm f f' P p.1 p.2) atTop
      (𝓝 (∑' x₁, ∑' x₂, (f' x₁ x₂ + inclGen f x₁ x₂) * P x₁ * P x₂)) ∧
    ∀ K, |∑ p ∈ quadBox K, quadDriftTerm f f' P p.1 p.2| ≤ quadDriftBound a C R := by
  refine ⟨(hD.hasSum_quadDriftTerm ha hC hfb hfb').comp quad_tendsto_box, fun K => ?_⟩
  have hg : ∀ p : ℤ × ℤ, |quadDriftTerm f f' P p.1 p.2| ≤
      9 * C * (3 * Real.exp a * R) ^ 2 * (quadRho3 p.1 * quadRho3 p.2) := fun p => by
    have h1 := hD.abs_quadDriftTerm_le hfb hfb' p.1 p.2
    have hF : 0 ≤ 9 * C * quadW a p.1 * quadW a p.2 :=
      mul_nonneg (mul_nonneg (by positivity) (quadW_pos a _).le) (quadW_pos a _).le
    have h2 := hD.pair_le ha (F := 9 * C * quadW a p.1 * quadW a p.2) (K := 9 * C) p.1 p.2
      (by rw [abs_of_nonneg hF])
    rw [abs_of_nonneg hF] at h2
    exact h1.trans h2
  have hs := summable_quadRho3_prod.mul_left (9 * C * (3 * Real.exp a * R) ^ 2)
  calc |∑ p ∈ quadBox K, quadDriftTerm f f' P p.1 p.2|
      ≤ ∑ p ∈ quadBox K, |quadDriftTerm f f' P p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ quadBox K, 9 * C * (3 * Real.exp a * R) ^ 2 * (quadRho3 p.1 * quadRho3 p.2) :=
        Finset.sum_le_sum fun p _ => hg p
    _ ≤ ∑' p : ℤ × ℤ, 9 * C * (3 * Real.exp a * R) ^ 2 * (quadRho3 p.1 * quadRho3 p.2) :=
        hs.sum_le_tsum _ fun p _ => mul_nonneg (by positivity)
          (mul_nonneg (quadRho3_nonneg _) (quadRho3_nonneg _))
    _ = quadDriftBound a C R := by rw [tsum_mul_left, quadDriftBound]

/-- **Integrated drifts on a good path.** If on `[0,N]` the box drifts are continuous, converge
to `c` and are bounded by a constant, then `c` is integrable on `[0,N]` and
`∫_0^t (box drift) → ∫_0^t c` for `t ∈ [0,N]`. -/
lemma quad_path_integral_drift {N M : ℝ} (hN : 0 ≤ N) {A : ℕ → ℝ → ℝ} {c : ℝ → ℝ}
    (hcont : ∀ K, ContinuousOn (A K) (Set.Icc 0 N))
    (hlim : ∀ s ∈ Set.Icc 0 N, Tendsto (fun K => A K s) atTop (𝓝 (c s)))
    (hb : ∀ s ∈ Set.Icc 0 N, ∀ K, |A K s| ≤ M) :
    IntervalIntegrable c MeasureTheory.volume 0 N ∧ ∀ t : ℝ, 0 ≤ t → t ≤ N →
      Tendsto (fun K => ∫ s in (0 : ℝ)..t, A K s) atTop (𝓝 (∫ s in (0 : ℝ)..t, c s)) := by
  have hsubI : ∀ {t : ℝ}, 0 ≤ t → t ≤ N → Set.uIoc 0 t ⊆ Set.Icc 0 N := fun ht0 htN s hs => by
    rw [Set.uIoc_of_le ht0] at hs; exact ⟨hs.1.le, hs.2.trans htN⟩
  refine ⟨?_, fun t ht0 htN => ?_⟩
  · have hsub := hsubI hN le_rfl
    have hvol : MeasureTheory.volume (Set.uIoc (0 : ℝ) N) < ∞ := by
      rw [Set.uIoc_of_le hN, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound hvol ?_ M ?_
    · exact aestronglyMeasurable_of_tendsto_ae atTop
        (fun K => ((hcont K).mono hsub).aestronglyMeasurable measurableSet_uIoc)
        ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => hlim s (hsub hs)))
    · refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun s hs => ?_)
      exact le_of_tendsto ((continuous_norm.tendsto _).comp (hlim s (hsub hs)))
        (Eventually.of_forall fun K => by
          rw [Function.comp_apply, Real.norm_eq_abs]; exact hb s (hsub hs) K)
  · exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun K =>
        ((hcont K).mono (hsubI ht0 htN)).aestronglyMeasurable measurableSet_uIoc)
      (Eventually.of_forall fun K => ae_of_all _ fun s hs => by
        rw [Real.norm_eq_abs]; exact hb s (hsubI ht0 htN hs) K)
      intervalIntegrable_const
      (ae_of_all _ fun s hs => hlim s (hsubI ht0 htN hs))

/-- **Continuity of the bracket density on a good path.** If `P(s,·)` satisfies
`QuadDecay a R` and `|f_s| ≤ C W W` for `s ∈ [0,N]`, and `f` is continuous in time, then
`s ↦ ∑ₓ 2 (2 D_s(x))² P(s,x) P(s,x+1)` is continuous on `[0,N]`. -/
lemma IsUnitWave.quad_path_continuousOn_bracket (hu : IsUnitWave 𝓕 B ψ ψ' μ) {a C R N : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) {f : ℝ → ℤ → ℤ → ℝ} {ω : Ω}
    (hD : ∀ s ∈ Set.Icc 0 N, QuadDecay a R (density ψ' ω s))
    (hfb : ∀ s ∈ Set.Icc 0 N, ∀ x₁ x₂, |f s x₁ x₂| ≤ C * quadW a x₁ * quadW a x₂)
    (hc : ∀ x₁ x₂, ContinuousOn (f · x₁ x₂) (Set.Icc 0 N)) :
    ContinuousOn (fun s => ∑' x : ℤ,
      2 * (2 * quadD ψ' f s ω x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1))
      (Set.Icc 0 N) := by
  have hP : ∀ x, ContinuousOn (fun s => density ψ' ω s x) (Set.Icc 0 N) := fun x =>
    (hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self
  -- continuity of the rows
  have hDc : ∀ x, ContinuousOn (fun s => quadD ψ' f s ω x) (Set.Icc 0 N) := fun x => by
    refine continuousOn_tsum (u := fun x' => C * R * (quadW a (x + 1) + quadW a x) *
      quadRho x') (fun x' => ((hc _ _).sub (hc _ _)).mul (hP x'))
      (summable_quadRho.mul_left _) fun x' s hs => ?_
    rw [Real.norm_eq_abs, sub_mul]
    have h1 := (hD s hs).abs_row_term_le ha hC (hfb s hs) (x + 1) x'
    have h2 := (hD s hs).abs_row_term_le ha hC (hfb s hs) x x'
    calc _ ≤ |f s (x + 1) x' * density ψ' ω s x'| + |f s x x' * density ψ' ω s x'| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * Real.exp a * C * R * quadSigma := ⟨_, rfl⟩
  have hterm : ∀ x : ℤ, ContinuousOn (fun s => 2 * (2 * quadD ψ' f s ω x) ^ 2 *
      density ψ' ω s x * density ψ' ω s (x + 1)) (Set.Icc 0 N) := fun x =>
    ((continuousOn_const.mul ((continuousOn_const.mul (hDc x)).pow 2)).mul (hP x)).mul
      (hP (x + 1))
  refine continuousOn_tsum (f := fun (x : ℤ) (s : ℝ) => 2 * (2 * quadD ψ' f s ω x) ^ 2 *
      density ψ' ω s x * density ψ' ω s (x + 1))
    (u := fun x => 8 * (L ^ 2 * R * quadRho x) * R) hterm
    ((summable_quadRho.mul_left (8 * (L ^ 2 * R))).mul_right R |>.congr fun x => by ring)
    fun x s hs => ?_
  have hb : ∀ y, |quadD ψ' f s ω y| ≤ L * quadW a y := fun y =>
    ((hD s hs).abs_row_sub_le ha hC (hfb s hs) y).trans (le_of_eq (by rw [hL]))
  have h1 := (hD s hs).sq_mul_le hb x
  have h2 := (hD s hs).le_R ha (x + 1)
  have p0 := (hD s hs).nonneg x; have p1 := (hD s hs).nonneg (x + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : 0 ≤ quadD ψ' f s ω x ^ 2 * density ψ' ω s x := by positivity
  have : 0 ≤ 8 * (L ^ 2 * R * quadRho x) := by linarith
  calc 2 * (2 * quadD ψ' f s ω x) ^ 2 * density ψ' ω s x * density ψ' ω s (x + 1)
      = 8 * (quadD ψ' f s ω x ^ 2 * density ψ' ω s x) * density ψ' ω s (x + 1) := by ring
    _ ≤ 8 * (L ^ 2 * R * quadRho x) * R := by gcongr

end QSSEPtoKPZ
