/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.Martingales.Defs
public import QSSEPtoKPZ.WaveFunction.MomentEstimate

/-!
# Proposition 2.1, equation (2.2): moments of `‖ψ_t‖_a`

Statement: Stage 2, task T0; proof: task D4. Existence and uniqueness in Proposition 2.1
are the companion statements E1 and U1 (`Companions.lean`), not part of Stage 2.

Proof (`docs/stage2-design.md`, 1.2 (g)). Replace `ψ` by a unit-norm version `ψ'`
(`IsWaveFunction.exists_isUnitWave`), equal to `ψ` at all times almost surely. With the
truncated weights `w_{b,R}(x) = e^{b min(|x|,R)}` and `V_{b,R}(t) = ∑ₓ w_{b,R}(x) P(t,x)`:

* `𝔼 sup_{t ≤ T} V_{b,R}(t) ≤ C(b, T)` uniformly in `R` (`IsUnitWave.lintegral_iSup_momentV_le`,
  file `MomentEstimate.lean`);
* Jensen's inequality for the probability `P(t,·)`: `V_{a,R}^{2^k} ≤ V_{2^k a,R}`
  (`IsUnitWave.momentV_pow_le`);
* `∑ₓ e^{a|x|} P(t,x) ≤ sup_R V_{a,R}(t)` and monotone convergence in `R`;
* `s^k ≤ 1 + s^{2^k}` for `s ∈ [0, ∞]`.

Hence `𝔼 sup_{t ≤ T} ‖ψ_t‖_a^{2k} ≤ 1 + C(2^k a, T) < ∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}

/-- `s^k ≤ 1 + s^n` in `[0, ∞]` for `k ≤ n`. -/
private lemma momentBound_pow_le {s : ℝ≥0∞} {k n : ℕ} (h : k ≤ n) : s ^ k ≤ 1 + s ^ n := by
  rcases le_or_gt s 1 with hs | hs
  · exact (pow_le_one₀ zero_le hs).trans le_self_add
  · exact (pow_le_pow_right₀ hs.le h).trans le_add_self

/-- `∑ₓ e^{a|x|} P(t,x) ≤ sup_R V_{a,R}(t)` (each finite partial sum is a partial sum of
`V_{a,R}` for `R` large). -/
private lemma momentBound_tsum_le_iSup {ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)} {a : ℝ} (ha : 0 ≤ a)
    (ω : Ω) (t : ℝ) :
    ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ' ω t x) ≤
      ⨆ R : ℕ, ENNReal.ofReal (momentV ψ' a R t ω) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  refine le_iSup_of_le (F.sup Int.natAbs) ?_
  rw [momentV, ENNReal.ofReal_tsum_of_nonneg
    (fun x => mul_nonneg (momentWeight_pos a _ x).le (IsUnitWave.density_nonneg ψ' ω t x))
    (summable_momentV ha ψ' _ t ω)]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x hx => ?_)) (ENNReal.sum_le_tsum F)
  rw [momentWeight_eq_of_le a (Finset.le_sup (f := Int.natAbs) hx)]

omit [IsProbabilityMeasure μ] in
/-- `sup_{t ∈ [0,T]} V_{b,R}(t)` is measurable. -/
private lemma momentBound_measurable {ψ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hu : IsUnitWave 𝓕 B ψ ψ' μ) {b : ℝ} (hb : 0 ≤ b) (T : ℝ) (R : ℕ) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (momentV ψ' b R t ω) := by
  have e : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (momentV ψ' b R t ω)) =
      fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ∑' x,
        ENNReal.ofReal (momentWeight b R x * density ψ' ω t x) := by
    funext ω
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    rw [momentV, ENNReal.ofReal_tsum_of_nonneg
      (fun x => mul_nonneg (momentWeight_pos b R x).le (IsUnitWave.density_nonneg ψ' ω t x))
      (summable_momentV hb ψ' R t ω)]
  rw [e]
  refine measurable_iSup_Icc_tsum (fun x ω => ?_) (fun x t ht => ?_)
  · exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      ((hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self))
  · exact (((hu.weight_measurable_density ⟨t, ht.1⟩ x).mono ((nullAug μ 𝓕).le _) le_rfl).const_mul
      _).ennreal_ofReal

/-- **Proposition 2.1, equation (2.2)**: for all `a ≥ 0`, `T` and `k`,
`𝔼[sup_{t ∈ [0,T]} ‖ψ_t‖_a^{2k}] < ∞`, where `‖ψ‖_a² = ∑_{x ∈ ℤ} e^{a|x|} |ψ(x)|²`. The norm is
computed in `[0, ∞]` (no convergence issue), and the supremum is stated to be almost everywhere
measurable, so that the expectation is a genuine one. -/
theorem moment_bound (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {a T : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)) μ ∧
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)) ^ k ∂μ < ⊤ := by
  classical
  rcases lt_or_ge T 0 with hT | hT
  · have h0 : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)) = 0 :=
      fun ω => by simp [Set.Icc_eq_empty (not_le.2 hT)]
    simp only [h0]
    refine ⟨aemeasurable_const, ?_⟩
    calc ∫⁻ _, (0 : ℝ≥0∞) ^ k ∂μ ≤ ∫⁻ _, 1 ∂μ :=
          lintegral_mono fun _ => pow_le_one₀ zero_le zero_le_one
      _ < ⊤ := by simp
  obtain ⟨ψ', hu⟩ := hψ.exists_isUnitWave hB
  set G' : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ' ω t x) with hG'
  have hGG : ∀ᵐ ω ∂μ, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)) = G' ω := by
    filter_upwards [hu.ae_eq] with ω hω
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    have h := hω ⟨t, ht.1⟩
    simp only [density]
    rw [show ψ t ω = ψ' t ω from h.symm]
  -- measurability
  have hG'm : Measurable G' := by
    refine measurable_iSup_Icc_tsum (fun x ω => ?_) (fun x t ht => ?_)
    · exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
        ((hu.weight_continuousOn_density ω x).mono Set.Icc_subset_Ici_self))
    · exact (((hu.weight_measurable_density ⟨t, ht.1⟩ x).mono ((nullAug μ 𝓕).le _)
        le_rfl).const_mul _).ennreal_ofReal
  refine ⟨hG'm.aemeasurable.congr (hGG.mono fun ω h => h.symm), ?_⟩
  rw [lintegral_congr_ae (hGG.mono fun ω h => by rw [h])]
  -- reduction to the truncated first moments of weight `b = 2^k a`
  have hb : 0 ≤ (2 : ℝ) ^ k * a := by positivity
  set H : ℕ → Ω → ℝ≥0∞ := fun R ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal (momentV ψ' (2 ^ k * a) R t ω) with hH
  have hpt : ∀ ω, G' ω ^ k ≤ 1 + ⨆ R, H R ω := by
    intro ω
    refine (momentBound_pow_le (Nat.lt_two_pow_self).le).trans (add_le_add le_rfl ?_)
    rw [hG', ENNReal.iSup_pow_of_ne_zero (by positivity)]
    refine iSup_le fun t => ?_
    rw [ENNReal.iSup_pow_of_ne_zero (by positivity)]
    refine iSup_le fun ht => ?_
    refine (pow_le_pow_left₀ zero_le (momentBound_tsum_le_iSup ha ω t) _).trans ?_
    rw [ENNReal.iSup_pow_of_ne_zero (by positivity)]
    refine iSup_le fun R => le_iSup_of_le R ?_
    rw [← ENNReal.ofReal_pow (momentV_nonneg _ _ _ _ _)]
    exact le_iSup₂_of_le (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (momentV ψ' (2 ^ k * a) R t ω)) t ht
      (ENNReal.ofReal_le_ofReal (hu.momentV_pow_le ω ht.1 ha R k))
  have hHm : ∀ R, AEMeasurable (H R) μ := fun R => (momentBound_measurable hu hb T R).aemeasurable
  have hHmono : ∀ᵐ ω ∂μ, Monotone fun R => H R ω := ae_of_all _ fun ω R R' hRR' =>
    iSup₂_le fun t ht => le_iSup₂_of_le (f := fun (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (momentV ψ' (2 ^ k * a) R' t ω)) t ht (ENNReal.ofReal_le_ofReal
        ((summable_momentV hb ψ' R t ω).tsum_le_tsum (fun x => mul_le_mul_of_nonneg_right
          (momentWeight_mono hb hRR' x) (IsUnitWave.density_nonneg ψ' ω t x))
          (summable_momentV hb ψ' R' t ω)))
  calc ∫⁻ ω, G' ω ^ k ∂μ ≤ ∫⁻ ω, (1 + ⨆ R, H R ω) ∂μ := lintegral_mono hpt
    _ = 1 + ⨆ R, ∫⁻ ω, H R ω ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_iSup' hHm hHmono]
        simp
    _ ≤ 1 + momentConst (2 ^ k * a) T := by
        gcongr
        exact iSup_le fun R => hu.lintegral_iSup_momentV_le hB hb hT R
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
        (momentConst_ne_top _ _).lt_top⟩

end QSSEPtoKPZ
