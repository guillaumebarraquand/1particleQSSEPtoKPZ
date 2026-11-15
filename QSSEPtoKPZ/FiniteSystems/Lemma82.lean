/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Lemma82Aux
public import QSSEPtoKPZ.FiniteSystems.Picard
public import QSSEPtoKPZ.FiniteSystems.RandomWalkTail

/-!
# Lemma 8.2 (task L6)

Task L6 (statement from task I0‴ of Stage 5, `docs/stage5-interfaces.md`).
`docs/stage5-design.md`, Section 1.2 (d), decision D1‴.

`lemma82_bound` has the statement of `lemma_8_2` (`FiniteSystems/Statements.lean`), which quotes
it. Route: replace `ψ`, `ψ^L` by unit-norm Itô versions (`IsWaveFunction.exists_unitIto`); the
columns `u^y = U_· e_y`, `y ∈ Λ_L`, are Itô solutions on `Λ_L` started from `e_y`
(`exists_isWaveIto` with `ψ₀ = lp.single 2 y 1`, then `IsWaveIto.exists_unitVersion`); by
`IsWaveIto.inner_eq`, `⟨u^y_t, ψ^L_t⟩ = δ_{y0}`; by `IsWaveIto.inner_restrict_eq`,
`⟨u^y_t, φ_t⟩_{Λ_L} = δ_{y0} + V_t(y) + N_t(y)` (`φ = ψ|_{Λ_L}`); by `IsWaveIto.frame_orthonormal`
and `frame_parseval`, `‖φ_t - ψ^L_t‖ = ‖V_t + N_t‖`; Doob for each `N(y)`
(`lintegral_tsum_iSup_stochInt_sq_le`; the rows of `U_t` are unit vectors), Cauchy–Schwarz for
`V`, `𝔼 P(u,x) = p_u(x)` (`prop_2_2`), `∑_{Λ_L} |P - P^L| ≤ 2 ‖φ - ψ^L‖`. The deterministic steps
are in `FiniteSystems/Lemma82Aux.lean` (`lemma82_pointwise`).

The finite-variation part is bounded as in the article,
`∑_y |V_t(y)|² ≤ (t/2) ∫_0^t (P(s,L) + P(s,-L)) ds`, and the martingale part by Doob,
`𝔼 ∑_y sup_{t ≤ S} |N_t(y)|² ≤ 4 ∫_0^S 𝔼 (P(s,L+1) + P(s,-L-1)) ds`; with
`(a+b)² ≤ 2a² + 2b²` and `∑_{Λ_L}|P - P^L| ≤ 2 ‖φ - ψ^L‖` this gives the constant `4(8+S)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate InnerProductSpace

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-- Twin of `lemma_8_2` (**Lemma 8.2**, (8.1); same statement). -/
theorem lemma82_bound [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {L : ℕ} (hL : 1 ≤ L) (hψL : IsWaveFunction L 𝓕 B ψL μ) {S : ℝ} (hS : 0 < S) :
    (∀ s : ℝ, 0 ≤ s → Summable fun x : ℤ => if (L : ℤ) ≤ |x| then rwKernel s x else 0) ∧
    IntervalIntegrable (fun s => rwTail s L) volume 0 S ∧
    AEMeasurable (fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x|) ^ 2)) μ ∧
    ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x|) ^ 2)) ∂μ ≤
      ENNReal.ofReal (4 * (8 + S) * ∫ s in (0 : ℝ)..S, rwTail s L) := by
  classical
  refine ⟨fun s hs => summable_rwTail hB hψ hs L, intervalIntegrable_rwTail hB hψ L hS.le, ?_⟩
  set 𝓖 := QSSEPtoKPZ.nullAug μ 𝓕 with h𝓖
  have hB' : IsBrownianFamily 𝓖 B μ := hB.nullAug
  set Sb := Finset.Icc (-(L : ℤ)) L with hSb
  -- unit-norm Itô versions of `ψ` and `ψ^L`
  obtain ⟨ψ', hψ'I, hψ'n, hψ'e⟩ := hψ.exists_unitIto hB
  obtain ⟨ψL', hψLI, hψLn, hψLe⟩ := hψL.exists_unitIto hB
  -- the columns `u^y = U_· e_y`, `y ∈ Λ_L`
  have hsingle : ∀ y ∈ Sb, ∀ x, x ∉ box (L : ℕ∞) → (lp.single 2 y (1 : ℂ) : ℤ → ℂ) x = 0 := by
    intro y hy x hx
    have : x ≠ y := fun h => hx (h ▸ pairing_mem_box_iff.2 hy)
    simp [lp.single_apply, this]
  have hcol : ∀ y : ℤ, ∃ u : ℝ → Ω → ℓ²(ℤ, ℂ), y ∈ Sb →
      IsWaveIto L 𝓖 B (lp.single 2 y 1) u μ ∧ ∀ ω (t : ℝ≥0), ‖u t ω‖ = 1 := by
    intro y
    by_cases hy : y ∈ Sb
    · obtain ⟨u0, hu0, -⟩ := exists_isWaveIto hB (L : ℕ∞) _ (hsingle y hy)
      obtain ⟨u, hu, hun, -⟩ := hu0.exists_unitVersion hB
        (by rw [lp.norm_single (by norm_num), norm_one])
      exact ⟨u, fun _ => ⟨hu, hun⟩⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hy⟩
  choose u hu using hcol
  -- the Duhamel formula (8.2) for each column, and the integrands of its martingale part
  have hR : ∀ y (hy : y ∈ Sb), _ := fun y hy => (hu y hy).1.inner_restrict_eq hB' hL hψ'I
    (fun ω t => ⟨((hu y hy).2 ω t).le, (hψ'n ω t).le⟩)
  set hk : ℤ × Bool → ℤ × Fin 2 → ℝ → Ω → ℝ := fun k i s ω =>
    if k.1 ∈ Sb then (if k.2 then (pairingBoundaryCoef L (u k.1) ψ' i s ω).re
      else (pairingBoundaryCoef L (u k.1) ψ' i s ω).im) else 0 with hkdef
  have hk_t : ∀ y ∈ Sb, hk (y, true) = fun i s ω => (pairingBoundaryCoef L (u y) ψ' i s ω).re :=
    fun y hy => by funext i s ω; simp [hk, hy]
  have hk_f : ∀ y ∈ Sb, hk (y, false) = fun i s ω => (pairingBoundaryCoef L (u y) ψ' i s ω).im :=
    fun y hy => by funext i s ω; simp [hk, hy]
  have hk_0 : ∀ y ∉ Sb, ∀ b, hk (y, b) = 0 := fun y hy b => by funext i s ω; simp [hk, hy]
  have hkI : ∀ k, IsItoIntegrable 𝓖 μ (hk k) := by
    rintro ⟨y, b⟩
    by_cases hy : y ∈ Sb
    · cases b
      · rw [hk_f y hy]; exact (hR y hy).2.1
      · rw [hk_t y hy]; exact (hR y hy).1
    · rw [hk_0 y hy b]; exact isItoIntegrable_zero
  have hid : ∀ y, ∀ᵐ ω ∂μ, y ∈ Sb → ∀ t : ℝ≥0,
      ⟪u y t ω, ψ' t ω⟫_ℂ - ⟪u y t ω, ψL' t ω⟫_ℂ =
        -(1 / 2 : ℂ) * (∫ s in (0 : ℝ)..t,
          (conj (u y s ω L) * ψ' s ω L + conj (u y s ω (-L)) * ψ' s ω (-L)))
        + ((stochInt 𝓖 μ B (hk (y, true)) t ω : ℂ) +
          Complex.I * (stochInt 𝓖 μ B (hk (y, false)) t ω : ℂ)) := by
    intro y
    by_cases hy : y ∈ Sb
    · filter_upwards [(hR y hy).2.2, (hu y hy).1.inner_eq hB' hψLI] with ω h1 h2 _ t
      rw [hk_t y hy, hk_f y hy, h2 t,
        pairing_inner_eq_sum (u y t ω) (ψ' t ω) ((hu y hy).1.support ω t), h1 t,
        ← pairing_inner_eq_sum (lp.single 2 y 1) waveInit (hsingle y hy)]
      ring
    · exact ae_of_all _ fun ω h => absurd h hy
  have hon := IsWaveIto.frame_orthonormal hB' (u := u) (fun y hy => (hu y hy).1)
  -- measurability and continuity of the coordinates
  have hψ'm : ∀ (t : ℝ≥0) (x : ℤ), Measurable fun ω => ψ' t ω x := fun t x =>
    (hψ'I.adapted t x).mono (𝓖.le t) le_rfl
  have hψLm : ∀ (t : ℝ≥0) (x : ℤ), Measurable fun ω => ψL' t ω x := fun t x =>
    (hψLI.adapted t x).mono (𝓖.le t) le_rfl
  -- the two parts of the bound
  set G : Ω → ℝ≥0∞ := fun ω => 2 * ENNReal.ofReal S *
    ∫⁻ s in Set.Ioc 0 S, ENNReal.ofReal (2 * (‖ψ' s ω L‖ ^ 2 + ‖ψ' s ω (-L)‖ ^ 2)) with hGdef
  set X : Ω → ℝ≥0∞ := fun ω => ∑' k : ℤ × Bool,
    ⨆ t ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal (stochInt 𝓖 μ B (hk k) t ω ^ 2) with hXdef
  have hGm : Measurable G :=
    (lemma82_measurable_lintegral hψ'm hψ'I.continuous 2 L (-L) S).const_mul _
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂μ, (⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
      ((∑ x ∈ Sb, |density ψ ω s x - density ψL ω s x|) ^ 2)) ≤ G ω + 8 * X ω := by
    filter_upwards [hψ'e, hψLe, hon, ae_all_iff.2 hid] with ω he1 he2 hon' hid'
    refine iSup₂_le fun t ht => ?_
    set τ : ℝ≥0 := ⟨t, ht.1⟩ with hτ
    have e1 : ψ t ω = ψ' t ω := (he1 τ).symm
    have e2 : ψL t ω = ψL' t ω := (he2 τ).symm
    have hcont : ∀ y ∈ Sb, ContinuousOn
        (fun s => conj (u y s ω L) * ψ' s ω L + conj (u y s ω (-L)) * ψ' s ω (-L))
        (Set.Icc 0 t) := by
      intro y hy
      have hc := fun x => lemma82_continuousOn_apply (φ := fun s => u y s ω) ((hu y hy).1.continuous ω) x
      have hc' := fun x => lemma82_continuousOn_apply (φ := fun s => ψ' s ω) (hψ'I.continuous ω) x
      exact (((Complex.continuous_conj.comp_continuousOn (hc L)).mul (hc' L)).add
        ((Complex.continuous_conj.comp_continuousOn (hc (-L))).mul (hc' (-L)))).mono
        Set.Icc_subset_Ici_self
    have hP := lemma82_pointwise ht.1 ht.2 (fun y s => u y s ω) (fun s => ψ' s ω) (ψL' τ ω)
      (fun y => stochInt 𝓖 μ B (hk (y, true)) t ω) (fun y => stochInt 𝓖 μ B (hk (y, false)) t ω)
      (fun s hs y hy x hx => (hu y hy).1.support ω ⟨s, hs⟩ x hx)
      (fun s hs y hy z hz => hon' ⟨s, hs⟩ y hy z hz) (hψ'n ω τ).le (hψLn ω τ).le hcont
      (fun y hy => hid' y hy τ)
    have hX : ∑ y ∈ Sb, (ENNReal.ofReal (stochInt 𝓖 μ B (hk (y, true)) t ω ^ 2) +
        ENNReal.ofReal (stochInt 𝓖 μ B (hk (y, false)) t ω ^ 2)) ≤ X ω := by
      calc ∑ y ∈ Sb, (ENNReal.ofReal (stochInt 𝓖 μ B (hk (y, true)) t ω ^ 2) +
          ENNReal.ofReal (stochInt 𝓖 μ B (hk (y, false)) t ω ^ 2))
          = ∑ k ∈ Sb ×ˢ (Finset.univ : Finset Bool),
              ENNReal.ofReal (stochInt 𝓖 μ B (hk k) t ω ^ 2) := by
            rw [Finset.sum_product]
            simp
        _ ≤ ∑ k ∈ Sb ×ˢ (Finset.univ : Finset Bool),
              ⨆ t ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal (stochInt 𝓖 μ B (hk k) t ω ^ 2) :=
            Finset.sum_le_sum fun k _ => le_iSup₂
              (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) S) =>
                ENNReal.ofReal (stochInt 𝓖 μ B (hk k) t ω ^ 2)) t ht
        _ ≤ X ω := ENNReal.sum_le_tsum _
    simp only [density, e1, e2]
    exact hP.trans (add_le_add le_rfl (mul_le_mul' le_rfl hX))
  -- expectation of the finite-variation part
  set J := ∫ s in (0 : ℝ)..S, rwTail s L with hJdef
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hS.le fun s hs =>
    rwTail_nonneg hB hψ hs.1 L
  have hL1 : (L : ℤ) ≠ -(L : ℤ) := by omega
  have hEG : ∫⁻ ω, G ω ∂μ ≤ 2 * ENNReal.ofReal S * ENNReal.ofReal (2 * J) := by
    rw [hGdef, lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
    exact mul_le_mul' le_rfl (lemma82_lintegral_density_le hB hψ hψ'm hψ'I.continuous hψ'e
      (by norm_num) hL1 (by simp) (by simp) hS.le)
  -- expectation of the martingale part (Doob)
  have hEX : ∫⁻ ω, X ω ∂μ ≤ 4 * ENNReal.ofReal (1 * J) := by
    refine (lintegral_tsum_iSup_stochInt_sq_le hB' hkI S).trans (mul_le_mul' le_rfl ?_)
    have hL2 : (L : ℤ) + 1 ≠ -(L : ℤ) - 1 := by omega
    have hpe : ∀ᵐ ω ∂μ, ∀ s ∈ Set.Ioc (0 : ℝ) S,
        ∑' k, ∑' i, ‖hk k i s ω‖ₑ ^ 2 ≤
          ENNReal.ofReal (1 * (‖ψ' s ω ((L : ℤ) + 1)‖ ^ 2 + ‖ψ' s ω (-(L : ℤ) - 1)‖ ^ 2)) := by
      filter_upwards [hon] with ω hon' s hs
      set σ : ℝ≥0 := ⟨s, hs.1.le⟩ with hσ
      have hrow := fun x (hx : x ∈ Sb) => lemma82_rows (fun y => u y σ ω)
        (fun y hy => (hu y hy).1.support ω σ) (hon' σ) hx
      have hLm : (L : ℤ) ∈ Sb := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
      have hLm' : -(L : ℤ) ∈ Sb := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
      have hy0 : ∀ y ∉ Sb, ∑' b : Bool, ∑' i, ‖hk (y, b) i s ω‖ₑ ^ 2 = 0 := fun y hy => by
        simp [hk_0 y hy]
      have hy1 : ∀ y ∈ Sb, ∑' b : Bool, ∑' i, ‖hk (y, b) i s ω‖ₑ ^ 2 =
          ENNReal.ofReal (‖u y s ω L‖ ^ 2 * ‖ψ' s ω (L + 1)‖ ^ 2 +
            ‖u y s ω (-L)‖ ^ 2 * ‖ψ' s ω (-L - 1)‖ ^ 2) := fun y hy => by
        rw [tsum_fintype, Fintype.sum_bool, hk_t y hy, hk_f y hy, ← ENNReal.tsum_add,
          ← lemma82_tsum_boundaryCoef]
        exact tsum_congr fun i => lemma82_enorm_re_im _
      refine le_of_eq ?_
      calc ∑' k, ∑' i, ‖hk k i s ω‖ₑ ^ 2
          = ∑' k : ℤ × Bool, ∑' i, ‖hk (k.1, k.2) i s ω‖ₑ ^ 2 := rfl
        _ = ∑' y, ∑' b : Bool, ∑' i, ‖hk (y, b) i s ω‖ₑ ^ 2 :=
          ENNReal.tsum_prod (f := fun y b => ∑' i, ‖hk (y, b) i s ω‖ₑ ^ 2)
        _ = ∑ y ∈ Sb, ∑' b : Bool, ∑' i, ‖hk (y, b) i s ω‖ₑ ^ 2 := tsum_eq_sum hy0
        _ = ∑ y ∈ Sb, ENNReal.ofReal (‖u y s ω L‖ ^ 2 * ‖ψ' s ω (L + 1)‖ ^ 2 +
            ‖u y s ω (-L)‖ ^ 2 * ‖ψ' s ω (-L - 1)‖ ^ 2) := Finset.sum_congr rfl hy1
        _ = ENNReal.ofReal (1 * (‖ψ' s ω ((L : ℤ) + 1)‖ ^ 2 + ‖ψ' s ω (-(L : ℤ) - 1)‖ ^ 2)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
          congr 1
          have r1 : ∑ y ∈ Sb, ‖u y s ω L‖ ^ 2 = 1 := hrow L hLm
          have r2 : ∑ y ∈ Sb, ‖u y s ω (-L)‖ ^ 2 = 1 := hrow (-L) hLm'
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, r1, r2]
          ring
    calc ∑' k, energy μ (hk k) S
        = ∑' k, ∫⁻ ω, (∫⁻ s in Set.Ioc 0 S, ∑' i, ‖hk k i s ω‖ₑ ^ 2) ∂μ := rfl
      _ ≤ ∫⁻ ω, (∑' k, ∫⁻ s in Set.Ioc 0 S, ∑' i, ‖hk k i s ω‖ₑ ^ 2) ∂μ :=
          picardAux_tsum_lintegral_le _
      _ ≤ ∫⁻ ω, (∫⁻ s in Set.Ioc 0 S, ∑' k, ∑' i, ‖hk k i s ω‖ₑ ^ 2) ∂μ :=
          lintegral_mono fun ω => picardAux_tsum_lintegral_le _
      _ ≤ ∫⁻ ω, (∫⁻ s in Set.Ioc 0 S,
          ENNReal.ofReal (1 * (‖ψ' s ω ((L : ℤ) + 1)‖ ^ 2 + ‖ψ' s ω (-(L : ℤ) - 1)‖ ^ 2))) ∂μ :=
          lintegral_mono_ae (hpe.mono fun ω h => setLIntegral_mono' measurableSet_Ioc h)
      _ ≤ ENNReal.ofReal (1 * J) :=
          lemma82_lintegral_density_le hB hψ hψ'm hψ'I.continuous hψ'e (by norm_num) hL2
            (by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (L : ℤ) + 1)]; omega)
            (by rw [abs_of_neg (by omega : -(L : ℤ) - 1 < 0)]; omega) hS.le
  -- measurability of the supremum
  set Fp : Ω → ℝ≥0∞ := fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
      ((∑ x ∈ Sb, |‖ψ' s ω x‖ ^ 2 - ‖ψL' s ω x‖ ^ 2|) ^ 2) with hFpdef
  have hFpm : Measurable Fp := by
    have h := measurable_iSup_Icc_tsum (mΩ := mΩ) (T := S)
      (g := fun z s ω => if z = 0 then ENNReal.ofReal
        ((∑ x ∈ Sb, |‖ψ' s ω x‖ ^ 2 - ‖ψL' s ω x‖ ^ 2|) ^ 2) else 0) ?_ ?_
    · have e : Fp = fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) S, ∑' z : ℤ, (if z = 0 then ENNReal.ofReal
          ((∑ x ∈ Sb, |‖ψ' s ω x‖ ^ 2 - ‖ψL' s ω x‖ ^ 2|) ^ 2) else 0) := by
        funext ω; simp only [hFpdef, tsum_ite_eq]
      rw [e]; exact h
    · intro z ω
      by_cases hz : z = 0
      · simp only [hz, ↓reduceIte]
        refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.pow ?_ 2)
        refine continuousOn_finsetSum _ fun x _ => ?_
        exact (((lemma82_continuousOn_apply (φ := fun s => ψ' s ω) (hψ'I.continuous ω) x).norm.pow 2).sub
          ((lemma82_continuousOn_apply (φ := fun s => ψL' s ω) (hψLI.continuous ω) x).norm.pow 2)).abs.mono
          Set.Icc_subset_Ici_self
      · simp only [hz, ↓reduceIte]; exact continuousOn_const
    · intro z s hs
      by_cases hz : z = 0
      · simp only [hz, ↓reduceIte]
        exact ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun x _ =>
          continuous_abs.measurable.comp (((hψ'm ⟨s, hs.1⟩ x).norm.pow_const 2).sub
            ((hψLm ⟨s, hs.1⟩ x).norm.pow_const 2))).pow_const 2)
      · simp only [hz, ↓reduceIte]; exact measurable_const
  have hFpe : (fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
      ((∑ x ∈ Sb, |density ψ ω s x - density ψL ω s x|) ^ 2)) =ᵐ[μ] Fp := by
    filter_upwards [hψ'e, hψLe] with ω he1 he2
    refine iSup_congr fun s => iSup_congr fun hs => ?_
    have e1 : ψ s ω = ψ' s ω := (he1 ⟨s, hs.1⟩).symm
    have e2 : ψL s ω = ψL' s ω := (he2 ⟨s, hs.1⟩).symm
    simp only [density, e1, e2]
  refine ⟨hFpm.aemeasurable.congr hFpe.symm, ?_⟩
  -- assembly
  calc ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Sb, |density ψ ω s x - density ψL ω s x|) ^ 2)) ∂μ
      ≤ ∫⁻ ω, (G ω + 8 * X ω) ∂μ := lintegral_mono_ae hpt
    _ = ∫⁻ ω, G ω ∂μ + 8 * ∫⁻ ω, X ω ∂μ := by
        rw [lintegral_add_left hGm, lintegral_const_mul' (8 : ℝ≥0∞) X (by norm_num)]
    _ ≤ 2 * ENNReal.ofReal S * ENNReal.ofReal (2 * J) + 8 * (4 * ENNReal.ofReal (1 * J)) :=
        add_le_add hEG (mul_le_mul' le_rfl hEX)
    _ = ENNReal.ofReal (4 * (8 + S) * J) := by
        have e : 4 * (8 + S) * J = 2 * S * (2 * J) + 8 * (4 * (1 * J)) := by ring
        have h2S : (0 : ℝ) ≤ 2 * S := by linarith
        rw [e, ENNReal.ofReal_add (mul_nonneg h2S (by linarith)) (by positivity),
          ENNReal.ofReal_mul h2S, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        simp only [ENNReal.ofReal_ofNat]

end QSSEPtoKPZ
