/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage3-design.md.
-/
module

public import QSSEPtoKPZ.Tightness.AssemblyAux

/-!
# Proposition 5.1, tightness: assembly (task Q4)

`tightAsm_prop_5_1` is the statement `prop_5_1` of `Tightness/Prop51.lean`, proved as in the
proof of Proposition 5.1 of the article, in the form of decisions D1', D2' of
`docs/stage3-design.md` (a criterion in `C([0,T], ℳ₊(ℝ))` with the countable family `f_j`).

Given `T > 0` and `ε > 0`:
* compact containment (condition (i)): with `K = 4 e^{2T} / ε`, (5.1) gives
  `ℙ(sup_{t ≤ T} 𝖹_n(t;cosh) ≥ K) ≤ ε/2`, and `{ν : ∫ cosh dν ≤ K}` is compact
  (`isCompact_tightCoshBall`);
* modulus of continuity of the test paths (condition (ii)): for `j, m ∈ ℕ`, with
  `η_m = 1/(3(m+1))`, Aldous' criterion (`tightAsm_modulus`, from (5.2)) and the choice of scales
  `tightAsm_choose` give `δ_{j,m} > 0`, independent of the realization and of `n`, with
  `ℙ(∃ s, t ≤ T, |t - s| ≤ δ_{j,m}, |𝖹_n(t;f_j) - 𝖹_n(s;f_j)| > 1/(m+1)) ≤ ε 2^{-j-m-3}`;
* the compact set is `𝒦 = {γ : γ(t) ∈ {∫ cosh ≤ K} ∀ t, t ↦ ∫ f_j dγ(t) ∈ 𝒞_j ∀ j}`, with
  `𝒞_j` the (Arzelà–Ascoli) compact set of real paths bounded by `K` with modulus `δ_{j,·}`
  (`isCompact_pathCptSet`, `isCompact_pathCptModulus`);
* union bound: `ℙ(Zv ∉ 𝒦) ≤ ε/2 + ∑_{j,m} ε 2^{-j-m-3} = ε`.

The version `Zv` on `[0,T]` is compared with a version `Z'` on `[0,T+2]` with adapted test
integrals (`exists_tiltedPath_version`), to which Aldous' criterion applies: almost surely both
coincide with `𝖹_n(t)` for every `t ∈ [0,T]`. The event `{Zv ∉ 𝒦}` is contained, up to a null
set, in the union of the events above, which bounds its outer probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal lp BoundedContinuousFunction

noncomputable section

namespace QSSEPtoKPZ

universe u

/-- `∑_{j,m} ε/8 · 2^{-j} 2^{-m} = ε/2`, in `[0, ∞]`, and `ε/2 + ε/2 = ε`. -/
private lemma tightAsm_tsum {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε / 2) + ∑' j : ℕ, ∑' m : ℕ,
      ENNReal.ofReal (ε / 8 * (1 / 2) ^ j * (1 / 2) ^ m) = ENNReal.ofReal ε := by
  have h2 : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hem : ∀ j m : ℕ, ENNReal.ofReal (ε / 8 * (1 / 2) ^ j * (1 / 2) ^ m) =
      ENNReal.ofReal (ε / 8) * 2⁻¹ ^ j * 2⁻¹ ^ m := by
    intro j m
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num), h2]
  simp_rw [hem, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **Proposition 5.1**, tightness (statement `prop_5_1` of `Tightness/Prop51.lean`). -/
theorem tightAsm_prop_5_1 {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ 𝒦 : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), IsCompact 𝒦 ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
        IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ → ∀ {n : ℝ}, 1 ≤ n →
        ∀ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ),
          (∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t) →
          μ (Zv ⁻¹' 𝒦ᶜ) ≤ ENNReal.ofReal ε := by
  -- the constants, chosen before the probability space
  obtain ⟨c, hc⟩ := aldous_condition.{u} (T + 1)
  set c₀ : ℝ := max c 0 with hc₀
  choose Cj hCj0 hCj using fun j => isC13_bumpTestRaw j
  set η : ℕ → ℝ := fun m => 1 / (3 * (m + 1)) with hη_def
  have hη : ∀ m, 0 < η m := fun m => by positivity
  set e : ℕ → ℕ → ℝ := fun j m => ε / 8 * (1 / 2) ^ j * (1 / 2) ^ m with he_def
  choose δ δ₁ N hδ hδδ₁ hδ₁ hN hbound using fun j m =>
    tightAsm_choose T c₀ (Cj j) (η m / 4) (e := e j m) (by positivity)
  set K : ℝ := 4 * Real.exp (2 * T) / ε with hK_def
  have hK : 0 < K := by positivity
  refine ⟨pathCptSet (tightCoshBall (ENNReal.ofReal K)) fun j => pathCptModulus T K (δ j),
    isCompact_pathCptSet (isCompact_tightCoshBall _ ENNReal.ofReal_ne_top)
      fun j => isCompact_pathCptModulus T K (δ j) (hδ j), ?_⟩
  intro Ω mΩ 𝓕 μ _ B ψ hB hψ n hn Zv hZ
  -- a version on `[0, T+2]` with adapted test integrals; Lemma 5.2; (5.2) with the constant `c₀`
  obtain ⟨Zv', -, hZa, hZe⟩ := exists_tiltedPath_version hB hψ hn (T + 2)
  obtain ⟨hsumb, -, hcc⟩ := lemma_5_2 hB hψ hn
  have hsum : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t) := by
    filter_upwards [hsumb] with ω hω t ht
    simpa using hω t ht 0 ⟨by norm_num, by norm_num⟩
  have hc' : ∀ {C : ℝ} {φ : ℝ → ℝ}, IsC13 1 (fun _ => φ) (fun _ _ => 0) C →
      ∀ {τ : Ω → ℝ≥0}, IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)) →
      (∀ ω, (τ ω : ℝ) ≤ T + 1) → ∀ {s η : ℝ}, 0 ≤ s → s ≤ 1 / 16 → 0 < η →
      μ {ω | η < |pairZ n ψ ω ((τ ω : ℝ) + s) φ - pairZ n ψ ω (τ ω) φ|} ≤
        ENNReal.ofReal (c₀ * (C * s / η + C ^ 2 * Real.sqrt s / η ^ 2)) := by
    intro C φ hφ τ hτ hτT s η hs hs' hη
    have hC := aldousCond_C_nonneg hφ
    exact (hc hB hψ hn hφ hτ hτT hs hs' hη).2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  -- compact containment: `ℙ(sup_{t ≤ T} 𝖹_n(t;cosh) ≥ K) ≤ ε/2`
  set A₀ : Set Ω := {ω | ENNReal.ofReal K ≤ ⨆ t ∈ Icc (0 : ℝ) T,
    ENNReal.ofReal (pairZ n ψ ω t Real.cosh)} with hA₀_def
  have hA₀ : μ A₀ ≤ ENNReal.ofReal (ε / 2) := by
    refine (hcc T K hT hK).trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [hK_def]
    field_simp
    ring
  -- modulus of continuity of the test paths
  set E : ℕ → ℕ → Set Ω := fun j m => {ω | ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) T,
    |t - s| ≤ δ j m ∧ 3 * η m ≤ |tightAsmX hT.le Zv' j t ω - tightAsmX hT.le Zv' j s ω|}
    with hE_def
  have hE : ∀ j m, μ (E j m) ≤ ENNReal.ofReal (e j m) := fun j m =>
    (tightAsm_modulus hT.le (le_max_right c 0) hc' Zv' hZa hZe hsum (hCj0 j) (hCj j 1) (hη m)
      (hδ j m) (hδδ₁ j m) (hδ₁ j m) (hN j m)).trans (ENNReal.ofReal_le_ofReal (hbound j m))
  -- `{Zv ∉ 𝒦} ⊆ A₀ ∪ ⋃_{j,m} E_{j,m}` almost surely
  have hincl : Zv ⁻¹' (pathCptSet (tightCoshBall (ENNReal.ofReal K))
      fun j => pathCptModulus T K (δ j))ᶜ ≤ᵐ[μ] (A₀ ∪ ⋃ j, ⋃ m, E j m : Set Ω) := by
    filter_upwards [hZ, hZe, hsumb] with ω hZω hZ'ω hbω hω
    by_cases hA : ω ∈ A₀
    · exact Or.inl hA
    refine Or.inr (by_contra fun hne => hω ?_)
    have hball : ∀ t, Zv ω t ∈ tightCoshBall (ENNReal.ofReal K) := by
      intro t
      show ∫⁻ x, ENNReal.ofReal (Real.cosh x) ∂(Zv ω t : Measure ℝ) ≤ ENNReal.ofReal K
      rw [hZω t, tightAsm_lintegral_cosh (hbω t t.2.1 1 ⟨by norm_num, le_rfl⟩)
        (hbω t t.2.1 (-1) ⟨le_rfl, by norm_num⟩)]
      by_contra h
      exact hA (le_trans (not_le.1 h).le
        (le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) T) =>
          ENNReal.ofReal (pairZ n ψ ω t Real.cosh)) (t : ℝ) t.2))
    have hXZ : ∀ j, ∀ u : Icc (0 : ℝ) T,
        tightAsmX hT.le Zv' j u ω = pathCptTest j (Zv ω) u := by
      intro j u
      rw [tightAsmX_of_mem hT.le Zv' j ⟨u.2.1, by linarith [u.2.2]⟩, pathCptTest_apply,
        hZ'ω, hZω]
    refine ⟨hball, fun j => ⟨fun t => ?_, fun m s t hst => ?_⟩⟩
    · rw [pathCptTest_apply]
      exact tightAsm_abs_integral_le hK.le (hball t) j
    · by_contra hlt
      refine hne (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨m, s, s.2, t, t.2, ?_, ?_⟩⟩)
      · rw [abs_sub_comm]; exact hst
      · rw [hXZ, hXZ, abs_sub_comm]
        have e3 : 3 * η m = 1 / (m + 1) := by
          simp only [hη_def]; field_simp
        rw [e3]
        exact (not_le.1 hlt).le
  calc μ (Zv ⁻¹' (pathCptSet (tightCoshBall (ENNReal.ofReal K))
        fun j => pathCptModulus T K (δ j))ᶜ)
      ≤ μ (A₀ ∪ ⋃ j, ⋃ m, E j m) := measure_mono_ae hincl
    _ ≤ μ A₀ + μ (⋃ j, ⋃ m, E j m) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ∑' j : ℕ, ∑' m : ℕ, ENNReal.ofReal (e j m) :=
        add_le_add hA₀ ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j =>
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => hE j m)))
    _ = ENNReal.ofReal ε := tightAsm_tsum hε

end QSSEPtoKPZ
