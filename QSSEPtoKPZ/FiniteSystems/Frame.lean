/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.FiniteSystems.Pairing
public import QSSEPtoKPZ.WaveFunction.UnitNorm

/-!
# Norm conservation, unit versions, and the columns of `U_t` (task L4)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task L4.
`docs/stage5-design.md`, Sections 1.2 (b)–(d), 3.2, 3.4 (L4).

* `IsWaveIto.norm_eq` (finite `L`): `‖ψ_t‖ = ‖ψ_0‖` for all `t`, almost surely.
* `IsWaveIto.exists_unitVersion` (finite `L`): an Itô solution with `‖ψ_0‖ = 1` for the augmented
  filtration has a version with `‖ψ_t‖ = 1` for every `t` and `ω`.
* `IsWaveFunction.exists_unitIto` (every `L`): every wave function has a unit-norm Itô version
  (for `L = ∞` from Stage 2's `IsUnitWave`; for finite `L` from `IsGoodWaveBox` (task L3) and the
  conservation of the norm, which makes `τ_R ∧ N = N` for `R > 1`).
* `IsWaveIto.frame_orthonormal`: Itô solutions `u^y` with `u^y_0 = e_y`, `y ∈ Λ_L`, are
  orthonormal for all `t`, almost surely (the columns `U_t e_y` of the unitary matrix of
  Definition 1.1).
* `frame_parseval` (finite-dimensional linear algebra): an orthonormal family `(w_y)_{y ∈ Λ_L}` of
  vectors supported in `Λ_L` satisfies `∑_y |⟨w_y, v⟩|² = ∑_{x ∈ Λ_L} |v(x)|²` for every `v`
  (with `v = e_x`: the rows of `U_t` are unit vectors).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp ComplexConjugate InnerProductSpace

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℤ × Fin 2 → ℝ → Ω → ℝ}

/-! ### Auxiliary lemmas -/

/-- The real and imaginary parts of `ψ(x)` with the coefficients of the wave equation make
`ψ(x)` a complex Itô process. -/
private lemma frame_cIto_of_re_im {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0} {L : ℕ∞}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} {x : ℤ}
    (hre : IsItoProcessUpTo 𝓖 μ B τ (fun t ω => (ψ t ω x).re)
      (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).re) (waveDiffRe ψ x))
    (him : IsItoProcessUpTo 𝓖 μ B τ (fun t ω => (ψ t ω x).im)
      (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).im) (waveDiffIm ψ x)) :
    IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => ψ t ω x)
      (fun s ω => -((degree L x : ℂ) / 2) * ψ s ω x) (waveDiffC ψ x) := by
  have e1 : (fun s ω => (-((degree L x : ℂ) / 2) * ψ s ω x).re) =
      fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).re := by
    funext s ω
    simp [Complex.mul_re]
  have e2 : (fun s ω => (-((degree L x : ℂ) / 2) * ψ s ω x).im) =
      fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).im := by
    funext s ω
    simp [Complex.mul_im]
  have e3 : (fun i s ω => (waveDiffC ψ x i s ω).re) = waveDiffRe ψ x := by
    funext i s ω; simp
  have e4 : (fun i s ω => (waveDiffC ψ x i s ω).im) = waveDiffIm ψ x := by
    funext i s ω; simp
  unfold IsCItoProcessUpTo
  rw [e1, e2, e3, e4]
  exact ⟨hre, him⟩

/-- **Conservation of the norm on a box, from the Itô form up to the localizing times.** If `ψ`
has continuous adapted `ℓ²` paths vanishing outside `Λ_L`, starts from `ψ0`, and its coordinates
are complex Itô processes with the coefficients of the wave equation up to every `τ_R ∧ N`, then
`‖ψ_t‖ = ‖ψ0‖` for all `t`, almost surely. -/
private lemma frame_norm_eq_aux [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ} {ψ0 : ℓ²(ℤ, ℂ)} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω)
    (hsupp : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0) (hinit : ∀ ω, ψ 0 ω = ψ0)
    (hito : ∀ (R : ℝ) (N : ℝ≥0), ∀ x ∈ box L, IsCItoProcessUpTo 𝓖 μ B (waveStop ψ R N)
      (fun t ω => ψ t ω x) (fun s ω => -((degree L x : ℂ) / 2) * ψ s ω x) (waveDiffC ψ x)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ‖ψ t ω‖ = ‖ψ0‖ := by
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have hsupp' : ∀ ω (s : ℝ), 0 ≤ s → ∀ x, x ∉ box L → ψ s ω x = 0 :=
    fun ω s hs x hx => hsupp ω ⟨s, hs⟩ x hx
  have key : ∀ N n : ℕ, ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (∑ x ∈ S, conj (ψ (min t (waveStop ψ ((n : ℝ) + 1) N ω) : ℝ≥0) ω x) *
        ψ (min t (waveStop ψ ((n : ℝ) + 1) N ω) : ℝ≥0) ω x) =
        ∑ x ∈ S, conj (ψ 0 ω x) * ψ 0 ω x := by
    intro N n
    have hτ := isStoppingTime_waveStop_of_continuous hadapt hc ((n : ℝ) + 1) N
    have hbd : ∀ ω (s : ℝ), 0 ≤ s → s ≤ waveStop ψ ((n : ℝ) + 1) N ω →
        ‖ψ s ω‖ ≤ max ((n : ℝ) + 1) ‖ψ0‖ ∧ ‖ψ s ω‖ ≤ max ((n : ℝ) + 1) ‖ψ0‖ := by
      intro ω s hs0 hs
      have h1 := pairing_norm_le_of_le_waveStop hc hs0 hs
      rw [hinit] at h1
      exact ⟨h1, h1⟩
    have hito' : ∀ x ∈ S, IsCItoProcessUpTo 𝓖 μ B (waveStop ψ ((n : ℝ) + 1) N)
        (fun t ω => ψ t ω x) (fun s ω => -((degree L x : ℂ) / 2) * ψ s ω x) (waveDiffC ψ x) :=
      fun x hx => hito _ N x (pairing_mem_box_iff.2 hx)
    have hP := pairing_isCIto_sum hB hτ ⟨N, fun ω => waveStop_le ψ _ N ω⟩ S (pairing_degree_le L)
      (pairing_degree_le L) hito' hito' hc hc hadapt hadapt hbd
    have hP0 := hP.congr_pos hB (a' := fun _ _ => 0) (b' := fun _ _ _ => 0)
      (fun ω s hs0 _ => (pairing_drift_sum_box L ψ ψ s ω (hsupp' ω s hs0)
        (hsupp' ω s hs0)).symm)
      (fun i s ω hs => (pairing_coef_sum_box L ψ ψ s ω (hsupp' ω s hs.le)
        (hsupp' ω s hs.le) i).symm)
    exact pairing_eq_of_zero hB hP0
  have key' := ae_all_iff.2 fun N : ℕ => ae_all_iff.2 fun n : ℕ => key N n
  filter_upwards [key'] with ω hω t
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨n1, hn1⟩ := pairing_waveStop_eventually (hc ω) N
  have e := hω N n1 t
  rw [hn1 _ le_rfl, min_eq_left (show t ≤ (N : ℝ≥0) from by exact_mod_cast hN)] at e
  rw [← pairing_inner_eq_sum _ _ (hsupp ω t), ← pairing_inner_eq_sum (ψ 0 ω) (ψ 0 ω)
    (fun x hx => by simpa using hsupp ω 0 x hx), hinit ω,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖ψ t ω‖ ^ 2 = ‖ψ0‖ ^ 2 := by exact_mod_cast e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e'

/-- **Modification on a null set.** Let `ψ` have continuous `𝓕ᵃ`-adapted `ℓ²` paths vanishing
outside `Λ_L`, start from `ψ0` with `‖ψ0‖ = 1`, have norm `1` at all times almost surely, and
let its coordinates be Itô processes with the coefficients of the wave equation up to stopping
times `τ_N` equal to `N` on the paths of norm `1`. Then `ψ`, changed into `ψ0` on a measurable
null set, is an Itô solution of norm `1` for every `t` and `ω`. -/
private lemma frame_modify [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) {L : ℕ∞}
    {ψ0 : ℓ²(ℤ, ℂ)} (h1 : ‖ψ0‖ = 1) {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hadapt : ∀ (t : ℝ≥0) (x : ℤ), Measurable[nullAug μ 𝓕 t] fun ω => ψ t ω x)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω)
    (hsupp : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0) (hinit : ∀ ω, ψ 0 ω = ψ0)
    (hnorm : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ‖ψ t ω‖ = 1)
    (τ : ℝ≥0 → Ω → ℝ≥0) (hτ : ∀ N ω, (∀ t : ℝ≥0, ‖ψ t ω‖ = 1) → τ N ω = N)
    (hre : ∀ x ∈ box L, ∀ N : ℝ≥0, IsItoProcessUpTo (nullAug μ 𝓕) μ B (τ N)
      (fun t ω => (ψ t ω x).re) (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).re)
      (waveDiffRe ψ x))
    (him : ∀ x ∈ box L, ∀ N : ℝ≥0, IsItoProcessUpTo (nullAug μ 𝓕) μ B (τ N)
      (fun t ω => (ψ t ω x).im) (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).im)
      (waveDiffIm ψ x)) :
    ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveIto L (nullAug μ 𝓕) B ψ0 ψ' μ ∧
      (∀ ω (t : ℝ≥0), ‖ψ' t ω‖ = 1) ∧ ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω := by
  classical
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  set N := toMeasurable μ {ω | ¬ ∀ t : ℝ≥0, ‖ψ t ω‖ = 1} with hNdef
  have hN0 : μ N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hnorm
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa : ∀ᵐ ω ∂μ, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω, ω ∉ N → ∀ t : ℝ≥0, ‖ψ t ω‖ = 1 := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hNt : ∀ t : ℝ≥0, MeasurableSet[nullAug μ 𝓕 t] N := fun t =>
    nullSets_le_nullAug t _ (measurableSet_nullSets hNm hN0)
  have hsupp0 : ∀ x, x ∉ box L → ψ0 x = 0 := fun x hx => by
    rw [← hinit ω0]; exact hsupp ω0 0 x hx
  set ψ' : ℝ → Ω → ℓ²(ℤ, ℂ) := fun t ω => if ω ∈ N then ψ0 else ψ t ω with hψ'
  -- transfer of the Itô property
  have htr : ∀ (f : ℂ → ℝ) (W : (ℝ → Ω → ℓ²(ℤ, ℂ)) → ℤ → ℤ × Fin 2 → ℝ → Ω → ℝ),
      (∀ φ φ' x i s ω s' ω', φ s ω = φ' s' ω' → W φ x i s ω = W φ' x i s' ω') →
      ∀ x (D : ℝ) (Nt : ℝ≥0), IsItoProcessUpTo (nullAug μ 𝓕) μ B (τ Nt)
        (fun t ω => f (ψ t ω x)) (fun s ω => D * f (ψ s ω x)) (W ψ x) →
      IsItoProcessUpTo (nullAug μ 𝓕) μ B (fun _ => Nt) (fun t ω => f (ψ' t ω x))
        (fun s ω => D * f (ψ' s ω x)) (W ψ' x) := by
    intro f W hW x D Nt h
    have hWψ' : ∀ i s ω, W ψ' x i s ω =
        if ω ∈ N then W (fun _ _ => ψ0) x i 0 ω0 else W ψ x i s ω := by
      intro i s ω
      by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte]; exact hW _ _ x i s ω 0 ω0 (by simp [ψ', hω])
      · simp only [hω, ↓reduceIte]; exact hW _ _ x i s ω s ω (by simp [ψ', hω])
    refine h.congr_null hB.nullAug hN0 (fun ω hω => (hτ Nt ω (hgood ω hω)).symm)
      (fun ω hω t => by simp [ψ', hω]) (fun ω hω s => by simp [ψ', hω])
      (fun ω hω i s => by simp only [hWψ', hω, ↓reduceIte]) (fun i => ?_)
    have hm : Measurable fun p : ℝ × Ω => if p.2 ∈ N then
        (if 0 < p.1 then (if p.1 ≤ (Nt : ℝ) then W (fun _ _ => ψ0) x i 0 ω0 else 0) else 0)
        else (if 0 < p.1 then (if p.1 ≤ τ Nt p.2 then W ψ x i p.1 p.2 else 0) else 0) :=
      Measurable.ite (hNm.preimage measurable_snd)
        (Measurable.ite (measurableSet_lt measurable_const measurable_fst)
          (Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const
            measurable_const) measurable_const) (h.integrable.meas i)
    convert hm using 1
    funext p
    by_cases hp : p.2 ∈ N
    · simp only [hp, hWψ', ↓reduceIte]
    · simp only [hp, hWψ', ↓reduceIte, hτ Nt p.2 (hgood p.2 hp)]
  have hWre : ∀ (φ φ' : ℝ → Ω → ℓ²(ℤ, ℂ)) x i s ω s' ω', φ s ω = φ' s' ω' →
      waveDiffRe φ x i s ω = waveDiffRe φ' x i s' ω' := by
    intro φ φ' x i s ω s' ω' h
    simp only [waveDiffRe, h]
  have hWim : ∀ (φ φ' : ℝ → Ω → ℓ²(ℤ, ℂ)) x i s ω s' ω', φ s ω = φ' s' ω' →
      waveDiffIm φ x i s ω = waveDiffIm φ' x i s' ω' := by
    intro φ φ' x i s ω s' ω' h
    simp only [waveDiffIm, h]
  refine ⟨ψ', ⟨fun t x => ?_, fun ω => ?_, fun ω t x hx => ?_, fun ω => ?_,
    fun x hx Nt => htr Complex.re waveDiffRe hWre x _ Nt (hre x hx Nt),
    fun x hx Nt => htr Complex.im waveDiffIm hWim x _ Nt (him x hx Nt)⟩,
    fun ω t => ?_, ?_⟩
  · have e : (fun ω => ψ' t ω x) = fun ω => if ω ∈ N then ψ0 x else ψ t ω x := by
      funext ω; by_cases hω : ω ∈ N <;> simp [ψ', hω]
    rw [e]
    exact Measurable.ite (hNt t) measurable_const (hadapt t x)
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ↓reduceIte]; exact continuous_const
    · simp only [ψ', hω, ↓reduceIte]; exact hc ω
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ↓reduceIte]; exact hsupp0 x hx
    · simp only [ψ', hω, ↓reduceIte]; exact hsupp ω t x hx
  · by_cases hω : ω ∈ N
    · simp [ψ', hω]
    · simp only [ψ', hω, ↓reduceIte]; exact hinit ω
  · by_cases hω : ω ∈ N
    · simp only [ψ', hω, ↓reduceIte]; exact h1
    · simp only [ψ', hω, ↓reduceIte]; exact hgood ω hω t
  · filter_upwards [hNa] with ω hω t
    simp [ψ', hω]

/-- **Conservation of the norm on a finite box**: almost surely `‖ψ_t‖ = ‖ψ0‖` for all `t ≥ 0`. -/
theorem IsWaveIto.norm_eq [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ} {ψ0 : ℓ²(ℤ, ℂ)} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsWaveIto L 𝓖 B ψ0 ψ μ) : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ‖ψ t ω‖ = ‖ψ0‖ := by
  filter_upwards [h.inner_eq hB h] with ω hω t
  have e := hω t
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖ψ t ω‖ ^ 2 = ‖ψ0‖ ^ 2 := by exact_mod_cast e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e'

/-- **Unit-norm version on a finite box.** An Itô solution on `Λ_L` (`L` finite) for the
augmented filtration with `‖ψ0‖ = 1` has a version which is still an Itô solution, has norm `1`
for every `t` and `ω`, and is indistinguishable from it. -/
theorem IsWaveIto.exists_unitVersion [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {L : ℕ} {ψ0 : ℓ²(ℤ, ℂ)} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)}
    (h : IsWaveIto L (QSSEPtoKPZ.nullAug μ 𝓕) B ψ0 ψ μ) (h1 : ‖ψ0‖ = 1) :
    ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveIto L (QSSEPtoKPZ.nullAug μ 𝓕) B ψ0 ψ' μ ∧
      (∀ ω (t : ℝ≥0), ‖ψ' t ω‖ = 1) ∧ ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω := by
  obtain ⟨ψ', h1', h2', h3'⟩ := frame_modify hB h1 h.adapted h.continuous h.support h.init
    (by filter_upwards [h.norm_eq hB.nullAug] with ω hω t; rw [hω t, h1])
    (fun N _ => N) (fun _ _ _ => rfl) (fun x hx N => h.re x hx N) (fun x hx N => h.im x hx N)
  exact ⟨ψ', h1', h2', h3'⟩

/-- **Every wave function has a unit-norm Itô version** (every `L ∈ ℕ ∪ {∞}`): an Itô solution
for the augmented filtration started from `e₀`, of norm `1` for every `t` and `ω`, and
indistinguishable from `ψ`. -/
theorem IsWaveFunction.exists_unitIto [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {L : ℕ∞} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveIto L (QSSEPtoKPZ.nullAug μ 𝓕) B waveInit ψ' μ ∧
      (∀ ω (t : ℝ≥0), ‖ψ' t ω‖ = 1) ∧ ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω := by
  induction L using ENat.recTopCoe with
  | top =>
    obtain ⟨ψ', hu⟩ := hψ.exists_isUnitWave hB
    have hdeg : ∀ x, ((degree ⊤ x : ℝ) / 2) = 1 := by
      intro x; rw [waveDegree_top]; norm_num
    refine ⟨ψ', ⟨fun t x => hu.toIsGoodWave.measurable_apply t x, hu.continuous,
      fun ω t x hx => absurd (waveBox_top_mem x) hx, hu.init, fun x _ N => ?_, fun x _ N => ?_⟩,
      hu.norm_eq_one, hu.ae_eq⟩
    · have h := IsGoodWave.isItoProcessUpTo_re hB hu.toIsGoodWave 2 N x
      rw [hu.waveStop_eq N] at h
      have e : (fun s ω => -((degree ⊤ x : ℝ) / 2) * (ψ' s ω x).re) =
          fun s ω => -(ψ' s ω x).re := by
        funext s ω; rw [hdeg]; ring
      rw [e]
      exact h
    · have h := IsGoodWave.isItoProcessUpTo_im hB hu.toIsGoodWave 2 N x
      rw [hu.waveStop_eq N] at h
      have e : (fun s ω => -((degree ⊤ x : ℝ) / 2) * (ψ' s ω x).im) =
          fun s ω => -(ψ' s ω x).im := by
        funext s ω; rw [hdeg]; ring
      rw [e]
      exact h
  | coe n =>
    obtain ⟨ψ1, hg⟩ := hψ.exists_isGoodWaveBox
    have hito : ∀ (R : ℝ) (N : ℝ≥0), ∀ x ∈ box (n : ℕ∞), IsCItoProcessUpTo (QSSEPtoKPZ.nullAug μ 𝓕) μ B
        (waveStop ψ1 R N) (fun t ω => ψ1 t ω x) (fun s ω => -((degree n x : ℂ) / 2) * ψ1 s ω x)
        (waveDiffC ψ1 x) := fun R N x hx =>
      frame_cIto_of_re_im (hg.isItoProcessUpTo_re hB R N hx) (hg.isItoProcessUpTo_im hB R N hx)
    have hnorm := frame_norm_eq_aux hB.nullAug hg.measurable_apply hg.continuous hg.support
      hg.init hito
    obtain ⟨ψ', h1', h2', h3'⟩ := frame_modify hB norm_waveInit hg.measurable_apply
      hg.continuous hg.support hg.init
      (by filter_upwards [hnorm] with ω hω t; rw [hω t, norm_waveInit])
      (fun N => waveStop ψ1 2 N)
      (fun N ω h => hitTime_eq_of_forall_lt fun t _ => by simp only [h t]; norm_num)
      (fun x hx N => hg.isItoProcessUpTo_re hB 2 N hx)
      (fun x hx N => hg.isItoProcessUpTo_im hB 2 N hx)
    refine ⟨ψ', h1', h2', ?_⟩
    filter_upwards [h3', hg.ae_eq] with ω h1 h2 t
    rw [h1 t, h2 t]

/-- **The columns of `U_t` are orthonormal.** If, for each `y ∈ Λ_L` (`L` finite), `u y` is an Itô
solution on `Λ_L` started from `e_y`, all driven by the same Brownian family for the same
filtration, then almost surely, for all `t ≥ 0` and `y, z ∈ Λ_L`, `⟨u^y_t, u^z_t⟩ = δ_{yz}`. -/
theorem IsWaveIto.frame_orthonormal [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ} {u : ℤ → ℝ → Ω → ℓ²(ℤ, ℂ)}
    (hu : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, IsWaveIto L 𝓖 B (lp.single 2 y 1) (u y) μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ z ∈ Finset.Icc (-(L : ℤ)) L,
      ⟪u y t ω, u z t ω⟫_ℂ = if y = z then 1 else 0 := by
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have h : ∀ y z : ℤ, ∀ᵐ ω ∂μ, y ∈ S → z ∈ S → ∀ t : ℝ≥0,
      ⟪u y t ω, u z t ω⟫_ℂ = if y = z then 1 else 0 := by
    intro y z
    by_cases hy : y ∈ S
    · by_cases hz : z ∈ S
      · filter_upwards [(hu y hy).inner_eq hB (hu z hz)] with ω hω _ _ t
        rw [hω t, lp.inner_single_left, lp.single_apply, Pi.single_apply, RCLike.inner_apply']
        simp
      · exact ae_of_all _ fun ω _ h => absurd h hz
    · exact ae_of_all _ fun ω h => absurd h hy
  filter_upwards [ae_all_iff.2 fun y => ae_all_iff.2 fun z => h y z] with ω hω t y hy z hz
  exact hω y z hy hz t

/-- **Parseval on a box.** If `(w_y)_{y ∈ Λ_L}` are orthonormal vectors of `ℓ²(ℤ)` supported in
`Λ_L` (`L` finite), then `∑_{y ∈ Λ_L} |⟨w_y, v⟩|² = ∑_{x ∈ Λ_L} |v(x)|²` for every `v ∈ ℓ²(ℤ)`. -/
theorem frame_parseval {L : ℕ} (w : ℤ → ℓ²(ℤ, ℂ))
    (hw : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ x, x ∉ box L → w y x = 0)
    (hon : ∀ y ∈ Finset.Icc (-(L : ℤ)) L, ∀ z ∈ Finset.Icc (-(L : ℤ)) L,
      ⟪w y, w z⟫_ℂ = if y = z then 1 else 0)
    (v : ℓ²(ℤ, ℂ)) :
    ∑ y ∈ Finset.Icc (-(L : ℤ)) L, ‖⟪w y, v⟫_ℂ‖ ^ 2 = ∑ x ∈ Finset.Icc (-(L : ℤ)) L, ‖v x‖ ^ 2 := by
  classical
  set S := Finset.Icc (-(L : ℤ)) L with hSdef
  have : Nonempty S := ⟨⟨0, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩⟩
  have hinner : ∀ f g : ℓ²(ℤ, ℂ), (∀ x, x ∉ box L → f x = 0) →
      ⟪f, g⟫_ℂ = ∑ x : S, conj (f x) * g x := by
    intro f g hf
    rw [pairing_inner_eq_sum f g hf, ← Finset.sum_coe_sort S]
  set e : S → EuclideanSpace ℂ S := fun y => WithLp.toLp 2 (fun x : S => w y x) with hedef
  set v' : EuclideanSpace ℂ S := WithLp.toLp 2 (fun x : S => v x) with hv'
  have he : ∀ y z : S, ⟪e y, e z⟫_ℂ = ⟪w y, w z⟫_ℂ := by
    intro y z
    rw [PiLp.inner_apply, hinner _ _ (hw y y.2)]
    simp [e]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hev : ∀ y : S, ⟪e y, v'⟫_ℂ = ⟪w y, v⟫_ℂ := by
    intro y
    rw [PiLp.inner_apply, hinner _ _ (hw y y.2)]
    simp [e, v']
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hon' : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro y z
    rw [he, hon y y.2 z z.2]
    by_cases h : y = z
    · subst h
      simp
    · have h' : (y : ℤ) ≠ z := fun h' => h (Subtype.ext h')
      simp only [h, h', ↓reduceIte]
  have hcard : Fintype.card S = Module.finrank ℂ (EuclideanSpace ℂ S) :=
    finrank_euclideanSpace.symm
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    have := (basisOfOrthonormalOfCardEqFinrank hon' hcard).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at this
    rw [this]
  have hP := (OrthonormalBasis.mk hon' hspan).sum_sq_norm_inner_right v'
  rw [EuclideanSpace.norm_sq_eq] at hP
  simp only [OrthonormalBasis.coe_mk, hev] at hP
  rw [← Finset.sum_coe_sort S, ← Finset.sum_coe_sort S (fun x => ‖v x‖ ^ 2)]
  simpa [v'] using hP

end QSSEPtoKPZ
