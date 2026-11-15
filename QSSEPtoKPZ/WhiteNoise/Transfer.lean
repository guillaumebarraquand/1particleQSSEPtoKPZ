/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Projection
public import QSSEPtoKPZ.WhiteNoise.TransferFactor
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Transfer of Walsh integrals between white noises (task G6)

Interface file of task I0″ (Stage 4); proved by task G6 (13 November 2026), with the
factorizations of `TransferFactor.lean`.
See `docs/stage4-design.md`, Sections 1.2 (h) and 3.3, and `docs/stage4-interfaces.md`.

A Walsh integral whose integrand and value are measurable functions of the noise coordinates
`noiseMap S₁` on one space gives, through the same functions, a Walsh integral on any other
space carrying a white noise. Proof: `IsWalshIntegral.condExp_noise` on `Ω₁` (the projection
`noiseProj` fixes functions of the noise, `noiseProj_ae_eq_self`), then induction on the derivation for the noise filtration, every node
being factorized through `noiseMap` (Doob–Dynkin, `Measurable.exists_eq_measurable_comp`); the
induction must quantify over **all** factorizations, so that the `add` and `limit` cases
compose; `L²` norms move between the spaces by `IsWhiteNoise.map_noiseMap_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

section TransferAux

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂}
  {S₁ : ℝ → ℝ → Ω₁ → ℝ} {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₁ : Measure Ω₁} {ν₂ : Measure Ω₂}

/-- The law of `(noise, s, y)` under `ν ⊗ Leb²` is the same on both spaces. -/
private lemma transfer_map_eq (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂) :
    (ν₁.prod (volume : Measure (ℝ × ℝ))).map (Prod.map (noiseMap S₁) id) =
      (ν₂.prod (volume : Measure (ℝ × ℝ))).map (Prod.map (noiseMap S₂) id) := by
  rw [← Measure.map_prod_map _ _ h₁.measurable_noiseMap measurable_id,
    ← Measure.map_prod_map _ _ h₂.measurable_noiseMap measurable_id]
  simp only [Measure.map_id, h₁.map_noiseMap_eq h₂]

/-- Almost-everywhere identities between functions of `(noise, s, y)` transfer. -/
private lemma transfer_ae_field (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂)
    {G₁ G₂ : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ} (hG₁ : Measurable G₁) (hG₂ : Measurable G₂)
    (h : (fun p : Ω₁ × ℝ × ℝ => G₁ (noiseMap S₁ p.1, p.2)) =ᵐ[ν₁.prod volume]
      fun p => G₂ (noiseMap S₁ p.1, p.2)) :
    (fun p : Ω₂ × ℝ × ℝ => G₁ (noiseMap S₂ p.1, p.2)) =ᵐ[ν₂.prod volume]
      fun p => G₂ (noiseMap S₂ p.1, p.2) := by
  have hs : MeasurableSet {q | G₁ q = G₂ q} := measurableSet_eq_fun hG₁ hG₂
  have e1 := (ae_map_iff (h₁.measurable_noiseMap.prodMap measurable_id).aemeasurable hs).2 h
  rw [transfer_map_eq h₁ h₂] at e1
  exact (ae_map_iff (h₂.measurable_noiseMap.prodMap measurable_id).aemeasurable hs).1 e1

/-- Almost-sure identities between functions of the noise transfer. -/
private lemma transfer_ae_value (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂)
    {Ξ₁ Ξ₂ : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ} (hΞ₁ : Measurable Ξ₁) (hΞ₂ : Measurable Ξ₂)
    (h : (fun ω => Ξ₁ (noiseMap S₁ ω)) =ᵐ[ν₁] fun ω => Ξ₂ (noiseMap S₁ ω)) :
    (fun ω => Ξ₁ (noiseMap S₂ ω)) =ᵐ[ν₂] fun ω => Ξ₂ (noiseMap S₂ ω) := by
  have hs : MeasurableSet {q | Ξ₁ q = Ξ₂ q} := measurableSet_eq_fun hΞ₁ hΞ₂
  have e1 := (ae_map_iff h₁.measurable_noiseMap.aemeasurable hs).2 h
  rw [h₁.map_noiseMap_eq h₂] at e1
  exact (ae_map_iff h₂.measurable_noiseMap.aemeasurable hs).1 e1

/-- `L²` norms of functions of `(noise, s, y)` are the same on both spaces. -/
private lemma transfer_eLpNorm_field (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁)
    (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂) {G : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ} (hG : Measurable G) :
    eLpNorm (fun p : Ω₁ × ℝ × ℝ => G (noiseMap S₁ p.1, p.2)) 2 (ν₁.prod volume) =
      eLpNorm (fun p : Ω₂ × ℝ × ℝ => G (noiseMap S₂ p.1, p.2)) 2 (ν₂.prod volume) := by
  have e1 := eLpNorm_map_measure (μ := ν₁.prod volume) (p := 2) (g := G) hG.aestronglyMeasurable
    (h₁.measurable_noiseMap.prodMap (measurable_id (α := ℝ × ℝ))).aemeasurable
  have e2 := eLpNorm_map_measure (μ := ν₂.prod volume) (p := 2) (g := G) hG.aestronglyMeasurable
    (h₂.measurable_noiseMap.prodMap (measurable_id (α := ℝ × ℝ))).aemeasurable
  rw [transfer_map_eq h₁ h₂] at e1
  exact e1.symm.trans e2

/-- `L²` norms of functions of the noise are the same on both spaces. -/
private lemma transfer_eLpNorm_value (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁)
    (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂) {Ξ : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ} (hΞ : Measurable Ξ) :
    eLpNorm (fun ω => Ξ (noiseMap S₁ ω)) 2 ν₁ = eLpNorm (fun ω => Ξ (noiseMap S₂ ω)) 2 ν₂ := by
  have e1 := eLpNorm_map_measure (μ := ν₁) (p := 2) (g := Ξ) hΞ.aestronglyMeasurable
    h₁.measurable_noiseMap.aemeasurable
  have e2 := eLpNorm_map_measure (μ := ν₂) (p := 2) (g := Ξ) hΞ.aestronglyMeasurable
    h₂.measurable_noiseMap.aemeasurable
  rw [h₁.map_noiseMap_eq h₂] at e1
  exact e1.symm.trans e2

/-- **Transfer, induction on the derivation for the noise filtration.** The statement is
quantified over all factorizations `h = H(N₁, s, y)`, `X = Ξ(N₁)`. -/
private theorem transfer_aux (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂)
    {h : ℝ → ℝ → Ω₁ → ℝ} {X : Ω₁ → ℝ}
    (hX : IsWalshIntegral (noiseFiltration S₁ ν₁) S₁ ν₁ h X) :
    ∀ (H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ) (Ξ : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ),
      Measurable (fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2) → Measurable Ξ →
      uncurryField h =ᵐ[ν₁.prod volume] (fun p => H (noiseMap S₁ p.1) p.2.1 p.2.2) →
      X =ᵐ[ν₁] (fun ω => Ξ (noiseMap S₁ ω)) →
      IsWalshIntegral 𝓖₂ S₂ ν₂ (fun s y ω => H (noiseMap S₂ ω) s y)
        (fun ω => Ξ (noiseMap S₂ ω)) := by
  have : IsProbabilityMeasure ν₁ := h₁.isProbabilityMeasure
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    intro H Ξ hH hΞ hh hXe
    obtain ⟨K, hK⟩ := hbdd
    have hcm : Measurable c := hc.mono ((noiseFiltration S₁ ν₁).le s) le_rfl
    have hci : Integrable c ν₁ :=
      Integrable.of_bound hcm.aestronglyMeasurable K (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hK ω)
    obtain ⟨c₀, hc₀, hcc₀⟩ := h₁.exists_noisePath_factor hc hci
    let c₁ : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ := fun w => max (-K) (min K (c₀ w))
    have hc₁ : Measurable[noisePathSigma s] c₁ := measurable_const.max (measurable_const.min hc₀)
    have hc₁m : Measurable c₁ := hc₁.mono (noisePathSigma_le s) le_rfl
    have hcc₁ : c =ᵐ[ν₁] fun ω => c₁ (noiseMap S₁ ω) := by
      filter_upwards [hcc₀] with ω hω
      have := abs_le.1 (hK ω)
      simp only [c₁, ← hω]
      rw [min_eq_right this.2, max_eq_right this.1]
    have hc₁b : ∃ C : ℝ, ∀ ω, |c₁ (noiseMap S₂ ω)| ≤ C := ⟨|K|, fun ω => by
      simp only [c₁, abs_le]
      constructor
      · exact (neg_le_neg (le_abs_self K)).trans (le_max_left _ _)
      · exact max_le (by linarith [neg_abs_le K, le_abs_self K])
          ((min_le_left _ _).trans (le_abs_self K))⟩
    have hN₂ : Measurable[𝓖₂ s, noisePathSigma s] (noiseMap S₂) :=
      measurable_iff_comap_le.2 (h₂.noiseMap_comap_pathSigma_le s)
    have hblock := IsWalshIntegral.block (𝓖 := 𝓖₂) (S := S₂) (ν := ν₂) s t a b
      (fun ω => c₁ (noiseMap S₂ ω)) hst hab (hc₁.comp hN₂) hc₁b
    refine hblock.congr_ae h₂ ?_ ?_
    · let G : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ → ℝ := fun q =>
        if (s : ℝ) < q.2.1 ∧ q.2.1 ≤ t ∧ a < q.2.2 ∧ q.2.2 ≤ b then c₁ q.1 else 0
      have hR : MeasurableSet {q : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ |
          (s : ℝ) < q.2.1 ∧ q.2.1 ≤ t ∧ a < q.2.2 ∧ q.2.2 ≤ b} :=
        (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
          ((measurableSet_le (measurable_fst.comp measurable_snd) measurable_const).inter
          ((measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const)))
      have hG : Measurable G := Measurable.ite hR (hc₁m.comp measurable_fst) measurable_const
      refine transfer_ae_field h₁ h₂ hG hH ?_
      refine EventuallyEq.trans ?_ hh
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcc₁] with p hp
      simp only [uncurryField, G]
      split_ifs
      · exact hp.symm
      · rfl
    · let r : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ := fun w => w (t, a, b) - w (s, a, b)
      have hr : Measurable r := (measurable_pi_apply _).sub (measurable_pi_apply _)
      have hrect₁ : ∀ ω, rectMass S₁ s t a b ω = r (noiseMap S₁ ω) := fun ω => by
        simp only [r, noiseMap, rectMass]
        ring
      have hrect₂ : ∀ ω, rectMass S₂ s t a b ω = r (noiseMap S₂ ω) := fun ω => by
        simp only [r, noiseMap, rectMass]
        ring
      simp only [hrect₂]
      refine transfer_ae_value h₁ h₂ (Ξ₁ := fun w => c₁ w * r w) (hc₁m.mul hr) hΞ ?_
      refine EventuallyEq.trans ?_ hXe
      filter_upwards [hcc₁] with ω hω
      simp only [← hrect₁, hω]
  | add h h' X X' hX hX' ih ih' =>
    intro H Ξ hH hΞ hh hXe
    obtain ⟨H₁, Ξ₁, hH₁, hΞ₁, e₁, f₁⟩ := h₁.exists_noiseMap_factor hX
    obtain ⟨H₂, Ξ₂, hH₂, hΞ₂, e₂, f₂⟩ := h₁.exists_noiseMap_factor hX'
    have hsum := IsWalshIntegral.add _ _ _ _ (ih H₁ Ξ₁ hH₁ hΞ₁ e₁ f₁) (ih' H₂ Ξ₂ hH₂ hΞ₂ e₂ f₂)
    refine hsum.congr_ae h₂ ?_ ?_
    · refine transfer_ae_field h₁ h₂ (G₁ := fun q => H₁ q.1 q.2.1 q.2.2 + H₂ q.1 q.2.1 q.2.2)
        (hH₁.add hH₂) hH ?_
      filter_upwards [e₁, e₂, hh] with p a1 a2 a3
      simp only [uncurryField] at a1 a2 a3 ⊢
      rw [← a1, ← a2, a3]
    · refine transfer_ae_value h₁ h₂ (Ξ₁ := fun w => Ξ₁ w + Ξ₂ w) (hΞ₁.add hΞ₂) hΞ ?_
      filter_upwards [f₁, f₂, hXe] with ω a1 a2 a3
      rw [← a1, ← a2, ← a3]
  | limit h X hs Xs hXs hh hX hhs hXs' ih =>
    intro H Ξ hH hΞ hhe hXe
    choose Hk Ξk hHk hΞk ek fk using fun k => h₁.exists_noiseMap_factor (hXs k)
    refine IsWalshIntegral.limit _ _ (fun k s y ω => Hk k (noiseMap S₂ ω) s y)
      (fun k ω => Ξk k (noiseMap S₂ ω)) (fun k => ih k _ _ (hHk k) (hΞk k) (ek k) (fk k))
      ?_ ?_ ?_ ?_
    · rw [memLp_iff] at hh ⊢
      have := transfer_eLpNorm_field h₁ h₂ hH
      rw [← eLpNorm_congr_ae hhe] at this
      exact this ▸ hh
    · rw [memLp_iff] at hX ⊢
      have := transfer_eLpNorm_value h₁ h₂ hΞ
      rw [← eLpNorm_congr_ae hXe] at this
      exact this ▸ hX
    · refine hhs.congr fun k => ?_
      have := transfer_eLpNorm_field h₁ h₂
        (G := fun q => Hk k q.1 q.2.1 q.2.2 - H q.1 q.2.1 q.2.2) ((hHk k).sub hH)
      exact (eLpNorm_congr_ae ((ek k).sub hhe)).trans this
    · refine hXs'.congr fun k => ?_
      have := transfer_eLpNorm_value h₁ h₂ (Ξ := fun w => Ξk k w - Ξ w) ((hΞk k).sub hΞ)
      exact (eLpNorm_congr_ae ((fk k).sub hXe)).trans this

end TransferAux

/-- **Transfer of Walsh integrals between white noises.** -/
theorem IsWalshIntegral.transfer {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂}
    {S₁ : ℝ → ℝ → Ω₁ → ℝ} {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₁ : Measure Ω₁} {ν₂ : Measure Ω₂}
    (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂)
    {H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ} {Ξ : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ}
    (hH : Measurable fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2)
    (hΞ : Measurable Ξ)
    (hW : IsWalshIntegral 𝓖₁ S₁ ν₁ (fun s y ω => H (noiseMap S₁ ω) s y)
      (fun ω => Ξ (noiseMap S₁ ω))) :
    IsWalshIntegral 𝓖₂ S₂ ν₂ (fun s y ω => H (noiseMap S₂ ω) s y)
      (fun ω => Ξ (noiseMap S₂ ω)) := by
  have : IsProbabilityMeasure ν₁ := h₁.isProbabilityMeasure
  have hc := IsWalshIntegral.condExp_noise h₁ hW
  have hiso := IsWalshIntegral.isometry_lib h₁ hW
  have hNm : Measurable[⨆ t, noiseFiltration S₁ ν₁ t] (noiseMap S₁) :=
    measurable_iff_comap_le.2 h₁.noiseMap_comap_le_iSup
  have hpm : Measurable[noiseProdSigma S₁ ν₁, inferInstance]
      (Prod.map (noiseMap S₁) (id : ℝ × ℝ → ℝ × ℝ)) := by
    rw [noiseProdSigma_eq, measurable_iff_comap_le]
    change MeasurableSpace.comap _ (MeasurableSpace.prod MeasurableSpace.pi inferInstance) ≤ _
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
    exact sup_le_sup (MeasurableSpace.comap_mono (measurable_iff_comap_le.1 hNm)) le_rfl
  have hfm : AEStronglyMeasurable[noiseProdSigma S₁ ν₁]
      (uncurryField fun s y ω => H (noiseMap S₁ ω) s y) (ν₁.prod volume) :=
    (hH.comp hpm).stronglyMeasurable.aestronglyMeasurable
  have e1 := noiseProj_ae_eq_self S₁ hiso.1 hfm
  have hXm : StronglyMeasurable[⨆ t, noiseFiltration S₁ ν₁ t] (fun ω => Ξ (noiseMap S₁ ω)) :=
    (hΞ.comp hNm).stronglyMeasurable
  rw [condExp_of_stronglyMeasurable (noiseProj_iSup_le S₁ ν₁) hXm
    (hiso.2.1.integrable one_le_two)] at hc
  have hN := isWalshIntegral_noiseSheet_iff.1
    ((isWalshIntegral_noiseSheet_iff.2 hc).congr_ae h₁.noiseSheet e1 (ae_eq_refl _))
  exact transfer_aux h₁ h₂ hN H Ξ hH hΞ (ae_eq_refl _) (ae_eq_refl _)

end QSSEPtoKPZ
