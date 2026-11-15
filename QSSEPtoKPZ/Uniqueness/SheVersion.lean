/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Uniqueness.NoiseFunctional
public import QSSEPtoKPZ.Uniqueness.StochFubini
public import QSSEPtoKPZ.LimitPoints.PathSpace
public import QSSEPtoKPZ.Uniqueness.SheVersionAux

/-!
# The law of the limit is the law of the solution of the SHE (task K5)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task K5.
See `docs/stage4-design.md`, Section 1.2 (h) (third item), decisions D2″ and D4″, and
`docs/stage4-interfaces.md`.

On a space `Ω₁` carrying a white noise, let `Y` be a random path in `C([0,T], ℳ₊)` with a tight
law, `Y(0) = δ₀`, and a nonnegative density `Z₁ ∈ ℋ_T` solving (7.13). Then on any space `Ω'`
carrying a solution `Z` of (1.13), the measures `𝒵(t) = sheMeasure Z t` (`δ₀` at `t = 0`,
`max(Z(t,x),0) dx` otherwise) form, almost surely, a continuous path with the law of `Y`, and
`Z ≥ 0` on `(0,T] × ℝ` almost surely. Proof without Lusin–Souslin: the map
`ι(γ) = (γ(t)(f_j))_{t ∈ D, j}` (countable dense `D` of good times, Stage 3 bumps `f_j`) is
continuous and injective, and a homeomorphism on each compact set; the law of `Y` charges a
σ-compact set; `IsWeakMild.exists_noise_functional` makes `(∫ Z(t,x) f_j(x) dx)_{t,j}` on `Ω'`
and `ι(Y)` on `Ω₁` the same function of the noise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The test integral `∫ H(w,t,x) f_j(x) dx` of a noise functional `H`. -/
def sheVerFun (H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ) (j : ℕ) (w : ℝ≥0 × ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, H w t x * bumpTestRaw j x

/-- `(w, t) ↦ ∫ H(w,t,x) f_j(x) dx` is measurable. -/
theorem measurable_sheVerFun {H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hH : Measurable fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2) (j : ℕ) :
    Measurable fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ => sheVerFun H j p.1 p.2 := by
  have hF : Measurable fun q : ((ℝ≥0 × ℝ × ℝ → ℝ) × ℝ) × ℝ =>
      H q.1.1 q.1.2 q.2 * bumpTestRaw j q.2 :=
    (hH.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).mul
      ((continuous_bumpTestRaw j).measurable.comp measurable_snd)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

/-- From `Z = H(N)` almost everywhere on `Ω × [0,T] × ℝ`: almost surely, for almost every `t`,
the bump integrals of `Z(t,·)` and `H(N,t,·)` agree. -/
private lemma sheVer_ae_ae_integral {Ω₂ W : Type*} {m₂ : MeasurableSpace Ω₂} [MeasurableSpace W]
    {ν₂ : Measure Ω₂} {N₂ : Ω₂ → W} {Z₂ : ℝ → ℝ → Ω₂ → ℝ} {H : W → ℝ → ℝ → ℝ} {T : ℝ}
    (hZH : ∀ᵐ p ∂(ν₂.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
      Z₂ p.2.1 p.2.2 p.1 = H (N₂ p.1) p.2.1 p.2.2) :
    ∀ᵐ ω ∂ν₂, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ j,
      (∫ x, Z₂ t x ω * bumpTestRaw j x) = ∫ x, H (N₂ ω) t x * bumpTestRaw j x := by
  filter_upwards [Measure.ae_ae_of_ae_prod hZH] with ω hω
  filter_upwards [Measure.ae_ae_of_ae_prod hω] with t ht j
  exact integral_congr_ae (ht.mono fun x hx => by simp only [hx])

/-- **The SHE side of the end of Section 7.** -/
theorem exists_sheVersion_map_eq {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₁] {𝓖₁ : Filtration ℝ≥0 m₁} {S₁ : ℝ → ℝ → Ω₁ → ℝ}
    (hS₁ : IsWhiteNoise 𝓖₁ S₁ P₁) {T : ℝ} (hT : 0 < T)
    {Y : Ω₁ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ K : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), IsCompact K ∧
      P₁ (Y ⁻¹' Kᶜ) ≤ ENNReal.ofReal ε)
    (hY0 : ∀ᵐ ω ∂P₁, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0)
    {Z₁ : ℝ → ℝ → Ω₁ → ℝ} (hZ₁ : IsWeakMild T 𝓖₁ S₁ Z₁ P₁) (hZ₁0 : ∀ t x ω, 0 ≤ Z₁ t x ω)
    (hdens : ∀ᵐ ω ∂P₁, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z₁ t x ω))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {𝓖 : Filtration ℝ≥0 mΩ'} {S : ℝ → ℝ → Ω' → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {Z : ℝ → ℝ → Ω' → ℝ} (hZ : IsMildSolution 𝓖 S Z ν) :
    ∃ 𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable 𝒵 ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      ν.map 𝒵 = P₁.map Y ∧
      ∀ᵐ ω ∂ν, ∀ t x : ℝ, 0 < t → t ≤ T → 0 ≤ Z t x ω := by
  classical
  have hN₁ : Measurable (noiseMap S₁) := hS₁.measurable_noiseMap
  have hN' : Measurable (noiseMap S) := hS.measurable_noiseMap
  -- the jointly measurable version `Z'` of `Z`, solving (7.13) (K3)
  obtain ⟨Z', hZ'Z, hZ'w, -⟩ := heatMild_isWeakMild hS hZ hT
  -- the noise functional `H` (K4): `Z₁ = H(N₁)` on `Ω₁`, `Z' = H(N')` on `Ω'`
  obtain ⟨H, hHm, hH1, hH2⟩ : ∃ H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ,
      Measurable (fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2) ∧
      (∀ᵐ p ∂(P₁.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
        Z₁ p.2.1 p.2.2 p.1 = H (noiseMap S₁ p.1) p.2.1 p.2.2) ∧
      (∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
        Z' p.2.1 p.2.2 p.1 = H (noiseMap S p.1) p.2.1 p.2.2) :=
    (hZ₁.exists_noise_functional hT hS₁).imp fun H h => ⟨h.1, h.2.1, h.2.2 hS hZ'w⟩
  have hΦ := measurable_sheVerFun hHm
  have hpair : ∀ j, Measurable fun q : Ω₁ × ℝ => pairFM (pathAt (Y q.1) q.2) (bumpTestRaw j) :=
    fun j => ((continuous_pairFM (continuous_bumpTestRaw j) ⟨1, abs_bumpTestRaw_le j⟩).comp
      continuous_pathAt_prod).measurable.comp ((hY.comp measurable_fst).prodMk measurable_snd)
  -- good times on `Ω₁`: `Y(t)(f_j) = ∫ H(N₁,t,x) f_j(x) dx` almost surely
  have hgood1 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P₁, ∀ j,
      pairFM (pathAt (Y ω) t) (bumpTestRaw j) = sheVerFun H j (noiseMap S₁ ω) t := by
    have hE : MeasurableSet {q : Ω₁ × ℝ | ∀ j, pairFM (pathAt (Y q.1) q.2) (bumpTestRaw j) =
        sheVerFun H j (noiseMap S₁ q.1) q.2} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_eq_fun (hpair j)
        ((hΦ j).comp ((hN₁.comp measurable_fst).prodMk measurable_snd))
    refine (Measure.ae_ae_comm (p := fun ω t => ∀ j, pairFM (pathAt (Y ω) t) (bumpTestRaw j) =
      sheVerFun H j (noiseMap S₁ ω) t) hE).1 ?_
    filter_upwards [hdens, sheVer_ae_ae_integral hH1] with ω h1 h2
    filter_upwards [h1, h2] with t ht1 ht2 j
    have hm : Measurable fun x => Z₁ t x ω :=
      hZ₁.measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [pairFM, ht1, sheVer_integral_withDensity hm (fun x => hZ₁0 t x ω), ht2 j]
    rfl
  -- good times on `Ω'`: `∫ Z'(t,x) f_j(x) dx = ∫ H(N',t,x) f_j(x) dx` almost surely
  have hgood2 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂ν, ∀ j,
      (∫ x, Z' t x ω * bumpTestRaw j x) = sheVerFun H j (noiseMap S ω) t := by
    have hZm : ∀ j, Measurable fun q : Ω' × ℝ => ∫ x, Z' q.2 x q.1 * bumpTestRaw j x := by
      intro j
      have hF : Measurable fun q : (Ω' × ℝ) × ℝ => Z' q.1.2 q.2 q.1.1 * bumpTestRaw j q.2 :=
        (hZ'w.measurable.comp (measurable_fst.fst.prodMk
          (measurable_fst.snd.prodMk measurable_snd))).mul
          ((continuous_bumpTestRaw j).measurable.comp measurable_snd)
      exact hF.stronglyMeasurable.integral_prod_right'.measurable
    have hE : MeasurableSet {q : Ω' × ℝ | ∀ j, (∫ x, Z' q.2 x q.1 * bumpTestRaw j x) =
        sheVerFun H j (noiseMap S q.1) q.2} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_eq_fun (hZm j)
        ((hΦ j).comp ((hN'.comp measurable_fst).prodMk measurable_snd))
    refine (Measure.ae_ae_comm (p := fun ω t => ∀ j, (∫ x, Z' t x ω * bumpTestRaw j x) =
      sheVerFun H j (noiseMap S ω) t) hE).1 ?_
    exact sheVer_ae_ae_integral hH2
  -- a countable dense set `D ⊆ (0,T]` of good times
  obtain ⟨D, hDA, hDT, hDc, hDcl⟩ := sheVer_exists_dense hT
    (A := {t | (∀ᵐ ω ∂P₁, ∀ j, pairFM (pathAt (Y ω) t) (bumpTestRaw j) =
        sheVerFun H j (noiseMap S₁ ω) t) ∧
      ∀ᵐ ω ∂ν, ∀ j, (∫ x, Z' t x ω * bumpTestRaw j x) = sheVerFun H j (noiseMap S ω) t})
    (ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self (hgood1.and hgood2))
  have : Countable D := hDc.to_subtype
  -- the embedding `ι`, compact sets of the tight law, the measurable inverse `G`
  have hιc : Continuous (sheVerEmb (T := T) D) := continuous_sheVerEmb D
  have hιi : Function.Injective (sheVerEmb (T := T) D) := sheVerEmb_injective hDcl
  choose K hKc hKP using fun m : ℕ => htight (1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨G, hGm, hBm, hGι⟩ := sheVer_exists_measurable_inv hιc hιi hKc
  let Φv : (ℝ≥0 × ℝ × ℝ → ℝ) → (D → ℕ → ℝ) := fun w d j => sheVerFun H j w d
  have hΦv : Measurable Φv := measurable_pi_iff.2 fun d => measurable_pi_iff.2 fun j =>
    (hΦ j).comp (measurable_id.prodMk measurable_const)
  let 𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) := fun ω => G (Φv (noiseMap S ω))
  have h𝒵m : Measurable 𝒵 := hGm.comp (hΦv.comp hN')
  -- on `Ω₁`: `Y ∈ ⋃ K_m` and `Φ(N₁) = ι(Y)` almost surely
  have hF1 : ∀ᵐ ω ∂P₁, Y ω ∈ ⋃ m, K m := by
    rw [ae_iff]
    have ht := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [ENNReal.ofReal_zero] at ht
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto' ht fun m => ?_)
    exact (measure_mono (s := {a | Y a ∉ ⋃ m, K m}) (t := Y ⁻¹' (K m)ᶜ)
      fun ω hω hm => hω (Set.mem_iUnion.2 ⟨m, hm⟩)).trans (hKP m)
  have hF2 : ∀ᵐ ω ∂P₁, Φv (noiseMap S₁ ω) = sheVerEmb D (Y ω) := by
    filter_upwards [ae_all_iff.2 fun d : D => (hDA d.2).1] with ω hω
    funext d j
    exact (hω d j).symm
  have hF12 : ∀ᵐ ω ∂P₁, Φv (noiseMap S₁ ω) ∈ ⋃ m, sheVerEmb D '' K m := by
    filter_upwards [hF1, hF2] with ω h1 h2
    rw [h2]
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h1
    exact Set.mem_iUnion.2 ⟨m, Set.mem_image_of_mem _ hm⟩
  have hF3 : ∀ᵐ ω ∂P₁, G (Φv (noiseMap S₁ ω)) = Y ω := by
    filter_upwards [hF12, hF2] with ω h1 h2
    have := hGι _ h1
    rw [h2] at this ⊢
    exact hιi this
  -- the law
  have hmap : ν.map 𝒵 = P₁.map Y := by
    have e1 : ν.map 𝒵 = (ν.map (noiseMap S)).map (G ∘ Φv) :=
      (Measure.map_map (hGm.comp hΦv) hN').symm
    have e2 : P₁.map (fun ω => G (Φv (noiseMap S₁ ω))) = (P₁.map (noiseMap S₁)).map (G ∘ Φv) :=
      (Measure.map_map (hGm.comp hΦv) hN₁).symm
    rw [e1, hS.map_noiseMap_eq hS₁, ← e2]
    exact Measure.map_congr hF3
  -- on `Ω'`: `Φ(N') ∈ ⋃ ι(K_m)` almost surely
  have hF4 : ∀ᵐ ω ∂ν, Φv (noiseMap S ω) ∈ ⋃ m, sheVerEmb D '' K m := by
    have h2 : ∀ᵐ y ∂(P₁.map (Φv ∘ noiseMap S₁)), y ∈ ⋃ m, sheVerEmb D '' K m :=
      (ae_map_iff (hΦv.comp hN₁).aemeasurable hBm).2 hF12
    have h3 : ν.map (Φv ∘ noiseMap S) = P₁.map (Φv ∘ noiseMap S₁) := by
      rw [← Measure.map_map hΦv hN', ← Measure.map_map hΦv hN₁, hS.map_noiseMap_eq hS₁]
    rw [← h3] at h2
    exact ae_of_ae_map (hΦv.comp hN').aemeasurable h2
  have hF5 : ∀ᵐ ω ∂ν, ∀ d : D, ∀ j,
      (∫ x, Z' d x ω * bumpTestRaw j x) = sheVerFun H j (noiseMap S ω) d :=
    ae_all_iff.2 fun d => (hDA d.2).2
  -- `𝒵(0) = δ₀` by the law
  let δ0 : FiniteMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
  have hS0 : MeasurableSet {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) | pathAt γ 0 = δ0} :=
    (isClosed_eq (continuous_pathAt_prod.comp (continuous_id.prodMk continuous_const))
      continuous_const).measurableSet
  have hF7 : ∀ᵐ ω ∂ν, pathAt (𝒵 ω) 0 = δ0 := by
    have h1 : ∀ᵐ γ ∂(P₁.map Y), pathAt γ 0 = δ0 :=
      (ae_map_iff hY.aemeasurable hS0).2 (hY0.mono fun ω h => FiniteMeasure.toMeasure_injective h)
    rw [← hmap] at h1
    exact ae_of_ae_map h𝒵m.aemeasurable h1
  -- pathwise identification on `(0,T]`, positivity from the bumps
  have hmain : ∀ᵐ ω ∂ν, ∀ t ∈ Set.Ioc (0 : ℝ) T, (∀ x, 0 ≤ Z t x ω) ∧
      (pathAt (𝒵 ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z t x ω) := by
    filter_upwards [hF4, hF5, hZ'Z, hZ.continuous] with ω h4 h5 h6 h7 t ht
    have hιω : sheVerEmb D (𝒵 ω) = Φv (noiseMap S ω) := hGι _ h4
    have hgc : Continuous fun x => Z t x ω :=
      h7.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht.1, trivial⟩
    refine sheVer_eq_withDensity_of_bump hgc fun j hj => ?_
    have hEq : Set.EqOn (fun s => pairFM (pathAt (𝒵 ω) s) (bumpTestRaw j))
        (fun s => ∫ x, Z s x ω * bumpTestRaw j x) D := by
      intro d hd
      calc pairFM (pathAt (𝒵 ω) d) (bumpTestRaw j) = Φv (noiseMap S ω) ⟨d, hd⟩ j := by
            rw [← hιω]; rfl
        _ = ∫ x, Z' d x ω * bumpTestRaw j x := (h5 ⟨d, hd⟩ j).symm
        _ = ∫ x, Z d x ω * bumpTestRaw j x :=
            integral_congr_ae (ae_of_all _ fun x => by simp only [h6 d x (hDT hd).1])
    have hc1 : Continuous fun s => pairFM (pathAt (𝒵 ω) s) (bumpTestRaw j) :=
      (continuous_pairFM (continuous_bumpTestRaw j) ⟨1, abs_bumpTestRaw_le j⟩).comp
        (continuous_pathAt_prod.comp (continuous_const.prodMk continuous_id))
    have hc2 := (sheVer_continuousOn_integral (g := fun s x => Z s x ω) h7 hj).mono
      (fun s hs => hs.1 : Set.Ioc (0 : ℝ) T ⊆ Set.Ioi 0)
    exact hEq.of_subset_closure hc1.continuousOn hc2 hDT (Set.Ioc_subset_Icc_self.trans hDcl) ht
  refine ⟨𝒵, h𝒵m, ?_, hmap, ?_⟩
  · filter_upwards [hmain, hF7] with ω h1 h2 t
    obtain ⟨t, ht⟩ := t
    rw [← pathAt_of_mem _ ht]
    by_cases h0 : t = 0
    · subst h0
      rw [h2]
      simp [sheMeasure, δ0]
    · have ht' : t ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
      simp only [sheMeasure, h0, ↓reduceIte]
      exact (h1 t ht').2
  · filter_upwards [hmain] with ω h t x ht0 htT
    exact (h t ⟨ht0, htT⟩).1 x

end QSSEPtoKPZ
