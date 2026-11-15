/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import Mathlib.Probability.Process.Predictable

/-!
# Existence of the Itô–Walsh integral for predictable integrands (task G4b)

INTERFACE FILE (task I0″ of Stage 4): the statement below is an interface, proved by task G4b.
See `docs/stage4-design.md`, Section 3.3, and `docs/stage4-interfaces.md`.

Every square-integrable field which is measurable for the predictable σ-algebra (times the
Borel σ-algebra in space) has a Walsh integral. Proof: the fields with a Walsh integral are
closed under sums, scalar multiples, `L²` limits (`IsWalshIntegral.exists_limit`) and
almost-everywhere modifications. A Dynkin argument (`MeasurableSpace.induction_on_inter`, from
the rectangles `((i, ∞) × A) × (l, u]`, which give blocks) shows that the indicator of every
`𝒫 ⊗ 𝓑(ℝ)`-set, cut to a box `(0,n] × (-n,n]`, has a Walsh integral; letting `n → ∞` and using
the density of simple functions (`MemLp.induction`, for the σ-algebra `𝒫 ⊗ 𝓑(ℝ)` pulled back to
`Ω × ℝ × ℝ` and the trimmed measure) concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-! ### Fields with a Walsh integral -/

/-- The fields `f` on `Ω × ℝ × ℝ` (`f (ω, s, y) = h(s, y, ω)`) that have a Walsh integral. -/
private def WalshIntegrable (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω)
    (f : Ω × ℝ × ℝ → ℝ) : Prop :=
  ∃ X : Ω → ℝ, IsWalshIntegral 𝓖 S ν (fun s y ω => f (ω, s, y)) X

private lemma walshInt_zero : WalshIntegrable 𝓖 S ν 0 :=
  ⟨_, IsWalshIntegral.zero 𝓖 S ν⟩

private lemma walshInt_add {f g : Ω × ℝ × ℝ → ℝ} (hf : WalshIntegrable 𝓖 S ν f)
    (hg : WalshIntegrable 𝓖 S ν g) : WalshIntegrable 𝓖 S ν (f + g) := by
  obtain ⟨X, hX⟩ := hf
  obtain ⟨X', hX'⟩ := hg
  exact ⟨_, IsWalshIntegral.add _ _ _ _ hX hX'⟩

private lemma walshInt_const_mul {f : Ω × ℝ × ℝ → ℝ} (hf : WalshIntegrable 𝓖 S ν f) (c : ℝ) :
    WalshIntegrable 𝓖 S ν (fun p => c * f p) := by
  obtain ⟨X, hX⟩ := hf
  exact ⟨_, hX.const_mul c⟩

private lemma walshInt_sub {f g : Ω × ℝ × ℝ → ℝ} (hf : WalshIntegrable 𝓖 S ν f)
    (hg : WalshIntegrable 𝓖 S ν g) : WalshIntegrable 𝓖 S ν (f - g) := by
  obtain ⟨X, hX⟩ := hf
  obtain ⟨X', hX'⟩ := hg
  exact ⟨_, hX.sub hX'⟩

/-- Closure under `L²` limits (`IsWalshIntegral.exists_limit`). -/
private lemma walshInt_of_tendsto (hS : IsWhiteNoise 𝓖 S ν) {fs : ℕ → Ω × ℝ × ℝ → ℝ}
    {f : Ω × ℝ × ℝ → ℝ} (hfs : ∀ k, WalshIntegrable 𝓖 S ν (fs k))
    (hf : MemLp f 2 (ν.prod volume))
    (hlim : Tendsto (fun k => eLpNorm (fs k - f) 2 (ν.prod volume)) atTop (𝓝 0)) :
    WalshIntegrable 𝓖 S ν f := by
  choose Xs hXs using hfs
  obtain ⟨X, hX, -⟩ := IsWalshIntegral.exists_limit hS (h := fun s y ω => f (ω, s, y)) hXs hf hlim
  exact ⟨X, hX⟩

/-- Closure under almost-everywhere modification (`IsWalshIntegral.congr_ae`). -/
private lemma walshInt_congr_ae (hS : IsWhiteNoise 𝓖 S ν) {f g : Ω × ℝ × ℝ → ℝ}
    (hf : WalshIntegrable 𝓖 S ν f) (hfg : f =ᵐ[ν.prod volume] g) : WalshIntegrable 𝓖 S ν g := by
  obtain ⟨X, hX⟩ := hf
  exact ⟨X, hX.congr_ae hS hfg EventuallyEq.rfl⟩

/-- A rectangle `c 𝟙_{(i,t] × (a,b]}` with `c` bounded and `𝓖_i`-measurable (possibly empty). -/
private lemma walshInt_rect (i t : ℝ≥0) (a b : ℝ) {c : Ω → ℝ} (hc : Measurable[𝓖 i] c)
    (hbdd : ∃ C : ℝ, ∀ ω, |c ω| ≤ C) :
    WalshIntegrable 𝓖 S ν
      (fun p => if (i : ℝ) < p.2.1 ∧ p.2.1 ≤ t ∧ a < p.2.2 ∧ p.2.2 ≤ b then c p.1 else 0) := by
  by_cases hit : i ≤ t ∧ a ≤ b
  · exact ⟨_, IsWalshIntegral.block i t a b c hit.1 hit.2 hc hbdd⟩
  · convert (walshInt_zero : WalshIntegrable 𝓖 S ν 0) using 1
    funext p
    split_ifs with hp
    · obtain ⟨h1, h2, h3, h4⟩ := hp
      exact absurd ⟨by exact_mod_cast h1.le.trans h2, h3.le.trans h4⟩ hit
    · rfl

/-- Indicators of increasing unions: if `Tₖ ↑ U`, `U` of finite measure, and every `c 𝟙_{Tₖ}`
has a Walsh integral, then so does `c 𝟙_U`. -/
private lemma walshInt_indicator_iUnion (hS : IsWhiteNoise 𝓖 S ν) {T : ℕ → Set (Ω × ℝ × ℝ)}
    {U : Set (Ω × ℝ × ℝ)} (hmono : Monotone T) (hU : ⋃ k, T k = U)
    (hTm : ∀ k, MeasurableSet (T k)) (hUfin : ν.prod volume U < ∞) (c : ℝ)
    (hT : ∀ k, WalshIntegrable 𝓖 S ν ((T k).indicator fun _ => c)) :
    WalshIntegrable 𝓖 S ν (U.indicator fun _ => c) := by
  have hUm : MeasurableSet U := hU ▸ MeasurableSet.iUnion hTm
  have hsub : ∀ k, T k ⊆ U := fun k => hU ▸ Set.subset_iUnion T k
  refine walshInt_of_tendsto hS hT (memLp_indicator_const 2 hUm.nullMeasurableSet c
    (Or.inr hUfin.ne)) ?_
  have e : ∀ k, (T k).indicator (fun _ => c) - U.indicator (fun _ => c) =
      -((U \ T k).indicator fun _ => c) := by
    intro k
    rw [Set.indicator_sdiff (hsub k), neg_sub]
  simp_rw [e, eLpNorm_neg]
  have hmeas : Tendsto (fun k => ν.prod volume (U \ T k)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν.prod volume) (s := fun k => U \ T k)
      (fun k => (hUm.diff (hTm k)).nullMeasurableSet)
      (fun k l hkl => Set.sdiff_subset_sdiff_right (hmono hkl))
      ⟨0, (measure_mono Set.sdiff_subset).trans_lt hUfin |>.ne⟩
    have h0 : (⋂ k, U \ T k) = ∅ := by
      rw [← Set.sdiff_iUnion, hU, Set.sdiff_self]
    rwa [h0, measure_empty] at h
  have hr : Tendsto (fun k => ν.prod volume (U \ T k) ^ (1 / (2 : ℝ≥0∞).toReal)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp hmeas
    rwa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num)] at this
  simp_rw [eLpNorm_indicator_const ((hUm.diff (hTm _)).nullMeasurableSet) two_ne_zero
    ENNReal.ofNat_ne_top]
  rw [show (0 : ℝ≥0∞) = ‖c‖ₑ * 0 by simp]
  exact ENNReal.Tendsto.const_mul hr (Or.inr enorm_ne_top)

/-! ### Predictable sets -/

/-- The map `(ω, s, y) ↦ ((s⁺, ω), y)` from `Ω × ℝ × ℝ` to `(ℝ≥0 × Ω) × ℝ`. -/
private def walshPredMap (p : Ω × ℝ × ℝ) : (ℝ≥0 × Ω) × ℝ := ((p.2.1.toNNReal, p.1), p.2.2)

/-- The box `(0, n] × (-n, n]` in the variables `(s, y)`. -/
private def walshBox (n : ℕ) : Set (Ω × ℝ × ℝ) :=
  {p | 0 < p.2.1 ∧ p.2.1 ≤ n ∧ -(n : ℝ) < p.2.2 ∧ p.2.2 ≤ n}

private lemma walsh_predictable_le :
    𝓖.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact (measurableSet_singleton _).prod (𝓖.le _ _ hA)
  · exact measurableSet_Ioi.prod (𝓖.le _ _ hA)

private lemma measurable_walshPredMap :
    Measurable[inferInstance, (𝓖.predictable).prod (borel ℝ)] (walshPredMap (Ω := Ω)) := by
  have h : Measurable (walshPredMap (Ω := Ω)) := by
    unfold walshPredMap
    fun_prop
  refine h.mono le_rfl ?_
  exact sup_le_sup (MeasurableSpace.comap_mono walsh_predictable_le)
    (MeasurableSpace.comap_mono BorelSpace.measurable_eq.ge)

private lemma measurableSet_walshBox (n : ℕ) : MeasurableSet (walshBox (Ω := Ω) n) := by
  unfold walshBox
  measurability

private lemma measure_walshBox_lt_top [IsProbabilityMeasure ν] (n : ℕ) :
    ν.prod volume (walshBox (Ω := Ω) n) < ∞ := by
  have e : walshBox (Ω := Ω) n = Set.univ ×ˢ (Set.Ioc 0 (n : ℝ) ×ˢ Set.Ioc (-(n : ℝ)) n) := by
    ext p
    simp [walshBox, and_assoc]
  rw [e, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
  simp [ENNReal.mul_lt_top]

/-- The σ-algebra `𝒫 ⊗ 𝓑(ℝ)` pulled back to `Ω × ℝ × ℝ` by `walshPredMap`. -/
@[instance_reducible]
private def walshPredSigma (𝓖 : Filtration ℝ≥0 mΩ) : MeasurableSpace (Ω × ℝ × ℝ) :=
  MeasurableSpace.comap walshPredMap ((𝓖.predictable).prod (borel ℝ))

/-- **Dynkin argument**: for every set `A` of the σ-algebra `𝒫 ⊗ 𝓑(ℝ)` (`𝒫` the predictable
σ-algebra), the indicator of `{(ω, s, y) ∈ (0,n] × (-n,n] : ((s, ω), y) ∈ A}` has a Walsh
integral. The generators `((i, ∞) × A) × (l, u]` give blocks, and the class is a Dynkin system
(complements in the box, countable disjoint unions by `walshInt_indicator_iUnion`). -/
private lemma walshInt_box_indicator (hS : IsWhiteNoise 𝓖 S ν) (n : ℕ) (A : Set ((ℝ≥0 × Ω) × ℝ))
    (hA : MeasurableSet[(𝓖.predictable).prod (borel ℝ)] A) :
    WalshIntegrable 𝓖 S ν ((walshBox n ∩ walshPredMap ⁻¹' A).indicator fun _ => (1 : ℝ)) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  set C : Set (Set (ℝ≥0 × Ω)) := {s | ∃ A, MeasurableSet[𝓖 ⊥] A ∧ s = {⊥} ×ˢ A} ∪
    {s | ∃ i A, MeasurableSet[𝓖 i] A ∧ s = Set.Ioi i ×ˢ A} with hCdef
  set D : Set (Set ℝ) := {S : Set ℝ | ∃ l u, l < u ∧ Set.Ioc l u = S} with hDdef
  have hpiC : IsPiSystem C := by
    rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩) t (⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩) hne
    · exact Or.inl ⟨A ∩ B, hA.inter hB, by rw [Set.prod_inter_prod, Set.inter_self]⟩
    · exfalso
      obtain ⟨⟨x, ω⟩, ⟨hx1, -⟩, hx2, -⟩ := hne
      simp only [Set.mem_singleton_iff] at hx1
      subst hx1
      exact not_lt_bot (show j < ⊥ from hx2)
    · exfalso
      obtain ⟨⟨x, ω⟩, ⟨hx1, -⟩, hx2, -⟩ := hne
      simp only [Set.mem_singleton_iff] at hx2
      subst hx2
      exact not_lt_bot (show i < ⊥ from hx1)
    · refine Or.inr ⟨max i j, A ∩ B, (𝓖.mono (le_max_left i j) _ hA).inter
        (𝓖.mono (le_max_right i j) _ hB),
        ?_⟩
      rw [Set.prod_inter_prod, Set.Ioi_inter_Ioi]
  have hspC : IsCountablySpanning C := by
    refine ⟨fun k => if k = 0 then {⊥} ×ˢ Set.univ else Set.Ioi ⊥ ×ˢ Set.univ, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact Or.inl ⟨Set.univ, MeasurableSet.univ, rfl⟩
      · exact Or.inr ⟨⊥, Set.univ, MeasurableSet.univ, rfl⟩
    · refine Set.eq_univ_of_forall fun ⟨x, ω⟩ => Set.mem_iUnion.2 ?_
      rcases eq_bot_or_bot_lt x with hx | hx
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simpa using hx⟩
  have hpiD : IsPiSystem D := isPiSystem_Ioc id id
  have hspD : IsCountablySpanning D := by
    refine ⟨fun k => Set.Ioc (-((k : ℝ) + 1)) ((k : ℝ) + 1), fun k => ⟨_, _, by linarith, rfl⟩,
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    refine ⟨k, ?_, ?_⟩ <;> linarith [abs_le.1 (le_refl |x|), neg_abs_le x, le_abs_self x]
  have hgen : (𝓖.predictable).prod (borel ℝ) = MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) C D) := by
    rw [borel_eq_generateFrom_Ioc ℝ]
    exact generateFrom_prod_eq hspC hspD
  have hφ := measurable_walshPredMap (𝓖 := 𝓖) (Ω := Ω)
  have hbox : WalshIntegrable 𝓖 S ν ((walshBox n).indicator fun _ => (1 : ℝ)) := by
    convert walshInt_rect (𝓖 := 𝓖) (S := S) (ν := ν) 0 n (-n) n (c := fun _ => (1 : ℝ))
      measurable_const ⟨1, by simp⟩ using 1
    funext p
    simp [walshBox, Set.indicator_apply]
  refine MeasurableSpace.induction_on_inter (C := fun A _ =>
    WalshIntegrable 𝓖 S ν ((walshBox n ∩ walshPredMap ⁻¹' A).indicator fun _ => (1 : ℝ)))
    hgen (hpiC.prod hpiD) ?_ ?_ ?_ ?_ A hA
  · simp only [Set.preimage_empty, Set.inter_empty, Set.indicator_empty]
    exact walshInt_zero
  · rintro - ⟨P, hP, B, ⟨l, u, hlu, rfl⟩, rfl⟩
    rcases hP with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩
    · have e : walshBox n ∩ walshPredMap ⁻¹' (({⊥} ×ˢ A) ×ˢ Set.Ioc l u) = ∅ := by
        ext ⟨ω, s, y⟩
        simp only [walshBox, walshPredMap, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨⟨hs, -⟩, ⟨h0, -⟩, -⟩
        rw [bot_eq_zero', Real.toNNReal_eq_zero] at h0
        linarith
      rw [e, Set.indicator_empty]
      exact walshInt_zero
    · convert walshInt_rect (𝓖 := 𝓖) (S := S) (ν := ν) i n (max l (-n)) (min u n)
        (c := A.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hA)
        ⟨1, fun ω => by by_cases h : ω ∈ A <;> simp [h]⟩ using 1
      funext ⟨ω, s, y⟩
      have hi : (0 : ℝ) ≤ i := i.2
      have key : (ω, s, y) ∈ walshBox n ∩ walshPredMap ⁻¹' ((Set.Ioi i ×ˢ A) ×ˢ Set.Ioc l u) ↔
          ((i : ℝ) < s ∧ s ≤ ((n : ℝ≥0) : ℝ) ∧ max l (-n) < y ∧ y ≤ min u n) ∧ ω ∈ A := by
        simp only [walshBox, walshPredMap, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
          Set.mem_prod, Set.mem_Ioi, Set.mem_Ioc, Real.lt_toNNReal_iff_coe_lt, max_lt_iff,
          le_min_iff, NNReal.coe_natCast]
        constructor
        · rintro ⟨⟨-, h2, h3, h4⟩, ⟨h5, hω⟩, h6, h7⟩
          exact ⟨⟨h5, h2, ⟨h6, h3⟩, h7, h4⟩, hω⟩
        · rintro ⟨⟨h5, h2, ⟨h6, h3⟩, h7, h4⟩, hω⟩
          exact ⟨⟨by linarith, h2, h3, h4⟩, ⟨h5, hω⟩, h6, h7⟩
      split_ifs with hc
      · by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem (key.2 ⟨hc, hω⟩), Set.indicator_of_mem hω]
        · rw [Set.indicator_of_notMem (fun h => hω (key.1 h).2), Set.indicator_of_notMem hω]
      · exact Set.indicator_of_notMem (fun h => hc (key.1 h).1) _
  · intro t htm ih
    have e : walshBox n ∩ walshPredMap ⁻¹' tᶜ = walshBox n \ (walshBox n ∩ walshPredMap ⁻¹' t) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e, Set.indicator_sdiff Set.inter_subset_left]
    exact walshInt_sub hbox ih
  · intro f hdisj hfm ih
    set T : ℕ → Set (Ω × ℝ × ℝ) := fun N => ⋃ i ∈ Finset.range N, walshBox n ∩ walshPredMap ⁻¹' f i
      with hTdef
    have hfm' : ∀ i, MeasurableSet (walshBox (Ω := Ω) n ∩ walshPredMap ⁻¹' f i) := fun i =>
      (measurableSet_walshBox n).inter (hφ (hfm i))
    refine walshInt_indicator_iUnion hS (T := T) ?_ ?_ ?_ ?_ 1 ?_
    · intro N M hNM
      exact Set.biUnion_subset_biUnion_left (by simpa using Finset.range_mono hNM)
    · ext p
      simp only [hTdef, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_preimage,
        exists_prop]
      constructor
      · rintro ⟨N, i, -, hb, hi⟩
        exact ⟨hb, i, hi⟩
      · rintro ⟨hb, i, hi⟩
        exact ⟨i + 1, i, by omega, hb, hi⟩
    · intro N
      exact Finset.measurableSet_biUnion _ fun i _ => hfm' i
    · exact (measure_mono Set.inter_subset_left).trans_lt (measure_walshBox_lt_top n)
    · intro N
      induction N with
      | zero =>
        simp only [hTdef, Finset.range_zero, Finset.notMem_empty, Set.iUnion_of_empty,
          Set.iUnion_empty, Set.indicator_empty]
        exact walshInt_zero
      | succ N ihN =>
        have e : T (N + 1) = T N ∪ (walshBox n ∩ walshPredMap ⁻¹' f N) := by
          simp only [hTdef, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
        have hd : Disjoint (T N) (walshBox n ∩ walshPredMap ⁻¹' f N) := by
          simp only [hTdef, Set.disjoint_iUnion_left]
          intro i hi
          exact ((hdisj (by simp at hi; omega : i ≠ N)).preimage walshPredMap).mono
            Set.inter_subset_right Set.inter_subset_right
        rw [e, Set.indicator_union_of_disjoint hd]
        exact walshInt_add ihN (ih N)

/-- **Existence of the Walsh integral** for fields that are predictable (as functions of
`((s, ω), y)`), vanish for `s ≤ 0`, and are square integrable on `Ω × ℝ × ℝ`. -/
theorem exists_isWalshIntegral (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ}
    (hp : Measurable[(𝓖.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2)
    (hneg : ∀ s y ω, s ≤ 0 → h s y ω = 0)
    (h2 : MemLp (uncurryField h) 2 (ν.prod volume)) :
    ∃ X : Ω → ℝ, IsWalshIntegral 𝓖 S ν h X := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  have hφ := measurable_walshPredMap (𝓖 := 𝓖) (Ω := Ω)
  -- the σ-algebra `𝒫 ⊗ 𝓑(ℝ)` pulled back to `Ω × ℝ × ℝ`, and the trimmed measure
  have hm : walshPredSigma 𝓖 ≤ (inferInstance : MeasurableSpace (Ω × ℝ × ℝ)) := hφ.comap_le
  set μ := (ν.prod volume).trim hm with hμdef
  set P : Set (Ω × ℝ × ℝ) := {p | 0 < p.2.1} with hPdef
  have hPm : MeasurableSet P := measurableSet_lt measurable_const (by fun_prop)
  have key : ∀ f : Ω × ℝ × ℝ → ℝ, MemLp f 2 μ → WalshIntegrable 𝓖 S ν (P.indicator f) := by
    intro f hf
    refine @MemLp.induction _ _ (walshPredSigma 𝓖) _ 2 μ _ ENNReal.ofNat_ne_top
      (fun f => WalshIntegrable 𝓖 S ν (P.indicator f)) ?_ ?_ ?_ ?_ f hf
    · -- indicators of sets of finite measure
      intro c s hs hμs
      obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
      rw [hμdef, trim_measurableSet_eq hm hs] at hμs
      rw [Set.indicator_indicator]
      refine walshInt_indicator_iUnion hS (T := fun k => walshBox k ∩ walshPredMap ⁻¹' A)
        ?_ ?_ (fun k => (measurableSet_walshBox k).inter (hφ hA))
        ((measure_mono Set.inter_subset_right).trans_lt hμs) c ?_
      · intro k l hkl p ⟨⟨h1, h2, h3, h4⟩, hp⟩
        have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
        exact ⟨⟨h1, h2.trans hkl', by linarith, h4.trans hkl'⟩, hp⟩
      · ext p
        simp only [Set.mem_iUnion, Set.mem_inter_iff, hPdef, Set.mem_ofPred_eq, walshBox]
        constructor
        · rintro ⟨k, ⟨h1, -⟩, hp⟩
          exact ⟨h1, hp⟩
        · rintro ⟨h1, hp⟩
          obtain ⟨k, hk⟩ := exists_nat_gt (max p.2.1 |p.2.2|)
          rw [max_lt_iff] at hk
          exact ⟨k, ⟨h1, hk.1.le, by linarith [neg_abs_le p.2.2], (le_abs_self _).trans hk.2.le⟩,
            hp⟩
      · intro k
        have e : ((walshBox k ∩ walshPredMap ⁻¹' A).indicator fun _ => c) =
            fun p => c * (walshBox k ∩ walshPredMap ⁻¹' A).indicator (fun _ => (1 : ℝ)) p := by
          funext p
          by_cases hp : p ∈ walshBox k ∩ walshPredMap ⁻¹' A
          · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, mul_one]
          · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
        rw [e]
        exact walshInt_const_mul (walshInt_box_indicator hS k A hA) c
    · -- sums
      intro f g _ _ _ hf hg
      rw [Set.indicator_add']
      exact walshInt_add hf hg
    · -- closedness in `L²`
      refine IsSeqClosed.isClosed fun F G hF hFG => ?_
      have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F G).1 hFG
      refine walshInt_of_tendsto hS hF
        ((memLp_of_memLp_trim hm (Lp.memLp G)).indicator hPm.nullMeasurableSet) ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
        (fun k => ?_)
      rw [← Set.indicator_sub']
      refine (eLpNorm_indicator_le _ hPm.nullMeasurableSet).trans (le_of_eq ?_)
      exact (eLpNorm_trim_ae hm ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))).symm
    · -- almost-everywhere modifications
      intro f g hfg _ hf
      refine walshInt_congr_ae hS hf ?_
      filter_upwards [ae_eq_of_ae_eq_trim hfg] with p hp
      by_cases hpP : p ∈ P
      · rw [Set.indicator_of_mem hpP, Set.indicator_of_mem hpP, hp]
      · rw [Set.indicator_of_notMem hpP, Set.indicator_of_notMem hpP]
  -- the field `h` is `m`-measurable: `h(s, y, ω) = H((s⁺, ω), y)`, using `h = 0` for `s ≤ 0`
  have hcomp : uncurryField h = (fun q : (ℝ≥0 × Ω) × ℝ => h q.1.1 q.2 q.1.2) ∘ walshPredMap := by
    funext ⟨ω, s, y⟩
    simp only [uncurryField, Function.comp_apply, walshPredMap]
    rcases le_or_gt s 0 with hs | hs
    · rw [hneg s y ω hs, Real.toNNReal_of_nonpos hs, NNReal.coe_zero, hneg 0 y ω le_rfl]
    · rw [Real.coe_toNNReal s hs.le]
  have hfm : StronglyMeasurable[walshPredSigma 𝓖] (uncurryField h) := by
    rw [hcomp]
    exact (hp.comp (comap_measurable _)).stronglyMeasurable
  have hfμ : MemLp (uncurryField h) 2 μ :=
    memLp_iff.2 (by rw [hμdef, eLpNorm_trim hm hfm]; exact h2.eLpNorm_lt_top)
  have hW := key _ hfμ
  rw [Set.indicator_eq_self.2] at hW
  · exact hW
  · intro p hp
    by_contra hp'
    exact hp (hneg p.2.1 p.2.2 p.1 (not_lt.1 hp'))

end QSSEPtoKPZ
