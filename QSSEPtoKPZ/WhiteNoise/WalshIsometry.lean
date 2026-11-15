/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshElem

/-!
# Itô's isometry for the Itô–Walsh integral: companion statement W (task G4b)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G4b.
See `docs/stage4-design.md`, Section 3.3, and `docs/stage4-interfaces.md`.

`IsWalshIntegral.ae_eq_lib` and `IsWalshIntegral.isometry_lib` are the library copies of the
companion statements **W** (`IsWalshIntegral.ae_eq`, `IsWalshIntegral.isometry` of
`Companions.lean`): their statements are identical (checked with `pp.all`), and
`Solution.lean` proves the companions by quoting these. They are also statements submitted to
the author (`docs/stage4-statements.md`). Proof: pass to the limit in the elementary
isometry along the approximations of `IsWalshIntegral.exists_elem_tendsto`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### Auxiliary results -/

section Aux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- For `f ∈ L²(μ)`, `∫ f² dμ = ‖f‖₂²`. -/
private lemma walsh_integral_sq_eq {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) : ∫ x, f x ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal ∂μ := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (by positivity)]
  have e : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by simp
  rw [e] at h0 ⊢
  rw [Real.rpow_inv_natCast_pow h0 two_ne_zero]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Real.norm_eq_abs, sq_abs]

/-- Square integrability of a Walsh integral and of its integrand. -/
private lemma walsh_memLp (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) :
    MemLp (uncurryField h) 2 (ν.prod volume) ∧ MemLp X 2 ν := by
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    have he : (WalshElem.single s t a b c).IsAdapted 𝓖 :=
      ⟨fun _ => hst, fun _ => hab, fun _ => hc, fun _ => hbdd⟩
    have hi := he.isometry hS
    rw [WalshElem.field_single, WalshElem.value_single] at hi
    exact ⟨hi.1, hi.2.1⟩
  | add h h' X X' _ _ ih ih' => exact ⟨ih.1.add ih'.1, ih.2.add ih'.2⟩
  | limit h X hs Xs _ hh hX _ _ _ => exact ⟨hh, hX⟩

/-- **Itô's isometry, norm form**: `‖X‖_{L²(ν)} = ‖h‖_{L²(ν ⊗ ds ⊗ dy)}`. Proof: pass to the
limit in the elementary isometry along the approximations of
`IsWalshIntegral.exists_elem_tendsto`. -/
private lemma walsh_norm_eq (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) :
    (eLpNorm X 2 ν).toReal = (eLpNorm (uncurryField h) 2 (ν.prod volume)).toReal := by
  obtain ⟨hh2, hX2⟩ := walsh_memLp hS hX
  obtain ⟨e, he, h1, h2⟩ := hX.exists_elem_tendsto hS
  have hi := fun j => (he j).isometry hS
  -- the elementary isometry, in norm form
  have heq : ∀ j, ‖(hi j).2.1.toLp ((e j).value S)‖ =
      ‖(hi j).1.toLp (uncurryField (e j).field)‖ := by
    intro j
    rw [Lp.norm_toLp, Lp.norm_toLp]
    have := (hi j).2.2
    rw [walsh_integral_sq_eq (hi j).2.1, walsh_integral_sq_eq (hi j).1] at this
    exact (sq_eq_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).1 this
  have tX : Tendsto (fun j => (hi j).2.1.toLp ((e j).value S)) atTop (𝓝 (hX2.toLp X)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j => (hi j).2.1) X hX2).2 h2
  have th : Tendsto (fun j => (hi j).1.toLp (uncurryField (e j).field)) atTop
      (𝓝 (hh2.toLp (uncurryField h))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j => (hi j).1) _ hh2).2 h1
  rw [← Lp.norm_toLp X hX2, ← Lp.norm_toLp _ hh2]
  refine tendsto_nhds_unique (tX.norm) ?_
  simp_rw [heq]
  exact th.norm

end Aux

/-- **W**, first part (library copy of `IsWalshIntegral.ae_eq` of `Companions.lean`; the
Itô-Walsh integral is well defined; Section 7.2). If `X = ∫ h dξ` and `X' = ∫ h' dξ`, and the
fields `h` and `h'` agree almost everywhere on `Ω × ℝ₊ × ℝ`, then `X = X'` almost surely. -/
theorem IsWalshIntegral.ae_eq_lib {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {h h' : ℝ → ℝ → Ω → ℝ} {X X' : Ω → ℝ}
    (hX : IsWalshIntegral 𝓖 S ν h X) (hX' : IsWalshIntegral 𝓖 S ν h' X')
    (hh : uncurryField h =ᵐ[ν.prod volume] uncurryField h') :
    X =ᵐ[ν] X' := by
  have hd := hX.sub hX'
  obtain ⟨-, hd2⟩ := walsh_memLp hS hd
  have hn := walsh_norm_eq hS hd
  have hz : uncurryField (fun s y ω => h s y ω - h' s y ω) =ᵐ[ν.prod volume] 0 := by
    filter_upwards [hh] with p hp
    simp only [uncurryField] at hp ⊢
    rw [hp, sub_self]
    rfl
  rw [eLpNorm_congr_ae hz, eLpNorm_zero, ENNReal.toReal_zero] at hn
  have h0 : eLpNorm (fun ω => X ω - X' ω) 2 ν = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hn with h0 | h0
    · exact h0
    · exact absurd h0 hd2.eLpNorm_lt_top.ne
  rw [eLpNorm_eq_zero_iff two_ne_zero] at h0
  filter_upwards [h0] with ω hω
  exact sub_eq_zero.1 hω

/-- **W**, second part (library copy of `IsWalshIntegral.isometry` of `Companions.lean`; Itô's
isometry for the Itô-Walsh integral; Section 7.2). If `X = ∫ h dξ`, then `h` is square
integrable on `Ω × ℝ₊ × ℝ`, `X` is square integrable, and `𝔼[X²] = 𝔼 ∫∫ h(s,y)² ds dy`. -/
theorem IsWalshIntegral.isometry_lib {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} (hS : IsWhiteNoise 𝓖 S ν)
    {h : ℝ → ℝ → Ω → ℝ} {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    MemLp (uncurryField h) 2 (ν.prod volume) ∧ MemLp X 2 ν ∧
      ∫ ω, X ω ^ 2 ∂ν = ∫ p, uncurryField h p ^ 2 ∂(ν.prod volume) := by
  obtain ⟨hh2, hX2⟩ := walsh_memLp hS hX
  refine ⟨hh2, hX2, ?_⟩
  rw [walsh_integral_sq_eq hX2, walsh_integral_sq_eq hh2, walsh_norm_eq hS hX]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- **Polarized isometry**: `𝔼[X X'] = 𝔼 ∫∫ h h'`. -/
theorem IsWalshIntegral.integral_mul (hS : IsWhiteNoise 𝓖 S ν) {h h' : ℝ → ℝ → Ω → ℝ}
    {X X' : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) (hX' : IsWalshIntegral 𝓖 S ν h' X') :
    ∫ ω, X ω * X' ω ∂ν = ∫ p, uncurryField h p * uncurryField h' p ∂(ν.prod volume) := by
  obtain ⟨hh2, hX2⟩ := walsh_memLp hS hX
  obtain ⟨hh2', hX2'⟩ := walsh_memLp hS hX'
  have ha := (IsWalshIntegral.isometry_lib hS (IsWalshIntegral.add _ _ _ _ hX hX')).2.2
  have hs := (IsWalshIntegral.isometry_lib hS (hX.sub hX')).2.2
  have e1 : ∀ ω, X ω * X' ω = ((X ω + X' ω) ^ 2 - (X ω - X' ω) ^ 2) / 4 := fun ω => by ring
  have e2 : ∀ p, uncurryField h p * uncurryField h' p =
      ((uncurryField h p + uncurryField h' p) ^ 2 - (uncurryField h p - uncurryField h' p) ^ 2)
        / 4 := fun p => by ring
  simp_rw [e1, e2]
  rw [integral_div, integral_div, integral_sub, integral_sub]
  · simp only [uncurryField] at ha hs ⊢
    rw [ha, hs]
  all_goals first
    | exact (hX2.add hX2').integrable_sq | exact (hX2.sub hX2').integrable_sq
    | exact (hh2.add hh2').integrable_sq | exact (hh2.sub hh2').integrable_sq

/-- Walsh integrals are stable under almost-everywhere modification of the integrand and of the
value. -/
theorem IsWalshIntegral.congr_ae (hS : IsWhiteNoise 𝓖 S ν) {h h' : ℝ → ℝ → Ω → ℝ}
    {X X' : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X)
    (hh : uncurryField h =ᵐ[ν.prod volume] uncurryField h') (hXX : X =ᵐ[ν] X') :
    IsWalshIntegral 𝓖 S ν h' X' := by
  obtain ⟨hh2, hX2⟩ := walsh_memLp hS hX
  refine IsWalshIntegral.limit h' X' (fun _ => h) (fun _ => X) (fun _ => hX) (hh2.ae_eq hh)
    (hX2.ae_eq hXX) ?_ ?_
  · have hz : uncurryField h - uncurryField h' =ᵐ[ν.prod volume] 0 := by
      filter_upwards [hh] with p hp
      simp [hp]
    simp [eLpNorm_congr_ae hz]
  · have hz : X - X' =ᵐ[ν] 0 := by
      filter_upwards [hXX] with p hp
      simp [hp]
    simp [eLpNorm_congr_ae hz]

/-- **Closure under `L²` limits of integrands** (existence of the limit value, by the isometry and
completeness of `L²`): if `hₖ → h` in `L²(Ω × ℝ₊ × ℝ)` and `h ∈ L²`, then `∫ h dξ` exists and is
the `L²` limit of the `∫ hₖ dξ`. -/
theorem IsWalshIntegral.exists_limit (hS : IsWhiteNoise 𝓖 S ν) {hs : ℕ → ℝ → ℝ → Ω → ℝ}
    {Xs : ℕ → Ω → ℝ} (hX : ∀ k, IsWalshIntegral 𝓖 S ν (hs k) (Xs k)) {h : ℝ → ℝ → Ω → ℝ}
    (h2 : MemLp (uncurryField h) 2 (ν.prod volume))
    (hlim : Tendsto (fun k => eLpNorm (uncurryField (hs k) - uncurryField h) 2 (ν.prod volume))
      atTop (𝓝 0)) :
    ∃ X : Ω → ℝ, IsWalshIntegral 𝓖 S ν h X ∧
      Tendsto (fun k => eLpNorm (Xs k - X) 2 ν) atTop (𝓝 0) := by
  have hm := fun k => walsh_memLp hS (hX k)
  let G : ℕ → Lp ℝ 2 ν := fun k => (hm k).2.toLp (Xs k)
  let F : ℕ → Lp ℝ 2 (ν.prod volume) := fun k => (hm k).1.toLp (uncurryField (hs k))
  have hF : Tendsto F atTop (𝓝 (h2.toLp _)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k => (hm k).1) _ h2).2 hlim
  have hdist : ∀ k l, dist (G k) (G l) = dist (F k) (F l) := by
    intro k l
    simp only [G, F, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    exact walsh_norm_eq hS ((hX k).sub (hX l))
  have hG : CauchySeq G := by
    have hc := Metric.cauchySeq_iff'.1 hF.cauchySeq
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hc ε hε
    exact ⟨N, fun n hn => (hdist n N) ▸ hN n hn⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hG
  have hL' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' G L).1 hL
  have e : ∀ k, eLpNorm (Xs k - ⇑L) 2 ν = eLpNorm (⇑(G k) - ⇑L) 2 ν := fun k =>
    eLpNorm_congr_ae (((hm k).2.coeFn_toLp).symm.sub EventuallyEq.rfl)
  simp_rw [← e] at hL'
  exact ⟨L, IsWalshIntegral.limit h L hs Xs hX h2 (Lp.memLp L) hlim hL', hL'⟩

end QSSEPtoKPZ
