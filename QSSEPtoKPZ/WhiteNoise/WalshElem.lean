/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshBasic

/-!
# Elementary Walsh integrals and their isometry (task G4a)

INTERFACE FILE (task I0″ of Stage 4): the statements below are interfaces, proved by task G4a.
See `docs/stage4-design.md`, Section 3.3, and `docs/stage4-interfaces.md`.

An elementary integrand is a finite sum `∑ᵢ cᵢ 𝟙_{(sᵢ,tᵢ] × (aᵢ,bᵢ]}` with `cᵢ` bounded and
`𝓖_{sᵢ}`-measurable; its integral is `∑ᵢ cᵢ ξ((sᵢ,tᵢ] × (aᵢ,bᵢ])`. Itô's isometry holds for
them (expand the square and compute each cross term `𝔼[cᵢ cⱼ ξ(Rᵢ) ξ(Rⱼ)]` from `indep_past`,
`indep` and `integral_sq_rectMass`, without refining to a common grid), and every Walsh integral is an `L²` limit of
elementary ones (induction on `IsWalshIntegral`, diagonal extraction in the `limit` case).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The data of an elementary Walsh integrand: `k` blocks `cᵢ 𝟙_{(sᵢ,tᵢ] × (aᵢ,bᵢ]}`. -/
structure WalshElem (Ω : Type*) where
  /-- The number of blocks. -/
  k : ℕ
  /-- Time intervals `(sᵢ, tᵢ]`. -/
  s : Fin k → ℝ≥0
  /-- Time intervals `(sᵢ, tᵢ]`. -/
  t : Fin k → ℝ≥0
  /-- Space intervals `(aᵢ, bᵢ]`. -/
  a : Fin k → ℝ
  /-- Space intervals `(aᵢ, bᵢ]`. -/
  b : Fin k → ℝ
  /-- The random coefficients. -/
  c : Fin k → Ω → ℝ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The elementary integrand `∑ᵢ cᵢ 𝟙_{(sᵢ,tᵢ] × (aᵢ,bᵢ]}`. -/
def WalshElem.field (e : WalshElem Ω) : ℝ → ℝ → Ω → ℝ := fun r y ω =>
  ∑ i, if (e.s i : ℝ) < r ∧ r ≤ e.t i ∧ e.a i < y ∧ y ≤ e.b i then e.c i ω else 0

/-- Its integral `∑ᵢ cᵢ ξ((sᵢ,tᵢ] × (aᵢ,bᵢ])`. -/
def WalshElem.value (e : WalshElem Ω) (S : ℝ → ℝ → Ω → ℝ) : Ω → ℝ := fun ω =>
  ∑ i, e.c i ω * rectMass S (e.s i) (e.t i) (e.a i) (e.b i) ω

/-- The conditions of the `block` rule for every block: `sᵢ ≤ tᵢ`, `aᵢ ≤ bᵢ`, `cᵢ` bounded and
`𝓖_{sᵢ}`-measurable. -/
structure WalshElem.IsAdapted (e : WalshElem Ω) (𝓖 : Filtration ℝ≥0 mΩ) : Prop where
  le_t : ∀ i, e.s i ≤ e.t i
  le_b : ∀ i, e.a i ≤ e.b i
  meas : ∀ i, Measurable[𝓖 (e.s i)] (e.c i)
  bdd : ∀ i, ∃ C, ∀ ω, |e.c i ω| ≤ C

variable {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}

/-- An elementary integral is a Walsh integral. -/
theorem WalshElem.IsAdapted.isWalshIntegral {e : WalshElem Ω} (he : e.IsAdapted 𝓖) :
    IsWalshIntegral 𝓖 S ν e.field (e.value S) :=
  IsWalshIntegral.finset_sum Finset.univ fun i _ =>
    IsWalshIntegral.block (e.s i) (e.t i) (e.a i) (e.b i) (e.c i) (he.le_t i) (he.le_b i)
      (he.meas i) (he.bdd i)

/-! ### Itô's isometry for elementary integrands

The proof expands the square of `∑ᵢ cᵢ ξ(Rᵢ)` and computes each cross term
`𝔼[cᵢ cⱼ ξ(Rᵢ) ξ(Rⱼ)] = 𝔼[cᵢ cⱼ] |Rᵢ ∩ Rⱼ|` (lemma `walsh_integral_pair`), instead of refining
to a common grid: the time interval of the block that starts first is cut at the start of the
other one, the part before is orthogonal to the other block (`indep_past`), and two blocks
starting at the same time are handled by `indep_past` and the spatial covariance
`𝔼[ξ((u,v] × I) ξ((u,v] × J)] = (v - u) |I ∩ J|` (from `indep` and `integral_sq_rectMass`). -/

section Isometry

variable (hS : IsWhiteNoise 𝓖 S ν)
include hS

/-- The mass of a rectangle `(s,t] × (a,b]` with `s, t ≤ u` is `𝓖_u`-measurable. -/
private lemma walsh_meas_rect {s t u : ℝ≥0} (hs : s ≤ u) (ht : t ≤ u) (a b : ℝ) :
    Measurable[𝓖 u] (rectMass S s t a b) := by
  have h1 : ∀ x, Measurable[𝓖 u] (S t x) := fun x => (hS.adapted t x).mono (𝓖.mono ht) le_rfl
  have h0 : ∀ x, Measurable[𝓖 u] (S s x) := fun x => (hS.adapted s x).mono (𝓖.mono hs) le_rfl
  exact (((h1 b).sub (h1 a)).sub (h0 b)).add (h0 a)

/-- The mass of a rectangle is measurable. -/
private lemma walsh_meas_rect' (s t : ℝ≥0) (a b : ℝ) : Measurable (rectMass S s t a b) :=
  (walsh_meas_rect hS (le_max_left s t) (le_max_right s t) a b).mono (𝓖.le _) le_rfl

/-- The mass of a rectangle is square integrable. -/
private lemma walsh_memLp_rect {s t : ℝ≥0} (hst : s ≤ t) {a b : ℝ} (hab : a ≤ b) :
    MemLp (rectMass S s t a b) 2 ν :=
  (hS.gaussian s t a b hst hab).hasGaussianLaw.memLp_two

/-- The mass of a rectangle is centred. -/
private lemma walsh_integral_rect {s t : ℝ≥0} (hst : s ≤ t) {a b : ℝ} (hab : a ≤ b) :
    ∫ ω, rectMass S s t a b ω ∂ν = 0 := by
  rw [(hS.gaussian s t a b hst hab).integral_eq, integral_id_gaussianReal]

/-- The product of the masses of two rectangles is integrable. -/
private lemma walsh_int_rect_mul {s t s' t' : ℝ≥0} (hst : s ≤ t) (hst' : s' ≤ t')
    {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') :
    Integrable (fun ω => rectMass S s t a b ω * rectMass S s' t' a' b' ω) ν :=
  (walsh_memLp_rect hS hst hab).integrable_mul (walsh_memLp_rect hS hst' hab')

/-- A bounded measurable multiple of the product of the masses of two rectangles is
integrable. -/
private lemma walsh_int_bdd_mul {Y : Ω → ℝ} (hY : Measurable Y) (hYb : ∃ C, ∀ ω, |Y ω| ≤ C)
    {s t s' t' : ℝ≥0} (hst : s ≤ t) (hst' : s' ≤ t') {a b a' b' : ℝ} (hab : a ≤ b)
    (hab' : a' ≤ b') :
    Integrable (fun ω => Y ω * (rectMass S s t a b ω * rectMass S s' t' a' b' ω)) ν := by
  obtain ⟨C, hC⟩ := hYb
  exact (walsh_int_rect_mul hS hst hst' hab hab').bdd_mul hY.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)

/-- A `𝓖_u`-measurable variable is orthogonal to the mass of a rectangle `(u,v] × (a,b]`:
`𝔼[W ξ((u,v] × (a,b])] = 0`. -/
private lemma walsh_integral_mul_rect_eq_zero {u v : ℝ≥0} (huv : u ≤ v) {a b : ℝ} (hab : a ≤ b)
    {W : Ω → ℝ} (hW : Measurable[𝓖 u] W) :
    ∫ ω, W ω * rectMass S u v a b ω ∂ν = 0 := by
  have hind : IndepFun W (rectMass S u v a b) ν := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep_past u v huv)
      (le_iSup₂ (f := fun a b => MeasurableSpace.comap (rectMass S u v a b) inferInstance)
        a b)) hW.comap_le).symm
  rw [hind.integral_fun_mul_eq_mul_integral (hW.mono (𝓖.le u) le_rfl).aestronglyMeasurable
    (walsh_meas_rect' hS u v a b).aestronglyMeasurable, walsh_integral_rect hS huv hab,
    mul_zero]

/-- Masses of disjoint rectangles in the same time slab are orthogonal. -/
private lemma walsh_integral_rect_mul_disj {u v : ℝ≥0} (huv : u ≤ v) {a b a' b' : ℝ}
    (h1 : a ≤ b) (h2 : b ≤ a') (h3 : a' ≤ b') :
    ∫ ω, rectMass S u v a b ω * rectMass S u v a' b' ω ∂ν = 0 := by
  have hmono : Monotone ![a, b, a', b'] := by
    refine Fin.monotone_iff_le_succ.2 fun i => ?_
    fin_cases i <;> simp [h1, h2, h3]
  have hind : IndepFun (rectMass S u v a b) (rectMass S u v a' b') ν :=
    (hS.indep u v huv 3 ![a, b, a', b'] hmono).indepFun (show (0 : Fin 3) ≠ 2 by decide)
  rw [hind.integral_fun_mul_eq_mul_integral (walsh_meas_rect' hS u v a b).aestronglyMeasurable
    (walsh_meas_rect' hS u v a' b').aestronglyMeasurable, walsh_integral_rect hS huv h1, zero_mul]

/-- Nested rectangles in the same time slab: for `a ≤ b ≤ c`,
`𝔼[ξ((u,v] × (a,b]) ξ((u,v] × (a,c])] = (v - u)(b - a)`. -/
private lemma walsh_integral_rect_mul_nested {u v : ℝ≥0} (huv : u ≤ v) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ ω, rectMass S u v a b ω * rectMass S u v a c ω ∂ν = ((v : ℝ) - u) * (b - a) := by
  have e : ∀ ω, rectMass S u v a b ω * rectMass S u v a c ω =
      rectMass S u v a b ω ^ 2 + rectMass S u v a b ω * rectMass S u v b c ω := by
    intro ω
    simp only [rectMass]
    ring
  simp_rw [e]
  rw [integral_add ((walsh_memLp_rect hS huv hab).integrable_sq)
    (walsh_int_rect_mul hS huv huv hab hbc), walsh_integral_rect_mul_disj hS huv hab le_rfl hbc,
    add_zero, integral_sq_rectMass hS huv hab]

/-- Spatial covariance of the white noise in a time slab:
`𝔼[ξ((u,v] × I) ξ((u,v] × J)] = (v - u) |I ∩ J|`. -/
private lemma walsh_integral_rect_mul_space {u v : ℝ≥0} (huv : u ≤ v) {a b a' b' : ℝ}
    (hab : a ≤ b) (hab' : a' ≤ b') :
    ∫ ω, rectMass S u v a b ω * rectMass S u v a' b' ω ∂ν =
      ((v : ℝ) - u) * volume.real (Set.Ioc a b ∩ Set.Ioc a' b') := by
  wlog haa : a ≤ a' generalizing a b a' b'
  · rw [Set.inter_comm, ← this hab' hab (le_of_not_ge haa)]
    congr 1
    funext ω
    ring
  rw [Set.Ioc_inter_Ioc, Real.volume_real_Ioc, max_eq_right haa]
  rcases le_or_gt b a' with hba | hba
  · rw [walsh_integral_rect_mul_disj hS huv hab hba hab', min_eq_left (hba.trans hab'),
      max_eq_right (by linarith), mul_zero]
  · have e : ∀ ω, rectMass S u v a b ω * rectMass S u v a' b' ω =
        rectMass S u v a a' ω * rectMass S u v a' b' ω +
          rectMass S u v a' b' ω * rectMass S u v a' b ω := by
      intro ω
      simp only [rectMass]
      ring
    simp_rw [e]
    rw [integral_add (walsh_int_rect_mul hS huv huv haa hab')
      (walsh_int_rect_mul hS huv huv hab' hba.le),
      walsh_integral_rect_mul_disj hS huv haa le_rfl hab', zero_add]
    rcases le_total b b' with hbb | hbb
    · rw [show (fun ω => rectMass S u v a' b' ω * rectMass S u v a' b ω) =
          fun ω => rectMass S u v a' b ω * rectMass S u v a' b' ω by funext ω; ring,
        walsh_integral_rect_mul_nested hS huv hba.le hbb, min_eq_left hbb,
        max_eq_left (by linarith)]
    · rw [walsh_integral_rect_mul_nested hS huv hab' hbb, min_eq_right hbb,
        max_eq_left (by linarith)]

/-- A `𝓖_u`-measurable variable is independent of the masses of rectangles in the slab
`(u,v]`: `𝔼[Y ξ((u,v] × I) ξ((u,v] × J)] = 𝔼[Y] (v - u) |I ∩ J|`. -/
private lemma walsh_integral_mul_rect_mul_rect {u v : ℝ≥0} (huv : u ≤ v) {a b a' b' : ℝ}
    (hab : a ≤ b) (hab' : a' ≤ b') {Y : Ω → ℝ} (hY : Measurable[𝓖 u] Y) :
    ∫ ω, Y ω * (rectMass S u v a b ω * rectMass S u v a' b' ω) ∂ν =
      (∫ ω, Y ω ∂ν) * (((v : ℝ) - u) * volume.real (Set.Ioc a b ∩ Set.Ioc a' b')) := by
  have hm : ∀ a b, Measurable[⨆ (a : ℝ) (b : ℝ),
      MeasurableSpace.comap (rectMass S u v a b) inferInstance] (rectMass S u v a b) :=
    fun a b => measurable_iff_comap_le.2
      (le_iSup₂ (f := fun a b => MeasurableSpace.comap (rectMass S u v a b) inferInstance) a b)
  have hind : IndepFun Y (fun ω => rectMass S u v a b ω * rectMass S u v a' b' ω) ν := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep_past u v huv)
      ((hm a b).mul (hm a' b')).comap_le) hY.comap_le).symm
  rw [hind.integral_fun_mul_eq_mul_integral (hY.mono (𝓖.le u) le_rfl).aestronglyMeasurable
    (walsh_int_rect_mul hS huv huv hab hab').aestronglyMeasurable,
    walsh_integral_rect_mul_space hS huv hab hab']

/-- Two blocks starting at the same time `u`, with a `𝓖_u`-measurable bounded coefficient:
`𝔼[Y ξ((u,v] × I) ξ((u,w] × J)] = 𝔼[Y] |(u,v] ∩ (u,w]| |I ∩ J|`. -/
private lemma walsh_integral_same_start {u v w : ℝ≥0} (huv : u ≤ v) (huw : u ≤ w)
    {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') {Y : Ω → ℝ} (hY : Measurable[𝓖 u] Y)
    (hYb : ∃ C, ∀ ω, |Y ω| ≤ C) :
    ∫ ω, Y ω * (rectMass S u v a b ω * rectMass S u w a' b' ω) ∂ν =
      (∫ ω, Y ω ∂ν) * (volume.real (Set.Ioc (u : ℝ) v ∩ Set.Ioc (u : ℝ) w) *
        volume.real (Set.Ioc a b ∩ Set.Ioc a' b')) := by
  wlog hvw : v ≤ w generalizing v w a b a' b'
  · rw [Set.inter_comm (Set.Ioc (u : ℝ) v), Set.inter_comm (Set.Ioc a b),
      ← this huw huv hab' hab (le_of_not_ge hvw)]
    congr 1
    funext ω
    ring
  have hY' : Measurable Y := hY.mono (𝓖.le u) le_rfl
  have e : ∀ ω, Y ω * (rectMass S u v a b ω * rectMass S u w a' b' ω) =
      Y ω * (rectMass S u v a b ω * rectMass S u v a' b' ω) +
        Y ω * rectMass S u v a b ω * rectMass S v w a' b' ω := by
    intro ω
    simp only [rectMass]
    ring
  simp_rw [e]
  have hint : Integrable (fun ω => Y ω * rectMass S u v a b ω * rectMass S v w a' b' ω) ν :=
    (walsh_int_bdd_mul hS hY' hYb huv hvw hab hab').congr
      (ae_of_all _ fun ω => by simp only; ring)
  rw [integral_add (walsh_int_bdd_mul hS hY' hYb huv huv hab hab') hint,
    walsh_integral_mul_rect_eq_zero hS hvw hab' (W := fun ω => Y ω * rectMass S u v a b ω)
      ((hY.mono (𝓖.mono huv) le_rfl).mul (walsh_meas_rect hS huv le_rfl a b)), add_zero,
    walsh_integral_mul_rect_mul_rect hS huv hab hab' hY]
  congr 2
  rw [Set.Ioc_inter_Ioc, max_self, min_eq_left (by exact_mod_cast hvw), Real.volume_real_Ioc,
    max_eq_left (by simpa using huv)]

/-- **Cross terms of the isometry**: for two blocks `c 𝟙_{(s,t] × (a,b]}` and
`c' 𝟙_{(s',t'] × (a',b']}`, `𝔼[c ξ(R) c' ξ(R')] = 𝔼[c c'] |(s,t] ∩ (s',t']| |(a,b] ∩ (a',b']|`. -/
private lemma walsh_integral_pair {s t s' t' : ℝ≥0} (hst : s ≤ t) (hst' : s' ≤ t')
    {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') {c c' : Ω → ℝ} (hc : Measurable[𝓖 s] c)
    (hc' : Measurable[𝓖 s'] c') (hcb : ∃ C, ∀ ω, |c ω| ≤ C) (hcb' : ∃ C, ∀ ω, |c' ω| ≤ C) :
    ∫ ω, c ω * rectMass S s t a b ω * (c' ω * rectMass S s' t' a' b' ω) ∂ν =
      (∫ ω, c ω * c' ω ∂ν) * (volume.real (Set.Ioc (s : ℝ) t ∩ Set.Ioc (s' : ℝ) t') *
        volume.real (Set.Ioc a b ∩ Set.Ioc a' b')) := by
  wlog hss : s ≤ s' generalizing s t s' t' a b a' b' c c'
  · have h := this hst' hst hab' hab hc' hc hcb' hcb (le_of_not_ge hss)
    rw [Set.inter_comm (Set.Ioc (s : ℝ) t), Set.inter_comm (Set.Ioc a b)]
    convert h using 2
    · funext ω
      ring
    · congr 1
      funext ω
      ring
  obtain ⟨C, hC⟩ := hcb
  obtain ⟨C', hC'⟩ := hcb'
  have hY : Measurable[𝓖 s'] fun ω => c ω * c' ω := (hc.mono (𝓖.mono hss) le_rfl).mul hc'
  have hYb : ∃ K, ∀ ω, |c ω * c' ω| ≤ K := ⟨|C| * |C'|, fun ω => by
    rw [abs_mul]
    exact mul_le_mul ((hC ω).trans (le_abs_self _)) ((hC' ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)⟩
  rcases le_or_gt t s' with hts | hts
  · -- the blocks are disjoint in time
    rw [show (fun ω => c ω * rectMass S s t a b ω * (c' ω * rectMass S s' t' a' b' ω)) =
        fun ω => c ω * c' ω * rectMass S s t a b ω * rectMass S s' t' a' b' ω by
          funext ω; ring,
      walsh_integral_mul_rect_eq_zero hS hst' hab'
        (W := fun ω => c ω * c' ω * rectMass S s t a b ω) (hY.mul (walsh_meas_rect hS hss hts a b)),
      Set.Ioc_inter_Ioc, Real.volume_real_Ioc, max_eq_right]
    · simp
    · have h1 : min (t : ℝ) t' ≤ t := min_le_left _ _
      have h2 : (s' : ℝ) ≤ max (s : ℝ) s' := le_max_right _ _
      have h3 : (t : ℝ) ≤ s' := by exact_mod_cast hts
      linarith
  · -- cut `(s,t]` at `s'`
    have e : ∀ ω, c ω * rectMass S s t a b ω * (c' ω * rectMass S s' t' a' b' ω) =
        c ω * c' ω * rectMass S s s' a b ω * rectMass S s' t' a' b' ω +
          c ω * c' ω * (rectMass S s' t a b ω * rectMass S s' t' a' b' ω) := by
      intro ω
      simp only [rectMass]
      ring
    simp_rw [e]
    have hint : Integrable
        (fun ω => c ω * c' ω * rectMass S s s' a b ω * rectMass S s' t' a' b' ω) ν :=
      (walsh_int_bdd_mul hS (hY.mono (𝓖.le _) le_rfl) hYb hss hst' hab hab').congr
        (ae_of_all _ fun ω => by simp only; ring)
    rw [integral_add hint (walsh_int_bdd_mul hS (hY.mono (𝓖.le _) le_rfl) hYb hts.le hst' hab
      hab'), walsh_integral_mul_rect_eq_zero hS hst' hab'
      (W := fun ω => c ω * c' ω * rectMass S s s' a b ω) (hY.mul (walsh_meas_rect hS hss le_rfl a b)), zero_add,
      walsh_integral_same_start hS hts.le hst' hab hab' hY hYb]
    congr 3
    rw [Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioc, max_self,
      max_eq_right (show (s : ℝ) ≤ s' by exact_mod_cast hss)]

omit hS in
/-- The integral over `Ω × ℝ × ℝ` of the product of two blocks:
`∫ c 𝟙_R c' 𝟙_{R'} = 𝔼[c c'] |(s,t] ∩ (s',t']| |(a,b] ∩ (a',b']|`. -/
private lemma walsh_integral_block_mul_block [SFinite ν] {s t s' t' a b a' b' : ℝ} {c c' : Ω → ℝ} :
    ∫ p : Ω × ℝ × ℝ, (if s < p.2.1 ∧ p.2.1 ≤ t ∧ a < p.2.2 ∧ p.2.2 ≤ b then c p.1 else 0) *
        (if s' < p.2.1 ∧ p.2.1 ≤ t' ∧ a' < p.2.2 ∧ p.2.2 ≤ b' then c' p.1 else 0)
        ∂(ν.prod volume) =
      (∫ ω, c ω * c' ω ∂ν) * (volume.real (Set.Ioc s t ∩ Set.Ioc s' t') *
        volume.real (Set.Ioc a b ∩ Set.Ioc a' b')) := by
  have e : ∀ p : Ω × ℝ × ℝ,
      (if s < p.2.1 ∧ p.2.1 ≤ t ∧ a < p.2.2 ∧ p.2.2 ≤ b then c p.1 else 0) *
        (if s' < p.2.1 ∧ p.2.1 ≤ t' ∧ a' < p.2.2 ∧ p.2.2 ≤ b' then c' p.1 else 0) =
      c p.1 * c' p.1 *
        ((Set.Ioc s t ∩ Set.Ioc s' t') ×ˢ (Set.Ioc a b ∩ Set.Ioc a' b')).indicator 1 p.2 := by
    intro p
    simp only [Set.indicator_apply, Set.mem_prod, Set.mem_inter_iff, Set.mem_Ioc, Pi.one_apply]
    split_ifs <;> first | (exfalso; tauto) | ring
  simp_rw [e]
  have hpm := integral_prod_mul (μ := ν) (ν := (volume : Measure (ℝ × ℝ)))
    (fun ω => c ω * c' ω)
    (((Set.Ioc s t ∩ Set.Ioc s' t') ×ˢ (Set.Ioc a b ∩ Set.Ioc a' b')).indicator 1)
  rw [hpm, integral_indicator_one ((measurableSet_Ioc.inter measurableSet_Ioc).prod
    (measurableSet_Ioc.inter measurableSet_Ioc)), Measure.volume_eq_prod, measureReal_prod_prod]

omit hS in
/-- A block `c 𝟙_{(s,t] × (a,b]}` with `c` bounded and measurable is in `L²(Ω × ℝ × ℝ)`. -/
private lemma walsh_memLp_block [IsFiniteMeasure ν] {s t a b : ℝ} {c : Ω → ℝ}
    (hc : Measurable c) (hcb : ∃ C, ∀ ω, |c ω| ≤ C) :
    MemLp (fun p : Ω × ℝ × ℝ => if s < p.2.1 ∧ p.2.1 ≤ t ∧ a < p.2.2 ∧ p.2.2 ≤ b then c p.1
      else 0) 2 (ν.prod volume) := by
  obtain ⟨C, hC⟩ := hcb
  set A : Set (Ω × ℝ × ℝ) := Set.univ ×ˢ (Set.Ioc s t ×ˢ Set.Ioc a b) with hAdef
  have hA : MeasurableSet A := MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hAf : (ν.prod volume) A ≠ ⊤ := by
    rw [hAdef, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _)
      (ENNReal.mul_ne_top (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc]))
  have hfeq : (fun p : Ω × ℝ × ℝ => if s < p.2.1 ∧ p.2.1 ≤ t ∧ a < p.2.2 ∧ p.2.2 ≤ b then c p.1
      else 0) = A.indicator fun p => c p.1 := by
    funext p
    simp only [hAdef, Set.indicator_apply, Set.mem_prod, Set.mem_univ, Set.mem_Ioc, true_and,
      and_assoc]
  rw [hfeq]
  refine (memLp_indicator_const 2 hA.nullMeasurableSet |C| (Or.inr hAf)).of_le
    ((hc.comp measurable_fst).indicator hA).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  by_cases hp : p ∈ A
  · simp only [Set.indicator_of_mem hp, Real.norm_eq_abs, abs_abs]
    exact (hC p.1).trans (le_abs_self C)
  · simp [Set.indicator_of_notMem hp]

end Isometry

/-- **Itô's isometry for elementary integrands**, with the integrability of both sides. -/
theorem WalshElem.IsAdapted.isometry (hS : IsWhiteNoise 𝓖 S ν) {e : WalshElem Ω}
    (he : e.IsAdapted 𝓖) :
    MemLp (uncurryField e.field) 2 (ν.prod volume) ∧ MemLp (e.value S) 2 ν ∧
      ∫ ω, e.value S ω ^ 2 ∂ν = ∫ p, uncurryField e.field p ^ 2 ∂(ν.prod volume) := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  set f : Fin e.k → Ω × ℝ × ℝ → ℝ := fun i p =>
    if (e.s i : ℝ) < p.2.1 ∧ p.2.1 ≤ e.t i ∧ e.a i < p.2.2 ∧ p.2.2 ≤ e.b i then e.c i p.1
    else 0 with hfdef
  set g : Fin e.k → Ω → ℝ := fun i ω =>
    e.c i ω * rectMass S (e.s i) (e.t i) (e.a i) (e.b i) ω with hgdef
  have hcm : ∀ i, Measurable (e.c i) := fun i => (he.meas i).mono (𝓖.le _) le_rfl
  have hf : ∀ i, MemLp (f i) 2 (ν.prod volume) := fun i => walsh_memLp_block (hcm i) (he.bdd i)
  have hg : ∀ i, MemLp (g i) 2 ν := by
    intro i
    obtain ⟨C, hC⟩ := he.bdd i
    have hξ := walsh_memLp_rect hS (he.le_t i) (he.le_b i)
    refine MemLp.of_le_mul (c := |C|) hξ ((hcm i).aestronglyMeasurable.mul
      hξ.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    simp only [hgdef, norm_mul]
    gcongr
    exact (hC ω).trans (le_abs_self C)
  have hF : uncurryField e.field = fun p => ∑ i, f i p := rfl
  have hG : e.value S = fun ω => ∑ i, g i ω := rfl
  refine ⟨hF ▸ memLp_finsetSum _ fun i _ => hf i, hG ▸ memLp_finsetSum _ fun i _ => hg i, ?_⟩
  have hgi : ∀ i j, Integrable (fun ω => g i ω * g j ω) ν := fun i j =>
    (hg i).integrable_mul (hg j)
  have hfi : ∀ i j, Integrable (fun p => f i p * f j p) (ν.prod volume) := fun i j =>
    (hf i).integrable_mul (hf j)
  rw [hF, hG]
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hgi i j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hfi i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hgi i j, integral_finsetSum _ fun j _ => hfi i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [walsh_integral_pair hS (he.le_t i) (he.le_t j) (he.le_b i) (he.le_b j) (he.meas i)
    (he.meas j) (he.bdd i) (he.bdd j), walsh_integral_block_mul_block]

/-! ### Approximation of Walsh integrals by elementary ones -/

/-- The elementary integrand with one block `c 𝟙_{(s,t] × (a,b]}`. -/
def WalshElem.single (s t : ℝ≥0) (a b : ℝ) (c : Ω → ℝ) : WalshElem Ω :=
  ⟨1, fun _ => s, fun _ => t, fun _ => a, fun _ => b, fun _ => c⟩

/-- The concatenation of two elementary integrands (the sum of the integrands). -/
def WalshElem.append (e e' : WalshElem Ω) : WalshElem Ω :=
  ⟨e.k + e'.k, Fin.append e.s e'.s, Fin.append e.t e'.t, Fin.append e.a e'.a,
    Fin.append e.b e'.b, Fin.append e.c e'.c⟩

/-- The integrand of `WalshElem.single` is the block. -/
lemma WalshElem.field_single (s t : ℝ≥0) (a b : ℝ) (c : Ω → ℝ) :
    (WalshElem.single s t a b c).field =
      fun r y ω => if (s : ℝ) < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then c ω else 0 := by
  funext r y ω
  exact Fin.sum_univ_one (fun _ => if (s : ℝ) < r ∧ r ≤ t ∧ a < y ∧ y ≤ b then c ω else 0)

/-- The integral of `WalshElem.single` is `c ξ((s,t] × (a,b])`. -/
lemma WalshElem.value_single (s t : ℝ≥0) (a b : ℝ) (c : Ω → ℝ) (S : ℝ → ℝ → Ω → ℝ) :
    (WalshElem.single s t a b c).value S = fun ω => c ω * rectMass S s t a b ω := by
  funext ω
  exact Fin.sum_univ_one (fun _ => c ω * rectMass S s t a b ω)

/-- The integrand of a concatenation is the sum of the integrands. -/
lemma WalshElem.field_append (e e' : WalshElem Ω) (r y : ℝ) (ω : Ω) :
    (e.append e').field r y ω = e.field r y ω + e'.field r y ω := by
  exact (Fin.sum_univ_add (a := e.k) (b := e'.k) _).trans
    (by simp [WalshElem.field, WalshElem.append])

/-- The integral of a concatenation is the sum of the integrals. -/
lemma WalshElem.value_append (e e' : WalshElem Ω) (S : ℝ → ℝ → Ω → ℝ) (ω : Ω) :
    (e.append e').value S ω = e.value S ω + e'.value S ω := by
  exact (Fin.sum_univ_add (a := e.k) (b := e'.k) _).trans
    (by simp [WalshElem.value, WalshElem.append])

/-- A concatenation of adapted elementary integrands is adapted. -/
lemma WalshElem.IsAdapted.append {e e' : WalshElem Ω} (he : e.IsAdapted 𝓖)
    (he' : e'.IsAdapted 𝓖) : (e.append e').IsAdapted 𝓖 := by
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i => simpa [WalshElem.append] using he.le_t i
    | right i => simpa [WalshElem.append] using he'.le_t i
  · intro i
    induction i using Fin.addCases with
    | left i => simpa [WalshElem.append] using he.le_b i
    | right i => simpa [WalshElem.append] using he'.le_b i
  · intro i
    induction i using Fin.addCases with
    | left i =>
      have h1 : (e.append e').s (Fin.castAdd e'.k i) = e.s i := Fin.append_left _ _ _
      have h2 : (e.append e').c (Fin.castAdd e'.k i) = e.c i := Fin.append_left _ _ _
      rw [h1, h2]
      exact he.meas i
    | right i =>
      have h1 : (e.append e').s (Fin.natAdd e.k i) = e'.s i := Fin.append_right _ _ _
      have h2 : (e.append e').c (Fin.natAdd e.k i) = e'.c i := Fin.append_right _ _ _
      rw [h1, h2]
      exact he'.meas i
  · intro i
    induction i using Fin.addCases with
    | left i => simpa [WalshElem.append] using he.bdd i
    | right i => simpa [WalshElem.append] using he'.bdd i

/-- **Every Walsh integral is an `L²` limit of elementary integrals**, integrands and values
converging together. -/
theorem IsWalshIntegral.exists_elem_tendsto (hS : IsWhiteNoise 𝓖 S ν) {h : ℝ → ℝ → Ω → ℝ}
    {X : Ω → ℝ} (hX : IsWalshIntegral 𝓖 S ν h X) :
    ∃ e : ℕ → WalshElem Ω, (∀ j, (e j).IsAdapted 𝓖) ∧
      Tendsto (fun j => eLpNorm (uncurryField (e j).field - uncurryField h) 2 (ν.prod volume))
        atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm ((e j).value S - X) 2 ν) atTop (𝓝 0) := by
  -- `hS` is not needed: the approximation only uses the triangle inequality for `eLpNorm`.
  have := hS.isProbabilityMeasure
  clear this
  induction hX with
  | block s t a b c hst hab hc hbdd =>
    refine ⟨fun _ => WalshElem.single s t a b c,
      fun _ => ⟨fun _ => hst, fun _ => hab, fun _ => hc, fun _ => hbdd⟩, ?_, ?_⟩
    · simp [WalshElem.field_single]
    · simp [WalshElem.value_single]
  | add h h' X X' _ _ ih ih' =>
    obtain ⟨e, he, h1, h2⟩ := ih
    obtain ⟨e', he', h1', h2'⟩ := ih'
    refine ⟨fun j => (e j).append (e' j), fun j => (he j).append (he' j), ?_, ?_⟩
    · have hsplit : ∀ j, uncurryField ((e j).append (e' j)).field -
          uncurryField (fun r y ω => h r y ω + h' r y ω) =
          (uncurryField (e j).field - uncurryField h) +
            (uncurryField (e' j).field - uncurryField h') := by
        intro j
        funext p
        simp only [uncurryField, WalshElem.field_append, Pi.sub_apply, Pi.add_apply]
        ring
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using h1.add h1') (fun j => zero_le) (fun j => ?_)
      rw [hsplit]
      exact eLpNorm_add_le one_le_two
    · have hsplit : ∀ j, ((e j).append (e' j)).value S - (fun ω => X ω + X' ω) =
          ((e j).value S - X) + ((e' j).value S - X') := by
        intro j
        funext ω
        simp only [WalshElem.value_append, Pi.sub_apply, Pi.add_apply]
        ring
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using h2.add h2') (fun j => zero_le) (fun j => ?_)
      rw [hsplit]
      exact eLpNorm_add_le one_le_two
  | limit h X hs Xs _ _ _ hhs hXs ih =>
    choose e he h1 h2 using ih
    have hex : ∀ k : ℕ, ∃ j,
        eLpNorm (uncurryField (e k j).field - uncurryField (hs k)) 2 (ν.prod volume) <
          (k : ℝ≥0∞)⁻¹ ∧ eLpNorm ((e k j).value S - Xs k) 2 ν < (k : ℝ≥0∞)⁻¹ := by
      intro k
      have hk : (0 : ℝ≥0∞) < (k : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k)
      exact (((tendsto_order.1 (h1 k)).2 _ hk).and ((tendsto_order.1 (h2 k)).2 _ hk)).exists
    choose J hJ using hex
    refine ⟨fun k => e k (J k), fun k => he k (J k), ?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using ENNReal.tendsto_inv_nat_nhds_zero.add hhs) (fun k => zero_le)
        (fun k => ?_)
      calc eLpNorm (uncurryField (e k (J k)).field - uncurryField h) 2 (ν.prod volume)
          = eLpNorm ((uncurryField (e k (J k)).field - uncurryField (hs k)) +
              (uncurryField (hs k) - uncurryField h)) 2 (ν.prod volume) := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := eLpNorm_add_le one_le_two
        _ ≤ _ := by gcongr; exact (hJ k).1.le
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using ENNReal.tendsto_inv_nat_nhds_zero.add hXs) (fun k => zero_le)
        (fun k => ?_)
      calc eLpNorm ((e k (J k)).value S - X) 2 ν
          = eLpNorm (((e k (J k)).value S - Xs k) + (Xs k - X)) 2 ν := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := eLpNorm_add_le one_le_two
        _ ≤ _ := by gcongr; exact (hJ k).2.le

end QSSEPtoKPZ
