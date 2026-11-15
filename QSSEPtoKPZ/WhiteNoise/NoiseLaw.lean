/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# The noise coordinates and their law (task G5)

Interface statements of task I0″ of Stage 4, proved by task G5. See `docs/stage4-design.md`,
Sections 1.2 (h) and 3.3, and `docs/stage4-interfaces.md`.

Method: a grid `(T j, T (j+1)] × (X k, X (k+1)]` built from the finitely many corners at hand;
every rectangle with corners on the grid is a signed sum of cells (`rectMass_eq_noiseGridRect`),
and the cells are independent centred Gaussians, jointly independent of `𝓖 (T 0)`
(`IsWhiteNoise.measure_inter_noiseCells`, by induction over the time slabs: `indep` inside a
slab, `indep_past` across slabs). The finite-dimensional laws of `noiseMap` are then images of
a fixed product of Gaussians, and the law of `noiseMap` is determined by them (Mathlib's
`IsProjectiveLimit.unique`).

`noiseMap S ω : ℝ≥0 × ℝ × ℝ → ℝ`, `(t, a, b) ↦ ξ((0,t] × (a,b])`, with the product σ-algebra on
the function space. Its law is the same for all white noises (finite families of rectangle
masses are linear images of grids of independent centred Gaussian cells). `noiseSheet S` is the
"rectified" distribution function `(t, x) ↦ ξ((0,t] × (0,x])` (signed): it has the same rectangle
masses as `S` and is a function of the noise coordinates, whereas the values of `S` on the axes
(`S(0,x)`, `S(t,0)`) are not determined by the noise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The canonical noise coordinates: `(t, a, b) ↦ ξ((0,t] × (a,b]) = rectMass S 0 t a b`. -/
def noiseMap (S : ℝ → ℝ → Ω → ℝ) (ω : Ω) : ℝ≥0 × ℝ × ℝ → ℝ :=
  fun p => rectMass S 0 p.1 p.2.1 p.2.2 ω

/-- The rectified distribution function `ξ((0,t] × (0,x])` (signed). -/
def noiseSheet (S : ℝ → ℝ → Ω → ℝ) : ℝ → ℝ → Ω → ℝ := fun t x ω => rectMass S 0 t 0 x ω

/-- `noiseSheet S` has the same rectangle masses as `S`. -/
theorem rectMass_noiseSheet (S : ℝ → ℝ → Ω → ℝ) (s t a b : ℝ) (ω : Ω) :
    rectMass (noiseSheet S) s t a b ω = rectMass S s t a b ω := by
  simp only [rectMass, noiseSheet]
  ring

/-- `noiseSheet S` has the same noise coordinates as `S`. -/
theorem noiseMap_noiseSheet (S : ℝ → ℝ → Ω → ℝ) : noiseMap (noiseSheet S) = noiseMap S := by
  funext ω p
  exact rectMass_noiseSheet S 0 p.1 p.2.1 p.2.2 ω

variable {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}

/-! ### Grids of cells

For nondecreasing sequences `T : ℕ → ℝ≥0` (times) and `X : ℕ → ℝ` (space), the cells are the
rectangles `(T j, T (j+1)] × (X k, X (k+1)]`; every rectangle with corners on the grid is a
signed sum of cells (`rectMass_eq_noiseGridRect`, pure algebra), and for a white noise the
cells are independent centred Gaussians, jointly independent of `𝓖 (T 0)`
(`IsWhiteNoise.measure_inter_noiseCells`). -/

/-- The masses of the cells `(T j, T (j+1)] × (X k, X (k+1)]`, `j < m`, `k < n`. -/
def noiseCells (S : ℝ → ℝ → Ω → ℝ) (T : ℕ → ℝ≥0) (X : ℕ → ℝ) (m n : ℕ) (ω : Ω) :
    Fin m × Fin n → ℝ :=
  fun q => rectMass S (T q.1) (T ((q.1 : ℕ) + 1)) (X q.2) (X ((q.2 : ℕ) + 1)) ω

/-- Partial sums of a grid: `∑_{j' < j, k' < k} c (j', k')`, the cells outside
`Fin m × Fin n` counting `0`. -/
def noiseGridSum {m n : ℕ} (c : Fin m × Fin n → ℝ) (j k : ℕ) : ℝ :=
  ∑ j' ∈ Finset.range j, ∑ k' ∈ Finset.range k,
    if h : j' < m ∧ k' < n then c (⟨j', h.1⟩, ⟨k', h.2⟩) else 0

/-- The mass of the rectangle `(T j₁, T j₂] × (X k, X l]` as a function of the cells. -/
def noiseGridRect {m n : ℕ} (c : Fin m × Fin n → ℝ) (j₁ j₂ k l : ℕ) : ℝ :=
  noiseGridSum c j₂ l - noiseGridSum c j₂ k - noiseGridSum c j₁ l + noiseGridSum c j₁ k

/-- `c ↦ noiseGridRect c j₁ j₂ k l` is measurable (it is linear). -/
theorem measurable_noiseGridRect (m n j₁ j₂ k l : ℕ) :
    Measurable fun c : Fin m × Fin n → ℝ => noiseGridRect c j₁ j₂ k l := by
  have hsum : ∀ j k, Measurable fun c : Fin m × Fin n → ℝ => noiseGridSum c j k := by
    intro j k
    refine Finset.measurable_sum _ fun j' _ => Finset.measurable_sum _ fun k' _ => ?_
    by_cases h : j' < m ∧ k' < n
    · simp only [h, and_self, dite_true]
      exact measurable_pi_apply _
    · simp only [h, dite_false]
      exact measurable_const
  exact (((hsum j₂ l).sub (hsum j₂ k)).sub (hsum j₁ l)).add (hsum j₁ k)

/-- Telescoping in time and space: `noiseGridSum` of the cells is the mass of
`(T 0, T j] × (X 0, X k]`. -/
private theorem noiseGridSum_noiseCells (S : ℝ → ℝ → Ω → ℝ) (T : ℕ → ℝ≥0) (X : ℕ → ℝ)
    {m n j k : ℕ} (hj : j ≤ m) (hk : k ≤ n) (ω : Ω) :
    noiseGridSum (noiseCells S T X m n ω) j k = rectMass S (T 0) (T j) (X 0) (X k) ω := by
  have e1 : noiseGridSum (noiseCells S T X m n ω) j k = ∑ j' ∈ Finset.range j,
      ∑ k' ∈ Finset.range k, rectMass S (T j') (T (j' + 1)) (X k') (X (k' + 1)) ω := by
    refine Finset.sum_congr rfl fun j' hj' => Finset.sum_congr rfl fun k' hk' => ?_
    have h : j' < m ∧ k' < n :=
      ⟨(Finset.mem_range.1 hj').trans_le hj, (Finset.mem_range.1 hk').trans_le hk⟩
    simp only [h, and_self, dite_true, noiseCells]
  have e2 : ∀ j', ∑ k' ∈ Finset.range k, rectMass S (T j') (T (j' + 1)) (X k') (X (k' + 1)) ω
      = rectMass S (T j') (T (j' + 1)) (X 0) (X k) ω := by
    intro j'
    set Q := fun k' => rectMass S (T j') (T (j' + 1)) (X 0) (X k') ω
    calc _ = ∑ k' ∈ Finset.range k, (Q (k' + 1) - Q k') :=
          Finset.sum_congr rfl fun k' _ => by simp only [Q, rectMass]; ring
      _ = Q k - Q 0 := Finset.sum_range_sub Q k
      _ = _ := by simp only [Q, rectMass]; ring
  rw [e1, Finset.sum_congr rfl fun j' _ => e2 j']
  set Q := fun j' => rectMass S (T 0) (T j') (X 0) (X k) ω
  calc _ = ∑ j' ∈ Finset.range j, (Q (j' + 1) - Q j') :=
        Finset.sum_congr rfl fun j' _ => by simp only [Q, rectMass]; ring
    _ = Q j - Q 0 := Finset.sum_range_sub Q j
    _ = _ := by simp only [Q, rectMass]; ring

/-- **Grid decomposition** (algebra): the mass of `(T j₁, T j₂] × (X k, X l]` is a signed sum of
cells. -/
theorem rectMass_eq_noiseGridRect (S : ℝ → ℝ → Ω → ℝ) (T : ℕ → ℝ≥0) (X : ℕ → ℝ)
    {m n j₁ j₂ k l : ℕ} (hj₁ : j₁ ≤ m) (hj₂ : j₂ ≤ m) (hk : k ≤ n) (hl : l ≤ n) (ω : Ω) :
    rectMass S (T j₁) (T j₂) (X k) (X l) ω = noiseGridRect (noiseCells S T X m n ω) j₁ j₂ k l := by
  simp only [noiseGridRect, noiseGridSum_noiseCells S T X hj₁ hk,
    noiseGridSum_noiseCells S T X hj₁ hl, noiseGridSum_noiseCells S T X hj₂ hk, noiseGridSum_noiseCells S T X hj₂ hl, rectMass]
  ring

/-- A nondecreasing enumeration `T : ℕ → α` of a finite nonempty set `s`, starting from its
minimum and reaching every point of `s` before time `s.card`. -/
theorem noiseEnum_exists {α : Type*} [LinearOrder α] (s : Finset α) (hs : s.Nonempty) :
    ∃ T : ℕ → α, Monotone T ∧ T 0 = s.min' hs ∧ ∀ x ∈ s, ∃ j < s.card, T j = x := by
  have hc : 0 < s.card := hs.card_pos
  let e := s.orderEmbOfFin rfl
  refine ⟨fun j => e ⟨min j (s.card - 1), by omega⟩, fun i j hij => e.monotone ?_, ?_,
    fun x hx => ?_⟩
  · simp only [Fin.mk_le_mk]; omega
  · simp only [Nat.zero_min]
    exact Finset.orderEmbOfFin_zero rfl hc
  · have hx' : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨i, rfl⟩ := hx'
    refine ⟨i, i.2, ?_⟩
    have : min (i : ℕ) (s.card - 1) = i := by have := i.2; omega
    simp only [this, Fin.eta]

/-- Rectangle masses with times `≤ u` are `𝓖 u`-measurable. -/
theorem IsWhiteNoise.measurable_rectMass_noise_le (hS : IsWhiteNoise 𝓖 S ν) {s t u : ℝ≥0}
    (hs : s ≤ u) (ht : t ≤ u) (a b : ℝ) : Measurable[𝓖 u] (rectMass S s t a b) := by
  have h1 : ∀ x, Measurable[𝓖 u] (S t x) := fun x => (hS.adapted t x).mono (𝓖.mono ht) le_rfl
  have h2 : ∀ x, Measurable[𝓖 u] (S s x) := fun x => (hS.adapted s x).mono (𝓖.mono hs) le_rfl
  exact (((h1 b).sub (h1 a)).sub (h2 b)).add (h2 a)

/-- The noise coordinates `ξ((0,u] × (a,b])`, `u ≤ t`, are `𝓖 t`-measurable. -/
theorem IsWhiteNoise.measurable_noiseCoord_le (hS : IsWhiteNoise 𝓖 S ν) {u t : ℝ≥0}
    (hu : u ≤ t) (a b : ℝ) : Measurable[𝓖 t] (rectMass S 0 u a b) := by
  simpa using hS.measurable_rectMass_noise_le (zero_le : (0 : ℝ≥0) ≤ t) hu a b

/-- Rectangle masses are measurable. -/
theorem IsWhiteNoise.measurable_rectMass_noise (hS : IsWhiteNoise 𝓖 S ν) (s t : ℝ≥0) (a b : ℝ) :
    Measurable (rectMass S s t a b) :=
  (hS.measurable_rectMass_noise_le (le_max_left s t) (le_max_right s t) a b).mono (𝓖.le _) le_rfl

/-- The masses of the cells `(s,t] × (X k, X (k+1)]` of one time slab are independent. -/
private theorem IsWhiteNoise.measure_inter_slab (hS : IsWhiteNoise 𝓖 S ν) {s t : ℝ≥0}
    (hst : s ≤ t) {X : ℕ → ℝ} (hX : Monotone X) (n : ℕ) {B : ℕ → Set ℝ}
    (hB : ∀ k, MeasurableSet (B k)) :
    ν (⋂ k ∈ Finset.range n, rectMass S s t (X k) (X (k + 1)) ⁻¹' B k) =
      ∏ k ∈ Finset.range n, ν (rectMass S s t (X k) (X (k + 1)) ⁻¹' B k) := by
  have hind := hS.indep s t hst n (fun i : Fin (n + 1) => X i) (fun i j hij => hX hij)
  have := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun i : Fin n => B i)
    (fun i _ => hB i)
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  rw [Finset.prod_range (fun k => ν (rectMass S s t (X k) (X (k + 1)) ⁻¹' B k)), ← this]
  congr 1
  ext ω
  simp [Fin.forall_iff]

/-- The cells of a grid are independent, and independent of `𝓖 (T 0)` (indexed by `ℕ`). -/
private theorem IsWhiteNoise.measure_inter_grid (hS : IsWhiteNoise 𝓖 S ν) {T : ℕ → ℝ≥0}
    (hT : Monotone T) {X : ℕ → ℝ} (hX : Monotone X) (n : ℕ) {B : ℕ → ℕ → Set ℝ}
    (hB : ∀ j k, MeasurableSet (B j k)) {G : Set Ω} (hG : MeasurableSet[𝓖 (T 0)] G) (m : ℕ) :
    ν (G ∩ ⋂ j ∈ Finset.range m, ⋂ k ∈ Finset.range n,
        rectMass S (T j) (T (j + 1)) (X k) (X (k + 1)) ⁻¹' B j k) =
      ν G * ∏ j ∈ Finset.range m, ∏ k ∈ Finset.range n,
        ν (rectMass S (T j) (T (j + 1)) (X k) (X (k + 1)) ⁻¹' B j k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one, Finset.set_biInter_insert,
      Finset.prod_insert Finset.notMem_range_self]
    set E := ⋂ k ∈ Finset.range n, rectMass S (T m) (T (m + 1)) (X k) (X (k + 1)) ⁻¹' B m k
    set H := ⋂ j ∈ Finset.range m, ⋂ k ∈ Finset.range n,
        rectMass S (T j) (T (j + 1)) (X k) (X (k + 1)) ⁻¹' B j k
    have hE : MeasurableSet[⨆ (a : ℝ) (b : ℝ),
        MeasurableSpace.comap (rectMass S (T m) (T (m + 1)) a b) inferInstance] E := by
      refine Finset.measurableSet_biInter _ fun k _ => ?_
      exact le_iSup₂ (f := fun a b => MeasurableSpace.comap
        (rectMass S (T m) (T (m + 1)) a b) (inferInstance : MeasurableSpace ℝ)) (X k) (X (k + 1))
        _ ⟨B m k, hB m k, rfl⟩
    have hH : MeasurableSet[𝓖 (T m)] (G ∩ H) := by
      refine (𝓖.mono (hT (Nat.zero_le m)) _ hG).inter ?_
      refine Finset.measurableSet_biInter _ fun j hj => Finset.measurableSet_biInter _ fun k _ => ?_
      have hj' : j + 1 ≤ m := Finset.mem_range.1 hj
      exact hS.measurable_rectMass_noise_le (hT (by omega)) (hT hj') _ _ (hB j k)
    have hind := (Indep_iff _ _ _).1 (hS.indep_past (T m) (T (m + 1)) (hT m.le_succ)) E (G ∩ H)
      hE hH
    rw [show G ∩ (E ∩ H) = E ∩ (G ∩ H) by ext; simp only [Set.mem_inter_iff]; tauto, hind, ih,
      hS.measure_inter_slab (hT m.le_succ) hX n (hB m)]
    ring

/-- **Independence of the cells**: for `G ∈ 𝓖 (T 0)`,
`ν(G ∩ {cells ∈ ∏ B_q}) = ν(G) ∏_q ν(cell_q ∈ B_q)`. -/
theorem IsWhiteNoise.measure_inter_noiseCells (hS : IsWhiteNoise 𝓖 S ν) {T : ℕ → ℝ≥0}
    (hT : Monotone T) {X : ℕ → ℝ} (hX : Monotone X) {m n : ℕ} {G : Set Ω}
    (hG : MeasurableSet[𝓖 (T 0)] G) {B : Fin m × Fin n → Set ℝ} (hB : ∀ q, MeasurableSet (B q)) :
    ν (G ∩ noiseCells S T X m n ⁻¹' Set.univ.pi B) =
      ν G * ∏ q, ν ((fun ω => noiseCells S T X m n ω q) ⁻¹' B q) := by
  classical
  let B' : ℕ → ℕ → Set ℝ := fun j k =>
    if h : j < m ∧ k < n then B (⟨j, h.1⟩, ⟨k, h.2⟩) else Set.univ
  have hB' : ∀ j k, MeasurableSet (B' j k) := fun j k => by
    by_cases h : j < m ∧ k < n
    · simp only [B', h, and_self, dite_true]; exact hB _
    · simp only [B', h, dite_false]; exact MeasurableSet.univ
  have key := hS.measure_inter_grid hT hX n hB' hG m
  have hset : noiseCells S T X m n ⁻¹' Set.univ.pi B = ⋂ j ∈ Finset.range m,
      ⋂ k ∈ Finset.range n, rectMass S (T j) (T (j + 1)) (X k) (X (k + 1)) ⁻¹' B' j k := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Prod.forall,
      Fin.forall_iff, Set.mem_iInter, Finset.mem_range, noiseCells, B']
    constructor
    · intro h j hj k hk
      simpa [hj, hk] using h j hj k hk
    · intro h j hj k hk
      simpa [hj, hk] using h j hj k hk
  rw [hset, key]
  congr 1
  rw [Fintype.prod_prod_type, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [B', noiseCells, j.2, k.2]

/-- Cells are measurable. -/
theorem IsWhiteNoise.measurable_noiseCells (hS : IsWhiteNoise 𝓖 S ν) (T : ℕ → ℝ≥0) (X : ℕ → ℝ)
    (m n : ℕ) : Measurable (noiseCells S T X m n) :=
  Measurable.of_eval fun _ => hS.measurable_rectMass_noise _ _ _ _

/-- **Law of the cells**: independent centred Gaussians with variances the areas. -/
theorem IsWhiteNoise.map_noiseCells (hS : IsWhiteNoise 𝓖 S ν) {T : ℕ → ℝ≥0} (hT : Monotone T)
    {X : ℕ → ℝ} (hX : Monotone X) (m n : ℕ) :
    ν.map (noiseCells S T X m n) = Measure.pi fun q : Fin m × Fin n =>
      gaussianReal 0 ((T ((q.1 : ℕ) + 1) - T q.1) * (X ((q.2 : ℕ) + 1) - X q.2).toNNReal) := by
  have : IsProbabilityMeasure ν := (hS.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure
  refine (Measure.pi_eq fun B hB => ?_).symm
  rw [Measure.map_apply (hS.measurable_noiseCells T X m n) (MeasurableSet.univ_pi hB)]
  have := hS.measure_inter_noiseCells hT hX (G := Set.univ) MeasurableSet.univ hB
  rw [Set.univ_inter, measure_univ, one_mul] at this
  rw [this]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hlaw := hS.gaussian (T q.1) (T ((q.1 : ℕ) + 1)) (X q.2) (X ((q.2 : ℕ) + 1))
    (hT (Nat.le_succ _)) (hX (Nat.le_succ _))
  rw [← hlaw.map_eq, Measure.map_apply (hS.measurable_rectMass_noise _ _ _ _) (hB q)]
  rfl

/-- **Independence of the cells from the past**: the cells of a grid starting at `T 0` are
jointly independent of `𝓖 (T 0)`. -/
theorem IsWhiteNoise.indep_noiseCells (hS : IsWhiteNoise 𝓖 S ν) {T : ℕ → ℝ≥0} (hT : Monotone T)
    {X : ℕ → ℝ} (hX : Monotone X) (m n : ℕ) :
    Indep (MeasurableSpace.comap (noiseCells S T X m n) inferInstance) (𝓖 (T 0)) ν := by
  have : IsProbabilityMeasure ν := (hS.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure
  refine IndepSets.indep (hS.measurable_noiseCells T X m n).comap_le (𝓖.le _)
    ((isPiSystem_pi (α := fun _ : Fin m × Fin n => ℝ)).comap (noiseCells S T X m n))
    (@MeasurableSpace.isPiSystem_measurableSet Ω (𝓖 _))
    ?_ (@MeasurableSpace.generateFrom_measurableSet Ω (𝓖 _)).symm ?_
  · rw [← generateFrom_pi, MeasurableSpace.comap_generateFrom]
    rfl
  · rw [IndepSets_iff]
    rintro _ G ⟨_, ⟨B, hB, rfl⟩, rfl⟩ hG
    have hB' : ∀ q, MeasurableSet (B q) := fun q => hB q (Set.mem_univ q)
    have h1 := hS.measure_inter_noiseCells hT hX hG hB'
    have h2 := hS.measure_inter_noiseCells hT hX (G := Set.univ) MeasurableSet.univ hB'
    rw [Set.univ_inter, measure_univ, one_mul] at h2
    rw [Set.inter_comm, h1, h2, mul_comm]

/-! ### The law of the noise coordinates -/

/-- The noise coordinates are measurable (product σ-algebra on `ℝ≥0 × ℝ × ℝ → ℝ`). -/
theorem IsWhiteNoise.measurable_noiseMap (hS : IsWhiteNoise 𝓖 S ν) : Measurable (noiseMap S) :=
  Measurable.of_eval fun p => (hS.measurable_noiseCoord_le le_rfl p.2.1 p.2.2).mono (𝓖.le _) le_rfl

/-- Finite-dimensional laws of the noise coordinates through a grid: on a finite set `I` of
coordinates `(t, a, b)` with `t = T (j p)`, `a = X (k p)`, `b = X (l p)`, the law is the image of
the product of the Gaussian laws of the cells by a fixed linear map. -/
private theorem IsWhiteNoise.map_restrict_noiseMap (hS : IsWhiteNoise 𝓖 S ν) {T : ℕ → ℝ≥0}
    (hT : Monotone T) (hT0 : T 0 = 0) {X : ℕ → ℝ} (hX : Monotone X) {m n : ℕ}
    (I : Finset (ℝ≥0 × ℝ × ℝ)) (j k l : I → ℕ) (hj : ∀ p, j p ≤ m) (hk : ∀ p, k p ≤ n)
    (hl : ∀ p, l p ≤ n) (hTj : ∀ p, T (j p) = p.1.1) (hXk : ∀ p, X (k p) = p.1.2.1)
    (hXl : ∀ p, X (l p) = p.1.2.2) :
    ν.map (fun ω => I.restrict (noiseMap S ω)) =
      (Measure.pi fun q : Fin m × Fin n =>
        gaussianReal 0 ((T ((q.1 : ℕ) + 1) - T q.1) * (X ((q.2 : ℕ) + 1) - X q.2).toNNReal)).map
        (fun c (p : I) => noiseGridRect c 0 (j p) (k p) (l p)) := by
  have hΨ : Measurable fun (c : Fin m × Fin n → ℝ) (p : I) => noiseGridRect c 0 (j p) (k p) (l p) :=
    Measurable.of_eval fun p => measurable_noiseGridRect m n 0 (j p) (k p) (l p)
  have e : (fun ω => I.restrict (noiseMap S ω)) =
      (fun (c : Fin m × Fin n → ℝ) (p : I) => noiseGridRect c 0 (j p) (k p) (l p)) ∘
        noiseCells S T X m n := by
    funext ω p
    have := rectMass_eq_noiseGridRect S T X (Nat.zero_le m) (hj p) (hk p) (hl p) ω
    rw [hT0, hTj p, hXk p, hXl p, NNReal.coe_zero] at this
    exact this
  rw [e, ← Measure.map_map hΨ (hS.measurable_noiseCells T X m n), hS.map_noiseCells hT hX]

/-- **The law of the noise coordinates is the same for all white noises.** -/
theorem IsWhiteNoise.map_noiseMap_eq {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂}
    {S₁ : ℝ → ℝ → Ω₁ → ℝ} {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₁ : Measure Ω₁} {ν₂ : Measure Ω₂}
    (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂) :
    ν₁.map (noiseMap S₁) = ν₂.map (noiseMap S₂) := by
  have : IsProbabilityMeasure ν₁ := (h₁.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure
  have : IsProbabilityMeasure ν₂ := (h₂.gaussian 0 0 0 0 le_rfl le_rfl).isProbabilityMeasure
  have key : ∀ I : Finset (ℝ≥0 × ℝ × ℝ), ν₁.map (fun ω => I.restrict (noiseMap S₁ ω)) =
      ν₂.map (fun ω => I.restrict (noiseMap S₂ ω)) := by
    intro I
    classical
    set ts : Finset ℝ≥0 := insert 0 (I.image fun p => p.1)
    set xs : Finset ℝ := insert 0 (I.image (fun p => p.2.1) ∪ I.image fun p => p.2.2)
    obtain ⟨T, hT, hT0, hTs⟩ := noiseEnum_exists ts (Finset.insert_nonempty _ _)
    obtain ⟨X, hX, -, hXs⟩ := noiseEnum_exists xs (Finset.insert_nonempty _ _)
    have hT0' : T 0 = 0 := hT0.trans (le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
      zero_le)
    have hj : ∀ p : I, ∃ j < ts.card, T j = p.1.1 := fun p =>
      hTs _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ p.2))
    have hk : ∀ p : I, ∃ k < xs.card, X k = p.1.2.1 := fun p =>
      hXs _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ p.2)))
    have hl : ∀ p : I, ∃ l < xs.card, X l = p.1.2.2 := fun p =>
      hXs _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ p.2)))
    choose j hjm hTj using hj
    choose k hkn hXk using hk
    choose l hln hXl using hl
    rw [h₁.map_restrict_noiseMap hT hT0' hX I j k l (fun p => (hjm p).le) (fun p => (hkn p).le)
      (fun p => (hln p).le) hTj hXk hXl,
      h₂.map_restrict_noiseMap hT hT0' hX I j k l (fun p => (hjm p).le) (fun p => (hkn p).le)
      (fun p => (hln p).le) hTj hXk hXl]
  have hP₁ := isProjectiveLimit_map (P := ν₁) (X := fun p ω => noiseMap S₁ ω p)
    h₁.measurable_noiseMap.aemeasurable
  have hP₂ := isProjectiveLimit_map (P := ν₂) (X := fun p ω => noiseMap S₂ ω p)
    h₂.measurable_noiseMap.aemeasurable
  have hfam : (fun I : Finset (ℝ≥0 × ℝ × ℝ) => ν₁.map fun ω => I.restrict (noiseMap S₁ ω)) =
      fun I => ν₂.map fun ω => I.restrict (noiseMap S₂ ω) := funext key
  exact IsProjectiveLimit.unique (hfam ▸ hP₁) hP₂

end QSSEPtoKPZ
