/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.WalshMart
public import QSSEPtoKPZ.Martingales.Doob
public import QSSEPtoKPZ.Checks
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# A continuous version of `t ↦ ξ((0,t] × (a,b])` (task G9)

The frozen definition `IsWhiteNoise` has no continuity clause. For the Walsh integral process to
have a continuous version, we need one for `B(t) = ξ((0,t] × (a,b])`, which has independent
Gaussian increments `B(t) - B(s) ~ N(0, (t-s)(b-a))`. We prove it by the argument of
Kolmogorov's continuity theorem (Mathlib has the definition `IsKolmogorovProcess` but not the
theorem):

* fourth moments: `𝔼[(B(t) - B(s))⁴] = K (t-s)² (b-a)²`;
* on the dyadic grid `t_{j,k} = k T / 2^j` of `[0, T]`, Markov's inequality and Borel–Cantelli
  give, almost surely, `|B(t_{j,k+1}) - B(t_{j,k})| ≤ (9/10)^j` for all `k` and all large `j`
  (`2^j · 4^{-j} · (10/9)^{4j}` is summable);
* chaining: then `|B(t_{j+i,k}) - B(t_{j,⌊k/2^i⌋})| ≤ 9 (9/10)^j`, so the values along the
  grid approximations of `t` converge, uniformly in `t`, to a continuous limit, which is a.s.
  equal to `B(t)` (Fatou).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- The fourth moment of the standard Gaussian, as a real number. -/
private def walshBMK : ℝ := (∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 1)).toReal

private lemma walshBM_fourth_ne_top : ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 1) ≠ ∞ := by
  have hi := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (p := 4)
    (by norm_num)
  have e : (fun x : ℝ => ENNReal.ofReal (x ^ 4)) = fun x => ENNReal.ofReal (‖id x‖ ^ 4) := by
    funext x
    simp [Real.norm_eq_abs, (by decide : Even 4).pow_abs]
  rw [e]
  exact (hi.lintegral_lt_top).ne

/-- `𝔼[X⁴] = K v²` for `X ~ N(0, v)`. -/
private lemma walshBM_fourth_moment {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) ν) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂ν = ENNReal.ofReal (walshBMK * (v : ℝ) ^ 2) := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 4) := by fun_prop
  rw [hX.lintegral_comp (f := fun x => ENNReal.ofReal (x ^ 4)) hmeas.aemeasurable]
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  rw [hmap, lintegral_map hmeas (measurable_const_mul _)]
  have e : ∀ x : ℝ, ENNReal.ofReal ((Real.sqrt v * x) ^ 4) =
      ENNReal.ofReal ((v : ℝ) ^ 2) * ENNReal.ofReal (x ^ 4) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, show Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 by ring, Real.sq_sqrt v.coe_nonneg]
  simp_rw [e]
  rw [lintegral_const_mul _ hmeas, ENNReal.ofReal_mul (by
    unfold walshBMK; exact ENNReal.toReal_nonneg), walshBMK,
    ENNReal.ofReal_toReal walshBM_fourth_ne_top, mul_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ}
  {ν : Measure Ω}

/-- The chaining estimate along the dyadic grid. -/
private lemma walshBM_chain {f : ℕ → ℕ → ℝ} {N : ℕ}
    (hdouble : ∀ j k, f (j + 1) (2 * k) = f j k)
    (hinc : ∀ j ≥ N, ∀ k < 2 ^ j, |f j (k + 1) - f j k| ≤ (9 / 10 : ℝ) ^ j) :
    ∀ i j, N ≤ j → ∀ k ≤ 2 ^ (j + i),
      |f (j + i) k - f j (k / 2 ^ i)| ≤ 9 * (9 / 10 : ℝ) ^ j - 9 * (9 / 10 : ℝ) ^ (j + i) := by
  intro i
  induction i with
  | zero => intro j _ k _; simp
  | succ i ih =>
    intro j hj k hk
    have hpow : 2 ^ (j + (i + 1)) = 2 * 2 ^ (j + i) := by
      rw [← pow_succ']
      rfl
    have hk' : k / 2 ≤ 2 ^ (j + i) := by
      rw [hpow] at hk
      generalize 2 ^ (j + i) = X at hk ⊢
      omega
    have h1 : |f (j + (i + 1)) k - f (j + i) (k / 2)| ≤ (9 / 10 : ℝ) ^ (j + (i + 1)) := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · have : k / 2 = m := by omega
        rw [this, show k = 2 * m by omega, show j + (i + 1) = (j + i) + 1 by ring, hdouble,
          sub_self, abs_zero]
        positivity
      · have h2 : k / 2 = m := by omega
        rw [h2, hm, show j + (i + 1) = (j + i) + 1 by ring, ← hdouble (j + i) m]
        refine hinc _ (by omega) _ ?_
        have : 2 * m + 1 ≤ 2 * 2 ^ (j + i) := by rw [← hm, ← hpow]; exact hk
        rw [pow_succ]
        generalize 2 ^ (j + i) = X at this ⊢
        omega
    have h3 := ih j hj (k / 2) hk'
    have hdiv : k / 2 / 2 ^ i = k / 2 ^ (i + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    rw [hdiv] at h3
    have hp : (9 / 10 : ℝ) ^ (j + (i + 1)) = (9 / 10 : ℝ) ^ (j + i) * (9 / 10) := by
      rw [← pow_succ]
      rfl
    calc |f (j + (i + 1)) k - f j (k / 2 ^ (i + 1))|
        ≤ |f (j + (i + 1)) k - f (j + i) (k / 2)| + |f (j + i) (k / 2) - f j (k / 2 ^ (i + 1))| :=
          abs_sub_le _ _ _
      _ ≤ (9 / 10 : ℝ) ^ (j + (i + 1)) +
          (9 * (9 / 10 : ℝ) ^ j - 9 * (9 / 10 : ℝ) ^ (j + i)) := add_le_add h1 h3
      _ = 9 * (9 / 10 : ℝ) ^ j - 9 * (9 / 10 : ℝ) ^ (j + (i + 1)) := by rw [hp]; ring

/-- **Continuous version of `t ↦ ξ((0,t] × (a,b])`** on `[0, T]`: there is `W`, with every path
continuous on `[0, T]`, such that `W(u) = ξ((0,u] × (a,b])` almost surely for each
`u ∈ [0, T]`. -/
theorem walshProc_exists_cont_rect (hS : IsWhiteNoise 𝓖 S ν) (T a b : ℝ) (hab : a ≤ b) :
    ∃ W : ℝ → Ω → ℝ, (∀ ω, ContinuousOn (fun u => W u ω) (Set.Icc 0 T)) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) T, W u =ᵐ[ν] rectMass S 0 u a b := by
  have : IsProbabilityMeasure ν := hS.isProbabilityMeasure
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨fun _ _ => 0, fun _ => continuousOn_const, fun u hu => ae_of_all _ fun ω => ?_⟩
    have : u = 0 := le_antisymm (hu.2.trans hT) hu.1
    subst this
    simp [rectMass]
  -- notation
  set τ : ℝ≥0 := T.toNNReal with hτ
  have hτT : (τ : ℝ) = T := Real.coe_toNNReal _ hT.le
  set V : ℝ → Ω → ℝ := fun u => rectMass S 0 u a b with hV
  set f : Ω → ℕ → ℕ → ℝ := fun ω j k => V (gridPt τ j k) ω with hf
  set lam : ℝ := 9 / 10 with hlam
  have hV_meas : ∀ u : ℝ≥0, Measurable (V u) := fun u =>
    (prodNoise_meas_rect hS (zero_le (a := u)) le_rfl a b).mono (𝓖.le u) le_rfl
  have hdouble : ∀ ω j k, f ω (j + 1) (2 * k) = f ω j k := by
    intro ω j k
    simp only [hf, gridPt_double]
  -- the increments
  have hinc_eq : ∀ j k ω, f ω j (k + 1) - f ω j k =
      rectMass S (gridPt τ j k) (gridPt τ j (k + 1)) a b ω := by
    intro j k ω
    simp only [hf, hV, rectMass]
    ring
  have hvar : ∀ j k, k < 2 ^ j →
      (((gridPt τ j (k + 1) - gridPt τ j k) * (b - a).toNNReal : ℝ≥0) : ℝ) =
        T / 2 ^ j * (b - a) := by
    intro j k hk
    have h1 : min (k + 1) (2 ^ j) = k + 1 := min_eq_left hk
    have h2 : min k (2 ^ j) = k := min_eq_left hk.le
    rw [NNReal.coe_mul, NNReal.coe_sub (gridPt_mono τ j (Nat.le_succ k)),
      Real.coe_toNNReal _ (sub_nonneg.2 hab)]
    simp only [gridPt, h1, h2, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_pow, NNReal.coe_ofNat, hτT]
    push_cast
    ring
  -- Markov and the bad events
  set E : ℕ → Set Ω := fun j => ⋃ k ∈ Finset.range (2 ^ j),
    {ω | ENNReal.ofReal (lam ^ (4 * j)) ≤ ENNReal.ofReal ((f ω j (k + 1) - f ω j k) ^ 4)}
    with hE
  have hEj : ∀ j, ν (E j) ≤ ENNReal.ofReal (walshBMK * (T * (b - a)) ^ 2 *
      (1 / (2 * lam ^ 4)) ^ j) := by
    intro j
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hk : ∀ k ∈ Finset.range (2 ^ j), ν {ω | ENNReal.ofReal (lam ^ (4 * j)) ≤
        ENNReal.ofReal ((f ω j (k + 1) - f ω j k) ^ 4)} ≤
        ENNReal.ofReal (walshBMK * (T / 2 ^ j * (b - a)) ^ 2 / lam ^ (4 * j)) := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hlaw := hS.gaussian _ _ a b (gridPt_mono τ j (Nat.le_succ k)) hab
      have hmom := walshBM_fourth_moment hlaw
      rw [hvar j k hk'] at hmom
      have hlpos : 0 < lam ^ (4 * j) := by positivity
      refine (meas_ge_le_lintegral_div ?_ (by simpa using hlpos)
        ENNReal.ofReal_ne_top).trans ?_
      · exact ((hV_meas _).sub (hV_meas _)).pow_const 4 |>.ennreal_ofReal.aemeasurable
      · simp_rw [hinc_eq j k]
        rw [hmom, ← ENNReal.ofReal_div_of_pos hlpos]
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hl : lam ≠ 0 := by rw [hlam]; norm_num
    have e1 : (1 / (2 * lam ^ 4)) ^ j = 1 / ((2 : ℝ) ^ j * lam ^ (4 * j)) := by
      rw [one_div_pow, mul_pow, ← pow_mul]
    rw [e1, Nat.cast_pow, Nat.cast_ofNat]
    have hP : (2 : ℝ) ^ j ≠ 0 := by positivity
    have hQ : lam ^ (4 * j) ≠ 0 := pow_ne_zero _ hl
    generalize (2 : ℝ) ^ j = P at hP ⊢
    generalize lam ^ (4 * j) = Q at hQ ⊢
    field_simp
  have hsum : ∑' j, ν (E j) ≠ ∞ := by
    have hq0 : (0 : ℝ) ≤ 1 / (2 * lam ^ 4) := by positivity
    have hq1 : 1 / (2 * lam ^ 4) < 1 := by rw [hlam]; norm_num
    have hs : Summable fun j : ℕ => walshBMK * (T * (b - a)) ^ 2 * (1 / (2 * lam ^ 4)) ^ j :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEj)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by
      have : 0 ≤ walshBMK := ENNReal.toReal_nonneg
      positivity) hs]
    exact ENNReal.ofReal_ne_top
  -- the good event
  set G : Set Ω := {ω | ∃ N, ∀ j ≥ N, ∀ k < 2 ^ j, |f ω j (k + 1) - f ω j k| ≤ lam ^ j}
    with hG
  have hGae : ∀ᵐ ω ∂ν, ω ∈ G := by
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    refine ⟨N, fun j hj k hk => ?_⟩
    have hnot := hN j hj
    simp only [hE, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, not_exists,
      not_le] at hnot
    have h := hnot k hk
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h
    have h' : |f ω j (k + 1) - f ω j k| ^ 4 < (lam ^ j) ^ 4 := by
      rw [show |f ω j (k + 1) - f ω j k| ^ 4 = (f ω j (k + 1) - f ω j k) ^ 4 by
        rw [(by decide : Even 4).pow_abs], show (lam ^ j) ^ 4 = lam ^ (4 * j) by
          rw [← pow_mul, mul_comm]]
      exact h
    exact (pow_lt_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num)).1 h' |>.le
  -- grid approximations of `t`
  set κ : ℕ → ℝ → ℕ := fun j t => ⌊2 ^ j * t / T⌋₊ with hκ
  have hκle : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j, κ j t ≤ 2 ^ j := fun t ht j =>
    (tendsto_gridPt hT.le ht).1 j
  have hκdiv : ∀ t j i, κ (j + i) t / 2 ^ i = κ j t := by
    intro t j i
    simp only [hκ]
    rw [← Nat.floor_div_natCast]
    congr 1
    push_cast
    rw [pow_add]
    field_simp
  have hκclose : ∀ s t : ℝ, ∀ j, |s - t| ≤ T / 2 ^ j → 0 ≤ s → 0 ≤ t → κ j s ≤ κ j t + 1 := by
    intro s t j hst hs ht
    simp only [hκ]
    rw [← Nat.floor_add_one (by positivity)]
    refine Nat.floor_le_floor ?_
    have : s - t ≤ T / 2 ^ j := (le_abs_self _).trans hst
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    rw [div_le_iff₀ hT]
    calc 2 ^ j * s = 2 ^ j * t + 2 ^ j * (s - t) := by ring
      _ ≤ 2 ^ j * t + 2 ^ j * (T / 2 ^ j) := by gcongr
      _ = (2 ^ j * t / T + 1) * T := by field_simp
  -- the chaining estimate for a good `ω`
  have hchain : ∀ ω ∈ G, ∃ N, ∀ j ≥ N, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      |f ω (j + i) (κ (j + i) t) - f ω j (κ j t)| ≤ 9 * lam ^ j := by
    intro ω hω
    obtain ⟨N, hN⟩ := hω
    refine ⟨N, fun j hj i t ht => ?_⟩
    have h := walshBM_chain (hdouble ω) hN i j hj (κ (j + i) t) (hκle t ht _)
    rw [hκdiv] at h
    exact h.trans (by have : 0 ≤ lam ^ (j + i) := by positivity
                      linarith)
  -- the limit
  have hcauchy : ∀ ω ∈ G, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ L, Tendsto (fun j => f ω j (κ j t)) atTop (𝓝 L) := by
    intro ω hω t ht
    obtain ⟨N, hN⟩ := hchain ω hω
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 9 by positivity)
      (show lam < 1 by rw [hlam]; norm_num)
    refine ⟨max N j, fun n hn => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Real.dist_eq]
    refine (hN _ (le_max_left _ _) i t ht).trans_lt ?_
    have : lam ^ max N j ≤ lam ^ j := pow_le_pow_of_le_one (by positivity)
      (by rw [hlam]; norm_num) (le_max_right _ _)
    linarith
  classical
  set W : ℝ → Ω → ℝ := fun t ω => if ω ∈ G ∧ t ∈ Set.Icc (0 : ℝ) T then
    limUnder atTop (fun j => f ω j (κ j t)) else 0 with hW
  have hWlim : ∀ ω ∈ G, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun j => f ω j (κ j t)) atTop (𝓝 (W t ω)) := by
    intro ω hω t ht
    obtain ⟨L, hL⟩ := hcauchy ω hω t ht
    simp only [hW, hω, ht, and_self, ite_true]
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  -- modulus of continuity
  have hmod : ∀ ω ∈ G, ∃ N, ∀ j ≥ N, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      |s - t| ≤ T / 2 ^ j → |W s ω - W t ω| ≤ 19 * lam ^ j := by
    intro ω hω
    obtain ⟨N, hN⟩ := hchain ω hω
    obtain ⟨N', hN'⟩ := id hω
    refine ⟨max N N', fun j hj s hs t ht hst => ?_⟩
    have hmid : |f ω j (κ j s) - f ω j (κ j t)| ≤ lam ^ j := by
      have h1 := hκclose s t j hst hs.1 ht.1
      have h2 := hκclose t s j (by rwa [abs_sub_comm]) ht.1 hs.1
      rcases Nat.lt_or_ge (κ j s) (κ j t) with h | h
      · have : κ j t = κ j s + 1 := by omega
        rw [this, abs_sub_comm]
        exact hN' j (le_of_max_le_right hj) _ (by have := hκle t ht j; omega)
      · rcases Nat.lt_or_ge (κ j t) (κ j s) with h' | h'
        · have : κ j s = κ j t + 1 := by omega
          rw [this]
          exact hN' j (le_of_max_le_right hj) _ (by have := hκle s hs j; omega)
        · have : κ j s = κ j t := le_antisymm h' h
          rw [this, sub_self, abs_zero]
          positivity
    have hlim := ((hWlim ω hω s hs).comp (tendsto_add_atTop_nat j)).sub
      ((hWlim ω hω t ht).comp (tendsto_add_atTop_nat j))
    refine le_of_tendsto (((continuous_abs.tendsto _).comp hlim)) (Eventually.of_forall
      fun i => ?_)
    simp only [Function.comp_apply]
    rw [add_comm i j]
    have h1 := hN j (le_of_max_le_left hj) i s hs
    have h2 := hN j (le_of_max_le_left hj) i t ht
    calc |f ω (j + i) (κ (j + i) s) - f ω (j + i) (κ (j + i) t)|
        ≤ |f ω (j + i) (κ (j + i) s) - f ω j (κ j s)| + |f ω j (κ j s) - f ω j (κ j t)| +
          |f ω j (κ j t) - f ω (j + i) (κ (j + i) t)| := by
          have := abs_sub_le (f ω (j + i) (κ (j + i) s)) (f ω j (κ j s)) (f ω (j + i) (κ (j + i) t))
          have := abs_sub_le (f ω j (κ j s)) (f ω j (κ j t)) (f ω (j + i) (κ (j + i) t))
          linarith
      _ ≤ 9 * lam ^ j + lam ^ j + 9 * lam ^ j := by
          rw [abs_sub_comm (f ω j (κ j t))] at *
          linarith
      _ = 19 * lam ^ j := by ring
  refine ⟨W, fun ω => ?_, fun u hu => ?_⟩
  · by_cases hω : ω ∈ G
    · obtain ⟨N, hN⟩ := hmod ω hω
      refine Metric.continuousOn_iff.2 fun t ht ε hε => ?_
      obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 19 by positivity)
        (show lam < 1 by rw [hlam]; norm_num)
      set j := max N j₀
      refine ⟨T / 2 ^ j, by positivity, fun s hs hst => ?_⟩
      rw [Real.dist_eq] at hst ⊢
      refine (hN j (le_max_left _ _) s hs t ht hst.le).trans_lt ?_
      have : lam ^ j ≤ lam ^ j₀ := pow_le_pow_of_le_one (by positivity)
        (by rw [hlam]; norm_num) (le_max_right _ _)
      linarith
    · have : (fun u => W u ω) = fun _ => 0 := by
        funext u
        simp [hW, hω]
      rw [this]
      exact continuousOn_const
  · -- `W u = V u` almost surely, by Fatou
    have hu' : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hu.1
    have hVu : Measurable (V u) := by
      have := hV_meas u.toNNReal
      rwa [hu'] at this
    obtain ⟨hκle', hgrid⟩ := tendsto_gridPt hT.le hu
    have hconv : ∀ᵐ ω ∂ν, Tendsto (fun j => f ω j (κ j u)) atTop (𝓝 (W u ω)) := by
      filter_upwards [hGae] with ω hω
      exact hWlim ω hω u hu
    have hWm : AEMeasurable (W u) ν :=
      aemeasurable_of_tendsto_metrizable_ae' (fun j => (hV_meas _).aemeasurable) hconv
    -- `𝔼[(B(t_j) - B(u))²] = (u - t_j)(b - a) → 0`
    have hle : ∀ j, gridPt τ j (κ j u) ≤ u.toNNReal := by
      intro j
      rw [← NNReal.coe_le_coe, hu']
      simp only [gridPt, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
        NNReal.coe_ofNat, hτT]
      have h2 : (0 : ℝ) < 2 ^ j := by positivity
      have hk : ((min (κ j u) (2 ^ j) : ℕ) : ℝ) ≤ 2 ^ j * u / T := by
        refine (Nat.cast_le.2 (min_le_left _ _)).trans ?_
        exact Nat.floor_le (by have := hu.1; positivity)
      calc ((min (κ j u) (2 ^ j) : ℕ) : ℝ) / 2 ^ j * T ≤ (2 ^ j * u / T) / 2 ^ j * T := by
            gcongr
        _ = u := by field_simp
    have hsq : ∀ j, ∫⁻ ω, ENNReal.ofReal ((f ω j (κ j u) - V u ω) ^ 2) ∂ν =
        ENNReal.ofReal ((u - gridPt τ j (κ j u)) * (b - a)) := by
      intro j
      have e : ∀ ω, (f ω j (κ j u) - V u ω) ^ 2 =
          rectMass S (gridPt τ j (κ j u)) u.toNNReal a b ω ^ 2 := by
        intro ω
        simp only [hf, hV, rectMass, hu']
        ring
      simp_rw [e]
      have hint : Integrable (fun ω => rectMass S (gridPt τ j (κ j u)) u.toNNReal a b ω ^ 2) ν :=
        (hS.gaussian _ _ a b (hle j) hab).hasGaussianLaw.memLp_two.integrable_sq
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _),
        integral_sq_rectMass hS (hle j) hab, hu']
    have hlim0 : Tendsto (fun j => ∫⁻ ω, ENNReal.ofReal ((f ω j (κ j u) - V u ω) ^ 2) ∂ν)
        atTop (𝓝 0) := by
      simp_rw [hsq]
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have : Tendsto (fun j => (u - (gridPt τ j (κ j u) : ℝ)) * (b - a)) atTop
          (𝓝 ((u - u) * (b - a))) := (tendsto_const_nhds.sub hgrid).mul tendsto_const_nhds
      simpa using this
    have hmeas_j : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal ((f ω j (κ j u) - V u ω) ^ 2)) ν :=
      fun j => (((hV_meas _).sub hVu).pow_const 2).ennreal_ofReal.aemeasurable
    have hfatou := lintegral_liminf_le' (u := atTop) hmeas_j
    have hcongr : (fun ω => liminf (fun j => ENNReal.ofReal ((f ω j (κ j u) - V u ω) ^ 2)) atTop)
        =ᵐ[ν] fun ω => ENNReal.ofReal ((W u ω - V u ω) ^ 2) := by
      filter_upwards [hconv] with ω hω
      exact ((ENNReal.continuous_ofReal.tendsto _).comp
        (((hω.sub tendsto_const_nhds).pow 2))).liminf_eq
    rw [lintegral_congr_ae hcongr, hlim0.liminf_eq] at hfatou
    have h0 : ∫⁻ ω, ENNReal.ofReal ((W u ω - V u ω) ^ 2) ∂ν = 0 := le_antisymm hfatou zero_le
    have hae : AEMeasurable (fun ω => ENNReal.ofReal ((W u ω - V u ω) ^ 2)) ν :=
      ((hWm.sub hVu.aemeasurable).pow_const 2).ennreal_ofReal
    rw [lintegral_eq_zero_iff' hae] at h0
    filter_upwards [h0] with ω hω
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
    have : (W u ω - V u ω) ^ 2 = 0 := le_antisymm hω (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

end QSSEPtoKPZ
