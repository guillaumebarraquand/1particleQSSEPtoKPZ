/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.WhiteNoise.Prop72Calc
public import QSSEPtoKPZ.WhiteNoise.WalshIsometry
public import QSSEPtoKPZ.Tightness.TestFunctions
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Proposition 7.2, Step 3: time-dependent test functions (task J2)

Equation (7.12) in the form used by Step 4: given a white noise `ξ` (distribution function `S`)
on `Ω × Ω''` for which (7.11) holds for the simple integrands `𝟙_{(u,v]}(s) φ(y)`, `φ ∈ C_b³`
(the conclusion of `prop72_noise`), for every `φ ∈ C_b^{1,3}([0,T] × ℝ)` and `t ∈ [0,T]`:

  `M^φ(t) - M^φ(0) = ∫_0^t ∫_ℝ φ_s(y) Z(s,y) ξ(ds dy)`   (`prop72_walsh_timeDep`).

Proof (as in the article): with the grid `s_i = i t / N`, `i = 0, …, N`, the simple integrand
`φ^{(N)}(s,x) = ∑_i 𝟙_{(s_i, s_{i+1}]}(s) φ_{s_i}(x)` has the Walsh integral
`∑_i (M^{φ_{s_i}}(s_{i+1}) - M^{φ_{s_i}}(s_i))`, and
`M^φ(t) - M^φ(0) - ∑_i (M^{φ_{s_i}}(s_{i+1}) - M^{φ_{s_i}}(s_i))` is the sum of the increments of
the martingales `M^{φ - φ_{s_i}}` on `[s_i, s_{i+1}]` (linearity of `M^φ`). Instead of the
orthogonality of these increments, we use `(∑_{i<N} x_i)² ≤ N ∑ x_i²`: each increment has second
moment `𝔼 ∫_{s_i}^{s_{i+1}} ∫ Z² (φ_s - φ_{s_i})² ≤ L² δ² 𝔼 ∫_{s_i}^{s_{i+1}} ∫ Z²` (`L` a bound
of `∂ₛφ`, `δ = t/N`), so the total is `≤ N L² δ² 𝔼 ∫_0^T ∫ Z² = L² t² N⁻¹ 𝔼 ∫_0^T ∫ Z² → 0`.
On the integrand side, `|φ^{(N)} Z - φ Z| ≤ L δ |Z| 𝟙_{(0,t]}`, which tends to `0` in `L²`.
The closure rule of `IsWalshIntegral` concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-! ### The grid `s_i = i t / (k+1)` -/

/-- The grid point `s_i = i t / (k + 1)`. -/
private def prop72Grid (t : ℝ) (k i : ℕ) : ℝ := i * t / (k + 1)

private lemma prop72Grid_zero (t : ℝ) (k : ℕ) : prop72Grid t k 0 = 0 := by
  simp [prop72Grid]

private lemma prop72Grid_last (t : ℝ) (k : ℕ) : prop72Grid t k (k + 1) = t := by
  unfold prop72Grid
  push_cast
  field_simp

private lemma prop72Grid_mono {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : Monotone (prop72Grid t k) :=
  fun i j hij => by
    unfold prop72Grid
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) ht)
      (by positivity)

private lemma prop72Grid_succ_sub (t : ℝ) (k i : ℕ) :
    prop72Grid t k (i + 1) - prop72Grid t k i = t / (k + 1) := by
  unfold prop72Grid
  push_cast
  ring

private lemma prop72Grid_mem {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {i : ℕ} (hi : i ≤ k + 1) :
    prop72Grid t k i ∈ Set.Icc 0 t := by
  have h1 := prop72Grid_mono ht k (Nat.zero_le i)
  have h2 := prop72Grid_mono ht k hi
  rw [prop72Grid_zero] at h1
  rw [prop72Grid_last] at h2
  exact ⟨h1, h2⟩

/-! ### Elementary sums -/

/-- For a nondecreasing sequence `g`: if `|v_i - w| ≤ B` whenever `s ∈ (g_i, g_{i+1}]`, then
`|∑_{i<n} 𝟙_{(g_i, g_{i+1}]}(s) v_i - 𝟙_{(g_0, g_n]}(s) w| ≤ 𝟙_{(g_0, g_n]}(s) B`. -/
private lemma prop72_sum_ind_sub_le {g : ℕ → ℝ} (hg : Monotone g) {s w B : ℝ} {v : ℕ → ℝ}
    (n : ℕ) (hv : ∀ i < n, g i < s → s ≤ g (i + 1) → |v i - w| ≤ B) :
    |(∑ i ∈ Finset.range n, if g i < s ∧ s ≤ g (i + 1) then v i else 0) -
        (if g 0 < s ∧ s ≤ g n then w else 0)| ≤ if g 0 < s ∧ s ≤ g n then B else 0 := by
  induction n with
  | zero =>
    have : ¬ (g 0 < s ∧ s ≤ g 0) := fun h => absurd (h.1.trans_le h.2) (lt_irrefl _)
    simp [this]
  | succ n ih =>
    have ih := ih fun i hi => hv i (by omega)
    rw [Finset.sum_range_succ]
    by_cases hsn : s ≤ g n
    · have h1 : ¬ (g n < s ∧ s ≤ g (n + 1)) := fun h => absurd h.1 (not_lt.2 hsn)
      have h2 : (g 0 < s ∧ s ≤ g (n + 1)) ↔ (g 0 < s ∧ s ≤ g n) :=
        ⟨fun h => ⟨h.1, hsn⟩, fun h => ⟨h.1, h.2.trans (hg n.le_succ)⟩⟩
      simp only [h1, h2, ↓reduceIte, add_zero]
      exact ih
    · push Not at hsn
      have h0 : ¬ (g 0 < s ∧ s ≤ g n) := fun h => absurd h.2 (not_le.2 hsn)
      simp only [h0, ↓reduceIte, sub_zero] at ih
      rw [abs_nonpos_iff.1 ih, zero_add]
      have hg0 : g 0 < s := (hg (Nat.zero_le n)).trans_lt hsn
      by_cases hs1 : s ≤ g (n + 1)
      · simp only [hsn, hs1, hg0, and_self, ↓reduceIte]
        exact hv n n.lt_succ_self hsn hs1
      · simp [hs1]

/-- Superadditivity of the lower integral over finite sums (no measurability needed). -/
private lemma prop72_sum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (G : ℕ → α → ℝ≥0∞) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫⁻ x, G i x ∂μ ≤ ∫⁻ x, ∑ i ∈ Finset.range n, G i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    exact (add_le_add_left ih _).trans (le_lintegral_add _ _)

/-- `∑_{i<n} ∫⁻_{(g_i, g_{i+1}]} F = ∫⁻_{(g_0, g_n]} F` for a nondecreasing `g`. -/
private lemma prop72_sum_setLIntegral_Ioc {g : ℕ → ℝ} (hg : Monotone g) (F : ℝ → ℝ≥0∞)
    (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫⁻ s in Set.Ioc (g i) (g (i + 1)), F s =
      ∫⁻ s in Set.Ioc (g 0) (g n), F s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
      (Set.Ioc_disjoint_Ioc_of_le le_rfl),
      Set.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le n)) (hg n.le_succ)]

/-- `‖x‖ₑ² = (x²)` in `ℝ≥0∞`. -/
private lemma prop72_enorm_rpow_two (x : ℝ) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-! ### The second moment of the increments -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- For a martingale `N` with bracket (7.3) `∫_0^· ∫ Z² ψ²`, and `|ψ| ≤ B` on `(a,b] × ℝ`:
`𝔼 (N_b - N_a)² ≤ B² 𝔼 ∫_a^b ∫ Z²`. -/
private lemma prop72_lintegral_sq_incr_le {Pr : Measure Ω} [IsFiniteMeasure Pr]
    {𝒢 : Filtration ℝ≥0 mΩ} {T : ℝ} {N : ℝ → Ω → ℝ} {Z : ℝ → ℝ → Ω → ℝ} {ψ : ℝ → ℝ → ℝ}
    (h : HasBracket T 𝒢 N (limBracket Z ψ) Pr) {a b B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) (hψ : ∀ s ∈ Set.Ioc a b, ∀ x, |ψ s x| ≤ B) :
    ∫⁻ ω, ENNReal.ofReal ((N b ω - N a ω) ^ 2) ∂Pr ≤
      ENNReal.ofReal (B ^ 2) *
        ∫⁻ ω, (∫⁻ s in Set.Ioc a b, ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr := by
  have hb : 0 ≤ b := ha.trans hab
  have hMa : MemLp (N a) 2 Pr := h.memLp ⟨a, ha⟩ (hab.trans hbT)
  have hMb : MemLp (N b) 2 Pr := h.memLp ⟨b, hb⟩ hbT
  have hAa : Integrable (limBracket Z ψ a) Pr := h.integrable_bracket ⟨a, ha⟩ (hab.trans hbT)
  have hAb : Integrable (limBracket Z ψ b) Pr := h.integrable_bracket ⟨b, hb⟩ hbT
  have hpos : 0 ≤ᵐ[Pr] fun ω => limBracket Z ψ b ω - limBracket Z ψ a ω := by
    filter_upwards [h.mono] with ω hω
    exact sub_nonneg.2 (hω ⟨ha, hab.trans hbT⟩ ⟨hb, hbT⟩ hab)
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun ω => (N b ω - N a ω) ^ 2)
    (hMb.sub hMa).integrable_sq (ae_of_all _ fun ω => sq_nonneg _),
    prop72_integral_sq_incr h ha hab hbT,
    ofReal_integral_eq_lintegral_ofReal (f := fun ω => limBracket Z ψ b ω - limBracket Z ψ a ω)
      (hAb.sub hAa) hpos]
  calc ∫⁻ ω, ENNReal.ofReal (limBracket Z ψ b ω - limBracket Z ψ a ω) ∂Pr
      ≤ ∫⁻ ω, (∫⁻ s in Set.Ioc a b, ∫⁻ x, ‖Z s x ω ^ 2 * ψ s x ^ 2‖ₑ) ∂Pr :=
        lintegral_mono fun ω => prop72_ofReal_limBracket_sub_le Z ψ ha hab ω
    _ ≤ ∫⁻ ω, (∫⁻ s in Set.Ioc a b, ∫⁻ x,
          ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr := by
        refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioc fun s hs =>
          lintegral_mono fun x => ?_
        have h1 : ψ s x ^ 2 ≤ B ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hψ s hs x) 2
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity),
          ← ENNReal.ofReal_mul (sq_nonneg B)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (Z s x ω)])
    _ = _ := by simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **The `L²` estimate of Step 3**, for the grid `s_i = i t/(k+1)`:
`𝔼 (∑_i (M^{φ_{s_i}}(s_{i+1}) - M^{φ_{s_i}}(s_i)) - (M^φ(t) - M^φ(0)))² ≤
L² t² (k+1)⁻¹ 𝔼 ∫_0^T ∫ Z²`, where `|∂ₛφ| ≤ L`. -/
private lemma prop72_L2_bound {Pr : Measure Ω} [IsFiniteMeasure Pr] {𝒢 : Filtration ℝ≥0 mΩ}
    {T : ℝ} {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} {Z : ℝ → ℝ → Ω → ℝ}
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {φ φt : ℝ → ℝ → ℝ} {C : ℝ} (hφ : IsC13 T φ φt C) {L : ℝ}
    (hL : ∀ s ∈ Set.Icc 0 T, ∀ x, |φt s x| ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1),
        (limMart Y (fun _ => φ (prop72Grid t k i)) (fun _ _ => 0) (prop72Grid t k (i + 1)) ω -
          limMart Y (fun _ => φ (prop72Grid t k i)) (fun _ _ => 0) (prop72Grid t k i) ω) -
        (limMart Y φ φt t ω - limMart Y φ φt 0 ω)) ^ 2) ∂Pr ≤
      ENNReal.ofReal (L ^ 2 * t ^ 2 / (k + 1)) *
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr := by
  set a := prop72Grid t k with ha_def
  have ha0 : a 0 = 0 := prop72Grid_zero t k
  have halast : a (k + 1) = t := prop72Grid_last t k
  have hamono : Monotone a := prop72Grid_mono ht0 k
  have haT : ∀ i ∈ Finset.range (k + 1), a i ∈ Set.Icc 0 T ∧ a (i + 1) ∈ Set.Icc 0 T := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have h1 := prop72Grid_mem ht0 k (i := i) (by omega)
    have h2 := prop72Grid_mem ht0 k (i := i + 1) (by omega)
    exact ⟨⟨h1.1, h1.2.trans htT⟩, ⟨h2.1, h2.2.trans htT⟩⟩
  set N : ℕ → ℝ → Ω → ℝ :=
    fun i => limMart Y (fun s x => φ s x - φ (a i) x) (fun s x => φt s x - 0) with hN
  set G : ℕ → Ω → ℝ := fun i ω => N i (a (i + 1)) ω - N i (a i) ω with hG
  -- the difference is a sum of increments of the `M^{φ - φ_{s_i}}`
  have hD : ∀ ω, ((∑ i ∈ Finset.range (k + 1),
      (limMart Y (fun _ => φ (a i)) (fun _ _ => 0) (a (i + 1)) ω -
        limMart Y (fun _ => φ (a i)) (fun _ _ => 0) (a i) ω)) -
      (limMart Y φ φt t ω - limMart Y φ φt 0 ω)) ^ 2 =
      (∑ i ∈ Finset.range (k + 1), G i ω) ^ 2 := by
    intro ω
    have htel : limMart Y φ φt t ω - limMart Y φ φt 0 ω = ∑ i ∈ Finset.range (k + 1),
        (limMart Y φ φt (a (i + 1)) ω - limMart Y φ φt (a i) ω) := by
      rw [Finset.sum_range_sub (fun i => limMart Y φ φt (a i) ω), ha0, halast]
    have hsum : ∑ i ∈ Finset.range (k + 1), G i ω =
        (limMart Y φ φt t ω - limMart Y φ φt 0 ω) - ∑ i ∈ Finset.range (k + 1),
          (limMart Y (fun _ => φ (a i)) (fun _ _ => 0) (a (i + 1)) ω -
            limMart Y (fun _ => φ (a i)) (fun _ _ => 0) (a i) ω) := by
      rw [htel, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hs := hφ.prop72Slice (haT i hi).1
      simp only [hG, hN, prop72_limMart_sub Y hφ hs (haT i hi).1,
        prop72_limMart_sub Y hφ hs (haT i hi).2]
      ring
    rw [hsum]
    ring
  simp_rw [hD]
  have hNb : ∀ i ∈ Finset.range (k + 1),
      HasBracket T 𝒢 (N i) (limBracket Z (fun s x => φ s x - φ (a i) x)) Pr :=
    fun i hi => hmart (hφ.prop72Sub (hφ.prop72Slice (haT i hi).1))
  have hGm : ∀ i ∈ Finset.range (k + 1), MemLp (G i) 2 Pr := fun i hi =>
    ((hNb i hi).memLp ⟨a (i + 1), (haT i hi).2.1⟩ (haT i hi).2.2).sub
      ((hNb i hi).memLp ⟨a i, (haT i hi).1.1⟩ (haT i hi).1.2)
  set δ : ℝ := t / (k + 1) with hδ
  have hinc : ∀ i ∈ Finset.range (k + 1), ∫⁻ ω, ENNReal.ofReal (G i ω ^ 2) ∂Pr ≤
      ENNReal.ofReal ((L * δ) ^ 2) * ∫⁻ ω,
        (∫⁻ s in Set.Ioc (a i) (a (i + 1)), ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr := by
    intro i hi
    refine prop72_lintegral_sq_incr_le (hNb i hi) (haT i hi).1.1 (hamono i.le_succ)
      (haT i hi).2.2 fun s hs x => ?_
    have hsT : s ∈ Set.Icc 0 T := ⟨(haT i hi).1.1.trans hs.1.le, hs.2.trans (haT i hi).2.2⟩
    refine (hφ.prop72_abs_sub_le hL hsT (haT i hi).1 x).trans ?_
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL s hsT x)
    have : |s - a i| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hs.1]), hδ, ← prop72Grid_succ_sub t k i]
      linarith [hs.2]
    exact mul_le_mul_of_nonneg_left this hL0
  set K := ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr
  calc ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), G i ω) ^ 2) ∂Pr
      ≤ ∫⁻ ω, ENNReal.ofReal ((k + 1) * ∑ i ∈ Finset.range (k + 1), G i ω ^ 2) ∂Pr := by
        refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
        have := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1)) (f := fun i => G i ω)
        simpa using this
    _ = ENNReal.ofReal (k + 1) *
          ∑ i ∈ Finset.range (k + 1), ∫⁻ ω, ENNReal.ofReal (G i ω ^ 2) ∂Pr := by
        rw [← lintegral_finsetSum' _ fun i hi =>
          ((hGm i hi).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    _ ≤ ENNReal.ofReal (k + 1) * ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal ((L * δ) ^ 2) *
          ∫⁻ ω, (∫⁻ s in Set.Ioc (a i) (a (i + 1)), ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr := by
        gcongr with i hi
        exact hinc i hi
    _ ≤ ENNReal.ofReal (k + 1) * ENNReal.ofReal ((L * δ) ^ 2) *
          ∫⁻ ω, ∑ i ∈ Finset.range (k + 1),
            (∫⁻ s in Set.Ioc (a i) (a (i + 1)), ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr := by
        rw [← Finset.mul_sum, mul_assoc]
        gcongr
        exact prop72_sum_lintegral_le Pr _ _
    _ ≤ ENNReal.ofReal (k + 1) * ENNReal.ofReal ((L * δ) ^ 2) * K := by
        gcongr
        refine lintegral_mono fun ω => ?_
        rw [prop72_sum_setLIntegral_Ioc hamono, ha0, halast]
        exact lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT))
    _ = ENNReal.ofReal (L ^ 2 * t ^ 2 / (k + 1)) * K := by
        rw [← ENNReal.ofReal_mul (by positivity), hδ]
        congr 2
        field_simp

/-- **Proposition 7.2, Step 3, (7.12)**. Let `ξ` be a white noise (distribution function `S`)
on `Ω × Ω''` for a filtration `𝒢̄`, such that (7.11) holds for the simple integrands:
`∫∫ 𝟙_{(u,v]}(s) φ(y) Z(s,y) ξ(ds dy) = M^φ(v) - M^φ(u)` for `φ ∈ C_b³`, `0 ≤ u ≤ v ≤ T` (the
conclusion of `prop72_noise`). Then for `φ ∈ C_b^{1,3}([0,T] × ℝ)` and `t ∈ [0,T]`,
`∫_0^t ∫ φ_s(y) Z(s,y) ξ(ds dy) = M^φ(t) - M^φ(0)`. -/
theorem prop72_walsh_timeDep {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {𝒢 : Filtration ℝ≥0 mΩ} {T : ℝ} {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Z : ℝ → ℝ → Ω → ℝ}
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
    {𝒢b : Filtration ℝ≥0 (mΩ.prod m'')} {S : ℝ → ℝ → Ω × Ω'' → ℝ}
    (hS : IsWhiteNoise 𝒢b S (Pr.prod ν''))
    (hsimple : ∀ (φ : ℝ → ℝ) (C : ℝ), IsC13 T (fun _ => φ) (fun _ _ => 0) C →
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ T →
      IsWalshIntegral 𝒢b S (Pr.prod ν'')
        (fun s y ω => if u < s ∧ s ≤ v then φ y * Z s y ω.1 else 0)
        (fun ω => limMart Y (fun _ => φ) (fun _ _ => 0) v ω.1 -
          limMart Y (fun _ => φ) (fun _ _ => 0) u ω.1))
    {φ φt : ℝ → ℝ → ℝ} {C : ℝ} (hφ : IsC13 T φ φt C) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    IsWalshIntegral 𝒢b S (Pr.prod ν'')
      (fun s y ω => if 0 < s ∧ s ≤ t then φ s y * Z s y ω.1 else 0)
      (fun ω => limMart Y φ φt t ω.1 - limMart Y φ φt 0 ω.1) := by
  have hT : 0 ≤ T := ht0.trans htT
  obtain ⟨c, -, hc⟩ := hφ.bound
  have hL : ∀ s ∈ Set.Icc 0 T, ∀ x, |φt s x| ≤ c 1 := fun s hs x => (hc s hs x).2.1
  have hL0 : 0 ≤ c 1 := (abs_nonneg _).trans (hL 0 ⟨le_rfl, hT⟩ 0)
  have hφb : ∀ s ∈ Set.Icc 0 T, ∀ x, |φ s x| ≤ c 0 := fun s hs x => (hc s hs x).1
  have hc0 : 0 ≤ c 0 := (abs_nonneg _).trans (hφb 0 ⟨le_rfl, hT⟩ 0)
  set ν := Pr.prod ν'' with hν
  -- the approximating simple integrands and their integrals
  set hs : ℕ → ℝ → ℝ → Ω × Ω'' → ℝ := fun k s y ω => ∑ i ∈ Finset.range (k + 1),
    if prop72Grid t k i < s ∧ s ≤ prop72Grid t k (i + 1) then
      φ (prop72Grid t k i) y * Z s y ω.1 else 0 with hhs
  set Xs : ℕ → Ω × Ω'' → ℝ := fun k ω => ∑ i ∈ Finset.range (k + 1),
    (limMart Y (fun _ => φ (prop72Grid t k i)) (fun _ _ => 0) (prop72Grid t k (i + 1)) ω.1 -
      limMart Y (fun _ => φ (prop72Grid t k i)) (fun _ _ => 0) (prop72Grid t k i) ω.1)
    with hXs_def
  have hmemT : ∀ k, ∀ i ∈ Finset.range (k + 1), prop72Grid t k i ∈ Set.Icc 0 T ∧
      prop72Grid t k (i + 1) ∈ Set.Icc 0 T := by
    intro k i hi
    have hi' := Finset.mem_range.1 hi
    have h1 := prop72Grid_mem ht0 k (i := i) (by omega)
    have h2 := prop72Grid_mem ht0 k (i := i + 1) (by omega)
    exact ⟨⟨h1.1, h1.2.trans htT⟩, ⟨h2.1, h2.2.trans htT⟩⟩
  have hXs : ∀ k, IsWalshIntegral 𝒢b S ν (hs k) (Xs k) := fun k =>
    IsWalshIntegral.finset_sum _ fun i hi =>
      hsimple _ _ (hφ.prop72Slice (hmemT k i hi).1) _ _ (hmemT k i hi).1.1
        (prop72Grid_mono ht0 k i.le_succ) (hmemT k i hi).2.2
  -- the dominating field `𝟙_{(0,t]}(s) Z(s,y)`
  obtain ⟨C1, -, hC1⟩ := isC13_bumpTestRaw 0
  have hW := hsimple _ _ (hC1 T) 0 t le_rfl ht0 htT
  set W := uncurryField (fun s y (ω : Ω × Ω'') =>
    if 0 < s ∧ s ≤ t then bumpTestRaw 0 y * Z s y ω.1 else 0) with hWdef
  have hWm : MemLp W 2 (ν.prod volume) := (IsWalshIntegral.isometry_lib hS hW).1
  have hb1 : ∀ y, bumpTestRaw 0 y = 1 := fun y => rfl
  set h : ℝ → ℝ → Ω × Ω'' → ℝ := fun s y ω => if 0 < s ∧ s ≤ t then φ s y * Z s y ω.1 else 0
    with hh
  -- pointwise bounds
  have hbound : ∀ (k : ℕ) p, |uncurryField (hs k) p - uncurryField h p| ≤
      c 1 * (t / (k + 1)) * |W p| := by
    intro k p
    obtain ⟨ω, s, y⟩ := p
    have key := prop72_sum_ind_sub_le (prop72Grid_mono ht0 k) (s := s)
      (w := φ s y * Z s y ω.1) (B := c 1 * (t / (k + 1)) * |Z s y ω.1|)
      (v := fun i => φ (prop72Grid t k i) y * Z s y ω.1) (k + 1) (by
        intro i hi h1 h2
        have hi' : i ∈ Finset.range (k + 1) := Finset.mem_range.2 hi
        have hsT : s ∈ Set.Icc 0 T :=
          ⟨(hmemT k i hi').1.1.trans h1.le, h2.trans (hmemT k i hi').2.2⟩
        rw [← sub_mul, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        refine (hφ.prop72_abs_sub_le hL (hmemT k i hi').1 hsT y).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hL0
        rw [abs_sub_comm, abs_of_nonneg (by linarith), ← prop72Grid_succ_sub t k i]
        linarith)
    rw [prop72Grid_zero, prop72Grid_last] at key
    simp only [uncurryField, hhs, hh, hWdef, hb1, one_mul]
    refine key.trans ?_
    split_ifs <;> simp
  have hbound0 : ∀ p, |uncurryField h p| ≤ c 0 * |W p| := by
    rintro ⟨ω, s, y⟩
    simp only [uncurryField, hh, hWdef, hb1, one_mul]
    split_ifs with hst
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hφb s ⟨hst.1.le, hst.2.trans htT⟩ y) (abs_nonneg _)
    · simp
  -- `δ_k = t / (k+1) → 0`
  have hδ : Tendsto (fun k : ℕ => t / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
    simpa [mul_one_div, div_eq_mul_inv] using this
  have hsm : ∀ k, AEStronglyMeasurable (uncurryField (hs k)) (ν.prod volume) := fun k =>
    (IsWalshIntegral.isometry_lib hS (hXs k)).1.aestronglyMeasurable
  -- `h` is measurable, as the pointwise limit of the `hs k`
  have hhm : AEStronglyMeasurable (uncurryField h) (ν.prod volume) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hsm (ae_of_all _ fun p => ?_)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => (Real.norm_eq_abs _).trans_le
      (hbound k p)) ?_
    simpa using (hδ.const_mul (c 1)).mul_const |W p|
  have hh2 : MemLp (uncurryField h) 2 (ν.prod volume) :=
    (hWm.const_mul (c 0)).of_le hhm (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
      exact hbound0 p)
  -- the value
  have hMt := (hmart hφ).memLp ⟨t, ht0⟩ htT
  have hM0 := (hmart hφ).memLp 0 hT
  have hX2 : MemLp (fun ω : Ω × Ω'' => limMart Y φ φt t ω.1 - limMart Y φ φt 0 ω.1) 2 ν :=
    (hMt.sub hM0).comp_measurePreserving measurePreserving_fst
  refine IsWalshIntegral.limit _ _ hs Xs hXs hh2 hX2 ?_ ?_
  · -- convergence of the integrands
    have hle : ∀ k, eLpNorm (uncurryField (hs k) - uncurryField h) 2 (ν.prod volume) ≤
        ‖c 1 * (t / (k + 1))‖ₑ * eLpNorm W 2 (ν.prod volume) := by
      intro k
      rw [← eLpNorm_const_smul]
      refine eLpNorm_mono ((hsm k).sub hhm) fun p => ?_
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ c 1 * (t / (k + 1)))]
      exact hbound k p
    have hlim : Tendsto (fun k : ℕ => ‖c 1 * (t / (k + 1))‖ₑ * eLpNorm W 2 (ν.prod volume))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ‖c 1 * (t / (k + 1))‖ₑ) atTop (𝓝 0) := by
        have h2 : Tendsto (fun k : ℕ => c 1 * (t / ((k : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using hδ.const_mul (c 1)
        have := ((continuous_enorm (E := ℝ)).tendsto 0).comp h2
        rw [enorm_zero] at this
        exact this
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hWm.eLpNorm_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => zero_le) hle
  · -- convergence of the values
    set K := ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z s x ω ^ 2)) ∂Pr
      with hK
    have hKt : K ≠ ∞ := hZ2.ne
    set D : ℕ → Ω → ℝ := fun k ω => (∑ i ∈ Finset.range (k + 1),
        (limMart Y (fun _ => φ (prop72Grid t k i)) (fun _ _ => 0) (prop72Grid t k (i + 1)) ω -
          limMart Y (fun _ => φ (prop72Grid t k i)) (fun _ _ => 0) (prop72Grid t k i) ω)) -
        (limMart Y φ φt t ω - limMart Y φ φt 0 ω) with hD
    have hDm : ∀ k, MemLp (D k) 2 Pr := fun k =>
      (memLp_finsetSum _ fun i hi =>
        ((hmart (hφ.prop72Slice (hmemT k i hi).1)).memLp ⟨_, (hmemT k i hi).2.1⟩
          (hmemT k i hi).2.2).sub
        ((hmart (hφ.prop72Slice (hmemT k i hi).1)).memLp ⟨_, (hmemT k i hi).1.1⟩
          (hmemT k i hi).1.2)).sub (hMt.sub hM0)
    have heq : ∀ k, eLpNorm (Xs k - fun ω : Ω × Ω'' =>
        limMart Y φ φt t ω.1 - limMart Y φ φt 0 ω.1) 2 ν = eLpNorm (D k) 2 Pr := fun k =>
      eLpNorm_comp_measurePreserving (hDm k).aestronglyMeasurable measurePreserving_fst
    have hle : ∀ k : ℕ, eLpNorm (D k) 2 Pr ≤
        (ENNReal.ofReal (c 1 ^ 2 * t ^ 2 / (k + 1)) * K) ^ (1 / 2 : ℝ) := by
      intro k
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (hDm k).aestronglyMeasurable, ENNReal.toReal_ofNat]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      simp_rw [prop72_enorm_rpow_two]
      exact prop72_L2_bound hmart hφ hL ht0 htT k
    have hlim : Tendsto (fun k : ℕ =>
        (ENNReal.ofReal (c 1 ^ 2 * t ^ 2 / (k + 1)) * K) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => c 1 ^ 2 * t ^ 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (c 1 ^ 2 * t ^ 2)
        simpa [mul_one_div, div_eq_mul_inv] using this
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hKt)
      rw [ENNReal.ofReal_zero, zero_mul] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp h2
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    simp_rw [heq]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => zero_le) hle

end QSSEPtoKPZ
