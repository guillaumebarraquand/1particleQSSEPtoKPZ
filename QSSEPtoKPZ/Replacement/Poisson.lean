/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md.
-/
module

public import QSSEPtoKPZ.Replacement.Mollifier

/-!
# Lemma 6.3: a Poisson equation for `𝓡`

The even function `g_m : ℤ → ℝ` of (6.7),

  `g_m(0) = k_m(0)/4`,  `g_m(1) = 0`,  `g_m(r+1) = g_m(r) + (1/2) ∑_{u > r} k_m(u)` for `r ≥ 1`,

solves `𝓡 g_m = (1/2) 𝟙_{|r| = 1} - k_m` (6.8), and satisfies the bounds of Lemma 6.3.

`gM ρ m` is defined on `ℕ` by the recursion (6.7) (`gNat`), and extended to `ℤ` as an even
function. `gM_spec` checks that it satisfies (6.7) as written in the article.
-/

@[expose] public section

noncomputable section

namespace QSSEPtoKPZ

/-- The function `g_m` of (6.7) on `ℕ`, defined by recursion. The sum `∑_{u > r+1} k_m(u)` is
written `∑_{u ≥ 0} k_m(r + 2 + u)`. -/
def gNat (ρ : ℝ → ℝ) (m : ℕ) : ℕ → ℝ
  | 0 => kM ρ m 0 / 4
  | 1 => 0
  | r + 2 => gNat ρ m (r + 1) + 1 / 2 * ∑' u : ℕ, kM ρ m ((r : ℤ) + 2 + u)

/-- The even function `g_m : ℤ → ℝ` of (6.7): `g_m(r) = g_m(|r|)`. -/
def gM (ρ : ℝ → ℝ) (m : ℕ) (r : ℤ) : ℝ := gNat ρ m r.natAbs

/-! ### Auxiliary facts: tail sums of `k_m` and the recursion for `g_m` -/

/-- The tail sum `T(s) = ∑_{u ≥ s} k_m(u) = ∑_{u ≥ 0} k_m(s + u)`. -/
def tailK (ρ : ℝ → ℝ) (m : ℕ) (s : ℤ) : ℝ := ∑' u : ℕ, kM ρ m (s + u)

lemma gNat_add_two (ρ : ℝ → ℝ) (m n : ℕ) :
    gNat ρ m (n + 2) = gNat ρ m (n + 1) + 1 / 2 * tailK ρ m (n + 2) := by
  rw [gNat, tailK]

lemma gM_natCast (ρ : ℝ → ℝ) (m n : ℕ) : gM ρ m n = gNat ρ m n := by
  simp [gM]

lemma gM_neg_natCast (ρ : ℝ → ℝ) (m n : ℕ) : gM ρ m (-n) = gNat ρ m n := by
  simp [gM]

lemma chainGen_neg {g : ℤ → ℝ} (hg : ∀ r, g (-r) = g r) (r : ℤ) :
    chainGen g (-r) = chainGen g r := by
  unfold chainGen
  rw [show -r + 1 = -(r - 1) by ring, show -r - 1 = -(r + 1) by ring]
  simp only [hg, abs_neg]
  ring

namespace IsMollifier

variable {ρ : ℝ → ℝ} {m : ℕ}

lemma kM_eq_zero (hρ : IsMollifier ρ) (hm : 1 ≤ m) {r : ℤ} (hr : 2 * (m : ℤ) ≤ |r|) :
    kM ρ m r = 0 :=
  (hρ.kM_props hm).2.2 r hr

lemma kM_nonneg (hρ : IsMollifier ρ) (hm : 1 ≤ m) (r : ℤ) : 0 ≤ kM ρ m r :=
  (hρ.kM_props hm).2.1 r

lemma summable_kM_nat (hρ : IsMollifier ρ) (hm : 1 ≤ m) (s : ℤ) :
    Summable (fun u : ℕ => kM ρ m (s + u)) := by
  have hs : Summable (kM ρ m) :=
    summable_of_eq_zero_of_le_abs (2 * m) fun r hr => hρ.kM_eq_zero hm hr
  exact hs.comp_injective (i := fun u : ℕ => s + (u : ℤ)) fun a b h => by simpa using h

lemma tailK_nonneg (hρ : IsMollifier ρ) (hm : 1 ≤ m) (s : ℤ) : 0 ≤ tailK ρ m s :=
  tsum_nonneg fun _ => hρ.kM_nonneg hm _

lemma tailK_eq (hρ : IsMollifier ρ) (hm : 1 ≤ m) (s : ℤ) :
    tailK ρ m s = kM ρ m s + tailK ρ m (s + 1) := by
  unfold tailK
  rw [(hρ.summable_kM_nat hm s).tsum_eq_zero_add]
  congr 1
  · simp
  · congr 1
    ext u
    congr 1
    push_cast
    ring

lemma tailK_eq_zero (hρ : IsMollifier ρ) (hm : 1 ≤ m) {s : ℤ} (hs : 2 * (m : ℤ) ≤ s) :
    tailK ρ m s = 0 := by
  unfold tailK
  have : ∀ u : ℕ, kM ρ m (s + u) = 0 := fun u =>
    hρ.kM_eq_zero hm (le_abs.2 (Or.inl (by omega)))
  simp [this]

lemma tailK_le_tailK_one (hρ : IsMollifier ρ) (hm : 1 ≤ m) (j : ℕ) :
    tailK ρ m (1 + j) ≤ tailK ρ m 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hρ.tailK_eq hm (1 + j)
    have h' := hρ.kM_nonneg hm (1 + j)
    rw [show (1 : ℤ) + (j + 1 : ℕ) = 1 + j + 1 by push_cast; ring]
    linarith

/-- Equation (6.5) in the form `2 k_m(0) + 2 ∑_{u ≥ 1} k_m(u) = 1`. -/
lemma two_kM_zero_add_two_tailK_one (hρ : IsMollifier ρ) (hm : 1 ≤ m) :
    2 * kM ρ m 0 + 2 * tailK ρ m 1 = 1 := by
  obtain ⟨hsum, h1⟩ := hρ.tsum_chainPi_mul_kM hm
  set f : ℤ → ℝ := fun r => chainPi r * kM ρ m r with hf
  have hpos : Summable (fun n : ℕ => f n) := by
    have := hsum.comp_injective (i := fun n : ℕ => (n : ℤ)) Nat.cast_injective
    exact this
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    have := hsum.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun a b h => by simpa using h)
    exact this
  have h2 := tsum_of_nat_of_neg_add_one hpos hneg
  have h3 := hpos.tsum_eq_zero_add
  have h4 : f ↑(0 : ℕ) + ∑' b : ℕ, f ↑(b + 1) + ∑' n : ℕ, f (-((n : ℤ) + 1)) = 1 := by
    rw [← h3, ← h2]; exact h1
  have e0 : f ↑(0 : ℕ) = 2 * kM ρ m 0 := by
    simp only [hf, chainPi]; norm_num
  have e1 : ∀ b : ℕ, f ↑(b + 1) = kM ρ m (1 + b) := by
    intro b
    have : ((b + 1 : ℕ) : ℤ) ≠ 0 := by omega
    simp only [hf, chainPi, this, ite_false]
    push_cast; ring_nf
  have e2 : ∀ b : ℕ, f (-((b : ℤ) + 1)) = kM ρ m (1 + b) := by
    intro b
    have : -((b : ℤ) + 1) ≠ 0 := by omega
    simp only [hf, chainPi, this, ite_false]
    rw [(hρ.kM_props hm).1]; ring_nf
  rw [e0, tsum_congr e1, tsum_congr e2] at h4
  unfold tailK
  linarith

lemma kM_zero_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) : kM ρ m 0 ≤ 1 / 2 := by
  linarith [hρ.two_kM_zero_add_two_tailK_one hm, hρ.tailK_nonneg hm 1]

lemma tailK_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) {s : ℤ} (hs : 1 ≤ s) :
    tailK ρ m s ≤ 1 / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = 1 + j := ⟨(s - 1).toNat, by omega⟩
  linarith [hρ.tailK_le_tailK_one hm j, hρ.two_kM_zero_add_two_tailK_one hm,
    hρ.kM_nonneg hm 0]

lemma gNat_nonneg (hρ : IsMollifier ρ) (hm : 1 ≤ m) (n : ℕ) : 0 ≤ gNat ρ m n := by
  rcases n with _ | n
  · simp only [gNat]; linarith [hρ.kM_nonneg hm 0]
  · induction n with
    | zero => simp [gNat]
    | succ n ih =>
      rw [gNat_add_two]
      linarith [hρ.tailK_nonneg hm (n + 2)]

lemma abs_gNat_succ_sub_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (n : ℕ) :
    |gNat ρ m (n + 1) - gNat ρ m n| ≤ 1 / 4 := by
  rcases n with _ | n
  · simp only [gNat]
    have := hρ.kM_nonneg hm 0
    have := hρ.kM_zero_le hm
    rw [abs_le]; constructor <;> linarith
  · rw [gNat_add_two]
    have := hρ.tailK_nonneg hm (n + 2)
    have := hρ.tailK_le hm (s := n + 2) (by omega)
    rw [abs_le]; constructor <;> linarith

lemma gNat_succ_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (n : ℕ) :
    gNat ρ m (n + 1) ≤ n / 4 ∧ gNat ρ m (n + 1) ≤ (2 * m - 2) / 4 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  induction n with
  | zero => simp only [gNat]; constructor <;> norm_num; linarith
  | succ n ih =>
    rw [gNat_add_two]
    by_cases h : 2 * m ≤ n + 2
    · rw [hρ.tailK_eq_zero hm (by omega)]
      push_cast
      constructor <;> linarith [ih.1, ih.2]
    · have := hρ.tailK_le hm (s := n + 2) (by omega)
      have h' : (n : ℝ) + 3 ≤ 2 * m := by exact_mod_cast (by omega : n + 3 ≤ 2 * m)
      push_cast
      constructor <;> linarith [ih.1, ih.2]

lemma gNat_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (n : ℕ) : gNat ρ m n ≤ m / 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rcases n with _ | n
  · simp only [gNat]; linarith [hρ.kM_zero_le hm]
  · linarith [(hρ.gNat_succ_le hm n).2]

lemma gNat_add_three (hρ : IsMollifier ρ) (hm : 1 ≤ m) {j : ℕ} (hj : 2 * m ≤ j + 2) :
    gNat ρ m (j + 3) = gNat ρ m (j + 1) := by
  rw [gNat_add_two, gNat_add_two, hρ.tailK_eq_zero hm (by omega),
    hρ.tailK_eq_zero hm (by omega)]
  ring

end IsMollifier

set_option linter.unusedVariables false in
/-- **Equation (6.7)**, as written in the article: `g_m` is even, `g_m(0) = k_m(0)/4`,
`g_m(1) = 0`, and `g_m(r+1) = g_m(r) + (1/2) ∑_{u > r} k_m(u)` for `r ≥ 1`. -/
theorem IsMollifier.gM_spec {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m) :
    (∀ r, gM ρ m (-r) = gM ρ m r) ∧ gM ρ m 0 = kM ρ m 0 / 4 ∧ gM ρ m 1 = 0 ∧
      ∀ r : ℤ, 1 ≤ r →
        gM ρ m (r + 1) = gM ρ m r + 1 / 2 * ∑' u : ℤ, if r < u then kM ρ m u else 0 := by
  refine ⟨fun r => by simp [gM], by simp [gM, gNat], by simp [gM, gNat], fun r hr => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n + 1 := ⟨(r - 1).toNat, by omega⟩
  rw [show (n : ℤ) + 1 + 1 = ((n + 2 : ℕ) : ℤ) by push_cast; ring,
    show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, gM_natCast, gM_natCast,
    gNat_add_two]
  congr 2
  -- `∑_{u ≥ 0} k_m(n + 2 + u) = ∑_{u > n + 1} k_m(u)`
  unfold tailK
  have hinj : Function.Injective (fun u : ℕ => ((n : ℤ) + 2) + u) := fun a b h => by simpa using h
  rw [← hinj.tsum_eq]
  · congr 1
    ext u
    have : ((n + 1 : ℕ) : ℤ) < (n : ℤ) + 2 + u := by push_cast; omega
    simp only [this, ite_true]
  · intro u hu
    rw [Function.mem_support] at hu
    have : ((n + 1 : ℕ) : ℤ) < u := by
      by_contra h
      simp only [h, ite_false, ne_eq, not_true_eq_false] at hu
    exact ⟨(u - n - 2).toNat, by simp only; omega⟩

/-- **Lemma 6.3**, equation (6.8): `𝓡 g_m(r) = (1/2) 𝟙_{|r| = 1} - k_m(r)` for all `r ∈ ℤ`. -/
theorem IsMollifier.chainGen_gM {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m)
    (r : ℤ) :
    chainGen (gM ρ m) r = 1 / 2 * (if |r| = 1 then 1 else 0) - kM ρ m r := by
  have hk0 := hρ.two_kM_zero_add_two_tailK_one hm
  -- it suffices to treat `r = n ≥ 0`, since `g_m` and `k_m` are even
  suffices h : ∀ n : ℕ, chainGen (gM ρ m) n = 1 / 2 * (if |(n : ℤ)| = 1 then 1 else 0) - kM ρ m n by
    rcases Int.eq_nat_or_neg r with ⟨n, rfl | rfl⟩
    · exact h n
    · rw [chainGen_neg (hρ.gM_spec hm).1, abs_neg, (hρ.kM_props hm).1]
      exact h n
  intro n
  rcases n with _ | _ | n
  · -- `r = 0`
    simp [chainGen, gM, gNat]
    ring
  · -- `r = 1`
    have h2 : gM ρ m 2 = 1 / 2 * tailK ρ m 2 := by
      rw [show (2 : ℤ) = ((0 + 2 : ℕ) : ℤ) by norm_num, gM_natCast, gNat_add_two]
      simp [gNat]
    have ht := hρ.tailK_eq hm 1
    norm_num at ht
    simp only [chainGen]
    norm_num
    rw [h2]
    simp [gM, gNat]
    linarith
  · -- `r = n + 2`
    have hab : |((n + 2 : ℕ) : ℤ)| ≠ 1 := by
      rw [abs_of_nonneg (by positivity)]; omega
    simp only [chainGen, hab, ite_false]
    rw [show ((n + 2 : ℕ) : ℤ) + 1 = ((n + 1 + 2 : ℕ) : ℤ) by push_cast; ring,
      show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
      gM_natCast, gM_natCast, gM_natCast, gNat_add_two, gNat_add_two]
    have ht := hρ.tailK_eq hm ((n : ℤ) + 2)
    rw [show ((n + 1 : ℕ) : ℤ) + 2 = (n : ℤ) + 2 + 1 by push_cast; ring]
    push_cast at ht ⊢
    ring_nf at ht ⊢
    linarith

/-- **Lemma 6.3**, bounds: `0 ≤ g_m(r) ≤ m/2` for all `r ∈ ℤ`. -/
theorem IsMollifier.gM_nonneg_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m)
    (r : ℤ) :
    0 ≤ gM ρ m r ∧ gM ρ m r ≤ m / 2 := by
  exact ⟨hρ.gNat_nonneg hm _, hρ.gNat_le hm _⟩

/-- **Lemma 6.3**, bounds: `|g_m(r+1) - g_m(r)| ≤ 1/4` for all `r ∈ ℤ`. -/
theorem IsMollifier.abs_gM_succ_sub_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ} (hm : 1 ≤ m)
    (r : ℤ) :
    |gM ρ m (r + 1) - gM ρ m r| ≤ 1 / 4 := by
  rcases Int.eq_nat_or_neg r with ⟨n, rfl | rfl⟩
  · rw [← Nat.cast_succ, gM_natCast, gM_natCast]
    exact hρ.abs_gNat_succ_sub_le hm n
  · rcases n with _ | n
    · simpa [gM] using hρ.abs_gNat_succ_sub_le hm 0
    · rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, gM_neg_natCast,
        gM_neg_natCast, abs_sub_comm]
      exact hρ.abs_gNat_succ_sub_le hm n

/-- **Lemma 6.3**: `g_m(r+1) = g_m(r-1)` when `|r| ≥ 2m`. -/
theorem IsMollifier.gM_add_one_eq_sub_one {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {m : ℕ}
    (hm : 1 ≤ m) {r : ℤ} (hr : 2 * (m : ℤ) ≤ |r|) :
    gM ρ m (r + 1) = gM ρ m (r - 1) := by
  rcases Int.eq_nat_or_neg r with ⟨n, rfl | rfl⟩
  · rw [abs_of_nonneg (by positivity)] at hr
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 2 := ⟨n - 2, by omega⟩
    rw [show ((j + 2 : ℕ) : ℤ) + 1 = ((j + 3 : ℕ) : ℤ) by push_cast; ring,
      show ((j + 2 : ℕ) : ℤ) - 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring, gM_natCast, gM_natCast]
    exact hρ.gNat_add_three hm (by omega)
  · rw [abs_neg, abs_of_nonneg (by positivity)] at hr
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 2 := ⟨n - 2, by omega⟩
    rw [show -((j + 2 : ℕ) : ℤ) + 1 = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
      show -((j + 2 : ℕ) : ℤ) - 1 = -((j + 3 : ℕ) : ℤ) by push_cast; ring, gM_neg_natCast,
      gM_neg_natCast]
    exact (hρ.gNat_add_three hm (by omega)).symm

/-- **Lemma 6.3**: `g_m(0) ≤ C/m` for all `m ≥ 1`, for a constant `C` which depends only on `ρ`. -/
theorem IsMollifier.exists_gM_zero_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → gM ρ m 0 ≤ C / m := by
  obtain ⟨c, C, hc, hb⟩ := hρ.bM_bounds
  have h0 := hρ.kappa_zero_pos
  refine ⟨kappa ρ 0 / (4 * c), fun m hm => ?_⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbm := (hb m hm).1
  have : gM ρ m 0 = kappa ρ 0 / (4 * (m * bM ρ m)) := by
    simp only [gM, Int.natAbs_zero, gNat, kM, Int.cast_zero, zero_div]
    ring
  rw [this, div_div]
  apply div_le_div_of_nonneg_left h0.le (by positivity)
  nlinarith

end QSSEPtoKPZ
