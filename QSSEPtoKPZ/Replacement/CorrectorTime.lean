/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.Replacement.CorrectorAlgebra

/-!
# Lemma 6.4: time regularity of `f_t`

Task G1. The hypotheses of Lemma 3.2 for `f_t = κ_n G Φ_t` (`corrF`): `∂ₜf_t = corrF'`
(`hasDerivWithinAt_corrF`, by the chain rule `IsC13.hasDerivWithinAt_line`), continuity of
`∂ₜf_t` on `[0,T]` (`continuousOn_corrF'`) and the bounds (`abs_corrF_le`). Also the continuity
in `t` of the integrands after clamping the time to `[0,T]` (`corrClamp`), used for the joint
measurability of the processes `𝖱_n` and of the bracket density.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace QSSEPtoKPZ

variable {ρ : ℝ → ℝ} {m : ℕ} {n T C : ℝ} {φ φt : ℝ → ℝ → ℝ}

/-- The projection `t ↦ max 0 (min t T)` of `ℝ` onto `[0,T]`. -/
def corrClamp (T t : ℝ) : ℝ := max 0 (min t T)

lemma corrClamp_mem (hT : 0 ≤ T) (t : ℝ) : corrClamp T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma corrClamp_of_mem {t : ℝ} (ht : t ∈ Icc 0 T) : corrClamp T t = t := by
  rw [corrClamp, min_eq_left ht.2, max_eq_right ht.1]

lemma continuous_corrClamp : Continuous (corrClamp T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- Continuity along continuous paths in `[0,T] × ℝ` of `φ`, `∂ₜφ` and `∂ₓφ`. -/
lemma IsC13.corr_continuousOn_comp (hφ : IsC13 T φ φt C) {a : ℝ → ℝ} (ha : Continuous a) :
    ContinuousOn (fun s => φ s (a s)) (Icc 0 T) ∧ ContinuousOn (fun s => φt s (a s)) (Icc 0 T) ∧
      ContinuousOn (fun s => deriv (φ s) (a s)) (Icc 0 T) := by
  have hp : ContinuousOn (fun s : ℝ => (s, a s)) (Icc 0 T) :=
    (continuous_id.prodMk ha).continuousOn
  have hm : MapsTo (fun s : ℝ => (s, a s)) (Icc 0 T) (Icc 0 T ×ˢ univ) := fun s hs =>
    ⟨hs, mem_univ _⟩
  refine ⟨?_, hφ.continuousOn.1.comp hp hm, ?_⟩
  · have := (hφ.continuousOn.2 0 (by norm_num)).comp hp hm
    simpa only [iteratedDeriv_zero, Function.comp_def] using this
  · have := (hφ.continuousOn.2 1 (by norm_num)).comp hp hm
    simpa only [iteratedDeriv_one, Function.comp_def] using this

/-- Clamped version: `t ↦ φ_{clamp t}(a t)` (and `∂ₜφ`, `∂ₓφ`) is continuous on `ℝ`. -/
lemma IsC13.corr_continuous_clamp (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) {a : ℝ → ℝ} (ha : Continuous a) :
    Continuous (fun t => φ (corrClamp T t) (a t)) ∧
      Continuous (fun t => φt (corrClamp T t) (a t)) ∧
      Continuous (fun t => deriv (φ (corrClamp T t)) (a t)) := by
  -- write `a t = a' (clamp t)` is not possible; use the joint continuity directly
  have hp : Continuous (fun t : ℝ => (corrClamp T t, a t)) := continuous_corrClamp.prodMk ha
  have hm : ∀ t, (corrClamp T t, a t) ∈ Icc 0 T ×ˢ (univ : Set ℝ) := fun t =>
    ⟨corrClamp_mem hT t, mem_univ _⟩
  refine ⟨?_, hφ.continuousOn.1.comp_continuous hp hm, ?_⟩
  · have := (hφ.continuousOn.2 0 (by norm_num)).comp_continuous hp hm
    simpa only [iteratedDeriv_zero, Function.comp_def] using this
  · have := (hφ.continuousOn.2 1 (by norm_num)).comp_continuous hp hm
    simpa only [iteratedDeriv_one, Function.comp_def] using this

/-- `t ↦ y_n(t,x)` is continuous. -/
lemma corr_continuous_rescaledPosition (n : ℝ) (x : ℤ) : Continuous fun t => rescaledPosition n t x := by
  unfold rescaledPosition; fun_prop

/-- **`∂ₜ f_t = corrF'`** on `[0,T]` (hypothesis of Lemma 3.2). -/
lemma hasDerivWithinAt_corrF (hn : 1 ≤ n) (hφ : IsC13 T φ φt C) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x₁ x₂ : ℤ) :
    HasDerivWithinAt (fun s => corrF n ρ m φ s x₁ x₂) (corrF' n ρ m φ φt t x₁ x₂) (Icc 0 T) t := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hU : ∀ x : ℤ, HasDerivWithinAt (fun s => φ s (rescaledPosition n s x))
      (corrDt n φ φt t x) (Icc 0 T) t := fun x => by
    have := hφ.corr_hasDerivWithinAt_line ht ((x : ℝ) / n ^ (1 / 2 : ℝ)) (-n ^ (1 / 4 : ℝ))
    simp only [← corr_rescaledPosition_eq_line hn0] at this
    convert this using 1
    rw [corrDt]; ring
  have := (((hU x₁).const_mul (gM ρ m (x₂ - x₁))).fun_mul (hU x₂)).const_mul (corrPref n)
  convert this using 1
  · funext s; simp only [corrF]
  · simp only [corrF']; ring

/-- **`∂ₜ f_t` is continuous on `[0,T]`** (hypothesis of Lemma 3.2). -/
lemma continuousOn_corrF' (hφ : IsC13 T φ φt C) (x₁ x₂ : ℤ) :
    ContinuousOn (fun s => corrF' n ρ m φ φt s x₁ x₂) (Icc 0 T) := by
  obtain ⟨a1, b1, c1⟩ := hφ.corr_continuousOn_comp (corr_continuous_rescaledPosition n x₁)
  obtain ⟨a2, b2, c2⟩ := hφ.corr_continuousOn_comp (corr_continuous_rescaledPosition n x₂)
  simp only [corrF', corrDt]
  exact continuousOn_const.mul (continuousOn_const.mul (((b1.sub (continuousOn_const.mul c1)).mul
    a2).add (a1.mul (b2.sub (continuousOn_const.mul c2)))))

/-- **Bounds on `f_t` and `∂ₜf_t`** on `[0,T]` (hypothesis of Lemma 3.2):
both are bounded by `κ_n m (1 + n^{1/4}) C²`. -/
lemma abs_corrF_le (hρ : IsMollifier ρ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hφ : IsC13 T φ φt C)
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) (x₁ x₂ : ℤ) :
    |corrF n ρ m φ t x₁ x₂| ≤ corrPref n * m * (1 + n ^ (1 / 4 : ℝ)) * C ^ 2 ∧
      |corrF' n ρ m φ φt t x₁ x₂| ≤ corrPref n * m * (1 + n ^ (1 / 4 : ℝ)) * C ^ 2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨-, hκ0, -, -⟩ := corrPref_props hn
  have hC := hφ.corr_C_nonneg hT
  have hq : 0 ≤ n ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos hn0 _).le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hg := hρ.gM_nonneg_le hm (x₂ - x₁)
  have hga : |gM ρ m (x₂ - x₁)| ≤ m / 2 := by rw [abs_of_nonneg hg.1]; exact hg.2
  obtain ⟨u1, v1, d1, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x₁)
  obtain ⟨u2, v2, d2, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x₂)
  have hD : ∀ x : ℤ, |corrDt n φ φt t x| ≤ (1 + n ^ (1 / 4 : ℝ)) * C := fun x => by
    obtain ⟨-, v, d, -⟩ := hφ.corr_abs_le_C hT ht (rescaledPosition n t x)
    unfold corrDt
    calc _ ≤ |φt t (rescaledPosition n t x)| +
          |n ^ (1 / 4 : ℝ) * deriv (φ t) (rescaledPosition n t x)| := abs_sub _ _
      _ = |φt t (rescaledPosition n t x)| +
          n ^ (1 / 4 : ℝ) * |deriv (φ t) (rescaledPosition n t x)| := by
          rw [abs_mul, abs_of_nonneg hq]
      _ ≤ C + n ^ (1 / 4 : ℝ) * C := by gcongr
      _ = _ := by ring
  constructor
  · unfold corrF
    rw [abs_mul, abs_of_nonneg hκ0]
    calc corrPref n * |gM ρ m (x₂ - x₁) * φ t (rescaledPosition n t x₁) *
          φ t (rescaledPosition n t x₂)| ≤ corrPref n * (m / 2 * C * C) := by
          gcongr; exact corr_abs_mul3_le hga u1 u2
      _ ≤ corrPref n * m * (1 + n ^ (1 / 4 : ℝ)) * C ^ 2 := by
          have : (0 : ℝ) ≤ corrPref n * m * C ^ 2 := by positivity
          nlinarith
  · unfold corrF'
    rw [abs_mul, abs_of_nonneg hκ0, abs_mul]
    have hs : |corrDt n φ φt t x₁ * φ t (rescaledPosition n t x₂) +
        φ t (rescaledPosition n t x₁) * corrDt n φ φt t x₂| ≤
        2 * ((1 + n ^ (1 / 4 : ℝ)) * C * C) := by
      calc _ ≤ |corrDt n φ φt t x₁ * φ t (rescaledPosition n t x₂)| +
            |φ t (rescaledPosition n t x₁) * corrDt n φ φt t x₂| := abs_add_le _ _
        _ = |corrDt n φ φt t x₁| * |φ t (rescaledPosition n t x₂)| +
            |φ t (rescaledPosition n t x₁)| * |corrDt n φ φt t x₂| := by rw [abs_mul, abs_mul]
        _ ≤ (1 + n ^ (1 / 4 : ℝ)) * C * C + C * ((1 + n ^ (1 / 4 : ℝ)) * C) := by
            gcongr
            · exact hD x₁
            · exact hD x₂
        _ = _ := by ring
    calc corrPref n * (|gM ρ m (x₂ - x₁)| * |corrDt n φ φt t x₁ * φ t (rescaledPosition n t x₂) +
          φ t (rescaledPosition n t x₁) * corrDt n φ φt t x₂|) ≤
        corrPref n * (m / 2 * (2 * ((1 + n ^ (1 / 4 : ℝ)) * C * C))) := by gcongr
      _ = _ := by ring

/-- Continuity in `t` of `f_{clamp t}(x₁,x₂)`. -/
lemma continuous_corrF_clamp (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) (x₁ x₂ : ℤ) :
    Continuous fun t => corrF n ρ m φ (corrClamp T t) x₁ x₂ := by
  have h1 := (hφ.corr_continuous_clamp hT
    ((corr_continuous_rescaledPosition n x₁).comp (continuous_corrClamp (T := T)))).1
  have h2 := (hφ.corr_continuous_clamp hT
    ((corr_continuous_rescaledPosition n x₂).comp (continuous_corrClamp (T := T)))).1
  simp only [corrF]
  exact continuous_const.mul ((continuous_const.mul h1).mul h2)

/-- Continuity in `t` of `𝒬^θ F_t(x₁,x₂)` when each `F_t(a,b)` is continuous in `t`. -/
lemma corr_continuous_tiltedInclGen {F : ℝ → ℤ → ℤ → ℝ} (hF : ∀ a b, Continuous fun t => F t a b)
    (θ : ℝ) (x₁ x₂ : ℤ) : Continuous fun t => tiltedInclGen θ (F t) x₁ x₂ := by
  unfold tiltedInclGen
  have := hF
  split_ifs <;> fun_prop

/-- Continuity in `t` of the integrand of the remainder at the clamped time. -/
lemma continuous_corrRem_clamp (hφ : IsC13 T φ φt C) (hT : 0 ≤ T) (x₁ x₂ : ℤ) :
    Continuous fun t => corrRem n ρ m φ φt (corrClamp T t) x₁ x₂ := by
  have hc : ∀ x : ℤ, Continuous (fun t => rescaledPosition n (corrClamp T t) x) := fun x =>
    (corr_continuous_rescaledPosition n x).comp continuous_corrClamp
  have hU1 := (hφ.corr_continuous_clamp hT (hc x₁)).1
  have hV1 := (hφ.corr_continuous_clamp hT (hc x₁)).2.1
  have hW1 := (hφ.corr_continuous_clamp hT (hc x₁)).2.2
  have hU2 := (hφ.corr_continuous_clamp hT (hc x₂)).1
  have hV2 := (hφ.corr_continuous_clamp hT (hc x₂)).2.1
  have hW2 := (hφ.corr_continuous_clamp hT (hc x₂)).2.2
  have hQ : Continuous fun t => tiltedInclGen (thetaN n) (corrF n ρ m φ (corrClamp T t)) x₁ x₂ :=
    corr_continuous_tiltedInclGen (F := fun t => corrF n ρ m φ (corrClamp T t))
    (fun a b => continuous_corrF_clamp hφ hT a b) (thetaN n) x₁ x₂
  have hF := continuous_corrF_clamp (ρ := ρ) (m := m) (n := n) hφ hT x₁ x₂
  simp only [corrRem, corrDrift, corrF', corrDt, corrEdens, corrBdens]
  split_ifs
  all_goals
    refine (((Continuous.add (Continuous.add ?_ (continuous_const.mul hQ)) ?_).sub
      (continuous_const.mul (hU1.mul hU2))).add
      (continuous_const.mul ((continuous_const.mul hU1).mul hU2)))
    · exact continuous_const.mul (continuous_const.mul (((hV1.sub (continuous_const.mul hW1)).mul
        hU2).add (hU1.mul (hV2.sub (continuous_const.mul hW2)))))
    · first | exact continuous_const.mul hF | exact continuous_const

end QSSEPtoKPZ
