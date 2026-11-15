/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage2-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Riemann

/-!
# Complex Riemann sums against `complexBM` (package C, task C7)

INTERFACE FILE (task I0 of Stage 2): the statements below are frozen interfaces. The two
algebraic identities (and their combination
`itoSum_sde_eq_realRiemann`) are proved here (task I0); `tendstoInMeasure_complex_iff` is proved
by task C7. See `docs/stage2-design.md`, Section 2.2 (design decision C-5), and
`docs/stage2-interfaces.md`.

The complex notation `W⁽ˣ⁾ = (B_{x,0} + i B_{x,1}) / √2` of the frozen statement enters only
here: the Riemann sums `itoSum f W⁽ˣ⁾` and `itoSum f conj(W⁽ˣ⁾)` are written with the real
Riemann sums `realRiemann` of `Re f`, `Im f` against `B_{x,0}`, `B_{x,1}`; and convergence in
measure of complex random variables is that of their real and imaginary parts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- With `f = f₁ + i f₂` and `W = (B_{x,0} + i B_{x,1}) / √2`:
`itoSum f W = (R(f₁, B_{x,0}) - R(f₂, B_{x,1}) + i (R(f₂, B_{x,0}) + R(f₁, B_{x,1}))) / √2`,
where `R` is the real left-point Riemann sum. -/
theorem itoSum_complexBM (f : ℝ → Ω → ℂ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ) (t : ℝ)
    (m : ℕ) (ω : Ω) :
    itoSum f (complexBM B x) t m ω =
      (((realRiemann (fun s ω => (f s ω).re) (B (x, 0)) t m ω -
          realRiemann (fun s ω => (f s ω).im) (B (x, 1)) t m ω : ℝ) : ℂ) +
        Complex.I * ((realRiemann (fun s ω => (f s ω).im) (B (x, 0)) t m ω +
          realRiemann (fun s ω => (f s ω).re) (B (x, 1)) t m ω : ℝ) : ℂ)) /
        (Real.sqrt 2 : ℂ) := by
  simp only [itoSum, realRiemann, complexBM, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  apply Complex.ext <;> simp <;> ring

/-- With `f = f₁ + i f₂` and `W = (B_{x,0} + i B_{x,1}) / √2`:
`itoSum f conj(W) = (R(f₁, B_{x,0}) + R(f₂, B_{x,1}) + i (R(f₂, B_{x,0}) - R(f₁, B_{x,1}))) / √2`,
where `R` is the real left-point Riemann sum. -/
theorem itoSum_conj_complexBM (f : ℝ → Ω → ℂ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ) (t : ℝ)
    (m : ℕ) (ω : Ω) :
    itoSum f (fun s ω => conj (complexBM B x s ω)) t m ω =
      (((realRiemann (fun s ω => (f s ω).re) (B (x, 0)) t m ω +
          realRiemann (fun s ω => (f s ω).im) (B (x, 1)) t m ω : ℝ) : ℂ) +
        Complex.I * ((realRiemann (fun s ω => (f s ω).im) (B (x, 0)) t m ω -
          realRiemann (fun s ω => (f s ω).re) (B (x, 1)) t m ω : ℝ) : ℂ)) /
        (Real.sqrt 2 : ℂ) := by
  simp only [itoSum, realRiemann, complexBM, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  apply Complex.ext <;> simp <;> ring

/-- The noise term of the equation of `ψ` (field `sde` of `IsWaveFunction`) in real form: with
`g = g₁ + i g₂`, `h = h₁ + i h₂` (in the application `g = ψ(x+1)`, `h = ψ(x-1)`),
`i itoSum g W⁽ˣ⁾ + i itoSum h conj(W⁽ˣ⁻¹⁾)` has real part
`-(R(g₂, B_{x,0}) + R(g₁, B_{x,1}) + R(h₂, B_{x-1,0}) - R(h₁, B_{x-1,1})) / √2` and imaginary
part `(R(g₁, B_{x,0}) - R(g₂, B_{x,1}) + R(h₁, B_{x-1,0}) + R(h₂, B_{x-1,1})) / √2`. -/
theorem itoSum_sde_eq_realRiemann (g h : ℝ → Ω → ℂ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ) (x : ℤ)
    (t : ℝ) (m : ℕ) (ω : Ω) :
    Complex.I * itoSum g (complexBM B x) t m ω +
        Complex.I * itoSum h (fun s ω => conj (complexBM B (x - 1) s ω)) t m ω =
      ((-(realRiemann (fun s ω => (g s ω).im) (B (x, 0)) t m ω +
            realRiemann (fun s ω => (g s ω).re) (B (x, 1)) t m ω +
            realRiemann (fun s ω => (h s ω).im) (B (x - 1, 0)) t m ω -
            realRiemann (fun s ω => (h s ω).re) (B (x - 1, 1)) t m ω) / Real.sqrt 2 : ℝ) : ℂ) +
        Complex.I * (((realRiemann (fun s ω => (g s ω).re) (B (x, 0)) t m ω -
            realRiemann (fun s ω => (g s ω).im) (B (x, 1)) t m ω +
            realRiemann (fun s ω => (h s ω).re) (B (x - 1, 0)) t m ω +
            realRiemann (fun s ω => (h s ω).im) (B (x - 1, 1)) t m ω) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [itoSum_complexBM, itoSum_conj_complexBM]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Complex random variables converge in measure if and only if their real parts and their
imaginary parts do (for any measure and any filter). -/
theorem tendstoInMeasure_complex_iff {κ : Type*} {l : Filter κ} (μ : Measure Ω)
    {F : κ → Ω → ℂ} {G : Ω → ℂ} :
    TendstoInMeasure μ F l G ↔
      TendstoInMeasure μ (fun k ω => (F k ω).re) l (fun ω => (G ω).re) ∧
        TendstoInMeasure μ (fun k ω => (F k ω).im) l (fun ω => (G ω).im) := by
  simp_rw [tendstoInMeasure_iff_norm]
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
        (fun _ => zero_le) fun k => measure_mono fun ω (hω : ε ≤ _) => ?_
      show ε ≤ ‖F k ω - G ω‖
      refine hω.trans ?_
      rw [Real.norm_eq_abs, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
        (fun _ => zero_le) fun k => measure_mono fun ω (hω : ε ≤ _) => ?_
      show ε ≤ ‖F k ω - G ω‖
      refine hω.trans ?_
      rw [Real.norm_eq_abs, ← Complex.sub_im]
      exact Complex.abs_im_le_norm _
  · rintro ⟨hre, him⟩ ε hε
    have h2 : 0 < ε / 2 := half_pos hε
    have hsum := (hre (ε / 2) h2).add (him (ε / 2) h2)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun k => (measure_mono fun ω (hω : ε ≤ _) => ?_).trans
        (measure_union_le _ _)
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs,
      ← Complex.sub_re, ← Complex.sub_im] at hcon
    have := Complex.norm_le_abs_re_add_abs_im (F k ω - G ω)
    linarith [hcon.1, hcon.2]

end QSSEPtoKPZ
