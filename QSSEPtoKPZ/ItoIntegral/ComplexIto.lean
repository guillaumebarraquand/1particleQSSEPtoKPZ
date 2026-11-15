/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.ItoIntegral.Product

/-!
# Complex Itô processes and the product rule for `\bar z w` (task G11b)

INTERFACE FILE (task I0‴ of Stage 5, `docs/stage5-interfaces.md`); the proofs are task G11b.
`docs/stage5-design.md`, Section 3.3.

`IsCItoProcessUpTo 𝓖 μ B τ Z a b` (definition, complete): the real and imaginary parts of the
complex process `Z` are Itô processes up to `τ` (`IsItoProcessUpTo`) with the real and imaginary
parts of the complex drift `a` and of the complex diffusion coefficients `b`:
`Z_{t∧τ} = Z_0 + ∫_0^{t∧τ} a ds + ∑ᵢ ∫_0^t bᵢ 𝟙_{s ≤ τ} dBᵢ` (real Brownian motions `Bᵢ`).

* `IsCItoProcessUpTo.conj_mul`: product rule for `\bar Z W`,
  `d(\bar Z W) = (\bar Z c + W \bar a + ∑ᵢ \bar bᵢ dᵢ) ds + ∑ᵢ (\bar Z dᵢ + W \bar bᵢ) dBᵢ`
  (four applications of `IsItoProcessUpTo.mul`);
* `IsCItoProcessUpTo.add`, `.const_mul` (complex constant), `.finset_sum`.

Proof (task G11b): with `Z = X + iY`, `W = U + iV`, `Re(\bar Z W) = XU + YV` and
`Im(\bar Z W) = XV - YU`; the four real products come from `IsItoProcessUpTo.mul`, and the
coefficients are identified pointwise. The square-summability of `b`, `d` gives the convergence
of `∑ᵢ \bar bᵢ dᵢ` and of the four real series `∑ᵢ Re/Im bᵢ · Re/Im dᵢ`, so that the real and
imaginary parts of the complex `tsum` split (`Complex.re_tsum`, `Summable.tsum_add`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate

noncomputable section

namespace QSSEPtoKPZ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Complex Itô process up to a stopping time**: the real and imaginary parts of `Z` are Itô
processes up to `τ` with drifts `Re a`, `Im a` and diffusion coefficients `Re bᵢ`, `Im bᵢ`. -/
def IsCItoProcessUpTo (𝓖 : Filtration ℝ≥0 mΩ) {ι : Type*} (μ : Measure Ω)
    (B : ι → ℝ → Ω → ℝ) (τ : Ω → ℝ≥0) (Z a : ℝ → Ω → ℂ) (b : ι → ℝ → Ω → ℂ) : Prop :=
  IsItoProcessUpTo 𝓖 μ B τ (fun t ω => (Z t ω).re) (fun s ω => (a s ω).re)
      (fun i s ω => (b i s ω).re) ∧
    IsItoProcessUpTo 𝓖 μ B τ (fun t ω => (Z t ω).im) (fun s ω => (a s ω).im)
      (fun i s ω => (b i s ω).im)

variable {ι : Type*} [Countable ι] {𝓖 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ι → ℝ → Ω → ℝ}

/-! ### Auxiliary lemmas -/

omit [Countable ι] [IsProbabilityMeasure μ] in
/-- Rewriting the process, drift and diffusion coefficients of an Itô process pointwise. -/
private lemma cIto_congr {τ : Ω → ℝ≥0} {X X' a a' : ℝ → Ω → ℝ} {b b' : ι → ℝ → Ω → ℝ}
    (h : IsItoProcessUpTo 𝓖 μ B τ X a b) (hX : ∀ t ω, X t ω = X' t ω)
    (ha : ∀ s ω, a s ω = a' s ω) (hb : ∀ i s ω, b i s ω = b' i s ω) :
    IsItoProcessUpTo 𝓖 μ B τ X' a' b' := by
  have e1 : X = X' := funext fun t => funext (hX t)
  have e2 : a = a' := funext fun s => funext (ha s)
  have e3 : b = b' := funext fun i => funext fun s => funext (hb i s)
  subst e1 e2 e3
  exact h

/-- For `f = Re` or `Im`: `f(z)² ≤ |z|²`. -/
private lemma cIto_sq_le {f : ℂ → ℝ} (hf : ∀ z, |f z| ≤ ‖z‖) (z : ℂ) : f z ^ 2 ≤ ‖z‖ ^ 2 :=
  (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (hf z) 2)

omit [Countable ι] in
/-- For `f = Re` or `Im`: if `∑ᵢ |bᵢ|² < ∞` then `∑ᵢ f(bᵢ)² ≤ ∑ᵢ |bᵢ|²`. -/
private lemma cIto_tsum_sq_le {f : ℂ → ℝ} (hf : ∀ z, |f z| ≤ ‖z‖) {b : ι → ℂ}
    (hb : Summable fun i => ‖b i‖ ^ 2) : (∑' i, f (b i) ^ 2) ≤ ∑' i, ‖b i‖ ^ 2 :=
  (hb.of_nonneg_of_le (fun _ => sq_nonneg _) fun _ => cIto_sq_le hf _).tsum_le_tsum
    (fun i => cIto_sq_le hf (b i)) hb

omit [Countable ι] in
/-- For `f, g ∈ {Re, Im}`: `∑ᵢ f(bᵢ) g(dᵢ)` converges when `∑ᵢ |bᵢ|²`, `∑ᵢ |dᵢ|²` do
(`|xy| ≤ (x² + y²)/2`). -/
private lemma cIto_summable_mul {f g : ℂ → ℝ} (hf : ∀ z, |f z| ≤ ‖z‖) (hg : ∀ z, |g z| ≤ ‖z‖)
    {b d : ι → ℂ} (hb : Summable fun i => ‖b i‖ ^ 2) (hd : Summable fun i => ‖d i‖ ^ 2) :
    Summable fun i => f (b i) * g (d i) := by
  refine Summable.of_norm_bounded ((hb.add hd).div_const 2) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hf (b i)
  have h2 := hg (d i)
  have h3 := abs_nonneg (f (b i))
  have h4 := abs_nonneg (g (d i))
  nlinarith [sq_nonneg (‖b i‖ - ‖d i‖)]

omit [Countable ι] in
/-- `∑ᵢ \bar bᵢ dᵢ` converges when `∑ᵢ |bᵢ|²`, `∑ᵢ |dᵢ|²` do. -/
private lemma cIto_summable_conj_mul {b d : ι → ℂ} (hb : Summable fun i => ‖b i‖ ^ 2)
    (hd : Summable fun i => ‖d i‖ ^ 2) : Summable fun i => conj (b i) * d i := by
  refine Summable.of_norm_bounded ((hb.add hd).div_const 2) fun i => ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖b i‖ - ‖d i‖)]

omit [Countable ι] in
/-- Real part of `∑ᵢ \bar bᵢ dᵢ`. -/
private lemma cIto_re_tsum {b d : ι → ℂ} (hb : Summable fun i => ‖b i‖ ^ 2)
    (hd : Summable fun i => ‖d i‖ ^ 2) :
    (∑' i, conj (b i) * d i).re =
      (∑' i, (b i).re * (d i).re) + ∑' i, (b i).im * (d i).im := by
  rw [Complex.re_tsum (cIto_summable_conj_mul hb hd), ← Summable.tsum_add
    (cIto_summable_mul Complex.abs_re_le_norm Complex.abs_re_le_norm hb hd)
    (cIto_summable_mul Complex.abs_im_le_norm Complex.abs_im_le_norm hb hd)]
  congr 1
  funext i
  simp [Complex.mul_re]

omit [Countable ι] in
/-- Imaginary part of `∑ᵢ \bar bᵢ dᵢ`. -/
private lemma cIto_im_tsum {b d : ι → ℂ} (hb : Summable fun i => ‖b i‖ ^ 2)
    (hd : Summable fun i => ‖d i‖ ^ 2) :
    (∑' i, conj (b i) * d i).im =
      (∑' i, (b i).re * (d i).im) + -1 * ∑' i, (b i).im * (d i).re := by
  rw [Complex.im_tsum (cIto_summable_conj_mul hb hd), ← tsum_mul_left, ← Summable.tsum_add
    (cIto_summable_mul Complex.abs_re_le_norm Complex.abs_im_le_norm hb hd)
    ((cIto_summable_mul Complex.abs_im_le_norm Complex.abs_re_le_norm hb hd).mul_left (-1))]
  congr 1
  funext i
  simp [Complex.mul_im]

omit [Countable ι] in
/-- The bounds required by the real product rule, for the parts `f(Z)`, `g(W)` (`f, g ∈
{Re, Im}`), from the bounds on the complex processes. -/
private lemma cIto_bd {f g : ℂ → ℝ} (hf : ∀ z, |f z| ≤ ‖z‖) (hg : ∀ z, |g z| ≤ ‖z‖) {K : ℝ}
    {z w a c : ℂ} {b d : ι → ℂ} (hb : Summable fun i => ‖b i‖ ^ 2)
    (hd : Summable fun i => ‖d i‖ ^ 2)
    (h : ‖z‖ ≤ K ∧ ‖w‖ ≤ K ∧ ‖a‖ ≤ K ∧ ‖c‖ ≤ K ∧
      (∑' i, ‖b i‖ ^ 2) ≤ K ∧ (∑' i, ‖d i‖ ^ 2) ≤ K) :
    |f z| ≤ K ∧ |g w| ≤ K ∧ |f a| ≤ K ∧ |g c| ≤ K ∧
      (∑' i, f (b i) ^ 2) ≤ K ∧ (∑' i, g (d i) ^ 2) ≤ K :=
  ⟨(hf z).trans h.1, (hg w).trans h.2.1, (hf a).trans h.2.2.1, (hg c).trans h.2.2.2.1,
    (cIto_tsum_sq_le hf hb).trans h.2.2.2.2.1, (cIto_tsum_sq_le hg hd).trans h.2.2.2.2.2⟩

/-- **Product rule for `\bar Z W`.** Let `τ` be a bounded stopping time, and `Z`, `W` complex
Itô processes up to `τ` (drifts `a`, `c`, coefficients `b`, `d`), with all paths continuous and
adapted, the coefficient families square-summable, and `|Z|, |W|, |a|, |c|, ∑ᵢ |bᵢ|²,
∑ᵢ |dᵢ|² ≤ K` on `[0, τ]`. Then `\bar Z W` is a complex Itô process up to `τ`:
`d(\bar Z W) = (\bar Z c + W \bar a + ∑ᵢ \bar bᵢ dᵢ) ds + ∑ᵢ (\bar Z dᵢ + W \bar bᵢ) dBᵢ`. -/
theorem IsCItoProcessUpTo.conj_mul (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T)
    {Z W a c : ℝ → Ω → ℂ} {b d : ι → ℝ → Ω → ℂ} {K : ℝ}
    (hZ : IsCItoProcessUpTo 𝓖 μ B τ Z a b) (hW : IsCItoProcessUpTo 𝓖 μ B τ W c d)
    (hZc : ∀ ω, Continuous fun t : ℝ≥0 => Z t ω) (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω)
    (hZa : ∀ t : ℝ≥0, Measurable[𝓖 t] (Z t)) (hWa : ∀ t : ℝ≥0, Measurable[𝓖 t] (W t))
    (hbs : ∀ ω (s : ℝ), Summable fun i => ‖b i s ω‖ ^ 2)
    (hds : ∀ ω (s : ℝ), Summable fun i => ‖d i s ω‖ ^ 2)
    (hbd : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω →
      ‖Z s ω‖ ≤ K ∧ ‖W s ω‖ ≤ K ∧ ‖a s ω‖ ≤ K ∧ ‖c s ω‖ ≤ K ∧
      ∑' i, ‖b i s ω‖ ^ 2 ≤ K ∧ ∑' i, ‖d i s ω‖ ^ 2 ≤ K) :
    IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => conj (Z t ω) * W t ω)
      (fun s ω => conj (Z s ω) * c s ω + W s ω * conj (a s ω) + ∑' i, conj (b i s ω) * d i s ω)
      (fun i s ω => conj (Z s ω) * d i s ω + W s ω * conj (b i s ω)) := by
  obtain ⟨hZr, hZi⟩ := hZ
  obtain ⟨hWr, hWi⟩ := hW
  have hre := Complex.abs_re_le_norm
  have him := Complex.abs_im_le_norm
  have cre : ∀ {V : ℝ → Ω → ℂ}, (∀ ω, Continuous fun t : ℝ≥0 => V t ω) →
      ∀ ω, Continuous fun t : ℝ≥0 => (V t ω).re := fun h ω => Complex.continuous_re.comp (h ω)
  have cim : ∀ {V : ℝ → Ω → ℂ}, (∀ ω, Continuous fun t : ℝ≥0 => V t ω) →
      ∀ ω, Continuous fun t : ℝ≥0 => (V t ω).im := fun h ω => Complex.continuous_im.comp (h ω)
  have are : ∀ {V : ℝ → Ω → ℂ}, (∀ t : ℝ≥0, Measurable[𝓖 t] (V t)) →
      ∀ t : ℝ≥0, Measurable[𝓖 t] fun ω => (V t ω).re :=
    fun h t => Complex.measurable_re.comp (h t)
  have aim : ∀ {V : ℝ → Ω → ℂ}, (∀ t : ℝ≥0, Measurable[𝓖 t] (V t)) →
      ∀ t : ℝ≥0, Measurable[𝓖 t] fun ω => (V t ω).im :=
    fun h t => Complex.measurable_im.comp (h t)
  -- the four real products `Re Z Re W`, `Im Z Im W`, `Re Z Im W`, `Im Z Re W`
  have P1 := hZr.mul hB hτ hτb hWr (cre hZc) (cre hWc) (are hZa) (are hWa)
    (fun ω s hs h => cIto_bd hre hre (hbs ω s) (hds ω s) (hbd ω s hs h))
  have P2 := hZi.mul hB hτ hτb hWi (cim hZc) (cim hWc) (aim hZa) (aim hWa)
    (fun ω s hs h => cIto_bd him him (hbs ω s) (hds ω s) (hbd ω s hs h))
  have P3 := hZr.mul hB hτ hτb hWi (cre hZc) (cim hWc) (are hZa) (aim hWa)
    (fun ω s hs h => cIto_bd hre him (hbs ω s) (hds ω s) (hbd ω s hs h))
  have P4 := hZi.mul hB hτ hτb hWr (cim hZc) (cre hWc) (aim hZa) (are hWa)
    (fun ω s hs h => cIto_bd him hre (hbs ω s) (hds ω s) (hbd ω s hs h))
  refine ⟨cIto_congr (P1.add hB P2) ?_ ?_ ?_,
    cIto_congr (P3.add hB (P4.const_mul hB (-1))) ?_ ?_ ?_⟩
  · intro t ω
    simp [Complex.mul_re]
  · intro s ω
    simp only [Complex.add_re, cIto_re_tsum (hbs ω s) (hds ω s)]
    simp [Complex.mul_re]
    ring
  · intro i s ω
    simp [Complex.mul_re]
    ring
  · intro t ω
    simp [Complex.mul_im]
  · intro s ω
    simp only [Complex.add_im, cIto_im_tsum (hbs ω s) (hds ω s)]
    simp [Complex.mul_im]
    ring
  · intro i s ω
    simp [Complex.mul_im]
    ring

/-- **Sum** of two complex Itô processes up to the same `τ`. -/
theorem IsCItoProcessUpTo.add (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {Z W a c : ℝ → Ω → ℂ} {b d : ι → ℝ → Ω → ℂ}
    (hZ : IsCItoProcessUpTo 𝓖 μ B τ Z a b) (hW : IsCItoProcessUpTo 𝓖 μ B τ W c d) :
    IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => Z t ω + W t ω) (fun s ω => a s ω + c s ω)
      (fun i s ω => b i s ω + d i s ω) := by
  refine ⟨cIto_congr (hZ.1.add hB hW.1) (fun t ω => by simp) (fun s ω => by simp)
    (fun i s ω => by simp), cIto_congr (hZ.2.add hB hW.2) (fun t ω => by simp)
    (fun s ω => by simp) (fun i s ω => by simp)⟩

/-- **Complex constant multiple** of a complex Itô process. -/
theorem IsCItoProcessUpTo.const_mul (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {Z a : ℝ → Ω → ℂ} {b : ι → ℝ → Ω → ℂ} (hZ : IsCItoProcessUpTo 𝓖 μ B τ Z a b) (k : ℂ) :
    IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => k * Z t ω) (fun s ω => k * a s ω)
      (fun i s ω => k * b i s ω) := by
  refine ⟨cIto_congr ((hZ.1.const_mul hB k.re).add hB (hZ.2.const_mul hB (-k.im)))
    (fun t ω => by simp only [Complex.mul_re]; ring)
    (fun s ω => by simp only [Complex.mul_re]; ring)
    (fun i s ω => by simp only [Complex.mul_re]; ring),
    cIto_congr ((hZ.2.const_mul hB k.re).add hB (hZ.1.const_mul hB k.im))
    (fun t ω => by simp only [Complex.mul_im]) (fun s ω => by simp only [Complex.mul_im])
    (fun i s ω => by simp only [Complex.mul_im])⟩

/-- **Finite sum** of complex Itô processes up to the same `τ` (e.g. over the sites of a box). -/
theorem IsCItoProcessUpTo.finset_sum (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {κ : Type*} (S : Finset κ) {Z a : κ → ℝ → Ω → ℂ} {b : κ → ι → ℝ → Ω → ℂ}
    (hZ : ∀ k ∈ S, IsCItoProcessUpTo 𝓖 μ B τ (Z k) (a k) (b k)) :
    IsCItoProcessUpTo 𝓖 μ B τ (fun t ω => ∑ k ∈ S, Z k t ω) (fun s ω => ∑ k ∈ S, a k s ω)
      (fun i s ω => ∑ k ∈ S, b k i s ω) := by
  refine ⟨cIto_congr (IsItoProcessUpTo.finset_sum hB S fun k hk => (hZ k hk).1)
    (fun t ω => by simp [Complex.re_sum]) (fun s ω => by simp [Complex.re_sum])
    (fun i s ω => by simp [Complex.re_sum]),
    cIto_congr (IsItoProcessUpTo.finset_sum hB S fun k hk => (hZ k hk).2)
    (fun t ω => by simp [Complex.im_sum]) (fun s ω => by simp [Complex.im_sum])
    (fun i s ω => by simp [Complex.im_sum])⟩

end QSSEPtoKPZ
