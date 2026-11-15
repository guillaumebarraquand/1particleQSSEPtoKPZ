/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage5-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.WhiteNoise.Isonormal
public import QSSEPtoKPZ.WhiteNoise.ExistenceBuild
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Existence of space-time white noise (companion E2; task E2b)

STATEMENT FILE (task T0‴ of Stage 5, `docs/stage5-statements.md`); the proof is task E2b, in this
file (`docs/stage5-design.md`, Section 1.2 (g), decision D4‴): `exists_isonormal` with
`H = L²(ℝ²)` (`Lp ℝ 2 (volume : Measure (ℝ × ℝ))`, indicators by `indicatorConstLp`),
`S(t,x) = W(𝟙_{(0,t]×(0,x]})` for `x ≥ 0` and `-W(𝟙_{(0,t]×(x,0]})` for `x < 0`,
`𝓖_t = σ(S(r,x) : r ≤ t, x ∈ ℝ)`; the three clauses of `IsWhiteNoise` from Mathlib's
`IsGaussianProcess.iIndepFun_of_covariance_eq_zero` and `indepFun_of_covariance_eq_zero`.

Proved (task E2b): the construction and the three clauses are in `WhiteNoise/ExistenceBuild.lean`
(`wnExist_isWhiteNoise`), applied to the isonormal process of `exists_isonormal`.

`exists_isWhiteNoise_lib` is the companion statement **E2** of `Companions.lean`
(`exists_isWhiteNoise`), word for word (checked with `pp.all` and by the kernel).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal lp

noncomputable section

namespace QSSEPtoKPZ

/-- **E2** (existence of space-time white noise; used implicitly throughout Section 7), library
copy of `exists_isWhiteNoise`. There are a probability space, a filtration and a random field
`S` which is the distribution function of a space-time white noise with respect to this
filtration. -/
theorem exists_isWhiteNoise_lib :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ν : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ)
      (S : ℝ → ℝ → Ω → ℝ),
      IsProbabilityMeasure ν ∧ IsWhiteNoise 𝓖 S ν := by
  obtain ⟨Ω, mΩ, P, W, hP, hW, hGP, hlaw, hcov, hlin⟩ :=
    exists_isonormal (Lp ℝ 2 (volume : Measure (ℝ × ℝ)))
  exact ⟨Ω, mΩ, P, wnExistFilt (wnExistS W) (fun _ _ => hW _), wnExistS W, hP,
    wnExist_isWhiteNoise hW hGP hlaw hcov hlin⟩

end QSSEPtoKPZ
