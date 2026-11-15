/-
Lean proof of Theorem 1.2 of G. Barraquand, "Convergence of the one-particle quantum symmetric
simple exclusion process to the KPZ equation" (2026). Written by Claude (Anthropic) at the
request of the author. See README.md and docs/stage4-design.md.
-/
module

public import QSSEPtoKPZ.Definitions
public import QSSEPtoKPZ.Replacement.CorrectorDefs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.LiminfLimsup

/-!
# Definitions for the limit points (Section 7.1 of the article)

STATEMENT FILE (task T0″ of Stage 4): these definitions are part of the statements of Section 7
submitted to the author (`docs/stage4-statements.md`). They are complete (no `sorry`).

`ℳ₊ = FiniteMeasure ℝ` (topology of weak convergence) and `C([0,T], ℳ₊)` is
`C(Set.Icc 0 T, FiniteMeasure ℝ)` with the compact-open topology and its **Borel** σ-algebra (the
instance used by the frozen statement of Theorem 1.2). Mathlib's own `MeasurableSpace` instance
on `FiniteMeasure ℝ` (the Giry σ-algebra) is never used: the Borel σ-algebra of `ℳ₊` is always
written `borel (FiniteMeasure ℝ)`.

* `pathAt γ t`: `γ(t)` for real `t`, `t` being projected on `[0,T]`.
* `pairFM μ f = μ(f) = ∫ f dμ`.
* `pathFiltrationCan T`: the canonical filtration `σ(γ(s) : s ≤ t)` of `C([0,T], ℳ₊)`.
* `pathFiltration Y`: the natural filtration `𝒢⁰_t = σ(𝒵(s) : s ≤ t)` of a path-valued map `Y`.
* `limMart Y φ φt`: the process `M^φ` of (7.2).
* `limBracket Z φ`: the process `∫_0^t ∫ Z(s,x)² φ_s(x)² dx ds` of (7.3).
* `limDensity ρ μ x`: `liminf_k (μ ⋆ ρ_{1/k})(x)` (`0` if infinite), proof of Prop. 7.1 (2).
* `limField ρ Y t x ω = limDensity ρ (Y(ω)(t)) x`: the density `Z(t,x)` of Prop. 7.1 (2).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace QSSEPtoKPZ

/-- `γ(t)` for a real `t`, with `t` projected on `[0,T]` (so `γ(t) = γ(0)` for `t < 0` and
`γ(t) = γ(T)` for `t > T`); `0` if `T < 0` (then `[0,T]` is empty). -/
def pathAt {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t : ℝ) : FiniteMeasure ℝ :=
  if h : 0 ≤ T then γ (Set.projIcc 0 T h t) else 0

/-- `μ(f) = ∫ f dμ`, for a finite measure `μ` on `ℝ` (the notation `𝒵(t;f)` of the article). -/
def pairFM (μ : FiniteMeasure ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, f x ∂(μ : Measure ℝ)

/-- The canonical filtration of `C([0,T], ℳ₊)`: `σ(γ ↦ γ(s) : s ∈ [0,T], s ≤ t)`, where `ℳ₊`
carries its Borel σ-algebra `borel (FiniteMeasure ℝ)` (not Mathlib's Giry instance). The
intersection with the Borel σ-algebra of `C([0,T], ℳ₊)` is there only to make the inclusion
`𝒢_t ≤ 𝒢_∞` hold by definition; it does not change the σ-algebra (task G2 proves it). -/
def pathFiltrationCan (T : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) where
  seq t := (⨆ s : Set.Icc (0 : ℝ) T, ⨆ (_ : (s : ℝ) ≤ t),
      (borel (FiniteMeasure ℝ)).comap fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => γ s) ⊓
    inferInstance
  mono' _ _ h := inf_le_inf_right _ (iSup_mono fun _ => iSup_mono' fun hs =>
    ⟨hs.trans (by exact_mod_cast h), le_rfl⟩)
  le' _ := inf_le_right

/-- The natural filtration `𝒢⁰_t = σ(Y(s) : s ≤ t)` of a map `Y : Ω → C([0,T], ℳ₊)`: the inverse
image of the canonical filtration (intersected with `mΩ`, which changes nothing when `Y` is
measurable). -/
def pathFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} {T : ℝ}
    (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : Filtration ℝ≥0 mΩ where
  seq t := ((pathFiltrationCan T t).comap Y) ⊓ mΩ
  mono' _ _ h := inf_le_inf_right _ (MeasurableSpace.comap_mono ((pathFiltrationCan T).mono h))
  le' _ := inf_le_right

variable {Ω : Type*}

/-- The process (7.2):
`M^φ(t) = 𝒵(t;φ_t) - φ_0(0) - ∫_0^t 𝒵(s; ∂ₛφ_s + ½ ∂ₓ²φ_s) ds`, where `𝒵(t) = Y(ω)(t)` and
`φt` is the time derivative of `φ` (as in `IsC13`). -/
def limMart {T : ℝ} (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (φ φt : ℝ → ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  pairFM (pathAt (Y ω) t) (φ t) - φ 0 0 -
    ∫ s in (0 : ℝ)..t, pairFM (pathAt (Y ω) s) (fun x => φt s x + iteratedDeriv 2 (φ s) x / 2)

/-- The process (7.3): `∫_0^t ∫_ℝ Z(s,x)² φ_s(x)² dx ds`. -/
def limBracket (Z : ℝ → ℝ → Ω → ℝ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, ∫ x, Z s x ω ^ 2 * φ s x ^ 2

/-- `liminf_{k → ∞} (μ ⋆ ρ_{1/(k+1)})(x)`, where `(μ ⋆ ρ_ε)(x) = ∫ ρ_ε(x - y) μ(dy)`, and `0` if
this liminf is infinite (proof of Proposition 7.1 (2)). The liminf is taken in `[0, ∞]`; the
convolutions are genuine integrals (bounded continuous integrand, finite measure) when `ρ` is a
mollifier. -/
def limDensity (ρ : ℝ → ℝ) (μ : FiniteMeasure ℝ) (x : ℝ) : ℝ :=
  (liminf (fun k : ℕ => ENNReal.ofReal
    (∫ y, rhoEps ρ (1 / ((k : ℝ) + 1)) (x - y) ∂(μ : Measure ℝ))) atTop).toReal

/-- The random field `Z(t,x) = liminf_k (𝒵(t) ⋆ ρ_{1/k})(x)` (`0` if infinite) of
Proposition 7.1 (2), for `𝒵 = Y(ω)`. -/
def limField {T : ℝ} (ρ : ℝ → ℝ) (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t x : ℝ)
    (ω : Ω) : ℝ :=
  limDensity ρ (pathAt (Y ω) t) x

end QSSEPtoKPZ
