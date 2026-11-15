# Stage 2: interfaces of packages B and C (task I0)

Written on 12 November 2026 by the I0 agent (Opus 5.5). For the main session and the proving agents. The Lean files are the reference; this list gives one line per interface theorem: name, file (under `QSSEPtoKPZ/`), meaning. Lemmas marked **(proved)** were proved in I0; all others are `sorry` and belong to the task named in the heading. Section 2 of `docs/stage2-design.md` is the specification; the departures from it are listed at the end.

Conventions common to all files: processes are `X : ℝ → Ω → E`, only `t ≥ 0` matters; filtrations are `Filtration ℝ≥0 mΩ`; stopping times are `τ : Ω → ℝ≥0` coerced to `WithTop ℝ≥0`; integrands are families `h : ι → ℝ → Ω → ℝ` of which only the values at times `s > 0` matter; `I_t(h) = stochInt 𝓖 μ B h t`. Package C assumes `[Countable ι]`, `[IsProbabilityMeasure μ]`, `hB : IsBrownianFamily 𝓖 B μ`; package B assumes `[IsFiniteMeasure μ]` where needed.

## Definitions (complete, no `sorry`)

| Name | File | Meaning |
|---|---|---|
| `hitTime X K T` | `Martingales/Stopping.lean` | first time `X_t ≥ K`, capped at `T` |
| `ElemBlock 𝓖 ι` | `ItoIntegral/Elementary.lean` | block `ξ 𝟙_{(a,b]} eᵢ`, `a ≤ b`, `ξ` bounded `𝓖_a`-measurable |
| `ElemIntegrand 𝓖 ι` | same | `List (ElemBlock 𝓖 ι)` |
| `ElemIntegrand.toFun`, `.integral`, `.smul`, `ElemBlock.smul` | same | represented family; `∑ ξ (Bᵢ(b∧t) - Bᵢ(a∧t))`; multiplication by a constant |
| `pathEnergy h T ω`, `energy μ h T` | same | `∫_0^T ∑ᵢ hᵢ² ds` pathwise / in expectation, in `[0,∞]` |
| `IsItoIntegrable 𝓖 μ h` | `ItoIntegral/Basic.lean` | jointly measurable on `(0,∞)×Ω`, energy limit (on every `[0,T]`) of one sequence of elementary integrands |
| `stochInt 𝓖 μ B h t ω` | same | pathwise `limUnder` of elementary integrals along the fast sequence of `IsItoIntegrable.exists_fast` (proved); `0` if not integrable |
| `realRiemann f W t m ω` | `ItoIntegral/Riemann.lean` | `∑_{k<m} f(t_k)(W(t_{k+1}) - W(t_k))`, `t_k = kt/m` (real `itoSum`) |
| `IsItoProcessUpTo 𝓖 μ B τ X a b` | `ItoIntegral/Product.lean` | `b𝟙_{s≤τ}` integrable, `a` integrable on `[0,τ]` a.s., and a.s. `∀ t`, `X_{t∧τ} = X_0 + ∫_0^{t∧τ} a + I_t(b𝟙_{s≤τ})` |

## B1 — `Martingales/NullAug.lean` (uses: `Defs.lean` only)

- `measurableSet_nullSets` **(proved)**: a measurable null set is in `nullSets μ`.
- `nullSets_le_nullAug` **(proved)**: `nullSets μ ≤ 𝓕ᵃ_t`.
- `measurableSet_nullAug_iff`: `G ∈ 𝓕ᵃ_t` ⇔ `G` measurable and `G =ᵐ F` for some `F ∈ 𝓕_t`.
- `condExp_sup_nullSets`: `𝔼[X | m ∨ σ(null sets)] = 𝔼[X | m]` a.s. (finite measure).
- `condExp_nullAug`: `𝔼[X | 𝓕ᵃ_t] = 𝔼[X | 𝓕_t]` a.s.
- `aestronglyMeasurable_of_nullAug`: `𝓕ᵃ_t`-measurable ⇒ a.e. equal to `𝓕_t`-measurable.
- `stronglyMeasurable_nullAug_of_ae`: measurable and a.e. equal to `𝓕_t`-measurable ⇒ `𝓕ᵃ_t`-measurable.
- `IsBrownianFamily.nullAug`: a Brownian family for `𝓕` is one for `𝓕ᵃ`.
- `IsWaveFunction.nullAug`: a wave function for `𝓕` is one for `𝓕ᵃ`.
- `exists_continuous_version`: `𝓖 ⊇ null sets`, adapted, a.s. continuous ⇒ indistinguishable version, adapted, all paths continuous.
- `IsWaveFunction.exists_good`: version `ψ'` of `ψ`, wave function for `𝓕ᵃ`, all paths continuous, zero outside `Λ_L` for all `ω`.
- `IsCL2Mart.exists_version`: version of a continuous `L²` martingale, `𝓕ᵃ`-adapted, all paths continuous on `[0,T]`, indistinguishable on `[0,T]`, `IsCL2Mart` for `𝓕ᵃ`.
- `isCL2Mart_nullAug_iff`, `hasBracket_nullAug_iff`: `IsCL2Mart`/`HasBracket` for `𝓕ᵃ` ⇔ for `𝓕`.
- `IsCL2Mart.congr`, `HasBracket.congr` (needs `0 ≤ T`): stable under indistinguishability on `[0,T]`.
- `IsCL2Mart.mono_horizon`, `HasBracket.mono_horizon`: restriction from `[0,T]` to `[0,S]`, `S ≤ T`.
- `IsCL2Mart.timeChange`, `HasBracket.timeChange`: on `[0,cT]` for `𝓕` ⇒ `t ↦ M_{ct}` (and `A_{ct}`) on `[0,T]` for `timeChange c 𝓕`.
- `IsCL2Mart.const_mul`, `HasBracket.const_mul`: `cM`, bracket `c²A`.
- `IsCL2Mart.add`: sum of two continuous `L²` martingales.
- `isCL2Mart_of_martingale`: Mathlib `Martingale` + a.s. continuity on `[0,T]` + `L²` ⇒ `IsCL2Mart`.
- `IsCL2Mart.martingale_stopped`: adapted `IsCL2Mart` on `[0,T]`, frozen after `T` ⇒ Mathlib `Martingale`.

## B2 — `Martingales/Doob.lean` (uses: `Defs.lean`; Mathlib `maximal_ineq`)

- `lintegral_iSup_sq_le_of_submartingale`: nonnegative submartingale, `𝔼 max_{k≤n} f_k² ≤ 4 𝔼 f_n²`.
- `lintegral_iSup_sq_le_of_martingale`: martingale, same inequality.
- `IsCL2Mart.lintegral_iSup_sq_le`: `sup_{[0,T]} M²` a.e. measurable and `𝔼 sup_{[0,T]} M² ≤ 4 𝔼 M_T²`.
- `IsCL2Mart.measure_exists_ge_le`: `M ≥ 0` on `[0,T]` ⇒ `ℙ(∃ t ≤ T, M_t ≥ K) ≤ 𝔼 M_T / K`.

## B3 — `Martingales/Stopping.lean` (uses: B1, B2 interfaces)

- `hitTime_le` **(proved)**: `hitTime ≤ T`.
- `lt_of_lt_hitTime` **(proved)**: `t < hitTime` ⇒ `X_t < K`.
- `hitTime_eq_of_forall_lt` **(proved)**: `X < K` on `[0,T)` ⇒ `hitTime = T`.
- `isStoppingTime_hitTime`: all paths continuous + adapted ⇒ `hitTime` is a stopping time of the raw filtration.
- `le_of_le_hitTime`: continuous path, `X_0 ≤ K`, `t ≤ hitTime` ⇒ `X_t ≤ K`.
- `condExp_stopped_of_forall`: `𝔼[V_t|𝓕_t] = Y_t` for deterministic `t ≤ T`, a.s. continuity, domination of `sup(|V|+|Y|)` ⇒ `𝔼[V_τ|𝓕_τ] = Y_τ` for stopping times `τ ≤ T` of `𝓕ᵃ`.
- `IsCL2Mart.condExp_stopped`: optional sampling `𝔼[M_τ|𝓕_σ] = M_σ`, `σ ≤ τ ≤ T` stopping times of `𝓕ᵃ`.
- `IsCL2Mart.stopped`: `M_{·∧τ}` is a continuous `L²` martingale on `[0,T]` (for `𝓕`).
- `HasBracket.stopped`: `⟨M_{·∧τ}⟩ = A_{·∧τ}` on `[0,T]` (for `𝓕`).

## C1 — `ItoIntegral/Elementary.lean` (uses: `Defs.lean`, Brownian family)

- `toFun_nil`, `toFun_append`, `integral_nil`, `integral_append`, `toFun_smul`, `integral_smul`, `integral_of_nonpos` **(proved)**: algebra of lists of blocks; `I_t(e) = 0` for `t ≤ 0`.
- `ElemIntegrand.integral_adapted`: `I_t(e)` is `𝓖_t`-measurable for every `ω`.
- `ElemIntegrand.integral_continuous`: a.s. continuous paths.
- `ElemIntegrand.memLp_integral`: `I_t(e) ∈ L^p`, `p < ∞`.
- `ElemIntegrand.hasBracket_integral`: `HasBracket T 𝓖 I(e) (∫_0^t ∑ᵢ eᵢ²)`.
- `ElemIntegrand.condExp_integral_mul`: cross bracket `⟨I(e),I(e')⟩ = ∫ ∑ᵢ eᵢe'ᵢ`.
- `ElemIntegrand.lintegral_integral_sq`: isometry `𝔼 I_t(e)² = energy e t`.

## C2 — `ItoIntegral/FourthMoment.lean` (uses: C1 proved, C3 interface)

- `lintegral_elem_integral_sub_pow_four_le`: `∑ᵢ eᵢ² ≤ K` on `(u,v]` ⇒ `𝔼(I_v(e) - I_u(e))⁴ ≤ 6K²(v-u)²`.
- `lintegral_stochInt_sub_pow_four_le`: same for Itô-integrable `h`.

## C3 — `ItoIntegral/Basic.lean` (uses: C1 proved, B2 interface)

- `IsItoIntegrable.exists_fast` **(proved)**: elementary `e_k` with `energy(e_k - h, k) ≤ 8⁻ᵏ`.
- `stochInt_of_nonpos` **(proved)**: `I_t(h) = 0` for `t ≤ 0`, every `ω`.
- `isItoIntegrable_zero` **(proved)**: `0` is Itô-integrable.
- `stochInt_adapted`: `I_t(h)` is `𝓖_t`-measurable for every `ω` (any `h`).
- `stochInt_continuous`: a.s. continuous on `[0,∞)`.
- `IsItoIntegrable.energy_lt_top`: finite energy on every `[0,T]`.
- `isItoIntegrable_elem`, `stochInt_elem`: elementary integrands; `I(e.toFun) = e.integral` a.s. for all `t`.
- `stochInt_zero`: `I(0) = 0` a.s. for all `t`.
- `IsItoIntegrable.add`, `stochInt_add`; `IsItoIntegrable.const_mul`, `stochInt_const_mul`; `IsItoIntegrable.finset_sum`, `stochInt_finset_sum`: linearity, a.s. for all `t`.
- `IsItoIntegrable.congr`: zero energy distance + measurability ⇒ integrable.
- `stochInt_congr`: zero energy distance on `[0,T]` ⇒ same integral on `[0,T]` a.s. (locality).
- `lintegral_stochInt_sq`: isometry `𝔼 I_t(h)² = energy h t`.
- `hasBracket_stochInt`: `HasBracket T 𝓖 I(h) (∫_0^t ∑ᵢ hᵢ²)` for every `T`.
- `condExp_stochInt_mul`: cross bracket `⟨I(h),I(g)⟩_t = ∫_0^t ∑ᵢ hᵢgᵢ`.
- `lintegral_iSup_stochInt_sq_le`: `𝔼 sup_{[0,T]} I(h)² ≤ 4 energy h T`.
- `tendsto_lintegral_iSup_stochInt_sub`: energy convergence on `[0,T]` ⇒ `𝔼 sup_{[0,T]} (I(h_k) - I(g))² → 0`.

## C4 — `ItoIntegral/Integrands.lean`, `ItoIntegral/Riemann.lean` (uses: C3 interface)

- `IsItoIntegrable.of_tendsto`: closure under energy limits (on every `[0,T]`).
- `isItoIntegrable_of_leftContinuous`: `∑ᵢ hᵢ² ≤ K` (summable), adapted, componentwise left-continuous at `s > 0` ⇒ integrable.
- `IsItoIntegrable.indicator_stoppingTime`: `h 𝟙_{s≤τ}` for a stopping time `τ` of `𝓖`.
- `IsItoIntegrable.mul_leftContinuous`: `Z h`, `Z` bounded, adapted, left-continuous.
- `IsItoIntegrable.mul_indicator_gt`: `ξ 𝟙_{s>u} h`, `ξ` bounded `𝓖_u`-measurable.
- `IsItoIntegrable.indicator_index`: `h 𝟙_{i∈S}`.
- `tendsto_riemann_stochInt`: bounded, adapted, left-continuous `f` ⇒ `f 𝟙_{j=i}` integrable and `realRiemann f (B i) t m → I_t(f 𝟙_{j=i})` in `L²`.
- `tendsto_riemann_stochInt_finset`: same for `∑_{j∈S}` (finitely many Brownian motions).

## C5 — `ItoIntegral/Stopping.lean` (uses: C3, C4, B3 interfaces)

- `stochInt_indicator_stoppingTime`: `I_t(h 𝟙_{s≤τ}) = I_{t∧τ}(h)` a.s. for all `t`.
- `stochInt_mul_indicator_gt`: `I_t(ξ 𝟙_{s>u} h) = ξ (I_t(h) - I_{t∧u}(h))` a.s. for all `t`.

## C6 — `ItoIntegral/Product.lean` (uses: C2–C5 interfaces)

- `IsItoProcessUpTo.mul`: **product rule** up to a bounded stopping time, with `|X|,|Y|,|a|,|c|,∑bᵢ²,∑dᵢ² ≤ K` on `[0,τ]`: `d(XY) = (Xc + Ya + ∑ᵢbᵢdᵢ)ds + (Xd + Yb)dB`.
- `IsItoProcessUpTo.add`, `.const_mul`, `.finset_sum`: linear combinations.
- `isItoProcessUpTo_deterministic`: a deterministic `C¹` function on `[0,T]` is an Itô process (no diffusion) up to any `τ ≤ T`.
- `IsItoProcessUpTo.mono`: up to `τ` ⇒ up to any stopping time `σ ≤ τ`.

## C7 — `ItoIntegral/Complex.lean` (uses: `realRiemann` from C4)

- `itoSum_complexBM` **(proved)**: `itoSum f W⁽ˣ⁾` in terms of the real Riemann sums of `Re f`, `Im f` against `B_{x,0}`, `B_{x,1}`.
- `itoSum_conj_complexBM` **(proved)**: same for `conj W⁽ˣ⁾`.
- `itoSum_sde_eq_realRiemann` **(proved)**: real and imaginary parts of the noise term `i itoSum ψ(x+1) W⁽ˣ⁾ + i itoSum ψ(x-1) conj W⁽ˣ⁻¹⁾` of the frozen equation, as `±(1/√2)` combinations of four real Riemann sums (matches design 1.2 (e)).
- `tendstoInMeasure_complex_iff`: convergence in measure of complex variables ⇔ of real and imaginary parts.

C7 is therefore reduced to one short lemma.

## Dependencies

```
Defs ─► B1 (NullAug) ─┐
Defs ─► B2 (Doob) ────┼─► B3 (Stopping)
Defs ─► C1 (Elementary) ─► C3 (Basic) ─► C4 (Integrands, Riemann) ─► C7 (Complex)
                  B2 ──────┘      │  └──► C2 (FourthMoment)
                                  └──► C5 (Stopping; also B3) ─► C6 (Product; also C2, C4)
```
Import graph of the files: `NullAug, Doob ← Defs`; `Martingales/Stopping ← NullAug, Doob`; `Elementary ← Defs`; `Basic ← Elementary, Doob`; `FourthMoment ← Basic`; `Integrands ← Basic`; `Riemann ← Integrands`; `ItoIntegral/Stopping ← Integrands, Martingales/Stopping`; `Product ← FourthMoment, Riemann, ItoIntegral/Stopping`; `Complex ← Riemann`. Proofs may use any interface of a file they import (still `sorry` or not); a proving task must not change any statement.

## Departures from `docs/stage2-design.md`, Section 2

1. `ElemBlock` has a field `le : a ≤ b`. Without it a reversed block is `0` in `toFun` but not in `integral` (for `t ≥ a`, `Bᵢ(b) - Bᵢ(a) ≠ 0`), and the isometry would be false.
2. `IsItoIntegrable.meas` asks measurability of `h` restricted to `s > 0` (`if 0 < p.1 then … else 0`). With measurability on all of `ℝ × Ω`, the conclusion of the product rule would be false: its integrand `X d 𝟙_{s≤τ}` involves `X` at negative times, where nothing is assumed (and `ψ` at negative times is arbitrary).
3. `IsItoProcessUpTo` is a structure with a third condition, `a` integrable on `[0, τ]` a.s. Without it the junk value `0` of non-integrable interval integrals makes `add` and the product rule false. With it, the product rule no longer needs `hameas`, `hcmeas`; it gets `hτb : ∃ T, ∀ ω, τ ω ≤ T` (true in every use).
4. Riemann sums: definition `realRiemann` (same grid as `itoSum`); integrand `f 𝟙_{j=i}` without the cut `s ≤ t`; joint measurability of `f` dropped (it follows from adaptedness and left-continuity); bound only for `s ≥ 0`; integrability returned as a conjunct; a finite-family version added.
5. `hitTime` takes a real level `K` (design: `ℝ≥0`).
6. `condExp_stopped_of_forall`: `T : ℝ`; continuity on `[0,T]` only; `hYa` dropped (it follows from `h`); new hypothesis `hVm` (`V_t` a.e. strongly measurable), so that a non-measurable `V` cannot make the conclusion fail through the junk value of `condExp`; domination written as `∫⁻ sup ofReal(|V|+|Y|) ≠ ∞`.
7. Package B uses `[IsFiniteMeasure μ]` instead of `[IsProbabilityMeasure μ]`; `measure_exists_ge_le` asks `M ≥ 0` only on `[0,T]`.
8. The continuous-time `L²` inequality for nonnegative *sub*martingales is not stated: (2.2) needs only Doob's inequality for the martingale part (`lintegral_iSup_stochInt_sq_le`), since `e^{-ct}V_R^k ≤ 1 + N_t`. The discrete version is stated (B2 needs it anyway).
9. `HasCovariation` is not in `Martingales/Defs.lean` on `master` (T0 may add it); the cross bracket is stated with `condExp` (`condExp_stochInt_mul`, `condExp_integral_mul`).
10. `HasBracket.congr` needs `0 ≤ T` (the condition `A_0 = 0` is not on `[0,T]` when `T < 0`). The restriction lemmas are named `mono_horizon` (`HasBracket` has a field `mono`).
