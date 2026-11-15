# Parse audit of the approved statements (binder scope and precedence)

Prepared on 13 November 2026, branch `work-parseaudit` (base `3876ded`). Independent audit, read-only: no `.lean` file was changed.

**Question.** Does every approved Lean term *mean* what the approved sheet (or docstring) says? The audit looks for one class of error: the Lean parser reading the source text differently from the intended formula (scope of the binders `∫`, `∫⁻`, `∑`, `∑'`, `⨆`, `⨅`, `∏`, `∀`, `∃`, `fun`, `∀ᵐ`; which integral a `∂μ` belongs to; `in` ranges; precedence of `•`, `*`, `/`, `^`, unary `-`; coercions `↑` and `ENNReal.ofReal` on the wrong subterm; `→` versus `∧`).

**Answer.** 161 declarations checked. **One misparse**, in the Stage 4 definition `IsWeakMild` (field `weak`), repeated in the Stage 4 statement `IsMildSolution.isWeakMild`. It makes `IsMildSolution.isWeakMild` false (as soon as a solution of (1.13) exists), and makes `IsWeakMild` hold only for fields that vanish almost everywhere, so that `prop_7_3` is true but no longer says anything about (7.13). All other declarations (Stage 0, 1, 2, 3, and the other Stage 4 ones) are read by Lean as the sheets say.

## Method

1. A scratch file (outside the repository) imports the whole library and, for every declaration, prints its type with `pp.parens true`, `pp.funBinderTypes true`, `pp.proofs false`, `pp.fieldNotation false`, `pp.deepTerms true`; for a definition it also prints its value, and for a structure or inductive type the type of each constructor and of each field. Every binder therefore appears as `(∫ (x : ℝ), (BODY) ∂μ)`, with its body explicitly delimited, and every operator application is parenthesized.
2. Each printout was read term by term against the sheet (`docs/stage1-statements.md`, `docs/stage2-statements.md`, `docs/stage3-statements.md`, `docs/stage4-statements.md`; for Stage 0 the docstrings and `README.md`). The source text was not used as evidence.
3. Two mechanical scans of the printouts, as a safety net: (a) every binder whose body contains, at its top level, a `+` or `-` (4 hits: `lemma_6_4`, `prop_6_2`, both intended, and the two occurrences below); (b) every binder whose body contains another binder after a binary operator (3 hits, all the misparse below); (c) every coercion `↑(…)` applied to a compound term, to catch an integer or natural division or subtraction computed before the cast (no hit), and every argument of `ENNReal.ofReal` and `Real.toNNReal` (all on the intended subterm).
4. The suspected misparse was confirmed by the kernel (see "Kernel checks" below). The instances hidden by the pretty-printer in `Measurable[𝓕 t]` (fields `adapted` of `IsBrownianFamily`, `IsWaveFunction`, `IsWhiteNoise`; constructor `IsWalshIntegral.block`; predictability in `prop_7_1`, `prop_7_2`) were checked by `example`s with the explicit σ-algebra: they are the filtration, as intended.

## The problem found

### P1. `IsWeakMild.weak` and `IsMildSolution.isWeakMild`: the first integral swallows the second

**Where.** `QSSEPtoKPZ/Uniqueness/Defs.lean`, line 60 (field `weak` of `IsWeakMild`), and `QSSEPtoKPZ/Uniqueness/MildSolution.lean`, line 56 (third conjunct of `IsMildSolution.isWeakMild`; its second conjunct `IsWeakMild T 𝓖 S Z' ν` inherits the error). Source text, in both places:

```
(fun ω => ∫ x, Z t x ω * f x - ∫ x, heatKernel t x * f x)
```

**How Lean reads it** (printout with `pp.parens`):

```
fun (ω : Ω) => (∫ (x : ℝ), (((Z t x ω) * (f x)) - (∫ (x : ℝ), ((heatKernel t x) * (f x)))))
```

that is, $X(\omega)=\int_{\mathbb R}\big(Z(t,x)f(x)-c_f\big)\,dx$ with the constant $c_f=\int g_t(x)f(x)\,dx$. The binder `∫ x,` extends as far to the right as possible, so the subtraction and the second integral are inside the first integral.

**What the sheet says** (`docs/stage4-statements.md`, definition `IsWeakMild`, equation (7.13)): $X(\omega)=\int Z(t,x)f(x)\,dx-\int g_t(x)f(x)\,dx$, which is the right side needed for $\int Z(t,x)f(x)dx=\int g_t f+\int_0^t\int(g_{t-s}\ast f)(y)Z(s,y)\xi(ds\,dy)$.

**Consequence.** Let $f\in C^\infty_c(\mathbb R)$ with $c_f\ne0$ (for instance any $f\ge0$, $f\not\equiv0$). Outside the support of $f$ the integrand equals $-c_f$, so it is not integrable on $\mathbb R$, and Lean's integral of a non-integrable function is $0$: the misparsed right side is $X\equiv0$, whatever $Z$ is. (The kernel-checked lemma below proves $\int(h-c)=0$ for $h$ integrable and $c\ne0$.) For such $f$, `weak` therefore says that the Walsh integral of $h_f(s,y)=\mathbf 1_{0<s<t}(g_{t-s}\ast f)(y)Z(s,y)$ is $0$. By Itô's isometry (companion W), $\mathbb E\int_0^t\int(g_{t-s}\ast f)(y)^2Z(s,y)^2\,dy\,ds=0$, and $g_{t-s}\ast f>0$ everywhere for $f\ge0$, $f\not\equiv0$; hence $Z=0$ almost everywhere on $\Omega\times(0,t)\times\mathbb R$, for almost every $t\in(0,T]$, hence on $\Omega\times(0,T)\times\mathbb R$. Conversely $Z\equiv0$ satisfies the misparsed `IsWeakMild` (block with $c=0$; for $c_f=0$ the right side is $\int0\cdot f=0$). So, given W:

* **`IsWeakMild`**: does not express (7.13). It holds exactly for the measurable, square integrable fields that vanish almost everywhere on $\Omega\times(0,T)\times\mathbb R$.
* **`IsMildSolution.isWeakMild`: false** whenever a solution of (1.13) exists (which is the case: Bertini–Cancrini, Chen–Dalang; statement E3, not formalized). Indeed $Z'=Z$ almost surely on $(0,\infty)\times\mathbb R$ and $\mathbb E[Z(t,x)]=g_t(x)>0$ (or $\mathbb E[Z(t,x)^2]\ge g_t(x)^2$ by `IsMildSolution.integral_sq`), so $Z'$ does not vanish almost everywhere. Its third conjunct alone is already false for every $t\in(0,T]$ and every $f\ge0$, $f\not\equiv0$.
* **`prop_7_3`** (its own text parses correctly): its hypotheses force $Z^1=Z^2=0$ almost everywhere, so it is **true but degenerate**: it no longer states uniqueness for (7.13), and the route of Stage 4 (identify the limit field, which satisfies (7.8) in the correct form given by `prop_7_2`, with $Z$ through Proposition 7.3) cannot go through, since that limit field is not almost everywhere $0$.
* `main_theorem_top` and the other Stage 4 statements are not affected as statements (they do not mention `IsWeakMild`). `prop_7_2`, whose right side is `pairFM (pathAt (Y ω.1) t) f - ∫ x, heatKernel t x * f x`, is parsed correctly: the first term is a function application, not a binder.
* Not frozen, same text, to be corrected with the rest: `heatMild_isWeakMild` (`QSSEPtoKPZ/Uniqueness/StochFubini.lean`, line 46). The auxiliary statements that use `IsWeakMild` (`IsWeakMild.exists_noise_functional`, `isWeakMild_prod_of_eq_7_8`, and those of `SheVersion.lean`, `Theorem12.lean`) are all still `sorry`, so no proof relies on the misparse yet.

**Fix** (parenthesize the first integral), in `Defs.lean` line 60, `MildSolution.lean` line 56 and `StochFubini.lean` line 46:

```
(fun ω => (∫ x, Z t x ω * f x) - ∫ x, heatKernel t x * f x)
```

(with `Z'` in place of `Z` in the last two). This changes approved statements of Stage 4, so it is a proposal to the author (rule 3 of `CLAUDE.md`). After the fix, `pp.parens` should print `((∫ (x : ℝ), ((Z t x ω) * (f x))) - (∫ (x : ℝ), ((heatKernel t x) * (f x))))`.

**Why the earlier audits missed it.** The source text reads like the formula, and the docstring writes the formula correctly; only a printout with explicit parentheses shows the scope of the binder.

## Kernel checks (scratch file, not in the repository)

```lean
-- The source text is, by definition, the misparsed term:
example (Z f g : ℝ → ℝ) :
    (∫ x, Z x * f x - ∫ x, g x * f x) = ∫ x, (Z x * f x - ∫ y, g y * f y) := rfl

-- The field `IsWeakMild.weak` has exactly the misparsed type:
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {T : ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
    {S Z : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω} (h : IsWeakMild T 𝓖 S Z ν) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ f : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      IsWalshIntegral 𝓖 S ν
        (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω else 0)
        (fun ω => ∫ x, (Z t x ω * f x - ∫ y, heatKernel t y * f y)) := h.weak

-- The misparsed right side vanishes when the constant is nonzero:
theorem misparsed_eq_zero (h : ℝ → ℝ) (c : ℝ) (hh : Integrable h) (hc : c ≠ 0) :
    ∫ x, (h x - c) = 0 := by
  apply integral_undef
  intro hint
  have h2 : Integrable (fun _ : ℝ => c) := by
    have := hh.sub hint
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [integrable_const_iff] at h2
  rcases h2 with h0 | hfin
  · exact hc h0
  · have : volume (Set.univ : Set ℝ) < ⊤ := measure_lt_top _ _
    simp at this
```

All three are accepted (`lake env lean`, Lean 4.35.0, Mathlib v4.35.0).

## Points checked and found correct (selection)

These are the places where a misparse was most likely; each was read in the parenthesized printout.

* **Stage 0.** `IsWaveFunction.sde`: the limit is $\psi_t(x)-\mathbf 1_{x=0}+\frac{D(x,x)}2\int_0^t\psi_s(x)ds$, the integral being the last factor, as (1.7) requires. `heatKernel`: `(-(x ^ 2)) / (2 * t)`, i.e. $-x^2/(2t)$, not $(-x)^2$. `rescaledField`, `rescaledPosition`, `rescaledMeasure`: exponents $1/2$, $1/4$, $3/4$, $-1/2$ are real divisions (`(-1) / 2`), `ENNReal.ofReal` covers $n^{-1/2}Z_n$, `•` multiplies the Dirac mass. `IsMildSolution.mild`: $X=Z(t,x)-g_t(x)$ (function application, no binder). `IsWalshIntegral.isometry`: $\int X^2\,d\nu=\int(\text{uncurryField }h)^2\,d(\nu\otimes\mathrm{Leb})$, each `∂` on its own integral. `main_theorem`: `∀ᵐ ω ∂(μ k)`, $L_k/\mathrm{ofReal}(n_k^{3/4})$.
* **Stage 1.** `bM`, `kM`: `kappa ρ (↑r / ↑m)` is a real division (two separate casts); `occupationTime_le`: $\min(S,\frac14+\sqrt S)\le\frac54\sqrt S$; `hasDerivAt_uN_apply`: $\frac{n\lambda_n}2\mathbf 1_{\lvert r\rvert=1}u_n$; `gM_spec`: $g_m(r)+\frac12\sum_{u>r}k_m(u)$; `uN_bounds`: $2^{1+16t}$.
* **Stage 2.** `moment_bound` and `WN_moments`: the power $k$ is applied to the supremum, `((⨆ t ∈ Icc 0 T, …) ^ k)`. `prop_2_2` (2.4): $((\mathbf 1_{x=0}+\int_0^t\Delta P)+J_t(x-1))-J_t(x)$. `lemma_2_3_linear`, `lemma_2_3_quadratic`, `lemma_3_2`, `MN`: $M_t=(\text{pairing}-f_0(0))-\int_0^t(\dots)$ with the drift entirely inside the integral. `QNdens`, `bracketDensN2`: the square covers the whole bracket, $e^{\pm\theta_n/2}$ written `exp ((-(θ)) / 2)`. `smoothedNormSq`: the inner `∂ν` belongs to the inner integral, the square to the inner integral. `prop_3_1` (2), (3), `lemma_6_4` (6.13)–(6.15), `prop_4_3_bounds`, `prop_4_3_increment` (integral from $\tau$ to $\tau+s$), `prop_6_1`, `prop_6_2` (integrand $\mathcal E_n-\lVert\cdot\rVert_2^2$ inside the time integral, absolute value outside): as on the sheet.
* **Stage 3.** `lemma_5_2` (5.1): $\mathbb P(K\le\sup_t\mathsf Z_n(t;\cosh))\le\mathrm{ofReal}(2e^{2T}/K)$; `aldous_condition`: $c\,(Cs/\eta+C^2\sqrt s/\eta^2)$; `prop_5_1`: `Zv ⁻¹' 𝒦ᶜ` is the preimage of the complement.
* **Stage 4.** `limMart` (7.2), `limBracket` (7.3), `limDensity` (liminf of `ofReal` of the convolution, then `toReal`), `heatConv`, `eq_7_4`, `prop_7_1`, `prop_7_2` (see above), `IsMildSolution.integral_sq` ($((2^{-(k+1)}t^{(k+1)/2-1})/\Gamma(\frac{k+1}2))\,g_{t/2}(x)$, real casts).

No `≤` chains occur; `→`/`∧` nesting was read in every statement and agrees with the sheets.

## Table of all declarations checked

### Stage 0 (25 declarations)

| Declaration | Verdict |
|---|---|
| `IsBrownianFamily` | OK |
| `complexBM` | OK |
| `itoSum` | OK |
| `box` | OK |
| `degree` | OK |
| `IsWaveFunction` | OK |
| `density` | OK |
| `rescaledPosition` | OK |
| `rescaledField` | OK |
| `rescaledMeasure` | OK |
| `rectMass` | OK |
| `IsWhiteNoise` | OK |
| `uncurryField` | OK |
| `IsWalshIntegral` | OK |
| `heatKernel` | OK |
| `IsMildSolution` | OK |
| `sheMeasure` | OK |
| `main_theorem` | OK |
| `exists_isWaveFunction` | OK |
| `isWaveFunction_unique` | OK |
| `exists_isWhiteNoise` | OK |
| `IsWalshIntegral.ae_eq` | OK |
| `IsWalshIntegral.isometry` | OK |
| `isMildSolution_unique` | OK |
| `IsMildSolution.nonneg` | OK |

### Stage 1 (43 declarations)

| Declaration | Verdict |
|---|---|
| `thetaN` | OK |
| `cN` | OK |
| `lambdaN` | OK |
| `aN` | OK |
| `sq_le_two_mul_cosh_sub_one` | OK |
| `constants_bounds` | OK |
| `BddZ` | OK |
| `chainGen` | OK |
| `chainOpLinear` | OK |
| `chainOp` | OK |
| `chainPi` | OK |
| `defectInd` | OK |
| `chainGen_max_abs_one` | OK |
| `chainGen_sq` | OK |
| `occupationTime` | OK |
| `occupationTime_le` | OK |
| `defectOp` | OK |
| `generatorU` | OK |
| `uN` | OK |
| `uN_neg` | OK |
| `uN_zero` | OK |
| `hasDerivAt_uN_apply` | OK |
| `uN_regularity` | OK |
| `uN_bounds` | OK |
| `uN_le_one_add_sqrt` | OK |
| `IsMollifier` | OK |
| `kappa` | OK |
| `bM` | OK |
| `kM` | OK |
| `IsMollifier.kappa_even_nonneg_smooth` | OK |
| `IsMollifier.kappa_support_integral` | OK |
| `IsMollifier.kappa_le_kappa_zero` | OK |
| `IsMollifier.kM_props` | OK |
| `IsMollifier.tsum_chainPi_mul_kM` | OK |
| `IsMollifier.bM_bounds` | OK |
| `gNat` | OK |
| `gM` | OK |
| `IsMollifier.gM_spec` | OK |
| `IsMollifier.chainGen_gM` | OK |
| `IsMollifier.gM_nonneg_le` | OK |
| `IsMollifier.abs_gM_succ_sub_le` | OK |
| `IsMollifier.gM_add_one_eq_sub_one` | OK |
| `IsMollifier.exists_gM_zero_le` | OK |

### Stage 2 (65 declarations)

| Declaration | Verdict |
|---|---|
| `nullSets` | OK |
| `nullSets_le` | OK |
| `nullAug` | OK |
| `le_nullAug` | OK |
| `timeChange` | OK |
| `IsCL2Mart` | OK |
| `HasBracket` | OK |
| `HasCovariation` | OK |
| `lap` | OK |
| `inclGen` | OK |
| `abs_lap_le` | OK |
| `memℓp_lap` | OK |
| `lapOpLinear` | OK |
| `lapOp` | OK |
| `memℓp_delta0` | OK |
| `delta0` | OK |
| `rwKernel` | OK |
| `prop_2_2` | OK |
| `hasSum_density` | OK |
| `moment_bound` | OK |
| `lemma_2_3_linear` | OK |
| `quadDiff` | OK |
| `lemma_2_3_quadratic` | OK |
| `zN` | OK |
| `tiltedMeasure` | OK |
| `pairZ` | OK |
| `WN` | OK |
| `varrhoN` | OK |
| `EN` | OK |
| `IsC13` | OK |
| `AN` | OK |
| `MN` | OK |
| `QNdens` | OK |
| `QN` | OK |
| `filtN` | OK |
| `tiltedInclGen` | OK |
| `pairZ2` | OK |
| `bracketDensN2` | OK |
| `sinh_sub_self_bounds` | OK |
| `rescaledMeasure_eq` | OK |
| `varrhoN_bounds` | OK |
| `prop_3_1_generator` | OK |
| `identity_uv` | OK |
| `tilt_identity` | OK |
| `tiltedInclGen_diff` | OK |
| `WN_moments` | OK |
| `prop_3_1` | OK |
| `hasBracket_WN` | OK |
| `lemma_3_2` | OK |
| `prop_4_3_condSecondMoment` | OK |
| `prop_4_3_condSecondMoment_stopping` | OK |
| `prop_4_3_bounds` | OK |
| `prop_4_3_increment` | OK |
| `rhoEps` | OK |
| `kappaEps` | OK |
| `smoothedNormSq` | OK |
| `FN` | OK |
| `BN` | OK |
| `kappaEps_eq_conv` | OK |
| `smoothedNormSq_eq` | OK |
| `BN_eq` | OK |
| `prop_6_1` | OK |
| `lemma_6_4` | OK |
| `tendsto_bM` | OK |
| `prop_6_2` | OK |

### Stage 3 (7 declarations)

| Declaration | Verdict |
|---|---|
| `integral_tiltedMeasure` | OK |
| `lemma_5_2` | OK |
| `aldous_condition` | OK |
| `prop_5_1_continuous` | OK |
| `prop_5_1_version` | OK |
| `prop_5_1` | OK |
| `prop_5_1_isTight` | OK |

### Stage 4 (21 declarations)

| Declaration | Verdict |
|---|---|
| `pathAt` | OK |
| `pairFM` | OK |
| `pathFiltrationCan` | OK |
| `pathFiltration` | OK |
| `limMart` | OK |
| `limBracket` | OK |
| `limDensity` | OK |
| `limField` | OK |
| `heatConv` | OK |
| `IsWeakMild` | **PROBLEM** (field `weak`: misparse, see P1) |
| `prop_7_1` | OK |
| `eq_7_4` | OK |
| `prop_7_2` | OK |
| `prop_7_3` | OK as text; **affected** through `IsWeakMild` (see P1): true but degenerate |
| `IsMildSolution.integral_sq` | OK |
| `IsMildSolution.isWeakMild` | **PROBLEM** (same misparse, twice: through `IsWeakMild` and in its own third conjunct; see P1). False whenever a mild solution exists |
| `main_theorem_top` | OK |
| `IsMildSolution.nonneg_of_isWaveFunction` | OK |
| `IsWalshIntegral.ae_eq_lib` | OK |
| `IsWalshIntegral.isometry_lib` | OK |
| `isMildSolution_unique_lib` | OK |

**Totals:** 161 declarations (Stage 0: 25, Stage 1: 43, Stage 2: 65, Stage 3: 7, Stage 4: 21). PROBLEM: 2 (`IsWeakMild`, `IsMildSolution.isWeakMild`, one misparse P1). Affected through P1 without a misparse of its own: 1 (`prop_7_3`). OK: 158.

The Stage 1 list contains, besides the statements of `docs/stage1-statements.md`, the definitions they use (`thetaN`, `cN`, `lambdaN`, `aN`, `BddZ`, `chainOpLinear`, `occupationTime`, `defectOp`, `gNat`).
