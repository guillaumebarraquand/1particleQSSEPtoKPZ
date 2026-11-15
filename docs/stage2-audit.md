# Audit of the Stage 2 statements (12 November 2026)

Independent audit by an Opus 5.5 agent, on commit `12c243d`, before the statements went to the author. Its findings were handled as follows: E1 fixed (`HasCovariation` requires bounded variation); W1 fixed (`prop_6_1` asserts the summability of `zN`); W2, W3 recorded in `PROGRESS.md` for Stages 3–4; remarks: the sheet's line on D1–D8 corrected, the others left as they are. The report is reproduced unchanged below.

---

# Stage 2 statements: adversarial audit

Audited on 12 November 2026, 22:37–22:50 CET. Project at commit `12c243d` (master). Article SHA-256 `3547cb86…`, the expected version (1713 lines). Equation numbers were checked against `QSSEPtoKPZ.aux`, and all docstring numbers are correct.

Method:
- Each statement and definition was compared symbol by symbol with Sections 2, 3, 4.3 and 6 of the article. The places where Sections 5 and 7 use them were also read.
- The article's derivations were redone by hand, with independent checks of: (3.8), (3.9), the bracket factors of (2.5), (2.7), (2.8), (3.11), (3.15), (3.22), the drift of (3.21) via (3.20), (3.20) and (3.23) term by term, the constants of Prop 3.1 (1)–(3), (4.8), (6.11), (6.13) and (6.15).
- Lean checks used scratch files `A1.lean` and `A2.lean` in this folder, run with `lake env lean`:
  - `lemma_6_4`, `prop_4_3_increment` and `prop_4_3_condSecondMoment_stopping` were printed with `pp.coercions`. `1 / m`, `m / n ^ (1/2)` and `m ^ 2 / n` elaborate to real division with `↑m`. `τ ω + s` is `↑(τ ω) + s` in ℝ. The `μ[… fun _ => 1 | hτ.measurableSpace]` term parses as intended.
  - `hτ.measurableSpace ≤ mΩ` holds (`IsStoppingTime.measurableSpace_le`, no extra assumptions). So the conditional expectations with respect to `𝓕ⁿ_τ` are not the junk value `0`.
  - `IsC13 1 (fun _ _ => 1) (fun _ _ => 0) 1` elaborates. All its fields are closed except the trivial `iteratedDeriv` of a constant, so `IsC13` is satisfiable.

Summary: **1 ERROR, 3 WEAKNESS, 5 REMARK.**

---

## ERROR

### E1. `HasCovariation` does not determine the cross-bracket (definition; `Martingales/Covariation.lean:37–45`)

**Problem.** `HasCovariation T 𝓕 M N A μ` requires only this: `A` is integrable, a.s. continuous on `[0,T]`, with `A 0 = 0`, and `MN − A` is a martingale. It does **not** require `A` to have finite variation. Without that requirement, `A` is determined only up to adding a continuous martingale that is 0 at time 0. Counterexample:
- Let `M = N = 0` and let `A = B` be a Brownian motion of the filtration.
- Then `MN − A = −B` is a martingale, `A` is integrable, continuous and `A_0 = 0`.
- So `HasCovariation T 𝓕 0 0 B` holds, although $\langle 0,0\rangle=0$.

More generally, $A=\langle M,N\rangle+L$ satisfies the definition for any continuous $L^2$ martingale $L$ with $L_0=0$.

So the docstring's reading, "`⟨M, N⟩_t = A_t`", is not what the definition says. `HasBracket` does not have this problem, because `mono` gives finite variation, and the argument recorded in `PROGRESS.md` (a continuous finite-variation martingale is constant) applies to it. That argument does not apply to `HasCovariation`.

**Impact now.** The only current use is `prop_2_2` with `A = 0`. There "`J x · J y` is a martingale" is exactly $\langle J(x),J(y)\rangle=0$, so `prop_2_2` is faithful as it stands.

**Why it must still be fixed before freezing.**
- The definition is submitted for approval as carrying the meaning of "bracket".
- Section 7.2 uses cross-brackets with nonzero $A$: (7.9) `crossbracket`, $\langle M^{\varphi_1},M^{\varphi_2}\rangle=\int\!\!\int Z^2\varphi_1\varphi_2$, obtained by polarization.
- Any later statement of that form written with `HasCovariation` would be strictly weaker than the article's.

**Fix.** Add a finite-variation field:
```lean
  bv : ∀ᵐ ω ∂μ, BoundedVariationOn (fun t => A t ω) (Set.Icc 0 T)
```
(`BoundedVariationOn` exists in Mathlib v4.35.0, checked in `A2.lean`.) An alternative is to define it by polarization, with `HasBracket` of `M + N` and `M − N` and `A = (A₊ − A₋)/4`. With either fix, `prop_2_2` keeps its proof idea: `A = 0` has bounded variation. Update the docstrings and deviation 16 of `stage2-statements.md`.

---

## WEAKNESS

### W1. `prop_6_1` can, taken alone, hold through Lean's junk values (`Replacement/L2Bound.lean:47–60`)

The integrand is `ENNReal.ofReal (smoothedNormSq (tiltedMeasure n ψ ω t) (fun _ => 1) ρ ε)`, and `smoothedNormSq` is a Bochner integral of a Bochner integral. It equals `0` in two cases:
- when `tiltedMeasure n ψ ω t` is an infinite measure (`∑ₓ 𝔷_n(t,x) = ∞`, so the inner integral is junk);
- when `y ↦ (…)²` is not integrable.

Unlike every other probabilistic statement, `prop_6_1` asserts neither the a.s. summability of `zN` nor the integrability in `y`. This goes against the policy stated in `stage2-statements.md` ("No statement can hold because of a convention of Lean").

The statement is still true and faithful. Junk occurs only on a null set:
- the a.s. summability for all `t ≥ 0` is a conjunct of `WN_moments` and others;
- `smoothedNormSq_eq` gives integrability and the identity (6.1) for every finite measure.

So the *set* of statements certifies the genuine value. A reader of `prop_6_1` alone cannot see this.

**Fix.** Add the conjunct
`(∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → Summable (zN n ψ ω t))`.
Optionally also add `∀ᵐ ω, ∀ t ≥ 0, Integrable (fun y => (∫ x, rhoEps ρ (m * n^(-1/2:ℝ)) (y - x) ∂tiltedMeasure n ψ ω t) ^ 2)`.

The same applies, more mildly, to `prop_6_2`. Its first conjunct gives summability, but the integrability in `y` of the integrand of `smoothedNormSq … (φ s) ρ ε` is only certified through `smoothedNormSq_eq`.

### W2. No statement links `tiltedMeasure` and `pairZ` / `pairZ2`

The same object $\mathsf Z_n(t)$ appears in two forms, and no stated result says they agree:
- Section 6 and Prop 6.2 use the measure `tiltedMeasure`, through `smoothedNormSq`;
- Props 3.1, 4.3 and Lemma 6.4 use the series `pairZ` / `pairZ2` / `EN` / `BN`.

`BN_eq` is the only bridge, and only for `BN`. Section 7.1 needs $\mathsf Z_n(t;\varphi)=\int\varphi\,d\mathsf Z_n(t)$ to pass from (3.14) to the weak convergence of measures.

This is not an article statement, so it is not required for approval. Recommend recording it as a planned lemma (`integral_tiltedMeasure`: for summable `zN` and bounded measurable `φ`, `∫ φ ∂tiltedMeasure = pairZ … φ`), so that the two definitions are known to agree before they are frozen.

### W3. Nothing about path-space measurability or the natural filtration of $\mathsf Z_n$ (for Sections 5 and 7)

Section 7.1 uses two facts:
- $\mathsf W_n,\mathsf E_n,M^\phi_n,\langle M_n^\phi\rangle$ are measurable functions of the trajectory $(\mathsf Z_n(t))_{t\le T}$;
- $M_n^\phi$ and $(M_n^\phi)^2-Q_n$ are martingales for the *natural filtration of $\mathsf Z_n$*.

Both can be derived from the stated `HasBracket` (filtration `filtN n 𝓕`) and from the frozen adaptedness of `ψ`, by the tower property. No Stage 2 statement provides them directly. This is acceptable because it is not a result of Sections 2–6. It is flagged so that Stage 3/4 plans the lemma, and does not try to read it off the statements.

---

## REMARK

- **R1.** `docs/stage2-statements.md:19` says "recommended options, not yet answered by the author". According to `PROGRESS.md` line 76, D1–D8 were all accepted on 12 November 2026. The sentence is stale.
- **R2.** `quadDiff` is a definition used in a statement, but it lives in the statement file `WaveFunction/Quadratic.lean` and not in `WaveFunction/Defs.lean`. This is harmless. Moving it would group all the definitions to be approved in definition files.
- **R3.** `HasCovariation` (with the fix of E1) and `HasBracket` give the bracket `A` without stating that it is adapted. Adaptedness up to null sets follows from the `s = t` case of the martingale condition. It would help the author to say so in the docstrings. `PROGRESS.md` already records this for D2.
- **R4.** In `lemma_6_4`, `R` and `q` are only required to be jointly measurable, not adapted or progressive. The "∃" form is faithful: `∫R` and `∫q` are determined up to indistinguishability by the decomposition of `N` and by the uniqueness of the bracket. The proof of Prop 6.2 needs nothing more. No change needed; noted so that nobody later relies on adaptedness of `R`.
- **R5.** `lemma_2_3_linear`: the summability conjunct is stated for `(α t (x+1) - α t x)^2 * P * P`, while the bracket uses `2 * (…)^2 * P * P` (constant multiple, different association). This is fine, and is noted only because the proof needs a one-line `Summable.mul_left` plus a `ring_nf`.

---

## Statements checked and found faithful (apart from the items above)

Section 2
- `moment_bound` (2.2): $(\sup_t\|\psi_t\|_a^2)^k=\sup_t\|\psi_t\|_a^{2k}$. ENNReal terms are nonnegative, so `ofReal` does not truncate. `AEMeasurable` is true, because $t\mapsto\|\psi_t\|_a^2$ is lower semicontinuous a.s. The cases $T<0$ and $k=0$ are harmless.
- `prop_2_2` (2.3)–(2.5), $\mathbb EP=p_t$: the Riemann-sum integrand $\overline{\psi(x)}\psi(x+1)$ against $W^{(x)}$ and the factor 2·Im are as in (2.3). The bracket factor $2PP$ is checked: Im$(a\,dW)$ has quadratic variation $|a|^2/2$. The signs $J(x-1)-J(x)$ match (2.4). Integrability of `lap P` and of `PP` is asserted. "a.s. ∀ t" is true (P and J are a.s. continuous; countably many x). `rwKernel` $=e^{t\Delta}\delta_0$ equals $p_t$ by symmetry of Δ. The cross-bracket with $A=0$ is faithful (see E1).
- `hasSum_density`: faithful.
- `lemma_2_3_linear` (2.7): the hypotheses read "C¹ in time" as `HasDerivWithinAt` on `Icc 0 T` plus a continuous derivative, with the bound $Ce^{a|x|}$. $M$ is the last term of (2.7), since $\sum_x\alpha_0(x)P(0,x)=\alpha_0(0)$. The bracket is $2(\nabla\alpha)^2PP$. All series and interval integrals are asserted.
- `lemma_2_3_quadratic` (2.8): product summability on ℤ² justifies the iterated `tsum`s. `quadDiff` is the bracket of (2.8). The bracket is $2\cdot(2D)^2PP$. `inclGen` (2.6) was recomputed from Itô's formula, as the drift of $\sum fPP$.

Section 3, definitions
- `zN`, `tiltedMeasure`, `pairZ`, `WN`, `EN`, `varrhoN`, `AN`, `MN`, `QNdens`/`QN`, `filtN`, `tiltedInclGen` (term by term against (3.19)), `pairZ2`, `bracketDensN2` (recomputed from (2.8) with $F_s=e^{\theta(x_1+x_2)-2\lambda s}f_{2s/n}$: $8D_F^2PP\,ds=4n\,S^2\mathfrak z\mathfrak z\,dt$), `IsC13`.
- `IsC13` implies $C\ge0$ when $T\ge0$, so $C^2\ge\|\phi\|_{1,3}^2$.

Section 3, statements
- `sinh_sub_self_bounds`, `identity_uv`, `varrhoN_bounds`.
- `rescaledMeasure_eq` (3.8): the exponents give exactly $\varrho_n$. It is true for every ω and every real $t$, because `density ≥ 0` and $n^{-1/2}n^{1/2}=1$.
- `prop_3_1_generator`: the constants of the article's proof give at most $(\tfrac{\cosh1}{4}+\tfrac{\cosh1}{6}+\tfrac e6)n^{-1/4}\le n^{-1/4}$ times the relevant norms.
- `tilt_identity` (3.20): recomputed term by term. Symmetry is not needed.
- `tiltedInclGen_diff` (3.23): recomputed. Evenness is not needed.
- `WN_moments` (3.7).
- `prop_3_1`: the bracket $(3.15)$ comes from Lemma 2.3 (1) after the time change. (2): $2\lambda_n C^2\cdot n\sum\mathfrak z\mathfrak z=2C^2a_n\mathsf E_n$. (3): constant $5$; the article's $2\sinh\theta_n+n^{-1/2}\le 3.4\,n^{-1/4}$.
- `hasBracket_WN` (3.16): $a_n\mathsf E_n=n\lambda_n\sum\mathfrak z\mathfrak z$, and $\mathsf W_n(0)=1$ a.s. (`sde` at $t=0$).
- `lemma_3_2` (3.21)–(3.22): drift recomputed via (3.20), bracket via (3.11).

Section 4.3
- `prop_4_3_condSecondMoment`, `prop_4_3_condSecondMoment_stopping` (D4, `nullAug`: the σ-algebra is ≤ mΩ, checked), `prop_4_3_bounds` ($4\cdot2^{1+16t}=2^{3+16t}$; $a_n\ge1$), `prop_4_3_increment`.

Section 6
- `rhoEps`, `kappaEps`, `smoothedNormSq` (convolution convention of the Notation paragraph), `FN` (6.9), `BN` (6.10).
- `kappaEps_eq_conv`, `smoothedNormSq_eq` (6.1), `BN_eq` (6.11): $\kappa_{mn^{-1/2}}(y_1-y_2)=n^{1/2}b_mk_m(x_2-x_1)$, with $b_m>0$, and the hypothesis `Summable` makes the measure finite. `tendsto_bM`.
- `lemma_6_4`: (6.13) uses $c_n\ge1$. (6.15): $16(m\lambda^{1/2}+\tfrac14)^2/(n\lambda)\le 32m^2/n+2n^{-1/2}$. "∃ R, q" is faithful by uniqueness of the semimartingale decomposition and of the bracket. Joint measurability of `R`, `q` is achievable: restrict to a measurable conull set where ψ is continuous (Carathéodory), and multiply by $\mathbf 1_{[0,T]}$. The φ ≡ 1 clause is true: $\mathcal Q^\theta 1=0$, $\Gamma(G,1)=0$, and φt = 0 on `[0,T]` by uniqueness of one-sided derivatives.
- `prop_6_1` (apart from W1): `∃ C` comes before Ω (D8), and the C in the statement does not depend on T.
- `prop_6_2`: the ε–δ form is equivalent to $\lim_{\varepsilon\to0}\limsup_n=0$, with $n$ real as in the article. Bounding the outer measure is stronger, and is still provable, since the event is contained in a measurable event up to a null set.

Junk-value scan (all statements):
- Every `tsum` has its summability asserted, or follows from "a.s. Σ𝔷 converges ∀ t ≥ 0" with bounded test functions.
- Every interval integral has its integrability on `[0,T]` (or `[τ, τ+s]`) asserted.
- Every `condExp` has an integrable argument and a sub-σ-algebra that is ≤ mΩ, under a probability measure.
- Every `lintegral` carries an `AEMeasurable` conjunct.
- No `⨆` in ℝ; no ℕ subtraction or division; `rpow` only of $n\ge1$ or of $2$.
- No division by zero: $c_nn^{1/2}>0$, $m\ge1$, $b_m>0$, $\varepsilon>0$.
- The only residual junk risk is W1.

No hypothesis set was found to be contradictory: `IsC13`, the bounds of Lemmas 2.3 and 3.2, bounded stopping times, and `IsMollifier` are all satisfiable.
