# Stage 5: the statements, for comparison with the article

Prepared on 13 November 2026 (task T0‴ of `docs/stage5-design.md`). **Nothing below is proved yet**, except where it is said that a statement is deduced from another one. The statements of Section 8 of the article, the existence half of Proposition 2.1, Theorem 1.2 for arbitrary $L_n$ and the companion statements E1, U1, E2, P are written in Lean, with complete definitions (no `sorry`) and proofs left as `sorry` (or quoting an auxiliary lemma with the same statement, which is itself `sorry`). `lake build` succeeds; the new files produce only warnings `declaration uses 'sorry'`. No frozen file was changed (`Definitions.lean`, `MainTheorem.lean`, `Companions.lean`, `Challenge.lean`, `Solution.lean` and the Stage 0–4 statements are untouched; `scripts/make_challenge.py --check` passes).

By your instruction of 13 November 2026 ("Once stage 4 is completed, start Stage 5 and progress as much as possible without waiting for my approval"), these statements will be proved before you review them. They are written to be read literally; every departure from the article is listed below.

Equation numbers are those of the article of 11 November 2026 (SHA-256 `3547cb86…`, 1713 lines, unchanged on 13 November 2026: checked), read from its `.aux` file.

Files (under `QSSEPtoKPZ/`): `FiniteSystems/Defs.lean` (definitions), `FiniteSystems/Statements.lean` (Proposition 2.1, Lemma 8.2, Proposition 8.1), `Assembly/MainTheorem.lean` (Theorem 1.2), `FiniteSystems/Existence.lean` (E1, P), `FiniteSystems/Uniqueness.lean` (U1), `WhiteNoise/Existence.lean` (E2), `Assembly/Corollaries.lean` (the two consequences of `Corollaries.lean`).

## How to read the statements

The conventions of Stages 2–4 apply (`docs/stage2-statements.md`, `docs/stage4-statements.md`): arbitrary probability spaces in arbitrary universes, filtrations without the usual conditions, processes indexed by $t\ge0$; every series, integral and expectation that appears is asserted to be genuine; probabilities of events that are not claimed measurable are outer probabilities $\mathbb P^\ast$.

* **Wave function on $\Lambda_L$** (`IsWaveFunction L 𝓕 B ψ μ`, frozen definition of Stage 0): $\psi$ adapted to $\mathcal F$, almost surely continuous in $\ell^2(\mathbb Z)$, vanishing outside $\Lambda_L$, and solving (1.7) on $\Lambda_L$ (Itô integrals as limits in probability of left-point Riemann sums), driven by the family $B=(B_{x,j})_{x\in\mathbb Z,\,j\in\lbrace0,1\rbrace}$ of independent real Brownian motions (`IsBrownianFamily`), $W^{(x)}=(B_{x,0}+\mathrm iB_{x,1})/\sqrt2$. $L\in\mathbb N\cup\lbrace\infty\rbrace$; $\Lambda_\infty=\mathbb Z$.
* **Coupling** (Section 8): "$\psi^\infty$ and $\psi^L$ are driven by the same Brownian motions" is rendered by two hypotheses `IsWaveFunction ⊤ 𝓕 B ψ μ` and `IsWaveFunction L 𝓕 B ψL μ` with the same $\mathcal F$, $B$, $\mu$. Both are otherwise arbitrary realizations (no construction is assumed).
* $\mathcal F^a$ = `nullAug μ 𝓕`: $\mathcal F_t$ augmented by the null sets of $\mu$.
* $P(t,x)=\lvert\psi_t(x)\rvert^2$ (`density`), $p_s(x)$ = `rwKernel s x` $=(e^{s\Delta}\delta_0)(x)$, the law of the continuous-time simple random walk $X_s$ (approved in Stage 2).
* $\mathfrak z_n(t,x)=e^{\theta_nx-n\lambda_nt/2}P(nt/2,x)$ (`zN`), $y_n(t,x)=n^{-1/2}(x-n^{3/4}t)$ (`rescaledPosition`), $\mathsf Z_n(t)=\sum_{x\in\mathbb Z}\mathfrak z_n(t,x)\delta_{y_n(t,x)}$ (`tiltedMeasure`, (3.5)), all of Stage 2.
* **Total variation**: $\lVert\mu-\nu\rVert_{TV}$ is Mathlib's `etvDist μ ν` $=\lvert\mu-\nu\rvert(\mathbb R)$ for finite measures, and $+\infty$ if one of them is infinite; so a bound on it also asserts finiteness.

## Definitions (`FiniteSystems/Defs.lean`)

* `tiltedMeasureBox L n ψ ω t`: $\mathsf Z^L_n(t)=\sum_{x\in\Lambda_L}\mathfrak z_n(t,x)\,\delta_{y_n(t,x)}$, the measure defined before Proposition 8.1, with $\mathfrak z_n$ computed from $\psi$. With $\psi=\psi^L$ it is the article's $\mathsf Z^L_n(t)$; with $L=\infty$ it is $\mathsf Z_n(t)$.
* `rwTail s L`: $\mathsf P(\lvert X_s\rvert\ge L)=\sum_{x\in\mathbb Z,\ \lvert x\rvert\ge L}p_s(x)$.

## Statements

### Proposition 2.1, existence (`FiniteSystems/Statements.lean`)

* `prop_2_1_existence`. On any filtered probability space carrying a Brownian family $B$ indexed by $\mathbb Z\times\lbrace0,1\rbrace$, and for every $L\in\mathbb N\cup\lbrace\infty\rbrace$, there is a process $\psi$ which is a wave function on $\Lambda_L$ driven by $B$, for the filtration $\mathcal F^a$.

  This is *strong* existence (on the given space, driven by the given Brownian motions). For $L=\infty$ it is the existence half of Proposition 2.1; for $L<\infty$ the existence half of "linear SDE in finite dimension" (Section 1.3). The filtration is augmented by the null sets because the solution is built as an almost sure limit which must be made continuous for every $\omega$; the article works under the usual conditions, where $\mathcal F^a=\mathcal F$. The uniqueness half is U1 below.

### Lemma 8.2 (`FiniteSystems/Statements.lean`)

* `lemma_8_2`, **Lemma 8.2 with (8.1)**. Let $\psi$ be a wave function on $\mathbb Z$ and $\psi^L$ a wave function on $\Lambda_L$ ($L\ge1$ an integer), driven by the same Brownian family for the same filtration, on a probability space; $P^\infty=\lvert\psi\rvert^2$, $P^L=\lvert\psi^L\rvert^2$; $S>0$. Then:
  1. for every $s\ge0$ the series $\sum_{\lvert x\rvert\ge L}p_s(x)$ converges;
  2. $s\mapsto\mathsf P(\lvert X_s\rvert\ge L)$ is integrable on $[0,S]$;
  3. $\omega\mapsto\sup_{s\in[0,S]}\big(\sum_{x\in\Lambda_L}\lvert P^\infty(s,x)-P^L(s,x)\rvert\big)^2$ is almost everywhere measurable;
  4. $$\mathbb E\Big[\sup_{s\in[0,S]}\Big(\sum_{x\in\Lambda_L}\big\lvert P^\infty(s,x)-P^L(s,x)\big\rvert\Big)^2\Big]\le4(8+S)\int_0^S\mathsf P(\lvert X_s\rvert\ge L)\,ds.\qquad(8.1)$$

  The expectation is computed in $[0,\infty]$ (the supremum as an element of $[0,\infty]$).

### Proposition 8.1 (`FiniteSystems/Statements.lean`)

* `prop_8_1`, **Proposition 8.1**. Let $n_k\ge1$ with $n_k\to\infty$, and integers $L_k\ge1$ with $L_k/n_k^{3/4}\to\infty$. For each $k$, on a filtered probability space $(\Omega_k,\mathcal F_k,\mu_k)$ with a Brownian family $B_k$, let $\psi_k$ be a wave function on $\mathbb Z$ and $\psi^L_k$ a wave function on $\Lambda_{L_k}$, both driven by $B_k$ for $\mathcal F_k$. Then for all $T>0$ and $\varepsilon>0$,
  $$\mathbb P^\ast_k\Big(\sup_{t\in[0,T]}\big\lVert\mathsf Z^{L_k}_{n_k}(t)-\mathsf Z_{n_k}(t)\big\rVert_{TV}>\varepsilon\Big)\xrightarrow[k\to\infty]{}0,$$
  where $\mathsf Z^{L_k}_{n_k}$ is computed from $\psi^L_k$ and $\mathsf Z_{n_k}$ from $\psi_k$.

### Theorem 1.2 (`Assembly/MainTheorem.lean`)

* `main_theorem_lib`: the frozen `main_theorem` of `MainTheorem.lean`, word for word (see "Checks"). Once it is proved, `Solution.lean` will state `main_theorem` and prove it by quoting `main_theorem_lib` (decision D7‴, at the end of Stage 5).

### Companion statements (library copies)

* `exists_isWaveFunction_lib` (**E1**, `FiniteSystems/Existence.lean`): for every $L$, there are a probability space (in `Type`), a filtration, a Brownian family $B$ indexed by $\mathbb Z\times\lbrace0,1\rbrace$ and a wave function on $\Lambda_L$ driven by $B$.
* `isWaveFunction_unique_lib` (**U1**, `FiniteSystems/Uniqueness.lean`): two wave functions on $\Lambda_L$ driven by the same Brownian family for the same filtration are indistinguishable: almost surely $\psi_t=\psi'_t$ for all $t\ge0$.
* `exists_isWhiteNoise_lib` (**E2**, `WhiteNoise/Existence.lean`): there are a probability space, a filtration and a space-time white noise (`IsWhiteNoise`).
* `IsMildSolution.nonneg_lib` (**P**, `FiniteSystems/Existence.lean`): every solution $Z$ of (1.13) satisfies, almost surely, $Z(t,x)\ge0$ for all $t>0$, $x\in\mathbb R$. **Already deduced** (in Lean) from E1 with $L=\infty$ and the Stage 4 result `IsMildSolution.nonneg_of_isWaveFunction` (proved): it depends only on the `sorry` of E1.
* W and U3: the Stage 4 copies `IsWalshIntegral.ae_eq_lib`, `IsWalshIntegral.isometry_lib`, `isMildSolution_unique_lib` (proved).

### Consequences (`Assembly/Corollaries.lean`, decision D10‴)

* `main_theorem_fixed_time_lib`, `IsMildSolution.integral_sheMeasure_lib`: the two results of `Corollaries.lean` (for fixed $t$ and bounded continuous $\varphi$, $\int\varphi\,d\mathcal Z_{n_k}(t)\Rightarrow\int\varphi\,d\mathcal Z(t)$; and $\int\varphi\,d\mathcal Z(t)=\int Z(t,x)\varphi(x)\,dx$), with the same statements and the same proofs, quoting the library copies. They depend only on the `sorry` of `main_theorem_lib` and of E1, and will be free of `sorry` when those are proved; `Corollaries.lean` itself keeps depending on the statement files.

## Deviations from the article

1. **Sequences instead of the real parameter $n$** in Proposition 8.1 (as in the frozen Theorem 1.2; equivalent).
2. **The coupling** of Section 8 is a pair of hypotheses on one space (same filtration, same Brownian family); nothing is assumed about how $\psi^\infty$, $\psi^L$ were built. In particular $\psi^L$ is not assumed to be $U_te_0$; that it is (up to indistinguishability) is part of the proof.
3. **Augmented filtration** in `prop_2_1_existence` (above).
4. **Lemma 8.2** also asserts that the series and the time integral on the right are genuine and that the supremum on the left is a random variable (up to null sets). The series is asserted for $s\ge0$ only.
5. **Total variation** is $+\infty$ when one of the measures is infinite, so Proposition 8.1 also says that the measures are finite with probability tending to $1$.
6. **Theorem 1.2 for finite $L_n$** (end of Section 8): the sentences "we may now assume that $L_n$ is finite for all $n$" and "since the law of $\mathcal Z_n$ only depends on the law of $P^{L_n}$, we may assume that the QSSEP on $\Lambda_{L_n}$ is coupled to the QSSEP on $\mathbb Z$" are not used. The frozen statement already provides, on each $\Omega_k$, the whole Brownian family indexed by $\mathbb Z\times\lbrace0,1\rbrace$; the wave function on $\mathbb Z$ is constructed on $\Omega_k$ itself from $B_k$ (`prop_2_1_existence`), so the coupling is realized on the given space, and the indices with $L_k=\infty$ and $L_k<\infty$ are treated together (D2‴).
7. **Billingsley's Theorem 3.1** and the bounded Lipschitz distance are replaced by a lemma with an explicit metric on $C([0,T],\mathcal M_+)$ (D6‴). This is a step of the proof, not a statement.

## Decisions D1‴–D12‴ (from `docs/stage5-design.md`, Section 5)

You asked us to proceed without waiting; **the recommendation was taken in every case**, and you review afterwards.

1. **D1‴. Lemma 8.2 with the article's constant $4(8+S)$**, proved with the columns $U_te_y$ of the unitary matrix of Definition 1.1 (built as wave functions on $\Lambda_L$ with initial conditions $e_y$) and a pairing identity (Duhamel (8.2) read coordinatewise: $(U_t^\ast\phi_t)(y)=\langle U_te_y,\phi_t\rangle$), instead of `PLAN.md`'s product rule for $\lVert\phi-\psi^L\rVert^2$ with a weaker constant. **Taken.**
2. **D2‴. Coupling on the given space** (deviation 6). **Taken.**
3. **D3‴. E1 from E2**: Brownian motions $B_{(x,j)}(t)$ = continuous versions of $\xi((0,t]\times(2x+j,2x+j+1])$, then strong existence. **Taken.**
4. **D4‴. E2 by an isonormal Gaussian process** on $L^2(\mathbb R^2)$ (Hilbert basis, product of standard Gaussians). **Taken.**
5. **D5‴. Form of Proposition 8.1**: sequences, one space per $k$, `etvDist`, outer probability. **Taken.**
6. **D6‴. Billingsley's Theorem 3.1** replaced by a Slutsky lemma with an explicit path metric, for varying probability spaces. **Taken.**
7. **D7‴. Layout of the final proof**: the library proves `main_theorem_lib` and the companion copies; `Solution.lean` is rewritten (at the end of Stage 5) to import the library and restate the eight theorems with proofs quoting the copies; `Definitions.lean`, `MainTheorem.lean`, `Companions.lean`, `Challenge.lean` keep their `sorry` and their hashes. **Taken.**
8. **D8‴. U1** by unit-norm Itô versions and the Volterra lemma of Stage 4 (Gronwall), for every $L$. **Taken.**
9. **D9‴. Identification for finite $L$** in new files copied from Stage 2, the approved Stage 2 files being left untouched. **Taken.**
10. **D10‴. Proved copies of the corollaries** (`Assembly/Corollaries.lean`). **Taken, and done** (above).
11. **D11‴. Statement sheet and audit without waiting**: this sheet; an independent audit (task A‴) follows. **Taken.**
12. **D12‴. Comparator**: not installed (a download needs your permission); locally the Stage 0 substitute (`pp.all` comparison of the 17 definitions and 8 theorems between `Challenge.lean` and `Solution.lean`, `#print axioms`). **Taken; the comparator run is left to you.**

## Route changes with respect to `PLAN.md`, Section 3

1. **Section 8 (row "the unitary matrix $U_t$ and the random walk $X$")**: `PLAN.md` said that $U_t$ is not needed and planned the product rule for the norm of $\psi^\infty\vert_{\Lambda_L}-\psi^L$ with a weaker constant. Now (D1‴) $U_t$ is used through its columns $U_te_y$, which are wave functions on $\Lambda_L$ started from $e_y$; Lemma 8.2 is proved as printed, with the constant $4(8+S)$. The matrix SDE (1.6) and the random walk $X$ itself (beyond its law $p_s$) are still not needed. The weaker route would give a bound in $\int_0^Sp_u(\pm L)^{1/2}du$, enough for Proposition 8.1 but not (8.1).
2. **Proposition 2.1 (b)** (Picard iteration, "used only in Section 8 and for E1"): unchanged in substance, but it is now used in the proof of Theorem 1.2 itself, to construct the wave function on $\mathbb Z$ on each given space (D2‴), instead of a transfer of laws.
3. **E1, E2** (table of Section 2 of `PLAN.md`, "Package L" for E1, "Package J" for E2): E2 by an isonormal Gaussian process (D4‴); E1 from E2 through continuous versions of the white noise on unit intervals (D3‴), so E1 rests on E2.
4. **End of the proof of Theorem 1.2**: Billingsley's Theorem 3.1 replaced by an explicit-metric Slutsky lemma (D6‴).

These are to be recorded in `PROGRESS.md` (rule 7 of `CLAUDE.md`).

## Checks

* `lake build` succeeds (Lean 4.35.0, Mathlib v4.35.0); in the new files the only warnings are `declaration uses 'sorry'`.
* **Copies against the frozen statements** (`main_theorem`, `exists_isWaveFunction`, `isWaveFunction_unique`, `exists_isWhiteNoise`, `IsMildSolution.nonneg`, and the two corollaries): in one environment importing both, the types are structurally identical (`Expr` equality, same universe parameters: two for `main_theorem` and `main_theorem_fixed_time`, one for U1, P and `integral_sheMeasure`, none for E1, E2), and their printouts with `pp.all` and all elision disabled (`pp.deepTerms`, `pp.proofs`, thresholds and `pp.maxSteps` raised; no `⋯` in any printout) are identical (30 435 characters for `main_theorem`, 7 680 for E1, 6 040 for U1, 688 for E2, 880 for P, 8 500 and 1 884 for the corollaries). The kernel accepts each copy as a proof of the frozen statement, and conversely (14 checks). The `pp.all` printouts of the Stage 4 copies W, U3 were re-checked against `Companions.lean` (identical, `Expr` equality).
* The three statements of `FiniteSystems/Statements.lean` and the auxiliary lemmas they quote (`picard_isWaveFunction`, `lemma82_bound`, `prop81_tendsto`) are identical in the same sense.
* **Binder scope**: all new statements and definitions were printed with `set_option pp.parens true`; every sum, integral and supremum has the intended scope.
* The steps of Section 8 were re-derived for the statements: the constant of (8.1) ($\lVert\phi-\psi^L\rVert\le\lVert N\rVert+\lVert V\rVert$, Doob $4\int\mathbb E[P^\infty(u,L+1)+P^\infty(u,-L-1)]$, Cauchy–Schwarz for the drift, $\sum_{\Lambda_L}\lvert P^\infty-P^L\rvert\le2\lVert\phi-\psi^L\rVert$), the cancellations of the pairing identity on a box (noise bond by bond; drift $\sum_y(D_L(y)/2-1)\overline{a(y)}\psi(y)$, which is $-\frac12$ at $y=\pm L$ and $0$ inside), and the bound used for Proposition 8.1, $\frac{16}{\varepsilon^2}nT(8+\frac{nT}2)e^{2\theta_nL-rL/3}+\frac{4e^{2T}}{\varepsilon\cosh\ell}$.
* Not checked: that the statements are provable as written (the proofs are the next tasks).

## Remarks on the article

No error was found in Section 8 or in Section 2.1 (as in `docs/stage5-design.md`, Section 1.3). Points where the Lean statements make something explicit:

* In the proof of Lemma 8.2, the identity $\phi_0=\psi^L_0=e_0$ and the unitarity of $U_s$ are used; in Lean, unitarity is obtained from the conservation of inner products of solutions on $\Lambda_L$ (the same pairing identity with two solutions on the box).
* In Lemma 8.2, "$\mathsf P(\lvert X_s\rvert\ge L)$" is $\sum_{\lvert x\rvert\ge L}p_s(x)$ with $p_s$ = `rwKernel`, approved in Stage 2 as the law of $X_s$.
* In the proof of Proposition 8.1, the bound (8.3) uses $\lambda_n\ge0$ and $t\ge0$ for $e^{\theta_nx-n\lambda_nt/2}\le e^{\theta_nL_n}$ on $\Lambda_{L_n}$, and the second term needs $\ell_n>0$ (true for $n$ large); the Lean auxiliary bound assumes $n^{3/4}T<L$.
