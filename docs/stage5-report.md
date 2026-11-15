# Stage 5 (finite systems and assembly): final report to the author

13 November 2026. Stage 5 is finished, and with it the formal proof of Theorem 1.2.

## What is proved

**Theorem 1.2 holds in Lean, for every sequence $L_k\in\mathbb Z_{\ge1}\cup\lbrace\infty\rbrace$ with $L_k/n_k^{3/4}\to\infty$**, as frozen and approved at Stage 0 (`main_theorem`), together with all the companion statements:

| | Statement | Lean (in `Solution.lean`) |
|---|---|---|
| Thm 1.2 | convergence of $\mathcal Z_{n_k}$ to the solution of the SHE in $C([0,T],\mathcal M_+)$ | `main_theorem` |
| E1 | existence of the wave function for every $L$ | `exists_isWaveFunction` |
| U1 | uniqueness of the wave function | `isWaveFunction_unique` |
| E2 | existence of a space-time white noise | `exists_isWhiteNoise` |
| W | Itô isometry and uniqueness for the Walsh integral | `IsWalshIntegral.isometry`, `IsWalshIntegral.ae_eq` |
| U3 | uniqueness of the solution of (1.13) | `isMildSolution_unique` |
| P | positivity of the solution of (1.13) | `IsMildSolution.nonneg` |

(E3, existence of a continuous mild solution, was excluded by the author's decision of 11 November 2026.)

**Checks** (13 November 2026, commit `eb55058`):

* `lake build` succeeds for the three targets `QSSEPtoKPZ`, `Challenge`, `Solution`. The only `sorry` in the project are those of the statement files `MainTheorem.lean`, `Companions.lean` and their copy `Challenge.lean` (decision D7‴: these files keep their approved hashes; `Solution.lean` proves the same theorems from the library).
* In `Solution.lean`, `#print axioms` of the eight theorems gives only `propext`, `Classical.choice`, `Quot.sound`.
* **Comparator substitute**: the 25 declarations of `Challenge.lean` (17 definitions, 8 theorems), printed fully elaborated (`pp.all`, no elision), are identical in the environments of `Challenge.lean` and `Solution.lean`. `make_challenge.py --check` passes; `Definitions.lean`, `MainTheorem.lean`, `Companions.lean`, `Challenge.lean` have their Stage 0 hashes.
* All approved or frozen statements of Stages 2–5 (105 declarations) are unchanged (`check_frozen` against `897d883`, `535961f`, `2a86280`, `afb1d44`) and depend only on the three standard axioms.
* **Comparator** (15 November 2026): `lake comparator` (part of Lean 4.35.0, nothing downloaded) accepts the solution; with `--paranoid`, the Lean paranoid kernel, lean4lean, nanoda, con-leche and con-ron all accept it as well (logs `docs/comparator-2026-11-15.log`, `docs/comparator-paranoid-2026-11-15.log`).

## Section 8 and the existence results

* **Proposition 2.1 (existence)** by Picard iteration in $\ell^2$: contraction $\mathbb E\sup_{s\le t}\lVert\varphi_1'-\varphi_2'\rVert^2\le(16+2T)\int_0^t\mathbb E\sup_{u\le s}\lVert\varphi_1-\varphi_2\rVert^2ds$, iterated bound $d_k\le d_0(Cn)^k/k!$, almost sure uniform convergence.
* **U1** by Gronwall's inequality (through the Volterra lemma of Stage 4).
* **Lemma 8.2** with the article's constant $4(8+S)$, through the columns of $U_t$ (decision D1‴, a change of route: `PLAN.md` had said $U_t$ is not needed), the pairing identity on $\Lambda_L$ (conservation of inner products; the Duhamel formula (8.2) coordinate by coordinate), Parseval and Doob.
* **Proposition 8.1** as in the article: (8.3), Chebyshev with Lemma 8.2, (5.1), Chernoff with $\cosh r-1\le\frac23r^2$ on $[0,1]$.
* **`main_theorem` for finite $L_k$**: on each given space the wave function on $\mathbb Z$ is built from the given Brownian family (strong existence), `main_theorem_top` of Stage 4 applies, and the finite systems are compared through Proposition 8.1 and a Slutsky lemma (decisions D2‴, D6‴).
* **E2** from an isonormal Gaussian process on $L^2(\mathbb R^2)$; **E1** from a Brownian family built from the white noise (continuous versions of Stage 4) and Proposition 2.1; **P** from E1 and the conditional positivity of Stage 4.

**The article.** No step of Sections 2.1 and 8 failed. The independent audit of the Stage 5 statements found no error (one missing helper lemma, added).

## Size, time, usage

* **Lean:** about 8,700 lines in Stage 5 (design estimate 10,000–16,000); 62,600 lines in the library in total.
* **Time:** Stage 5 from the start of its design (13 November, 13:51 CET) to the final checks (about 16:25), about 2.5 hours, with up to seven agents in parallel.
* **Agents:** 21 Opus 5.5 agents (design, statements and interfaces, audit, 18 proof tasks).
* **Usage:** weekly limit (all models) 92% before Stage 5, 98% after it.

## Over the whole project (11–13 November 2026)

About 62,600 lines of Lean, five stages, roughly 110 agents. Errors in statements were found and corrected at every stage by audits before the author's approval, and one after approval (the parenthesization of (7.13), Stage 4, corrected with the author's agreement; a parse audit of all approved declarations found no other). No step of the article was found to fail; the departures from the printed proofs are listed in the stage reports (`docs/stage2-report.md` to `docs/stage5-report.md`).

## Remaining

* Nothing has been published or pushed (rule 1).
