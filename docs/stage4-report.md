# Stage 4 (identification of the limit): report to the author

13 November 2026. Stage 4 is finished. Following the author's instruction, Stage 5 has started (its design is being written).

## What is proved

The checkpoint of `PLAN.md` is reached: **Theorem 1.2 holds in Lean when $L_n=\infty$ for all $n$** (`main_theorem_top`, which is the frozen `main_theorem` with $L_k=\infty$; checked with `pp.all`, and Lean derives one from the other). All statements approved on 13 November 2026 (`docs/stage4-statements.pdf`, decisions D1″–D11″) are proved:

| Article | Lean | Content |
|---|---|---|
| Prop 7.1, (7.1)–(7.3) | `prop_7_1` | limit points: $\mathcal Z(0)=\delta_0$; density $Z\ge0$, predictable, in $L^2$; martingale problem with bracket $\int_0^t\int Z^2\phi^2$ |
| (7.4) | `eq_7_4` | $\mathbb E\int_0^T\lVert\mathcal Z(t)\ast\rho_\varepsilon\rVert_2^2dt\le C2^{16T}$, $C$ depending only on $\rho$ |
| Prop 7.2, (7.8) | `prop_7_2` | representation with a white noise on an enlarged space |
| Prop 7.3, (7.13) | `prop_7_3` | uniqueness in $\mathcal H_T$ for the weak mild equation |
| (7.15) | `IsMildSolution.integral_sq` | $\mathbb E[Z(t,x)^2]=\sum_{k\ge1}K^{\ast k}(t,x)$ for the given solution |
| after (7.15) | `IsMildSolution.isWeakMild` | the given solution satisfies (7.13) for every $t$ (stochastic Fubini) |
| Thm 1.2, $L_n=\infty$ | `main_theorem_top` | convergence in distribution in $C([0,T],\mathcal M_+)$ |
| companion P, conditional | `IsMildSolution.nonneg_of_isWaveFunction` | if a wave function on $\mathbb Z$ exists, every solution of (1.13) is $\ge0$ |
| companions W, U3 | `IsWalshIntegral.ae_eq_lib`, `isometry_lib`, `isMildSolution_unique_lib` | Itô's isometry and uniqueness for the Walsh integral; uniqueness of the solution of (1.13) |

* `#print axioms` of each of the 93 approved statements of Stages 2–4 gives only `propext`, `Classical.choice`, `Quot.sound`.
* `lake build` succeeds. No `sorry` is left in the library except those of the statement of Theorem 1.2 (`main_theorem`, the companion statements, `Challenge.lean`), which Stage 5 closes.
* Frozen statements, checked with `scripts/check_frozen.py` (fully elaborated, no elision): the 65 of Stage 2, the 7 of Stage 3 and the 21 of Stage 4 are identical to the approved ones; the four statement files of Stage 0 have their approved hashes.

Generic infrastructure proved on the way (none of it was in Mathlib): Skorokhod's representation along a subsequence on separable metrizable spaces; Lévy's characterization (one martingale and finite families); the integral against an orthogonal martingale measure; Walsh integrals: isometry, existence, martingale property, a continuous version (built by hand: the frozen white noise has no continuity clause and Mathlib has no Kolmogorov–Chentsov theorem); the law of the noise; the projection of Walsh integrals onto the noise and their transfer between probability spaces; heat-kernel identities, the iterated kernels $K^{\ast k}$ (Beta integrals), a Volterra lemma; $L^2$ densities by duality and Lebesgue differentiation for mollifiers.

## The article

No step of Section 7 failed. Where the Lean proof departs from the printed text (decisions D1″–D5″, approved):

* **Skorokhod** is used only along a subsequence, proved by explicit couplings; no Polishness of $\mathcal M_+$ is needed.
* **BDG** is replaced by a localization at the first time $\max(\langle M_n^\phi\rangle,(M_n^\phi)^2)\ge L$. The passage from local to true martingale at the end of Proposition 7.1 (3), implicit in the article, is written out.
* **Identification without existence:** the given solution $Z$ of (1.13) plays the role of $Z^\star$. A solution of (7.13) is a function of the noise (conditioning on the noise gives another solution, then Proposition 7.3), which transfers to any space carrying a white noise. Lusin–Souslin is replaced by the $\sigma$-compact range of a tight law. Positivity of $Z$ on $(0,T]$ is deduced from the limit.
* **Proposition 7.3** with mollified test functions and the inequality $F\le K\ast F$, instead of an orthonormal basis.
* Smaller points: in Step 3 of Proposition 7.2 the approximation error is bounded with $(\sum_{i<N}x_i)^2\le N\sum x_i^2$ instead of orthogonality; Proposition 6.2 is used in a form uniform in the realization (its proof gives it; the approved statement fixes the realization first). The Stage 4 design and an independent audit list the four places where Section 7 is compressed (design, Section 1.3); all were filled in.

## Errors found in the statements, and their correction

* **Before approval** (independent audit and an external review): `prop_7_2` lacked $\mathcal Z(0)=\delta_0$ and was false without it; the constant of `eq_7_4` could depend on the probability space; two interfaces (the projection onto the noise, which used a conditional expectation on an infinite measure space, and the closure rule of the martingale-measure integral) were false. All corrected before the author's approval.
* **After approval:** a parsing error in the approved definition `IsWeakMild` (Lean reads `∫ x, a - ∫ x, b` as `∫ x, (a - ∫ x, b)`), which made `IsMildSolution.isWeakMild` false. Found by the task proving Proposition 7.3; corrected by parentheses with the author's agreement. A parse audit of all 161 approved declarations of Stages 0–4 (`docs/parse-audit.md`), printed with explicit parentheses, found no other error. The pitfall is now in `CLAUDE.md` and in the task rules.

## Size, time, usage

* **Lean:** about 25,300 lines added in Stage 4 (98 files); 54,000 lines in the library in total. The design estimated 16,000–26,000 lines, `PLAN.md` 27,000–41,000.
* **Time:** from the start of the design (13 November, 08:03 CET) to the final integration (14:06), about 6 hours, with up to eight agents in parallel. The author's approval came at about 12:10.
* **Agents:** 34 Opus 5.5 agents: design, statements and interfaces, audit, repair, parse audit, and 29 proof tasks (5 to 50 minutes each).
* **Usage:** weekly limit (all models) 76% before Stage 4, 92% after it; 5-hour window 33%.
* **Tooling:** merges are serialized by a lock; the merge script builds a branch before checking its statements (a stale build once gave a false alarm); the printouts of approved statements at fixed commits are cached.
