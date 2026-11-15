# Stage 2 (fixed $n$): report to the author

13 November 2026. Stage 2 is finished. Following the author's instruction, Stage 3 (tightness) has started.

## What is proved

The checkpoint of `PLAN.md` is reached: Propositions 3.1, 4.3, 6.1 and 6.2 hold in Lean for every realization of the wave function on $\mathbb Z$, with no usual conditions on the filtration. All 27 statements approved on 12 November 2026 (`docs/stage2-statements.pdf`) are proved, together with the definitions they use: 65 declarations in all.

* `#print axioms` of each of the 65 gives only `propext`, `Classical.choice`, `Quot.sound`.
* `lake build` succeeds. The only `sorry` left in the project are those of the statement of Theorem 1.2: `main_theorem`, the seven companion statements, and their copies in `Challenge.lean`.
* Frozen statements, checked with `scripts/check_frozen.py`, fully elaborated and with no elision:
  * the 25 declarations of the statement of Theorem 1.2 are identical to those approved at Stage 0, and the four statement files have their approved hashes;
  * the 65 declarations of Stage 2 are identical to those approved at commit `897d883`;
  * the Stage 1 declarations are unchanged since the Stage 1 report: 39 identical, and 3 definitionally equal, as checked by the kernel at the time.

| Article | Lean | Note |
|---|---|---|
| (2.2) | `moment_bound` | proved, instead of the citation of Da Prato–Zabczyk |
| conservation of mass | `hasSum_density` | proved first, by localization |
| Prop 2.2, with $\mathbb EP(t,x)=p_t(x)$ | `prop_2_2` | |
| Lemma 2.3 (1), (2) | `lemma_2_3_linear`, `lemma_2_3_quadratic` | |
| (3.7)–(3.9), (3.18), (3.20), (3.23), Prop 3.1, (3.16) | `TiltedField/` | |
| Lemma 3.2 | `lemma_3_2` | |
| Prop 4.3, (4.7)–(4.9) | `SecondMoments/TotalMass.lean` | |
| (6.1), (6.11), Lemma 6.4, Prop 6.1, $b_m\to1$, Prop 6.2 | `Replacement/` | |

The infrastructure is generic and reusable in later stages:

* **Package B, martingales in continuous time:** null augmentation and versions, Doob's maximal and $L^2$ inequalities, stopping times, optional sampling, stopped martingales and brackets.
* **Package C, the Itô integral** against a countable Brownian family: isometry, martingale property, brackets, linearity, stopping, the fourth moment bound $\mathbb E[(I_v-I_u)^4]\le3K^2(v-u)^2$, convergence of the left-point Riemann sums of the frozen definition, and the product rule.

## The article

No step of the article failed, and no statement needed a hypothesis that the article does not state. Remarks, all minor and recorded in `PROGRESS.md`:

* **Hypotheses not needed.** (3.20) holds for every $f$ (symmetry is not needed), and (3.23) for every $g$ (evenness is not needed). The approved statements keep the article's hypotheses.
* **Different routes in Lean.** These are not corrections:
  * (2.2) is proved by Jensen's inequality, $V_a^{2^k}\le V_{2^ka}$ for the probability $P(t,\cdot)$, and by a nonpositive drift for $e^{-ct}V$.
  * Lemma 2.3 (1) controls the tails with (2.2) for $k=1$, using $P\le1$.
  * In Proposition 6.2 the martingale term is bounded through (4.8): this gives a factor $K^2$ instead of $K^4$, with the same conclusion.
  * $\mathbb EP=p_t$ uses uniqueness by Picard iteration.
* **Constants.** The constant of Proposition 3.1 (1) was checked against the printed proof: the coefficients are at most $\cosh(1)/4$, $\cosh(1)/6$ and $e/6$.
* **Design, not article.** The drift bound $\Delta w_R\le2(\cosh a-1)w_R$ of the design document fails at $x=0$; the constant $2(e^a-1)$ was used instead. The article is not affected: it cites Da Prato–Zabczyk for (2.2).

## Size, time, usage

* **Lean:** about 22,300 lines added in Stage 2 (78 files); 25,200 lines in the library in total. The design estimated 16,000–27,000 lines for Stage 2, and `PLAN.md` 30,000–45,000.
* **Time:** from the start of the design (12 November, about 21:50) to the last merge (13 November, about 01:50), about 4 hours, with up to six agents in parallel.
* **Agents:** 27 Opus 5.5 agents, each in a fresh context and its own git worktree: design, statements, interfaces, audit, and 23 proof tasks. Claude Code counted about 7.2 million tokens for them.
* **Usage:** the 5-hour limit was reached once (13 November, about 01:05). One task was interrupted and resumed from its saved state after the reset. The usage of this session, which includes the agents, is to be read by the author (`/usage`, or Settings > Usage).

## How the work was organised

* The author approved the statements. An independent audit before the approval found one error, in the definition of a cross-bracket, which needed bounded variation; it was fixed before the approval.
* Every merge went through `scripts/task_merge.sh`. It checks a clean state, that no frozen file is touched, that no `sorry` is left, that the statements existing at the base and the 65 approved declarations are unchanged, and that both the branch and the merged state build.
* Two incidents were caught and fixed:
  * a name clash between two parallel tasks; the merge script now builds the merged state before committing;
  * a first version of the merge script that could miss a changed statement; it was fixed before it mattered.
* `docs/handoff.md` and `AGENTS.md` allow the work to be resumed by another session or by Codex.
