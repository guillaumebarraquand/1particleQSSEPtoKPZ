# Stage 3 (tightness): report to the author

13 November 2026. Stage 3 is finished. Following the author's instruction, Stage 4 (identification of the limit) has started.

## What is proved

The checkpoint of `PLAN.md` is reached: Proposition 5.1 holds in Lean. All 7 statements approved on 13 November 2026 (`docs/stage3-statements.pdf`, decisions D1'–D8') are proved:

| Article | Lean | Content |
|---|---|---|
| notation of Section 5 | `integral_tiltedMeasure` | $\int\varphi\ d\mathsf Z_n(t)=\sum_x\mathfrak z_n(t,x)\varphi(y_n(t,x))=\mathsf Z_n(t;\varphi)$ for bounded measurable $\varphi$ |
| Lemma 5.2, (5.1) | `lemma_5_2` | $\mathbb E[\mathsf Z_n(t;e_b)]\le e^{2t}$ for $\lvert b\rvert\le1$; $\mathbb P(\sup_{t\le T}\mathsf Z_n(t;\cosh)\ge K)\le2e^{2T}/K$ |
| (5.2) | `aldous_condition` | $\mathbb P(\lvert\mathsf Z_n(\tau+s;\varphi)-\mathsf Z_n(\tau;\varphi)\rvert>\eta)\le c\big(\frac{Cs}\eta+\frac{C^2\sqrt s}{\eta^2}\big)$ |
| Prop 5.1, continuity | `prop_5_1_continuous`, `prop_5_1_version` | continuous trajectories; a Borel-measurable version in $C([0,T],\mathcal M_+)$ |
| Prop 5.1, tightness | `prop_5_1`, `prop_5_1_isTight` | uniform compact sets; tightness of the laws in Mathlib's sense |

* `#print axioms` of each of the 7 gives only `propext`, `Classical.choice`, `Quot.sound`.
* `lake build` succeeds. The only `sorry` left in the project are those of the statement of Theorem 1.2 (`main_theorem`, the companion statements, and their copies in `Challenge.lean`).
* Frozen statements, checked with `scripts/check_frozen.py` (fully elaborated, no elision) at every merge: the 7 statements of Stage 3 are identical to those approved at commit `535961f`, and the 65 declarations of Stage 2 to those approved at `897d883`.

Infrastructure proved on the way, generic and reusable:

* a countable family of bump functions $(f_j)$ that determines weak convergence on $\mathcal M_+(\mathbb R)$; the embedding $\mu\mapsto(\mu(f_j))_j$ of $\mathcal M_+$ into $\mathbb R^{\mathbb N}$; $\mathcal M_+$ is metrizable and second countable, and its Borel $\sigma$-algebra is described (none of this was in Mathlib);
* compactness of $\lbrace\mu:\int\cosh\ d\mu\le M\rbrace$, and of sets of paths in $C([0,T],\mathcal M_+)$ (Arzelà–Ascoli);
* Aldous' criterion for processes with continuous paths;
* a version of $t\mapsto\mathsf Z_n(t)$ with all paths continuous and adapted test integrals, and a measurable version of $t\mapsto\mathcal Z_n(t)=\varrho_n(t)\mathsf Z_n(t)$, the measure of Theorem 1.2 (for Stage 5).

## The article

No step of the article failed. Places where the Lean proof is worded differently (same mathematics):

* **(5.1).** Doob's inequality is applied to the martingale $\sum_x\alpha_s(x)P(s,x)$, $\alpha_s(x)=e^{\theta'x-2(\cosh\theta'-1)s}$, on $[0,nT/2]$ for $\mathcal F$ directly, instead of after the time change to $\mathcal F^n$. The supremum is handled by bounding the event for every $K'<K$ and letting $K'\to K$, so that continuity of the paths is not needed at that point. The identity $\mathsf Z_n(t;e_b)=e^{\kappa t}N_b(nt/2)$ holds for every realization, and only $\kappa\le2$ is used.
* **(5.2).** The constant obtained is $c=32(1+2^{3+16H})$ with $H=T+1$. The article's bound on $\mathbb E\sup\mathsf W_n$ is obtained from $\sup\mathsf W_n\le1+\sup\mathsf W_n^2$ and (4.8).
* **Proposition 5.1.** The compact set is $\lbrace\gamma:\gamma(t)\in\lbrace\int\cosh\le K\rbrace\ \forall t,\ t\mapsto\gamma(t)(f_j)\in\mathcal C_j\ \forall j\rbrace$, with $K=4e^{2T}/\varepsilon$ and $\mathcal C_j$ sets of equicontinuous paths obtained from Aldous' criterion with errors $\varepsilon2^{-j-m-3}$.

## Size, time, usage

* **Lean:** about 3,550 lines added in Stage 3 (16 files); 28,800 lines in the library in total. The design estimated 4,600–8,200 lines, `PLAN.md` 8,000–12,000.
* **Time:** design, statements, interfaces, audit and infrastructure on 13 November from about 01:55 to 03:00 (CET); the four proof tasks after the approval, from 08:00 to 08:47, about 5 to 10 minutes each.
* **Agents:** 13 Opus 5.5 agents (design, statements, interfaces, audit, 5 infrastructure tasks (H1 with H3, H2, H4, H5a, H5b), 4 proof tasks), each in a fresh context and its own git worktree.
* **Usage:** weekly limit (all models) 72% before Stage 3, 76% after it (the Stage 4 design included); 5-hour window 12%.
