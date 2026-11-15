# Stage 1 (pilot): report to the author

12 November 2026. Stage 1 is finished: as `CLAUDE.md` asks, the work stops here until the author decides whether to continue.

## What is proved

Every statement of the pilot (`docs/stage1-statements.md`, approved on 12 November 2026) is proved in Lean. `lake build` succeeds. The pilot files contain no `sorry`, `admit`, `axiom` or `native_decide`, and `#print axioms` of each of the 23 theorems gives only `propext`, `Classical.choice`, `Quot.sound`. The only `sorry` left in the project are those of the statement: `main_theorem`, the seven companion statements, and their copies in `Challenge.lean`.

| Article | Lean | Proof follows |
|---|---|---|
| (3.2), and $\theta^2\le2(\cosh\theta-1)\le\theta^2\cosh\theta$ | `constants_bounds`, `sq_le_two_mul_cosh_sub_one` | the article |
| (4.3) | `chainGen_max_abs_one`, `chainGen_sq` | direct computation |
| Lemma 4.1 | `occupationTime_le` | the analytic route of `PLAN.md` (see below) |
| Lemma 4.2 (1), (4.5) | `uN_neg`, `uN_zero`, `hasDerivAt_uN_apply`, `uN_regularity` | operator exponential on $\ell^\infty(\mathbb Z)$ |
| Lemma 4.2 (2), (4.6) | `uN_bounds`, `uN_le_one_add_sqrt` | Khas'minskii, in analytic form (see below) |
| Section 6, properties of $\kappa$ and $k_m$; (6.5); (6.6) | `IsMollifier.kappa_*`, `kM_props`, `tsum_chainPi_mul_kM`, `bM_bounds` | the article; (6.6) directly |
| (6.7), Lemma 6.3 | `gM_spec`, `chainGen_gM`, `gM_nonneg_le`, `abs_gM_succ_sub_le`, `gM_add_one_eq_sub_one`, `exists_gM_zero_le` | the article |

**No step of the article failed, and no statement turned out false.** Nothing was added to "Questions and findings for the article".

### How the analytic route goes

* **Semigroup tools** (`SecondMoments/Semigroup.lean`, reusable).
  * Positivity: for $t,a,b\ge0$ and a bounded $w\ge0$, $e^{t(a\mathcal R+bM_w)}$ maps nonnegative functions to nonnegative functions, where $M_w$ is the multiplication by $w$. This holds because $a\mathcal R+bM_w+cI$ has nonnegative matrix entries for $c$ large enough.
  * Comparison principle: if $d'-Ad\ge0$ on $[0,t]$ and $d(0)\ge0$, then $d(t)\ge0$, for $A$ of this form.
  * $\mathcal R\mathbf 1=0$.
* **Lemma 4.1.** Let $V(S)=\int_0^Se^{u\mathcal R}h\ du$, with $h=\mathbf 1_{\lvert r\rvert=1}$. Then $V$ satisfies $V'=\mathcal RV+h$ and $V(0)=0$. The function $w(S,r)=\tfrac12\big(\sqrt{1+r^2+4S}-\max(\lvert r\rvert,1)\big)$ satisfies $\partial_Sw\ge\mathcal Rw+h$, by (4.3) and the concavity of the square root. The comparison principle gives $V\le w\le\tfrac14+\sqrt S$. The bound by $S$ comes from $0\le e^{v\mathcal R}h\le\mathbf 1$.
* **Lemma 4.2 (2).** Write $u(t)=e^{tA_n}\mathbf 1$ with $A_n=a\mathcal R+bM_h$, $a=\tfrac{nc_n}2$, $b=\tfrac{n\lambda_n}2$, and let $U=\max_{[0,t]}\lVert u\rVert$.
  * The comparison principle, applied with the operator $a\mathcal R$, gives $u\le\mathbf 1+\tfrac{bU}aV(at)$.
  * Lemma 4.1 then gives $u\le1+\tfrac54\sqrt t\ U$. Here $b^2\le a$ follows from (3.2), since $n\lambda_n^2=a_n^2\le c_n^2\le2c_n$; the article bounds the constant by $2\sqrt t$, the Lean proof by $\tfrac54\sqrt t$.
  * For $t\le\tfrac1{16}$ this gives $u\le1+4\sqrt t\le2$.
  * Positivity gives sub-multiplicativity $u(t+s)\le\lVert u(s)\rVert\ u(t)$, hence $u(t)\le2^{1+16t}$.
  * The lower bound $u\ge1$ comes from the comparison principle applied to $u-\mathbf 1$.

## Size

| | Lines of Lean |
|---|---|
| Statements and definitions (approved before the proofs) | 461 |
| Proofs and auxiliary results | 1,449 |
| **Total for Stage 1** | **1,910** (8 files, 1,902 lines now) |

The plan estimated the analytic part of package F and Lemma 6.3 at 4,000 to 6,000 lines. The pilot took about a third of that.

## Sessions, models, time

| Work | Model | Wall time | Runs of Lean | Lines |
|---|---|---|---|---|
| Statements, numerical test, checks, merges (this session) | Opus 5.5, effort not shown | – | – | 461 |
| Model test, Section 6.1 and Lemma 6.3 | Opus 5.5, `high` (new session) | 12 min | 16 | 495 (kept) |
| Model test, Section 6.1 and Lemma 6.3 | Fable 5.2, `high` (new session) | 11 min | 9 | 561 (not kept) |
| (3.2) | Opus 5.5 agent of this session | 1.6 min | 9 | 64 |
| (4.3), Lemma 4.1, semigroup tools | Opus 5.5 agent of this session | 13 min | 15 | 563 |
| Lemma 4.2 | Opus 5.5 agent of this session | 7.3 min | 13 | 345 |

From the approval of the statements to the last proof, the proofs themselves took about 35 minutes of agent time. The agents started from a fresh context, so they did not re-read this long conversation; their effort level cannot be set, and it is not shown.

## Usage

* Model test, measured by the author (session reports): Opus 5.5 at `high`, **3.60 USD**; Fable 5.2 at `high`, **5.65 USD**, for the same task. Both amounts are API-equivalent estimates, not amounts billed.
* Plan limits: weekly 53% after the Opus run and 55% after the Fable run; scoped weekly 83% and then 86%.
* The three agents (3.2, Lemma 4.1, Lemma 4.2) used 67k, 180k and 140k tokens as counted by Claude Code. Their cost is included in the usage of this session, which can only be read from outside: **`/usage` of this session, or Settings > Usage, to be read by the author.**
* Rate measured on the model test: about 7 USD per 1,000 lines of Lean kept (Opus 5.5).

**What this says about the whole proof, with caution.** At the pilot's rate, the 80,000 to 125,000 lines of the plan would cost of the order of 600 USD to 900 USD API-equivalent, and some tens of hours of agent time. The plan estimated 5,000 USD to 14,000 USD. But the pilot is the easiest part of the proof: it contains no stochastic calculus, no measure theory on path spaces, and no identification of limits, and the Lemma 4.1–4.2 work also benefited from a detailed proof sketch. The plan's own estimate for the pilot (4,000 to 6,000 lines) was three times too high, and its estimates for packages I, J, K are the least certain. A second measurement on a stochastic package (B or C) would be needed before relying on these figures.

## Difficulties, and what was learned

1. **The frozen statements can be elaborated differently without any change of text.** Two imports added to `FeynmanKac.lean` made Lean reach two standard structures by different, equivalent routes: "$\mathbb R$ is a normed space over $\mathbb R$" through the inner product space instead of the normed field, and a different proof of the continuity of scalar multiplication. This happened in `defectOp`, `hasDerivAt_uN_apply` and `uN_regularity`. The kernel checked that the approved statements and the approved value of `defectOp` are definitionally equal to the new ones (`rfl`, about 10 minutes of checking). The new script `scripts/check_frozen.py` compares every frozen declaration with an approved commit and flags such differences. The last run: the 25 declarations of the statement of Theorem 1.2 are identical to those approved at Stage 0; of the 42 pilot declarations, 39 are identical and the 3 above are definitionally equal.
2. **My own checks were first made on truncated printouts.** Lean elides deep subterms (`⋯`) by default, even with `pp.all`. All comparisons were redone with elision disabled, including `Challenge` against `Solution`, and they hold.
3. **Lean and Mathlib technicalities**, none mathematical:
   * imports that are not transitive under the module system;
   * the exponential of an operator lacking an algebra structure over $\mathbb Q$ in one Mathlib lemma;
   * timeouts when splitting $\sum_{\mathbb Z}$ into two sums over $\mathbb N$;
   * renamed and deprecated Mathlib names;
   * casts between $\mathbb N$, $\mathbb Z$ and $\mathbb R$.
4. **Working method.** One agent per file, each in its own git worktree sharing Mathlib, checked and merged by the main session. This worked well: the two independent files were proved in parallel, and each agent started from a short context.

## Decision for the author

Whether to continue to Stage 2 (packages B, C, D, E, G and the rest of F: martingales in continuous time, the Itô integral, the wave function, the tilted field, the replacement lemma), and if so with which setting. A reasonable next step would be to measure the cost on one package with stochastic content, for instance B (Doob's inequalities and optional stopping in continuous time), before committing to the whole.
