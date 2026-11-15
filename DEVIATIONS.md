# Where the formal proof departs from the article

The formal proof follows the article section by section. It departs from the printed proofs where a theorem cited in the article is not available in Mathlib and a direct argument was shorter, or where the article compresses a step. **No step of the article was found to fail, and no statement of the article needed a hypothesis that the article does not state.** Details, stage by stage, are in `docs/stage1-report.md` to `docs/stage5-report.md` and in the design documents.

## General

* **Filtrations** are arbitrary (no usual conditions). Martingales and brackets are defined up to null sets; stopping times are taken for the filtration augmented by the null sets.
* **Stochastic calculus** is developed only as far as needed: the Itô integral against a countable family of Brownian motions, and the product rule for processes $X_0+\int a\,ds+\sum_j\int b_j\,dB_j$. Everything in Sections 2–6 is polynomial in $\psi$, so no general Itô formula is needed.
* **Constants**: several estimates hold with constants different from the printed ones; each time the conclusion used later is the same.

## Section 2 (the wave function on $\mathbb Z$)

* Proposition 2.1 (well-posedness in $\ell^2_a$) is cited from Da Prato–Zabczyk in the article. In Lean: conservation of $\sum_xP(t,x)$ and the moment bound (2.2) are proved for *any* solution, by the product rule with truncated weights; (2.2) by Jensen's inequality $V_a^{2^k}\le V_{2^ka}$ and a nonpositive drift for $e^{-ct}V$. Existence is proved by Picard iteration in $\ell^2$ (Stage 5), uniqueness by Gronwall's inequality.
* $\mathbb E P(t,x)=p_t(x)$ uses uniqueness for the Kolmogorov equation by Picard iteration.
* Lemma 2.3 (1): the tails are controlled with (2.2) for $k=1$ and $P\le1$.

## Section 3 (the tilted field)

* (3.20) holds for every $f$ (symmetry is not needed) and (3.23) for every $g$ (evenness is not needed); the statements keep the article's hypotheses.

## Section 4 (second moments)

* The Markov chain $R$ is replaced by its generator $\mathcal R$, a bounded operator on $\ell^\infty(\mathbb Z)$, and $\mathsf E_r[f(R_v)]$ by $(e^{v\mathcal R}f)(r)$; $u_n$ is defined by the operator exponential instead of the Feynman–Kac formula. Lemmas 4.1 and 4.2 are proved analytically in $\ell^\infty(\mathbb Z)$ (positivity of $e^{t\mathcal R}$, the identities (4.3), Duhamel's formula). The constant in Lemma 4.2 (2) can be taken $\frac54\sqrt t$.

## Section 5 (tightness)

* Jakubowski's criterion in the Skorokhod space $D([0,T],\mathcal M_+)$ is replaced by a criterion directly in $C([0,T],\mathcal M_+)$: compact containment and tightness of $t\mapsto\mathsf Z_n(t;f_j)$ in $C([0,T],\mathbb R)$ for a countable family of bump functions $f_j$, with Aldous' criterion for processes with continuous paths.
* (5.1): Doob's inequality is applied to $\sum_x\alpha_s(x)P(s,x)$ for the original filtration (no time change), and the supremum is handled by bounding the event for every $K'<K$.

## Section 6 (the replacement lemma)

* In Proposition 6.2 the martingale term is bounded through (4.8), which gives a factor $K^2$ instead of $K^4$, with the same conclusion. Section 7 uses Proposition 6.2 in a form uniform in the realization of the wave function; the proof gives it (its constant comes from Lemma 6.4 and depends only on the mollifier).

## Section 7 (identification of the limit)

* **Skorokhod's representation** (Billingsley, Theorem 6.7) is used only along a subsequence, and is proved by explicit couplings on a separable metrizable space; completeness of $\mathcal M_+$ is not needed.
* **BDG** is replaced by a localization at the first time $\max(\langle M_n^\phi\rangle,(M_n^\phi)^2)\ge L$. The passage from local to true martingale at the end of Proposition 7.1 (3), implicit in the article, is written out (from $\mathbb E\,Q(T)<\infty$ and Doob).
* **Proposition 7.1 (2)**: the $L^2$ density is obtained by duality (Riesz) instead of weak compactness, and identified by Lebesgue's differentiation theorem for the mollifiers.
* **Proposition 7.2**: Lévy's characterization is proved by discretization (for one martingale and for finite families). In Step 3 the approximation error is bounded with $(\sum_{i<N}x_i)^2\le N\sum x_i^2$ instead of orthogonality. The enlargement of the probability space is the product with a space carrying a white noise.
* **Proposition 7.3** is proved with the test functions $\rho_\delta(z-\cdot)$ and the inequality $F\le K\ast F$ (then a Volterra lemma), instead of an orthonormal basis and Parseval.
* **End of the proof.** The article takes the solution $Z^\star$ of (7.14) given by Chen–Dalang and concludes that "the law of $\mathcal Z$ is the law of the process described in the statement". In Lean no existence result is used: the given solution $Z$ of (1.13) plays the role of $Z^\star$ ((7.15) is proved for it as the series $\sum_kK^{\ast k}$, and (7.13) by a stochastic Fubini argument), and the identification is done by uniqueness in law: conditioning a solution of (7.13) on the noise gives another solution, so by Proposition 7.3 the solution is a function of the noise, which transfers to any space carrying a white noise. The Lusin–Souslin step is replaced by the $\sigma$-compactness of a tight law. The positivity of $Z$ is deduced from the limit.

## Section 8 (finite systems)

* For finite $L_k$, the wave function on $\mathbb Z$ is built on each given probability space from its Brownian family (strong existence by Picard iteration), so the finite and infinite systems are compared directly on one space; the step "the law depends only on the law of $P^L$" is not needed.
* **Lemma 8.2** is proved with the article's constant $4(8+S)$, through the columns $U_te_y$ of the evolution (each one a wave function started from $e_y$), the pairing identity on $\Lambda_L$ (the Duhamel formula (8.2) coordinate by coordinate), Parseval and Doob.
* **Theorem 3.1 of Billingsley** (convergence of close sequences) is replaced by a Slutsky lemma with one probability space per $k$ and an explicit metric on $C([0,T],\mathcal M_+)$.

## Companion statements

* E2 (existence of a white noise) from an isonormal Gaussian process on $L^2(\mathbb R^2)$; E1 from a Brownian family built from the white noise and Proposition 2.1; U1 by Gronwall's inequality; U3 by the second-moment computation $F=K+K\ast F$, $K^{\ast k}\le\varepsilon_k(T)K$; P from the convergence (Section 7) and E1.
