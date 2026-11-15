# Stage 2: the statements, for comparison with the article

Prepared on 12 November 2026 (task T0 of `docs/stage2-design.md`). **Nothing below is proved**: each theorem ends with `sorry`. The definitions are complete (no `sorry`). `lake build` succeeds; the only warnings `declaration uses 'sorry'` are those of the 27 statements below and the existing ones (`main_theorem`, the companion statements, `Challenge.lean`). No frozen file was changed.

Scope: the results of Sections 2, 3, Proposition 4.3 and Section 6, for $L=\infty$ (decision D7). Equation numbers are those of the article of 11 November 2026 (read from its `.aux` file).

## How to read the statements

* **Probability space.** Every probabilistic statement is made for an arbitrary probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration $\mathcal F_t$, $t\ge0$ (no usual conditions), a family $B=(B_{x,j})$, $x\in\mathbb Z$, $j\in\lbrace0,1\rbrace$, of independent $(\mathcal F_t)$-Brownian motions (`IsBrownianFamily`), and a wave function $\psi$ on $\mathbb Z$ driven by $W^{(x)}=(B_{x,0}+iB_{x,1})/\sqrt2$ (`IsWaveFunction ⊤`, the frozen definition of Stage 0). $P(t,x)=\lvert\psi_t(x)\rvert^2$ (`density`).
* **Martingales and brackets** (decisions D1, D2; definitions in `Martingales/Defs.lean` and `Martingales/Covariation.lean`). "$M$ is a continuous square-integrable martingale on $[0,T]$" (`IsCL2Mart`) means: almost surely $t\mapsto M_t$ is continuous on $[0,T]$; $M_t\in L^2$ for $t\in[0,T]$; and $\mathbb E[M_t\mid\mathcal F_s]=M_s$ almost surely for $0\le s\le t\le T$. "$\langle M\rangle=A$ on $[0,T]$" (`HasBracket`) means moreover: $A_t$ is integrable, almost surely $A$ is continuous and nondecreasing on $[0,T]$ with $A_0=0$, and $M^2-A$ is a martingale in the same sense. "$\langle M,N\rangle=A$" (`HasCovariation`) means: $M$ and $N$ are as above, $A_t$ is integrable, almost surely $A$ is continuous and of bounded variation on $[0,T]$ with $A_0=0$, and $MN-A$ is a martingale. The bounded variation makes $A$ unique. No general quadratic variation is defined: every bracket is an explicit time integral.
* **Filtration of Sections 3 to 6.** $\mathcal F^n_t=\mathcal F_{nt/2}$ (`filtN`).
* **No statement can hold because of a convention of Lean.** In Lean a non-convergent series has sum $0$, the integral of a non-integrable function is $0$, and the expectation of a non-measurable function in $[0,\infty]$ is a lower integral. Each statement therefore also asserts, as part of its conclusion, the convergence of its series, the integrability of its integrands and the measurability of its suprema. In Sections 3 to 6 this mostly takes the form "almost surely, $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$": since $\mathfrak z_n\ge0$, all other series of these sections have terms bounded by a constant times $\mathfrak z_n(t,x)$ (bounded test functions, and $\mathfrak z_n(t,x+1)\le\mathcal W_n(t)$), so this one conjunct makes them all genuine.
* **Constants.** "A constant $C$ depending only on $\rho$" is written: there is $C$ such that for every probability space, every Brownian family, every wave function, and all $n,m,T,\phi$, the inequality holds (decision D8).
* **The norm $\lVert\phi\rVert_{1,3}$** enters through a hypothesis $\lVert\phi\rVert_{1,3}\le C$, and the inequality is claimed with $C$ in place of the norm, for every such $C$ (decision D6). This is equivalent to the article's form.
* **Times.** Real time $t$; statements only concern $t\ge0$ (in $[0,T]$ when $T$ is given).

## Deviations from the article

Decisions of `docs/stage2-design.md` (all eight accepted by the author on 12 November 2026), as applied:

1. **D1, D2.** "Martingale" and "bracket" are understood as above, with respect to the filtration of the article ($\mathcal F_t$, or $\mathcal F^n_t$), without usual conditions, up to null sets.
2. **D3. No stochastic integral in the statements.** $J(x)$ of (2.3) is the limit in probability of left-point Riemann sums (the convention of the frozen definition `IsWaveFunction`). The last terms of (2.7), (2.8), the martingale $N_n^f$ of (3.21)-(3.22) and $N_n$ of (6.12) are described as "the remainder of the identity is a continuous square-integrable martingale with the following bracket", the bracket being the one of the article's stochastic integral, computed with (2.5) or (3.11). The rescaled currents $\mathsf J_n$ of (3.10), their brackets (3.11) and the representation (3.17) are not stated.
3. **D4. Stopping times** in Proposition 4.3 are bounded stopping times of $\mathcal F^n$ augmented by the null sets (`nullAug`): slightly more stopping times than those of $\mathcal F^n$. The $\sigma$-algebra $\mathcal F^n_\tau$ is the one of this augmented filtration. Item (1) is also stated separately for deterministic times, with $\mathcal F^n_t$ itself.
4. **D5. Lemma 6.4**: the remainder $\mathsf R_n$ is given by "there exists" with its bound (6.14) (and joint measurability), not by the explicit formula (6.16); likewise $\langle N_n\rangle=\int q$ with the bound (6.15) on $q$.
5. **D6.** $C_b^{1,3}([0,T]\times\mathbb R)$ is `IsC13` (definition below), with an explicit time derivative, one-sided at $0$ and $T$.
6. **D7.** $L=\infty$ only: Proposition 2.2 is not stated for finite $L$.
7. **D8.** Proposition 6.2 in $\varepsilon$-$\delta$ form (equivalent to $\lim_{\varepsilon\to0}\limsup_{n\to\infty}=0$); constants "depending only on $\rho$" quantified before the probability space.

Other deviations:

8. **$p_t$ is defined analytically**: $p_t=e^{t\Delta}\delta_0$, the exponential of the bounded operator $\Delta$ on $\ell^\infty(\mathbb Z)$ applied to $\mathbf 1_{x=0}$ (as $u_n$ in Stage 1). The random walk is not formalized.
9. **The measure $\mathcal Z_n(t)$ of (3.5)** is defined as a measure (`tiltedMeasure`), and $\lVert(\varphi\mu)\ast \rho_\varepsilon\rVert_2^2$ is defined for any measure $\mu$ (`smoothedNormSq`), as $\int_{\mathbb R}\big(\int\varphi(x)\rho_\varepsilon(y-x)\mu(dx)\big)^2dy$. Propositions 6.1 and 6.2 are stated with these, as in the article.
10. **Hypotheses kept although not needed.** (3.20) holds for every $f$ (symmetry is not used) and (3.23) for every $g$ (evenness is not used); the statements keep the article's hypotheses.
11. **"$C^1$ in the time variable"** (Lemmas 2.3 and 3.2) is read as: for each space point, $t\mapsto f_t$ has a derivative on $[0,T]$ (one-sided at $0$ and $T$), continuous on $[0,T]$. Symmetry of $f_t$ is assumed for $t\in[0,T]$ only.
12. **Proposition 6.2**: the probability of the event $\lbrace\sup_{t\le T}\lvert\dots\rvert>\eta\rbrace$ is the outer probability (the event is not claimed measurable). A bound on the outer probability is stronger than the article's.
13. **Prop 4.3 (3)**: $\langle\mathcal W_n\rangle_{\tau+s}-\langle\mathcal W_n\rangle_\tau$ is written $a_n\int_\tau^{\tau+s}\mathcal E_n(r)dr$, by (3.16).
14. **(3.16)** is stated together with $\mathcal W_n(0)=1$ almost surely (recalled at the beginning of Section 4.2).
15. **Added statements** not numbered in the article: $\kappa_\varepsilon=\rho_\varepsilon\ast \rho_\varepsilon$ and $b_m\to1$ (both asserted in the text of Section 6), and (6.11) is stated for a realization $\omega$ and a time $t$ at which $\sum_x\mathfrak z_n(t,x)$ converges.
16. **`HasCovariation`** is in a new file `Martingales/Covariation.lean` (`Martingales/Defs.lean` was already merged and is not changed). Compared with the design, it also requires $A$ integrable, continuous, of bounded variation, with $A_0=0$. The bounded variation was added after the independent audit: without it, $A$ would be determined only up to a continuous martingale (for instance $M=N=0$ and $A$ a Brownian motion would satisfy the definition).

## Section 2

### Definitions

* `lap` (`WaveFunction/Defs.lean`): $\Delta f(x)=f(x+1)+f(x-1)-2f(x)$ on $\mathbb Z$.
* `inclGen`, **(2.6)**: $\mathcal Qf(x_1,x_2)=(\Delta_1+\Delta_2)f(x_1,x_2)+\mathbf 1_{\lvert x_1-x_2\rvert=1}\big[f(x_1,x_1)+f(x_2,x_2)-2f(x_1,x_2)\big]$.
* `lapOp`, `delta0`, `rwKernel` (`WaveFunction/Kernel.lean`): $\Delta$ as a bounded operator on $\ell^\infty(\mathbb Z)$ (norm at most $4$), $\delta_0=\mathbf 1_{x=0}$, and $p_t(x)=(e^{t\Delta}\delta_0)(x)$.

### Statements

* `moment_bound`, **Proposition 2.1, (2.2)** (`WaveFunction/MomentBound.lean`): for $a\ge0$, $T$ and $k\in\mathbb N$, the function $\omega\mapsto\sup_{t\in[0,T]}\lVert\psi_t\rVert_a^2$ (with values in $[0,\infty]$, $\lVert\psi\rVert_a^2=\sum_xe^{a\lvert x\rvert}\lvert\psi(x)\rvert^2$) is almost everywhere measurable, and
$$\mathbb E\Big[\sup_{t\in[0,T]}\lVert\psi_t\rVert_a^{2k}\Big]<\infty.$$

* `prop_2_2`, **Proposition 2.2, (2.3)-(2.5) and $\mathbb EP(t,x)=p_t(x)$** (`WaveFunction/EquationP.lean`): there are real processes $J(x)$, $x\in\mathbb Z$, such that
  * (2.3): for all $x$ and $t\ge0$, $2\ \mathrm{Im}\sum_{k<m}\overline{\psi_{t_k}(x)}\psi_{t_k}(x+1)\big(W^{(x)}(t_{k+1})-W^{(x)}(t_k)\big)$, $t_k=kt/m$, converges in probability to $J_t(x)$ as $m\to\infty$;
  * (2.4): almost surely, for all $t\ge0$ and $x$, $s\mapsto\Delta P(s,x)$ and $s\mapsto P(s,x)P(s,x+1)$ are integrable on $[0,t]$ and
$$P(t,x)=\mathbf 1_{x=0}+\int_0^t\Delta P(s,x)ds+J_t(x-1)-J_t(x);$$
  * (2.5): for every $x$ and $T$, $J(x)$ is a continuous square-integrable martingale on $[0,T]$ with $\langle J(x)\rangle_t=2\int_0^tP(s,x)P(s,x+1)ds$; and for $x\ne y$, $\langle J(x),J(y)\rangle=0$ on $[0,T]$;
  * for all $t\ge0$ and $x$, $P(t,x)$ is integrable and $\mathbb E[P(t,x)]=p_t(x)$.

* `hasSum_density`, **conservation of the mass** (stated after Lemma 2.3; `WaveFunction/Mass.lean`): almost surely, for all $t\ge0$, $\sum_{x\in\mathbb Z}P(t,x)=1$ (convergent series).

* `lemma_2_3_linear`, **Lemma 2.3 (1), (2.7)** (`WaveFunction/Linear.lean`). Let $T>0$, $a\ge0$, and $\alpha_t(x)$, $C^1$ in $t\in[0,T]$ with derivative $\partial_t\alpha$, such that $\lvert\alpha_t(x)\rvert+\lvert\partial_t\alpha_t(x)\rvert\le Ce^{a\lvert x\rvert}$ for $t\in[0,T]$. Then:
  * almost surely, for all $t\in[0,T]$, the series $\sum_x\lvert\alpha_t(x)\rvert P(t,x)$, $\sum_x\lvert(\partial_t\alpha_t+\Delta\alpha_t)(x)\rvert P(t,x)$ and $\sum_x(\alpha_t(x+1)-\alpha_t(x))^2P(t,x)P(t,x+1)$ converge, and the drift $s\mapsto\sum_x(\partial_s\alpha_s+\Delta\alpha_s)(x)P(s,x)$ and the bracket density below are integrable on $[0,T]$;
  * the process
$$M_t=\sum_x\alpha_t(x)P(t,x)-\alpha_0(0)-\int_0^t\sum_x(\partial_s\alpha_s+\Delta\alpha_s)(x)P(s,x)ds$$
  (the last term of (2.7)) is a continuous square-integrable martingale on $[0,T]$ with
$$\langle M\rangle_t=\int_0^t\sum_x2\big(\alpha_s(x+1)-\alpha_s(x)\big)^2P(s,x)P(s,x+1)ds .$$

* `lemma_2_3_quadratic`, **Lemma 2.3 (2), (2.8)** (`WaveFunction/Quadratic.lean`). Let $T>0$, $a\ge0$, and $f_t(x_1,x_2)$, symmetric in $(x_1,x_2)$ for $t\in[0,T]$, $C^1$ in $t\in[0,T]$ with derivative $\partial_tf$, such that $\lvert f_t(x_1,x_2)\rvert+\lvert\partial_tf_t(x_1,x_2)\rvert\le Ce^{a(\lvert x_1\rvert+\lvert x_2\rvert)}$. Write $D_s(x)=\sum_{x'}\big(f_s(x+1,x')-f_s(x,x')\big)P(s,x')$ (`quadDiff`). Then:
  * almost surely, for all $t\in[0,T]$: the double series of $\lvert f_t(x_1,x_2)\rvert P(t,x_1)P(t,x_2)$ and of $\lvert(\partial_tf_t+\mathcal Qf_t)(x_1,x_2)\rvert P(t,x_1)P(t,x_2)$ over $\mathbb Z^2$ converge; for each $x$ the series $\sum_{x'}\lvert f_t(x+1,x')-f_t(x,x')\rvert P(t,x')$ converges; the series $\sum_x(2D_t(x))^2P(t,x)P(t,x+1)$ converges; and the drift and the bracket density below are integrable on $[0,T]$;
  * the process
$$M_t=\sum_{x_1,x_2}f_t(x_1,x_2)P(t,x_1)P(t,x_2)-f_0(0,0)-\int_0^t\sum_{x_1,x_2}(\partial_sf_s+\mathcal Qf_s)(x_1,x_2)P(s,x_1)P(s,x_2)ds$$
  (the last term of (2.8), $2\int_0^t\sum_xD_s(x)dJ_s(x)$) is a continuous square-integrable martingale on $[0,T]$ with
$$\langle M\rangle_t=\int_0^t\sum_x2\big(2D_s(x)\big)^2P(s,x)P(s,x+1)ds .$$

## Section 3

### Definitions (`TiltedField/Defs.lean`; the constants $\theta_n,c_n,\lambda_n,a_n$ of (3.1) are those of Stage 1)

* `zN`, **(3.3)**: $\mathfrak z_n(t,x)=\exp(\theta_nx-\frac{n\lambda_n}2t)P(\frac{nt}2,x)$. The position (3.4) is the frozen `rescaledPosition`: $y_n(t,x)=n^{-1/2}(x-n^{3/4}t)$.
* `tiltedMeasure`, **(3.5)**: the measure $\mathcal Z_n(t)=\sum_x\mathfrak z_n(t,x)\delta_{y_n(t,x)}$; `pairZ`: $\mathcal Z_n(t;\varphi)=\sum_x\mathfrak z_n(t,x)\varphi(y_n(t,x))$.
* `WN`, **(3.6)**: $\mathcal W_n(t)=\mathcal Z_n(t;1)$.
* `varrhoN`, **(3.8)**: $\varrho_n(t)=\exp\big((\frac{n\lambda_n}2-\frac{n^{1/2}}2-\frac1{24})t\big)$.
* `EN`, **(3.12)**: $\mathcal E_n(t;\varphi)=n^{1/2}\sum_x\mathfrak z_n(t,x)\mathfrak z_n(t,x+1)\varphi(y_n(t,x))\varphi(y_n(t,x+1))$, and $\mathcal E_n(t)=\mathcal E_n(t;1)$.
* `IsC13 T φ φt C` (Section 3.2): for $t\in[0,T]$, $\phi_t$ is $C^3$ on $\mathbb R$; $\varphi_t$ (`φt`) is the derivative of $t\mapsto\phi_t(x)$ on $[0,T]$; $\partial_t\phi$ and $\partial_x^k\phi$, $k=0,1,2,3$, are continuous on $[0,T]\times\mathbb R$; and $\lVert\phi\rVert_\infty+\lVert\partial_t\phi\rVert_\infty+\sum_{k=1}^3\lVert\partial_x^k\phi\rVert_\infty\le C$ (suprema over $[0,T]\times\mathbb R$). A function $\varphi\in C^3_b(\mathbb R)$ is seen as `IsC13 1 (fun _ => φ) (fun _ _ => 0) C`.
* `AN`, **(3.13)**: $\mathcal A_n\varphi(y)=\frac n2\big[e^{\theta_n}\varphi(y+n^{-1/2})+e^{-\theta_n}\varphi(y-n^{-1/2})-2c_n\varphi(y)\big]-n^{1/4}\varphi'(y)$.
* `MN`, **(3.14)**: $M_n^\phi(t)=\mathcal Z_n(t;\phi_t)-\phi_0(0)-\int_0^t\mathcal Z_n(s;\partial_s\phi_s+\mathcal A_n\phi_s)ds$.
* `QNdens`, `QN`, **(3.15)**: $Q_n(t)=n\int_0^t\sum_x\mathfrak z_n(s,x)\mathfrak z_n(s,x+1)\big[e^{\theta_n/2}\phi_s(y_n(s,x+1))-e^{-\theta_n/2}\phi_s(y_n(s,x))\big]^2ds$.
* `filtN`: $\mathcal F^n_t=\mathcal F_{nt/2}$.
* `tiltedInclGen`, **(3.19)**: $\mathcal Q^\theta f$, transcribed term by term.
* `pairZ2` (Section 3.3): $\mathcal Z_n^{\otimes2}(t;f)=\sum_{x_1,x_2}\mathfrak z_n(t,x_1)\mathfrak z_n(t,x_2)f(x_1,x_2)$.
* `bracketDensN2`: $4n\sum_x\mathfrak z_n(s,x)\mathfrak z_n(s,x+1)\big[\sum_{x'}\mathfrak z_n(s,x')\big(e^{\theta_n/2}f_s(x+1,x')-e^{-\theta_n/2}f_s(x,x')\big)\big]^2$, the density of the bracket of $N_n^f$ of (3.22), by (3.11).

### Statements without probability (`TiltedField/Identities.lean`)

* `sinh_sub_self_bounds`, **the inequality of Section 3.1** (before (3.2)): for $\theta\ge0$, $0\le\sinh\theta-\theta\le\frac{\theta^3}6\cosh\theta$.
* `rescaledMeasure_eq`, **(3.8)**: for $n\ge1$, every realization $\omega$ and every $t$, the measure $\mathcal Z_n(t)$ of Theorem 1.2 (`rescaledMeasure ⊤ n P t`, equation (1.15)) equals $\varrho_n(t)$ times the measure of (3.5).
* `varrhoN_bounds`, **(3.9)**: for $n\ge1$ and $t\ge0$, $1\le\varrho_n(t)\le\exp(tn^{-1/2})$.
* `prop_3_1_generator`, **Proposition 3.1 (1)**: for $n\ge1$ and $\varphi\in C^3_b(\mathbb R)$ with $\lVert\varphi\rVert_{1,3}\le C$, for all $y$, $\lvert\mathcal A_n\varphi(y)-\frac12\varphi''(y)\rvert\le n^{-1/4}C$.
* `identity_uv`, **(3.18)**: $(e^{\theta/2}u-e^{-\theta/2}v)^2=2(\cosh\theta-1)uv+(u-v)(e^\theta u-e^{-\theta}v)$ for all real $u,v,\theta$.
* `tilt_identity`, **(3.20)**: for symmetric $f$ and $w_\theta(x_1,x_2)=e^{\theta(x_1+x_2)}$, $\mathcal Q(w_\theta f)=w_\theta\big[\mathcal Q^\theta f+4(\cosh\theta-1)f+2(\cosh\theta-1)\mathbf 1_{\lvert x_1-x_2\rvert=1}f\big]$.
* `tiltedInclGen_diff`, **(3.23)**: if $f(x_1,x_2)=g(x_2-x_1)$ with $g$ even, then $\mathcal Q^\theta f(x_1,x_2)=\cosh\theta\ \mathcal Rg(x_2-x_1)$, with $\mathcal R$ of (3.24) (`chainGen`, Stage 1).

### Probabilistic statements

* `WN_moments`, **(3.7)** (`TiltedField/Martingales.lean`): for $n\ge1$, $T$ and $k\in\mathbb N$: almost surely $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$; $\sup_{t\in[0,T]}\mathcal W_n(t)$ is almost everywhere measurable; and $\mathbb E\big[\sup_{t\in[0,T]}\mathcal W_n(t)^k\big]<\infty$.

* `prop_3_1`, **Proposition 3.1, (3.14), (3.15), items (2) and (3)**: let $n\ge1$, $T>0$, and $\phi$ with `IsC13 T φ φt C`. Then
  * almost surely, $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$, and $s\mapsto\mathcal Z_n(s;\partial_s\phi_s+\mathcal A_n\phi_s)$, the integrand of (3.15), $s\mapsto\mathcal E_n(s;\phi_s)$ and $s\mapsto\mathcal E_n(s)$ are integrable on $[0,T]$;
  * $M_n^\phi$ is a continuous square-integrable $(\mathcal F^n_t)$-martingale on $[0,T]$ with $\langle M_n^\phi\rangle_t=Q_n(t)$, the right-hand side of (3.15);
  * (2): almost surely, for $0\le s\le t\le T$, $\langle M_n^\phi\rangle_t-\langle M_n^\phi\rangle_s\le2C^2a_n\int_s^t\mathcal E_n(r)dr$ (that is, $2C^2(\langle\mathcal W_n\rangle_t-\langle\mathcal W_n\rangle_s)$ by (3.16));
  * (3): almost surely, for $t\in[0,T]$, $\big\lvert\langle M_n^\phi\rangle_t-a_n\int_0^t\mathcal E_n(s;\phi_s)ds\big\rvert\le5n^{-1/4}C^2\int_0^t\mathcal E_n(s)ds$.

  Item (1) is `prop_3_1_generator`.

* `hasBracket_WN`, **(3.16)**: for $n\ge1$ and $T>0$: almost surely $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$ and $\mathcal E_n$ is integrable on $[0,T]$; $\mathcal W_n$ is a continuous square-integrable $(\mathcal F^n_t)$-martingale on $[0,T]$ with $\langle\mathcal W_n\rangle_t=a_n\int_0^t\mathcal E_n(s)ds$; and $\mathcal W_n(0)=1$ almost surely.

* `lemma_3_2`, **Lemma 3.2, (3.21), (3.22)** (`TiltedField/Quadratic.lean`): let $n\ge1$, $T>0$, and $f_t(x_1,x_2)$, symmetric for $t\in[0,T]$, $C^1$ in $t\in[0,T]$, with $\lvert f_t\rvert\le C$ and $\lvert\partial_tf_t\rvert\le C$. Then almost surely $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$ and the drift and bracket density below are integrable on $[0,T]$; and
$$N_n^f(t)=\mathcal Z_n^{\otimes2}(t;f_t)-f_0(0,0)-\int_0^t\mathcal Z_n^{\otimes2}\Big(s;\partial_sf_s+\frac n2\mathcal Q^{\theta_n}f_s+\frac{n\lambda_n}2\mathbf 1_{\lvert x_1-x_2\rvert=1}f_s\Big)ds$$
is a continuous square-integrable $(\mathcal F^n_t)$-martingale on $[0,T]$ with
$$\langle N_n^f\rangle_t=\int_0^t4n\sum_x\mathfrak z_n(s,x)\mathfrak z_n(s,x+1)\Big[\sum_{x'}\mathfrak z_n(s,x')\big(e^{\theta_n/2}f_s(x+1,x')-e^{-\theta_n/2}f_s(x,x')\big)\Big]^2ds,$$
the bracket of the stochastic integral (3.22), computed with (3.11).

## Proposition 4.3 (`SecondMoments/TotalMass.lean`)

$u_n$ is `uN` of Stage 1: $u_n(t)=\exp\big(t(\frac{nc_n}2\mathcal R+\frac{n\lambda_n}2\mathbf 1_{\lvert r\rvert=1})\big)\mathbf 1$.

* `prop_4_3_condSecondMoment`, **Proposition 4.3 (1), (4.7)**, deterministic times: for $n\ge1$ and $s,t\ge0$, almost surely $\sum_x\mathfrak z_n(r,x)$ converges for all $r\ge0$ and the family $\mathfrak z_n(t,x_1)\mathfrak z_n(t,x_2)u_n(s,x_2-x_1)$ is summable over $\mathbb Z^2$; $\mathcal W_n(t+s)^2$ is integrable; and almost surely
$$\mathbb E\big[\mathcal W_n(t+s)^2\mid\mathcal F^n_t\big]=\sum_{x_1,x_2}\mathfrak z_n(t,x_1)\mathfrak z_n(t,x_2)u_n(s,x_2-x_1).$$

* `prop_4_3_condSecondMoment_stopping`, **Proposition 4.3 (1)**, last sentence: the same with $t$ replaced by a bounded stopping time $\tau$ (decision D4) and $\mathcal F^n_t$ by $\mathcal F^n_\tau$, for $s\ge0$.

* `prop_4_3_bounds`, **Proposition 4.3 (2), (4.8)**: for $n\ge1$ and $t\ge0$: almost surely $\sum_x\mathfrak z_n(r,x)$ converges for all $r\ge0$ and $\mathcal E_n$ is integrable on $[0,t]$; $\sup_{s\in[0,t]}\mathcal W_n(s)^2$ is almost everywhere measurable and $\mathbb E\big[\sup_{s\in[0,t]}\mathcal W_n(s)^2\big]\le2^{3+16t}$; $\int_0^t\mathcal E_n(s)ds$ is integrable and $\mathbb E\big[\int_0^t\mathcal E_n(s)ds\big]\le2^{1+16t}$.

* `prop_4_3_increment`, **Proposition 4.3 (3), (4.9)**: for $n\ge1$, a bounded stopping time $\tau$ (decision D4) and $s\in[0,\frac1{16}]$: almost surely $\sum_x\mathfrak z_n(r,x)$ converges for all $r\ge0$ and $\mathcal E_n$ is integrable on $[\tau,\tau+s]$; $a_n\int_\tau^{\tau+s}\mathcal E_n(r)dr$ is integrable; and almost surely
$$\mathbb E\Big[a_n\int_\tau^{\tau+s}\mathcal E_n(r)dr\ \Big\vert\ \mathcal F^n_\tau\Big]\le4\sqrt s\ \mathcal W_n(\tau)^2 .$$

## Section 6

$\rho$ is a parameter with `IsMollifier ρ` (Stage 1: $C^\infty$, even, nonnegative, zero outside $[-1,1]$, $\int\rho=1$); $\kappa=\rho\ast \rho$, $b_m$, $k_m$, $g_m$ are those of Stage 1.

### Definitions (`Replacement/CorrectorDefs.lean`)

* `rhoEps`: $\rho_\varepsilon(x)=\rho(x/\varepsilon)/\varepsilon$; `kappaEps`: $\kappa_\varepsilon(x)=\kappa(x/\varepsilon)/\varepsilon$.
* `smoothedNormSq ν φ ρ ε`: $\lVert(\varphi\nu)\ast \rho_\varepsilon\rVert_2^2=\int_{\mathbb R}\big(\int_{\mathbb R}\varphi(x)\rho_\varepsilon(y-x)\nu(dx)\big)^2dy$, for a measure $\nu$ on $\mathbb R$.
* `FN`, **(6.9)**: $\mathsf F_n(t)=\frac2{c_nn^{1/2}}\sum_{x_1,x_2}\mathfrak z_n(t,x_1)\mathfrak z_n(t,x_2)g_m(x_2-x_1)\phi_t(y_n(t,x_1))\phi_t(y_n(t,x_2))$.
* `BN`, **(6.10)**: $\mathsf B_n(t;\varphi)=n^{1/2}\sum_{x_1,x_2}\mathfrak z_n(t,x_1)\mathfrak z_n(t,x_2)k_m(x_2-x_1)\varphi(y_n(t,x_1))\varphi(y_n(t,x_2))$.

### Statements

* `kappaEps_eq_conv` (`Replacement/L2Bound.lean`; text at the beginning of Section 6): for $\varepsilon>0$, $\kappa_\varepsilon=\rho_\varepsilon\ast \rho_\varepsilon$.
* `smoothedNormSq_eq`, **(6.1)**: for a finite measure $\nu$ on $\mathbb R$, $\varphi$ bounded continuous and $\varepsilon>0$: $y\mapsto\big((\varphi\nu)\ast \rho_\varepsilon(y)\big)^2$ is integrable, $(x,y)\mapsto\varphi(x)\varphi(y)\kappa_\varepsilon(x-y)$ is $\nu\otimes\nu$-integrable, and $\lVert(\varphi\nu)\ast \rho_\varepsilon\rVert_2^2=\int\int\varphi(x)\varphi(y)\kappa_\varepsilon(x-y)\nu(dx)\nu(dy)$.
* `BN_eq`, **(6.11)**: for $n\ge1$, an integer $m\ge1$, $\varphi$ bounded continuous, and a realization $\omega$ and a time $t$ at which $\sum_x\mathfrak z_n(t,x)$ converges, $\mathsf B_n(t;\varphi)=b_m^{-1}\lVert(\varphi\mathcal Z_n(t))\ast \rho_{mn^{-1/2}}\rVert_2^2$.
* `tendsto_bM` (`Replacement/ReplacementLemma.lean`; Section 6.1, before (6.6)): $b_m\to1$ as $m\to\infty$.
* `lemma_6_4`, **Lemma 6.4, (6.12)-(6.15)** (`Replacement/Corrector.lean`): there is $K$, depending only on $\rho$, such that for every probability space, Brownian family and wave function, all $n\ge1$, integers $m\ge1$, $T>0$ and $\phi$ with `IsC13 T φ φt C`, there are jointly measurable processes $\mathsf R_n$ and $q$ with:
  * almost surely, $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$, and $s\mapsto\mathcal E_n(s;\phi_s)$, $s\mapsto\mathsf B_n(s;\phi_s)$, $\mathsf R_n$ and $q$ are integrable on $[0,T]$;
  * almost surely, for all $t\in[0,T]$:
$$\lvert\mathsf F_n(t)\rvert\le\frac m{n^{1/2}}C^2\mathcal W_n(t)^2\quad(6.13),\qquad\lvert\mathsf R_n(t)\rvert\le K\Big(\frac m{n^{1/2}}+\frac1{n^{1/4}}+\frac1m\Big)C^2\mathcal W_n(t)^2\quad(6.14),$$
$$0\le q(t)\le K\Big(\frac{m^2}n+\frac1{n^{1/2}}\Big)C^4\mathcal W_n(t)^2\ a_n\mathcal E_n(t)\quad(6.15,\ \text{since }d\langle\mathcal W_n\rangle_t=a_n\mathcal E_n(t)dt);$$
  * (6.12): $N_n(t)=\mathsf F_n(t)-\mathsf F_n(0)-\int_0^t\big(\mathcal E_n(s;\phi_s)-\mathsf B_n(s;\phi_s)+\mathsf R_n(s)\big)ds$ is a continuous square-integrable $(\mathcal F^n_t)$-martingale on $[0,T]$ with $\langle N_n\rangle_t=\int_0^tq(s)ds$;
  * if $\phi\equiv1$: $\mathsf R_n\equiv0$, and almost surely $\mathsf F_n(t)\ge0$ for $t\in[0,T]$.
* `prop_6_1`, **Proposition 6.1, (6.2)** (`Replacement/L2Bound.lean`): there is $C$, depending only on $\rho$, such that for every probability space, Brownian family and wave function, all $n\ge1$, integers $m\ge1$ and $T>0$: almost surely the series $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$ (added after the audit, so that the bound cannot hold because of a junk value); almost surely $t\mapsto\lVert\mathcal Z_n(t)\ast \rho_{mn^{-1/2}}\rVert_2^2$ is almost everywhere measurable on $[0,T]$, $\omega\mapsto\int_0^T\lVert\mathcal Z_n(t)\ast \rho_{mn^{-1/2}}\rVert_2^2dt$ is almost everywhere measurable (both integrals in $[0,\infty]$), and
$$\mathbb E\Big[\int_0^T\lVert\mathcal Z_n(t)\ast \rho_{mn^{-1/2}}\rVert_2^2dt\Big]\le C\ 2^{16T}.$$
* `prop_6_2`, **Proposition 6.2, (6.3)** (`Replacement/ReplacementLemma.lean`): let $T>0$ and $\phi$ with `IsC13 T φ φt C`. Then
  * for all $n\ge1$ and $\varepsilon>0$, almost surely $\sum_x\mathfrak z_n(t,x)$ converges for all $t\ge0$, and $s\mapsto\mathcal E_n(s;\phi_s)$ and $s\mapsto\lVert(\phi_s\mathcal Z_n(s))\ast \rho_\varepsilon\rVert_2^2$ are integrable on $[0,T]$;
  * for all $\eta>0$ and $\delta>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ there is $N$ with, for all $n\ge N$,
$$\mathbb P\Big(\exists t\in[0,T]:\ \Big\lvert\int_0^t\big(\mathcal E_n(s;\phi_s)-\lVert(\phi_s\mathcal Z_n(s))\ast \rho_\varepsilon\rVert_2^2\big)ds\Big\rvert>\eta\Big)\le\delta .$$
  This is equivalent to $\lim_{\varepsilon\to0}\limsup_{n\to\infty}\mathbb P(\dots)=0$ for every $\eta>0$.

## Checks

* Numerical (12 November 2026, Python, scripts in the session's scratch folder, not in the repository): (3.18) at 1,000 random points; the inequality on $\sinh\theta-\theta$ for $\theta\in[0,5]$; (3.20) and (3.23) for random symmetric $f$ and even $g$ on $\lvert x_i\rvert\le4$, $\theta\in\lbrace0,0.3,-0.7,1.1\rbrace$; (3.8) (the exponents) and (3.9) for $n$ from $1$ to $10^8$ and $t\le30$; Proposition 3.1 (1) for $\varphi(y)=\sin(ay)$; the pointwise inequalities behind Proposition 3.1 (2), (3); (6.1) and (6.11) for a bump function $\rho$, $n=37$, $m=3$, 13 atoms (agreement to $10^{-11}$). No discrepancy.
* By hand: the proofs of Proposition 3.1 (1)-(3), of the bounds (6.13)-(6.15) of Lemma 6.4 (including the constants of the article's proof), of (6.11), and the derivation of Lemma 3.2 from Lemma 2.3 (2) through (3.20) were re-derived. No error was found.
* Not checked: that the statements are provable in Lean as written (the proofs are the next tasks).

## Remarks on the article

No error was found. Minor points, none of which changes a statement:

* (3.20) holds for every $f:\mathbb Z^2\to\mathbb R$, and (3.23) for every $g:\mathbb Z\to\mathbb R$; symmetry and evenness are not used.
* Lemma 3.2 does not repeat $n\ge1$ (fixed at the beginning of Section 3.1).
* The bracket of $N_n^f$ is not written in Lemma 3.2; it follows from (3.22) and (3.11) and is the one used in the proof of Lemma 6.4.
