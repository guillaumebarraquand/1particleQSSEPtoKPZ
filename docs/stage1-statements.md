# Stage 1 (pilot): the statements, for comparison with the article

Prepared on 12 November 2026. **Nothing below is proved yet, except where marked "proved"**: each theorem ends with `sorry`. The definitions are complete (no `sorry`). `lake build` succeeds.

Scope of the pilot (`PROGRESS.md`): the analytic part of Section 4 and Lemma 6.3, with what they need from Sections 3 and 6.

## Deviations from the article, all foreseen in `PLAN.md`

1. **The Markov chain is replaced by its semigroup.** The chain $(R_v)$ of Section 4.1 is not formalized. Its generator $\mathcal R$ is a bounded operator on $\ell^\infty(\mathbb Z)$, and $\mathsf E_r[f(R_v)]$ is replaced by $(e^{v\mathcal R}f)(r)$. Consequences:
   * Lemma 4.1 bounds $\int_0^S(e^{v\mathcal R}\mathbf 1_{\lvert\cdot\rvert=1})(r)\ dv$ instead of $\mathsf E_r\big[\int_0^S\mathbf 1_{\lvert R_v\rvert=1}\ dv\big]$.
   * $u_n$ is *defined* as $\exp\big(t(\tfrac{nc_n}2\mathcal R+\tfrac{n\lambda_n}2\mathbf 1_{\lvert r\rvert=1})\big)\mathbf 1$, which the article obtains from (4.4) by the Feynman–Kac formula. The expectation (4.4) and the Feynman–Kac formula are not formalized. This is the route of `PLAN.md`, Section 3, row "Section 4".
2. **Support of $\kappa$.** The article says "$\kappa$ is supported in $[-2,2]$". The Lean statement is the precise form used later: $\kappa(x)=0$ for $\lvert x\rvert\ge2$, including at $\pm2$, which is what gives $k_m(\pm2m)=0$. It holds because $\kappa=\rho*\rho$ with $\rho=0$ outside $[-1,1]$.
3. **(6.6)** is stated, but the convergence $b_m\to\int\kappa=1$, from which the article deduces it, is not. The bounds will be proved directly: $b_m\ge2\kappa(0)/m$ for small $m$, and $b_m\ge\delta\kappa(0)/2$ when $m\delta\ge1$, where $\kappa\ge\kappa(0)/2$ on $[-\delta,\delta]$.
4. **Integrability.** In Lemma 4.1, the integrability of $v\mapsto(e^{v\mathcal R}\mathbf 1_{\lvert\cdot\rvert=1})(r)$ is part of the conclusion, so that the bound cannot hold for the degenerate reason that Lean's integral of a non-integrable function is $0$ (the lesson of the Stage 0 read-back).
5. **Not stated:** the inequality $0\le\sinh\theta-\theta\le\frac{\theta^3}6\cosh\theta$ of Section 3.1 (not used in the pilot), and the remark after Lemma 6.3 on uniqueness of the bounded solution of the Poisson equation (not used).

## Section 3.1 (`QSSEPtoKPZ/TiltedField/Constants.lean`)

Definitions, for real $n$: $\theta_n=n^{-1/4}$, $c_n=\cosh\theta_n$, $\lambda_n=2(\cosh\theta_n-1)$, $a_n=n^{1/2}\lambda_n$ (equation (3.1)).

* `sq_le_two_mul_cosh_sub_one`: for $\theta\ge0$, $\theta^2\le2(\cosh\theta-1)\le\theta^2\cosh\theta$.
* `constants_bounds`, **(3.2)**: for $n\ge1$, $n^{-1/2}\le\lambda_n\le c_nn^{-1/2}$ and $1\le a_n\le c_n\le\cosh1<2$.

## The operator $\mathcal R$ (`QSSEPtoKPZ/SecondMoments/Generator.lean`)

Definitions, complete and proved:

* `chainGen`: for any $g:\mathbb Z\to\mathbb R$, $\mathcal Rg(r)=2[g(r+1)+g(r-1)-2g(r)]+2\cdot\mathbf 1_{\lvert r\rvert=1}[g(0)-g(r)]$, equation (3.24).
* `chainOp`: the same formula as a bounded linear operator on $\ell^\infty(\mathbb Z)$, with $\lVert\mathcal R\rVert\le12$ (proved).
* `chainPi`: $\pi(r)=1+\mathbf 1_{r=0}$, equation (4.1).
* `defectInd`: the function $\mathbf 1_{\lvert r\rvert=1}$, as an element of $\ell^\infty(\mathbb Z)$.

## Lemma 4.1 (`QSSEPtoKPZ/SecondMoments/OccupationTime.lean`)

* `chainGen_max_abs_one`, **(4.3)**: $\mathcal Rf_1=2\cdot\mathbf 1_{\lvert r\rvert=1}$ for $f_1(r)=\max(\lvert r\rvert,1)$.
* `chainGen_sq`, **(4.3)**: $\mathcal Rf_2=4-2\cdot\mathbf 1_{\lvert r\rvert=1}$ for $f_2(r)=r^2$.
* `occupationTime_le`, **Lemma 4.1, (4.2)**: for $S\ge0$ and $r\in\mathbb Z$, the function $v\mapsto(e^{v\mathcal R}\mathbf 1_{\lvert\cdot\rvert=1})(r)$ is integrable on $[0,S]$, and

$$\int_0^S\big(e^{v\mathcal R}\mathbf 1_{\lvert\cdot\rvert=1}\big)(r)\ dv\le\min\Big(S,\ \frac14+\sqrt S\Big)\le\frac54\sqrt S.$$

## Lemma 4.2 (`QSSEPtoKPZ/SecondMoments/FeynmanKac.lean`)

Definitions: $M$ is the multiplication by $\mathbf 1_{\lvert r\rvert=1}$ on $\ell^\infty(\mathbb Z)$; $A_n=\frac{nc_n}2\mathcal R+\frac{n\lambda_n}2M$ (`generatorU`); and

$$u_n(t)=e^{tA_n}\mathbf 1\in\ell^\infty(\mathbb Z),\qquad t\in\mathbb R\qquad(\texttt{uN}).$$

* `uN_neg`, **Lemma 4.2 (1)**: $u_n(t,-r)=u_n(t,r)$.
* `uN_zero`, **(4.5)**, initial condition: $u_n(0,\cdot)=\mathbf 1$.
* `hasDerivAt_uN_apply`, **(4.5)**: for all $t$ and $r$,

$$\partial_tu_n(t,r)=\frac{nc_n}2\mathcal Ru_n(t,\cdot)(r)+\frac{n\lambda_n}2\mathbf 1_{\lvert r\rvert=1}u_n(t,r).$$

* `uN_regularity`, **Lemma 4.2 (1)**: $t\mapsto u_n(t,\cdot)$ is $C^1$ from $\mathbb R$ to $\ell^\infty(\mathbb Z)$ with derivative $A_nu_n(t,\cdot)$, and for every $T$ there is $C$ with $\lvert u_n(t,r)\rvert\le C$ and $\lvert\partial_tu_n(t,r)\rvert\le C$ for $t\in[0,T]$, $r\in\mathbb Z$.
* `uN_bounds`, **(4.6)**: for $n\ge1$, $t\ge0$, $r\in\mathbb Z$: $1\le u_n(t,r)\le2^{1+16t}$.
* `uN_le_one_add_sqrt`, **(4.6)**: for $n\ge1$, $0\le t\le\frac1{16}$, $r\in\mathbb Z$: $u_n(t,r)\le1+4\sqrt t$.

## Section 6: the mollifier and $k_m$ (`QSSEPtoKPZ/Replacement/Mollifier.lean`)

The function $\rho$ is a parameter. `IsMollifier ρ` means: $\rho$ is $C^\infty$, even, nonnegative, $\rho(x)=0$ for $\lvert x\rvert>1$, and $\int\rho=1$. Definitions: $\kappa=\rho*\rho$ (`kappa`); $b_m=\frac1m\sum_{r\in\mathbb Z}\pi(r)\kappa(r/m)$ and $k_m(r)=\kappa(r/m)/(mb_m)$ (`bM`, `kM`, equation (6.4)).

* `kappa_even_nonneg_smooth`: $\kappa$ is even, nonnegative and $C^\infty$.
* `kappa_support_integral`: $\kappa(x)=0$ for $\lvert x\rvert\ge2$, and $\int\kappa=1$.
* `kappa_le_kappa_zero`: $\kappa(x)\le\kappa(0)$ for all $x$, $\kappa(0)=\int\rho^2$, and $\kappa(0)>0$.
* `kM_props`: for $m\ge1$, $k_m$ is even, nonnegative, and $k_m(r)=0$ when $\lvert r\rvert\ge2m$.
* `tsum_chainPi_mul_kM`, **(6.5)**: for $m\ge1$, the series $\sum_r\pi(r)k_m(r)$ is summable and equals $1$.
* `bM_bounds`, **(6.6)**: there are constants $c>0$ and $C$ with $c\le b_m\le C$ for all $m\ge1$.

## Lemma 6.3 (`QSSEPtoKPZ/Replacement/Poisson.lean`)

Definition: $g_m$ is defined on $\mathbb N$ by the recursion (6.7), $g_m(0)=k_m(0)/4$, $g_m(1)=0$, $g_m(r+2)=g_m(r+1)+\frac12\sum_{u\ge r+2}k_m(u)$, and extended to $\mathbb Z$ by $g_m(r)=g_m(\lvert r\rvert)$ (`gM`). All the statements below assume `IsMollifier ρ` and $m\ge1$.

* `gM_spec`, **(6.7) as printed**: $g_m$ is even, $g_m(0)=k_m(0)/4$, $g_m(1)=0$, and $g_m(r+1)=g_m(r)+\frac12\sum_{u>r}k_m(u)$ for $r\ge1$.
* `chainGen_gM`, **(6.8)**: $\mathcal Rg_m(r)=\frac12\mathbf 1_{\lvert r\rvert=1}-k_m(r)$ for all $r\in\mathbb Z$.
* `gM_nonneg_le`: $0\le g_m(r)\le\frac m2$ for all $r$.
* `abs_gM_succ_sub_le`: $\lvert g_m(r+1)-g_m(r)\rvert\le\frac14$ for all $r$.
* `gM_add_one_eq_sub_one`: $g_m(r+1)=g_m(r-1)$ when $\lvert r\rvert\ge2m$.
* `exists_gM_zero_le`: there is $C$, depending only on $\rho$, with $g_m(0)\le C/m$ for all $m\ge1$.

## Numerical test of the statements

Run on 12 November 2026, on a lattice of $121$ sites, and with $\rho$ the standard bump function $\rho(x)\propto e^{-1/(1-x^2)}$. All statements above were checked:

* the two identities (4.3), for $\lvert r\rvert\le9$;
* Lemma 4.1 for $S\in\lbrace0.05,0.5,1,3,10,30\rbrace$: the occupation time is at most $3.76$ at $S=30$, against the bound $5.73$;
* Lemma 4.2 and (3.2) for $n\in\lbrace1,10,100\rbrace$ and $t\in\lbrace0.01,\tfrac1{16},0.5,2\rbrace$;
* (6.8), (6.5) and all the bounds of Lemma 6.3 for $m\in\lbrace1,2,3,5,8\rbrace$; $mg_m(0)$ stays between $0.10$ and $0.16$.

No discrepancy with the article was found.
