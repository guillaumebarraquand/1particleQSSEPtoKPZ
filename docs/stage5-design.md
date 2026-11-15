# Stage 5: design (packages L, M: finite systems, companions, assembly)

Written on 13 November 2026 by a design agent (Opus 5.5), at the request of the main session. **Nothing in this document is proved.** It fixes the Lean statements, the generic infrastructure and the order of work for Stage 5, the last stage of `PLAN.md`: Section 8 of the article (Lemma 8.2, Proposition 8.1), the end of the proof of Theorem 1.2 for arbitrary $L_n$, and the companion statements E1, U1, E2, P. The Lean signatures of Sections 2 and 3 marked "elaborated" were checked to elaborate against Mathlib v4.35.0 and the library at commit `91918fb` (with `sorry` proofs) in a scratch file outside the repository (Section 7); they are a starting point for the task T0‴/I0‴, not frozen text.

By the author's instruction of 13 November 2026 ("Once stage 4 is completed, start Stage 5 and progress as much as possible without waiting for my approval"), the statements of Section 2 will be written and proved without waiting for his approval, and reviewed afterwards. They are therefore written to be read literally: nothing is weakened with respect to the article, and every departure is listed (1.3, Section 5).

Equation numbers are those of the article (version of 11 November 2026, SHA-256 `3547cb86…`, 1713 lines, unchanged on 13 November 2026: checked), read from its `.aux` file: Proposition 2.1 with (2.1), (2.2); (3.8), (3.9); Lemma 5.2 with (5.1); Proposition 8.1; Lemma 8.2 with (8.1); (8.2) (Duhamel); (8.3) (total variation decomposition).

Readers: Section 1 is for the author. Sections 2 to 4 are for the agents who will write the Lean code. Section 5 lists the decisions (taken as recommended by the main session, to be reviewed by the author afterwards), Section 6 the risks and the estimate, Section 7 the final checks of the checkpoint.

---

## 1. Mathematical overview

### 1.1 What Stage 5 proves, and what Stage 4 leaves

The checkpoint of `PLAN.md` is "`main_theorem`, companions E1, U1, E2, W, U3, comparator run". Stage 4 leaves (branch `work-integ4`, being merged when this was written):

* `main_theorem_top`: the frozen `main_theorem` with $L_k=\infty$ for every $k$, on arbitrary probability spaces;
* `IsMildSolution.nonneg_of_isWaveFunction`: if some probability space carries a Brownian family and a wave function on $\mathbb Z$, every mild solution of (1.13) is nonnegative;
* the companions W and U3, proved as library copies `IsWalshIntegral.ae_eq_lib`, `IsWalshIntegral.isometry_lib`, `isMildSolution_unique_lib` (statements identical to `Companions.lean`, checked with `pp.all`);
* `walshProc_exists_cont_rect` (task G9): for a white noise $\xi$, the process $t\mapsto\xi((0,t]\times(a,b])$ has a version with continuous paths on $[0,T]$. Stage 5 uses it to build Brownian motions (E1).

**How the frozen `main_theorem` quantifies.** For each $k$ it takes an arbitrary probability space $\Omega_k$ with a filtration $\mathcal F_k$, a family $B_k=(B_{k,i})_{i\in\mathbb Z\times\lbrace0,1\rbrace}$ of independent Brownian motions **indexed by all of** $\mathbb Z\times\lbrace0,1\rbrace$ (not only by the bonds of $\Lambda_{L_k}$), and a process $\psi_k$ satisfying `IsWaveFunction (L k)`; on another arbitrary space, a white noise and a solution $Z$ of (1.13). It asserts versions and convergence in distribution. So what must be proved for finite $L_k$ is a statement about *every* realization of the finite system, not about one coupling chosen by us. The article says "since the law of $\mathcal Z_n$ only depends on the law of $P^{L_n}$, we may assume that the QSSEP on $\Lambda_{L_n}$ is coupled to the QSSEP on $\mathbb Z$". In Lean this transfer of laws is not needed: since $\Omega_k$ already carries the whole family $B_k$, we **construct the wave function on $\mathbb Z$ on $\Omega_k$ itself**, driven by $B_k$ (strong existence, Proposition 2.1, by Picard iteration), and compare it with the given $\psi_k$ on the same space (decision D2‴). This is the coupling of Section 8, realized on the given space.

**Is E1 needed by `main_theorem`?** No. `main_theorem` needs *strong* existence on a given space (above), not the companion E1 (existence of *some* space carrying a Brownian family and a wave function). E1 is a companion (non-vacuity) and an input of P: `IsMildSolution.nonneg` is `nonneg_of_isWaveFunction` applied to E1 with $L=\infty$ (elaborated: a one-line proof). E1 itself needs a probability space carrying a Brownian family indexed by $\mathbb Z\times\lbrace0,1\rbrace$; Mathlib defines Brownian motion but does not construct it. Stage 5 builds it from a white noise, so E1 rests on E2.

**U1** (`isWaveFunction_unique`) is pathwise uniqueness for every $L$: two wave functions driven by the same Brownian family, for the same filtration, are indistinguishable. It is the uniqueness half of Proposition 2.1 ($L=\infty$) and of "linear SDE in finite dimension" ($L<\infty$). It is not used by `main_theorem` either (the coupling compares the given $\psi_k$ with the constructed one through Lemma 8.2, which holds for any two solutions), but the identification lemmas it needs are shared with Lemma 8.2.

**E2** (`exists_isWhiteNoise`) is not used by the main theorem; it is a companion, and the base of E1.

| Article | Content | In Lean (Section 2) |
|---|---|---|
| Prop 2.1, existence | strong existence of the wave function on any space with a Brownian family | `prop_2_1_existence` (every $L\in\mathbb N\cup\lbrace\infty\rbrace$) |
| Prop 2.1, uniqueness; Section 1.3 | pathwise uniqueness | `isWaveFunction_unique_lib` (U1) |
| Lemma 8.2, (8.1) | $\mathbb E\sup_{s\le S}(\sum_{\Lambda_L}\lvert P^\infty-P^L\rvert)^2\le4(8+S)\int_0^S\mathsf P(\lvert X_s\rvert\ge L)ds$ | `lemma_8_2` |
| Prop 8.1 | $\sup_{t\le T}\lVert\mathsf Z_n^{L_n}(t)-\mathsf Z_n(t)\rVert_{TV}\to0$ in probability | `prop_8_1` |
| Proof of Thm 1.2 (end of Section 8) | all $L_n$ | `main_theorem_lib` (= `main_theorem`) |
| companions | E1, E2, P | `exists_isWaveFunction_lib`, `exists_isWhiteNoise_lib`, `IsMildSolution.nonneg_lib` |

### 1.2 How the Lean proof goes

**(a) Strong existence: Picard iteration** (`PLAN.md`, row "Proposition 2.1 (b)"). Let $\mathcal F^a$ be the null augmentation of $\mathcal F$ (library `nullAug`, Stage 2); $B$ is a Brownian family for it. For $L\in\mathbb N\cup\lbrace\infty\rbrace$ and an initial vector $\psi_0\in\ell^2$ supported in $\Lambda_L$, define $\psi^{(0)}_t=\psi_0$ and, for $x\in\Lambda_L$,
$$\psi^{(m+1)}_t(x)=\psi_0(x)+\mathrm i\int_0^t\psi^{(m)}_s(x+1)\,dW^{(x)}_s+\mathrm i\int_0^t\psi^{(m)}_s(x-1)\,d\overline W{}^{(x-1)}_s-\frac{D_L(x,x)}2\int_0^t\psi^{(m)}_s(x)\,ds,$$
$\psi^{(m+1)}_t(x)=0$ outside $\Lambda_L$, with the library's Itô integral `stochInt` against the real Brownian motions (real and imaginary parts, coefficients `waveDiffRe`, `waveDiffIm` of Stage 2). By Doob's inequality for each coordinate, Itô's isometry and Cauchy–Schwarz for the drift, summed over $x$ (Tonelli),
$$\mathbb E\sup_{s\le t}\lVert\psi^{(m+1)}_s-\psi^{(m)}_s\rVert^2\le(16+2T)\int_0^t\mathbb E\sup_{u\le s}\lVert\psi^{(m)}_u-\psi^{(m-1)}_u\rVert^2ds\qquad(t\le T),$$
since $\sum_{x,j}\lVert\sigma_{x,j}(\psi)\rVert^2\le2\lVert\psi\rVert^2$ (the article's computation with $a=0$). Hence $\sum_m(\mathbb E\sup_{s\le T}\lVert\psi^{(m+1)}-\psi^{(m)}\rVert^2)^{1/2}<\infty$, the iterates converge almost surely uniformly on $[0,T]$ in $\ell^2$, the limit is continuous and adapted, and passing to the limit in $L^2$ in the stochastic integrals gives the equation. Continuity in $\ell^2$ of each iterate: $\mathbb E\sum_x\sup_{t\le T}\lvert M_t(x)\rvert^2<\infty$ for the martingale parts, so the partial sums over $\lvert x\rvert\le K$ converge uniformly on $[0,T]$. Paths are made continuous for *every* $\omega$ by changing them on a measurable null set, which the augmented filtration allows. The result is an Itô representation (`IsWaveIto`, 3.2) from which `IsWaveFunction` follows (left-point Riemann sums converge to `stochInt`, Stage 2). The same construction with $\psi_0=e_y$ gives the columns $U_te_y$ of the unitary matrix of Definition 1.1, used for Lemma 8.2.

Why the null augmentation: the frozen `IsWaveFunction` asks adaptedness to the given filtration without completion, and a limit which is continuous only almost surely cannot always be made continuous for every $\omega$ without leaving $\mathcal F_t$. The constructed solution is a wave function for $\mathcal F^a$; this is enough everywhere: `main_theorem_top` is applied with the filtrations $\mathcal F_k^a$ (the given $\psi_k$, $B_k$ satisfy the hypotheses for $\mathcal F_k^a$ by the library lemmas `IsWaveFunction.nullAug`, `IsBrownianFamily.nullAug`), and E1 chooses its filtration (an augmented one).

**(b) Identification of a given solution, every $L$.** Stage 2 proved, for $L=\infty$, that a wave function has a version with continuous paths and $\lVert\psi_t\rVert=1$ whose coordinates are Itô processes (`IsUnitWave`, `isItoProcessUpTo_re/im`). For finite $L$ the same argument is repeated with $D_L$ instead of $2$ (new files, Stage 2 files untouched): identification up to the stopping times $\tau_R\wedge N$ (`isItoProcessUpTo_of_riemann`, Stage 2), then conservation of $\lVert\psi_t\rVert^2=\sum_{x\in\Lambda_L}\lvert\psi_t(x)\rvert^2$ by the product rule on the *finite* box (no infinite sums), hence $\tau_R=N$ for $R>1$.

**(c) The pairing identity on a box** (the heart of Section 8 in Lean). For $L$ finite, let $a$ be an Itô solution of the equation on $\Lambda_L$ and $b$ either another one, or the restriction to $\Lambda_L$ of an Itô solution $\psi$ on $\mathbb Z$. The product rule for $\overline{a(x)}b(x)$, summed over $x\in\Lambda_L$, gives:

* if $b$ solves the equation on $\Lambda_L$: $\langle a_t,b_t\rangle=\langle a_0,b_0\rangle$. The martingale terms cancel bond by bond (on the bond $(x,x+1)$ the coefficients are $\tfrac{\mathrm i}{\sqrt2}(\overline{a(x)}b(x+1)+\overline{a(x+1)}b(x))$ from the products and $-\tfrac{\mathrm i}{\sqrt2}(\cdots)$ from the conjugates, and similarly on the second Brownian motion of the bond), and the drift is $\sum_y\overline{a(y)}b(y)\,(-\tfrac{D(y)}2-\tfrac{D(y)}2+D(y))=0$, the bracket terms contributing $D_L(y)$ at each site;
* if $b=\psi\vert_{\Lambda_L}$: $\psi(\pm L)$ has the extra noise of the outer bonds and drift coefficient $-1$ instead of $-\tfrac12$, and
$$\langle a_t,\psi_t\rangle_{\Lambda_L}=\langle a_0,\psi_0\rangle_{\Lambda_L}-\tfrac12\int_0^t\big(\overline{a_s(L)}\psi_s(L)+\overline{a_s(-L)}\psi_s(-L)\big)ds+\int_0^t\overline{a_s(L)}\,\mathrm i\psi_s(L+1)\,dW^{(L)}_s+\int_0^t\overline{a_s(-L)}\,\mathrm i\psi_s(-L-1)\,d\overline W{}^{(-L-1)}_s.$$
This is the article's Duhamel formula (8.2) read coordinatewise: $(U_t^\ast\phi_t)(y)=\langle U_te_y,\phi_t\rangle$.

With $a=b$: conservation of the norm on finite boxes (1.2 (b)). With $a=U_\cdot e_y$, $b=U_\cdot e_z$: the columns of $U_t$ are orthonormal, so $U_t$ is unitary and its rows are unit vectors too (finite-dimensional linear algebra).

**(d) Lemma 8.2 as in the article** (decision D1‴). Let $\phi=\psi^\infty\vert_{\Lambda_L}$, $\delta=\phi-\psi^L$. By (c), $\langle U_te_y,\psi^L_t\rangle=\delta_{y0}$ and $\langle U_te_y,\phi_t\rangle=\delta_{y0}+V_t(y)+N_t(y)$ with $V$, $N$ the drift and martingale terms above; by Parseval in $\mathbb C^{\Lambda_L}$ (orthonormal basis $(U_te_y)_y$), $\lVert\delta_t\rVert=\lVert N_t+V_t\rVert\le\lVert N_t\rVert+\lVert V_t\rVert$. Doob's inequality for each $N(y)$ (library: $\mathbb E\sup I^2\le4\,\mathbb E\int\sum h^2$), the rows of $U$ being unit vectors, gives $\mathbb E\sup_{s\le S}\lVert N_s\rVert^2\le4\int_0^S\mathbb E[P^\infty(u,L+1)+P^\infty(u,-L-1)]du$; Cauchy–Schwarz gives $\sup_{s\le S}\lVert V_s\rVert^2\le\tfrac S2\int_0^S(P^\infty(u,L)+P^\infty(u,-L))du$; then $\mathbb E[P^\infty(u,x)]=p_u(x)$ (Proposition 2.2, Stage 2) and $\sum_{\Lambda_L}\lvert P^\infty-P^L\rvert\le2\lVert\delta\rVert$. The constant $4(8+S)$ of the article is obtained exactly. The matrix SDE (1.6) for $U$ is never written: $U$ enters only through its columns, which are wave functions with initial conditions $e_y$.

`PLAN.md` proposed instead the product rule for $\lVert\delta_t\rVert^2$ directly, with a weaker constant. That route gives $\lVert\delta_t\rVert^2=M_t+\int_0^t(P^\infty(L+1)+P^\infty(-L-1)-\mathrm{Re}(\overline{\delta(L)}\psi^\infty(L)+\overline{\delta(-L)}\psi^\infty(-L)))ds$, whose drift involves $\lvert\psi^\infty(\pm L)\rvert=P^{1/2}$; it yields a bound of order $\int_0^S p_u(\pm L)^{1/2}du$ instead of $\int_0^Sp_u$, enough for Proposition 8.1 but not Lemma 8.2 as printed. Since the statements are proved before the author reviews them, the faithful constant is recommended; the extra cost (columns of $U$, Parseval) is about 0.5k lines, the pairing identity (c) being needed in both routes.

**(e) Proposition 8.1 as in the article.** A quantitative internal lemma (`prop81_bound`): for $n\ge1$, $L\ge1$, $T,\varepsilon>0$ with $n^{3/4}T<L$, and $r=\min\lbrace1,L/(nT)\rbrace$, $\ell=n^{-1/2}(L-n^{3/4}T)$,
$$\mathbb P^\ast\Big(\sup_{t\le T}\sum_x\lvert\mathfrak z^L_n(t,x)-\mathfrak z_n(t,x)\rvert>\varepsilon\Big)\le\frac{16}{\varepsilon^2}nT\Big(8+\frac{nT}2\Big)e^{2\theta_nL-rL/3}+\frac{4e^{2T}}{\varepsilon\cosh\ell},$$
from (8.3), Lemma 8.2 with $S=nT/2$, Chebyshev, the bound $\mathsf P(\lvert X_s\rvert\ge L)\le2e^{-rL/3}$ for $s\le nT/2$, and Lemma 5.2 ((5.1), Stage 3). The exponential moment $\sum_xe^{rx}p_s(x)=e^{2s(\cosh r-1)}$ is obtained from Lemma 2.3 (1) (Stage 2) with $\alpha_t(x)=e^{rx-2t(\cosh r-1)}$ ($\partial_t\alpha+\Delta\alpha=0$, so the linear functional is a martingale with mean $1$) and $\mathbb E P=p$. Proposition 8.1 follows by the article's asymptotics ($2\theta_n\le r_n/6$ and $r_nL_n\ge\min\lbrace n^{3/4},n^{1/2}/T\rbrace$ eventually), and by $\lVert\mu-\nu\rVert_{TV}\le\sum_x\lvert a_x-b_x\rvert$ for two atomic measures $\sum_xa_x\delta_{y_x}$, $\sum_xb_x\delta_{y_x}$ (Mathlib's Hahn decomposition and `IsHahnDecomposition.etvDist_eq`).

**(f) The end of the proof of Theorem 1.2** (`main_theorem_lib`). On each $\Omega_k$: $\psi^\infty_k$ is the given $\psi_k$ if $L_k=\infty$, the solution on $\mathbb Z$ constructed in (a) otherwise. `main_theorem_top` (for the filtrations $\mathcal F^a_k$) gives versions $Y_k$ of $\varrho_{n_k}\mathsf Z_{n_k}$ (the QSSEP on $\mathbb Z$) converging in distribution to the version $\mathcal Z$ on $\Omega'$. For finite $L_k$ the version $X_k$ of $\mathcal Z_{n_k}=\varrho_{n_k}\mathsf Z^{L_k}_{n_k}$ is explicit (a finite sum of atoms with continuous weights and positions), and $X_k=Y_k$ when $L_k=\infty$. For every bounded continuous $f$ and $t\le T$,
$$\Big\lvert\int f\,dX_k(t)-\int f\,dY_k(t)\Big\rvert\le\lVert f\rVert_\infty\,\varrho_{n_k}(t)\sum_x\lvert\mathfrak z^{L_k}_{n_k}(t,x)-\mathfrak z_{n_k}(t,x)\rvert,$$
which tends to $0$ in probability uniformly in $t$ and $f$ by `prop81_bound` (the deterministic bound tends to $0$ by the hypothesis $L_k/n_k^{3/4}\to\infty$; it is $0$ when $L_k=\infty$) and $\varrho_n(t)\le e^{tn^{-1/2}}$ ((3.9)). The article's Billingsley Theorem 3.1 is replaced by a generic lemma (`tendstoInDistribution_of_close`, decision D6‴) on $C([0,T],\mathcal M_+)$ with **varying** probability spaces, proved with an explicit metric built from the Stage 3 embedding of $\mathcal M_+$ into $\mathbb R^{\mathbb N}$ (bump functions $f_j$, $\lVert f_j\rVert_\infty\le1$):
$$d(\gamma,\gamma')=\sup_{t\le T}\sum_j\min\big(2^{-j},\lvert\gamma(t)(f_j)-\gamma'(t)(f_j)\rvert\big),$$
which induces the topology of $C([0,T],\mathcal M_+)$ (`ContinuousMap.isEmbedding_postcomp` and Mathlib's countable-product metric `PiCountable`) and is bounded by the uniform weak closeness above; then the proof of Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` (bounded Lipschitz test functions) is repeated with `dist` and with one space per $k$.

**(g) E2: an isonormal Gaussian process** (decision D4‴). On $\Omega_0=\mathbb R^I$ with the product of standard Gaussians (`Measure.infinitePi`), where $(e_i)_{i\in I}$ is a Hilbert basis of $H=L^2(\mathbb R^2)$ ($I$ countable since $H$ is separable; `exists_hilbertBasis`, `Lp.SecondCountableTopology`), $W(h)=\sum_i\langle e_i,h\rangle\xi_i$ in $L^2(\Omega_0)$ is a linear isometry; each $W(h)$ is $N(0,\lVert h\rVert^2)$ (characteristic functions of the partial sums, limit in $L^2$), hence $W$ is a Gaussian process (`IsGaussianProcess`: every linear combination is a.s. $W$ of the combination) with covariance $\langle h,g\rangle$. Then $S(t,x)=W(\mathbf 1_{(0,t]\times(0,x]})$ for $x\ge0$ (and $-W(\mathbf 1_{(0,t]\times(x,0]})$ for $x<0$), $\mathcal G_t=\sigma(S(r,x):r\le t,x\in\mathbb R)$. The rectangle masses are a.s. $W(\mathbf 1_{(s,t]\times(a,b]})$; the three clauses of `IsWhiteNoise` follow from Mathlib's `IsGaussianProcess.iIndepFun_of_covariance_eq_zero` and `IsGaussianProcess.indepFun_of_covariance_eq_zero` (orthogonal indicators), the latter giving independence of the whole future rectangle process from the whole past process, i.e. of the generated $\sigma$-algebras.

**(h) E1: Brownian family from the white noise** (decision D3‴). With the unit intervals $I_{(x,j)}=(2x+j,2x+j+1]$, $B_{(x,j)}(t)$ is the continuous version of $\xi((0,t]\times I_{(x,j)})$ (G9 on $[0,N]$ for each $N$, glued: the versions agree a.s. on the rationals, hence on $[0,N]$), with the filtration $\mathcal G^a$. Gaussian increments with variance $t-s$, independence across $(x,j)$ (consecutive unit intervals, `indep` clause of the white noise) and independence of $\mathcal G^a_s$ (`indep_past`, null sets added on both sides) give `IsBrownianFamily`. Then E1 for every $L$: Picard (a) on this space, for the filtration $\mathcal G^{aa}$ (or with an idempotence lemma for `nullAug`).

**(i) U1** (decision D8‴). Take unit-norm Itô versions $\hat\psi,\hat\psi'$ (1.2 (b); Stage 2 for $L=\infty$). $F(t)=\mathbb E\lVert\hat\psi_t-\hat\psi'_t\rVert^2\le4$ satisfies, by the isometry and Cauchy–Schwarz, $F(t)\le(4+2T)\int_0^tF(s)ds$ on $[0,T]$; the library's Volterra lemma (Stage 4, kernel $(t-s)^{-1/2}\ge T^{-1/2}$) gives $F=0$; continuity gives indistinguishability. The hypothesis "probability measure" of U1 is not stated in `Companions.lean`; it follows from `IsBrownianFamily` (the increments have a Gaussian law), a small lemma.

### 1.3 Check of Section 8 and Section 2.1 of the article

Every step of Section 8 (lines 1412–1497) was re-derived. **No error was found.** Points checked, and points where the text is compressed:

1. Lemma 8.2, $d(U_s^\ast\phi_s)=U_s^\ast d\Upsilon_s$: with $dU^\ast=-\mathrm iU^\ast dH-\tfrac12U^\ast D\,dt$, the Itô correction is $U^\ast(dH)^2\phi=U^\ast D\phi\,dt$, which cancels the two drifts $-\tfrac12U^\ast D\phi$; the cross term $U^\ast dH\,d\Upsilon$ vanishes because $\Upsilon$ is driven by $W^{(L)},W^{(-L-1)}$, which do not appear in $H$. Correct.
2. Doob and Itô: $\mathbb E\sup_{s\le S}\lVert\int U^\ast d\Upsilon^{\mathrm{mart}}\rVert^2\le4\int_0^S\mathbb E[P^\infty(u,L+1)+P^\infty(u,-L-1)]du$ uses $\lVert U^\ast e_{\pm L}\rVert=1$ and $L\ne-L-1$; the finite-variation part gives $\tfrac S2\int(P^\infty(u,L)+P^\infty(u,-L))du$; $(a+b)^2\le2a^2+2b^2$ gives $8\int(\cdots)+S\int(\cdots)\le(8+S)\int\mathsf P(\lvert X_u\rvert\ge L)du$. Correct. The last step uses $\lVert\phi_s\rVert\le1$, i.e. $\sum_xP^\infty(s,x)=1$ (Lemma 2.3), and $\lVert\psi^L_s\rVert=1$ ($U_s$ unitary).
3. (8.3): the weights $e^{\theta_nx-n\lambda_nt/2}\le e^{\theta_nL_n}$ on $\Lambda_{L_n}$ ($\lambda_n\ge0$); outside $\Lambda_{L_n}$ the measure $\mathsf Z^{L_n}_n$ has no atoms. Correct (equal atoms' positions are not needed for the bound).
4. Chernoff bound: $\mathsf E e^{rX_s}=e^{2s(\cosh r-1)}$, $\cosh r-1\le\frac23r^2$ on $[0,1]$ (the ratio $(\cosh r-1)/r^2$ increases, $\cosh1-1\approx0.543$), $nTr_n^2\le r_nL_n$. Correct; the second moment of the first term is $\le4nT(8+nT/2)\exp(2\theta_nL_n-r_nL_n/3)$ as printed.
5. $r_n/\theta_n=\min\lbrace n^{1/4},L_nn^{-3/4}/T\rbrace\to\infty$; $r_nL_n=\min\lbrace L_n,L_n^2/(nT)\rbrace\ge\min\lbrace n^{3/4},n^{1/2}/T\rbrace$ once $L_n\ge n^{3/4}$; the polynomial prefactor is beaten by $e^{-r_nL_n/6}$. Correct.
6. Second term: for $x\notin\Lambda_{L_n}$ and $t\le T$, $\lvert y_n(t,x)\rvert>\ell_n$ (for $x>L_n$: $y\ge n^{-1/2}(L_n+1-n^{3/4}T)$; for $x<-L_n$: $y\le-n^{-1/2}(L_n+1)$). Correct.
7. Proof of Theorem 1.2: "we may now assume that $L_n$ is finite for all $n$" (splitting the sequence into the indices with $L_n=\infty$ and the others, each subsequence converging to the same limit) and "since the law of $\mathcal Z_n$ only depends on the law of $P^{L_n}$, we may assume [the coupling]" — the second sentence uses that the finite system is a measurable function of its driving Brownian motions (strong uniqueness, so uniqueness in law) and enlarges the space with independent Brownian motions for the bonds outside $\Lambda_{L_n}$. Both are standard; in Lean neither is needed (1.1, 1.2 (f)): the frozen statement already provides the whole family $B_k$, and the two cases are treated together.
8. Billingsley's Theorem 3.1 and the bounded Lipschitz distance with $d\le\lVert\cdot\rVert_{TV}$: correct; in Lean replaced by 1.2 (f).
9. Section 2.1 (for E1, U1): Proposition 2.1 is quoted from Da Prato–Zabczyk; the Lean route (Picard, Gronwall) proves the existence and uniqueness of a continuous adapted $\ell^2$-valued solution directly (no weighted spaces $\ell^2_a$; the moment bound (2.2) was proved in Stage 2 for every solution). Nothing to correct.

Minor remarks (not errors): Proposition 8.1 indexes $L_n$ by the real parameter $n$; Lean states it for sequences $n_k\to\infty$, as the frozen theorem does (equivalent). In Lemma 8.2 "$\mathsf P(\lvert X_s\rvert\ge L)$" is $\sum_{\lvert x\rvert\ge L}p_s(x)$ with $p_s$ the library's `rwKernel` (approved in Stage 2 as the law of $X_s$).

---

## 2. The article's results in Lean

Conventions of Stages 2–4: arbitrary probability spaces in arbitrary universes, filtrations without the usual conditions, processes `ℝ → Ω → _`, probabilities of events not claimed measurable are outer probabilities, every series, integral and expectation that appears is asserted genuine. All of this section was elaborated (Section 7), and printed with `set_option pp.parens true`: every big operator ($\sum$, $\int$, $\sup$) that is followed by further terms is parenthesized. Proposed files: `QSSEPtoKPZ/FiniteSystems/Statements.lean` (2.1–2.3), `QSSEPtoKPZ/Assembly/MainTheorem.lean` (2.4), `QSSEPtoKPZ/FiniteSystems/Existence.lean`, `QSSEPtoKPZ/WhiteNoise/Existence.lean` (2.5). Statement list for the author: `docs/stage5-statements.md` (+ PDF), written by T0‴.

### 2.1 Definitions

```lean
/-- The measure `𝖹_n^L(t) = ∑_{x ∈ Λ_L} 𝔷_n(t,x) δ_{y_n(t,x)}` of Section 8, where
`𝔷_n(t,x) = exp(θ_n x - n λ_n t / 2) P(n t / 2, x)` is computed from `ψ` (`zN`, Stage 2). -/
def tiltedMeasureBox (L : ℕ∞) (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) : Measure ℝ :=
  Measure.sum fun x : box L =>
    ENNReal.ofReal (zN n ψ ω t x) • Measure.dirac (rescaledPosition n t x)

/-- `𝖯(|X_s| ≥ L) = ∑_{|x| ≥ L} p_s(x)`, `X` the continuous-time simple random walk. -/
def rwTail (s : ℝ) (L : ℕ) : ℝ := ∑' x : ℤ, if (L : ℤ) ≤ |x| then rwKernel s x else 0
```
`tiltedMeasureBox ⊤` is Stage 2's `tiltedMeasure` (the article's $\mathsf Z_n$); `tiltedMeasureBox L` with $\psi=\psi^L$ is the article's $\mathsf Z^L_n$ (same formula, sum over $\Lambda_L$). The total variation norm is Mathlib's `etvDist μ ν` ($=\lVert\mu-\nu\rVert_{TV}$ for finite measures, $=\infty$ if one of them is infinite, so that a bound on it also asserts finiteness; decision D5‴).

### 2.2 Proposition 2.1 (existence; elaborated)

```lean
theorem prop_2_1_existence (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞) :
    ∃ ψ : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveFunction L (nullAug μ 𝓕) B ψ μ
```
On any filtered space carrying a Brownian family indexed by $\mathbb Z\times\lbrace0,1\rbrace$, there is a wave function on $\Lambda_L$ driven by it, adapted to the filtration augmented by the null sets (the article works under the usual conditions, where the two filtrations coincide). For $L=\infty$ this is the existence half of Proposition 2.1; for $L<\infty$, Section 1.3 ("linear SDE in finite dimension"). The uniqueness half is U1 (2.5).

### 2.3 Lemma 8.2 and Proposition 8.1 (elaborated)

```lean
/-- **Lemma 8.2**, (8.1). -/
theorem lemma_8_2 [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {L : ℕ} (hL : 1 ≤ L) (hψL : IsWaveFunction L 𝓕 B ψL μ) {S : ℝ} (hS : 0 < S) :
    (∀ s, Summable fun x : ℤ => if (L : ℤ) ≤ |x| then rwKernel s x else 0) ∧
    IntervalIntegrable (fun s => rwTail s L) volume 0 S ∧
    AEMeasurable (fun ω => ⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x|) ^ 2)) μ ∧
    ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) S, ENNReal.ofReal
        ((∑ x ∈ Finset.Icc (-(L : ℤ)) L, |density ψ ω s x - density ψL ω s x|) ^ 2)) ∂μ ≤
      ENNReal.ofReal (4 * (8 + S) * ∫ s in (0 : ℝ)..S, rwTail s L)
```
Reading: $\psi$ (on $\mathbb Z$) and $\psi^L$ (on $\Lambda_L$, $L\ge1$) are driven by the same Brownian family for the same filtration — the article's coupling — and are otherwise arbitrary realizations. Then the series and the time integral on the right are genuine, the supremum is a random variable, and
$$\mathbb E\Big[\sup_{s\in[0,S]}\Big(\sum_{x\in\Lambda_L}\lvert P^\infty(s,x)-P^L(s,x)\rvert\Big)^2\Big]\le4(8+S)\int_0^S\mathsf P(\lvert X_s\rvert\ge L)\,ds.$$
The hypothesis `IsProbabilityMeasure μ` is implied by `hB` (it is kept for uniformity with Stages 2–4).

```lean
/-- **Proposition 8.1**. -/
theorem prop_8_1 (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    (L : ℕ → ℕ) (hL₁ : ∀ k, 1 ≤ L k)
    (hL : Tendsto (fun k => (L k : ℝ) / n k ^ (3 / 4 : ℝ)) atTop atTop)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (ψL : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ))
    (hψL : ∀ k, IsWaveFunction (L k) (𝓕 k) (B k) (ψL k) (μ k))
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k => μ k {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
        etvDist (tiltedMeasureBox (L k) (n k) (ψL k) ω t) (tiltedMeasure (n k) (ψ k) ω t)})
      atTop (𝓝 0)
```
Reading: $n_k\to\infty$, $n_k\ge1$, integers $L_k\ge1$ with $L_k/n_k^{3/4}\to\infty$; for each $k$, on one space, the two systems coupled as in the article. Then for all $T,\varepsilon>0$, $\mathbb P^\ast(\sup_{t\le T}\lVert\mathsf Z^{L_k}_{n_k}(t)-\mathsf Z_{n_k}(t)\rVert_{TV}>\varepsilon)\to0$. The article indexes by the real $n$; sequences are equivalent and match the frozen theorem.

### 2.4 Theorem 1.2 (elaborated)

`main_theorem_lib`: the frozen `main_theorem`, word for word (checked: the `pp.all` printouts of `main_theorem` and `main_theorem_lib`, without elision, are identical after renaming; and the kernel accepts each as a proof of the other's type, with the same two universe variables).

### 2.5 Companions (elaborated)

`exists_isWaveFunction_lib` (E1), `isWaveFunction_unique_lib` (U1), `exists_isWhiteNoise_lib` (E2), `IsMildSolution.nonneg_lib` (P): statements identical (`pp.all`, checked) to `Companions.lean`. P is proved in one line, elaborated:
```lean
theorem IsMildSolution.nonneg_lib … :=
  IsMildSolution.nonneg_of_isWaveFunction.{0} (exists_isWaveFunction_lib ⊤) hS hZ
```
(`nonneg_of_isWaveFunction` quantifies its hypothesis over a universe variable; E1 lives in `Type`.) W and U3 are Stage 4's `IsWalshIntegral.ae_eq_lib`, `IsWalshIntegral.isometry_lib`, `isMildSolution_unique_lib`.

---

## 3. Generic infrastructure and interfaces

### 3.1 What Mathlib v4.35.0 and the library have (checked)

* Library: `stochInt` for a countable Brownian family, adapted for every $\omega$, continuous a.s.; `lintegral_iSup_stochInt_sq_le` (Doob, constant 4), `lintegral_stochInt_sq` (isometry), linearity, `stochInt_congr`, `tendsto_lintegral_iSup_stochInt_sub`; `IsItoIntegrable` for bounded left-continuous adapted families (`isItoIntegrable_of_leftContinuous`) and closure under energy limits (`IsItoIntegrable.of_tendsto`); `IsItoProcessUpTo` with `.mul` (product rule, bounded on $[0,\tau]$), `.add`, `.const_mul`, `.finset_sum`, `.mono`; `isItoProcessUpTo_of_riemann` (identification from Riemann sums); `waveDiffRe`, `waveDiffIm`, `waveSites`, `tsum_waveDiffRe_sq`; `IsWaveFunction.exists_good` (every $L$), `IsGoodWave`, `IsUnitWave` and `isItoProcessUpTo_re/im` ($L=\infty$); `prop_2_2` ($\mathbb EP=p$, `rwKernel`), `lemma_2_3_linear`, `lemma_5_2`; `rescaledMeasure_eq` ($L=\infty$), `varrhoN_bounds`; `IsBrownianFamily.nullAug`, `IsWaveFunction.nullAug`, `IsWhiteNoise.nullAug`, `IsWhiteNoise.isProbabilityMeasure`; `tightEmb`, `isEmbedding_tightEmb`, `measurable_pathFiniteMeasure_iff_tightEmb` (Stage 3); `volterra_ae_eq_zero` (Stage 4); G9's `walshProc_exists_cont_rect` (branch `work-integ4`).
* Mathlib: `etvDist`, `exists_isHahnDecomposition`, `IsHahnDecomposition.etvDist_eq`; `PiCountable.dist` (not an instance); `ContinuousMap.isEmbedding_postcomp`, `ContinuousMap.piEquiv`; `MetrizableSpace C(X, Y)`; `tendsto_iff_forall_lipschitz_integral_tendsto` (portmanteau, pseudo-emetric); `exists_hilbertBasis`, `OrthogonalFamily.linearIsometry`, `Lp.SecondCountableTopology`; `Measure.infinitePi`; `charFun_gaussianReal`, `Measure.ext_of_charFun`, `iIndepFun_iff_charFun_pi`; `IsGaussianProcess`, `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`, `IsGaussianProcess.indepFun_of_covariance_eq_zero`, `iIndepFun.hasGaussianLaw`; `IsPreBrownianReal`/`IsBrownianReal` (definitions only: **no construction of Brownian motion, no Kolmogorov extension or continuity theorem**).

### 3.2 Itô form of the wave equation (elaborated)

```lean
/-- Itô form of the wave equation on `Λ_L` with initial condition `ψ0`. -/
structure IsWaveIto (L : ℕ∞) (𝓖 : Filtration ℝ≥0 mΩ) (B : ℤ × Fin 2 → ℝ → Ω → ℝ)
    (ψ0 : ℓ²(ℤ, ℂ)) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (μ : Measure Ω) : Prop where
  adapted : ∀ (t : ℝ≥0) (x : ℤ), Measurable[𝓖 t] fun ω => ψ t ω x
  continuous : ∀ ω, Continuous fun t : ℝ≥0 => ψ t ω
  support : ∀ ω (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ t ω x = 0
  init : ∀ ω, ψ 0 ω = ψ0
  re : ∀ x ∈ box L, ∀ N : ℝ≥0, IsItoProcessUpTo 𝓖 μ B (fun _ => N)
    (fun t ω => (ψ t ω x).re) (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).re)
    (waveDiffRe ψ x)
  im : ∀ x ∈ box L, ∀ N : ℝ≥0, IsItoProcessUpTo 𝓖 μ B (fun _ => N)
    (fun t ω => (ψ t ω x).im) (fun s ω => -((degree L x : ℝ) / 2) * (ψ s ω x).im)
    (waveDiffIm ψ x)

theorem exists_isWaveIto [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (L : ℕ∞)
    (ψ0 : ℓ²(ℤ, ℂ)) (hψ0 : ∀ x, x ∉ box L → ψ0 x = 0) :
    ∃ ψ : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveIto L (nullAug μ 𝓕) B ψ0 ψ μ ∧
      ∀ T : ℝ, ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖ψ t ω‖ ^ 2) ∂μ < ⊤
theorem IsWaveIto.isWaveFunction [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓖 B μ)
    (h : IsWaveIto L 𝓖 B waveInit ψ μ) : IsWaveFunction L 𝓖 B ψ μ
theorem IsWaveFunction.exists_unitIto [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    ∃ ψ' : ℝ → Ω → ℓ²(ℤ, ℂ), IsWaveIto L (QSSEPtoKPZ.nullAug μ 𝓕) B waveInit ψ' μ ∧
      (∀ ω (t : ℝ≥0), ‖ψ' t ω‖ = 1) ∧ ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω
```
Also (L1): `IsBrownianFamily.isProbabilityMeasure` (nonempty index); linearity of `waveDiffRe/Im` in $\psi$; $\sum_i$`waveDiffRe`$^2$ $+\sum_i$`waveDiffIm`$^2=\lvert\psi(x+1)\rvert^2+\lvert\psi(x-1)\rvert^2$; `waveStop` is a stopping time for any adapted process with continuous $\ell^2$ paths (generalizing `IsGoodWave.isStoppingTime_waveStop`). Note: inside `namespace IsWaveFunction`, write `QSSEPtoKPZ.nullAug` (otherwise `nullAug` resolves to the lemma `IsWaveFunction.nullAug`; met while elaborating).

### 3.3 Generic Itô additions (G11)

* (G11a) **Continuous adapted integrands with finite energy are Itô-integrable**: if each $h_i$ is adapted with continuous paths for every $\omega$, $s\mapsto\sum_ih_i(s)^2$ continuous, and $\mathbb E\int_0^T\sum_ih_i^2<\infty$ for every $T$, then `IsItoIntegrable 𝓖 μ h` (truncate $h\cdot\min(1,K/\lVert h\rVert)$, bounded left-continuous, dominated convergence, `of_tendsto`). Also: the sum over $x$ of Doob's inequality, $\mathbb E\sum_x\sup_{t\le T}I_t(h^x)^2\le4\,\mathbb E\int_0^T\sum_x\sum_ih^x_i(s)^2ds$ (Tonelli on $[0,\infty]$).
* (G11b) **Complex Itô processes**: pairs of real Itô processes up to $\tau$; product rule for $\bar zw$ (four applications of `IsItoProcessUpTo.mul`), finite sums; the formula
$$d(\bar zw)=\big(\bar z\,a^w+w\,\overline{a^z}+\textstyle\sum_i\overline{b^z_i}b^w_i\big)ds+\textstyle\sum_i(\bar z\,b^w_i+w\,\overline{b^z_i})\,dB_i$$
with complex coefficients, the real and imaginary parts being `IsItoProcessUpTo` statements.

### 3.4 Package L interfaces (elaborated unless said)

```lean
theorem IsWaveIto.inner_eq [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓖 B μ) {L : ℕ}
    (ha : IsWaveIto L 𝓖 B a0 a μ) (hb : IsWaveIto L 𝓖 B b0 b μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ⟪a t ω, b t ω⟫_ℂ = ⟪a0, b0⟫_ℂ

def boundaryCoef (L : ℕ) (a ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (i : ℤ × Fin 2) (s : ℝ) (ω : Ω) : ℂ :=
  if i = ((L : ℤ), 0) then conj (a s ω L) * (Complex.I * ψ s ω (L + 1)) / Real.sqrt 2
  else if i = ((L : ℤ), 1) then conj (a s ω L) * (-ψ s ω (L + 1)) / Real.sqrt 2
  else if i = (-(L : ℤ) - 1, 0) then conj (a s ω (-L)) * (Complex.I * ψ s ω (-L - 1)) / Real.sqrt 2
  else if i = (-(L : ℤ) - 1, 1) then conj (a s ω (-L)) * ψ s ω (-L - 1) / Real.sqrt 2
  else 0

theorem IsWaveIto.inner_restrict_eq [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓖 B μ)
    {L : ℕ} (hL : 1 ≤ L) (ha : IsWaveIto L 𝓖 B a0 a μ) (hψ : IsWaveIto ⊤ 𝓖 B ψ0 ψ μ)
    (hbd : ∀ ω (t : ℝ≥0), ‖a t ω‖ ≤ 1 ∧ ‖ψ t ω‖ ≤ 1) :
    IsItoIntegrable 𝓖 μ (fun i s ω => (boundaryCoef L a ψ i s ω).re) ∧
    IsItoIntegrable 𝓖 μ (fun i s ω => (boundaryCoef L a ψ i s ω).im) ∧
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (∑ x ∈ Finset.Icc (-(L : ℤ)) L, conj (a t ω x) * ψ t ω x) =
        (∑ x ∈ Finset.Icc (-(L : ℤ)) L, conj (a0 x) * ψ0 x)
        - (1 / 2 : ℂ) * (∫ s in (0 : ℝ)..t,
            (conj (a s ω L) * ψ s ω L + conj (a s ω (-L)) * ψ s ω (-L)))
        + ((stochInt 𝓖 μ B (fun i s ω => (boundaryCoef L a ψ i s ω).re) t ω : ℂ)
          + Complex.I * (stochInt 𝓖 μ B (fun i s ω => (boundaryCoef L a ψ i s ω).im) t ω : ℂ))
```
(The coefficients of $d\overline W{}^{(x-1)}$ on $B_{x-1,0},B_{x-1,1}$ are $\mathrm i/\sqrt2$ and $1/\sqrt2$, those of $dW^{(x)}$ on $B_{x,0},B_{x,1}$ are $\mathrm i/\sqrt2$ and $-1/\sqrt2$, as in `waveDiffRe/Im`.) The first draft of this statement wrote `∑ …, f x - c * ∫ …, g s + d` without parentheses, which Lean reads as one sum over $x$ of everything that follows (the binder-scope pitfall recorded on 13 November 2026, branch `work-fixwm`); the parenthesized form above was checked with `pp.parens`.

Further interfaces (in words, signatures to be fixed by I0‴):

* (L2) Picard: the map $\Phi_L(\psi_0,\cdot)$ on adapted continuous $\ell^2$-valued processes with $\mathbb E\sup_{[0,T]}\lVert\cdot\rVert^2<\infty$; `picard_step_bound` (the contraction estimate of 1.2 (a)); `picard_iter_props` (each iterate continuous for every $\omega$, adapted to $\mathcal F^a$, supported in $\Lambda_L$, finite second moments); `picard_limit` (a.s. uniform convergence on $[0,T]$, the limit is `IsWaveIto`).
* (L3) `IsWaveFunction.exists_goodIto_upTo` for every $L$: the good version (`exists_good`) has Itô coordinates up to `waveStop ψ' R N`; for $L=\infty$ it is Stage 2's lemma.
* (L4) `IsWaveIto.norm_eq` (finite $L$: $\lVert\psi_t\rVert=\lVert\psi_0\rVert$ for all $t$, a.s., by `inner_eq` with $a=b$, first up to `waveStop`), `IsWaveFunction.exists_unitIto` (all $L$), the frame lemma: for $y\in\Lambda_L$, solutions $u^y$ with $u^y_0=e_y$ are orthonormal for all $t$ a.s., and $\sum_y\lvert u^y_t(x)\rvert^2=1$ for $x\in\Lambda_L$, $\sum_y\lvert\langle u^y_t,v\rangle\rvert^2=\lVert v\vert_{\Lambda_L}\rVert^2$ (finite-dimensional: `Matrix.mul_eq_one_comm`).
* (L5) `isWaveFunction_unique_lib` via `exists_unitIto`, the isometry for differences and `volterra_ae_eq_zero`.
* (L7) `rwKernel_nonneg`, `hasSum_rwKernel` ($\sum_xp_s(x)=1$), `tsum_exp_mul_rwKernel` ($\sum_xe^{rx}p_s(x)=e^{2s(\cosh r-1)}$, via `lemma_2_3_linear` and `prop_2_2` on a space carrying a wave function on $\mathbb Z$ — the hypotheses of Lemma 8.2 provide one), `rwTail_le` ($\le2e^{-rL+2s(\cosh r-1)}$), `cosh_sub_one_le` ($\le\frac23r^2$ on $[0,1]$); atomic bounds: `etvDist_sum_dirac_le` ($\lVert\sum_xa_x\delta_{y_x}-\sum_xb_x\delta_{y_x}\rVert_{TV}\le\sum_x\lvert a_x-b_x\rvert$ when both are finite) and `abs_integral_sum_dirac_sub_le` ($\lvert\int f\,d\mu-\int f\,d\nu\rvert\le\lVert f\rVert_\infty\sum_x\lvert a_x-b_x\rvert$).
* (L8) `prop81_bound` (elaborated):
```lean
theorem prop81_bound [IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ)
    {ψ ψL : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)
    {L : ℕ} (hL : 1 ≤ L) (hψL : IsWaveFunction L 𝓕 B ψL μ)
    {n T ε : ℝ} (hn : 1 ≤ n) (hT : 0 < T) (hε : 0 < ε) (hℓ : n ^ (3 / 4 : ℝ) * T < L) :
    μ {ω | ENNReal.ofReal ε < ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (∑' x : ℤ, |zN n ψL ω t x - zN n ψ ω t x|)} ≤
      ENNReal.ofReal (16 / ε ^ 2 * (n * T * (8 + n * T / 2)) *
          Real.exp (2 * thetaN n * L - min 1 (L / (n * T)) * L / 3)) +
        ENNReal.ofReal (4 * Real.exp (2 * T) /
          (ε * Real.cosh ((L - n ^ (3 / 4 : ℝ) * T) / n ^ (1 / 2 : ℝ))))
```
  plus the deterministic `prop81_bound_tendsto` (the right side tends to $0$ along $n_k\to\infty$ with $L_k/n_k^{3/4}\to\infty$).

### 3.5 Package M interfaces

```lean
/-- (M1, elaborated) Slutsky for paths of measures, with varying probability spaces. -/
theorem tendstoInDistribution_of_close {T : ℝ} {ι : ℕ → Type*} {mι : ∀ k, MeasurableSpace (ι k)}
    {P : ∀ k, Measure (ι k)} [∀ k, IsProbabilityMeasure (P k)]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X Y : ∀ k, ι k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    {Z : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hX : ∀ k, AEMeasurable (X k) (P k)) (hY : TendstoInDistribution Y atTop Z P ν)
    (hXY : ∀ ε > 0, Tendsto (fun k => P k {ω | ¬ ∀ (t : Set.Icc (0 : ℝ) T) (f : ℝ →ᵇ ℝ),
        |∫ x, f x ∂(X k ω t : Measure ℝ) - ∫ x, f x ∂(Y k ω t : Measure ℝ)| ≤ ε * ‖f‖})
      atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z P ν

/-- (M2, elaborated) Version of `𝒵_n` for a finite box. -/
theorem exists_rescaledPath_version_box [IsProbabilityMeasure μ] {L : ℕ}
    {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)} (hψ : IsWaveFunction L 𝓕 B ψ μ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), AEMeasurable Zv μ ∧
      ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T,
        (Zv ω t : Measure ℝ) = rescaledMeasure L n (density ψ ω) t
```
M1 inside: the pseudo-metric `pathDist` (elaborated as a definition) induced by $\gamma\mapsto(t\mapsto(\gamma(t)(f_j))_j)$ into $C([0,T],\mathbb R^{\mathbb N})$ with `PiCountable.dist`, installed as a local `PseudoMetricSpace` with `replaceTopology` (topology equality from `isEmbedding_postcomp` and `isEmbedding_tightEmb`), and Mathlib's proof of `tendstoInDistribution_of_tendstoInMeasure_sub` with `dist` and $P_k$. M2 inside: `rescaledMeasure_eq_box` ($\mathcal Z_n=\varrho_n\,$`tiltedMeasureBox`), continuity of a finite sum of atoms, measurability through `measurable_pathFiniteMeasure_iff_tightEmb` (the good version of `exists_good` has $m_\Omega$-measurable coordinates), and the closeness bound of 1.2 (f).

### 3.6 Existence interfaces (E2, E1)

```lean
/-- (E2a, elaborated) Isonormal Gaussian process on a separable real Hilbert space. -/
theorem exists_isonormal (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : H → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ h, Measurable (W h)) ∧ IsGaussianProcess W P ∧
      (∀ h, HasLaw (W h) (gaussianReal 0 (‖h‖ ^ 2).toNNReal) P) ∧
      (∀ h g, cov[W h, W g; P] = ⟪h, g⟫_ℝ) ∧
      ∀ (a b : ℝ) (h g : H), W (a • h + b • g) =ᵐ[P] fun ω => a * W h ω + b * W g ω

/-- (E1a, elaborated) A Brownian family indexed by `ℤ × {0,1}` exists. -/
theorem exists_isBrownianFamily :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
      (B : ℤ × Fin 2 → ℝ → Ω → ℝ), IsProbabilityMeasure μ ∧ IsBrownianFamily 𝓕 B μ
```
E2b: `exists_isWhiteNoise_lib` from `exists_isonormal` with `H = Lp ℝ 2 (volume : Measure (ℝ × ℝ))` (indicators by `indicatorConstLp`), as in 1.2 (g). E1b: `exists_isWaveFunction_lib` from `exists_isBrownianFamily`, `IsBrownianFamily.nullAug` and `prop_2_1_existence`; `IsMildSolution.nonneg_lib` (one line). Universes: every existence statement produces `Ω : Type`; keep the constructions in `Type` (the Hilbert basis index of a `Type` is a `Type`).

---

## 4. Task breakdown

Method of Stages 2–4 (`docs/task-rules.md`): one Opus 5.5 agent per task, fresh context, own worktree from the merged state, checked by `scripts/task_merge.sh` and merged by the main session. Tasks may use interface statements of other tasks while still `sorry`. Sizes are lines of Lean to write (k = thousands). Base: the merge of Stage 4 (`main_theorem_top`, G9, the companion copies W, U3).

| Id | Files (under `QSSEPtoKPZ/`) | Content | Uses | Size (k) |
|---|---|---|---|---|
| **T0‴+I0‴** | `FiniteSystems/Statements.lean`, `Assembly/MainTheorem.lean`, `FiniteSystems/Existence.lean`, `WhiteNoise/Existence.lean` (statements, `sorry`); all interface files of Section 3; `docs/stage5-statements.md` + PDF, `docs/stage5-interfaces.md`, `docs/frozen-stage5.txt` | Section 2 with `sorry`, definitions complete; interfaces | Stages 2–4 | 0.6–0.9 |
| A‴ | `docs/stage5-audit.md` | independent audit of Section 2 (as in Stages 2–4: read-back, `pp.parens`, counterexamples) | T0‴ | (doc) |
| G11a | `ItoIntegral/ContIntegrable.lean` | continuous adapted finite-energy ⇒ `IsItoIntegrable`; Doob summed over coordinates | Stage 2 C | 0.3–0.5 |
| G11b | `ItoIntegral/ComplexIto.lean` | complex Itô processes, product rule for $\bar zw$, finite sums | Stage 2 C6 | 0.4–0.6 |
| L1 | `FiniteSystems/WaveIto.lean` | `IsWaveIto`, `isWaveFunction`, coefficient algebra, `waveStop` stopping time, `IsBrownianFamily.isProbabilityMeasure` | Stage 2 D1 | 0.4–0.6 |
| L2a | `FiniteSystems/PicardIter.lean` | Picard map, $\ell^2$-valued iterates (null-set modification), continuity, adaptedness, contraction estimate | G11a, L1 | 0.8–1.2 |
| L2b | `FiniteSystems/Picard.lean` | limit, `exists_isWaveIto`, **`prop_2_1_existence`** | L2a | 0.6–1.0 |
| L3 | `FiniteSystems/Identification.lean` | good version and Itô coordinates up to `waveStop`, every $L$ | Stage 2 D1, L1 | 0.5–0.8 |
| L4 | `FiniteSystems/Pairing.lean`, `PairingAlgebra.lean`, `Frame.lean` | `inner_eq`, `inner_restrict_eq`, norm conservation on boxes, `exists_unitIto` (all $L$), frame/Parseval | G11b, L1, L3 | 0.9–1.4 |
| L5 | `FiniteSystems/Uniqueness.lean` | **U1** `isWaveFunction_unique_lib` | L4, G11a, Volterra | 0.4–0.7 |
| L6 | `FiniteSystems/Lemma82.lean` | frame from Picard, Duhamel, Doob, Parseval, **`lemma_8_2`** | L2b, L4, L7 | 0.8–1.2 |
| L7 | `FiniteSystems/RandomWalkTail.lean`, `FiniteSystems/AtomicTV.lean` | `rwKernel` sum and exponential moments, Chernoff, `cosh` bound; atomic TV and integral bounds | Stage 2 (2.3), Prop 2.2 | 0.5–0.8 |
| L8 | `FiniteSystems/Prop81.lean` | `prop81_bound`, asymptotics, **`prop_8_1`** | L6, L7, Lemma 5.2 | 0.5–0.8 |
| E2a | `WhiteNoise/Isonormal.lean` | `exists_isonormal` | Mathlib | 0.8–1.2 |
| E2b | `WhiteNoise/Existence.lean` | **E2** `exists_isWhiteNoise_lib` | E2a | 0.5–0.8 |
| E1a | `FiniteSystems/BrownianFamily.lean` | `exists_isBrownianFamily` (continuous versions by G9, glued; three clauses) | E2b, G9 | 0.5–0.8 |
| E1b | `FiniteSystems/Existence.lean` | **E1** `exists_isWaveFunction_lib`, **P** `IsMildSolution.nonneg_lib` | E1a, L2b | 0.1–0.2 |
| M1 | `Assembly/PathMetric.lean`, `Assembly/Slutsky.lean` | path metric, `tendstoInDistribution_of_close` | Stage 3 H2 | 0.5–0.8 |
| M2 | `Assembly/BoxVersion.lean` | `tiltedMeasureBox` identities, `rescaledMeasure_eq_box`, finite-box versions, closeness bound | Stage 2–3 | 0.3–0.5 |
| M3 | `Assembly/MainTheorem.lean` | **`main_theorem_lib`** | M1, M2, L2b, L8, `main_theorem_top` | 0.3–0.6 |
| F‴ | `Solution.lean`, `QSSEPtoKPZ.lean`, `docs/stage5-report.md` | final assembly and checks (Section 7) | all | 0.1–0.2 |

**Waves** (at most six agents at once):

* Wave 0: T0‴+I0‴ (one agent, as in Stage 4). The statements are not submitted for approval first (author's instruction); they go into `docs/frozen-stage5.txt` at their merge commit so that `task_merge.sh` protects them from silent changes.
* Wave 1: G11a, G11b, L1, L3, E2a, M1; plus the audit A‴ (a seventh, read-only agent, or at the start of wave 2).
* Wave 2: L2a, L4, L7, E2b, M2.
* Wave 3: L2b, L5, L6, E1a, M3.
* Wave 4: L8, E1b.
* Wave 5: F‴ (main session).

**Critical path**: I0‴ → G11b → L4 → L6 → L8 → M3 → F‴ (with L2a → L2b feeding L6 and E1b in parallel, and E2a → E2b → E1a → E1b a separate chain). Every task: no new `sorry`, standard axioms only except through other tasks' interfaces (listed in its report); distinctive names (`picard…`, `pairing…`, `frame…`, `isonormal…`, `pathMetric…`), private auxiliaries; the binder-scope rule (parenthesize big operators followed by other terms, check with `pp.parens`).

Notes for specific tasks:

* **L2a**: build each iterate as `⟨c, memℓp⟩` on the event where $\sum_x\sup_{t\le N}\lvert c_x(t)\rvert^2<\infty$ for all $N$ and all coordinate paths are continuous, and as the constant $\psi_0$ on a measurable null set containing the complement (`toMeasurable`), which `nullAug` contains (pattern of `IsWaveFunction.exists_good`). Use the finite energy of the previous iterate for G11a.
* **L3**: copy-adapt `WaveFunction/Good.lean` and `Identification.lean` with drift $-D_L(x,x)/2$ and the support clause; do not modify Stage 2 files.
* **L4**: do the cancellation once, as a pointwise algebraic identity on the coefficients (a `ring`-checked lemma per bond), then sum; treat $\lvert x\rvert=L$ separately. The degree $D_L(x,x)$ of `Definitions.lean` is `box`-indicator based: prove $D_L(x,x)=\#\lbrace y\in\Lambda_L:\lvert y-x\rvert=1\rbrace$ on $\Lambda_L$.
* **L6**: the columns are `exists_isWaveIto` with `ψ0 = lp.single 2 y 1`; the given $\psi,\psi^L$ are replaced by their unit Itô versions (`exists_unitIto`), indistinguishable from them.
* **E1a**: the continuous versions of G9 are only $\mathcal G^a_t$-measurable: use the filtration `nullAug ν 𝓖`; independence of $\mathcal G^a_s$ from the increments: add null sets on both sides of `indep_past`.
* **M1**: `TopologicalSpace.metrizableSpaceMetric` is *not* enough (its metric is not comparable to the test-function closeness); build the metric explicitly.
* **M3**: for each $k$ choose $\psi^\infty_k$ by cases on `L k = ⊤`; apply `main_theorem_top` with `fun k => nullAug (μ k) (𝓕 k)`; derive from `hL` that eventually ($L_k=\infty$ or $L_k\ge M n_k^{3/4}$) for every $M$.

---

## 5. Decisions (taken as recommended by the main session; for the author's review)

My recommendation in bold.

* **D1‴. Lemma 8.2 with the article's constant $4(8+S)$**, proved with the columns $U_te_y$ of the unitary matrix (built as wave functions with initial conditions $e_y$) and the pairing identity (1.2 (c)–(d)), instead of `PLAN.md`'s product rule for $\lVert\phi-\psi^L\rVert^2$ with a weaker constant. This is a change of route with respect to `PLAN.md` Section 3 (row "Section 8: $U_t$ … not needed"): $U_t$ is used through its columns; the matrix SDE (1.6) and the random walk $X$ (beyond its law $p_t$) are still not needed. **Recommended (faithful statement, about 0.5k more lines).**
* **D2‴. Coupling on the given space**: the wave function on $\mathbb Z$ is constructed on each $\Omega_k$ from the given Brownian family (strong existence), instead of the article's transfer of laws. **Recommended.**
* **D3‴. E1 from E2**: Brownian family = continuous versions of $\xi((0,t]\times I)$ for disjoint unit intervals (G9), then Picard. Alternative: Lévy–Ciesielski construction (0.8–1.2k lines more). **Recommended.**
* **D4‴. E2 by an isonormal process** on $L^2(\mathbb R^2)$ (Hilbert basis, `infinitePi` of standard Gaussians) and Mathlib's Gaussian-process independence lemmas. **Recommended.**
* **D5‴. Form of Proposition 8.1**: sequences $n_k$ as in the frozen theorem; one probability space per $k$; total variation as Mathlib's `etvDist` (infinite for infinite measures); outer probability of the event. **Recommended.**
* **D6‴. Billingsley's Theorem 3.1** replaced by `tendstoInDistribution_of_close` (explicit path metric from the bump functions of Stage 3, closeness "$\lvert\gamma(t)(f)-\gamma'(t)(f)\rvert\le\varepsilon\lVert f\rVert_\infty$ for all $t,f$", varying spaces), instead of the bounded Lipschitz distance. **Recommended.**
* **D7‴. Layout of the final proof**: the library proves `main_theorem_lib` and the companion copies `*_lib`; `Solution.lean` is rewritten to import the library (and **not** `MainTheorem.lean` or `Companions.lean`, whose names it redeclares) and to state the eight theorems verbatim with proofs `:= …_lib …`. `Definitions.lean`, `MainTheorem.lean`, `Companions.lean` and `Challenge.lean` are not touched: they keep their `sorry` (the "statement files" of rule 4) and their Stage 0 hashes. Alternative: replace the `sorry` of `MainTheorem.lean`/`Companions.lean` by library terms (changes the frozen files' hashes and requires `make_challenge.py` to strip proofs). **Recommended: Solution-only.**
* **D8‴. U1** by unit-norm Itô versions and the Volterra lemma (Gronwall), for every $L$. **Recommended.**
* **D9‴. Identification for finite $L$** in new files copied from Stage 2 (`IsGoodWave`/`Identification`), not by generalizing the approved Stage 2 files. **Recommended** (no risk to frozen declarations).
* **D10‴. `Corollaries.lean`** (the fixed-time corollary and $\int\varphi\,d\mathcal Z(t)=\int Z\varphi$) keeps depending on the statement files (it imports `MainTheorem.lean`, so it cannot import `Solution.lean`). Option: add proved copies in a file importing the library (0.1k). **Recommended: add the proved copies** (`Assembly/Corollaries.lean`), so that nothing proved by the project depends on a `sorry`.
* **D11‴. Statement sheet and audit without waiting**: T0‴ writes `docs/stage5-statements.md` (+ PDF); an independent audit (A‴) runs at the start of wave 1; errors found are fixed before the dependent tasks start; the author reviews afterwards. **Recommended.**
* **D12‴. Comparator**: not installed; installing it means downloading it (permission of the author). Locally, the checkpoint uses the Stage 0 substitute: `pp.all` comparison (no elision) of the 17 definitions and 8 theorems between the environments of `Challenge.lean` and `Solution.lean`, and `#print axioms` in `Solution.lean`. **Recommended; the comparator run itself is left to the author.**

**Places where the Lean proof departs from the article** (to record in `PROGRESS.md`): D1‴ (columns of $U$ rather than the matrix SDE; same constant), D2‴, D6‴; Picard iteration and Gronwall instead of Da Prato–Zabczyk for Proposition 2.1; filtrations augmented by null sets for the constructed solutions; E1, E2 constructions (not in the article).

---

## 6. Risks and estimate

**Risks.**

* **R1 (Picard in $\ell^2$, measurability).** Iterates must be adapted to $\mathcal F^a$ for every $\omega$ and continuous for every $\omega$; the null-set modifications must stay inside `nullAug`. Pattern exists (`exists_good`, `exists_isUnitWave`). Medium.
* **R2 (pairing algebra).** Four real product rules per site and bookkeeping of real/imaginary parts of complex coefficients on two Brownian motions per bond; risk of long proofs, not of failure. Mitigation: G11b states the complex product rule once; L4 proves one coefficient identity per bond with `ring`.
* **R3 (E2 Gaussian limits).** L² limits of Gaussian variables are Gaussian (characteristic functions); Mathlib's `IsGaussian` for vectors via linear functionals. If `IsGaussianProcess` is awkward, the independence clauses can be proved from `iIndepFun_iff_charFun_pi`/`indepFun_iff_charFun_prod` directly (+0.3k).
* **R4 (path metric).** `replaceTopology` and the Borel instance of `C(Set.Icc 0 T, FiniteMeasure ℝ)` must agree definitionally; if not, prove the portmanteau characterization via the embedding instead (+0.2k).
* **R5 (Stage 4 dependency).** M3 needs `main_theorem_top` and E1a needs G9, both on `work-integ4`; E1b/P needs `nonneg_of_isWaveFunction`. Start Stage 5 from the merged Stage 4.
* **R6 (universes).** `main_theorem_lib` has two universe variables, E1/E2 produce `Type`; P instantiates `nonneg_of_isWaveFunction.{0}` (checked).
* **R7 (usage).** Weekly usage was about 87% on 13 November 2026 (12:10 UTC); Stage 5 is about half of Stage 4.

**Size estimate.**

| Part | Tasks | k lines |
|---|---|---|
| statements, interfaces | T0‴+I0‴ | 0.6–0.9 |
| generic Itô | G11a, G11b | 0.7–1.1 |
| wave equation: Itô form, Picard, identification, pairing, U1 | L1–L5 | 3.6–5.7 |
| Lemma 8.2, Proposition 8.1 | L6, L7, L8 | 1.8–2.8 |
| E2, E1, P | E2a, E2b, E1a, E1b | 1.9–3.0 |
| assembly | M1, M2, M3, F‴ | 1.2–2.1 |
| **Total Stage 5** | 20 tasks (+ audit) | **about 10–16** |

`PLAN.md` gives 9–14k for packages L, M. Agent time: 20 tasks at 15–50 minutes, **about 7–14 agent-hours**, i.e. roughly 3–5 hours of wall time with six agents.

---

## 7. Final checks for the checkpoint, and what was checked here

### 7.1 Checkpoint (task F‴, main session)

1. `lake build` succeeds for the three targets (`QSSEPtoKPZ`, `Challenge`, `Solution`). Expected warnings: `declaration uses 'sorry'` only in `MainTheorem.lean`, `Companions.lean`, `Challenge.lean` (and `Corollaries.lean` through them).
2. No `sorry`, `admit`, `axiom`, `native_decide` in any other `.lean` file (`grep`).
3. In the environment of `Solution.lean`: `#print axioms` of `QSSEPtoKPZ.main_theorem`, `exists_isWaveFunction`, `isWaveFunction_unique`, `exists_isWhiteNoise`, `IsWalshIntegral.ae_eq`, `IsWalshIntegral.isometry`, `isMildSolution_unique`, `IsMildSolution.nonneg` shows only `propext`, `Classical.choice`, `Quot.sound`. Same for every approved statement of Stages 1–5 (they are in the root module).
4. `Solution.lean` imports no file that imports `MainTheorem.lean` or `Companions.lean` (else duplicate declarations); the eight theorems there are verbatim copies of `Challenge.lean`.
5. Comparator substitute: the 17 definitions and 8 theorem types printed with `pp.all` (no elision, `pp.proofs` irrelevant for types) in the environments of `Challenge.lean` and of `Solution.lean` are identical (as on 12 November 2026). `python3 scripts/make_challenge.py --check` passes; SHA-256 of `Definitions.lean`, `MainTheorem.lean`, `Companions.lean`, `Challenge.lean` equal to the Stage 0 values in `PROGRESS.md`.
6. `check_frozen`: Stage 0 (`6d27b6f`, 25 declarations), Stage 1 (`df64451`/`3d70e23`), Stage 2 (`897d883`, `docs/frozen-stage2.txt`), Stage 3 (`535961f`, `docs/frozen-stage3.txt`), Stage 4 (`2a86280`, `docs/frozen-stage4.txt`), Stage 5 (merge commit of T0‴, `docs/frozen-stage5.txt`): all "same" (or definitionally equal, kernel-checked, with an explanation).
7. What the comparator run needs (not done here, nothing online): the `comparator` tool installed locally (and, if `enable_nanoda` were true, the `nanoda` checker; it is `false`); `comparator.json` as it is (challenge module `Challenge`, solution module `Solution`, the eight theorem names, permitted axioms `propext`, `Quot.sound`, `Classical.choice`); a built project (`lake build`). Installing the tool is a download, to be decided by the author.
8. `PROGRESS.md`, `docs/stage5-report.md` (+ PDF): lines, agents, time, usage, departures (Section 5), the list of statements for the author.

### 7.2 What was checked for this design

* Article: SHA-256 unchanged (`3547cb86…`, 1713 lines). Section 8 (lines 1412–1497), Section 2.1 (Proposition 2.1), Section 1.3 (Definition 1.1, (1.6), (1.7)) read line by line; the steps of 1.3 re-derived by hand (Itô correction in $d(U^\ast\phi)$, Doob and Cauchy–Schwarz constants, Chernoff bound and $\cosh r-1\le\frac23r^2$, the asymptotics, $\lvert y_n(t,x)\rvert>\ell_n$); the drift and noise cancellations of the pairing identity (1.2 (c)) computed by hand, including the boundary drift $-\tfrac12(\overline{a(L)}\psi(L)+\overline{a(-L)}\psi(-L))$.
* Scratch file `<scratch>/s5design/Stage5.lean` (290 lines, a module importing the library), compiled with `lake env lean` from the worktree at commit `91918fb` (Lean 4.35.0, Mathlib v4.35.0): only `declaration uses 'sorry'` warnings. It contains every signature marked "elaborated": `tiltedMeasureBox`, `rwTail`, `prop_2_1_existence`, `lemma_8_2`, `prop_8_1`, `main_theorem_lib`, the four companion copies (P proved in one line from `nonneg_of_isWaveFunction`), `IsWaveIto`, `exists_isWaveIto`, `IsWaveIto.isWaveFunction`, `IsWaveFunction.exists_unitIto`, `IsWaveIto.inner_eq`, `boundaryCoef`, `IsWaveIto.inner_restrict_eq`, `prop81_bound`, `tendstoInDistribution_of_close`, `exists_rescaledPath_version_box`, `exists_isonormal`, `exists_isBrownianFamily`, `pathDist`.
* `pp.parens` printouts of `prop_2_1_existence`, `lemma_8_2`, `prop_8_1`, `inner_restrict_eq`, `prop81_bound`, `tendstoInDistribution_of_close`, `pathDist`: every sum, integral and supremum has the intended scope (one error found and fixed in the first draft of `inner_restrict_eq`, see 3.4).
* `main_theorem_lib` and the four companion copies against `MainTheorem.lean`/`Companions.lean`: `pp.all` printouts (no elision) identical after renaming, and `example : type_of% @main_theorem.{u, v} := @main_theorem_lib.{u, v}` (and conversely, and for the companions) accepted by the kernel.
* Mathlib names of 3.1 located by `grep` in the v4.35.0 sources (not all `#check`ed).
* Not checked: proofs; the line estimates; the exact signatures of the interfaces described in words (L2, L3, L7, the frame lemma); whether `replaceTopology` gives the definitional equality needed in M1; G9's `walshProc_exists_cont_rect` was read on branch `work-integ4` (commit `fb90228`), not yet on `master`.
