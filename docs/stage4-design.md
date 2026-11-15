# Stage 4: design (packages I, J, K, identification of the limit)

Written on 13 November 2026 by a design agent (Opus 5.5), at the request of the main session. **Nothing in this document is proved.** It fixes the Lean statements, the generic infrastructure and the order of work for Stage 4 (Section 7 of the article: Propositions 7.1, 7.2, 7.3 and the proof of Theorem 1.2 for $L_n=\infty$). The Lean signatures of Sections 2 and 3 were checked to elaborate against Mathlib v4.35.0 and the library at commit `367fdc1` (with `sorry` proofs) in a scratch file outside the repository (Section 7); they are a starting point for the tasks T0″ and I0″, not frozen text.

Equation numbers are those of the article (version of 11 November 2026, SHA-256 `3547cb86…`, unchanged on 13 November 2026: checked), read from its `.aux` file: Proposition 7.1 with (7.1)–(7.7), Proposition 7.2 with (7.8)–(7.12), Proposition 7.3 with (7.13), and (7.14), (7.15). Earlier results used: Proposition 3.1 ((3.14), (3.15)), (3.8), (3.9), Proposition 4.3 ((4.8), (4.9)), Proposition 5.1, (6.1), Propositions 6.1 ((6.2)) and 6.2 ((6.3)).

**Corrections of 13 November 2026** (after the audit `docs/stage4-audit.md` and an external review; details in the section "Corrections after the audit and an external review" of the audit and in the departures 17–22 of `docs/stage4-interfaces.md`): `prop_7_2` takes the hypothesis $\mathcal Z(0)=\delta_0$ (the claim of 2.3 that it is not needed was wrong); in `eq_7_4` the probability space of $\mathcal Z$ is bound after `∃ C`; the projection onto the noise (1.2 (h), G6) is a conditional expectation for the probability measure $\nu\otimes\gamma\otimes\gamma$, not for $\nu\otimes\mathrm{Leb}^2$; the `limit` rule of `IsMMIntegral` requires the limit process to be a.e. measurable at each time, and the covariation lemmas assume $\mathbb E\int_0^T\int q<\infty$; a bridge lemma `isWeakMild_prod_of_eq_7_8` (task Q5a) is added between Propositions 7.2 and the end of Section 7.

Readers: Section 1 is for the author. Sections 2 to 4 are for the agents who will write the Lean code. Section 5 lists the decisions for the author, Section 6 the risks and the estimate.

---

## 1. Mathematical overview

### 1.1 What Stage 4 proves

The checkpoint of `PLAN.md` is "Theorem 1.2 for $L_n=\infty$". It is reachable **literally** at the end of Stage 4: the Lean theorem `main_theorem_top` (Section 2.6) is the frozen `main_theorem` with $L_k=\infty$ for every $k$ (the hypotheses on $L$, which then hold trivially, are dropped). Its conclusion is word for word that of `main_theorem`: versions of $\mathcal Z_{n_k}$ (the measures of (1.15), not the tilted ones) and of $\mathcal Z(t)=\max(Z(t,x),0)\,dx$ on the given space carrying the given solution $Z$ of (1.13), and convergence in distribution in $C([0,T],\mathcal M_+)$. Nothing of Stage 5 is needed. The frozen `main_theorem` itself (all $L_k$, finite or not) needs Section 8 (package L) and stays for Stage 5.

| Article | Content | In Lean (Section 2) |
|---|---|---|
| Prop 7.1 (1) | $\mathcal Z(0)=\delta_0$ | `prop_7_1`, first conjunct |
| Prop 7.1 (2), (7.1), (7.4) | predictable density $Z\ge0$ in $L^2(\Omega\times[0,T]\times\mathbb R)$, $\mathcal Z(t)=Z(t,x)dx$ for a.e. $t$ | `prop_7_1`, second conjunct; `eq_7_4` |
| Prop 7.1 (3), (7.2), (7.3) | martingale problem | `prop_7_1`, third conjunct (`HasBracket`) |
| Prop 7.2, (7.8) | white noise representation | `prop_7_2` |
| Prop 7.3, (7.13) | uniqueness in $\mathcal H_T$ for the weak mild equation | `prop_7_3` (with the structure `IsWeakMild`) |
| (7.14), (7.15), stochastic Fubini | the solution of the SHE belongs to $\mathcal H_T$ and satisfies (7.13) | `IsMildSolution.integral_sq` (the second moment, as the series whose sum is (7.15)), `IsMildSolution.isWeakMild`, for the field $Z$ **given** in the statement (see 1.2 (h)) |
| Proof of Thm 1.2 for $L_n=\infty$ | | `main_theorem_top` |

Equations (7.5)–(7.7) and (7.9)–(7.12) are steps of the proofs; they appear as internal lemmas (Section 3), not as statements for approval.

**Companion statements.** In scope of Stage 4: **W** (`IsWalshIntegral.ae_eq`, `IsWalshIntegral.isometry`): they are needed by the proof (Itô's isometry for the Walsh integral is used in Proposition 7.3 and for the given field $Z$); **U3** (`isMildSolution_unique`): a by-product of the second-moment computation (1.2 (h)), a few hundred lines. They are proved as library theorems whose statements are identical (`pp.all`) to those of `Companions.lean`, as for `main_theorem` at the end. **E2** (existence of a white noise) is not needed by `main_theorem_top` (the given space $\Omega'$ carries a white noise, which is used for the enlargement in Proposition 7.2); it can be done in Stage 4 in parallel (task E2, off the critical path) or left to Stage 5 (decision D10″). **P** (`IsMildSolution.nonneg`) cannot be finished in Stage 4: the route deduces it from the limit, which requires a realization of the QSSEP on $\mathbb Z$ to exist (companion E1 for $L=\infty$, package L, Stage 5). Stage 4 proves the conditional form `IsMildSolution.nonneg_of_isWaveFunction` (if some wave function on $\mathbb Z$ exists, every mild solution is nonnegative); Stage 5 combines it with E1.

### 1.2 How the Lean proof goes, and where it departs from the article

`PLAN.md` (Section 3) fixed five rows for Section 7: Skorokhod's representation formalized on Polish spaces; BDG replaced by a fourth-moment bound from the product rule; Lévy's characterization by discretization; a contraction for (7.13) instead of Chen–Dalang; canonical space and pullback for equality of laws, with Lusin–Souslin. After surveying the library and Mathlib, this design keeps the spirit of each row but proposes **simpler routes for four of them** (decisions D1″–D4″); none changes a statement of the article.

**(a) Skorokhod's representation, along a subsequence, without Polishness** (D1″). The article uses Billingsley's Theorem 6.7 on the Polish space $C([0,T],\mathcal M_+)$. Mathlib has neither Skorokhod's theorem nor the completeness of $\mathcal M_+(\mathbb R)$ (decision D8' of Stage 3 deferred it). The proof only ever extracts subsequences, so it suffices to have: *if $P_k\to P$ weakly on a separable metrizable space $S$, then for some subsequence $k_j$ there are, on one probability space, $X_j\sim P_{k_j}$ and $X\sim P$ with $X_j\to X$ almost surely.* Proof: for $\varepsilon>0$, cover all but $\varepsilon$ of the $P$-mass by finitely many disjoint $P$-continuity sets $A_1,\dots,A_m$ of diameter $<\varepsilon$ (balls whose radii avoid the countably many radii with spheres of positive mass). Let $c_i=\min(P_k(A_i),P(A_i))$. On $S\times\prod_k(\dots)$ with a product measure (Mathlib's `Measure.infinitePi`), draw $X\sim P$ and, independently for each $k$, samples $Y_{k,i}\sim P_k(\cdot\mid A_i)$, a sample $Y_{k,0}$ of the normalized remainder $R_k=P_k-\sum_ic_iP_k(\cdot\mid A_i)$ and a uniform $V_k$; set $X_k=Y_{k,i}$ if $X\in A_i$ and $V_k<c_i/P(A_i)$, and $X_k=Y_{k,0}$ otherwise. Then $X_k\sim P_k$ exactly, and $\mathbb P(d(X_k,X)\ge\varepsilon)\le1-\sum_ic_i\to1-\sum_iP(A_i)\le\varepsilon$ (portmanteau for continuity sets, in Mathlib). Choosing $\varepsilon_j=2^{-j}$ and $k_j$ large, Borel–Cantelli gives almost sure convergence along $k_j$. No completeness, no Borel isomorphism.

**(b) "All quantities are measurable functions of the trajectory"** (as in the article). On $C([0,T],\mathcal M_+)$, $\mathfrak z_n(t,x)$ is read as the mass $\gamma(t)(\lbrace y_n(t,x)\rbrace)$ of an atom, a Borel function of the path ($\mu\mapsto\mu(F)$ is upper semicontinuous for closed $F$; this avoids Mathlib's Giry $\sigma$-algebra on `FiniteMeasure`, which is not known to be Borel). $\mathcal W_n$, $\mathcal E_n$, $Q_n=\langle M_n^\phi\rangle$, $M_n^\phi$ and $\lVert(\phi\mu)\ast\rho_\varepsilon\rVert_2^2$ become Borel functionals of the path, equal almost surely, for all $t$, to the quantities of Sections 3–6 on the version of Proposition 5.1. The estimates (4.8), (6.2), Proposition 3.1 (2)–(3), Proposition 6.2 and the martingale property of $M_n^\phi$, $(M_n^\phi)^2-Q_n$ are then restated as statements about the law $P_n$ of the path (on the canonical space with its natural filtration), and transported to the Skorokhod space.

**(c) Filtrations.** As in Stages 2–3 (decisions D1, D4): the natural filtration of $\mathcal Z$, augmented by the null sets; no right-continuity. A continuous martingale for $\mathcal G^0$ is one for this filtration. Proposition 7.2 only needs a filtration containing it.

**(d) BDG replaced by a localization in $M$** (D3″; `PLAN.md` proposed a fourth-moment bound from the product rule, which does not apply on the Skorokhod space, where no Brownian motion is left). The article stops at $\sigma_n^K=\inf\lbrace t:Q_n(t)\ge K\rbrace$ and needs $\mathbb E[M_n^\phi(t\wedge\sigma_n^K)^4]\le CK^2$ for uniform integrability. Instead stop at $\sigma_n^L=\inf\lbrace t:\max(Q_n(t),M_n^\phi(t)^2)\ge L\rbrace\wedge T$. The stopped quantities are bounded by $L$, so bounded convergence applies; the convergence $\sigma_n^L\to\sigma^L$ holds for all but countably many $L$ by the article's own argument (it uses only that $L\mapsto\sigma^L$ is nondecreasing and the processes continuous, not monotonicity of $Q$). Then $(M^\phi)^2-Q$ is a local martingale; since $\mathbb E[Q(T)]<\infty$ by (7.1) and $\mathbb E\sup_tM^\phi(t)^2\le4\mathbb E M^\phi(T)^2<\infty$ (Doob, in the library), it is a true martingale, which is what `HasBracket` requires. The article leaves this last step implicit ("this proves (7.3)").

**(e) Density in Proposition 7.1 (2).** As in the article, with one change of argument: from $\liminf_k\lVert\mathcal Z(t)\ast\rho_{1/k}\rVert_2=c<\infty$ one gets $\lvert\mathcal Z(t)(f)\rvert\le c\lVert f\rVert_2$ for $f\in C_c(\mathbb R)$, hence (Riesz) a density in $L^2$ — instead of weak compactness of a bounded subsequence. Lebesgue's differentiation theorem for the mollifiers $\rho_{1/k}$ (from Mathlib's version for balls) identifies the density with $Z(t,\cdot)=\liminf_k\mathcal Z(t)\ast\rho_{1/k}$.

**(f) Proposition 7.2** follows the article's four steps. Lean specifics: the integral $h\cdot M$ against the orthogonal martingale measure $\varphi\mapsto M^\varphi$ is an inductive closure (`IsMMIntegral`, same pattern as the frozen `IsWalshIntegral`); the enlargement is the product with a space carrying a white noise (an auxiliary white noise is a hypothesis of `prop_7_2`; in `main_theorem_top` it is the given one, decision D7″); the white noise $\xi$ is extended after time $T$ by the auxiliary noise, since the frozen `IsWhiteNoise` concerns all times; **Lévy's characterization** is proved by discretization (`PLAN.md`), in the form $\int_A e^{iu(N_t-N_s)}d\mathbb P=e^{-cu^2(t-s)/2}\mathbb P(A)$ for $A\in\mathcal G_s$, then for finite families with brackets $\delta_{ij}c_it$ (characteristic functions, `Measure.ext_of_charFun`, `indepFun_iff_charFun_prod` in Mathlib), which yields the three clauses of `IsWhiteNoise`.

**(g) Proposition 7.3** as in the article, with mollified test functions instead of an orthonormal basis (D5″): with $f=\rho_\delta(z-\cdot)$, Itô's isometry and Young's inequality give $\mathbb E\lVert D(t)\ast\rho_\delta\rVert_2^2\le\int_0^t(4\pi(t-s))^{-1/2}F(s)ds$; letting $\delta\to0$ (Fatou), $F(t)\le\frac1{2\sqrt\pi}\int_0^t\frac{F(s)}{\sqrt{t-s}}ds$, and the article's $e^{-at}$ argument concludes. Only the inequality is used (as in the last display of the article's proof). This avoids Gram–Schmidt and Parseval in $L^2(\mathbb R)$.

**(h) The end of Section 7: identification of the law** (D4″). The article takes the solution $Z^\star$ of (7.14) driven by the white noise $\xi$ of Proposition 7.2 (Chen–Dalang), shows $Z^\star\in\mathcal H_T$ by (7.15) and (7.13) by stochastic Fubini, and concludes from Proposition 7.3 and continuity that the law of $\mathcal Z$ "is the law of the process described in the statement". In Lean the statement concerns an **arbitrary** space $\Omega'$ carrying a white noise $S$ and a solution $Z$ (README, choice 5), and existence of a solution (E3) is not proved. The route below proves no existence at all:

* *The given field.* On $\Omega'$: $F(t,x)=\mathbb E[Z(t,x)^2]$ is finite (W) and satisfies $F=K+K\ast F$ with $K(t,x)=g_t(x)^2$ (Itô isometry, $\mathbb E Z(t,x)=g_t(x)$). Since $K^{\ast k}(t,x)=2^{-k}t^{k/2-1}\Gamma(k/2)^{-1}g_{t/2}(x)\le\varepsilon_k(T)K(t,x)$ with $\varepsilon_k(T)\to0$, $K^{\ast N}\ast F\le\varepsilon_N(F-K)\to0$ pointwise, so $F=\sum_{k\ge1}K^{\ast k}$; this series is (7.15) (checked by hand: its sum is $g_t(x)^2(1+\sqrt{\pi t}e^{t/4}\Phi(\sqrt{t/2}))$, a Mittag-Leffler function), hence $Z\in\mathcal H_T$. The same computation for the difference of two solutions gives U3 (the argument of README, choice 4). Stochastic Fubini: (7.13) for $Z$ and every $t\in(0,T]$, by Riemann sums in $x$ (continuity of $Z$) and the $L^2$ closure rule of `IsWalshIntegral`.
* *Uniqueness in law for (7.13).* Let $\xi$ be a white noise for a filtration $\bar{\mathcal G}$ on $\tilde\Omega$, $\mathcal N$ its natural filtration, and $\tilde Z\in\mathcal H_T$ a solution of (7.13). Conditional expectation onto $\mathcal N_\infty$ maps Walsh integrals to Walsh integrals: $\mathbb E[\int h\,d\xi\mid\mathcal N_\infty]=\int\hat h\,d\xi$, where $\hat h$ is the orthogonal projection of $h$ in $L^2(\nu\otimes\mathrm{Leb}^2)$ onto the $\mathcal N_\infty\otimes\mathcal B$-measurable fields (in Lean: the conditional expectation for the probability measure $\nu\otimes\gamma\otimes\gamma$, $\gamma$ the standard Gaussian, which has the same null sets; **not** Mathlib's `condExp` for $\nu\otimes\mathrm{Leb}^2$, which is $0$ on integrands in $L^2$ but not in $L^1$ of that infinite measure) (by induction on the definition of `IsWalshIntegral`: for a block $c\mathbf 1_{(s,t]\times(a,b]}$, $\mathbb E[c\mid\mathcal N_\infty]=\mathbb E[c\mid\mathcal N_s]$ because the increments of $\xi$ after $s$ are independent of $\bar{\mathcal G}_s$). The equation is linear and the projection takes out deterministic bounded factors, so $\hat Z$ = the projection of $\tilde Z\mathbf 1_{[0,T]}(t)$ is again a solution, and Proposition 7.3 gives $\tilde Z=\hat Z$: **the solution is a function $H$ of the noise**. By induction again, a Walsh integral whose integrand and value are functions of the noise transfers, through the same functions, to any other space carrying a white noise (the law of the noise coordinates $\xi((0,t]\times(a,b])$ is the same for all white noises). So $H(S)$ solves (7.13) on $\Omega'$, and Proposition 7.3 on $\Omega'$ gives $Z=H(S)$. Hence, for almost every $t$ and every $f\in C_c^\infty$, $\int Z(t,x)f(x)dx$ on $\Omega'$ and $\mathcal Z(t;f)$ on $\tilde\Omega$ are the same function of the noise.
* *Version on $\Omega'$ and positivity, without Lusin–Souslin* (D2″). Let $\iota(\gamma)=(\gamma(t)(f_j))_{t\in D,j\ge1}$, with $D\subset(0,T]$ countable, dense, made of good times, and $f_j$ the compactly supported bumps of Stage 3 ($j\ge1$). $\iota$ is continuous and injective on $C([0,T],\mathcal M_+)$. The law of $\mathcal Z$ is tight (it is a limit of the tight laws of Proposition 5.1), so it charges $\bigcup_m\iota(K_m)$ fully for compacts $K_m$; each $\iota(K_m)$ is compact, hence Borel, and $\iota$ is a homeomorphism on $K_m$. The vector $Y'(\omega)=(\int Z(t,x)f_j(x)dx)_{t,j}$ on $\Omega'$ has the same law, so almost surely $Y'(\omega)=\iota(\gamma_\omega)$ for a continuous path $\gamma_\omega$, measurable in $\omega$. Comparing $\gamma_\omega(t)$ and $Z(t,x)dx$ on the bumps, using continuity in $t\in(0,T]$ on both sides: $Z(t,\cdot)\ge0$ (bumps with small support), so $\max(Z,0)=Z$ and $\gamma_\omega(t)=$ `sheMeasure` for $t\in(0,T]$; at $t=0$, $\gamma_\omega(0)=\delta_0$ by the law. This replaces Lusin–Souslin (which needs $C([0,T],\mathcal M_+)$ Polish) by the $\sigma$-compactness of a tight law. Positivity of $Z$ on $(0,T]$ is thus obtained on the given space, inside the proof of `main_theorem_top`.
* *Conclusion* as in the article: every subsequence has a further subsequence converging to the law of the version on $\Omega'$ (Proposition 5.1, Prokhorov and metrizability from Stage 3), hence convergence; then $\mathcal Z_n=\varrho_n\mathsf Z_n$ with $\varrho_n\to1$ uniformly ((3.8), (3.9), Stage 2; Mathlib's `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`).

`PLAN.md` proposed a contraction of $\mathcal H_T$ (existence and uniqueness at once) and a pullback from a canonical space. The contraction needs jointly measurable versions of the parametrized integrals $(t,x)\mapsto\int\int g_{t-s}(x-y)F(s,y)\xi(dsdy)$ and existence on a canonical space; the route above needs neither (only uniqueness, a conditional expectation and the transfer lemma, which the pullback also needed). Decision D4″.

**(i) Polishness of $\mathcal M_+$ is not needed** (resolves D8' of Stage 3; D2″): (a) and (h) avoid it; Prokhorov's theorem (direct half) and the metrizability of the space of laws were enough in Stage 3.

### 1.3 Check of Section 7 of the article

Every step of Sections 7.1–7.3 was re-derived (Section 7 below). **No error was found.** Points where the text is compressed, all standard, and how Lean handles them:

1. Section 7.1, first lines: "Since this space is Polish" — true (classical) but not proved in Lean; not needed (1.2 (a)).
2. Proof of Prop 7.1 (3), last sentence: "$(M^\phi)^2-Q$ is a local martingale. As $Q$ is continuous, nondecreasing and adapted, this proves (7.3)." The passage from local to true martingale uses $\mathbb E[Q(T)]<\infty$ (from (7.1)) and $\mathbb E\sup_tM^\phi(t)^2<\infty$ (Doob); written out in Lean (1.2 (d)).
3. Same proof: BDG gives $\mathbb E[M_n^\phi(t\wedge\sigma_n^K)^4]\le CK^2$ — correct; replaced in Lean by a localization (1.2 (d)).
4. Proof of Theorem 1.2: "the law of $\mathcal Z$ is the law of the process described in the statement" uses that the solution of (7.14) is a measurable function of the noise (Chen–Dalang's solution is adapted to the filtration of $\xi$), so that its law does not depend on the space. In Lean this is the step "uniqueness in law" of 1.2 (h).

Also checked: $\lVert g_r\rVert_2^2=(4\pi r)^{-1/2}$; $\frac1{2\sqrt\pi}\int_0^\infty e^{-ar}r^{-1/2}dr=\frac1{2\sqrt a}$; Step 4 of Prop 7.2 (the function $\phi_s=g_{t-s}\ast f$, $\phi_s=f-\frac{s-t}2f″$ after $t$, is in $C_b^{1,3}$: its time derivative is $-\frac12g_{t-s}\ast f″$ from the left of $t$ and $-\frac12f″$ from the right, continuous at $t$; $\phi_0(0)=\int g_tf$ since $g$ is even); the polarization (7.9); the isometry argument for (7.11) (cross terms vanish by independence of $\xi'$ and $\mathcal Z$); $K^{\ast k}$ and (7.15) (1.2 (h)).

---

## 2. The article's results in Lean

**All statements of this section go to the author for approval** (rule 5 of `CLAUDE.md`), except the definitions, which are part of them. Conventions as in Stages 2–3: arbitrary probability spaces, no usual conditions, filtrations indexed by `ℝ≥0`, processes `ℝ → Ω → ℝ`; every series, integral and expectation that appears is asserted genuine (integrability or finiteness in the same statement), probabilities of events not claimed measurable are outer probabilities; the measurable structure on `C(Set.Icc 0 T, FiniteMeasure ℝ)` is the Borel one (the instance used by the frozen statement), never Mathlib's Giry structure on `FiniteMeasure ℝ`. The universe of the probability spaces is arbitrary. All of this section was elaborated (Section 7). Proposed files: `QSSEPtoKPZ/LimitPoints/Prop71.lean`, `QSSEPtoKPZ/WhiteNoise/Prop72.lean`, `QSSEPtoKPZ/Uniqueness/Prop73.lean`, `QSSEPtoKPZ/Uniqueness/MildSolution.lean`, `QSSEPtoKPZ/Uniqueness/Theorem12.lean`.

### 2.1 Definitions

```lean
/-- `γ(t)` for real `t`, `t` projected on `[0,T]`. -/
def pathAt {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t : ℝ) : FiniteMeasure ℝ :=
  if h : 0 ≤ T then γ (Set.projIcc 0 T h t) else 0
/-- `μ(f) = ∫ f dμ`. -/
def pairFM (μ : FiniteMeasure ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, f x ∂(μ : Measure ℝ)
/-- The natural filtration `σ(Y(s) : s ≤ t)` of a path-valued random variable (Borel σ-algebra
of `ℳ₊`), through the canonical filtration `pathFiltrationCan T` of `C([0,T], ℳ₊)`. -/
def pathFiltration (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : Filtration ℝ≥0 mΩ
/-- (7.2): `M^φ(t) = 𝒵(t;φ_t) - φ_0(0) - ∫_0^t 𝒵(s; ∂ₛφ_s + ½ ∂ₓ²φ_s) ds`. -/
def limMart (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  pairFM (pathAt (Y ω) t) (φ t) - φ 0 0 -
    ∫ s in (0 : ℝ)..t, pairFM (pathAt (Y ω) s) (fun x => φt s x + iteratedDeriv 2 (φ s) x / 2)
/-- (7.3): `∫_0^t ∫ Z(s,x)² φ_s(x)² dx ds`. -/
def limBracket (Z : ℝ → ℝ → Ω → ℝ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, ∫ x, Z s x ω ^ 2 * φ s x ^ 2
/-- `liminf_k (μ ⋆ ρ_{1/(k+1)})(x)`, and `0` if infinite (proof of Prop 7.1 (2)). -/
def limDensity (ρ : ℝ → ℝ) (μ : FiniteMeasure ℝ) (x : ℝ) : ℝ :=
  (liminf (fun k : ℕ => ENNReal.ofReal
    (∫ y, rhoEps ρ (1 / ((k : ℝ) + 1)) (x - y) ∂(μ : Measure ℝ))) atTop).toReal
/-- The density `Z(t,x)` of Proposition 7.1 (2). -/
def limField (ρ : ℝ → ℝ) (Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t x : ℝ) (ω : Ω) : ℝ :=
  limDensity ρ (pathAt (Y ω) t) x
/-- `(g_{t-s} ⋆ f)(y)`. -/
def heatConv (r : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x, heatKernel r (y - x) * f x
/-- `Z ∈ ℋ_T` and `Z` satisfies (7.13) for a.e. `t ∈ (0,T]` and all `f ∈ C_c^∞(ℝ)`. -/
structure IsWeakMild (T : ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (S : ℝ → ℝ → Ω → ℝ)
    (Z : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) : Prop where
  measurable : Measurable (uncurryField Z)
  sq_integrable : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂ν < ⊤
  weak : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), ∀ f : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    IsWalshIntegral 𝓖 S ν
      (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω else 0)
      (fun ω => ∫ x, Z t x ω * f x - ∫ x, heatKernel t x * f x)
```
* `limDensity`: the liminf is taken in $[0,\infty]$, so "$0$ if infinite" is `toReal` of `⊤`; the convolutions are genuine (bounded continuous integrand, finite measure).
* `IsWeakMild` is the article's "$Z\in\mathcal H_T$ satisfying (7.13)". Predictability is not required (decision D8″): it is not used by Proposition 7.3, whose statement is therefore stronger. The integrals $\int Z(t,x)f(x)dx$ are genuine for a.e. $(t,\omega)$ by the $L^2$ bound; outside a null set they do not matter (the value of a Walsh integral is only determined up to null sets).

### 2.2 Proposition 7.1 (E)

```lean
theorem prop_7_1 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T : ℝ} (hT : 0 < T)
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ωk : ℕ → Type*} {mΩk : ∀ k, MeasurableSpace (Ωk k)}
    (μ : ∀ k, Measure (Ωk k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩk k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ωk k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ωk k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (Zv : ∀ k, Ωk k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (hZv : ∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
      (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t)
    {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    (hconv : TendstoInDistribution Zv atTop Y μ Pr) :
    (∀ᵐ ω ∂Pr, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0) ∧
    (Measurable[((pathFiltration (mΩ := mΩ) Y).predictable).prod (borel ℝ)]
        (fun p : (ℝ≥0 × Ω) × ℝ => limField ρ Y p.1.1 p.2 p.1.2) ∧
      (∀ t x ω, 0 ≤ limField ρ Y t x ω) ∧
      ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (limField ρ Y t x ω ^ 2)) ∂Pr < ⊤ ∧
      ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (pathAt (Y ω) t : Measure ℝ) =
          volume.withDensity fun x => ENNReal.ofReal (limField ρ Y t x ω)) ∧
    ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T (nullAug Pr (pathFiltration Y)) (limMart Y φ φt)
        (limBracket (limField ρ Y) φ) Pr
```
Reading: $n_k\to\infty$; for each $k$ a realization of the QSSEP on $\mathbb Z$ and a version `Zv k` of $(\mathsf Z_{n_k}(t))_{t\in[0,T]}$ (Stage 3, `prop_5_1_version`); $Y$ is any random element whose law is the limit in distribution of the `Zv k` (decision D6″: a limit point, in the article's sense, is any such $Y$; the statement is about the law of $Y$ only). Then (1); (2) with (7.1) and the predictable density $Z$ = `limField`, for the natural filtration $\mathcal G^0$ (without null sets: $Z$ is a functional of the path); (3) `HasBracket`: $M^\phi$ is a continuous square-integrable martingale for $\mathcal G^0$ augmented by the null sets, with $\langle M^\phi\rangle_t=\int_0^t\int Z^2\phi^2$, for every $\phi\in C_b^{1,3}$ (`IsC13`, decision D6 of Stage 2). `HasBracket` asserts the integrability of $\langle M^\phi\rangle_t$; (7.1) makes the inner integrals genuine for a.e. $(\omega,s)$.

```lean
/-- (7.4): `𝔼 ∫_0^T ‖𝒵(t) ⋆ ρ_ε‖₂² dt ≤ C 2^{16T}`, `C` depending only on `ρ`, for every `ε > 0`. -/
theorem eq_7_4 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ {T : ℝ}, 0 < T → ∀ (n : ℕ → ℝ), (∀ k, 1 ≤ n k) → Tendsto n atTop atTop →
    ∀ {Ωk …} (μ …) (𝓕 …) (B …), (∀ k, IsBrownianFamily …) → ∀ (ψ …), (∀ k, IsWaveFunction ⊤ …) →
    ∀ (Zv …), (versions as above) →
    ∀ {Ω : Type*} {_ : MeasurableSpace Ω} {Pr : Measure Ω} [IsProbabilityMeasure Pr] {Y},
      Measurable Y → TendstoInDistribution Zv atTop Y μ Pr → ∀ {ε : ℝ}, 0 < ε →
      ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (smoothedNormSq (pathAt (Y ω) t : Measure ℝ) (fun _ => 1) ρ ε)) ∂Pr ≤
        ENNReal.ofReal (C * 2 ^ (16 * T))
```
(the elided binders are those of `prop_7_1`; elaborated in full). The space of $\mathcal Z$ is bound after `∃ C` (correction of 13 November 2026: in the first version it came from a `variable` line, so $C$ could depend on it). `smoothedNormSq` is the Stage 2 definition, (6.1).

### 2.3 Proposition 7.2 (E)

```lean
theorem prop_7_2 {Pr : Measure Ω} [IsProbabilityMeasure Pr] {𝒢 : Filtration ℝ≥0 mΩ}
    {T : ℝ} (hT : 0 < T) {Y : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} (hY : Measurable Y)
    (hY0 : ∀ᵐ ω ∂Pr, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0)
    {Z : ℝ → ℝ → Ω → ℝ}
    (hZp : Measurable[(𝒢.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => Z p.1.1 p.2 p.1.2)
    (hZ0 : ∀ t x ω, 0 ≤ Z t x ω)
    (hZ2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (Z t x ω ^ 2)) ∂Pr < ⊤)
    (hdens : ∀ᵐ ω ∂Pr, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z t x ω))
    (hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 T φ φt C →
      HasBracket T 𝒢 (limMart Y φ φt) (limBracket Z φ) Pr)
    {Ω″ : Type*} {m″ : MeasurableSpace Ω″} {ν″ : Measure Ω″} [IsProbabilityMeasure ν″]
    {𝓖″ : Filtration ℝ≥0 m″} {S″ : ℝ → ℝ → Ω″ → ℝ} (hS″ : IsWhiteNoise 𝓖″ S″ ν″) :
    ∃ (𝒢b : Filtration ℝ≥0 (mΩ.prod m″)) (S : ℝ → ℝ → Ω × Ω″ → ℝ),
      (∀ t, (𝒢 t).comap Prod.fst ≤ 𝒢b t) ∧ IsWhiteNoise 𝒢b S (Pr.prod ν″) ∧
      ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ t ∈ Set.Ioc (0 : ℝ) T,
        IsWalshIntegral 𝒢b S (Pr.prod ν″)
          (fun s y ω => if 0 < s ∧ s < t then heatConv (t - s) f y * Z s y ω.1 else 0)
          (fun ω => pairFM (pathAt (Y ω.1) t) f - ∫ x, heatKernel t x * f x)
```
Reading: "let $\mathcal Z$ and $Z$ be as in Proposition 7.1" is rendered by hypotheses equal to the conclusions (1)–(3) of `prop_7_1`, for an arbitrary filtration $\mathcal G$ (so `prop_7_2` does not mention the QSSEP; `prop_7_1` supplies the hypotheses with $\mathcal G$ = natural filtration with null sets). "Possibly after enlarging the probability space" is rendered by the product with an arbitrary space carrying a white noise $S″$ (decision D7″). The conclusion: a filtration $\bar{\mathcal G}$ on the product containing $\mathcal G$, a white noise $S$ (frozen `IsWhiteNoise`: its distribution function, for all times) for $\bar{\mathcal G}$, and (7.8) for all $f\in C_c^\infty$ and $t\in(0,T]$, the Walsh integral being the frozen `IsWalshIntegral`. Hypothesis (1) of Prop 7.1, $\mathcal Z(0)=\delta_0$ (`hY0`), **is needed** (correction of 13 November 2026; the first version of this document claimed the contrary): Step 3 writes $M^\phi(t)$ as a sum of increments of the $M^{\phi-\phi_{s_i}}$, which leaves out $M^\phi(0)=\mathcal Z(0;\phi_0)-\phi_0(0)$, and this is $0$ only because $\mathcal Z(0)=\delta_0$. Without it the statement is false ($\mathcal Z\equiv0$, $Z\equiv0$: $M^\phi\equiv-\phi_0(0)$ is a martingale with bracket $0$, but (7.8) would give $\int g_tf=0$; audit, E1).

### 2.4 Proposition 7.3 (E)

```lean
theorem prop_7_3 {𝓖 : Filtration ℝ≥0 mΩ} {S : ℝ → ℝ → Ω → ℝ} {ν : Measure Ω}
    (hS : IsWhiteNoise 𝓖 S ν) {T : ℝ} (hT : 0 < T) {Z₁ Z₂ : ℝ → ℝ → Ω → ℝ}
    (h₁ : IsWeakMild T 𝓖 S Z₁ ν) (h₂ : IsWeakMild T 𝓖 S Z₂ ν) :
    ∀ᵐ p ∂(ν.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
      Z₁ p.2.1 p.2.2 p.1 = Z₂ p.2.1 p.2.2 p.1
```

### 2.5 The solution of the stochastic heat equation (E)

The article's (7.14) is the equation of the frozen `IsMildSolution`; existence (Chen–Dalang) is not used (1.2 (h)). What the proof uses, for the field $Z$ **given** in the statement:

```lean
/-- (7.15), as a series: `𝔼[Z(t,x)²] = ∑_{k ≥ 1} K^{⋆k}(t,x)`,
`K^{⋆k}(t,x) = 2^{-k} t^{k/2-1} Γ(k/2)⁻¹ g_{t/2}(x)` (its sum is the right side of (7.15)). -/
theorem IsMildSolution.integral_sq (hS : IsWhiteNoise 𝓖 S ν) (hZ : IsMildSolution 𝓖 S Z ν)
    {t x : ℝ} (ht : 0 < t) :
    MemLp (Z t x) 2 ν ∧ HasSum (fun k : ℕ => (2 : ℝ) ^ (-((k : ℝ) + 1)) *
        t ^ (((k : ℝ) + 1) / 2 - 1) / Real.Gamma (((k : ℝ) + 1) / 2) * heatKernel (t / 2) x)
      (∫ ω, Z t x ω ^ 2 ∂ν)

/-- After (7.15): a solution of (1.13) has a jointly measurable version, which belongs to `ℋ_T`
and satisfies (7.13) (stochastic Fubini). -/
theorem IsMildSolution.isWeakMild (hS : IsWhiteNoise 𝓖 S ν) (hZ : IsMildSolution 𝓖 S Z ν)
    {T : ℝ} (hT : 0 < T) :
    ∃ Z' : ℝ → ℝ → Ω → ℝ, (∀ᵐ ω ∂ν, ∀ t x, 0 < t → Z' t x ω = Z t x ω) ∧
      IsWeakMild T 𝓖 S Z' ν
```
Decision D9″: (7.15) in series form (the closed form needs the Mittag-Leffler identity $\sqrt\pi\sum_{k\ge1}a^{k-1}/\Gamma(k/2)=1+\sqrt\pi\,a\,e^{a^2}\mathrm{erfc}(-a)$, $a=\sqrt t/2$; checked by hand, 200–400 more lines if wanted).

### 2.6 Theorem 1.2 for $L_n=\infty$ (E), and the companions

```lean
theorem main_theorem_top
    (n : ℕ → ℝ) (hn₁ : ∀ k, 1 ≤ n k) (hn : Tendsto n atTop atTop)
    {Ωk : ℕ → Type*} {mΩk : ∀ k, MeasurableSpace (Ωk k)}
    (μ : ∀ k, Measure (Ωk k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩk k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ωk k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ωk k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (ν : Measure Ω') [IsProbabilityMeasure ν]
    (𝓖 : Filtration ℝ≥0 mΩ') (S : ℝ → ℝ → Ω' → ℝ) (hS : IsWhiteNoise 𝓖 S ν)
    (Z : ℝ → ℝ → Ω' → ℝ) (hZ : IsMildSolution 𝓖 S Z ν) (T : ℝ) (hT : 0 < T) :
    ∃ (𝒵n : ∀ k, Ωk k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
      (𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)),
      (∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵n k ω t : Measure ℝ) = rescaledMeasure ⊤ (n k) (density (ψ k) ω) t) ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T,
        (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      TendstoInDistribution 𝒵n atTop 𝒵 μ ν
```
This is `main_theorem` with `L k = ⊤` (the hypotheses `hL₁`, `hL` dropped; with `L k = ⊤` the first holds and the second reads $\infty/n^{3/4}\to\infty$, true by `tendsto_size_top` of `Checks.lean`). In Stage 5, `main_theorem` for general $L$ is reduced to it by Section 8.

Also for approval (T0″ writes them; the statements of the first three are copied verbatim from `Companions.lean`, the merge script compares them with `pp.all`):
* `walsh_ae_eq`, `walsh_isometry` (W), `isMildSolution_unique'` (U3);
* `IsMildSolution.nonneg_of_isWaveFunction`: if there are a probability space, a Brownian family and a wave function on $\mathbb Z$, then every mild solution is almost surely nonnegative on $(0,\infty)\times\mathbb R$ (P is this plus E1 for $L=\infty$, Stage 5).

---

## 3. Generic infrastructure (not about QSSEP)

Conventions as in Stages 2–3: `module`, `public import`, `@[expose] public section`, `noncomputable section`, `namespace QSSEPtoKPZ`. Proposed folders: `QSSEPtoKPZ/LimitPoints/` (package I), `QSSEPtoKPZ/WhiteNoise/` (J), `QSSEPtoKPZ/Uniqueness/` (K). The signatures below marked "elaborated" were checked (Section 7); the others are sketched and fixed by I0″.

### 3.1 What Mathlib v4.35.0 and the library have (checked)

* **Mathlib.** `Measure.infinitePi` (products of probability measures over any index type); `measure_limsup_atTop_eq_zero` (Borel–Cantelli); `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`, `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` (portmanteau; need `HasOuterApproxClosed`, available for pseudo-metrizable spaces); `Measure.countable_meas_pos_of_disjoint_iUnion` (spheres of positive mass are countably many); `isCompact_closure_of_isTightMeasureSet` (Prokhorov); `tendsto_of_subseq_tendsto`; `TendstoInDistribution` and `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`; `Filtration.predictable` (`Probability/Process/Predictable.lean`: the predictable σ-algebra on `ℝ≥0 × Ω`, generated by `{0} × A` and `(s,t] × A`); `Measurable.exists_eq_measurable_comp` (Doob–Dynkin, target standard Borel, e.g. `ℝ`); `map_eq_iff_forall_finset_map_restrict_eq` (laws of processes indexed by any type are determined by finite-dimensional laws); `Measure.ext_of_charFun`, `indepFun_iff_charFun_prod` (characteristic functions); `gaussianReal`, `IsGaussian`, `gaussianReal_conv_gaussianReal`; `condExp_indep_eq`; `exists_measure_symmDiff_lt_of_generateFrom_isSetRing` (approximation of sets of a generated σ-algebra by a ring, for density of simple integrands); `MemLp.induction_dense`; `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` (Lebesgue differentiation); `Complex.Gamma_mul_Gamma_eq_betaIntegral` (Beta integral, complex form); `Continuous.isClosedEmbedding` (compact to Hausdorff); `Kernel.exists_measurable_map_eq_unitInterval` (not needed by D1″).
* **Missing in Mathlib**: Skorokhod's representation; Kolmogorov extension and existence of Brownian motion or white noise; completeness/Polishness of `FiniteMeasure ℝ` (Lusin–Souslin `measurableSet_range_of_continuous_injective` needs a Polish source); Lévy's characterization; any stochastic integral; BDG.
* **Library** (Stages 2–3, to reuse): `IsCL2Mart`, `HasBracket`, `HasCovariation`, `nullAug` and its lemmas (`isCL2Mart_nullAug_iff`, `hasBracket_nullAug_iff`, `HasBracket.congr`, `.mono_horizon`, `.const_mul`, `IsCL2Mart.add`), stopping (`hitTime`, `isStoppingTime_hitTime`, `HasBracket.stopped`, `IsCL2Mart.condExp_stopped`), Doob (`IsCL2Mart.lintegral_iSup_sq_le`, `IsCL2Mart.measure_exists_ge_le`); Stage 3: `tightEmb`, `isEmbedding_tightEmb`, the instances `SecondCountableTopology`, `MetrizableSpace` of `FiniteMeasure ℝ`, `borel_pathFiniteMeasure_eq_iSup_tightEmb`, `measurable_pathFiniteMeasure_iff_tightEmb`, `bumpTest`, `isCompact_tightCoshBall`, `prop_5_1`, `prop_5_1_isTight`, `prop_5_1_version`; Stage 2: `prop_3_1`, `prop_3_1_generator`, `hasBracket_WN`, `prop_4_3_bounds`, `prop_6_1`, `prop_6_2`, `smoothedNormSq_eq`, `rescaledMeasure_eq`, `varrhoN_bounds`; `Checks.lean`: `IsWalshIntegral.memLp_and_integral_eq_zero`, `integral_sq_rectMass`, `heatKernel_eq_gaussianPDFReal`, `integral_sheMeasure`, `tendsto_size_top`. The Itô integral of package C (Brownian families) is not reused directly: the white noise of `IsWhiteNoise` has no continuity clause, so its spatial increments are not an `IsBrownianFamily`; its elementary-integrand machinery (`ElemGrid`, `ElemClip`) is a model for G4.

### 3.2 I: path space, Skorokhod, densities

```lean
/-- (G1, elaborated) Skorokhod's representation along a subsequence. -/
theorem skorokhod_subseq {S : Type u} [TopologicalSpace S] [TopologicalSpace.MetrizableSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    {P : ℕ → ProbabilityMeasure S} {Plim : ProbabilityMeasure S} (h : Tendsto P atTop (𝓝 Plim)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Pr : Measure Ω)
      (_ : IsProbabilityMeasure Pr) (X : ℕ → Ω → S) (Y : Ω → S),
      (∀ k, Measurable (X k)) ∧ Measurable Y ∧
      (∀ k, Pr.map (X k) = (P (φ k) : Measure S)) ∧ Pr.map Y = (Plim : Measure S) ∧
      ∀ᵐ ω ∂Pr, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω))

/-- (G2, elaborated) The canonical filtration of `C([0,T], ℳ₊)`. -/
def pathFiltrationCan (T : ℝ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace
    C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))   -- σ(γ(s) : s ≤ t), Borel σ-algebra on ℳ₊
/-- (G2, elaborated) Martingale properties for the natural filtration of `X` ↔ for the canonical
filtration under the law of `X`. -/
theorem hasBracket_map_iff [IsProbabilityMeasure μ] {X : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)}
    (hX : Measurable X) {m a : ℝ → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) → ℝ}
    (hm : ∀ t, Measurable (m t)) (ha : ∀ t, Measurable (a t)) :
    HasBracket T (nullAug μ (pathFiltration X)) (fun t ω => m t (X ω)) (fun t ω => a t (X ω)) μ ↔
      HasBracket T (nullAug (μ.map X) (pathFiltrationCan T)) m a (μ.map X)
/-- (G2, elaborated) Hitting times of uniformly convergent continuous functions converge at
levels where the limit does not touch the level without crossing it. -/
theorem tendsto_hitLevel (hg : ContinuousOn g (Set.Icc 0 T))
    (hfg : TendstoUniformlyOn f g atTop (Set.Icc 0 T))
    (hK : sInf ({t ∈ Set.Icc 0 T | K ≤ g t} ∪ {T}) = sInf ({t ∈ Set.Icc 0 T | K < g t} ∪ {T})) :
    Tendsto (fun k => sInf ({t ∈ Set.Icc 0 T | K ≤ f k t} ∪ {T})) atTop
      (𝓝 (sInf ({t ∈ Set.Icc 0 T | K ≤ g t} ∪ {T})))
```
plus (G2): measurability of `γ ↦ pathAt γ t`, of pairings and of `(t, γ) ↦ pairFM (pathAt γ t) f`; "for a measurable process with continuous paths, the levels $L$ where $\inf\lbrace V\ge L\rbrace\ne\inf\lbrace V>L\rbrace$ with positive probability are countable"; hitting times of adapted continuous path functionals are stopping times of `nullAug (pathFiltrationCan T)`; the variant of `hasBracket_map_iff` for `IsCL2Mart` and for the comparison of two spaces with the same law (`Pr.map X = Pr'.map X'`), used to transfer Proposition 7.1 from the Skorokhod space to an arbitrary `Y`.

```lean
/-- (G3, elaborated) L² density criterion and identification with `limDensity`. -/
theorem withDensity_limDensity_of_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {μ : FiniteMeasure ℝ}
    {C : ℝ} (hC : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      |∫ x, f x ∂(μ : Measure ℝ)| ≤ C * (∫ x, f x ^ 2) ^ (1 / 2 : ℝ)) :
    MemLp (limDensity ρ μ) 2 volume ∧
      (μ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (limDensity ρ μ x)
```
plus (G3): for a finite measure with an $L^2$ density $u$, $\lVert\mu\ast\rho_\varepsilon\rVert_2\le\lVert u\rVert_2$ and $\mu\ast\rho_\varepsilon\to u$ in $L^2$ and a.e. (Lebesgue differentiation); continuity and adaptedness of $(t,x)\mapsto(\gamma(t)\ast\rho_\varepsilon)(x)$, hence predictability of `limField`; continuity of $\mu\mapsto\lVert(\varphi\mu)\ast\rho_\varepsilon\rVert_2^2$ on `FiniteMeasure ℝ` (by (6.1), integral of a bounded continuous function against $\mu\otimes\mu$).

### 3.3 J: white noise, Walsh integrals, Lévy, martingale measures

```lean
/-- (G5, elaborated) Noise coordinates `(t,a,b) ↦ ξ((0,t] × (a,b])`. -/
def noiseMap (S : ℝ → ℝ → Ω → ℝ) (ω : Ω) : ℝ≥0 × ℝ × ℝ → ℝ :=
  fun p => rectMass S 0 p.1 p.2.1 p.2.2 ω
theorem IsWhiteNoise.map_noiseMap_eq (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂) :
    ν₁.map (noiseMap S₁) = ν₂.map (noiseMap S₂)
/-- (G5, elaborated) The natural filtration of the noise, with the null sets. -/
def noiseFiltration (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) : Filtration ℝ≥0 mΩ
```
plus (G5): the increments after $s$ (all rectangles in $(s,\infty)\times\mathbb R$) are jointly independent of $\mathcal G_s$ (from `indep_past` for each $t$, adaptedness and a $\pi$-system induction over time slabs); $\mathbb E[c\mid\mathcal N_\infty]=\mathbb E[c\mid\mathcal N_s]$ for $c$ $\mathcal G_s$-measurable. The law of `noiseMap` is determined because each finite family of rectangle masses is a linear image of a grid of cells (algebraic additivity of `rectMass`), and the cells are independent centred Gaussians (`indep` within a time slab, `indep_past` across slabs).

```lean
-- (G4a/G4b, elaborated)
theorem IsWalshIntegral.const_mul (hX : IsWalshIntegral 𝓖 S ν h X) (c : ℝ) :
    IsWalshIntegral 𝓖 S ν (fun s y ω => c * h s y ω) (fun ω => c * X ω)
theorem IsWalshIntegral.congr_ae (hS : IsWhiteNoise 𝓖 S ν) (hX : IsWalshIntegral 𝓖 S ν h X)
    (hh : uncurryField h =ᵐ[ν.prod volume] uncurryField h') (hXX : X =ᵐ[ν] X') :
    IsWalshIntegral 𝓖 S ν h' X'
theorem exists_isWalshIntegral (hS : IsWhiteNoise 𝓖 S ν)
    (hp : Measurable[(𝓖.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2)
    (hneg : ∀ s y ω, s ≤ 0 → h s y ω = 0) (h2 : MemLp (uncurryField h) 2 (ν.prod volume)) :
    ∃ X : Ω → ℝ, IsWalshIntegral 𝓖 S ν h X
```
plus: monotonicity in the filtration; the elementary isometry for finite sums of blocks (refinement to a common grid, independence of cells from the past); W by approximating every derivation by finite block sums (induction on `IsWalshIntegral`); the library copies `walsh_ae_eq`, `walsh_isometry` of the companions. `congr_ae` comes from the limit rule with a constant sequence.

```lean
-- (G6, elaborated; corrected 13 November 2026) Projection onto the noise, transfer.
def noiseRefMeasure (ν : Measure Ω) : Measure (Ω × ℝ × ℝ) :=
  ν.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))
def noiseProj (S : ℝ → ℝ → Ω → ℝ) (ν : Measure Ω) (h : ℝ → ℝ → Ω → ℝ) (s y : ℝ) (ω : Ω) : ℝ :=
  ((noiseRefMeasure ν)[uncurryField h | noiseProdSigma S ν]) (ω, s, y)  -- 𝒩_∞ ⊗ 𝓑(ℝ²)
theorem IsWalshIntegral.condExp_noise (hS : IsWhiteNoise 𝓖 S ν)
    (hX : IsWalshIntegral 𝓖 S ν h X) :
    IsWalshIntegral (noiseFiltration S ν) S ν (noiseProj S ν h)
      (ν[X | ⨆ t, noiseFiltration S ν t])
theorem IsWalshIntegral.transfer (h₁ : IsWhiteNoise 𝓖₁ S₁ ν₁) (h₂ : IsWhiteNoise 𝓖₂ S₂ ν₂)
    {H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ} {Ξ : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ}
    (hH : Measurable fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2) (hΞ : Measurable Ξ)
    (hW : IsWalshIntegral 𝓖₁ S₁ ν₁ (fun s y ω => H (noiseMap S₁ ω) s y) (fun ω => Ξ (noiseMap S₁ ω))) :
    IsWalshIntegral 𝓖₂ S₂ ν₂ (fun s y ω => H (noiseMap S₂ ω) s y) (fun ω => Ξ (noiseMap S₂ ω))
```
`condExp_noise` uses the conditional expectation on `Ω × ℝ × ℝ` for the **probability** measure $\nu\otimes\gamma\otimes\gamma$ ($\gamma$ the standard Gaussian) and the σ-algebra $\mathcal N_\infty\otimes\mathcal B(\mathbb R^2)$. (Correction of 13 November 2026: the first version used $\nu\otimes\mathrm{Leb}^2$ and claimed that σ-finiteness of the trim suffices. It does not: a Walsh integrand is in $L^2$ but not necessarily in $L^1$ of this infinite measure, and Mathlib's `condExp` of a non-integrable function is $0$; e.g. $h(s,y)=\mathbf 1_{(0,1]}(s)\mathbf 1_{[0,\infty)}(y)/(1+y)$ has $\lVert h\rVert_2=1$, its Walsh integral is a non-zero noise-measurable variable, and the old statement made it the integral of $0$.) Every $h\in L^2(\nu\otimes\mathrm{Leb}^2)$ is integrable for $\nu\otimes\gamma^2$, the two measures have the same null sets, and the density is $\mathcal B(\mathbb R^2)$-measurable, so this conditional expectation is the orthogonal projection of $L^2(\nu\otimes\mathrm{Leb}^2)$ onto the $\mathcal N_\infty\otimes\mathcal B$-measurable fields (G6 proves the $L^2(\nu\otimes\mathrm{Leb}^2)$ contraction `noiseProj_memLp`, `noiseProj_add`, `noiseProj_mul_left`, `noiseProj_ae_eq_self` and the conditional Fubini `condExp_integral_noiseProj`, which K4 uses). Fiberwise property: for a.e. $(s,y)$ it is $\mathbb E[h(s,y)\mid\mathcal N_\infty]$. `transfer`: first `condExp_noise` on $\Omega_1$ (which fixes noise functions, `noiseProj_ae_eq_self`), then induction on the derivation, each node's integrand and value being factorized through `noiseMap` (Doob–Dynkin, `Measurable.exists_eq_measurable_comp`), statements quantified over all factorizations; a.e. identities move between the spaces by `map_noiseMap_eq`.

```lean
-- (G7a, elaborated) Lévy's characterization, set-integral form.
theorem levy_setIntegral [IsProbabilityMeasure μ] {N : ℝ → Ω → ℝ} {c T : ℝ} (hc : 0 ≤ c)
    (hN : HasBracket T 𝓖 N (fun t _ => c * t) μ) {s t : ℝ≥0} (hst : s ≤ t) (htT : (t : ℝ) ≤ T)
    (u : ℝ) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Complex.exp (((u * (N t ω - N s ω) : ℝ) : ℂ) * Complex.I) ∂μ =
      (Real.exp (-(c * u ^ 2 * ((t : ℝ) - s) / 2)) : ℂ) * (μ.real A : ℂ)
-- (G7b, elaborated) A family of martingales indexed by intervals with the white-noise brackets.
theorem isWhiteNoise_of_martingales [IsProbabilityMeasure μ] {S : ℝ → ℝ → Ω → ℝ}
    (hS : ∀ t x, Measurable[𝓖 t.toNNReal] (S t x)) (h0 : ∀ x ω, S 0 x ω = 0)
    (hcov : ∀ (T : ℝ) (a b a' b' : ℝ), a ≤ b → a' ≤ b' →
      HasCovariation T 𝓖 (fun t ω => S t b ω - S t a ω) (fun t ω => S t b' ω - S t a' ω)
        (fun t _ => t * (volume (Set.Ioc a b ∩ Set.Ioc a' b')).toReal) μ) :
    IsWhiteNoise 𝓖 S μ
```
Proof of G7a by discretization (`PLAN.md`): stop at $\tau_R$ (first time $\lvert N-N_s\rvert\ge R$), cut $[s,t]$ into $m$ pieces, expand $\exp(iu\Delta N_k+\frac{cu^2}2\Delta t_k)$ to third order; $\mathbb E[\Delta N_k^2\mid\mathcal G_{t_k}]=c\,\mathbb E[\Delta(t\wedge\tau_R)_k\mid\mathcal G_{t_k}]$; the remainders are bounded by $\mathbb E[\max_k\lvert\Delta N_k\rvert\sum_k\Delta N_k^2]\to0$, using $\mathbb E[(\sum_k\Delta N_k^2)^2]\le CR^2\mathbb E\sum_k\Delta N_k^2$ for a martingale with increments bounded by $2R$; then $R\to\infty$. G7b: Cramér–Wold (linear combinations have bracket $\sum\lambda_i^2c_it$ by bilinearity of `HasCovariation`), characteristic functions conditioned on $A\in\mathcal G_s$.

```lean
-- (G8, elaborated) The martingale-measure integral h · M, intensity q = Z².
inductive IsMMIntegral (T : ℝ) (𝒢 : Filtration ℝ≥0 mΩ) (q : ℝ → ℝ → Ω → ℝ)
    (M : (ℝ → ℝ) → ℝ → Ω → ℝ) (μ : Measure Ω) : (ℝ → ℝ → Ω → ℝ) → (ℝ → Ω → ℝ) → Prop
  | block (s t : ℝ≥0) (hst : s ≤ t) (a : Ω → ℝ) (φ : ℝ → ℝ) (C : ℝ)
      (hφ : IsC13 T (fun _ => φ) (fun _ _ => 0) C) (ha : Measurable[𝒢 s] a)
      (hab : ∃ K, ∀ ω, |a ω| ≤ K) :
      IsMMIntegral T 𝒢 q M μ (fun r x ω => if (s : ℝ) < r ∧ r ≤ t then a ω * φ x else 0)
        (fun r ω => a ω * (M φ (min r t) ω - M φ (min r s) ω))
  | add …   -- sums
  | limit … -- L²(q dℙ dr dx) for integrands (limit predictable), L²(ℙ; sup_{r ≤ T}) for
            -- processes, limit continuous and a.e. strongly measurable at each r ∈ [0,T]
theorem IsMMIntegral.hasCovariation (hq : predictable) (hq0 : ∀ r x ω, 0 ≤ q r x ω)
    (hq1 : 𝔼 ∫_0^T ∫ q < ∞)
    (hM : ∀ {φ ψ C C'}, IsC13 T (fun _ => φ) (fun _ _ => 0) C → IsC13 T (fun _ => ψ) (fun _ _ => 0) C' →
      HasCovariation T 𝒢 (M φ) (M ψ) (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * φ x * ψ x) μ)
    (hX : IsMMIntegral T 𝒢 q M μ h X) (hX' : IsMMIntegral T 𝒢 q M μ h' X') :
    HasCovariation T 𝒢 X X' (fun t ω => ∫ r in (0 : ℝ)..t, ∫ x, q r x ω * h r x ω * h' r x ω) μ
theorem exists_isMMIntegral (hq : predictable) (hq0) (hq1 : 𝔼 ∫_0^T ∫ q < ∞) (hM : …)
    (hh : predictable) (hh2 : 𝔼 ∫_0^T ∫ h² q < ∞) : ∃ X, IsMMIntegral T 𝒢 q M μ h X
```
(7.10) is `IsMMIntegral.hasCovariation`. (Corrections of 13 November 2026: without the measurability of the limit process the `limit` rule accepts, through the lower integral, an error that is not a.s. $0$ — on `Bool` with the trivial σ-algebra, zero intensity, $M=0$, $h=0$, the process $X(t,\mathrm{true})=t$, $X(t,\mathrm{false})=0$ would be "$0\cdot M$" — so `hasCovariation` and `ae_eq` would be false; `hq1` makes the Bochner integrals of the bracket genuine.) G8b: density of the blocks $a\mathbf 1_{(s,t]}\varphi$ ($\varphi\in C_b^3$) in $L^2(q\,d\mathbb P\,dr\,dx)$ restricted to predictable fields: indicators of predictable rectangles are approximated by sets of the generating ring (`exists_measure_symmDiff_lt_of_generateFrom_isSetRing`, finite measure $q\,d\mathbb P\,dr\,dx$ by (7.1)), and $\mathbf 1_B$ by smooth bumps in $L^2$ of a finite measure on $\mathbb R$.

(G9) **Enlargement by a product**: on $(\Omega\times\Omega″,\mathbb P\otimes\nu″)$ with $\bar{\mathcal G}_t=$ `nullAug` of $\mathcal G_t\otimes\mathcal G″_t$: `HasBracket`/`HasCovariation` for $\mathcal G$ lift (composition with `Prod.fst`); `IsWhiteNoise` for $\mathcal G″$ lifts; a martingale of the first factor and one of the second have covariation $0$; Walsh integrals against $S″$ of $\mathcal G$-predictable integrands (needed for $\int\int k\mathbf 1_{Z=0}\xi'$) via `exists_isWalshIntegral`.

### 3.4 K: heat kernel, Volterra, uniqueness in law

(G10a) $\int g_r^2=(4\pi r)^{-1/2}$; $g_a\ast g_b=g_{a+b}$; $\lVert g_r\ast f\rVert_\infty\le\lVert f\rVert_\infty$, $\lVert g_r\ast f\rVert_2\le\lVert f\rVert_2$; $K^{\ast k}(t,x)=2^{-k}t^{k/2-1}\Gamma(k/2)^{-1}g_{t/2}(x)$ (space convolution of Gaussians, Beta integral); $K^{\ast k}\le\varepsilon_k(T)K$ on $(0,T]$ with $\varepsilon_k(T)\to0$; the Volterra lemma: $F\in L^1[0,T]$, $F\ge0$, $F(t)\le c\int_0^t(t-s)^{-1/2}F(s)ds$ a.e. $\Rightarrow F=0$ a.e. (G10b) for $f\in C_c^\infty$ and $t\in(0,T]$, the function of Step 4 of Prop 7.2 is `IsC13 T` with $\partial_s\phi+\frac12\partial_x^2\phi=0$ on $[0,t]$, $\phi_t=f$, $\phi_0(0)=\int g_tf$.

```lean
-- (K4, elaborated) Uniqueness in law for (7.13).
theorem IsWeakMild.exists_noise_functional {T : ℝ} (hT : 0 < T) (hS : IsWhiteNoise 𝓖 S ν)
    (hZ : IsWeakMild T 𝓖 S Z ν) :
    ∃ H : (ℝ≥0 × ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ,
      Measurable (fun p : (ℝ≥0 × ℝ × ℝ → ℝ) × ℝ × ℝ => H p.1 p.2.1 p.2.2) ∧
      ∀ {Ω₂ : Type u} {m₂ : MeasurableSpace Ω₂} {𝓖₂ : Filtration ℝ≥0 m₂}
        {S₂ : ℝ → ℝ → Ω₂ → ℝ} {ν₂ : Measure Ω₂} {Z₂ : ℝ → ℝ → Ω₂ → ℝ},
        IsWhiteNoise 𝓖₂ S₂ ν₂ → IsWeakMild T 𝓖₂ S₂ Z₂ ν₂ →
        ∀ᵐ p ∂(ν₂.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume)),
          Z₂ p.2.1 p.2.2 p.1 = H (noiseMap S₂ p.1) p.2.1 p.2.2
-- (K5, elaborated) The SHE side of the end of Section 7.
theorem exists_sheVersion_map_eq (hS₁ : IsWhiteNoise 𝓖₁ S₁ P₁) (hT : 0 < T) (hY : Measurable Y)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ K, IsCompact K ∧ P₁ (Y ⁻¹' Kᶜ) ≤ ENNReal.ofReal ε)
    (hY0 : ∀ᵐ ω ∂P₁, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0)
    (hZ₁ : IsWeakMild T 𝓖₁ S₁ Z₁ P₁)
    (hdens : ∀ᵐ ω ∂P₁, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (pathAt (Y ω) t : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (Z₁ t x ω))
    (hS : IsWhiteNoise 𝓖 S ν) (hZ : IsMildSolution 𝓖 S Z ν) :
    ∃ 𝒵 : Ω' → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable 𝒵 ∧
      (∀ᵐ ω ∂ν, ∀ t : Set.Icc (0 : ℝ) T, (𝒵 ω t : Measure ℝ) = sheMeasure (fun s x => Z s x ω) t) ∧
      ν.map 𝒵 = P₁.map Y
```
In `exists_noise_functional` the universe of `Ω₂` is a separate universe variable of the theorem (instantiated at each use: the Skorokhod space lives in `Type`, $\Omega'$ in an arbitrary universe).

### 3.5 QSSEP infrastructure (package I, sample)

```lean
/-- (Q1a, elaborated) The atom of `γ(t)` at `y_n(t,x)`; equals `𝔷_n(t,x)` on the version. -/
def atomPath (n : ℝ) {T : ℝ} (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) (t : ℝ) (x : ℤ) : ℝ :=
  ((pathAt γ t : Measure ℝ) {rescaledPosition n t x}).toReal
theorem measurable_atomPath (n : ℝ) {T : ℝ} (t : ℝ) (x : ℤ) :
    Measurable fun γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) => atomPath n γ t x
```
With it, path versions `WNpath`, `ENpath`, `QNpath`, `MNpath` of `WN`, `EN`, `QN`, `MN` (same formulas with `atomPath` in place of `zN`), their joint measurability in $(t,\gamma)$, and the identities "almost surely, for all $t\in[0,T]$, `MNpath n φ φt (Zv ω) t = MN n ψ φ φt t ω`" etc. Then (Q1b), for $P_n$ = law of `Zv` (any version): (4.8), (6.2), Prop 3.1 (2)–(3) and Prop 6.2 under $P_n$; `HasBracket T (nullAug Pn (pathFiltrationCan T)) MNpath QNpath Pn` (via `hasBracket_map_iff` and the adaptedness of the version, `exists_tiltedPath_version` of Stage 3); measurability of the events of Prop 6.2 on the path space (supremum over rational $t$), so that bounds move between spaces as equalities of laws, not as outer-measure inequalities.

---

## 4. Task breakdown

Method of Stages 2–3 (`docs/task-rules.md`): one Opus 5.5 agent per task, fresh context, own worktree, checked by `scripts/task_merge.sh` and merged by the main session. Tasks may use interface statements of other tasks while still `sorry`. Sizes are lines of Lean to write (k = thousands).

| Id | Files (under `QSSEPtoKPZ/`) | Content | Uses | Size (k) |
|---|---|---|---|---|
| **T0″** | `LimitPoints/Prop71.lean`, `WhiteNoise/Prop72.lean`, `Uniqueness/{Prop73,MildSolution,Theorem12}.lean`; `docs/stage4-statements.md` + PDF | Section 2 with `sorry`, definitions complete; companion copies | Stages 2–3 | 0.3–0.5 |
| **I0″** | all files of Section 3 (signatures, definitions complete, proofs `sorry`); `docs/stage4-interfaces.md` | frozen interfaces | — | 0.5–0.8 |
| G1 | `LimitPoints/Skorokhod.lean`, `SkorokhodPartition.lean` | partitions into continuity sets, coupling, `infinitePi`, Borel–Cantelli | Mathlib | 0.8–1.2 |
| G2 | `LimitPoints/PathSpace.lean`, `PathMart.lean`, `HitLevel.lean` | canonical filtration, `hasBracket_map_iff` and variants, hitting times, countably many bad levels | Stage 3 H2 | 0.6–1.0 |
| G3 | `LimitPoints/Density.lean`, `Mollify.lean` | L² density criterion, Lebesgue differentiation for mollifiers, predictability, continuity of smoothed norms | Stage 2 (6.1) | 0.6–1.0 |
| G4a | `WhiteNoise/WalshBasic.lean`, `WalshElem.lean` | algebra of `IsWalshIntegral`, elementary isometry | Checks | 0.6–0.9 |
| G4b | `WhiteNoise/WalshIsometry.lean`, `WalshExists.lean` | W (isometry, ae_eq), `exists_isWalshIntegral`, companion copies | G4a | 0.6–0.9 |
| G5 | `WhiteNoise/NoiseLaw.lean`, `NoiseFiltration.lean` | `noiseMap`, law determined, future independent of past, conditional expectation lemma | — | 0.6–0.9 |
| G6 | `WhiteNoise/Projection.lean`, `Transfer.lean` | fiberwise conditional expectation on Ω × ℝ², `condExp_noise`, `transfer` | G4, G5 | 0.7–1.1 |
| G7a | `WhiteNoise/Levy.lean` | Lévy, one dimension | Stage 2 martingales | 0.6–0.9 |
| G7b | `WhiteNoise/LevyMulti.lean` | finite families, `isWhiteNoise_of_martingales` | G7a | 0.4–0.7 |
| G8a | `WhiteNoise/MMIntegral.lean` | `IsMMIntegral`, covariation (7.10), linearity, a.e. uniqueness | Covariation | 0.6–0.9 |
| G8b | `WhiteNoise/MMExists.lean` | density of simple integrands, `exists_isMMIntegral` | G8a | 0.5–0.8 |
| G9 | `WhiteNoise/Product.lean` | enlargement by a product | G4b | 0.4–0.7 |
| G10a | `Uniqueness/HeatKernel.lean`, `Volterra.lean` | Gaussian identities, $K^{\ast k}$, Volterra lemma | Checks | 0.6–1.0 |
| G10b | `Uniqueness/HeatTest.lean` | the test function of Step 4 is `IsC13` | G10a | 0.4–0.6 |
| K1 | `Uniqueness/Prop73.lean` | **Prop 7.3** | G4, G10a | 0.4–0.7 |
| K2 | `Uniqueness/SecondMoment.lean` | joint version, (7.15) series, $\mathcal H_T$, **U3** | G4, G10a | 0.6–1.0 |
| K3 | `Uniqueness/StochFubini.lean` | `IsMildSolution.isWeakMild` | K2, G4 | 0.5–0.8 |
| K4 | `Uniqueness/NoiseFunctional.lean` | `exists_noise_functional` | K1, G5, G6 | 0.4–0.7 |
| K5 | `Uniqueness/SheVersion.lean` | `exists_sheVersion_map_eq` (σ-compact range, positivity, $t=0$) | K3, K4, G2, Stage 3 | 0.6–1.0 |
| J1 | `WhiteNoise/Prop72Noise.lean` | **Prop 7.2** Steps 1–2: $\xi$, Lévy, (7.9)–(7.11) | G7b, G8, G9 | 0.6–1.0 |
| J2 | `WhiteNoise/Prop72.lean` | Steps 3–4: (7.12), (7.8) | J1, G10b, G4b | 0.5–0.9 |
| Q1a | `LimitPoints/PathFunctionals.lean` | atoms, path versions of $\mathcal W_n,\mathcal E_n,Q_n,M_n^\phi$, smoothed norms; identities on the version | Stages 2–3, G2 | 0.6–0.9 |
| Q1b | `LimitPoints/PrelimitLaw.lean` | (4.8), (6.2), Prop 3.1, Prop 6.2, brackets under $P_n$ | Q1a, G2 | 0.6–0.9 |
| Q2 | `LimitPoints/Prop71Density.lean` | **Prop 7.1 (1), (2)**, (7.4) | G1, G3, Q1b | 0.5–0.8 |
| Q3 | `LimitPoints/Prop71Mart.lean`, `ConvQ.lean` | (7.5), martingale property, (7.6) | G1, G2, Q1b, Q2 | 0.8–1.2 |
| Q4 | `LimitPoints/Prop71Bracket.lean`, `Prop71.lean` | bracket by localization, local → true martingale, transfer to any $Y$; **Prop 7.1** | Q3, G2 | 0.6–1.0 |
| Q5a | `Uniqueness/WeakMildBridge.lean` (added 13 November 2026) | `isWeakMild_prod_of_eq_7_8`: (7.8) + density $\Rightarrow$ `IsWeakMild` on $\Omega\times\Omega''$ | G2, G4b | 0.3–0.5 |
| Q5 | `Uniqueness/Theorem12.lean` | **`main_theorem_top`**, `nonneg_of_isWaveFunction` | all | 0.5–0.8 |
| E2 (optional) | `WhiteNoise/Existence.lean` | **E2**: isonormal Gaussian process on $L^2(\mathbb R_+\times\mathbb R)$ from i.i.d. $N(0,1)$ (`infinitePi`), Hilbert basis | G5 | 0.8–1.4 |

**Waves** (at most six agents at once; dependencies are on interfaces, so the order mostly limits the risk of an interface found false):

* Wave 0: T0″ and I0″ (two agents). T0″ goes to the author.
* Wave 1 (after I0″ is reviewed; generic, no approval needed): G1, G2, G3, G4a, G5, G10a.
* Wave 2: G4b, G6, G7a, G8a, G9, G10b.
* Wave 3 (after approval of T0″): G7b, G8b, K1, K2, Q1a, Q1b.
* Wave 4: K3, K4, J1, Q2, Q3 (and E2 if decided).
* Wave 5: K5, J2, Q4, Q5a.
* Wave 6: Q5.

**Critical path**: I0″ → G4a → G4b → G6 → K4 → K5 → Q5 (seven tasks after the interfaces), with two near-critical chains G7a → G7b → J1 → J2 → Q5 and Q1a → Q1b → Q3 → Q4 → Q5. Every task: no new `sorry`, standard axioms only except through other tasks' interfaces (to be listed); distinctive names (`skoro…`, `walsh…`, `noise…`, `levy…`, `mm…`, `heat…`, `path…`), private auxiliaries.

Notes for specific tasks:

* **G1**: the space has no metric instance; use `TopologicalSpace.metrizableSpaceMetric S` locally. Samples for the coupling: index the cells of level $k$ by `Fin m_k`, use `Measure.infinitePi` over `ℕ`, with `Measure.cond` for $P_k(\cdot\mid A_i)$ (any probability measure if $P_k(A_i)=0$).
* **G2**: `pathFiltrationCan` intersects with the ambient σ-algebra (`⊓ inferInstance`) to make `le'` trivial; prove it equals the supremum of the comaps (evaluation is Borel measurable).
* **G4a**: model the grid refinement on `ItoIntegral/ElemGrid.lean`; the variance of a block uses `indep_past` and `integral_sq_rectMass`.
* **G6**: the induction in `transfer` must quantify over all factorizations through `noiseMap` (not choose them), so that the `add` and `limit` cases compose.
* **G7a**: work with `𝓖`-stopping times of the library (`hitTime`); all paths continuous after `IsCL2Mart.exists_version`.
* **K2**: $F=K+K\ast F$ is pointwise in $(t,x)$ and needs Tonelli with the jointly measurable version; finiteness of $F$ comes from W, not from an a priori bound.
* **K3**: dominated convergence fails near $s=t$ with the crude bound; use the $L^2(dy)$ bound $\int(\sum_ic_ig_{t-s}(x_i-y))^2dy\lesssim\Delta x\lVert f\rVert_2^2(t-s)^{-1/2}$ and the boundedness of $\mathbb E Z(s,y)^2$ for $s\in[t/2,t]$.
* **Q3**: the four terms of (7.6) are separate lemmas; term 2 is Prop 6.2 transported by Q1b.
* **Q4**: the stopping level is for $V_n=\max(Q_n,(M_n^\phi)^2)$ (D3″); $V_n(0)=0$.
* **Q5**: for each subsequence: `prop_5_1_isTight`, `isCompact_closure_of_isTightMeasureSet`, sequential compactness (metrizable space of laws), canonical $Y=\mathrm{id}$, `prop_7_1`, `prop_7_2` with the given $(\Omega',S)$ as auxiliary noise, `isWeakMild_prod_of_eq_7_8` (task Q5a, added 13 November 2026), `exists_sheVersion_map_eq` (tightness of the limit law from `prop_5_1` and the portmanteau inequality for closed sets); then `tendsto_of_subseq_tendsto`; versions of $\mathcal Z_n$ by `rescaledMeasure_eq` and `varrhoN_bounds`.

---

## 5. Decisions for the author

My recommendation in bold.

* **D1″. Skorokhod's representation along a subsequence**, proved by explicit couplings on a separable metrizable space (1.2 (a)), instead of Billingsley's Theorem 6.7 on a Polish space. The article only uses it along subsequences. **Recommended.**
* **D2″. No Polishness of $\mathcal M_+(\mathbb R)$** (closes D8' of Stage 3): Lusin–Souslin replaced by the σ-compact range of a tight law (1.2 (h)). Alternative: prove completeness (a complete metric adding $\sup_k\lvert\mu(1-\chi_k)-\nu(1-\chi_k)\rvert$ to the embedding metric; 500–800 lines) and use Mathlib's Lusin–Souslin. **Recommended: no Polishness.**
* **D3″. BDG replaced by a localization** in $\max(Q_n,(M_n^\phi)^2)$ (1.2 (d)), instead of `PLAN.md`'s fourth-moment bound from the product rule (which does not apply on the Skorokhod space). The passage from local to true martingale is written out. **Recommended.**
* **D4″. Identification without existence**: uniqueness in law for (7.13) by conditional expectation onto the noise, Proposition 7.3 and transfer between spaces (1.2 (h)), instead of `PLAN.md`'s contraction and canonical space (or Chen–Dalang). The given solution $Z$ of the statement plays the role of $Z^\star$; (7.14) existence, continuity and positivity of $Z^\star$ are not used. **Recommended.**
* **D5″. Proposition 7.3** proved with the test functions $\rho_\delta(z-\cdot)$ and the inequality $F\le K\ast F$, instead of an orthonormal basis and Parseval; statement unchanged. **Recommended.**
* **D6″. Form of Proposition 7.1**: for any $Y$ whose law is the limit in distribution of versions of $\mathsf Z_{n_k}$ (`TendstoInDistribution`); natural filtration with null sets; martingale problem as `HasBracket`. **Recommended.**
* **D7″. Form of Proposition 7.2**: hypotheses = the conclusions of 7.1 for an arbitrary filtration; enlargement = product with any space carrying a white noise (hypothesis); frozen `IsWhiteNoise`, `IsWalshIntegral`. Alternative: prove E2 first and state "there is an enlargement". **Recommended (product with a given white noise).**
* **D8″. $\mathcal H_T$ in Proposition 7.3** = jointly measurable and square integrable (predictability not required), (7.13) for a.e. $t$ and all $f\in C_c^\infty$. **Recommended.**
* **D9″. (7.15)** as the series $\sum_kK^{\ast k}$ (`IsMildSolution.integral_sq`), not the closed form. **Recommended** (closed form: +200–400 lines).
* **D10″. Companions in Stage 4**: W and U3 yes; E2 optional (in Stage 4 if agents are free, else Stage 5); P in Stage 5 (needs E1), Stage 4 giving `nonneg_of_isWaveFunction`. **Recommended: W, U3 in Stage 4; E2 in Stage 4 wave 4 if usage allows; P in Stage 5.**
* **D11″. Checkpoint statement**: `main_theorem_top` = `main_theorem` with $L_k=\infty$. **Recommended.**

**Places where the Lean proof departs from the article** (to record in `PROGRESS.md`): D1″, D2″, D3″, D4″, D5″; the $L^2$ density by duality (1.2 (e)); the martingale-measure integral as an inductive closure, Lévy proved (1.2 (f)); stochastic Fubini by Riemann sums; filtrations without right-continuity.

---

## 6. Risks and estimate

**Risks.**

* **R1 (size of package J).** Lévy, the martingale-measure integral and the transfer lemma are new mathematics in Lean, each 0.6–1.1k lines; the least certain part of the estimate. Fallback for Lévy: the 4th-moment discretization lemma is the hard point; if it resists, use the bounded case (stop also at $\lvert N\rvert\ge R$) only.
* **R2 (conditional expectations on $\Omega\times\mathbb R^2$).** Lebesgue measure is infinite; on it, an $L^2$ field need not be integrable, and Mathlib's `condExp` of a non-integrable function is silently $0$ (σ-finiteness of the trim does not help). Resolved (13 November 2026) by conditioning for the probability measure $\nu\otimes\gamma\otimes\gamma$ (`noiseProj`, G6); no `condExp` for an infinite measure appears in the interfaces.
* **R3 (universes).** Statements quantifying over other probability spaces (`exists_noise_functional`, `prop_5_1`) carry universe variables; the Skorokhod space lives in `Type`, the given $\Omega'$ anywhere. Checked to elaborate; tasks must not fix universes to `0`.
* **R4 (laws vs outer measures).** Transporting bounds from the original spaces to the Skorokhod space requires the events to be measurable functions of the path (Q1b proves it); outer-measure bounds do not transport.
* **R5 (frozen interfaces).** As in Stages 2–3, an interface found false costs a re-run of its dependents; the most exposed are `hasBracket_map_iff` (G2), `condExp_noise` and `transfer` (G6), `IsMMIntegral` (G8).
* **R6 (predictability).** Mathlib's `Filtration.predictable` is new; its interplay with products in $x$ (`.prod (borel ℝ)`) and with null sets may need extra lemmas (G4b, G8b).
* **R7 (usage).** Weekly usage was 74% at the Stage 3 approval; Stage 4 is the largest stage after Stage 2. Plan the switch to Codex (`AGENTS.md`, `docs/handoff.md`) if the weekly usage nears 90%.

**Size estimate.**

| Part | Tasks | k lines |
|---|---|---|
| statements, interfaces | T0″, I0″ | 0.8–1.3 |
| package I generic (Skorokhod, path space, densities) | G1, G2, G3 | 2.0–3.2 |
| package J generic (Walsh, noise, projection/transfer, Lévy, MM integral, product) | G4a–G9 | 5.0–7.8 |
| package K generic (heat kernel, Volterra, test function) | G10a, G10b | 1.0–1.6 |
| article side K (Prop 7.3, mild solutions, U3, Fubini, law) | K1–K5 | 2.5–4.2 |
| article side J (Prop 7.2) | J1, J2 | 1.1–1.9 |
| article side I (Prop 7.1) and Theorem 1.2, $L=\infty$ | Q1a–Q5 | 3.6–5.6 |
| **Total Stage 4** | 31 tasks (+ E2: 0.8–1.4) | **about 16–26** |

`PLAN.md` gives 27–41k for packages I, J, K. The design is lower because of D1″–D4″ (no Polishness, no BDG, no existence for the SHE, no canonical-space contraction); Stage 2's design (16–27k) came out at about 22k. Agent time: at 20–60 minutes per task (Stage 2: 10–40 minutes; Stage 4 tasks are harder), **about 12–30 agent-hours**, i.e. roughly 5–8 hours of wall time with six agents in parallel, plus the author's review of T0″.

---

## 7. What was checked

* Article: SHA-256 unchanged (`3547cb86…`, 1713 lines). Section 7 (lines 1230–1411) read line by line, with Sections 3.1–3.2 (Prop 3.1), 5 and 6 for the results it uses; the steps listed in 1.3 re-derived by hand, including (7.15) as the sum of $K^{\ast k}$.
* Scratch file `<scratch>/s4design/Infra4.lean` (464 lines, 24 declarations with `sorry`, all definitions complete), compiled with `lake env lean` from the worktree at commit `367fdc1` (Lean 4.35.0, Mathlib v4.35.0): only `declaration uses 'sorry'` warnings. It contains every signature marked "elaborated" in Sections 2 and 3, including `prop_7_1`, `eq_7_4`, `prop_7_2`, `prop_7_3`, `IsMildSolution.integral_sq`, `IsMildSolution.isWeakMild`, `main_theorem_top`, `exists_sheVersion_map_eq`, `skorokhod_subseq`, `hasBracket_map_iff`, `IsWalshIntegral.transfer`, `IsWalshIntegral.condExp_noise`, `levy_setIntegral`, `isWhiteNoise_of_martingales`, `IsMMIntegral` and its two lemmas.
* Mathlib names of Section 3.1 checked with `#check` in `Names4.lean` (same folder). Not found: `measure_limsup_eq_zero` (use `measure_limsup_atTop_eq_zero`), a real Beta-integral lemma (use the complex one), any Skorokhod, Strassen or Kolmogorov-extension theorem, any `PolishSpace` instance for spaces of measures or of continuous maps.
* Not checked: proofs; the line estimates; the exact form of the remaining interface lemmas (sketched in words in Section 3); the elided binders of `eq_7_4` (elaborated in full in the scratch file).
