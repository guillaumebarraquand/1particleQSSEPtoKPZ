# Stage 4: interfaces of packages I, J, K (task I0″)

Written on 13 November 2026 by the T0″+I0″ agent (Opus 5.5). For the main session and the proving agents. The Lean files are the reference; this list gives, for each task of `docs/stage4-design.md` (Section 4), its files (under `QSSEPtoKPZ/`), its interface lemmas (meaning, Lean name) and what it may use. All interface lemmas are `sorry` unless marked **(proved)**. Sections 2–4 of `docs/stage4-design.md` are the specification; the departures are listed at the end. The statements submitted to the author (task T0″) are described in `docs/stage4-statements.md`.

Conventions: `module`, `@[expose] public section`, `noncomputable section`, namespace `QSSEPtoKPZ`. Processes `ℝ → Ω → ℝ`, fields `ℝ → ℝ → Ω → ℝ` (`Z t x ω`), filtrations `Filtration ℝ≥0 mΩ`, no usual conditions (null sets added by `nullAug` when needed). `ℳ₊ = FiniteMeasure ℝ`; **its Borel σ-algebra is always written `borel (FiniteMeasure ℝ)`** (Mathlib's instance is the Giry σ-algebra and is never used); `C([0,T], ℳ₊) = C(Set.Icc 0 T, FiniteMeasure ℝ)` with Mathlib's Borel instance (metrizable, second countable by Stage 3). Predictable fields: `Measurable[(𝓖.predictable).prod (borel ℝ)] fun p : (ℝ≥0 × Ω) × ℝ => h p.1.1 p.2 p.1.2`. Universes are never fixed to `0`.

`lake build` succeeds; the new files have 117 `sorry`: 8 statements of T0″ (the 3 others, `eq_7_4`, `IsMildSolution.integral_sq`, `IsMildSolution.isWeakMild`, quote a twin interface) and 109 interfaces; no other warning. **Corrections of 13 November 2026** (after the audit `docs/stage4-audit.md` and an external review, task S4-repair): departures 17–22 below; they add 5 interface `sorry` (G6: 6 instead of 2; new task Q5a: 1) and change the statements `prop_7_2` (new hypothesis $\mathcal Z(0)=\delta_0$) and `eq_7_4` (binder order).

## Definitions (complete, no `sorry`)

| Name | File | Meaning | Owner |
|---|---|---|---|
| `pathAt γ t`, `pairFM μ f` | `LimitPoints/Defs.lean` | $\gamma(t)$ ($t$ projected on $[0,T]$), $\mu(f)=\int f\,d\mu$ | T0″ |
| `pathFiltrationCan T`, `pathFiltration Y` | same | canonical filtration $\sigma(\gamma(s):s\le t)$; natural filtration $\mathcal G^0$ of $Y$ | T0″ |
| `limMart Y φ φt`, `limBracket Z φ` | same | $M^\phi$ (7.2); $\int_0^t\int Z^2\phi_s^2$ (7.3) | T0″ |
| `limDensity ρ μ x`, `limField ρ Y t x ω` | same | $\liminf_k(\mu\ast\rho_{1/(k+1)})(x)$ (0 if infinite); $Z(t,x)$ of Prop. 7.1 (2) | T0″ |
| `heatConv r f y`, `IsWeakMild T 𝓖 S Z ν` | `Uniqueness/Defs.lean` | $(g_r\ast f)(y)$; $Z\in\mathcal H_T$ solving (7.13) for a.e. $t$ | T0″ |
| `hitTimeStrict X K T` | `LimitPoints/HitLevel.lean` | first time $X>K$, capped at $T$ (library `hitTime`: first time $X\ge K$) | G2 |
| `WalshElem`, `.field`, `.value`, `.IsAdapted` | `WhiteNoise/WalshElem.lean` | elementary integrands $\sum_i c_i\mathbf 1_{(s_i,t_i]\times(a_i,b_i]}$ | G4a |
| `noiseMap S ω`, `noiseSheet S` | `WhiteNoise/NoiseLaw.lean` | $(t,a,b)\mapsto\xi((0,t]\times(a,b])$; $(t,x)\mapsto\xi((0,t]\times(0,x])$ | G5 |
| `noiseFiltration S ν` | `WhiteNoise/NoiseFiltration.lean` | $\mathcal N_t$ = noise up to $t$, with null sets | G5 |
| `IsMMIntegral T 𝒢 q M μ h X` | `WhiteNoise/MMIntegral.lean` | $X=h\cdot M$ (inductive: blocks, sums, limits; limit process a.e. measurable at each time, departure 19) | G8a |
| `noiseRefMeasure ν`, `noiseProdSigma S ν`, `noiseProj S ν h` | `WhiteNoise/Projection.lean` | $\nu\otimes\gamma\otimes\gamma$ ($\gamma$ standard Gaussian); $\mathcal N_\infty\otimes\mathcal B(\mathbb R^2)$; $\hat h=\mathbb E[h\mid\mathcal N_\infty\otimes\mathcal B]$ for $\nu\otimes\gamma^2$ = projection in $L^2(\nu\otimes\mathrm{Leb}^2)$ (departure 20) | S4-repair |
| `prodFiltration 𝒢₁ 𝒢₂ P` | `WhiteNoise/Product.lean` | $(\mathcal G^1_t\otimes\mathcal G^2_t)\vee$ null sets | G9 |
| `heatSqIter k t x` | `Uniqueness/HeatKernel.lean` | $K^{\ast(k+1)}(t,x)=2^{-(k+1)}t^{(k+1)/2-1}\Gamma(\frac{k+1}2)^{-1}g_{t/2}(x)$ | G10a |
| `heatTest t f`, `heatTestDeriv t f` | `Uniqueness/HeatTest.lean` | the test function of Step 4 of Prop. 7.2 and its time derivative | G10b |
| `atomPath`, `WNpath`, `ENpath`, `QNdensPath`, `QNpath`, `MNpath` | `LimitPoints/PathFunctionals.lean` | atoms and $\mathcal W_n,\mathcal E_n,\langle M_n^\phi\rangle,M_n^\phi$ as functionals of the path | Q1a |
| `IsPathPrelimLaw T n P` | `LimitPoints/PrelimitLaw.lean` | $P$ = law of an a.e. measurable version of $\mathsf Z_n$ on $[0,T]$, for some realization (universe `u`) | Q1b |
| `IsLimCoupling Pr T n X Xl` | `LimitPoints/Prop71Mart.lean` | Skorokhod coupling: $X_j$ with prelimit laws at scales $n_j\to\infty$, $X_j\to X_l$ a.s. | Q3 |

## Package I, generic

### G1 — `LimitPoints/SkorokhodPartition.lean`, `LimitPoints/Skorokhod.lean` (uses: Mathlib)
- `skoro_exists_partition`: separable metric space, probability $P$, $\varepsilon>0$ $\Rightarrow$ finitely many disjoint Borel sets of diameter $<\varepsilon$, $P$-null boundaries, $P((\bigcup A_i)^c)\le\varepsilon$.
- `skorokhod_subseq`: $P_k\to P$ weakly on a separable metrizable space $\Rightarrow$ along a subsequence, $X_k\sim P_{\varphi(k)}$, $Y\sim P$ on one probability space (same universe as the space), $X_k\to Y$ a.s.

### G2 — `LimitPoints/PathSpace.lean`, `PathMart.lean`, `HitLevel.lean` (uses: Stage 3 `FiniteMeasureEmbed`, Stage 2 martingales)
- `pathAt_of_mem` (on $[0,T]$, `pathAt γ t = γ ⟨t, _⟩`); `continuous_pathAt_prod` ($(\gamma,t)\mapsto\gamma(t)$ continuous); `continuous_pairFM` ($\mu\mapsto\mu(f)$, $f$ bounded continuous); `continuousOn_pairFM_pathAt` ($(\gamma,t)\mapsto\gamma(t)(\phi_t)$ on $C\times[0,T]$).
- `measurable_pathAt_pathFiltrationCan` ($s\le t$: $\gamma\mapsto\gamma(s)$ is $(\mathcal G_t,\mathrm{borel})$-measurable); `measurable_pairFM_pathFiltrationCan`; `pathFiltration_eq_comap` ($Y$ measurable).
- `measurable_predictable_of_continuous`: a field $F(t,x,\omega)$ jointly continuous in $(t,x)$ and adapted is predictable $\otimes$ Borel (generic). `predictable_mono`.
- `hasBracket_map_iff`, `isCL2Mart_map_iff`: martingale/bracket properties of $m(t,X)$, $a(t,X)$ for `nullAug μ (pathFiltration X)` $\iff$ of $m$, $a$ under the law of $X$ for `nullAug (μ.map X) (pathFiltrationCan T)`; hypotheses: $m(t,\cdot)$, $a(t,\cdot)$ measurable for $t\in[0,T]$, continuous in $t$ for **every** path, $a$ nondecreasing for every path.
- `pathCan_condExp_eq_zero`: $\mathbb E[D\prod_ig_i(\gamma(u_i)(f_i))]=0$ for all $u_i\le s$, $f_i,g_i$ bounded continuous $\Rightarrow$ $\mathbb E[D\mid\mathcal G_s\vee\mathcal N]=0$.
- `tendsto_hitTime`: uniform convergence on $[0,T]$ to a continuous path, `hitTime = hitTimeStrict` for the limit $\Rightarrow$ hitting times converge. `countable_hitTime_ne`: for a process with paths continuous on $[0,T]$, the levels where `hitTime ≠ hitTimeStrict` with positive outer probability are countable.

### G3 — `LimitPoints/Density.lean`, `LimitPoints/Mollify.lean` (uses: G2 interface, Stage 2 (6.1) `smoothedNormSq_eq`)
- `limDensity_nonneg` **(proved)**.
- `withDensity_limDensity_of_bound`: $\lvert\mu(f)\rvert\le C\lVert f\rVert_2$ on $C_c$ $\Rightarrow$ `limDensity ρ μ` $\in L^2$ and $\mu$ = `limDensity` $dx$.
- `lintegral_limDensity_sq_le`: $\int(\texttt{limDensity})^2\le\liminf_k\lVert\mu\ast\rho_{1/(k+1)}\rVert_2^2$ (Fatou).
- `measurable_limDensity_pathAt`: $(\gamma,t,x)\mapsto$ `limDensity ρ (γ(t)) x` measurable.
- `measurable_limField_predictable`: $Y$ measurable $\Rightarrow$ `limField ρ Y` predictable for `pathFiltration Y` (no null sets) — this is a conjunct of `prop_7_1`.
- `continuousOn_smoothedNormSq`: $(\mu,\varepsilon)\mapsto\lVert(\phi\mu)\ast\rho_\varepsilon\rVert_2^2$ continuous on $\mathcal M_+\times(0,\infty)$.
- `smoothedNormSq_withDensity_le`, `tendsto_smoothedNormSq_withDensity`: for $\mu=u\,dx$, $u\ge0$ in $L^2$: $\le\int\phi^2u^2$, and $\to\int\phi^2u^2$ as $\varepsilon\to0^+$.

## Package J, generic

### G4a — `WhiteNoise/WalshBasic.lean`, `WhiteNoise/WalshElem.lean` (uses: `Checks.lean`)
- `IsWhiteNoise.isProbabilityMeasure` **(proved)**.
- `IsWalshIntegral.zero`, `.const_mul`, `.sub`, `.finset_sum`, `.mono_filtration` (larger filtration), `.congr_rectMass` (depends on $S$ only through rectangle masses).
- `WalshElem.IsAdapted.isWalshIntegral`; `WalshElem.IsAdapted.isometry` (elementary isometry, with `MemLp` of both sides); `IsWalshIntegral.exists_elem_tendsto` (every Walsh integral is an $L^2$ limit of elementary ones, integrands and values together; needs `IsWhiteNoise`).

### G4b — `WhiteNoise/WalshIsometry.lean`, `WhiteNoise/WalshExists.lean` (uses: G4a)
- `IsWalshIntegral.ae_eq_lib`, `IsWalshIntegral.isometry_lib`: library copies of the companions **W** (statements identical to `Companions.lean`, checked with `pp.all`, see `docs/stage4-statements.md`).
- `IsWalshIntegral.integral_mul` ($\mathbb E[XX']=\mathbb E\iint hh'$), `.congr_ae` (a.e. modification of integrand and value), `.exists_limit` (closure under $L^2$ limits of integrands, the value being produced).
- `exists_isWalshIntegral`: predictable, vanishing for $s\le0$, $L^2$ $\Rightarrow$ the integral exists.

### G5 — `WhiteNoise/NoiseLaw.lean`, `WhiteNoise/NoiseFiltration.lean` (uses: G4a)
- `rectMass_noiseSheet`, `noiseMap_noiseSheet` **(proved)**; `IsWhiteNoise.measurable_noiseMap`; `IsWhiteNoise.map_noiseMap_eq` (the law of the noise coordinates is the same for all white noises).
- `IsWhiteNoise.noiseFiltration_le` ($\mathcal N_t\subseteq\mathcal G_t\vee$ null sets); `IsWhiteNoise.nullAug`; `IsWhiteNoise.noiseSheet` (`noiseSheet S` is a white noise for $\mathcal N$); `isWalshIntegral_noiseSheet_iff`; `IsWhiteNoise.indep_future` (rectangles in $(s,\infty)\times\mathbb R$ jointly independent of $\mathcal G_s$); `IsWhiteNoise.condExp_noise_eq` ($\mathbb E[c\mid\mathcal N_\infty]=\mathbb E[c\mid\mathcal N_s]$ for $c$ $\mathcal G_s$-measurable).

### G6 — `WhiteNoise/Projection.lean`, `WhiteNoise/Transfer.lean` (uses: G4, G5)
- `noiseProdSigma_le` ($\mathcal N_\infty\otimes\mathcal B(\mathbb R^2)\le$ product σ-algebra) and `stronglyMeasurable_noiseProj` **(proved)**.
- Projection $\hat h$ = `noiseProj S ν h` (conditional expectation for the probability measure $\nu\otimes\gamma\otimes\gamma$, departure 20), for $h\in L^2(\nu\otimes\mathrm{Leb}^2)$: `noiseProj_memLp` ($\hat h\in L^2(\nu\otimes\mathrm{Leb}^2)$, $\lVert\hat h\rVert_2\le\lVert h\rVert_2$), `noiseProj_ae_eq_self` (noise-measurable fields are fixed), `noiseProj_add`, `noiseProj_mul_left` (a bounded measurable deterministic factor $g(s,y)$ comes out), `condExp_integral_noiseProj` (for a.e. $t$, $\mathbb E[\int h(t,x)f(x)dx\mid\mathcal N_\infty]=\int\hat h(t,x)f(x)dx$, $f\in L^2$). All a.e. for $\nu\otimes\mathrm{Leb}^2$ (same null sets as $\nu\otimes\gamma^2$).
- `IsWalshIntegral.condExp_noise`: $\mathbb E[\int h\,d\xi\mid\mathcal N_\infty]=\int\hat h\,d\xi$ (integral for $\mathcal N$). Proof: induction (block: $\hat h=\mathbb E[c\mid\mathcal N_\infty]\mathbf 1_R$ a.e., `IsWhiteNoise.condExp_noise_eq`, truncate on a null set of $\mathcal N_s$ to get a bounded block; sum: `noiseProj_add`; limit: `noiseProj_memLp` on the differences), working with `noiseSheet` where a white noise for $\mathcal N$ is needed.
- `IsWalshIntegral.transfer`: a Walsh integral with integrand $H(\text{noise},s,y)$ and value $\Xi(\text{noise})$ ($H,\Xi$ measurable) transfers to any other space carrying a white noise.

### G7a — `WhiteNoise/Levy.lean` (uses: Stage 2 martingales, `hitTime`)
- `levy_setIntegral`: `HasBracket T 𝓖 N (c t)`, $s\le t\le T$, $A\in\mathcal G_s$ $\Rightarrow$ $\int_Ae^{iu(N_t-N_s)}=e^{-cu^2(t-s)/2}\mathbb P(A)$.

### G7b — `WhiteNoise/LevyMulti.lean` (uses: G7a, `Covariation`)
- `isWhiteNoise_of_martingales`: $S$ adapted, $S(0,\cdot)=0$, covariations $\langle S(\cdot,b)-S(\cdot,a),S(\cdot,b')-S(\cdot,a')\rangle_t=t\lvert(a,b]\cap(a',b']\rvert$ on every horizon $\Rightarrow$ `IsWhiteNoise`.

### G8a — `WhiteNoise/MMIntegral.lean`, `Martingales/CovariationAlgebra.lean` (uses: `Covariation`, Stage 2)
- `HasBracket.hasCovariation`, `HasCovariation.symm`, `.add_left`, `.const_mul_left`, `.of_hasBracket_add` (polarization), `.hasBracket` (generic covariation algebra, not in the library).
- `IsMMIntegral.hasCovariation` ((7.10)), `IsMMIntegral.const_mul`, `IsMMIntegral.ae_eq` (integrands equal $q\,d\mathbb P\,dr\,dx$-a.e. $\Rightarrow$ indistinguishable on $[0,T]$); intensity $q$ predictable, $\ge0$, with $\mathbb E\int_0^T\int q<\infty$ (`hq1`, departure 19; J1 supplies it from (7.1), $q=Z^2$). The `limit` rule requires `∀ r ∈ Icc 0 T, AEStronglyMeasurable (X r) μ`; with it (and `hM`, which makes all values a.s. continuous) the lower integral of $\sup_r$ is a.s. a countable supremum, so the convergence is genuine $L^2$ convergence and the martingale property passes to the limit.

### G8b — `WhiteNoise/MMExists.lean` (uses: G8a)
- `exists_isMMIntegral`: $q$ predictable, $\ge0$, $\mathbb E\int_0^T\int q<\infty$, covariations of $M$; $h$ predictable with $\mathbb E\int_0^T\int h^2q<\infty$ $\Rightarrow$ $h\cdot M$ exists. (The limit process must be continuous for every $\omega$ and a.e. measurable at each time: take the a.s. uniform limit along a fast subsequence on the event where it exists, $0$ elsewhere; that event's complement is null, so a.e. measurability holds even if the event is not measurable.)

### G9 — `WhiteNoise/Product.lean`, `WhiteNoise/WalshProcess.lean` (uses: G4b, G8a's `CovariationAlgebra`)
- `comap_fst_le_prodFiltration`; `HasCovariation.prod_fst`, `HasBracket.prod_fst` (first-factor martingales lift); `IsWhiteNoise.prod_snd` (second-factor white noise lifts); `measurable_predictable_prod_fst`; `hasCovariation_prod_fst_walsh` (first-factor martingale ⟂ Walsh process against the lifted noise).
- `exists_walshProcess`: $h$ predictable, $\mathbb E\int_0^T\int h^2<\infty$ $\Rightarrow$ a version of $t\mapsto\int_0^t\int h\,d\xi$ with `HasBracket` $\int_0^t\int h^2$; `walshProcess_hasCovariation`.

## Package K, generic

### G10a — `Uniqueness/HeatKernel.lean`, `Uniqueness/Volterra.lean` (uses: `Checks.lean`)
- `heatKernel_nonneg`, `heatKernel_integral` ($\int g_r=1$), `heatKernel_sq_integral` ($\int g_r^2=(4\pi r)^{-1/2}$), `heatKernel_conv` ($g_a\ast g_b=g_{a+b}$), `abs_heatConv_le`, `heatConv_sq_integral_le`.
- `heatSqIter_zero` ($=g_t^2$), `heatSqIter_succ` ($K^{\ast(k+2)}=K\ast K^{\ast(k+1)}$ on $(0,t)\times\mathbb R$, with integrability), `heatSqIter_le` ($K^{\ast(k+1)}\le\varepsilon_kK$ on $(0,T]$, $\sum\varepsilon_k<\infty$).
- `volterra_ae_eq_zero` (in $[0,\infty]$): $\int_0^TF<\infty$, $F(t)\le c\int_0^tF(s)(t-s)^{-1/2}ds$ a.e. $\Rightarrow F=0$ a.e.

### G10b — `Uniqueness/HeatTest.lean` (uses: G10a)
- `heatTest_self` ($\phi_t=f$) and `heatTest_zero_zero` ($\phi_0(0)=\int g_tf$) **(proved)**; `isC13_heatTest`; `heatTest_pde` ($\partial_s\phi+\frac12\partial_x^2\phi=0$ on $[0,t]$).

## Article side

### K1 — `Uniqueness/Prop73.lean` (statement file; uses: G4, G10a)
- prove `prop_7_3` in place (D5″: test functions $\rho_\delta(z-\cdot)$, Young, Fatou, `volterra_ae_eq_zero`).

### K2 — `Uniqueness/SecondMoment.lean` (uses: G4, G10a)
- `isMildSolution_unique_lib` (copy of **U3**, identical statement); `heatMild_exists_version` (jointly measurable version, continuous on $(0,\infty)\times\mathbb R$ for every $\omega$, still a mild solution); `heatMild_integral_sq` (= `IsMildSolution.integral_sq`); `heatMild_integral_sq_le` ($\mathbb E Z(t,x)^2\le Cg_t(x)^2$ on $(0,T]$).

### K3 — `Uniqueness/StochFubini.lean` (uses: K2, G4, G10a)
- `heatMild_isWeakMild` (= `IsMildSolution.isWeakMild`: version in $\mathcal H_T$, (7.13) for every $t\in(0,T]$).

### K4 — `Uniqueness/NoiseFunctional.lean` (uses: K1 `prop_7_3`, G5, G6)
- `IsWeakMild.exists_noise_functional`: $Z=H(\text{noise})$ a.e. on $\Omega\times[0,T]\times\mathbb R$, and every solution of (7.13) on any space (universe `u`) carrying a white noise is $H$ of its noise. Proof with $\hat Z$ = `noiseProj S ν (Z 𝟙_{[0,T]}(t))` (not a `condExp` for $\nu\otimes\mathrm{Leb}^2$: $Z$ is $L^2$ but not $L^1$ there): `condExp_noise`, `noiseProj_mul_left` (factor $\mathbf 1_{0<s<t}g_{t-s}\ast f$), `condExp_integral_noiseProj` (value), `noiseProj_memLp`, `stronglyMeasurable_noiseProj` + `noiseProdSigma_le` ($\hat Z\in\mathcal H_T$), `prop_7_3`, Doob–Dynkin.

### K5 — `Uniqueness/SheVersion.lean` (uses: K3, K4, G2, Stage 3)
- `exists_sheVersion_map_eq`: (tight $Y$ with $Y(0)=\delta_0$ and a nonnegative density $Z_1\in\mathcal H_T$ solving (7.13) on $\Omega_1$) + (mild solution $Z$ on $\Omega'$) $\Rightarrow$ a measurable continuous version of $t\mapsto$ `sheMeasure Z t` on $\Omega'$ with the law of $Y$, and $Z\ge0$ on $(0,T]\times\mathbb R$ a.s.

### Q5a — `Uniqueness/WeakMildBridge.lean` (new, 13 November 2026; uses: `LimitPoints/Defs`, `Uniqueness/Defs`, G4b `congr_ae`, G2 `continuous_pathAt_prod`)
- `isWeakMild_prod_of_eq_7_8`: $Y$ measurable, $Z$ jointly measurable (`Measurable (uncurryField Z)`), $Z\ge0$, (7.1), `hdens`, a white noise $S$ for $\bar{\mathcal G}$ on $\Omega\times\Omega''$ and (7.8) for all $f\in C_c^\infty$, $t\in(0,T]$ (the conclusion of `prop_7_2`) $\Rightarrow$ `IsWeakMild T 𝒢b S (fun t x ω => Z t x ω.1) (Pr.prod ν'')`. Proof: measurable set of $(\omega,t)$ where $\mathcal Z(t)=Z(t,x)dx$ (masses of rational intervals and total mass); Fubini swaps "a.s., a.e. $t$" into "a.e. $t$, a.s." with one null set of times for all $f$; $\mathcal Z(t;f)=\int Z(t,x)f(x)dx$ there (uses $Z\ge0$); `IsWalshIntegral.congr_ae` on the values; measurability and (7.1) on the product by Tonelli. For $Z$ = `limField ρ Y`, joint measurability is `measurable_limDensity_pathAt` composed with $(\omega,t,x)\mapsto(Y\omega,t,x)$. Audit remark R6.

### J1 — `WhiteNoise/Prop72Noise.lean` (uses: G7b, G8, G9, `CovariationAlgebra`)
- `prop72_noise`: hypotheses of `prop_7_2`; conclusion: filtration $\bar{\mathcal G}\supseteq\mathcal G$ on $\Omega\times\Omega''$, white noise $S$ for it, and (7.11) for $h=\mathbf 1_{(u,v]}(s)\varphi(y)$, $\varphi\in C^3_b$ time-independent: $\iint h\,Z\,d\xi=M^\varphi(v)-M^\varphi(u)$.

### J2 — `WhiteNoise/Prop72.lean` (statement file; uses: J1, G10b, G4b)
- prove `prop_7_2` in place (Step 3: approximate $\phi$ by $\phi^{(N)}$, orthogonality of increments via `hmart`, and $M^\phi(0)=0$ a.s. from the new hypothesis `hY0` ($\mathcal Z(0)=\delta_0$, departure 17); Step 4: `heatTest`). `prop72_noise` (J1) does not need `hY0` (it concerns increments only) and is unchanged.

### Q1a — `LimitPoints/PathFunctionals.lean` (uses: G2, Stage 2–3)
- `measurable_atomPath`, `measurable_ENpath`, `measurable_MNpath`, `measurable_QNpath` (for $t\in[0,T]$), `continuousOn_MNpath`, `continuousOn_monotoneOn_QNpath` (every path).
- On a version (pointwise: $\gamma(t)=\mathsf Z_n(t)$ for $t\in[0,T]$, summability): `atomPath_eq` (atoms = $\mathfrak z_n$), `WNpath_ENpath_eq`, `MNpath_QNpath_eq`.

### Q1b — `LimitPoints/PrelimitLaw.lean` (uses: Q1a, G2, Stages 2–3)
- `IsPathPrelimLaw.isProbabilityMeasure`, `.ae_dirac` ($\gamma(0)=\delta_0$), `.hasBracket` (Prop. 3.1 under $P$, canonical augmented filtration), `.prop_3_1_path` (Prop. 3.1 (2)–(3) and integrability, a.s.), `.prop_4_3_path` ((4.8), with measurability).
- `pathPrelim_eq_6_2` ((6.2), constant depending on $\rho$ only, with joint measurability); `measurableSet_pathReplEvent`; `pathPrelim_replacement` (Prop. 6.2, **uniform in the realization**: see departure 16).
- **Do `pathPrelim_replacement` first** (it is the riskiest interface of Q1b, and Q3 depends on it): copy the private `prop62_main` of `Replacement/ReplacementLemma.lean` publicly into a Q1b file, with the constant chosen **before** the realization ($K_\rho=\max(K_0,0)$, $K_0$ the constant of `lemma_6_4 hρ`, which depends only on $\rho$), then redo the final step of `prop_6_2`: there $\varepsilon_0$ depends only on $(K_\rho,C,T,\eta,\delta)$ and $N$ only on $(\rho,K_\rho,C,T,\eta,\delta,\varepsilon)$ (the Lipschitz constant of $\kappa$ from `hρ.kappa_lipschitz`, $b_m\to1$ from `tendsto_bM`), never on the realization. Then transport to $P$: $P(A)=\mu(Z_v^{-1}A)$ by `measurableSet_pathReplEvent` and `AEMeasurable Zv`, and the integrands agree on the version a.s. for all $s\in[0,T]$ (`WNpath_ENpath_eq`, `hZv`). The statement was checked against this proof (13 November 2026): its quantifier order ($T,\phi,C$; then $\eta,\delta$; $\exists\varepsilon_0$; $\forall\varepsilon$; $\exists N$; $\forall n\ge N$, $\forall P$) is exactly what the proof gives; no change.

### Q2 — `LimitPoints/Prop71Density.lean` (uses: Q1b, G1, G3)
- `limPt_eq_7_4` (= `eq_7_4`; the space of $\mathcal Z$ is bound after `∃ C`, departure 18), `limPt_dirac_density` (Prop. 7.1 (1)–(2), hypotheses of `prop_7_1`).

### Q3 — `LimitPoints/Prop71Mart.lean`, `LimitPoints/ConvQ.lean` (uses: Q1b, G2, G3; Q2 through hypotheses)
- `tendstoUniformlyOn_MNpath` ((7.5), deterministic: $\gamma_j\to\gamma$, $n_j\to\infty$); `IsLimCoupling.isCL2Mart` ($M^\phi$ martingale for $\mathcal G^0\vee$ null sets of the limit); `IsLimCoupling.tendsto_QN` ((7.6) in probability, density and (7.1) of the limit as hypotheses).

### Q4 — `LimitPoints/Prop71Bracket.lean`, `LimitPoints/Prop71.lean` (statement file; uses: Q2, Q3, G1, G2)
- `IsLimCoupling.hasBracket` (Prop. 7.1 (3) on the coupling, by localization, D3″); then prove `prop_7_1` in place: `skorokhod_subseq` on the laws, `limPt_dirac_density`, `IsLimCoupling.hasBracket`, transfer to $Y$ by `hasBracket_map_iff` twice (modify the bracket functional off the measurable set where $\int_0^T\int Z^2<\infty$, then `HasBracket.congr`).

### Q5 — `Uniqueness/Theorem12.lean` (statement file; uses: all, in particular Q5a)
- prove `main_theorem_top` and `IsMildSolution.nonneg_of_isWaveFunction` in place (design, note on Q5; positivity from `exists_sheVersion_map_eq`, on $(0,T]$ for every $T\in\mathbb N$). Chain: `prop_7_1` $\to$ `prop_7_2` (with `hY0` = its first conjunct, predictability for `nullAug Pr (pathFiltration Y)` by `predictable_mono`) $\to$ `isWeakMild_prod_of_eq_7_8` (Q5a) $\to$ `exists_sheVersion_map_eq` on $\Omega_1=\Omega\times\Omega'$ (lift `htight`, `hY0`, `hdens` through `Prod.fst`, `Measure.map_fst_prod`).

E2 (optional, decision D10″) has no file yet.

## Dependencies and import graph

Statement files are leaves: no interface file imports `Prop71`, `Prop72`, `MildSolution` or `Theorem12` (K4 imports `Prop73`, which K1 proves in place). `MildSolution.lean` imports `StochFubini` and quotes the twins; `Prop71.lean` imports `Prop71Density`, `Prop71Bracket`.

```
LimitPoints/Defs ─► PathSpace (G2) ─► PathMart (G2) ─┐
        │              ├─► Density (G3) ─► Mollify (G3)│
        │              └─► PathFunctionals (Q1a) ──────┴─► PrelimitLaw (Q1b) ─┬─► Prop71Density (Q2) ─┐
SkorokhodPartition ─► Skorokhod (G1) ───────────────────────────────────────────┘   Prop71Mart (Q3) ─► ConvQ (Q3) ─► Prop71Bracket (Q4) ─► Prop71 (T0″/Q4)
Martingales/Stopping ─► HitLevel (G2) ─────────────────────────────────────────────────────────────────┘
Checks ─► WalshBasic ─► WalshElem (G4a) ─► WalshIsometry ─► WalshExists (G4b) ─► Product, WalshProcess (G9)
NoiseLaw ─► NoiseFiltration (G5) ─► Projection ─► Transfer (G6)
Levy (G7a) ─► LevyMulti (G7b);  CovariationAlgebra, MMIntegral (G8a) ─► MMExists (G8b)
MMExists, LevyMulti, Product, WalshProcess, LimitPoints/Defs ─► Prop72Noise (J1) ─► Prop72 (T0″/J2) ◄─ HeatTest (G10b)
Uniqueness/Defs ─► HeatKernel ─► HeatTest;  Volterra (G10a)
HeatKernel, Volterra, WalshIsometry ─► Prop73 (T0″/K1) ─► NoiseFunctional (K4) ◄─ Transfer
HeatKernel, WalshIsometry ─► SecondMoment (K2) ─► StochFubini (K3) ─► MildSolution (T0″)
NoiseFunctional, StochFubini, PathSpace ─► SheVersion (K5)
LimitPoints/Defs, Uniqueness/Defs, WalshIsometry ─► WeakMildBridge (Q5a)
Prop71, Prop72, SheVersion, MildSolution, WeakMildBridge, Tightness/Prop51 ─► Theorem12 (T0″/Q5)
```
Waves as in the design (Section 4). Each task may use as black boxes the interfaces of the files it imports, `sorry` or not. Wave 1 (G1, G2, G3, G4a, G5, G10a) depends only on Stages 0–3.

## Departures from `docs/stage4-design.md`

1. **Files.** The definitions of Section 2.1 are in `LimitPoints/Defs.lean` and `Uniqueness/Defs.lean` (T0″); `pathFiltrationCan` (G2 in the design) is there too, since `pathFiltration` needs it. `Martingales/CovariationAlgebra.lean` (G8a) and `WhiteNoise/WalshProcess.lean` (G9) are new files.
2. **Companion copies** are named `IsWalshIntegral.ae_eq_lib`, `IsWalshIntegral.isometry_lib` (G4b, `WalshIsometry.lean`) and `isMildSolution_unique_lib` (K2, `SecondMoment.lean`), instead of `walsh_ae_eq`, `walsh_isometry`, `isMildSolution_unique'`.
3. **Twin interfaces** with the statements of Section 2: `heatMild_integral_sq`, `heatMild_isWeakMild`, `limPt_eq_7_4` (statements identical), `limPt_dirac_density` (parts (1)–(2) of `prop_7_1`). This keeps the statement files leaves of the import graph; `IsMildSolution.integral_sq`, `IsMildSolution.isWeakMild` and `eq_7_4` are proved by quoting them.
4. **`eq_7_4`** has an added conjunct: the integrand is jointly measurable in $(\omega,t)$ (convention "genuine integrals"; the design's statement was a bare upper bound on a lower integral).
5. **`IsMildSolution.isWeakMild`** asserts in addition (7.13) for **every** $t\in(0,T]$, as the article does (`IsWeakMild` only has almost every $t$).
6. **`hasBracket_map_iff`, `isCL2Mart_map_iff`**: added hypotheses — continuity in $t$ for every path (and monotonicity of $a$), measurability only for $t\in[0,T]$. Without them the equivalence can fail: the almost sure path properties in `HasBracket` (continuity, monotonicity) are not events of the path space in general, and the image of an almost sure property under `Measure.map` needs a measurable event.
7. **`IsMMIntegral`**: the `limit` rule requires the limit integrand to be predictable; `IsMMIntegral.hasCovariation` and `.ae_eq` require the intensity $q$ to be predictable. Without these, an integrand modified on a set of inner measure zero passes the (lower-integral) convergence test, and the bracket $\int_0^t\int q\,h\,h'$ need not be measurable: the design's `hasCovariation` could be false.
8. **`IsWeakMild.exists_noise_functional`** has an added conjunct ($Z=H(\text{noise})$ a.e. on the given space), so that K5 can work with two spaces in **different** universes (the design put $\Omega_1$ and $\Omega'$ in the same universe).
9. **`exists_sheVersion_map_eq`**: $\Omega_1$, $\Omega'$ in independent universes; **new hypothesis** `hZ₁0` ($Z_1\ge0$) and **new conclusion** ($Z\ge0$ on $(0,T]\times\mathbb R$ a.s.). Reason: `hdens` is written with `ENNReal.ofReal`, i.e. with $\max(Z_1,0)$, so comparing bumps only yields $\gamma(t)=\max(Z,0)\,dx$ (which is `sheMeasure`, so the version is unaffected), not $Z\ge0$; positivity comes from $Z_1\ge0$ through the noise functional. Q5 takes positivity from here.
10. **`noiseSheet`** (G5) is new: $S$ itself need not be a white noise for the noise filtration, because its values on the axes ($S(0,x)$, $S(t,0)$) are only $\mathcal G$-adapted, not functions of the noise; `noiseSheet S` (same rectangle masses) is. G5 also has `IsWhiteNoise.nullAug`, `indep_future`, `condExp_noise_eq`, `isWalshIntegral_noiseSheet_iff`; G4a has `IsWalshIntegral.congr_rectMass`.
11. **G4 split**: the elementary approximation `IsWalshIntegral.exists_elem_tendsto` is in G4a; `congr_ae` is in G4b (it needs the isometry); added `integral_mul`, `exists_limit`, `finset_sum`, `sub`, `zero`.
12. **Hitting times** are stated with the library's `hitTime` and a new `hitTimeStrict` (`tendsto_hitTime`, `countable_hitTime_ne`), instead of `sInf` of sets of reals (`tendsto_hitLevel`), so that `isStoppingTime_hitTime` and `HasBracket.stopped` apply directly.
13. **Q interfaces** (only sketched in the design): `IsPathPrelimLaw`, `IsLimCoupling`, the path functionals, and the lemmas listed above. `IsPathPrelimLaw.eq_4_8` is not a legal name (`eq_<n>` is reserved for equation lemmas of definitions): it is `IsPathPrelimLaw.prop_4_3_path`.
14. **G10a/G10b** additions: `heatSqIter`, `heatKernel_nonneg`, `heatKernel_integral`, `abs_heatConv_le`, `heatConv_sq_integral_le`; `heatTest_zero_zero` needs no hypothesis on $f$ (proved).
15. **G1**: the partition lemma takes a `MetricSpace` instance (use `metrizableSpaceMetric` inside `skorokhod_subseq`).
16. **Uniformity of Proposition 6.2.** The frozen `prop_6_2` fixes the realization before choosing $\varepsilon_0$ and $N$, but in Proposition 7.1 the realization changes with $k$; `pathPrelim_replacement` is uniform. The proof of `prop_6_2` is uniform (its constant `Kρ = max K0 0` comes from `lemma_6_4 hρ`), but `prop62_main` is private: Q1b must copy it publicly into its own file (allowed: same project) rather than edit `ReplacementLemma.lean`. The same remark does not affect (4.8), Prop. 3.1 (explicit constants) or (6.2) (`prop_6_1` is already uniform).
17. **`prop_7_2` takes $\mathcal Z(0)=\delta_0$** (`hY0`, after `hY`; audit E1). Without it the statement is false ($\mathcal Z\equiv0$, $Z\equiv0$); the design's claim that it is not needed was wrong. `prop_7_1` supplies it (first conjunct); `exists_sheVersion_map_eq` already has it; `prop72_noise` does not need it. J2 uses it for $M^\phi(0)=0$.
18. **`eq_7_4`, `limPt_eq_7_4`**: `∀ {Ω : Type*} {_ : MeasurableSpace Ω}` is bound after `∃ C` (audit W1), so $C$ depends only on $\rho$; the universe levels of `Ω` stay universe parameters of the theorem (outer, as they must be). The two statements are still identical (`Expr` equality checked, levels `[u_2, u_3]`).
19. **`IsMMIntegral`, `limit` rule**: new premise `∀ r ∈ Set.Icc 0 T, AEStronglyMeasurable (X r) μ`. Without it the rule was unsound: the lower integral $\int^-\sup_r(X_k-X)^2$ can be $0$ for a non-measurable error that is not a.s. $0$ (external review: `Bool`, trivial σ-algebra, $q=0$, $M=0$, $h=0$, $X(t,\mathrm{true})=t$, $X(t,\mathrm{false})=0$), so `hasCovariation` and `ae_eq` were false. **`IsMMIntegral.hasCovariation`, `.ae_eq`**: new hypothesis `hq1` ($\mathbb E\int_0^T\int q<\infty$, as in `exists_isMMIntegral`), so that the Bochner integrals $\int q\,h\,h'\,dx$ in the bracket are genuine for the blocks and their limits (J1 supplies it: $q=Z^2$, (7.1)). The `block` and `add` rules have no such trap (block integrands are predictable and their values are a.s. continuous and adapted up to null sets under `hM`). No other Lean file used these.
20. **Projection onto the noise** (G6). `IsWalshIntegral.condExp_noise` was false: it took Mathlib's `condExp` on $\Omega\times\mathbb R^2$ for the infinite measure $\nu\otimes\mathrm{Leb}^2$, on which an $L^2$ integrand need not be integrable, and `condExp` of a non-integrable function is $0$ (σ-finiteness does not help). Example: $h(s,y)=\mathbf 1_{(0,1]}(s)\mathbf 1_{[0,\infty)}(y)/(1+y)$, deterministic, $\lVert h\rVert_2^2=1$, $\lVert h\rVert_1=\infty$: its Walsh integral is noise-measurable with variance $1$, and the statement made it the integral of $0$. Now `noiseProj S ν h` is the conditional expectation for the probability measure `noiseRefMeasure ν` $=\nu\otimes\gamma\otimes\gamma$ (same null sets; $L^2(\nu\otimes\mathrm{Leb}^2)\subset L^1(\nu\otimes\gamma^2)$; density $\mathcal B(\mathbb R^2)$-measurable, so it is the $L^2(\nu\otimes\mathrm{Leb}^2)$ projection). `sigmaFinite_trim_noise` is removed (a probability measure needs no σ-finiteness check), replaced by `noiseProdSigma_le` (proved); new interfaces `noiseProj_memLp`, `noiseProj_ae_eq_self`, `noiseProj_add`, `noiseProj_mul_left`, `condExp_integral_noiseProj`, which K4 needs to show that $\hat Z$ solves (7.13). Audit of every other `condExp` in the Stage 4 interfaces: all are for probability measures on $\Omega$ (`IsCL2Mart`/`HasBracket` conditions, `condExp_noise_eq`, `pathCan_condExp_eq_zero`, the value $\nu[X\mid\mathcal N_\infty]$); none on $\Omega\times\mathbb R$ or $\Omega\times\mathbb R^2$ remains. `NoiseFunctional.lean` and `Transfer.lean` had $\mathbb E[\cdot\mid\mathcal N_\infty\otimes\mathcal B]$ only in their docstrings (statements unchanged; docstrings now use `noiseProj`).
21. **Bridge (7.8) $\to$ (7.13)** (audit R6): new interface file `Uniqueness/WeakMildBridge.lean`, lemma `isWeakMild_prod_of_eq_7_8`, owned by the new task **Q5a** (wave 5, after G4b; about 0.3–0.5 of a task), imported by `Theorem12.lean`. It needs $Z\ge0$ (because `hdens` only sees $\max(Z,0)$) and the joint measurability of $Z$ on $\Omega\times\mathbb R^2$.
22. **Uniform replacement** (departure 16): the statement of `pathPrelim_replacement` was checked against the proof of `prop_6_2` (constant of `lemma_6_4`, depending only on $\rho$; $\varepsilon_0$, $N$ depending only on $\rho,T,C,\eta,\delta,\varepsilon$); unchanged. Q1b should do it first (see Q1b).
