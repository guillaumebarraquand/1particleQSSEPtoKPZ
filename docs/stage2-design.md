# Stage 2: design (packages B, C, D, E, G and the rest of F)

Written on 12 November 2026 by a design agent (Opus 5.5), at the request of the main session. **Nothing in this document is proved.** It fixes the definitions, the Lean statements and the order of work for Stage 2. The Lean signatures of Sections 2 and 3 were checked to elaborate against Mathlib v4.35.0 in two scratch files (outside the repository, see Section 7); they are a starting point for the statement task T0, not frozen text.

Equation numbers are those of the article (version of 11 November 2026, SHA-256 `3547cb86…`, unchanged), read from its `.aux` file. **Remark for the main session:** three docstrings of the frozen Stage 1 files use wrong equation numbers: `Mollifier.lean` calls the definition of $b_m,k_m$ "(6.6)" (it is (6.4)), `Poisson.lean` and `stage1-statements.md` call the normalization $\sum_r\pi(r)k_m(r)=1$ "(6.9)" (it is (6.5)) and the bounds on $b_m$ "(6.10)" (it is (6.6)). Only comments are affected. In the article, (6.9) and (6.10) are the definitions of $\mathsf F_n$ and $\mathsf B_n$.

Readers: Section 1 is for the author. Sections 2 to 4 are for the agents who will write the Lean code. Section 5 lists the decisions for the author.

---

## 1. Mathematical overview

### 1.1 What Stage 2 proves

The checkpoint of `PLAN.md` (Section 5) is: Propositions 3.1, 4.3, 6.1, 6.2 hold in Lean for every realization of the wave function on $\mathbb Z$. That is, for every probability space, every filtration $\mathcal F_t$ (no usual conditions), every Brownian family $B$ and every $\psi$ with `IsWaveFunction ⊤ 𝓕 B ψ μ`. The chain of results is:

| Article | Content | Role |
|---|---|---|
| Prop 2.1, only (2.2) | $\mathbb E\big[\sup_{t\le T}\lVert\psi_t\rVert_a^{2k}\big]<\infty$ | moments needed for the infinite sums |
| (after Lemma 2.3) | $\sum_xP(t,x)=1$ for all $t$, almost surely | conservation of the mass |
| Prop 2.2, (2.3)-(2.5) | equation of $P$; currents $J(x)$ are continuous $L^2$ martingales with $\langle J(x),J(y)\rangle_t=2\ \mathbf 1_{x=y}\int_0^tP(s,x)P(s,x+1)ds$; $\mathbb E P(t,x)=p_t(x)$ | the semimartingale structure of $P$ |
| Lemma 2.3, (2.7), (2.8) | linear and quadratic functionals of $P$ with exponentially growing weights | duality with one and two inclusion particles |
| Section 3.1 | (3.7), (3.8), (3.9), the inequality on $\sinh\theta-\theta$ | definitions and elementary bounds |
| Prop 3.1, (3.13)-(3.16) | $M_n^\phi$ is a continuous $L^2$ martingale with bracket (3.15); items (1), (2), (3) | the martingale of the discrete SHE |
| (3.18), (3.20), (3.23) | algebraic identities | used in Lemma 3.2, Prop 4.3, Lemma 6.4 |
| Lemma 3.2, (3.21)-(3.22) | quadratic functionals of the tilted field | |
| Prop 4.3, (4.7)-(4.9) | conditional second moment, uniform bounds, increments of $\langle\mathsf W_n\rangle$ | uses Lemma 4.2 (proved in Stage 1) |
| Lemma 6.4, (6.11)-(6.15) | the corrector | uses Lemma 6.3 (proved in Stage 1) |
| Prop 6.1, (6.2); Prop 6.2, (6.3) | $L^2$ bound; replacement lemma | the checkpoint |

Not in Stage 2: existence and uniqueness in Proposition 2.1 (companions E1, U1, Stage 5); Proposition 2.2 for finite $L$ (Section 8 does not use it; see decision D7); Section 5; Section 7.

### 1.2 How the Lean proof goes, and where it departs from the article

**(a) Null sets and versions.** The article assumes the usual conditions. Lean's statement assumes nothing on $\mathcal F_t$, and continuity of $\psi$ only almost surely. The formal proof works with the *null augmentation* $\mathcal F^a_t=\mathcal F_t\vee\sigma(\mathcal N)$, where $\mathcal N$ is the class of measurable $\mu$-null sets. It is not right-continuous and it is not needed to be. Three facts make it harmless:

1. a Brownian family for $\mathcal F_t$ is a Brownian family for $\mathcal F^a_t$ (a set of $\mathcal F^a_s$ differs from a set of $\mathcal F_s$ by a null set, so the independence of the increments from the past is preserved);
2. $\mathbb E[X\mid\mathcal F^a_s]=\mathbb E[X\mid\mathcal F_s]$ almost surely, so a process is a martingale for one filtration if and only if it is one for the other, *as long as the martingale property is stated up to null sets* (point (b));
3. on $\mathcal F^a$ one can replace $\psi$ by a version $\tilde\psi$, indistinguishable from $\psi$, with *every* path continuous and adapted to $\mathcal F^a$: put $\tilde\psi=\psi$ outside a measurable null set containing the bad paths, and $\tilde\psi_t=e_0$ on it. After mass conservation is proved, the same trick gives a version with $\lVert\tilde\psi_t\rVert=1$ for all $t$ and all $\omega$.

Hitting times of closed sets by processes with *all* paths continuous are stopping times of the raw filtration (no right-continuity needed), and optional sampling for bounded stopping times is proved by approximating them from above by stopping times with finitely many values. So nothing in Stage 2 needs right-continuity of the filtration.

**(b) What "martingale" and "bracket" mean in the statements.** In the statements given to the author, "$M$ is a continuous square-integrable martingale on $[0,T]$" means: $M$ has continuous paths on $[0,T]$ almost surely, $M_t\in L^2$, and $\mathbb E[M_t\mid\mathcal F_s]=M_s$ almost surely for $s\le t\le T$ (this includes $s=t$, which says that $M_t$ is $\mathcal F_t$-measurable up to a null set). "$\langle M\rangle=A$" means moreover that $A$ is continuous, nondecreasing, $A_0=0$, integrable, and $M^2-A$ is a martingale in the same sense. Quadratic variation is never defined as a general object: every bracket in Sections 2 to 6 is an explicit time integral, and the statements say that this explicit process is the bracket. This is what the article's sentences mean under the usual conditions (the bracket of a continuous $L^2$ martingale being the unique continuous nondecreasing process with this property). The filtration in the statements is the article's $\mathcal F_t$ (or $\mathcal F^n_t=\mathcal F_{nt/2}$), not the augmented one.

**(c) The Itô integral.** Mathlib has none. The project defines one integral, against the whole countable family $(B_i)$, $i\in\mathbb Z\times\lbrace0,1\rbrace$:
$$I_t(h)=\sum_i\int_0^th_i(s)\ dB_i(s),$$
for families $h=(h_i)$ in the $L^2$ closure of *elementary* families (finite sums of $\xi\mathbf 1_{(a,b]}(s)e_i$ with $\xi$ bounded and $\mathcal F_a$-measurable), for the norm $\mathbb E\int_0^T\sum_ih_i(s)^2ds$, on every $[0,T]$. The infinite sums over $x\in\mathbb Z$ of stochastic integrals in the article ($\sum_x\int g_x\ dJ(x)$) are single integrals $I(h)$ of this kind: no separate limit theorem for series of stochastic integrals is needed, Itô's isometry does it. $I(h)$ is defined as the pathwise limit of the elementary integrals along a fast approximating sequence; Doob's $L^2$ inequality and Borel–Cantelli make this limit uniform on compacts, so $I(h)$ has continuous paths almost surely and is adapted, with no further "continuous version" theorem. Proved for it: isometry, martingale property, brackets $\langle I(h),I(g)\rangle_t=\int_0^t\sum_ih_ig_i\ ds$ (which contains $\langle\int f\ dB_i,\int g\ dB_j\rangle=\delta_{ij}\int fg$), stopping, a fourth moment bound for bounded integrands, and the convergence of left-point Riemann sums for bounded left-continuous adapted integrands (so the integral agrees with `itoSum` of the frozen statement). The complex notation $W^{(x)}=(B_{x,0}+iB_{x,1})/\sqrt2$ appears only in one algebraic lemma that rewrites `itoSum` against `complexBM` as real Riemann sums.

**(d) Itô's formula: only the product rule.** For processes $X=X_0+\int a\ ds+I(b)$, $Y=Y_0+\int c\ ds+I(d)$, stopped at a bounded stopping time before which $X,Y,a,c,\sum_ib_i^2,\sum_id_i^2$ are bounded:
$$X_tY_t=X_0Y_0+\int_0^t\Big(X_sc_s+Y_sa_s+\sum_ib_i(s)d_i(s)\Big)ds+I_t(Xd+Yb) .$$
Proof by the classical discretization: $X_{t_{k+1}}Y_{t_{k+1}}-X_{t_k}Y_{t_k}=X_{t_k}\Delta Y_k+Y_{t_k}\Delta X_k+\Delta X_k\Delta Y_k$; the first two sums converge to the stochastic integrals by the isometry and dominated convergence; the sum of $\Delta X_k\Delta Y_k$ converges to $\int\sum_ib_id_i\ ds$ in $L^2$ because it is a sum of martingale differences plus small terms, with the fourth moment bound $\mathbb E[(I_v(h)-I_u(h))^4]\le CK^2(v-u)^2$ when $\sum_ih_i^2\le K$. Everything in Sections 2 to 6 is polynomial in $\psi$, so nothing else is needed. Deterministic $C^1$ factors $\alpha_t(x)$ are Itô processes without diffusion, so time-dependent weights are covered.

**(e) The wave function as an Itô process (identification).** The frozen definition gives, for each $t$ and $x$, that the Riemann sums of $\psi(x\pm1)$ against $W$ converge in probability to $\psi_t(x)-\mathbf 1_{x=0}+\int_0^t\psi_s(x)ds$. Let $\tau_R$ be the first time $\lVert\tilde\psi_t\rVert_{\ell^2}\ge R$, capped at $N$. Before $\tau_R$ the integrands are bounded by $R$; on $\lbrace\tau_R>t\rbrace$ the Riemann sums of $\psi$ coincide with those of the bounded left-continuous integrand $\tilde\psi\mathbf 1_{[0,\tau_R]}$, which converge in $L^2$ to $I(\cdot)$. Hence, almost surely, the real and imaginary parts of $\tilde\psi(x)$ are Itô processes up to $\tau_R$, with explicit coefficients (writing $\psi(y)=u_y+iv_y$):
$$du_x=-u_xdt+\tfrac1{\sqrt2}\big(-v_{x+1}dB_{x,0}-u_{x+1}dB_{x,1}-v_{x-1}dB_{x-1,0}+u_{x-1}dB_{x-1,1}\big),$$
$$dv_x=-v_xdt+\tfrac1{\sqrt2}\big(u_{x+1}dB_{x,0}-v_{x+1}dB_{x,1}+u_{x-1}dB_{x-1,0}+v_{x-1}dB_{x-1,1}\big).$$
The product rule gives $P(t\wedge\tau_R,x)$, with drift $\Delta P$ and the diffusion of $J(x-1)-J(x)$, where in real coordinates $J(x)=\sqrt2\int\big(\mathrm{Im}(\overline{\psi(x)}\psi(x+1))dB_{x,0}+\mathrm{Re}(\overline{\psi(x)}\psi(x+1))dB_{x,1}\big)$, which is $2\int\mathrm{Im}(\overline{\psi(x)}\psi(x+1)dW^{(x)})$.

**(f) Conservation of mass, then no more localization.** Summing over $\lvert x\rvert\le K$: $\sum_{\lvert x\rvert\le K}P(t\wedge\tau_R,x)=1+(\text{flux through }\pm K)+J(-K-1)-J(K)$, stopped. As $K\to\infty$ the flux term tends to $0$ pathwise, and $\mathbb E[J_{t\wedge\tau_R}(K)^2]=2\mathbb E\int_0^{t\wedge\tau_R}P(s,K)P(s,K+1)ds\to0$ by dominated convergence (bounded by $R^4t$). So $\lVert\tilde\psi_{t\wedge\tau_R}\rVert^2=1$, hence $\tau_R=N$ for $R>1$, almost surely. From then on $\lvert\tilde\psi_t(x)\rvert\le1$ and all integrands of the equation of $P$ are bounded by $1$: the rest of Stage 2 uses only global $L^2$ theory. This replaces the a priori bound $P(s,x)P(s,x+1)\le\lVert\psi_s\rVert^4$ and (2.2) used in the article at this point; the article's order (Prop 2.2 before mass conservation) is kept for the statements, not for the proofs.

**(g) The moment bound (2.2)** (the article cites Da Prato–Zabczyk). With truncated weights $w_R(x)=e^{a\min(\lvert x\rvert,R)}$, $V_R(t)=\sum_xw_R(x)P(t,x)\le e^{aR}$ is a bounded Itô process (linear functional with a bounded weight, proved by boxes and mass conservation), with drift $\sum_x\Delta w_R(x)P\le c\ V_R$, $c=2(\cosh a-1)$, and bracket density $\le C\ V_R^2$. The product rule applied to $e^{-c_kt}V_R^k$ shows it is a supermartingale up to a martingale term, so $\mathbb E V_R(t)^k\le e^{c_kt}$; Doob's $L^2$ inequality on the martingale part gives $\mathbb E\sup_{t\le T}V_R(t)^{2k}\le C(a,k,T)$ uniformly in $R$; monotone convergence as $R\to\infty$ gives (2.2). Only $k\le4$ is used later, but the induction gives all $k$.

**(h) Lemma 2.3.** On boxes $\lvert x\rvert\le K$ (resp. $\lvert x_1\rvert,\lvert x_2\rvert\le K$): the product rule, summation by parts with boundary terms, then $K\to\infty$ once, the boundary terms going to $0$ pathwise (drift) and in $L^2$ (martingale part, by the isometry and (2.2) with $k=2$, resp. $k=4$). This is the article's proof. In the statements, the last term of (2.7), (2.8) is not written as a stochastic integral: the statements say that the remainder is a continuous $L^2$ martingale with the explicit bracket. (The stochastic integral representation is kept as an internal lemma for Stage 4, which needs it for a fourth moment bound.)

**(i) Sections 3, 4, 6** follow the article line by line, with three formal differences: (3.10), (3.11), (3.17) (the rescaled currents $\mathsf J_n$) are not stated, because Prop 3.1 is deduced from Lemma 2.3 (1) directly, as in the article, and the bracket (3.15) is read off from (2.7) after a change of time; the identity (6.1) is proved only for the discrete measures $\mathsf Z_n(t)$ that occur; the convergence $b_m\to\int\kappa=1$, which Stage 1 avoided, is proved for Prop 6.2 (a Riemann sum of a Lipschitz compactly supported function).

---

## 2. Infrastructure (packages B and C)

Conventions for all new files: `module`, `public import`, `@[expose] public section`, `noncomputable section`, `namespace QSSEPtoKPZ`, as in Stage 1. Processes are functions `X : ℝ → Ω → E`, like the frozen `ψ`; only times `t ≥ 0` matter. Filtrations are `Filtration ℝ≥0 mΩ`. Mathlib notions indexed by the filtration (martingales, stopping times, `stoppedValue`) are applied to `fun t : ℝ≥0 => X t`. **Stopping times are bounded and `ℝ≥0`-valued** (`τ : Ω → ℝ≥0`), coerced to `WithTop ℝ≥0` for Mathlib's `IsStoppingTime`: every stopping time of Stage 2 is bounded ($\tau_R\wedge N$, $\tau_K\wedge T$, the bounded $\tau$ of Prop 4.3), and this avoids `WithTop` arithmetic. Integrals in time are interval integrals `∫ s in (0 : ℝ)..t`. Energies and suprema in conclusions are written in `ℝ≥0∞` (`lintegral`, `⨆`), with a measurability conjunct when the function could fail to be measurable (Stage 0 and Stage 1 lessons: `lintegral` is the lower integral, `tsum` of a non-summable family is `0`, the integral of a non-integrable function is `0`).

### 2.1 Package B: martingales in continuous time

**Design decision B-1 (null augmentation, no right-continuity).** As in 1.2 (a). Mathlib has the right-continuous augmentation `Filtration.rightCont` (`𝓕₊`), not used. Tau Ceti has a `NullAugmentation` file (ideas only).

```lean
/-- The σ-algebra generated by the measurable `μ`-null sets. -/
@[instance_reducible] def nullSets (μ : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {s | MeasurableSet s ∧ μ s = 0}

/-- `𝓕ᵃ_t = 𝓕_t ∨ σ(null sets)`. -/
def nullAug (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 t ⊔ nullSets μ
  mono' _ _ h := sup_le_sup_right (𝓕.mono h) _
  le' t := sup_le (𝓕.le t) (nullSets_le μ)

/-- `t ↦ 𝓕 (c t)`; with `c = n/2` this is `𝓕ⁿ_t = 𝓕_{nt/2}` of Section 3. -/
def timeChange (c : ℝ≥0) (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (c * t)
  mono' _ _ h := 𝓕.mono (mul_le_mul_of_nonneg_left h c.2)
  le' t := 𝓕.le _
```

Main lemmas of `Martingales/NullAug.lean` (meaning in the comment):

```lean
-- G ∈ 𝓕ᵃ_t ↔ G measurable and G =ᵐ F for some F ∈ 𝓕_t
theorem measurableSet_nullAug_iff : MeasurableSet[nullAug μ 𝓕 t] G ↔ MeasurableSet G ∧ ∃ F, MeasurableSet[𝓕 t] F ∧ G =ᵐ[μ] F
-- E[X | 𝓕ᵃ_t] = E[X | 𝓕_t] a.s.
theorem condExp_nullAug [IsFiniteMeasure μ] (X : Ω → ℝ) (t : ℝ≥0) : μ[X | nullAug μ 𝓕 t] =ᵐ[μ] μ[X | 𝓕 t]
-- an 𝓕ᵃ_t-measurable function is a.e. equal to an 𝓕_t-measurable one
theorem aestronglyMeasurable_of_nullAug : StronglyMeasurable[nullAug μ 𝓕 t] X → AEStronglyMeasurable[𝓕 t] X μ
theorem IsBrownianFamily.nullAug (hB : IsBrownianFamily 𝓕 B μ) : IsBrownianFamily (nullAug μ 𝓕) B μ
theorem IsWaveFunction.nullAug (hψ : IsWaveFunction L 𝓕 B ψ μ) : IsWaveFunction L (nullAug μ 𝓕) B ψ μ
-- good version of an a.s. continuous adapted process (𝓖 contains the null sets)
theorem exists_continuous_version (h0 : nullSets μ ≤ 𝓖 0) (hX : ∀ t : ℝ≥0, StronglyMeasurable[𝓖 t] (X t))
    (hc : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => X t ω) :
    ∃ X', (∀ t : ℝ≥0, StronglyMeasurable[𝓖 t] (X' t)) ∧ (∀ ω, Continuous fun t : ℝ≥0 => X' t ω) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, X' t ω = X t ω
```

The specialization to $\psi$ (elaborated):

```lean
theorem IsWaveFunction.exists_good (hψ : IsWaveFunction L 𝓕 B ψ μ) :
    ∃ ψ' : ℝ → Ω → lp (fun _ : ℤ => ℂ) 2, IsWaveFunction L (nullAug μ 𝓕) B ψ' μ ∧
      (∀ ω, Continuous fun t : ℝ≥0 => ψ' t ω) ∧
      (∀ ω, ∀ (t : ℝ≥0) (x : ℤ), x ∉ box L → ψ' t ω x = 0) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ψ' t ω = ψ t ω
```

**Design decision B-2 (the article-facing martingale notions are "up to null sets").** Defined in `Martingales/Defs.lean`, part of what the author approves (all three elaborated):

```lean
/-- `M` is a continuous square-integrable martingale on `[0, T]` with respect to `𝓕`, up to null
sets: a.s. continuous paths on `[0, T]`, `M t ∈ L²`, and `𝔼[M t | 𝓕 s] = M s` a.s. for
`s ≤ t ≤ T` (the case `s = t` says that `M t` is a.e. equal to an `𝓕 t`-measurable function). -/
structure IsCL2Mart (T : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (M : ℝ → Ω → ℝ) (μ : Measure Ω) : Prop where
  cont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T)
  memLp : ∀ t : ℝ≥0, (t : ℝ) ≤ T → MemLp (M t) 2 μ
  condExp : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T → μ[M t | 𝓕 s] =ᵐ[μ] M s

/-- `⟨M⟩ = A` on `[0, T]`: `M` is a continuous L² martingale, `A` is integrable, a.s. continuous,
nondecreasing, `A 0 = 0`, and `M² - A` is a martingale. -/
structure HasBracket (T : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (M A : ℝ → Ω → ℝ) (μ : Measure Ω) : Prop
    extends IsCL2Mart T 𝓕 M μ where
  integrable_bracket : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Integrable (A t) μ
  zero : ∀ᵐ ω ∂μ, A 0 ω = 0
  mono : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Set.Icc 0 T)
  cont_bracket : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 T)
  condExp_sq : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T →
    μ[fun ω => M t ω ^ 2 - A t ω | 𝓕 s] =ᵐ[μ] fun ω => M s ω ^ 2 - A s ω

/-- `⟨M, N⟩ = A` on `[0, T]`. -/
structure HasCovariation (T : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (M N A : ℝ → Ω → ℝ) (μ : Measure Ω) : Prop where
  left : IsCL2Mart T 𝓕 M μ
  right : IsCL2Mart T 𝓕 N μ
  condExp_mul : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ T →
    μ[fun ω => M t ω * N t ω - A t ω | 𝓕 s] =ᵐ[μ] fun ω => M s ω * N s ω - A s ω
```

Transfer lemmas (`Martingales/NullAug.lean`): `IsCL2Mart` and `HasBracket` hold for `𝓕` iff they hold for `nullAug μ 𝓕`; they are stable under indistinguishability of `M` and `A` (`∀ᵐ ω, ∀ t, M t ω = M' t ω`); under time change (`HasBracket (c*T) 𝓕 M A μ → HasBracket T (timeChange c 𝓕) (fun t => M (c*t)) (fun t => A (c*t)) μ`); under restriction of `T`; `Martingale (fun t : ℝ≥0 => M t) 𝓖 μ` plus a.s. continuity and `L²` gives `IsCL2Mart`; and conversely an `IsCL2Mart` for `nullAug μ 𝓕` has a version which is a Mathlib `Martingale` with all paths continuous (from `exists_continuous_version` and the `s = t` case). Internally, packages B and C work with Mathlib's `Martingale` and versions with all paths continuous; only the article-facing statements use the a.e. notions.

**Design decision B-3 (continuous time from discrete time by dyadic grids and path continuity).** For a process with a.s. continuous paths on $[0,T]$, $\sup_{[0,T]}$ equals the supremum over the countable set $D_T=\lbrace k2^{-j}T\rbrace$, which is the increasing limit of the maxima over the finite grids $D_T^j$. On each grid the process indexed by $k\in\mathbb N$, with filtration $\mathcal F_{k2^{-j}T}$, is a discrete (sub)martingale, so Mathlib's `MeasureTheory.maximal_ineq` applies; monotone convergence passes to the limit. Mathlib v4.35.0 has Doob's maximal inequality (weak type) but **not** Doob's $L^p$ inequality (its docstring says it is "upcoming"); the $L^2$ inequality in discrete time is proved here from `maximal_ineq` and the layer-cake formula, by the classical argument $\mathbb E[(X^\ast )^2]=2\int_0^\infty\lambda\mu(X^\ast \ge\lambda)d\lambda\le2\mathbb E[X_NX^\ast ]\le2\lVert X_N\rVert_2\lVert X^\ast \rVert_2$ (Tau Ceti's `MaximalInequality/L2` may be read for ideas).

```lean
/-- Doob's L² inequality, continuous time: 𝔼 sup_{[0,T]} M² ≤ 4 𝔼 M_T². -/
theorem IsCL2Mart.lintegral_iSup_sq_le [IsProbabilityMeasure μ] (hM : IsCL2Mart T 𝓕 M μ) :
    AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2)) μ ∧
    ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (M t ω ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (M T ω ^ 2) ∂μ

/-- Doob's maximal inequality for a nonnegative continuous martingale. -/
theorem IsCL2Mart.measure_exists_ge_le [IsProbabilityMeasure μ] (hM : IsCL2Mart T 𝓕 M μ)
    (hpos : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ M t ω) {K : ℝ} (hK : 0 < K) :
    μ {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, K ≤ M t ω} ≤ ENNReal.ofReal ((∫ ω, M T ω ∂μ) / K)
```
(plus the discrete $L^2$ inequality for Mathlib `Submartingale`s indexed by `ℕ`, and a version of the $L^2$ inequality for nonnegative submartingales, used for $\sup_tV_R(t)^{k}$ in (2.2)).

**Design decision B-4 (stopping times and optional sampling by discretization from above).** For $\tau:\Omega\to\mathbb R_{\ge0}$ bounded, $\tau_j=\lceil2^j\tau\rceil2^{-j}$ is a stopping time with finitely many values, $\tau_j\downarrow\tau$, and $\mathcal F_\tau\subseteq\mathcal F_{\tau_j}$. Mathlib's `MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range` gives optional sampling at $\tau_j$ directly in continuous index. Path continuity and uniform integrability (`MeasureTheory.Integrable.uniformIntegrable_condExp_filtration`, Vitali `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`) pass to the limit. One general lemma covers all uses (optional sampling, the stopping-time form of (4.7), the stopped brackets):

```lean
/-- If `𝔼[V_t | 𝓕_t] = Y_t` for every deterministic `t ≤ T`, `V` and `Y` have a.s. continuous paths,
`Y` is adapted and `sup_{t ≤ T} (|V_t| + |Y_t|)` is integrable, then `𝔼[V_τ | 𝓕_τ] = Y_τ` for every
stopping time `τ ≤ T`.  (Applied with `V_t = M_T`, `Y_t = M_t` this is optional sampling; with
`V_t = 𝒲(t+s)²` it is the stopping-time form of (4.7).) -/
theorem condExp_stopped_of_forall [IsProbabilityMeasure μ] {V Y : ℝ → Ω → ℝ} {T : ℝ≥0}
    (hV : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => V t ω) (hY : ∀ᵐ ω ∂μ, Continuous fun t : ℝ≥0 => Y t ω)
    (hYa : ∀ t : ℝ≥0, AEStronglyMeasurable[nullAug μ 𝓕 t] (Y t) μ)
    (hdom : Integrable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (|V t ω| + |Y t ω|)) μ)
    (h : ∀ t : ℝ≥0, t ≤ T → μ[V t | 𝓕 t] =ᵐ[μ] Y t)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T) :
    μ[fun ω => V (τ ω) ω | hτ.measurableSpace] =ᵐ[μ] fun ω => Y (τ ω) ω

theorem IsCL2Mart.condExp_stopped [IsProbabilityMeasure μ] (hM : IsCL2Mart T 𝓕 M μ)
    {σ τ : Ω → ℝ≥0} (hσ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (nullAug μ 𝓕) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : σ ≤ τ) (hτT : ∀ ω, τ ω ≤ T) :
    μ[fun ω => M (τ ω) ω | hσ.measurableSpace] =ᵐ[μ] fun ω => M (σ ω) ω

-- stopped martingale and stopped bracket
theorem HasBracket.stopped (h : HasBracket T 𝓕 M A μ) (hτ : …) (hτT : ∀ ω, τ ω ≤ T) :
    HasBracket T 𝓕 (fun t ω => M (min t (τ ω)) ω) (fun t ω => A (min t (τ ω)) ω) μ

/-- First time `X ≥ K`, capped at `T`. -/
def hitTime (X : ℝ → Ω → ℝ) (K T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf ({t : ℝ≥0 | (K : ℝ) ≤ X t ω} ∪ {T}) ⊓ T

theorem isStoppingTime_hitTime (hX : ∀ t : ℝ≥0, Measurable[𝓕 t] (X t))
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (K T : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => (hitTime X K T ω : WithTop ℝ≥0))
```

`isStoppingTime_hitTime` holds for the raw filtration because all paths are continuous: $\lbrace\tau\le t\rbrace=\lbrace\sup_{s\in D\cap[0,t]\cup\lbrace t\rbrace}X_s\ge K\rbrace$ for $t<T$. Mathlib's `Adapted.isStoppingTime_hittingAfter` is for countable index only and is not used.

### 2.2 Package C: the Itô integral against the Brownian family

Generic over a countable index type `ι` (applied with `ι = ℤ × Fin 2`), a filtration `𝓖`, a probability measure `μ` and `hB : IsBrownianFamily 𝓖 B μ`. No completeness of `𝓖` is needed in this package.

**Design decision C-1 (integrands are families indexed by `ι`; one integral for all of them).** A family `h : ι → ℝ → Ω → ℝ`. Its energy on $[0,T]$ is $\mathbb E\int_0^T\sum_ih_i(s)^2ds$, in `ℝ≥0∞`. The infinite sums over $x$ of the article are absorbed here.

**Design decision C-2 (elementary integrands as lists of blocks).** A block is $\xi\mathbf 1_{(a,b]}(s)e_i$ with $\xi$ bounded and $\mathcal G_a$-measurable; an elementary integrand is a finite list of blocks (overlaps allowed). Sums are concatenations, so linearity is free; a "common refinement" lemma rewrites any list on a common grid with disjoint intervals, where the isometry and the martingale computations are done once. The elementary integral at time $t$ is $\sum_{\text{blocks}}\xi\ (B_i(b\wedge t)-B_i(a\wedge t))$: it is $\mathcal G_t$-measurable for *every* $\omega$, and has a.s. continuous paths. (All elaborated.)

```lean
structure ElemBlock (𝓖 : Filtration ℝ≥0 mΩ) (ι : Type*) where
  a : ℝ≥0
  b : ℝ≥0
  i : ι
  ξ : Ω → ℝ
  meas : Measurable[𝓖 a] ξ
  bdd : ∃ C, ∀ ω, |ξ ω| ≤ C

abbrev ElemIntegrand (𝓖 : Filtration ℝ≥0 mΩ) (ι : Type*) := List (ElemBlock 𝓖 ι)

open Classical in
def ElemIntegrand.toFun (e : ElemIntegrand 𝓖 ι) : ι → ℝ → Ω → ℝ :=
  fun i s ω => (e.map fun bl => if bl.i = i ∧ (bl.a : ℝ) < s ∧ s ≤ bl.b then bl.ξ ω else 0).sum

def ElemIntegrand.integral (e : ElemIntegrand 𝓖 ι) (B : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (e.map fun bl => bl.ξ ω * (B bl.i (min t bl.b) ω - B bl.i (min t bl.a) ω)).sum

/-- `∫_0^T ∑ᵢ hᵢ(s)² ds`, pathwise. -/
def pathEnergy (h : ι → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioc 0 T, ∑' i, ‖h i s ω‖ₑ ^ 2
/-- `𝔼 ∫_0^T ∑ᵢ hᵢ(s)² ds`. -/
def energy (μ : Measure Ω) (h : ι → ℝ → Ω → ℝ) (T : ℝ) : ℝ≥0∞ := ∫⁻ ω, pathEnergy h T ω ∂μ
```

Elementary facts (`ItoIntegral/Elementary.lean`): for $s\le t$, $\mathbb E[I_t(e)\mid\mathcal G_s]=I_s(e)$; $\mathbb E\big[I_t(e)I_t(e')-\int_0^t\sum_ie_ie'_i\mid\mathcal G_s\big]=I_s(e)I_s(e')-\int_0^s\sum_ie_ie'_i$; isometry. Tools: `IsBrownianFamily.indep_past` (joint independence of all increments on $[s,t]$ from $\mathcal G_s$), `IsBrownianFamily.indep`, `IsBrownianFamily.gaussian`, `MeasureTheory.condExp_indep_eq`, `MeasureTheory.condExp_mul_of_stronglyMeasurable_left` (pull-out), `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`; the lemma `iIndepFun_of_indep_past` of `Checks.lean` shows the pattern.

Fourth moment (`ItoIntegral/FourthMoment.lean`): if $\sum_ih_i(s)^2\le K$ on $(u,v]$, then $\mathbb E[(I_v(h)-I_u(h))^4]\le 6K^2(v-u)^2$. For elementary $h$, by induction over the grid: $\mathbb E S_{k+1}^4=\mathbb E S_k^4+6\mathbb E[S_k^2\sum_i\xi_i^2]\Delta_k+3\mathbb E[(\sum_i\xi_i^2)^2]\Delta_k^2$ (Gaussian moments $\mathbb E G^4=3$). Passes to the limit by Fatou along an a.s. convergent subsequence, after clipping the approximants (radial projection onto the ball of radius $\sqrt K$ in $\ell^2(\iota)$ is $1$-Lipschitz).

**Design decision C-3 (the closure, and the integral as a pathwise limit).** (Elaborated.)

```lean
/-- `h` is Itô-integrable: jointly measurable, and the limit for the energy on every `[0, T]` of a
single sequence of elementary integrands. -/
structure IsItoIntegrable (𝓖 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (h : ι → ℝ → Ω → ℝ) : Prop where
  meas : ∀ i, Measurable fun p : ℝ × Ω => h i p.1 p.2
  approx : ∃ e : ℕ → ElemIntegrand 𝓖 ι, ∀ T : ℝ,
    Tendsto (fun k => energy μ (fun i s ω => (e k).toFun i s ω - h i s ω) T) atTop (𝓝 0)

lemma IsItoIntegrable.exists_fast (hh : IsItoIntegrable 𝓖 μ h) :
    ∃ e : ℕ → ElemIntegrand 𝓖 ι, ∀ k : ℕ,
      energy μ (fun i s ω => (e k).toFun i s ω - h i s ω) k ≤ (8 : ℝ≥0∞)⁻¹ ^ k

open Classical in
/-- `∑ᵢ ∫_0^t hᵢ(s) dBᵢ(s)`: the pathwise limit of the elementary integrals along a fast
approximating sequence (`0` if `h` is not Itô-integrable). -/
def stochInt (𝓖 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (B : ι → ℝ → Ω → ℝ)
    (h : ι → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if hh : IsItoIntegrable 𝓖 μ h then
    limUnder atTop fun k => (hh.exists_fast.choose k).integral B t ω
  else 0
```

Why it works: by Doob's $L^2$ inequality for the elementary martingales, $\mathbb E\sup_{t\le T}\lvert I_t(e_{k+1})-I_t(e_k)\rvert^2\le16\cdot8^{-k}$ for $k\ge T$; by Borel–Cantelli (`MeasureTheory.measure_limsup_atTop_eq_zero`) the convergence is a.s. uniform on every $[0,T]$, so the limit has a.s. continuous paths; measurability of the limit comes from `MeasureTheory.StronglyMeasurable.limUnder`, so `stochInt` is $\mathcal G_t$-measurable for every $\omega$. Main theorems (`ItoIntegral/Basic.lean`; elaborated):

```lean
theorem stochInt_adapted (hB : IsBrownianFamily 𝓖 B μ) (t : ℝ≥0) : Measurable[𝓖 t] (stochInt 𝓖 μ B h t)
theorem hasBracket_stochInt (hB : IsBrownianFamily 𝓖 B μ) (hh : IsItoIntegrable 𝓖 μ h) (T : ℝ) :
    HasBracket T 𝓖 (stochInt 𝓖 μ B h) (fun t ω => ∫ s in (0 : ℝ)..t, ∑' i, h i s ω ^ 2) μ
theorem condExp_stochInt_mul (hB : IsBrownianFamily 𝓖 B μ) (hh : IsItoIntegrable 𝓖 μ h)
    (hg : IsItoIntegrable 𝓖 μ g) {s t : ℝ≥0} (hst : s ≤ t) :
    μ[fun ω => stochInt 𝓖 μ B h t ω * stochInt 𝓖 μ B g t ω -
        ∫ r in (0 : ℝ)..t, ∑' i, h i r ω * g i r ω | 𝓖 s] =ᵐ[μ]
      fun ω => stochInt 𝓖 μ B h s ω * stochInt 𝓖 μ B g s ω - ∫ r in (0 : ℝ)..s, ∑' i, h i r ω * g i r ω
```
together with: linearity (a.s., for all $t$); the isometry $\mathbb E[(I_t(h)-I_t(g))^2]=\mathbb E\int_0^t\sum_i(h_i-g_i)^2$ (the `HasBracket` above contains it); if the energy of $h_k-h$ on $[0,T]$ tends to $0$, then $\sup_{t\le T}\lvert I_t(h_k)-I_t(h)\rvert\to0$ in $L^2$; the fourth moment bound.

**Integrands that occur (`ItoIntegral/Integrands.lean`).** No general density theorem for progressive processes is proved. Instead, membership in the closure is proved for the shapes that occur:

1. bounded, left-continuous, adapted, jointly measurable families with $\sum_ih_i^2\le K$ (left-point dyadic steps converge pointwise by left-continuity, finite truncations of `ι` converge by dominated convergence);
2. $h\cdot\mathbf 1_{\lbrace s\le\tau\rbrace}$ for $h$ integrable and $\tau$ a bounded stopping time (first $\tau$ with finitely many values, where $\mathbf 1_{s\le\tau}=\mathbf 1_{\tau>t_k}$ on $(t_k,t_{k+1}]$ is $\mathcal G_{t_k}$-measurable; then $\tau_j\downarrow\tau$);
3. products with a bounded continuous adapted scalar process; sums; limits for the energy.

Riemann sums (the bridge to `itoSum`; elaborated):
```lean
theorem tendsto_riemann_stochInt [DecidableEq ι] (hB : IsBrownianFamily 𝓖 B μ) {f : ℝ → Ω → ℝ} (i : ι)
    {K : ℝ} (hf : ∀ s ω, |f s ω| ≤ K) (hfa : ∀ t : ℝ≥0, Measurable[𝓖 t] (f t))
    (hlc : ∀ ω (s : ℝ), 0 < s → ContinuousWithinAt (fun r => f r ω) (Set.Iic s) s)
    (hfm : Measurable fun p : ℝ × Ω => f p.1 p.2) (t : ℝ≥0) :
    Tendsto (fun m : ℕ => eLpNorm (fun ω => (∑ k ∈ Finset.range m,
        f (k * t / m) ω * (B i ((k + 1) * t / m) ω - B i (k * t / m) ω)) -
        stochInt 𝓖 μ B (fun j s ω => if j = i ∧ s ≤ t then f s ω else 0) t ω) 2 μ) atTop (𝓝 0)
```

**Stopping (`ItoIntegral/Stopping.lean`).** $I_t(h\mathbf 1_{[0,\tau]})=I_{t\wedge\tau}(h)$ a.s. for all $t$; $I_t(\xi\mathbf 1_{(u,\infty)}h)=\xi\ (I_t(h)-I_{t\wedge u}(h))$ for $\xi$ bounded $\mathcal G_u$-measurable (needed in the product rule). Both: elementary case and $\tau$ with finitely many values first, then limits.

**Design decision C-4 (Itô processes stopped at a bounded stopping time; the product rule).** (Elaborated.)

```lean
/-- `X_{t∧τ} = X_0 + ∫_0^{t∧τ} a ds + I_t(b 𝟙_{[0,τ]})` for all `t`, a.s. -/
def IsItoProcessUpTo (𝓖 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (B : ι → ℝ → Ω → ℝ)
    (τ : Ω → ℝ≥0) (X a : ℝ → Ω → ℝ) (b : ι → ℝ → Ω → ℝ) : Prop :=
  IsItoIntegrable 𝓖 μ (fun i s ω => if s ≤ τ ω then b i s ω else 0) ∧
  ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, X (min t (τ ω)) ω = X 0 ω + (∫ s in (0 : ℝ)..(min t (τ ω) : ℝ≥0), a s ω) +
    stochInt 𝓖 μ B (fun i s ω => if s ≤ τ ω then b i s ω else 0) t ω

/-- **Product rule.** -/
theorem IsItoProcessUpTo.mul (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0))) {X Y a c : ℝ → Ω → ℝ}
    {b d : ι → ℝ → Ω → ℝ} {K : ℝ}
    (hX : IsItoProcessUpTo 𝓖 μ B τ X a b) (hY : IsItoProcessUpTo 𝓖 μ B τ Y c d)
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hYc : ∀ ω, Continuous fun t : ℝ≥0 => Y t ω)
    (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t)) (hYa : ∀ t : ℝ≥0, Measurable[𝓖 t] (Y t))
    (hbd : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω →
      |X s ω| ≤ K ∧ |Y s ω| ≤ K ∧ |a s ω| ≤ K ∧ |c s ω| ≤ K ∧
      ∑' i, b i s ω ^ 2 ≤ K ∧ ∑' i, d i s ω ^ 2 ≤ K)
    (hameas : Measurable fun p : ℝ × Ω => a p.1 p.2) (hcmeas : Measurable fun p : ℝ × Ω => c p.1 p.2) :
    IsItoProcessUpTo 𝓖 μ B τ (fun t ω => X t ω * Y t ω)
      (fun s ω => X s ω * c s ω + Y s ω * a s ω + ∑' i, b i s ω * d i s ω)
      (fun i s ω => X s ω * d i s ω + Y s ω * b i s ω)
```
Corollaries in the same file: linear combinations of Itô processes; a deterministic $C^1$ function of time is an Itô process with $b=0$; summability bookkeeping when the families $b,d$ have finite support in `ι` (the case of $\psi(x)$, with 4 nonzero indices).

**Design decision C-5 (complex notation only in one algebraic lemma).** `ItoIntegral/Complex.lean`: with $f=f_1+if_2$ and $W^{(x)}=$ `complexBM B x`,
$$\texttt{itoSum}\ f\ W^{(x)}=\tfrac1{\sqrt2}\big(R(f_1,B_{x,0})-R(f_2,B_{x,1})+i\ (R(f_2,B_{x,0})+R(f_1,B_{x,1}))\big),$$
where $R(g,B_i)$ is the real left-point Riemann sum, and the analogous formula for $\overline{W^{(x-1)}}$; then convergence in measure of complex sums from that of their real and imaginary parts.

### 2.3 Main Mathlib tools (names checked with `#check` in v4.35.0)

| Use | Lemma |
|---|---|
| Doob, discrete | `MeasureTheory.maximal_ineq`, `MeasureTheory.Submartingale.expected_stoppedValue_mono` |
| Layer cake (Doob $L^2$) | `lintegral_rpow_eq_lintegral_meas_le_mul`, `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` |
| Optional sampling | `MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range`, `MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp`, `MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable_range`, `MeasureTheory.IsStoppingTime.measurableSpace` |
| Uniform integrability, Vitali | `MeasureTheory.Integrable.uniformIntegrable_condExp_filtration`, `MeasureTheory.Integrable.uniformIntegrable_condExp`, `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`, `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite` |
| Conditional expectation | `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`, `MeasureTheory.condExp_indep_eq`, `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`, `MeasureTheory.condExp_condExp_of_le`, `MeasureTheory.Filtration.condExp_condExp`, `MeasureTheory.condExp_mono`, `MeasureTheory.condExp_add`, `MeasureTheory.condExp_of_aestronglyMeasurable'`, `MeasureTheory.setIntegral_condExp`, `MeasureTheory.integral_condExp`, `MeasureTheory.eLpNorm_condExp_le_eLpNorm`, `MeasureTheory.tendsto_condExp_unique`, `MeasureTheory.Martingale.condExp_ae_eq` |
| Independence | `ProbabilityTheory.iIndepFun`, `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` |
| Convergence in measure | `MeasureTheory.tendstoInMeasure_ae_unique`, `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`, `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` |
| Borel–Cantelli | `MeasureTheory.measure_limsup_atTop_eq_zero` |
| Measurability | `MeasureTheory.StronglyMeasurable.limUnder`, `measurable_uncurry_of_continuous_of_measurable` |
| Integrals | `MeasureTheory.tendsto_integral_of_dominated_convergence`, `MeasureTheory.tendsto_lintegral_of_dominated_convergence`, `MeasureTheory.lintegral_tsum`, `MeasureTheory.integral_tsum`, `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` |
| ODE uniqueness ($\mathbb E P=p_t$) | `ODE_solution_unique` |
| Versions | `ProbabilityTheory.Indistinguishable` (optional) |
| From Stage 1 | `uN`, `uN_bounds`, `uN_le_one_add_sqrt`, `hasDerivAt_uN_apply`, `uN_regularity`, `uN_neg`, `chainGen`, `constants_bounds`, `gM` and Lemma 6.3, `kM`, `bM`, `bM_bounds`, `tsum_chainPi_mul_kM`, `IsMollifier`, `kappa` |

---

## 3. The article's results in Lean

**All the statements of this section are article results: they go to the author for approval before their proofs (CLAUDE.md, rule 5).** The definitions they use (`Martingales/Defs.lean`, `TiltedField/Defs.lean`, `Replacement/CorrectorDefs.lean`, `rwKernel`) are part of what is approved. The infrastructure of Section 2 is not submitted to the author, except the three definitions `IsCL2Mart`, `HasBracket`, `HasCovariation`, which carry the meaning of "martingale" and "bracket".

General rules applied: (i) every `tsum` and every interval integral of an article statement has its summability or integrability asserted in the conclusion, so that a statement cannot hold because of Lean's conventions; (ii) constants "depending only on $\rho$" are written `∃ C, ∀ (probability space, ψ, n, m, T, …)`; (iii) $\lVert\phi\rVert_{1,3}$ enters through a hypothesis "$\lVert\phi\rVert_{1,3}\le C$" (`IsC13 T φ φt C`), and the inequality is claimed with $C$ in place of the norm, for every such $C$, which is equivalent; (iv) the hypotheses on $(\Omega,\mathcal F,\mu,B,\psi)$ are always `[IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)`, written `(hB) (hψ)` below.

Signatures marked (E) were elaborated in the scratch files (with `sorry` proofs); the others are to be written in the same style by task T0.

### 3.1 Section 2 (`WaveFunction/`)

```lean
/-- The discrete Laplacian on ℤ. -/
def lap (f : ℤ → ℝ) (x : ℤ) : ℝ := f (x + 1) + f (x - 1) - 2 * f x

/-- `p_t = e^{tΔ} δ₀`, the law at time `t` of the simple random walk with rate 1 to each
neighbour, started from 0 (defined analytically, as `uN` in Stage 1). -/
def rwKernel (t : ℝ) (x : ℤ) : ℝ := (NormedSpace.exp (t • lapOp) delta0) x   -- lapOp : BddZ →L[ℝ] BddZ

/-- **Proposition 2.2**, (2.3)-(2.5), for `L = ∞`. (E, without the last conjunct) -/
theorem prop_2_2 (hB) (hψ) :
    ∃ J : ℤ → ℝ → Ω → ℝ,
      -- (2.3): J_t(x) = 2 ∫_0^t Im(conj ψ_s(x) ψ_s(x+1) dW_s^{(x)}), as a limit of Riemann sums
      (∀ (x : ℤ) (t : ℝ≥0), TendstoInMeasure μ (fun m ω => 2 * (itoSum
          (fun s ω => conj (ψ s ω x) * ψ s ω (x + 1)) (complexBM B x) t m ω).im) atTop (J x t)) ∧
      -- (2.4)
      (∀ᵐ ω ∂μ, ∀ (t : ℝ≥0) (x : ℤ), density ψ ω t x = (if x = 0 then 1 else 0) +
          (∫ s in (0 : ℝ)..t, lap (density ψ ω s) x) + J (x - 1) t ω - J x t ω) ∧
      -- (2.5)
      (∀ (x : ℤ) (T : ℝ), HasBracket T 𝓕 (J x)
          (fun t ω => 2 * ∫ s in (0 : ℝ)..t, density ψ ω s x * density ψ ω s (x + 1)) μ) ∧
      (∀ x y : ℤ, x ≠ y → ∀ T : ℝ, HasCovariation T 𝓕 (J x) (J y) 0 μ) ∧
      -- 𝔼 P(t,x) = p_t(x)
      (∀ (t : ℝ≥0) (x : ℤ), Integrable (fun ω => density ψ ω t x) μ ∧
          ∫ ω, density ψ ω t x ∂μ = rwKernel t x)

/-- Conservation of the mass (the consequence of (2.7) with α ≡ 1 stated after Lemma 2.3). (E) -/
theorem hasSum_density (hB) (hψ) : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, HasSum (density ψ ω t) 1

/-- **Proposition 2.1, (2.2)**: 𝔼 sup_{t ≤ T} ‖ψ_t‖_a^{2k} < ∞. (E) -/
theorem moment_bound (hB) (hψ) {a T : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      ∑' x : ℤ, ENNReal.ofReal (Real.exp (a * |(x : ℝ)|) * density ψ ω t x)) ^ k ∂μ < ⊤

/-- **Lemma 2.3 (1)**, (2.7). The last term of (2.7) is the martingale `M` below. (E, without the
interval-integrability conjunct) -/
theorem lemma_2_3_linear (hB) (hψ) {T a C : ℝ} {α α' : ℝ → ℤ → ℝ}
    (hα : ∀ x, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (α · x) (α' t x) (Set.Icc 0 T) t)
    (hα' : ∀ x, ContinuousOn (α' · x) (Set.Icc 0 T))
    (hbd : ∀ x, ∀ t ∈ Set.Icc 0 T, |α t x| + |α' t x| ≤ C * Real.exp (a * |(x : ℝ)|)) :
    (∀ᵐ ω ∂μ, (∀ t ∈ Set.Icc 0 T,
      Summable (fun x => |α t x| * density ψ ω t x) ∧
      Summable (fun x => |α' t x + lap (α t) x| * density ψ ω t x)) ∧
      IntervalIntegrable (fun s => ∑' x, (α' s x + lap (α s) x) * density ψ ω s x) volume 0 T) ∧
    HasBracket T 𝓕
      (fun t ω => ∑' x, α t x * density ψ ω t x - α 0 0 -
        ∫ s in (0 : ℝ)..t, ∑' x, (α' s x + lap (α s) x) * density ψ ω s x)
      (fun t ω => ∫ s in (0 : ℝ)..t, ∑' x,
        2 * (α s (x + 1) - α s x) ^ 2 * density ψ ω s x * density ψ ω s (x + 1)) μ

/-- The generator `𝒬` of (2.6). -/
def inclGen (f : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ := lap (f · x₂) x₁ + lap (f x₁ ·) x₂ +
  if |x₁ - x₂| = 1 then f x₁ x₁ + f x₂ x₂ - 2 * f x₁ x₂ else 0

/-- **Lemma 2.3 (2)**, (2.8). Same shape: hypotheses `f t x₁ x₂ = f t x₂ x₁`, `C¹` in time on
`[0,T]` with continuous derivative `f'`, `|f| + |f'| ≤ C e^{a(|x₁|+|x₂|)}`; conclusions: absolute
summability of the double series, interval integrability of the drift, and
`HasBracket T 𝓕 (∑∑ f P P - f 0 0 0 - ∫ ∑∑ (f' + 𝒬 f) P P) (∫ ∑_x 2 (2 ∑_{x'} (f(x+1,x') - f(x,x')) P(x'))² P(x) P(x+1))`. -/
theorem lemma_2_3_quadratic …
```

The bracket in `lemma_2_3_linear` is that of $\int\sum_x(\alpha_s(x+1)-\alpha_s(x))dJ_s(x)$ by (2.5): $\sum_x(\nabla\alpha)^2\ d\langle J(x)\rangle=\sum_x(\nabla\alpha)^2\ 2P(x)P(x+1)ds$.

### 3.2 Section 3 (`TiltedField/`)

Definitions (`TiltedField/Defs.lean`; all (E)). `rescaledPosition` of the frozen statement is $y_n(t,x)$ of (3.4).

```lean
/-- 𝔷_n(t,x) = exp(θ_n x - n λ_n t / 2) P(nt/2, x), (3.3). -/
def zN (n : ℝ) (ψ : ℝ → Ω → ℓ²(ℤ, ℂ)) (ω : Ω) (t : ℝ) (x : ℤ) : ℝ :=
  Real.exp (thetaN n * x - n * lambdaN n / 2 * t) * density ψ ω (n * t / 2) x
/-- 𝒵_n(t; φ) = ∑_x 𝔷_n(t,x) φ(y_n(t,x)), after (3.5). -/
def pairZ (n : ℝ) (ψ) (ω : Ω) (t : ℝ) (φ : ℝ → ℝ) : ℝ := ∑' x : ℤ, zN n ψ ω t x * φ (rescaledPosition n t x)
/-- 𝒲_n(t), (3.6). -/
def WN (n : ℝ) (ψ) (t : ℝ) (ω : Ω) : ℝ := pairZ n ψ ω t fun _ => 1
/-- ℰ_n(t; φ), (3.12). -/
def EN (n : ℝ) (ψ) (ω : Ω) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  n ^ (1 / 2 : ℝ) * ∑' x : ℤ, zN n ψ ω t x * zN n ψ ω t (x + 1) *
    φ (rescaledPosition n t x) * φ (rescaledPosition n t (x + 1))
/-- 𝒜_n φ, (3.13). -/
def AN (n : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  n / 2 * (Real.exp (thetaN n) * φ (y + n ^ (-1 / 2 : ℝ)) +
    Real.exp (-thetaN n) * φ (y - n ^ (-1 / 2 : ℝ)) - 2 * cN n * φ y) - n ^ (1 / 4 : ℝ) * deriv φ y
/-- φ ∈ C_b^{1,3}([0,T] × ℝ), with time derivative φt, and ‖φ‖_{1,3} ≤ C. -/
structure IsC13 (T : ℝ) (φ φt : ℝ → ℝ → ℝ) (C : ℝ) : Prop where
  contDiff : ∀ t ∈ Set.Icc 0 T, ContDiff ℝ 3 (φ t)
  hasDerivWithinAt : ∀ x, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (φ · x) (φt t x) (Set.Icc 0 T) t
  continuousOn : ContinuousOn (Function.uncurry φt) (Set.Icc 0 T ×ˢ Set.univ) ∧
    ∀ k ≤ 3, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (φ p.1) p.2) (Set.Icc 0 T ×ˢ Set.univ)
  bound : ∃ c : Fin 5 → ℝ, ∑ i, c i ≤ C ∧ ∀ t ∈ Set.Icc 0 T, ∀ x,
    |φ t x| ≤ c 0 ∧ |φt t x| ≤ c 1 ∧ |iteratedDeriv 1 (φ t) x| ≤ c 2 ∧
    |iteratedDeriv 2 (φ t) x| ≤ c 3 ∧ |iteratedDeriv 3 (φ t) x| ≤ c 4
/-- M_n^φ(t), (3.14). -/
def MN (n : ℝ) (ψ) (φ φt : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  pairZ n ψ ω t (φ t) - φ 0 0 - ∫ s in (0 : ℝ)..t, pairZ n ψ ω s (fun y => φt s y + AN n (φ s) y)
/-- The bracket (3.15). -/
def QN (n : ℝ) (ψ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  n * ∫ s in (0 : ℝ)..t, ∑' x : ℤ, zN n ψ ω s x * zN n ψ ω s (x + 1) *
    (Real.exp (thetaN n / 2) * φ s (rescaledPosition n s (x + 1)) -
      Real.exp (-thetaN n / 2) * φ s (rescaledPosition n s x)) ^ 2
/-- 𝓕ⁿ_t = 𝓕_{nt/2}. -/
def filtN (n : ℝ) (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ := timeChange (n / 2).toNNReal 𝓕
/-- 𝒬^θ, (3.19); 𝒵_n^{⊗2}(t; f); the bracket density of N_n^f, from (3.22) and (3.11). -/
def tiltedInclGen (θ : ℝ) (f : ℤ → ℤ → ℝ) (x₁ x₂ : ℤ) : ℝ := …   -- (E), transcribes (3.19)
def pairZ2 (n : ℝ) (ψ) (ω : Ω) (t : ℝ) (f : ℤ → ℤ → ℝ) : ℝ :=
  ∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω t x₁ * zN n ψ ω t x₂ * f x₁ x₂
def bracketDensN2 (n : ℝ) (ψ) (f : ℝ → ℤ → ℤ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  4 * n * ∑' x : ℤ, zN n ψ ω s x * zN n ψ ω s (x + 1) *
    (∑' x' : ℤ, zN n ψ ω s x' *
      (Real.exp (thetaN n / 2) * f s (x + 1) x' - Real.exp (-thetaN n / 2) * f s x x')) ^ 2
/-- ϱ_n(t), (3.8). -/
def varrhoN (n t : ℝ) : ℝ := Real.exp ((n * lambdaN n / 2 - n ^ (1 / 2 : ℝ) / 2 - 1 / 24) * t)
```

Statements (`TiltedField/Identities.lean`, no probability):

* `sinh_sub_le`: $0\le\sinh\theta-\theta\le\frac{\theta^3}6\cosh\theta$ for $\theta\ge0$ (Section 3.1).
* `rescaledMeasure_eq` (3.8): `rescaledMeasure ⊤ n P t = ENNReal.ofReal (varrhoN n t) • Measure.sum (fun x => ENNReal.ofReal (z x) • dirac (rescaledPosition n t x))` with $z$ the tilted field of $P$, for $P\ge0$ and $n\ge1$.
* `varrhoN_bounds` (3.9): $1\le\varrho_n(t)\le\exp(tn^{-1/2})$ for $n\ge1$, $t\ge0$.
* `identity_uv` (3.18), `tilt_identity` (3.20) with `inclGen`, `tiltedInclGen_diff` (3.23): $\mathcal Q^\theta f=\cosh\theta\ \mathcal Rg(x_2-x_1)$ when $f(x_1,x_2)=g(x_2-x_1)$ with $g$ even (`chainGen` of Stage 1).
* `prop_3_1_generator`, **Prop 3.1 (1)** (E): `IsC13 1 (fun _ => φ) 0 C → |AN n φ y - iteratedDeriv 2 φ y / 2| ≤ n ^ (-1/4 : ℝ) * C` for $n\ge1$.

Probabilistic statements:

```lean
/-- (3.7): 𝔼 sup_{t ≤ T} 𝒲_n(t)^k < ∞ (with a.s. summability of the series). -/
theorem WN_moments (hB) (hψ) {n T : ℝ} (hn : 1 ≤ n) (k : ℕ) : …

/-- **Proposition 3.1**, (3.14)-(3.15) and items (2), (3). (E) -/
theorem prop_3_1 (hB) (hψ) {n T C : ℝ} (hn : 1 ≤ n) (hT : 0 < T) {φ φt : ℝ → ℝ → ℝ}
    (hφ : IsC13 T φ φt C) :
    HasBracket T (filtN n 𝓕) (MN n ψ φ φt) (QN n ψ φ) μ ∧
    (∀ᵐ ω ∂μ, ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      QN n ψ φ t ω - QN n ψ φ s ω ≤ 2 * C ^ 2 * (aN n * ∫ r in s..t, EN n ψ ω r fun _ => 1)) ∧
    (∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      |QN n ψ φ t ω - aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s (φ s)| ≤
        5 * n ^ (-1 / 4 : ℝ) * C ^ 2 * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1)
    -- T0 adds: a.s. summability of the series in pairZ/EN and interval integrability on [0,T]

/-- (3.16): 𝒲_n is a continuous L² martingale with ⟨𝒲_n⟩_t = a_n ∫_0^t ℰ_n(s) ds, 𝒲_n(0) = 1. -/
theorem hasBracket_WN (hB) (hψ) {n T : ℝ} (hn : 1 ≤ n) :
    HasBracket T (filtN n 𝓕) (WN n ψ) (fun t ω => aN n * ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) μ ∧
    ∀ᵐ ω ∂μ, WN n ψ 0 ω = 1

/-- **Lemma 3.2**, (3.21)-(3.22). (E) -/
theorem lemma_3_2 (hB) (hψ) {n T C : ℝ} (hn : 1 ≤ n) {f f' : ℝ → ℤ → ℤ → ℝ}
    (hsymm : ∀ t x₁ x₂, f t x₁ x₂ = f t x₂ x₁)
    (hf : ∀ x₁ x₂, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (f · x₁ x₂) (f' t x₁ x₂) (Set.Icc 0 T) t)
    (hf' : ∀ x₁ x₂, ContinuousOn (f' · x₁ x₂) (Set.Icc 0 T))
    (hbd : ∀ t ∈ Set.Icc 0 T, ∀ x₁ x₂, |f t x₁ x₂| ≤ C ∧ |f' t x₁ x₂| ≤ C) :
    HasBracket T (filtN n 𝓕)
      (fun t ω => pairZ2 n ψ ω t (f t) - f 0 0 0 - ∫ s in (0 : ℝ)..t, pairZ2 n ψ ω s
        (fun x₁ x₂ => f' s x₁ x₂ + n / 2 * tiltedInclGen (thetaN n) (f s) x₁ x₂ +
          n * lambdaN n / 2 * (if |x₁ - x₂| = 1 then f s x₁ x₂ else 0)))
      (fun t ω => ∫ s in (0 : ℝ)..t, bracketDensN2 n ψ f s ω) μ
```

### 3.3 Section 4 (`SecondMoments/TotalMass.lean`)

```lean
/-- **Proposition 4.3 (1)**, (4.7), at a bounded stopping time of 𝓕ⁿ (augmented by the null
sets); `t` deterministic is the case of a constant stopping time. (E) -/
theorem prop_4_3_condSecondMoment (hB) (hψ) {n : ℝ} (hn : 1 ≤ n) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T) (s : ℝ) (hs : 0 ≤ s) :
    μ[fun ω => WN n ψ (τ ω + s) ω ^ 2 | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∑' x₁ : ℤ, ∑' x₂ : ℤ, zN n ψ ω (τ ω) x₁ * zN n ψ ω (τ ω) x₂ * uN n s (x₂ - x₁)

/-- **Proposition 4.3 (2)**, (4.8). (E) -/
theorem prop_4_3_bounds (hB) (hψ) {n t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) :
    ∫⁻ ω, ⨆ s ∈ Set.Icc 0 t, ENNReal.ofReal (WN n ψ s ω ^ 2) ∂μ ≤ ENNReal.ofReal (2 ^ (3 + 16 * t)) ∧
    Integrable (fun ω => ∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) μ ∧
    ∫ ω, (∫ s in (0 : ℝ)..t, EN n ψ ω s fun _ => 1) ∂μ ≤ 2 ^ (1 + 16 * t)
    -- T0 adds the AEMeasurable conjunct for the supremum

/-- **Proposition 4.3 (3)**, (4.9). (E) -/
theorem prop_4_3_increment (hB) (hψ) {n : ℝ} (hn : 1 ≤ n) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτb : ∃ T : ℝ≥0, ∀ ω, τ ω ≤ T) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 16) :
    μ[fun ω => aN n * ∫ r in (τ ω : ℝ)..(τ ω + s), EN n ψ ω r (fun _ => 1) | hτ.measurableSpace]
      ≤ᵐ[μ] fun ω => 4 * Real.sqrt s * WN n ψ (τ ω) ω ^ 2
```

### 3.4 Section 6 (`Replacement/`)

```lean
/-- ρ_ε(x) = ρ(x/ε)/ε. -/
def rhoEps (ρ : ℝ → ℝ) (ε x : ℝ) : ℝ := ρ (x / ε) / ε
/-- ‖(φ 𝒵_n(t)) * ρ_ε‖²₂. -/
def smoothedNormSq (n : ℝ) (ψ) (ρ : ℝ → ℝ) (ε : ℝ) (ω : Ω) (t : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ y, (∑' x : ℤ, zN n ψ ω t x * φ (rescaledPosition n t x) * rhoEps ρ ε (y - rescaledPosition n t x)) ^ 2
/-- 𝖥_n(t), (6.9), and 𝖡_n(t; φ), (6.10). (E) -/
def FN (n : ℝ) (ψ) (ρ : ℝ → ℝ) (m : ℕ) (φ : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  2 / (cN n * n ^ (1 / 2 : ℝ)) * pairZ2 n ψ ω t
    (fun x₁ x₂ => gM ρ m (x₂ - x₁) * φ t (rescaledPosition n t x₁) * φ t (rescaledPosition n t x₂))
def BN (n : ℝ) (ψ) (ρ : ℝ → ℝ) (m : ℕ) (t : ℝ) (φ : ℝ → ℝ) (ω : Ω) : ℝ :=
  n ^ (1 / 2 : ℝ) * pairZ2 n ψ ω t
    (fun x₁ x₂ => kM ρ m (x₂ - x₁) * φ (rescaledPosition n t x₁) * φ (rescaledPosition n t x₂))
```

* `smoothedNormSq_eq` (6.1) for these discrete measures, and `BN_eq` (6.11): $\mathsf B_n(t;\varphi)=b_m^{-1}\lVert(\varphi\mathsf Z_n(t))\ast \rho_{mn^{-1/2}}\rVert_2^2$ (with summability and integrability).
* `tendsto_bM` : $b_m\to1$ (used in the proof of Prop 6.2; not stated in the article as a result).

```lean
/-- **Lemma 6.4**, (6.12)-(6.15). The remainder R_n is given with its bound (6.14); in the article
it is the explicit expression (6.16), see decision D5. (E, without the measurability of R, q) -/
theorem lemma_6_4 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ K : ℝ, ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
      IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ →
      ∀ {n T C : ℝ} {m : ℕ} {φ φt : ℝ → ℝ → ℝ}, 1 ≤ n → 1 ≤ m → 0 < T → IsC13 T φ φt C →
      ∃ R q : ℝ → Ω → ℝ, Measurable (Function.uncurry R) ∧ Measurable (Function.uncurry q) ∧
        (∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
          |FN n ψ ρ m φ t ω| ≤ m / n ^ (1 / 2 : ℝ) * C ^ 2 * WN n ψ t ω ^ 2 ∧            -- (6.13)
          |R t ω| ≤ K * (m / n ^ (1 / 2 : ℝ) + 1 / n ^ (1 / 4 : ℝ) + 1 / m) * C ^ 2 *
            WN n ψ t ω ^ 2 ∧                                                          -- (6.14)
          0 ≤ q t ω ∧
          q t ω ≤ K * (m ^ 2 / n + 1 / n ^ (1 / 2 : ℝ)) * C ^ 4 * WN n ψ t ω ^ 2 *
            (aN n * EN n ψ ω t fun _ => 1)) ∧                                         -- (6.15)
        HasBracket T (filtN n 𝓕)                                                      -- (6.12)
          (fun t ω => FN n ψ ρ m φ t ω - FN n ψ ρ m φ 0 ω - ∫ s in (0 : ℝ)..t,
            (EN n ψ ω s (φ s) - BN n ψ ρ m s (φ s) ω + R s ω))
          (fun t ω => ∫ s in (0 : ℝ)..t, q s ω) μ ∧
        ((∀ t y, φ t y = 1) → (∀ t ω, R t ω = 0) ∧
          ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, 0 ≤ FN n ψ ρ m φ t ω)

/-- **Proposition 6.1**, (6.2). (E) -/
theorem prop_6_1 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
      IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ →
      ∀ {n T : ℝ} {m : ℕ}, 1 ≤ n → 1 ≤ m → 0 < T →
        ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (smoothedNormSq n ψ ρ (m * n ^ (-1 / 2 : ℝ)) ω t fun _ => 1)) ∂μ ≤
        ENNReal.ofReal (C * 2 ^ (16 * T))

/-- **Proposition 6.2**, (6.3), in the ε–δ form of `lim_{ε→0} limsup_{n→∞} ℙ(…) = 0`. (E) -/
theorem prop_6_2 (hB) (hψ) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {T C : ℝ} (hT : 0 < T)
    {φ φt : ℝ → ℝ → ℝ} (hφ : IsC13 T φ φt C) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀, ∃ N : ℝ, ∀ n ≥ N,
      μ {ω | ∃ t ∈ Set.Icc 0 T, η < |∫ s in (0 : ℝ)..t,
        (EN n ψ ω s (φ s) - smoothedNormSq n ψ ρ ε ω s (φ s))|} ≤ ENNReal.ofReal δ
```

### 3.5 Infrastructure statements (not for the author)

Section 2 lists them; also internal to D: the good unit-norm version $\hat\psi$ (`IsWaveFunction.exists_unit`), the local and global Itô relations of $\mathrm{Re}\ \hat\psi(x)$, $\mathrm{Im}\ \hat\psi(x)$ and $P(x)$, the stochastic-integral representations behind (2.4), (2.7), (2.8) (`stochInt` of explicit integrands; kept for Stage 4, which needs them for the fourth moment bound of Section 7.1), and the linear functional formula for bounded weights.

---

## 4. Task breakdown

Each task is for one agent in a fresh session, in its own git worktree, checked and merged by the main session (method of Stage 1). Sizes are lines of Lean to be written. "Uses" lists the statements the task may assume (possibly still `sorry` in `master`, if approved or frozen as interface). Rule for all tasks: no new `sorry` in the files of the task at the end; do not modify a statement of another file; report any statement that turns out false or unprovable as stated.

**Interface freezing.** To let tasks run in parallel, task I0 writes all infrastructure signatures of Section 2 with `sorry` proofs (interface files). A task may use an interface lemma of another package that is still `sorry`; the final check of Stage 2 requires them all proved. If an interface lemma must change, the main session changes it and tells the dependent tasks.

| Id | Files (under `QSSEPtoKPZ/`) | Content | Uses | Size | Can start |
|---|---|---|---|---|---|
| **T0** | `Martingales/Defs.lean`, `TiltedField/Defs.lean`, `Replacement/CorrectorDefs.lean`, `WaveFunction/Kernel.lean` (defs only), and all article statements of Section 3 with `sorry`, in their final files; `docs/stage2-statements.md` for the author | statements for approval | — | 700–1,000 | first |
| **I0** | interface files of B, C with `sorry` (Section 2 signatures) | frozen interfaces | T0 defs | 400–700 | with T0 |
| B1 | `Martingales/NullAug.lean` | nullAug lemmas; Brownian family and wave function transfer; versions; transfer of `IsCL2Mart`/`HasBracket` (filtration, indistinguishability, time change, restriction) | T0, I0 | 600–900 | after I0 |
| B2 | `Martingales/Doob.lean` | discrete $L^2$ Doob (layer cake); continuous-time maximal and $L^2$ inequalities | I0 | 600–1,000 | after I0 |
| B3 | `Martingales/Stopping.lean` | `hitTime` is a stopping time; dyadic discretization; `condExp_stopped_of_forall`; optional sampling; stopped brackets | B1 interface, B2 interface | 700–1,100 | after I0 |
| C1 | `ItoIntegral/Elementary.lean` | blocks, refinement, adaptedness, continuity, martingale, covariation, isometry | I0 | 900–1,400 | after I0 |
| C2 | `ItoIntegral/FourthMoment.lean` | fourth moment, elementary then limit | C1 | 400–700 | after C1 |
| C3 | `ItoIntegral/Basic.lean` | `IsItoIntegrable`, fast sequence, `stochInt`, $L^2$/uniform convergence, adaptedness, continuity, `HasBracket`, covariation, linearity | C1, B2 interface | 900–1,500 | after C1 |
| C4 | `ItoIntegral/Integrands.lean`, `ItoIntegral/Riemann.lean` | membership of the integrand shapes; Riemann sums | C3 interface | 700–1,100 | after I0 |
| C5 | `ItoIntegral/Stopping.lean` | stopping property; pulling out $\mathcal G_u$-measurable factors | C3, B3 interfaces | 500–800 | after I0 |
| C6 | `ItoIntegral/Product.lean` | `IsItoProcessUpTo`, product rule, corollaries | C2–C5 interfaces | 900–1,500 | after I0 |
| C7 | `ItoIntegral/Complex.lean` | `itoSum` against `complexBM`, conjugate | C4 interface | 300–500 | after I0 |
| D1 | `WaveFunction/Good.lean`, `WaveFunction/Identification.lean` | $\tilde\psi$; $\tau_R$; $\mathrm{Re}$, $\mathrm{Im}\ \tilde\psi(x)$ Itô processes up to $\tau_R\wedge N$ | B1, B3, C4, C5, C7 interfaces | 700–1,100 | after I0 |
| D2 | `WaveFunction/LocalP.lean`, `WaveFunction/Mass.lean` | $P(x)$ stopped Itô process; boxes; **mass conservation** (`hasSum_density`); unit-norm version $\hat\psi$; global Itô relations of $P(x)$ | D1, C6 | 800–1,300 | after D1 |
| D3 | `WaveFunction/EquationP.lean`, `WaveFunction/Kernel.lean` | **Prop 2.2** (with $\mathbb EP=p_t$) | D2 | 600–900 | after D2 |
| D4 | `WaveFunction/BoundedWeights.lean`, `WaveFunction/MomentBound.lean` | linear functionals with bounded weights; **(2.2)** | D2, C6, B2 | 800–1,200 | after D2 |
| D5 | `WaveFunction/Linear.lean` | **Lemma 2.3 (1)** | D4 | 600–1,000 | after D4 |
| D6 | `WaveFunction/Quadratic.lean` | **Lemma 2.3 (2)** | D4, D5 | 900–1,500 | after D4 |
| E1 | `TiltedField/Identities.lean` | sinh inequality, (3.8), (3.9), (3.18), (3.20), (3.23), **Prop 3.1 (1)** | T0 approved | 500–900 | after approval |
| E2 | `TiltedField/Martingales.lean` | (3.7), **Prop 3.1**, (3.16) | Lemma 2.3 (1) and (2.2) statements, E1, B1 | 700–1,200 | after approval |
| E3 | `TiltedField/Quadratic.lean` | **Lemma 3.2** | Lemma 2.3 (2) statement, E1 | 500–900 | after approval |
| F1 | `SecondMoments/TotalMass.lean` | **Prop 4.3** | Lemma 3.2, Prop 3.1 statements, Stage 1, B2, B3 | 500–900 | after approval |
| G1 | `Replacement/Corrector.lean` (+ `Replacement/CorrectorBounds.lean`) | **Lemma 6.4**: identity with $R_n$ from (6.16), (6.13), $\phi\equiv1$ case; then (6.14), (6.15) | Lemma 3.2 statement, E1, Lemma 6.3 | 1,200–2,000 (split in two tasks G1a/G1b if over 1,200) | after approval |
| G2 | `Replacement/L2Bound.lean` | (6.1), (6.11), **Prop 6.1** | Lemma 6.4, Prop 4.3 statements | 400–700 | after approval |
| G3 | `Replacement/ReplacementLemma.lean` | $b_m\to1$, continuity of $\kappa_\varepsilon$ in $\varepsilon$, **Prop 6.2** | Lemma 6.4 statement, B2, B3, B1 (good version of $\mathcal W_n$) | 600–1,000 | after approval |

Dependencies and parallelism:

```
T0 ──► author's approval ──► E1 ──► E2, E3 ──► F1 ──► G1 ──► G2, G3
 │                              (E, F, G use the approved D statements, still sorry)
 └► I0 ──► B1, B2, C1, C4, C5, C7 (parallel) ──► B3, C2, C3 ──► C6 ──► D1 ──► D2 ──► D3, D4 ──► D5, D6
```

* Wave 1 (as soon as T0 and I0 are written): B1, B2, C1 in parallel; T0 goes to the author.
* Wave 2: B3, C2, C3, C4, C5, C7. After approval: E1, then E2, E3 in parallel.
* Wave 3: C6, D1; F1, G1.
* Wave 4: D2; G2, G3. Wave 5: D3, D4. Wave 6: D5, D6.
* The article side (E, F, G) and the stochastic side (B, C, D) are independent once the statements are frozen: with two agents at a time, one on each side, the critical path is the chain I0 → C1 → C3 → C6 → D1 → D2 → D4 → D6 (8 tasks).
* Interface tasks that only use interfaces (C4, C5, C6, D1) can start before their inputs are proved; this is where the parallelism comes from, and where the risk of a wrong interface lies (Section 5, R3).

---

## 5. Risks and decisions for the author

**Decisions (my recommendation in bold).**

* **D1. Martingales "up to null sets", in the filtration of the article.** The statements say "continuous square-integrable martingale with bracket $A$" through `IsCL2Mart` and `HasBracket` of Section 2.1, with respect to $\mathcal F_t$ (resp. $\mathcal F_{nt/2}$), without usual conditions. Alternative: state with respect to the augmented filtration, or with Mathlib's `Martingale` for a chosen version. **Recommended: as proposed** (it is what the article's sentences mean, and it is robust to versions).
* **D2. Brackets are explicit processes.** "$\langle M\rangle=A$" means $M^2-A$ is a martingale with $A$ continuous nondecreasing; no general quadratic variation. **Recommended.**
* **D3. Stochastic integrals do not appear in the article statements.** $J(x)$ in Prop 2.2 is characterized by its Riemann sums (the convention of the frozen statement); the last terms of (2.7), (2.8), (3.21), (6.12) are characterized as martingales with explicit brackets. The representations (3.10), (3.11), (3.17) and the integrals of (2.7), (2.8), (3.22) are internal lemmas, not submitted. Alternative: expose the project's `stochInt` in the statements (more literal, but the author would have to check the construction of the integral). **Recommended: as proposed.**
* **D4. Stopping times in Prop 4.3** are those of the time-changed filtration augmented by the null sets (more stopping times than for $\mathcal F_{nt/2}$, fewer than under the usual conditions; Section 5 needs only what is proved here). **Recommended.**
* **D5. Lemma 6.4: $R_n$ given by "there exists" with its bound** (and measurability), instead of the explicit formula (6.16). The proof uses (6.16); the statement as in the article ("where … satisfies") does not name it. Alternative: define $\Gamma^\theta$ and $R_n$ explicitly in `CorrectorDefs.lean` and state $R_n=$ (6.16). **Recommended: "there exists"**, which is the content used in Prop 6.1, 6.2 and is simpler to compare with the article.
* **D6. $\lVert\phi\rVert_{1,3}$ through a bound $C$**, $C_b^{1,3}$ with an explicit time derivative `φt` and one-sided derivatives at $0$ and $T$ (`IsC13`). **Recommended.**
* **D7. Scope $L=\infty$.** Proposition 2.2 is stated in the article for all $L$; Section 8 does not use the finite-$L$ case (it uses $\mathbb EP^\infty(u,x)=p_u(x)$ and the equations of $\psi$ directly). **Recommended: $L=\infty$ only in Stage 2**; the finite case, if needed, in Stage 5 (same proof, with boundary sites).
* **D8. Prop 6.2 in ε–δ form**, equivalent to $\lim_{\varepsilon\to0}\limsup_{n\to\infty}=0$; Prop 6.1 and Lemma 6.4 with "∃ C depending only on ρ" quantified before the probability space. **Recommended.**

**Places where the Lean proof departs from the article** (statements unchanged; to be recorded in `PROGRESS.md`):

1. Mass conservation is proved first, by localization, from the equation of $\psi$ alone; (2.2) is then proved by truncated weights and a supermartingale argument, not by Da Prato–Zabczyk. Existence and uniqueness (the rest of Prop 2.1) are not proved in Stage 2.
2. No general Itô formula: product rule only; the Itô integral is built against the countable family $B$, so series of stochastic integrals are single integrals.
3. Usual conditions replaced by the null augmentation and versions (1.2 (a)).
4. (3.10), (3.11), (3.17) not used; Prop 3.1 read off Lemma 2.3 (1) after a change of time.
5. $b_m\to1$ is proved (the article states it; Stage 1 avoided it).

**Risks.**

* **R1 (size of package C).** The Itô integral is the largest new construction. The design avoids the density theorem for progressive integrands and the general Itô formula; the product rule still needs the fourth moment bound and the stopping lemmas. If C6 stalls, fallback: prove the product rule only for the specific processes ($\mathrm{Re}$, $\mathrm{Im}\ \psi(x)$, $P(x)$, deterministic weights), whose coefficients are bounded by $1$ after mass conservation.
* **R2 (measurability on null sets).** Processes built from the original $\psi$ may be non-measurable on a null set (e.g. $\int_0^t\psi_s(x)ds$ when the path is not measurable). The a.e. definitions D1 make the statements insensitive to this; internally everything is built from $\hat\psi$, which is continuous everywhere, and transferred by indistinguishability. Every task touching $\psi$ must follow this rule.
* **R3 (frozen interfaces).** Parallel tasks rely on `sorry` interfaces; an interface that is false as stated (a missing hypothesis) costs a re-run of its dependents. Mitigation: I0 is reviewed by the main session against this document before Wave 1; interface changes only add hypotheses that hold in all uses.
* **R4 (Lean conventions).** `tsum` of non-summable families is $0$, interval integrals of non-integrable functions are $0$, `lintegral` is the lower integral. Every article statement includes the needed summability/integrability/measurability (Section 3, rule (i)); T0 must add the conjuncts marked "T0 adds".
* **R5 (Lemma 6.4).** Long estimates with many constants (the Stage 1 experience: the article's constants are sometimes not the sharpest, which is harmless; a constant that is too small would be a finding for the article, rule 6 of CLAUDE.md).
* **R6 (time).** Section 7 (Stage 4) will need more from C: Lévy's characterization, BDG-type bounds. The design keeps C general (countable family, stopped Itô processes, fourth moments) so that it can be reused.

---

## 6. Size estimate

| Package | `PLAN.md`, Section 4 (k lines) | This design (k lines) | Tasks |
|---|---|---|---|
| B | 4–6 | 1.9–3.0 | B1, B2, B3 (+ part of T0, I0) |
| C | 8–12 | 4.6–7.5 | C1–C7 (+ part of I0) |
| D | 8–12 | 4.4–7.0 | D1–D6 |
| E | 6–9 (incl. Constants, done) | 1.7–3.0 | E1–E3 |
| F (rest: Prop 4.3) | part of 4–6 | 0.5–0.9 | F1 |
| G | 8–11 (incl. Lemma 6.3, done) | 2.2–3.7 | G1–G3 |
| statements, interfaces | — | 1.1–1.7 | T0, I0 |
| **Total Stage 2** | **about 30–45** (B, C, D, E, G, rest of F) | **about 16–27** | 25 tasks |

The design's figures are lower than the plan's because (i) Stage 1 measured that agents wrote about a third of the plan's estimate for the pilot, and (ii) the design removes general machinery (progressive density, general Itô formula, separate theory of series of stochastic integrals). They are less certain than Stage 1's: packages B and C are the first stochastic code of the project. At Stage 1's pace (300–550 lines per agent-hour) this is 35 to 80 agent-hours; with two agents in parallel, 20 to 45 hours of wall time, if no step of the article fails.

---

## 7. What was checked

* Scratch files (not in the repository): `<scratch>/design/Infra.lean` (package B and C signatures, including the full definitions of `nullAug`, `timeChange`, `IsCL2Mart`, `HasBracket`, `ElemBlock`, `ElemIntegrand`, `energy`, `IsItoIntegrable`, `stochInt`, `hitTime`, `IsItoProcessUpTo` and the statement of the product rule) and `Article2.lean` (all signatures marked (E) in Section 3). Both compile with `lake env lean` against the project (Lean 4.35.0, Mathlib v4.35.0), with only `declaration uses 'sorry'` warnings. Proofs are not written; definitions other than those listed are not checked.
* `Names.lean`, `Names2.lean` in the same folder: every Mathlib name of Section 2.3 resolves with `#check`.
* Not checked: that each interface statement is true as written (they are standard, but hypotheses may need adjusting when proved); the line estimates.
