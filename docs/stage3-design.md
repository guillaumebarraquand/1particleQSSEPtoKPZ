# Stage 3: design (package H, tightness)

Written on 13 November 2026 by a design agent (Opus 5.5), at the request of the main session. **Nothing in this document is proved.** It fixes the Lean statements, the generic infrastructure and the order of work for Stage 3 (Section 5 of the article: Lemma 5.2, equation (5.2), Proposition 5.1). The Lean signatures of Sections 2 and 3 were checked to elaborate against Mathlib v4.35.0 (with `sorry` proofs) in two scratch files outside the repository (Section 7); they are a starting point for the tasks T0' and I0', not frozen text.

Equation numbers are those of the article (version of 11 November 2026, SHA-256 `3547cb86…`, unchanged on 13 November 2026), read from its `.aux` file: Proposition 5.1 (tightness), Lemma 5.2 with (5.1) (compact containment), (5.2) (Aldous' condition), (3.8) ($\mathcal Z_n=\varrho_n\mathsf Z_n$), (4.8), (4.9) (Proposition 4.3).

Readers: Section 1 is for the author. Sections 2 to 4 are for the agents who will write the Lean code. Section 5 lists the decisions for the author.

---

## 1. Mathematical overview

### 1.1 What Stage 3 proves

The checkpoint of `PLAN.md` is Proposition 5.1: for every $T>0$, the processes $(\mathsf Z_n(t))_{t\in[0,T]}$ have continuous trajectories in $\mathcal M_+(\mathbb R)$ and their laws, $n\ge1$, are tight in $C([0,T],\mathcal M_+)$.

The article states Proposition 5.1 for the **tilted measures** $\mathsf Z_n(t)=\sum_x\mathfrak z_n(t,x)\delta_{y_n(t,x)}$ of (3.5) (`tiltedMeasure`, approved in Stage 2), not for the measures $\mathcal Z_n(t)$ of Theorem 1.2. They are related by (3.8), $\mathcal Z_n(t)=\varrho_n(t)\mathsf Z_n(t)$ with $1\le\varrho_n(t)\le e^{tn^{-1/2}}$ deterministic (`rescaledMeasure_eq`, `varrhoN_bounds`, proved in Stage 2). Stage 3 follows the article: everything is stated for $\mathsf Z_n$. The passage to $\mathcal Z_n$ is the last line of Section 7 and belongs to Stages 4–5.

| Article | Content | In Lean |
|---|---|---|
| notation $\mu(\varphi)=\int\varphi d\mu$ | $\mathsf Z_n(t;\varphi)=\int\varphi\ d\mathsf Z_n(t)$ | `integral_tiltedMeasure` (link between `tiltedMeasure` and `pairZ`, item W2 of the Stage 2 audit) |
| Lemma 5.2, (5.1) | $\mathbb E[\mathsf Z_n(t;e_b)]\le e^{2t}$ for $\lvert b\rvert\le1$; $\mathbb P(\sup_{t\le T}\mathsf Z_n(t;\cosh)\ge K)\le2e^{2T}/K$ | `lemma_5_2` |
| (5.2) | Aldous' condition for $\mathsf Z_n(\cdot;\varphi)$, with the quantitative bound of the proof | `aldous_condition` |
| Prop 5.1, first sentence | continuous trajectories in $\mathcal M_+$ | `prop_5_1_continuous`, `prop_5_1_version` |
| Prop 5.1, second sentence | tightness in $C([0,T],\mathcal M_+)$ | `prop_5_1` (uniform compact sets), `prop_5_1_isTight` (Mathlib's `IsTightMeasureSet`) |

Section 7 uses Proposition 5.1 (extraction of convergent subsequences) and Section 8 uses (5.1) (the mass of $\mathsf Z_n$ outside $[-\ell_n,\ell_n]$). Both uses are covered by the statements above.

### 1.2 How the Lean proof goes, and where it departs from the article

**(a) No Skorokhod space; a criterion stated directly in $C([0,T],\mathcal M_+)$** (route of `PLAN.md`). The article applies Jakubowski's criterion in $D([0,T],\mathcal M_+)$ and then notes that the processes are continuous. Mathlib has no Skorokhod space. Since the paths are continuous, the same two conditions give tightness directly in $C([0,T],\mathcal M_+)$:

* (i) *compact containment*: for every $\eta>0$ a compact $\mathcal K_\eta\subset\mathcal M_+$ with $\mathbb P(\mathsf Z_n(t)\in\mathcal K_\eta\ \forall t\le T)\ge1-\eta$ for all $n$;
* (ii) tightness in $C([0,T],\mathbb R)$ of $t\mapsto\mathsf Z_n(t;f_j)$ for each $f_j$ of a **countable** family $(f_j)$.

The family is $f_0=1$ and the functions $x\mapsto\beta(mx-k)$, $m\ge1$, $k\in\mathbb Z$, where $\beta(x)=s(x+1)-s(x)$ and $s$ is a smooth nondecreasing function equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$ (Mathlib's `Real.smoothTransition`). So $\beta$ is smooth, $0\le\beta\le1$, $\beta=0$ outside $[-1,1]$, and $\sum_{k\in\mathbb Z}\beta(x-k)=1$ (telescoping). These $f_j$ belong to $C_b^3$, so Proposition 3.1 applies to them, as to the $\varphi\in C_c^\infty$ of the article. The family is used through one analytic fact:

> **(F)** If $\mu_i(f_j)\to\mu(f_j)$ for every $j$ (along any filter), then $\mu_i\to\mu$ weakly.

Proof: $j=0$ gives convergence of the masses. Every compactly supported continuous $g$ is the uniform limit of $g_m(x)=\sum_kg(k/m)\beta(mx-k)$, with $\lVert g-g_m\rVert_\infty\le\sup_{\lvert x-y\rvert\le1/m}\lvert g(x)-g(y)\rvert$ (because $\beta\ge0$, $\sum_k\beta(mx-k)=1$ and $\beta(mx-k)=0$ unless $\lvert x-k/m\rvert<1/m$), and $g_m$ is a finite combination of the $f_j$; the masses being bounded, $\mu_i(g)\to\mu(g)$. For $f$ bounded continuous, write $f=f\chi_N+f(1-\chi_N)$ with $\chi_N=\sum_{\lvert k\rvert\le N}\beta(\cdot-k)$, which equals $1$ on $[-N+1,N-1]$, is compactly supported and is itself a combination of the $f_j$; then $\lvert\mu_i(f(1-\chi_N))\rvert\le\lVert f\rVert_\infty(\mu_i(1)-\mu_i(\chi_N))\to\lVert f\rVert_\infty(\mu(1)-\mu(\chi_N))$, which is small for $N$ large.

(F) says that $\mu\mapsto(\mu(f_j))_{j\ge0}$ is a homeomorphism of $\mathcal M_+(\mathbb R)$ onto its image in $\mathbb R^{\mathbb N}$. Three consequences, all needed and none in Mathlib: **$\mathcal M_+(\mathbb R)$ is metrizable and separable**; its Borel $\sigma$-algebra is generated by the maps $\mu\mapsto\mu(f_j)$; and (Section 2.4) a set of paths taking values in a fixed compact set of $\mathcal M_+$ and such that each $t\mapsto\gamma(t)(f_j)$ stays in a fixed compact set of $C([0,T],\mathbb R)$ is compact in $C([0,T],\mathcal M_+)$. With this last fact, the criterion (i)+(ii) is proved by a union bound over $j$, without Jakubowski's condition "separates points and is closed under addition".

The article says that $\mathcal M_+$ is Polish. Stage 3 proves metrizability and separability but not completeness; see decision D8' (Section 5).

**(b) Compact sets of $\mathcal M_+$** (article, proof of Prop 5.1, condition (i)). $\mathcal K=\lbrace\mu:\mu(\cosh)\le K\rbrace$ is compact: it is closed ($\mu\mapsto\mu(\cosh)$ is a supremum of continuous functions $\mu\mapsto\mu(\min(\cosh,N))$, hence lower semicontinuous), its elements have mass at most $K$ and give mass at most $K/\cosh\ell$ to $\mathbb R\setminus[-\ell,\ell]$; Mathlib's form of Prokhorov's theorem (`isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le`) gives compactness. As in the article.

**(c) Lemma 5.2** as in the article: Lemma 2.3 (1) (proved in Stage 2) with $\alpha_s(x)=e^{\theta'x-2(\cosh\theta'-1)s}$, $\theta'=\theta_n+bn^{-1/2}$, for which $\partial_s\alpha+\Delta\alpha=0$, gives a nonnegative continuous martingale equal to $1$ at time $0$; after the time change $s=nt/2$, $\mathsf Z_n(t;e_b)=e^{\kappa t}$ times this martingale, with $\lvert\kappa\rvert\le2$; Doob's maximal inequality (Stage 2, `IsCL2Mart.measure_exists_ge_le`) and $\cosh=(e_1+e_{-1})/2$ conclude. The inequality $\lvert\kappa\rvert\le2$ was checked numerically on a grid of $n\in[1,10^8]$, $b\in[-1,1]$ (maximum $1.22$); the Lean proof follows the article's bounds.

**(d) Aldous' condition (5.2)** as in the article: $\mathsf Z_n(\tau+s;\varphi)-\mathsf Z_n(\tau;\varphi)=\int_\tau^{\tau+s}\mathsf Z_n(u;\mathcal A_n\varphi)du+M_n^\varphi(\tau+s)-M_n^\varphi(\tau)$; the first term is at most $2Cs\sup_{u\le T+1}\mathsf W_n(u)$, with $\mathbb E\sup\mathsf W_n^2$ bounded by (4.8); for the second, optional sampling, Prop 3.1 (2) and (4.9) give $\mathbb E[(M_n^\varphi(\tau+s)-M_n^\varphi(\tau))^2]\le8C^2\sqrt s\ \mathbb E[\mathsf W_n(\tau)^2]$; Markov's inequality. The Lean statement keeps the bound $c_T\big(Cs/\eta+C^2\sqrt s/\eta^2\big)$ instead of only the limit (5.2), because the tightness proof needs it in quantitative form. The stopping times are those of $\mathcal F^n$ augmented by the null sets (decision D4 of Stage 2, already used in Prop 4.3).

**(e) Aldous' criterion for processes with continuous paths** (the article cites Aldous 1978 and Billingsley, Theorem 16.10, for càdlàg processes). Lean proves only what is needed, for continuous paths, in two steps.

* *Aldous' trick.* If $\mathbb P(\lvert X_{\rho+s}-X_\rho\rvert\ge\eta)\le a$ for every stopping time $\rho$ and every deterministic $s\le2\delta$, then $\mathbb P(\lvert X_\sigma-X_\tau\rvert\ge2\eta)\le3a$ for stopping times $\tau\le\sigma\le\tau+\delta$. Proof: for $s\in[\delta,2\delta]$, $\lvert X_\sigma-X_\tau\rvert\le\lvert X_{\tau+s}-X_\tau\rvert+\lvert X_{\sigma+u}-X_\sigma\rvert$ with $u=\tau+s-\sigma\in[0,2\delta]$; average over $s\in[\delta,2\delta]$ and use Fubini.
* *From the trick to the modulus of continuity.* Let $\tau_0=0$ and $\tau_{k+1}=\inf\lbrace t\ge\tau_k:\lvert X_t-X_{\tau_k}\rvert\ge\eta\rbrace\wedge T$. Pathwise: if $\lvert X_t-X_s\rvert\ge3\eta$ with $\lvert t-s\rvert\le\delta$, then either $\tau_N<T$, or some $k<N$ has a genuine hit $\lvert X_{\tau_{k+1}}-X_{\tau_k}\rvert\ge\eta$ with $\tau_{k+1}-\tau_k\le\delta$; and if $\tau_N<T$, at least $N-T/\delta_1$ of the $N$ first increments $\tau_{k+1}-\tau_k$ are genuine hits of length at most $\delta_1$. Each such event is contained in $\lbrace\lvert X_{\sigma_k}-X_{\tau_k}\rvert\ge\eta\rbrace$ with $\sigma_k=\tau_{k+1}\wedge(\tau_k+\delta)$, whose probability is bounded by the trick. Choosing first $\delta_1$, then $N=\lceil2T/\delta_1\rceil$, then $\delta\le\delta_1$:
$$\mathbb P\Big(\sup_{s,t\le T,\ \lvert t-s\rvert\le\delta}\lvert X_t-X_s\rvert\ge3\eta\Big)\le6a(\delta_1)+3N\ a(\delta),$$
where $a(\delta)$ bounds $\mathbb P(\lvert X_{\rho+s}-X_\rho\rvert\ge\eta/2)$ for $s\le2\delta$. This two-scale argument uses only the unconditional bound (5.2), as Aldous' criterion does. Together with a bound on $\sup_t\lvert X_t\rvert$ and the Arzelà–Ascoli theorem (in Mathlib), it gives tightness in $C([0,T],\mathbb R)$. For $X_t=\mathsf Z_n(t;f_j)$ the bound on the supremum is $\lvert\mathsf Z_n(t;f_j)\rvert\le\mathsf W_n(t)$ and (4.8), as in the article.

**(f) Versions and measurability.** The frozen statement asks for random variables $\Omega\to C([0,T],\mathcal M_+)$, measurable for the Borel $\sigma$-algebra of the topology of uniform convergence, which coincide almost surely with $t\mapsto\mathcal Z_n(t)$ for all $t$ at once. Stage 3 constructs such a version of $\mathsf Z_n$: on a measurable set of probability one on which $\sum_x\mathfrak z_n(t,x)$ converges and is dominated uniformly in $t\le T$ (Stage 2), the path $t\mapsto\mathsf Z_n(t)$ is continuous (the article's argument: uniformly convergent sum of continuous functions), and it is set to $0$ elsewhere. Measurability follows from (a): the Borel $\sigma$-algebra of $C([0,T],\mathcal M_+)$ is generated by the evaluations at times $t$ (Mathlib, for a second countable target), and that of $\mathcal M_+$ by the maps $\mu\mapsto\mu(f_j)$. The statements are made for *every* version, so they do not depend on the choice.

**(g) What "tight" means in the statements.** The probability spaces vary with the realization. The Lean statement is therefore the uniform one: for every $\varepsilon>0$ there is a compact $\mathcal K\subset C([0,T],\mathcal M_+)$ such that, for every probability space, every Brownian family, every wave function, every $n\ge1$ and every version $\mathsf Z_n$ of the process, $\mathbb P(\mathsf Z_n\notin\mathcal K)\le\varepsilon$. For a sequence of realizations (the setting of Theorem 1.2) this is Mathlib's `IsTightMeasureSet` of the family of laws (`prop_5_1_isTight`). Mathlib's Prokhorov theorem (`isCompact_closure_of_isTightMeasureSet`) then gives relative compactness of the laws, and, thanks to the metrizability proved here, the space of laws on $C([0,T],\mathcal M_+)$ is metrizable (Mathlib), so that Section 7 can extract convergent subsequences.

---

## 2. Infrastructure (generic, not about QSSEP)

Conventions as in Stage 2 (D1–D8, `docs/stage2-design.md` Section 2): `module`, `public import`, `@[expose] public section`, `noncomputable section`, `namespace QSSEPtoKPZ`; processes `X : ℝ → Ω → ℝ`; stopping times `τ : Ω → ℝ≥0` coerced to `WithTop ℝ≥0`; suprema and probabilities of events in `ℝ≥0∞`, with outer measure when measurability is not claimed. New folder: `QSSEPtoKPZ/Tightness/`.

### 2.1 What Mathlib v4.35.0 has, and what it lacks (checked)

* `FiniteMeasure ℝ` has the topology of weak convergence (`FiniteMeasure.instTopologicalSpace`, induced by `toWeakDualBCNN`), is T2 (`FiniteMeasure.t2Space`), and $\mu\mapsto\int f d\mu$ is continuous for bounded continuous $f$ (`FiniteMeasure.continuous_integral_boundedContinuousFunction`); `FiniteMeasure.tendsto_iff_forall_integral_tendsto`, `FiniteMeasure.ext_of_forall_integral_eq`, `FiniteMeasure.continuous_iff_forall_continuous_integral`.
* **Its `MeasurableSpace` instance is the Giry $\sigma$-algebra** (generated by $\mu\mapsto\mu(A)$), and Mathlib does **not** prove that it equals the Borel $\sigma$-algebra. Do not use the instance on `FiniteMeasure ℝ`; use `borel (FiniteMeasure ℝ)` explicitly (see `measurable_pathFiniteMeasure_iff` below). In particular `ContinuousMap.measurable_iff_eval` (which needs `[BorelSpace Y]`) is not usable with `Y = FiniteMeasure ℝ`; use `ContinuousMap.borel_eq_iSup_comap_eval` instead.
* **Missing:** metrizability, second countability, separability of `FiniteMeasure ℝ`. Mathlib has them only for `ProbabilityMeasure X` (Lévy–Prokhorov: `instMetrizableSpaceProbabilityMeasure`, `LevyProkhorov.eq_convergenceInDistribution`), and no separability of `ProbabilityMeasure X`. Provided by Section 2.3.
* `C(X, Y)` has the compact-open topology and `ContinuousMap.measurableSpace := borel _` with `BorelSpace` (file `MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean`); `ContinuousMap.borel_eq_iSup_comap_eval` needs `[SecondCountableTopology X] [SecondCountableTopology Y] [LocallyCompactSpace X] [RegularSpace Y]`. `C(X, Y)` is second countable (`ContinuousMap.instSecondCountableTopology`) and metrizable (`Topology/Metrizable/ContinuousMap.lean`, for `X` σ-compact and weakly locally compact) when `Y` is. With the instances of Section 2.3, `MetrizableSpace`, `SecondCountableTopology`, `SeparableSpace` of `C(Set.Icc 0 T, FiniteMeasure ℝ)` and `MetrizableSpace (ProbabilityMeasure C(Set.Icc 0 T, FiniteMeasure ℝ))` are found by instance search (checked; the last one needs `public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`, which `Prokhorov.lean` imports privately).
* Prokhorov: `isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le` (compact sets of finite measures; needs `NormalSpace E ∨ Monotone K`), `isCompact_closure_of_isTightMeasureSet` (only `T2Space`, `BorelSpace`), `isTightMeasureSet_of_isCompact_closure` (needs a complete second countable metric space; not needed in Stage 3).
* Tightness: `IsTightMeasureSet` (`MeasureTheory/Measure/Tight.lean`), `isTightMeasureSet_iff_exists_isCompact_measure_compl_le`.
* Arzelà–Ascoli: `BoundedContinuousFunction.arzela_ascoli`, `ArzelaAscoli.isCompact_of_equicontinuous`; `ContinuousMap.isometryEquivBoundedOfCompact`. Compact-open convergence: `ContinuousMap.tendsto_compactOpen_iff_forall`, `ContinuousMap.tendsto_iff_tendstoLocallyUniformly`; post-composition: `ContinuousMap.continuous_postcomp`, `ContinuousMap.isInducing_postcomp`, `ContinuousMap.isEmbedding_postcomp`. `ContinuousMap.piEquiv : (∀ i, C(A, X i)) ≃ C(A, ∀ i, X i)` is only an `Equiv`: its continuity in both directions (for compact `A`) must be proved (a lemma on `TendstoUniformlyOn` with a `Pi` target; no ready-made name was found).
* `Real.smoothTransition` with `.contDiff`, `.monotone`, `.zero_of_nonpos`, `.one_of_one_le`, `.nonneg`, `.le_one`.
* Embeddings: `Topology.IsInducing.secondCountableTopology`, `Topology.IsEmbedding.metrizableSpace`, `borel_comap`; `Pi.borelSpace` (countable products).
* Measurability: `measurable_uncurry_of_continuous_of_measurable` (Carathéodory), `measurable_of_tendsto_metrizable`, `StronglyAdapted.isStronglyProgressive_of_continuous` (the old name `progMeasurable_of_continuous` is deprecated).
* From Stage 2: `hitTime`, `isStoppingTime_hitTime` (all paths continuous, adapted), `lt_of_lt_hitTime`, `le_of_le_hitTime`, `hitTime_eq_of_forall_lt`, `aestronglyMeasurable_stoppedAt` (`Martingales/StoppingAux.lean`), `IsCL2Mart.condExp_stopped`, `HasBracket.stopped`, `condExp_stopped_of_forall`, `IsCL2Mart.measure_exists_ge_le` (Doob's maximal inequality), `HasBracket.timeChange`, `stronglyMeasurable_nullAug_of_ae`, `measurableSet_nullAug_iff`; `TiltGood`, `ae_tiltGood`, `TiltGood.summable`, `TiltGood.continuousOn_WN`, `tiltZ_measurable`, `tiltZ_nonneg` (`TiltedField/MartingalesBounds.lean`).

### 2.2 H1: the test functions (`Tightness/TestFunctions.lean`)

```lean
/-- `β(x) = s(x+1) - s(x)`, `s = Real.smoothTransition`. -/
def tightBump (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

/-- `f₀ = 1`, `f_{j+1}(x) = β((m+1) x - k)` with `(m, k)` the `j`-th element of `ℕ × ℤ`. -/
def tightTestRaw (j : ℕ) (x : ℝ) : ℝ :=
  match j with
  | 0 => 1
  | j + 1 => tightBump (((Denumerable.ofNat (ℕ × ℤ) j).1 + 1 : ℝ) * x -
      (Denumerable.ofNat (ℕ × ℤ) j).2)

def tightTest (j : ℕ) : ℝ →ᵇ ℝ :=      -- `BoundedContinuousFunction.mkOfBound _ 2 _`
theorem isC13_tightTest (j : ℕ) : ∃ C, IsC13 1 (fun _ => tightTestRaw j) (fun _ _ => 0) C
```
plus: `tightBump` is smooth, `0 ≤ β ≤ 1`, `β x = 0` for `|x| ≥ 1`, `∑' k : ℤ, β (x - k) = 1` (finitely many nonzero terms), and the bounds on its first three derivatives (continuous with compact support, hence bounded). `Denumerable.ofNat` is in `Mathlib.Basic.Denumerable`.

### 2.3 H2: $\mathcal M_+(\mathbb R)$ is metrizable and separable (`Tightness/FiniteMeasureEmbed.lean`)

All elaborated:
```lean
/-- `μ ↦ (∫ f_j dμ)_j`. -/
def measEmbed (μ : FiniteMeasure ℝ) : ℕ → ℝ := fun j => ∫ x, tightTest j x ∂(μ : Measure ℝ)

/-- (F): the family `(f_j)` determines weak convergence. -/
theorem FiniteMeasure.tendsto_of_forall_tightTest {ι : Type*} {L : Filter ι}
    {μs : ι → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (h : ∀ j, Tendsto (fun i => ∫ x, tightTest j x ∂(μs i : Measure ℝ)) L
      (𝓝 (∫ x, tightTest j x ∂(μ : Measure ℝ)))) :
    Tendsto μs L (𝓝 μ)

theorem isEmbedding_measEmbed : IsEmbedding measEmbed
instance : SecondCountableTopology (FiniteMeasure ℝ) :=
  isEmbedding_measEmbed.isInducing.secondCountableTopology
instance : TopologicalSpace.MetrizableSpace (FiniteMeasure ℝ) :=
  isEmbedding_measEmbed.metrizableSpace

theorem borel_finiteMeasure_eq :
    borel (FiniteMeasure ℝ) =
      ⨆ j, (borel ℝ).comap fun μ : FiniteMeasure ℝ => ∫ x, tightTest j x ∂(μ : Measure ℝ)

/-- Measurability of a random path in `C([0,T], ℳ₊)` (Borel σ-algebra of the compact-open
topology, the instance used by the frozen statement). -/
theorem measurable_pathFiniteMeasure_iff {Z : Type*} [MeasurableSpace Z] {T : ℝ}
    {g : Z → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)} :
    Measurable g ↔ ∀ (t : Set.Icc (0 : ℝ) T) (j : ℕ),
      Measurable fun z => ∫ x, tightTest j x ∂(g z t : Measure ℝ)
```
Proof of (F) in 1.2 (a); work with an arbitrary filter (first countability is not yet known). Injectivity of `measEmbed` is (F) along the constant filter (`pure`) plus `T2Space`. `IsInducing` from (F) with `L = comap measEmbed (𝓝 (measEmbed μ))`. `borel_finiteMeasure_eq` from `borel_comap` and `Pi.borelSpace`. `measurable_pathFiniteMeasure_iff` from `ContinuousMap.borel_eq_iSup_comap_eval` (`Set.Icc 0 T` is compact, second countable; `FiniteMeasure ℝ` is regular, being metrizable).

### 2.4 H3, H4: compact sets (`Tightness/CompactSets.lean`, `Tightness/PathCompact.lean`)

```lean
/-- `{μ : μ(cosh) ≤ M}` is compact (article, proof of Prop 5.1, condition (i)). -/
theorem isCompact_coshBall (M : ℝ≥0∞) (hM : M ≠ ⊤) :
    IsCompact {μ : FiniteMeasure ℝ | ∫⁻ x, ENNReal.ofReal (Real.cosh x) ∂(μ : Measure ℝ) ≤ M}

/-- `t ↦ ∫ f_j dγ(t)`. -/
def testPath {T : ℝ} (j : ℕ) (γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ)) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => ∫ x, tightTest j x ∂(γ t : Measure ℝ),
    (FiniteMeasure.continuous_integral_boundedContinuousFunction (tightTest j)).comp γ.continuous⟩

/-- Compact sets of `C([0,T], ℳ₊)`: compact containment plus compactness of the test paths. -/
theorem isCompact_pathSet {T : ℝ} {K₀ : Set (FiniteMeasure ℝ)} (hK₀ : IsCompact K₀)
    {C : ℕ → Set C(Set.Icc (0 : ℝ) T, ℝ)} (hC : ∀ j, IsCompact (C j)) :
    IsCompact {γ : C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ) |
      (∀ t, γ t ∈ K₀) ∧ ∀ j, testPath j γ ∈ C j}

/-- Bounded paths with a prescribed modulus of continuity. -/
def modulusSet (T M : ℝ) (δ : ℕ → ℝ) : Set C(Set.Icc (0 : ℝ) T, ℝ) :=
  {g | (∀ t, |g t| ≤ M) ∧ ∀ m : ℕ, ∀ s t : Set.Icc (0 : ℝ) T,
    |(s : ℝ) - t| ≤ δ m → |g s - g t| ≤ 1 / (m + 1)}

theorem isCompact_modulusSet (T M : ℝ) (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) :
    IsCompact (modulusSet T M δ)
```
* `isCompact_coshBall`: closed (supremum over $N$ of the continuous maps $\mu\mapsto\int\min(\cosh,N)d\mu$), contained in $\lbrace\mathrm{mass}\le M,\ \mu([-\ell,\ell]^c)\le M/\cosh\ell\ \forall\ell\in\mathbb N\rbrace$, compact by `isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le` (with `Monotone K`).
* `isCompact_pathSet`: either (a) post-compose with `measEmbed` (`ContinuousMap.isEmbedding_postcomp`), identify `C(I, ℕ → ℝ)` with `ℕ → C(I, ℝ)` (prove that `ContinuousMap.piEquiv` is a homeomorphism for compact `I`), use Tychonoff (`isCompact_univ_pi`) and the closedness of $\lbrace\eta:\eta(t)\in\mathrm{measEmbed}(K_0)\ \forall t\rbrace$; or (b) sequential compactness, since `C(I, FiniteMeasure ℝ)` is metrizable: extract a subsequence along which all test paths converge uniformly (product of compact metrizable spaces), identify the pointwise limit in $K_0$ by injectivity of `measEmbed`, and get uniform convergence in `C(I, FiniteMeasure ℝ)` from that of `measEmbed ∘ γ`. The task chooses; (a) is shorter if the `piEquiv` homeomorphism goes through.
* `isCompact_modulusSet`: Arzelà–Ascoli (`BoundedContinuousFunction.arzela_ascoli` through `ContinuousMap.isometryEquivBoundedOfCompact`, or `ArzelaAscoli.isCompact_of_equicontinuous`); the set is closed, equicontinuous and pointwise bounded by $M$.

### 2.5 H5: Aldous' criterion for continuous paths (`Martingales/Aldous.lean`, `Martingales/AldousPathwise.lean`)

Both elaborated:
```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **Aldous' trick**: from deterministic shifts to a stopping time `σ ∈ [τ, τ + δ]`. -/
theorem aldous_trick [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    {T δ η a : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ),
        μ {ω | η ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a)
    {τ σ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓖 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hσ : IsStoppingTime 𝓖 (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T) (hτσ : τ ≤ σ) (hσδ : ∀ ω, (σ ω : ℝ) ≤ τ ω + δ) :
    μ {ω | 2 * η ≤ |X (σ ω) ω - X (τ ω) ω|} ≤ ENNReal.ofReal (3 * a)

/-- **Aldous' criterion, continuous paths**, two-scale quantitative form. -/
theorem aldous_modulus [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω) (hXa : ∀ t : ℝ≥0, Measurable[𝓖 t] (X t))
    {T η δ δ₁ a a₁ : ℝ} {N : ℕ} (hT : 0 ≤ T) (hη : 0 < η) (hδ : 0 < δ) (hδδ₁ : δ ≤ δ₁)
    (hδ₁ : δ₁ ≤ 1 / 2) (hN : 2 * T ≤ N * δ₁)
    (hA₁ : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ₁),
        μ {ω | η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a₁)
    (hA : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (ρ ω : WithTop ℝ≥0)) →
      (∀ ω, (ρ ω : ℝ) ≤ T + 1) → ∀ s ∈ Set.Icc (0 : ℝ) (2 * δ),
        μ {ω | η / 2 ≤ |X (ρ ω + s) ω - X (ρ ω) ω|} ≤ ENNReal.ofReal a) :
    μ {ω | ∃ s ∈ Set.Icc (0 : ℝ) T, ∃ t ∈ Set.Icc (0 : ℝ) T,
      |t - s| ≤ δ ∧ 3 * η ≤ |X t ω - X s ω|} ≤ ENNReal.ofReal (6 * a₁ + 3 * N * a)
```
* Hypotheses on `X`: *all* paths continuous on `[0, ∞)` and adapted, the setting of Stage 2's `isStoppingTime_hitTime`. Applications use a version (Section 2.6) and the filtration `nullAug μ (filtN n 𝓕)`. The constants (`6`, `3`, the horizon `T + 1`) are those of the proof sketched in 1.2 (e); the task may adjust them (more room, e.g. `T + 2`) if the proof needs it, keeping the shape.
* `aldous_trick`: needs only joint measurability of $(s,\omega)\mapsto X_{\rho(\omega)+s}(\omega)$ (`measurable_uncurry_of_continuous_of_measurable`, `ρ` measurable) and Tonelli on $[0,2\delta]\times\Omega$; the stopping-time property is used only to apply `hA` at `τ` and `σ`.
* `aldous_modulus`: define the hitting sequence `aldousHit X η T k : Ω → ℝ≥0` (`τ₀ = 0`, `τ_{k+1}` = `hitTime` of the continuous adapted process $t\mapsto\lvert X_t-X_{t\wedge\tau_k}\rvert$ at level $\eta$, capped at $T$); prove it is a sequence of stopping times (adaptedness of the stopped process of a continuous adapted process: from Mathlib's progressive measurability, `StronglyAdapted.isStronglyProgressive_of_continuous`, or by dyadic approximation as in `StoppingAux.lean`); the two pathwise lemmas of 1.2 (e) are statements about one continuous function and its hitting sequence, with no probability (file `AldousPathwise.lean`); then the union bound and the Markov inequality on the counting variable $\sum_{k<N}\mathbf 1_{H_k}$.

### 2.6 Q3 infrastructure: the version (`Tightness/Version.lean`)

```lean
/-- Internal: a version of `t ↦ 𝖹_n(t)` on `[0, T]` which is measurable, whose test integrals are
adapted to the augmented time-changed filtration, and whose every path is continuous. -/
theorem exists_tiltedPath_version (hB) (hψ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable Zv ∧
      (∀ (t : Set.Icc (0 : ℝ) T) (j : ℕ), Measurable[nullAug μ (filtN n 𝓕) (t : ℝ).toNNReal]
        fun ω => ∫ x, tightTest j x ∂(Zv ω t : Measure ℝ)) ∧
      ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t
```
Construction: $S$ = complement of `toMeasurable μ` of the bad set (paths not `TiltGood n T`); $S$ is measurable, of probability one, and in `nullSets μ` (its complement is a measurable null set). On $S$, $t\mapsto\mathsf Z_n(t)$ is continuous (`FiniteMeasure.continuous_iff_forall_continuous_integral` and `integral_tiltedMeasure`, the series being dominated by $Ke^{-\lvert x\rvert}$); off $S$, the constant path $0$. Test integrals: on $S$ they are limits of finite sums of $\mathcal F_{nt/2}$-measurable functions (`tiltZ_measurable`), hence measurable for $\mathcal F_{nt/2}\vee\sigma(\text{null sets})$; measurability of `Zv` by `measurable_pathFiniteMeasure_iff`. Also a corollary for the frozen measures: `t ↦ ϱ_n(t) • Zv ω t` is a version of `rescaledMeasure ⊤ n (density ψ ω)` (by `rescaledMeasure_eq`), for use in Stage 5.

---

## 3. The article's results in Lean

**Statements marked (E) go to the author for approval before their proofs** (rule 5 of `CLAUDE.md`). All of Section 3 was elaborated in the scratch file `Stage3.lean` (Section 7). Hypotheses `(hB) (hψ)` mean `[IsProbabilityMeasure μ] (hB : IsBrownianFamily 𝓕 B μ) (hψ : IsWaveFunction ⊤ 𝓕 B ψ μ)`, as in Stage 2. Safeguards against Lean's conventions (rule (i) of `docs/stage2-design.md`, Section 3): every series is asserted to converge (or follows from a convergence asserted in the same statement), every expectation has an integrability conjunct, suprema are taken in $[0,\infty]$, probabilities of events whose measurability is not claimed are outer probabilities (a bound on the outer probability is stronger), and laws are only taken of maps asserted (almost everywhere) measurable.

### 3.1 Notation $\mathsf Z_n(t;\varphi)=\int\varphi\ d\mathsf Z_n(t)$ (E, auxiliary) — `Tightness/Integral.lean`

```lean
/-- `𝖹_n(t;φ) = ∫ φ d𝖹_n(t)` (the notation of the article), when `∑ₓ 𝔷_n(t,x) < ∞`. -/
theorem integral_tiltedMeasure {n t : ℝ} {ω : Ω} (hs : Summable (zN n ψ ω t))
    {φ : ℝ → ℝ} (hφm : Measurable φ) {c : ℝ} (hφ : ∀ y, |φ y| ≤ c) :
    IsFiniteMeasure (tiltedMeasure n ψ ω t) ∧
    Integrable φ (tiltedMeasure n ψ ω t) ∧
    ∫ y, φ y ∂(tiltedMeasure n ψ ω t) = pairZ n ψ ω t φ
```
(plus, internal: the `lintegral` version $\int^-\mathrm{ofReal}(\varphi)\ d\mathsf Z_n(t)=\sum_x\mathrm{ofReal}(\mathfrak z_n(t,x)\varphi(y_n(t,x)))$ for $\varphi\ge0$, without summability, used with $\varphi=\cosh$.)

### 3.2 Lemma 5.2 (E) — `Tightness/ExpMoments.lean`

```lean
/-- **Lemma 5.2**, with (5.1): for `n ≥ 1`, almost surely `∑ₓ 𝔷_n(t,x) e^{b y_n(t,x)}` converges for
all `t ≥ 0` and `b ∈ [-1,1]`; `𝔼[𝖹_n(t;e_b)] ≤ e^{2t}`; and
`ℙ(sup_{t ∈ [0,T]} 𝖹_n(t;cosh) ≥ K) ≤ 2 e^{2T} / K`. -/
theorem lemma_5_2 (hB) (hψ) {n : ℝ} (hn : 1 ≤ n) :
    (∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t → ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      Summable fun x => zN n ψ ω t x * Real.exp (b * rescaledPosition n t x)) ∧
    (∀ b ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => pairZ n ψ ω t fun y => Real.exp (b * y)) μ ∧
      ∫ ω, pairZ n ψ ω t (fun y => Real.exp (b * y)) ∂μ ≤ Real.exp (2 * t)) ∧
    ∀ T K : ℝ, 0 < T → 0 < K →
      μ {ω | ENNReal.ofReal K ≤ ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (pairZ n ψ ω t Real.cosh)} ≤ ENNReal.ofReal (2 * Real.exp (2 * T) / K)
```
The summability conjunct makes `pairZ` with the unbounded weights $e^{by}$, $\cosh$ genuine (on its complement, a null set, `pairZ` is $0$ by Lean's convention).

### 3.3 Equation (5.2) (E) — `Tightness/AldousCondition.lean`

```lean
/-- **Equation (5.2)** (Aldous' condition), with the quantitative bound of the proof of
Proposition 5.1: for every `T` there is `c` such that for every realization, `n ≥ 1`,
`φ ∈ C_b³` with `‖φ‖_{1,3} ≤ C`, stopping time `τ ≤ T` of `𝓕ⁿ` augmented by the null sets,
`s ∈ [0, 1/16]` and `η > 0`:
`ℙ(|𝖹_n(τ+s;φ) - 𝖹_n(τ;φ)| > η) ≤ c (C s / η + C² √s / η²)`. -/
theorem aldous_condition (T : ℝ) :
    ∃ c : ℝ, ∀ {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
      IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ →
      ∀ {n C : ℝ} {φ : ℝ → ℝ}, 1 ≤ n → IsC13 1 (fun _ => φ) (fun _ _ => 0) C →
      ∀ {τ : Ω → ℝ≥0}, IsStoppingTime (nullAug μ (filtN n 𝓕)) (fun ω => (τ ω : WithTop ℝ≥0)) →
      (∀ ω, (τ ω : ℝ) ≤ T) → ∀ {s η : ℝ}, 0 ≤ s → s ≤ 1 / 16 → 0 < η →
      μ {ω | η < |pairZ n ψ ω (τ ω + s) φ - pairZ n ψ ω (τ ω) φ|} ≤
        ENNReal.ofReal (c * (C * s / η + C ^ 2 * Real.sqrt s / η ^ 2))
```
T0' adds the conjunct `∀ᵐ ω ∂μ, ∀ t, 0 ≤ t → Summable (zN n ψ ω t)` after the `∀ … →` binders (the elaborated version above lacks it). The article's (5.2), $\lim_{\delta\to0}\sup_n\sup_{\tau,s\le\delta}\mathbb P(\dots)=0$, follows at once. A possible explicit constant: $c=2^{20+16T}$ (from (4.8) on $[0,T+1]$ and (4.9)); T0' may state it explicitly instead of "∃ c".

### 3.4 Proposition 5.1 (E) — `Tightness/Prop51.lean`

```lean
/-- **Proposition 5.1**, first part: almost surely, `t ↦ 𝖹_n(t)` is a continuous path in `ℳ₊(ℝ)`. -/
theorem prop_5_1_continuous (hB) (hψ) {n : ℝ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, ∃ γ : C(ℝ≥0, FiniteMeasure ℝ), ∀ t : ℝ≥0,
      (γ t : Measure ℝ) = tiltedMeasure n ψ ω t

/-- **Proposition 5.1**, the process as a random variable in `C([0,T], ℳ₊)`: a measurable version
(Borel σ-algebra of the topology of uniform convergence, as in the frozen statement). -/
theorem prop_5_1_version (hB) (hψ) {n : ℝ} (hn : 1 ≤ n) (T : ℝ) :
    ∃ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), Measurable Zv ∧
      ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t

universe u

/-- **Proposition 5.1**, tightness: for `T > 0` and `ε > 0` there is a compact set `𝒦` of
`C([0,T], ℳ₊)` such that, for every realization, every `n ≥ 1` and every version `Zv` of
`t ↦ 𝖹_n(t)`, `ℙ(Zv ∉ 𝒦) ≤ ε`. -/
theorem prop_5_1 {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ 𝒦 : Set C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ), IsCompact 𝒦 ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
        [IsProbabilityMeasure μ] {B : ℤ × Fin 2 → ℝ → Ω → ℝ} {ψ : ℝ → Ω → ℓ²(ℤ, ℂ)},
        IsBrownianFamily 𝓕 B μ → IsWaveFunction ⊤ 𝓕 B ψ μ → ∀ {n : ℝ}, 1 ≤ n →
        ∀ Zv : Ω → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ),
          (∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ) T, (Zv ω t : Measure ℝ) = tiltedMeasure n ψ ω t) →
          μ (Zv ⁻¹' 𝒦ᶜ) ≤ ENNReal.ofReal ε

/-- **Proposition 5.1** for a sequence of realizations: the laws are tight
(`IsTightMeasureSet`, Mathlib). -/
theorem prop_5_1_isTight {T : ℝ} (hT : 0 < T) (n : ℕ → ℝ) (hn : ∀ k, 1 ≤ n k)
    {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (𝓕 : ∀ k, Filtration ℝ≥0 (mΩ k))
    (B : ∀ k, ℤ × Fin 2 → ℝ → Ω k → ℝ) (hB : ∀ k, IsBrownianFamily (𝓕 k) (B k) (μ k))
    (ψ : ∀ k, ℝ → Ω k → ℓ²(ℤ, ℂ)) (hψ : ∀ k, IsWaveFunction ⊤ (𝓕 k) (B k) (ψ k) (μ k))
    (Zv : ∀ k, Ω k → C(Set.Icc (0 : ℝ) T, FiniteMeasure ℝ))
    (hZm : ∀ k, AEMeasurable (Zv k) (μ k))
    (hZ : ∀ k, ∀ᵐ ω ∂μ k, ∀ t : Set.Icc (0 : ℝ) T,
      (Zv k ω t : Measure ℝ) = tiltedMeasure (n k) (ψ k) ω t) :
    IsTightMeasureSet (Set.range fun k => (μ k).map (Zv k))
```
Remarks for T0': in `prop_5_1` the universe of `Ω` is a parameter `u` (the statement is universe-polymorphic; `prop_5_1_isTight` instantiates it). Two versions coincide almost surely (paths agreeing at all $t$ are equal), so `prop_5_1` for every version is not stronger than for one; it is stated for every version so that later stages can use any. The (E) status of `prop_5_1_isTight` is for the author's convenience: it is the literal "family of laws is tight".

### 3.5 Infrastructure statements (not for the author)

Section 2 (H1–H5, `exists_tiltedPath_version`), plus internal lemmas of the QSSEP tasks: the identity $\mathsf Z_n(t;e_b)=e^{\kappa t}N_{nt/2}$ with $\lvert\kappa\rvert\le2$; IsC13 of a time-independent $C_b^3$ function on any horizon; the decomposition of $\mathsf Z_n(\tau+s;\varphi)-\mathsf Z_n(\tau;\varphi)$ into drift and martingale increments at stopping times.

---

## 4. Task breakdown

Method of Stage 2 (`docs/task-rules.md`): one Opus 5.5 agent per task, fresh context, own worktree, checked by `scripts/task_merge.sh` and merged by the main session. Sizes are lines of Lean to write. "Uses" lists the statements a task may assume (possibly still `sorry` in `master`). The approved Stage 2 statements (`docs/frozen-stage2.txt`) and the new approved Stage 3 statements must not change.

| Id | Files (under `QSSEPtoKPZ/`) | Content | Uses | Size | Can start |
|---|---|---|---|---|---|
| **T0'** | `Tightness/Integral.lean`, `Tightness/ExpMoments.lean`, `Tightness/AldousCondition.lean`, `Tightness/Prop51.lean` (statements of Section 3 with `sorry`); `docs/stage3-statements.md` and its PDF for the author | statements for approval | Stage 2 | 250–450 | first |
| **I0'** | `Tightness/TestFunctions.lean`, `Tightness/FiniteMeasureEmbed.lean`, `Tightness/CompactSets.lean`, `Tightness/PathCompact.lean`, `Martingales/Aldous.lean`, `Tightness/Version.lean` (Section 2 signatures, definitions complete, proofs `sorry`); `docs/stage3-interfaces.md` | frozen interfaces | — | 300–500 | with T0' |
| H1 | `Tightness/TestFunctions.lean` | $\beta$: smoothness, bounds, support, partition of unity; `tightTest`; `isC13_tightTest` | I0' | 300–600 | after I0' |
| H2 | `Tightness/FiniteMeasureEmbed.lean` (+ `FiniteMeasureApprox.lean`) | (F) (uniform approximation of $C_c$ functions, cut-off, filter argument); embedding; instances; Borel $\sigma$-algebra; `measurable_pathFiniteMeasure_iff` | H1 interface | 600–1,000 | after I0' |
| H3 | `Tightness/CompactSets.lean` | `isCompact_coshBall` | — | 200–400 | after I0' |
| H4 | `Tightness/PathCompact.lean` | `isCompact_pathSet` (`piEquiv` homeomorphism or sequential argument), `isCompact_modulusSet` (Arzelà–Ascoli) | H2 interface | 500–900 | after I0' |
| H5a | `Martingales/Aldous.lean` (first part) | `aldous_trick` (joint measurability, Tonelli) | — | 250–450 | after I0' |
| H5b | `Martingales/AldousPathwise.lean`, `Martingales/Aldous.lean` (second part) | hitting sequence, stopping times, the two pathwise lemmas, `aldous_modulus` | H5a interface | 600–1,000 | after I0' |
| Q1 | `Tightness/Integral.lean`, `Tightness/ExpMoments.lean` | `integral_tiltedMeasure` (and the `lintegral` form); **Lemma 5.2** | Stage 2 (`lemma_2_3_linear`, `HasBracket.timeChange`, `IsCL2Mart.measure_exists_ge_le`) | 400–700 | after approval |
| Q2 | `Tightness/AldousCondition.lean` | **(5.2)** | Stage 2 (`prop_3_1`, `prop_3_1_generator`, `prop_4_3_bounds`, `prop_4_3_increment`, optional sampling), Q1 interface | 300–600 | after approval |
| Q3 | `Tightness/Version.lean`, `Tightness/Prop51.lean` (first two statements) | `exists_tiltedPath_version`, **Prop 5.1 continuity and version**; corollary for `rescaledMeasure ⊤` | H2 interface, Q1 interface | 400–700 | after approval |
| Q4 | `Tightness/Prop51.lean` (last two statements), `Tightness/Assembly.lean` | **Prop 5.1 tightness**: compact containment (H3 + Lemma 5.2), tightness of the test paths (H5 + (5.2) + (4.8) + `isCompact_modulusSet`), union bound, `isCompact_pathSet`; `prop_5_1_isTight` | all interfaces | 500–900 | after approval (better after H4, H5b merged) |

Dependencies and parallelism:

```
T0' ──► author's approval ──► Q1, Q2, Q3 ──► Q4
 │                                           ▲
 └► I0' ──► H1, H2, H3, H4, H5a, H5b ────────┘   (parallel, generic, no approval needed)
```

* Wave 1 (after T0' and I0' are merged and reviewed by the main session): H1, H2, H3, H4, H5a, H5b in parallel (six agents; or two batches of three). T0' goes to the author.
* Wave 2 (after approval): Q1, Q2, Q3 in parallel (they use only Stage 2 and the interfaces).
* Wave 3: Q4.
* Critical path: I0' → H5b → Q4, or T0' → approval → Q2 → Q4: three tasks after the interfaces.
* Every task: no new `sorry` at the end; standard axioms only except through `sorry`'d interfaces of other running tasks (to be listed); names prefixed (`tight…`, `aldous…`, `measEmbed…`) and private auxiliaries (rule 7 of `docs/task-rules.md`).

Notes for specific tasks:

* **H2**: avoid the `MeasurableSpace (FiniteMeasure ℝ)` instance (Giry); write `borel (FiniteMeasure ℝ)` and use `ContinuousMap.borel_eq_iSup_comap_eval`. The approximation argument works along an arbitrary filter; masses are eventually bounded by $\mu(1)+1$.
* **H4 (option a)**: needs a lemma "a family of maps `I → ℝ` converges uniformly in each coordinate iff the map `I → (ℕ → ℝ)` converges uniformly", for the `Pi` uniform structure (`Pi.uniformSpace`, `Topology/UniformSpace/Pi.lean`).
* **H5b**: the hitting sequence is defined by recursion on `k` with `hitTime` of Stage 2; its adaptedness requires that `t ↦ X (min t (τ_k ω)) ω` is adapted (stopped process of a continuous adapted process at a stopping time). The pathwise lemmas are independent of probability and can be written first.
* **Q1**: the time change: Lemma 2.3 (1) on $[0,nT/2]$ for $\mathcal F$, then `HasBracket.timeChange` to $\mathcal F^n$ (as in the proof of `prop_3_1`, `TiltedField/Martingales.lean`, line 307). The bound $\lvert\kappa\rvert\le2$: $\kappa=n(\sinh\theta_n\sinh\delta-\theta_n\delta)+n\cosh\theta_n(\cosh\delta-1)$, $\delta=bn^{-1/2}$, with the inequalities of Section 3.1 (`sinh_sub_self_bounds`, `constants_bounds`).
* **Q2**: Prop 3.1 is stated for `IsC13 T φ φt C`; a time-independent $C_b^3$ function satisfies `IsC13 T' (fun _ => φ) (fun _ _ => 0) C` for every `T'` (small lemma). Horizon $T+1$ for (4.8) and Prop 3.1 (since $\tau+s\le T+1/16$).
* **Q4**: apply `aldous_modulus` to $X_t=$ `testPath j (Zv' ω) (min t (T+2))` for a version `Zv'` on $[0,T+2]$ from `exists_tiltedPath_version` (all paths continuous, adapted to `nullAug μ (filtN n 𝓕)`); transfer (5.2) from `pairZ` to $X$ (equal at all times almost surely); for each $j$ and $m$ choose $\delta_1$, $N$, $\delta$ from the constant of (5.2) and `isC13_tightTest j` (uniformly in the realization and in $n$), with $\eta=1/(3(m+1))$ and error $\varepsilon2^{-j-m-3}$; the compact set is `{γ | (∀ t, γ t ∈ coshBall M) ∧ ∀ j, testPath j γ ∈ modulusSet T (M_j) (δ_j)}`.

---

## 5. Risks and decisions for the author

**Decisions (my recommendation in bold).**

* **D1'. No Skorokhod space: a tightness criterion in $C([0,T],\mathcal M_+)$** (compact containment plus tightness of the real processes $\mathsf Z_n(\cdot;f_j)$ for a countable family), instead of Jakubowski's criterion in $D([0,T],\mathcal M_+)$ followed by the remark that the paths are continuous. This is the route of `PLAN.md` (Section 3). **Recommended.**
* **D2'. The countable family** $f_0=1$, $f_{m,k}(x)=\beta(mx-k)$ ($m\ge1$, $k\in\mathbb Z$; $\beta$ a smooth bump whose integer translates sum to $1$), instead of all $\varphi\in C_c^\infty$. Same conditions (i), (ii) as the article, for fewer test functions; the constant $1$ controls the mass. **Recommended.**
* **D3'. Form of "tight"**: uniform compact sets over all realizations and all $n\ge1$, for every version (`prop_5_1`), plus Mathlib's `IsTightMeasureSet` for every sequence of realizations (`prop_5_1_isTight`). **Recommended.**
* **D4'. (5.2) in quantitative form**: $\mathbb P(\lvert\mathsf Z_n(\tau+s;\varphi)-\mathsf Z_n(\tau;\varphi)\rvert>\eta)\le c_T(Cs/\eta+C^2\sqrt s/\eta^2)$ for $s\le1/16$, $\varphi\in C_b^3$ with $\lVert\varphi\rVert_{1,3}\le C$ (the article takes $\varphi\in C_c^\infty$; its proof uses only $\lVert\varphi\rVert_{1,3}$), $\tau\le T$ a stopping time of $\mathcal F^n$ augmented by the null sets (as decision D4 of Stage 2). The constant: "there is $c$ depending only on $T$" (as D8 of Stage 2), or explicitly $2^{20+16T}$. **Recommended, with "∃ c".**
* **D5'. Lemma 5.2**: the event $\lbrace\sup_{t\le T}\mathsf Z_n(t;\cosh)\ge K\rbrace$ with the supremum in $[0,\infty]$ and its outer probability; summability of the exponentially weighted series and integrability asserted. **Recommended.**
* **D6'. Continuity and versions**: "almost surely, there is a continuous map $\gamma:[0,\infty)\to\mathcal M_+$ with $\gamma(t)=\mathsf Z_n(t)$ for all $t$"; and a measurable version $\Omega\to C([0,T],\mathcal M_+)$ (Borel $\sigma$-algebra of uniform convergence, as in the frozen statement). **Recommended.**
* **D7'. Scope: $\mathsf Z_n$ only**, as in the article (no tightness statement for $\mathcal Z_n=\varrho_n\mathsf Z_n$; a version of $\mathcal Z_n$ is given as an infrastructure corollary for Stage 5). **Recommended.**
* **D8'. Polish space.** The article uses that $\mathcal M_+$, hence $C([0,T],\mathcal M_+)$, is Polish (for Skorokhod's representation in Section 7.1). Stage 3 proves metrizable and separable, not complete. Skorokhod's representation theorem holds for a separable metric space (Billingsley, Theorem 6.7, needs only a separable support of the limit), so completeness can be avoided in Stage 4. **Recommended: do not prove completeness in Stage 3**; Stage 4 decides (if needed: Gδ argument via measures on $[-\infty,\infty]$, a separate task of 400–800 lines).

**Places where the Lean proof departs from the article** (statements unchanged in substance; to record in `PROGRESS.md`):

1. Jakubowski's criterion in $D$ replaced by a direct criterion in $C$ (D1'), with a countable family of test functions (D2').
2. Aldous' criterion is proved, for continuous paths only, by the trick of 1.2 (e) and a hitting-time count, not cited.
3. Metrizability and separability of $\mathcal M_+(\mathbb R)$ are proved through the embedding $\mu\mapsto(\mu(f_j))_j$ (not in Mathlib); completeness is not proved (D8').
4. (5.2) is stated and used in quantitative form (D4').

**Risks.**

* **R1 (H2, the new topology).** (F) and its consequences are the only substantial new mathematics of the stage outside the article. The argument is elementary but involves filters, uniform approximation and integrals of bounded continuous functions; budget 600–1,000 lines. Fallback: none needed mathematically; if the `IsInducing` proof is awkward, prove `isEmbedding_measEmbed` through `Topology.IsInducing` of `toWeakDualBCNN` and nets.
* **R2 (two $\sigma$-algebras on $\mathcal M_+$).** Mathlib's instance on `FiniteMeasure ℝ` is the Giry $\sigma$-algebra. Statements of Stage 3 never use it (only the Borel $\sigma$-algebra of `C(Set.Icc 0 T, FiniteMeasure ℝ)`, an instance). Stage 4 ("all quantities are measurable functions of the trajectory": the atoms $\mathfrak z_n(t,x)=\mathsf Z_n(t)(\lbrace y_n(t,x)\rbrace)$) will probably want "Giry = Borel" on $\mathcal M_+(\mathbb R)$ (`BorelSpace`); it follows from (F) by a $\pi$-$\lambda$ argument (300–500 lines), to be done in Stage 4.
* **R3 (stopping-time technicalities in H5b).** Adaptedness of stopped processes, measurability of $X$ at random times, horizons $T+1$, $T+2$. Mathlib's progressive measurability covers it; Stage 2's `StoppingAux.lean` has the dyadic tools.
* **R4 (measurability of real series).** `pairZ` is a `tsum`, $0$ when the series diverges; measurability is proved on the good set $S$ (limits of partial sums), never globally.
* **R5 (frozen interfaces).** As in Stage 2: an interface found false costs a re-run of its dependents. The interfaces of Section 2 are standard; the constants of `aldous_modulus` may need adjusting (the task may change them in its own file before Q4 uses them).
* **R6 (Stage 4 needs).** Stage 4 will need, besides Prop 5.1: Prokhorov (Mathlib), metrizability of the space of laws (available after H2), Skorokhod's representation (Stage 4), `BorelSpace (FiniteMeasure ℝ)` (R2), measurability of $\mathsf Z_n$-functionals of the path. The version of Q3 records adaptedness of test integrals, which helps with the natural filtration of $\mathsf Z_n$ (item W3 of the Stage 2 audit).

---

## 6. Size estimate

| Part | Tasks | This design (k lines) |
|---|---|---|
| statements, interfaces | T0', I0' | 0.55–0.95 |
| test functions, embedding, instances, Borel | H1, H2 | 0.9–1.6 |
| compact sets ($\mathcal M_+$, paths, Arzelà–Ascoli) | H3, H4 | 0.7–1.3 |
| Aldous' criterion | H5a, H5b | 0.85–1.45 |
| Lemma 5.2, (5.2) | Q1, Q2 | 0.7–1.3 |
| version, Prop 5.1 | Q3, Q4 | 0.9–1.6 |
| **Total Stage 3** | 12 tasks | **about 4.6–8.2** |

`PLAN.md` gives 8–12k lines for package H. The design is lower for the same reasons as in Stage 2 (Stage 2's design estimated 16–27k against 30–45k in the plan, and Stage 2 came out at about 20k): no Skorokhod space, Aldous only for continuous paths, the article side reduced to assembling Stage 2 results. The generic part (H1–H5, about 60% of the stage) is the least certain. At Stage 2's pace this is roughly 15 to 30 agent-hours; with up to six agents in parallel in Wave 1, a few hours of wall time plus the author's review of T0'.

---

## 7. What was checked

* Scratch files (not in the repository), in `<scratch>/design3/`:
  * `Names.lean`: every Mathlib name of Section 2.1 resolves with `#check` (two names tried and not found: `tendstoUniformlyOn_pi`, `MeasureTheory.measurable_of_tendsto_metrizable`; the latter is `measurable_of_tendsto_metrizable` at the root namespace). Instances `SecondCountableTopology (ℕ → ℝ)`, `MetrizableSpace (ℕ → ℝ)`, `T2Space` and `BorelSpace` of `C(Set.Icc 0 T, FiniteMeasure ℝ)` found.
  * `Stage3.lean`: all signatures of Sections 2.2–2.5 and 3 (with `sorry` proofs, definitions complete except three proof obligations of `tightTest`), compiled with `lake env lean` against the project at commit `5a42696` (Lean 4.35.0, Mathlib v4.35.0): only `declaration uses 'sorry'` warnings. With the two `sorry`'d instances of 2.3, instance search finds `MetrizableSpace`, `SecondCountableTopology`, `SeparableSpace`, `PseudoMetrizableSpace` of `C(Set.Icc 0 T, FiniteMeasure ℝ)` and `MetrizableSpace (ProbabilityMeasure C(Set.Icc 0 T, FiniteMeasure ℝ))`.
  * Not elaborated: `exists_tiltedPath_version` (Section 2.6) and the summability conjunct to add in `aldous_condition`.
* Numerical check of $\lvert\kappa\rvert\le2$ in the proof of Lemma 5.2: maximum $1.22$ over $n\in\lbrace1,1.01,1.1,1.5,2,3,5,10,10^2,10^4,10^8\rbrace$, $b\in[-1,1]$ (step $0.01$).
* The article (SHA-256 unchanged) Sections 3.1, 5, 7 (beginning of 7.1 and the end of 7.3) and 8 were read for the uses of Section 5.
* Not checked: proofs; the line estimates; that the constants in `aldous_trick`, `aldous_modulus` are exactly those the proofs give (they follow the sketch of 1.2 (e)). The repositories of `docs/existing-lean-code.md` for package H (`MarkovProcess` `PathTightness.lean`, `Critical2DKPZ` `ModulusTightness.lean`, type-D `aldous_tightness`) were not consulted; agents of H4, H5b may read them for ideas (no copying).
