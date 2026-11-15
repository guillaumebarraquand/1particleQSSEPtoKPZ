# Stage 3: interfaces of package H (task I0')

Written on 13 November 2026 by the I0' agent (Opus 5.5). For the main session and the proving agents. The Lean files are the reference; this list gives one line per interface: name, file (under `QSSEPtoKPZ/`), meaning. Lemmas marked **(proved)** were proved in I0'; all others are `sorry` and belong to the task named in the heading. Sections 2 and 4 of `docs/stage3-design.md` are the specification; the departures from it are listed at the end.

Conventions: `module`, `@[expose] public section`, namespace `QSSEPtoKPZ`. Processes `X : ℝ → Ω → ℝ`, filtrations `Filtration ℝ≥0 mΩ`, stopping times `τ : Ω → ℝ≥0` coerced to `WithTop ℝ≥0`; probabilities of events whose measurability is not claimed are outer measures. `ℳ₊(ℝ) = FiniteMeasure ℝ` with the weak topology; **its Borel σ-algebra is always written `borel (FiniteMeasure ℝ)`** (Mathlib's `MeasurableSpace (FiniteMeasure ℝ)` instance is the Giry σ-algebra). `C(Set.Icc 0 T, ·)` has the compact-open topology (uniform convergence) and Mathlib's Borel instance. Names are prefixed by topic (`bump…`, `tightEmb…`, `tightCoshBall`, `pathCpt…`, `aldous…`), different from the design's names, to avoid clashes with task T0' (see the list at the end).

## Definitions (complete, no `sorry`)

| Name | File | Meaning |
|---|---|---|
| `bumpBeta x` | `Tightness/TestFunctions.lean` | $\beta(x)=s(x+1)-s(x)$, $s$ = `Real.smoothTransition` (design: `tightBump`) |
| `bumpTestRaw j x` | same | $f_0=1$, $f_{j+1}(x)=\beta((m+1)x-k)$, $(m,k)$ = `Denumerable.ofNat (ℕ × ℤ) j` (design: `tightTestRaw`) |
| `bumpTest j` | same | $f_j$ as `ℝ →ᵇ ℝ` (bound 1) (design: `tightTest`) |
| `tightEmb μ` | `Tightness/FiniteMeasureEmbed.lean` | $\mu\mapsto(\int f_j\,d\mu)_{j\in\mathbb N}\in\mathbb R^{\mathbb N}$ (design: `measEmbed`) |
| instances `tightEmb_secondCountableTopology`, `tightEmb_metrizableSpace` | same | `SecondCountableTopology`, `MetrizableSpace` of `FiniteMeasure ℝ` (from `isEmbedding_tightEmb`, `sorry`'d) |
| `tightCoshBall M` | `Tightness/CompactSets.lean` | $\lbrace\mu:\int^-\cosh\,d\mu\le M\rbrace$, $M\in[0,\infty]$ |
| `pathCptTest j γ` | `Tightness/PathCompact.lean` | the real path $t\mapsto\int f_j\,d\gamma(t)$ in `C([0,T], ℝ)` (design: `testPath`) |
| `pathCptSet K₀ C` | same | $\lbrace\gamma:\gamma(t)\in K_0\ \forall t,\ \texttt{pathCptTest}\ j\ \gamma\in C_j\ \forall j\rbrace$ |
| `pathCptModulus T M δ` | same | $\lbrace g:\lvert g\rvert\le M,\ \lvert g(s)-g(t)\rvert\le\frac1{m+1}$ if $\lvert s-t\rvert\le\delta_m\ \forall m\rbrace$ (design: `modulusSet`) |
| `aldousHit X η T k` | `Martingales/AldousPathwise.lean` | $\tau_0=0$, $\tau_{k+1}$ = `hitTime` of $t\mapsto\lvert X_t-X_{t\wedge\tau_k}\rvert$ at level $\eta$, capped at $T\in\mathbb R_{\ge0}$ |

With the two instances, instance search finds `MetrizableSpace`, `SecondCountableTopology`, `SeparableSpace`, `BorelSpace` of `C(Set.Icc 0 T, FiniteMeasure ℝ)`, `RegularSpace (FiniteMeasure ℝ)`, and (with `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric` imported) `MetrizableSpace (ProbabilityMeasure C(Set.Icc 0 T, FiniteMeasure ℝ))` (checked).

## H1 — `Tightness/TestFunctions.lean` (uses: nothing)

- `contDiff_bumpBeta`: $\beta$ is $C^\infty$.
- `bumpBeta_nonneg`, `bumpBeta_le_one`, `continuous_bumpBeta` **(proved)**: $0\le\beta\le1$, continuity.
- `bumpBeta_eq_zero_of_one_le_abs`: $\beta(x)=0$ for $\lvert x\rvert\ge1$.
- `hasSum_bumpBeta_sub`: $\sum_{k\in\mathbb Z}\beta(x-k)=1$ (`HasSum`, so the series converges).
- `bumpBeta_iteratedDeriv_bound`: $\exists C\ge0$, $\lvert\beta^{(k)}\rvert\le C$ for $k\le3$.
- `bumpTestRaw_zero` **(proved)**: $f_0=1$.
- `bumpTestRaw_encode_succ` **(proved)**: $f_{\mathrm{encode}(m,k)+1}(x)=\beta((m+1)x-k)$, so every $\beta((m+1)\cdot-k)$ is in the family.
- `continuous_bumpTestRaw`, `abs_bumpTestRaw_le` **(proved)**: $f_j$ continuous, $\lvert f_j\rvert\le1$.
- `coe_bumpTest` **(proved)**: `⇑(bumpTest j) = bumpTestRaw j` (`rfl`).
- `isC13_bumpTestRaw`: $\exists C\ge0$, $\forall T$, `IsC13 T (fun _ => bumpTestRaw j) (fun _ _ => 0) C` ($f_j\in C_b^3$ as a time-independent test function on every horizon; used with `T = 1` in (5.2)).

## H2 — `Tightness/FiniteMeasureEmbed.lean` (uses: H1 interface)

- `continuous_tightEmb_apply` **(proved)**: $\mu\mapsto\int f_j\,d\mu$ is continuous.
- `tightEmb_tendsto_of_forall`: **(F)** if $\int f_j\,d\mu_i\to\int f_j\,d\mu$ along a filter for every $j$, then $\mu_i\to\mu$ weakly (design: `FiniteMeasure.tendsto_of_forall_tightTest`).
- `isEmbedding_tightEmb`: `tightEmb` is a topological embedding into $\mathbb R^{\mathbb N}$.
- `borel_finiteMeasure_eq_iSup_tightEmb`: `borel (FiniteMeasure ℝ) = ⨆ j, (borel ℝ).comap (μ ↦ ∫ f_j dμ)`.
- `measurable_finiteMeasure_iff_tightEmb`: $g:Z\to\mathcal M_+$ is measurable for `borel (FiniteMeasure ℝ)` iff every $z\mapsto\int f_j\,d g(z)$ is measurable (new, pointwise version).
- `borel_pathFiniteMeasure_eq_iSup_tightEmb`: the Borel σ-algebra of `C([0,T], ℳ₊)` is $\bigvee_{t,j}\sigma(\gamma\mapsto\int f_j\,d\gamma(t))$ (new).
- `measurable_pathFiniteMeasure_iff_tightEmb`: $g:Z\to C([0,T],\mathcal M_+)$ measurable iff $z\mapsto\int f_j\,d g(z)(t)$ measurable for all $t\in[0,T]$, $j$ (for Q3).

## H3 — `Tightness/CompactSets.lean` (uses: nothing)

- `isCompact_tightCoshBall`: for $M<\infty$, $\lbrace\mu:\int^-\cosh\,d\mu\le M\rbrace$ is compact (for Q4, condition (i)) (design: `isCompact_coshBall`).

## H4 — `Tightness/PathCompact.lean` (uses: H2 interface)

- `pathCptTest_apply` **(proved)**: `pathCptTest j γ t = ∫ f_j dγ(t)`.
- `isCompact_pathCptSet`: $K_0$ compact and every $C_j$ compact $\Rightarrow$ `pathCptSet K₀ C` compact in `C([0,T], ℳ₊)` (design: `isCompact_pathSet`).
- `isCompact_pathCptModulus`: $\delta_m>0$ for all $m$ $\Rightarrow$ `pathCptModulus T M δ` compact in `C([0,T], ℝ)` (Arzelà–Ascoli) (design: `isCompact_modulusSet`).

## H5a — `Martingales/AldousTrick.lean` (uses: Stage 2)

- `aldous_trick`: all paths continuous, adapted; $\mathbb P(\lvert X_{\rho+s}-X_\rho\rvert\ge\eta)\le a$ for stopping times $\rho\le T+1$, $s\in[0,2\delta]$; $0<\delta\le1$; stopping times $\tau\le\sigma\le\tau+\delta$, $\tau\le T$ $\Rightarrow$ $\mathbb P(\lvert X_\sigma-X_\tau\rvert\ge2\eta)\le3a$ (as in the design).

## H5b — `Martingales/AldousPathwise.lean`, `Martingales/Aldous.lean` (uses: H5a interface, Stage 2 `hitTime`, `isStoppingTime_hitTime`, `lt_of_lt_hitTime`)

- `aldousHit_zero`, `aldousHit_le` **(proved)**: $\tau_0=0$, $\tau_k\le T$.
- `aldousHit_monotone`: $\eta>0\Rightarrow k\mapsto\tau_k(\omega)$ nondecreasing.
- `aldousHit_abs_sub_lt`: $\eta>0$, $\tau_k\le u<\tau_{k+1}\Rightarrow\lvert X_u-X_{\tau_k}\rvert<\eta$.
- `aldousHit_abs_sub_le`: same with $u\le\tau_{k+1}$ and $\le\eta$, for a continuous path.
- `aldousHit_hit`: continuous path, $\tau_{k+1}<T\Rightarrow\lvert X_{\tau_{k+1}}-X_{\tau_k}\rvert\ge\eta$ (genuine hit).
- `isStoppingTime_aldousHit`: all paths continuous, adapted $\Rightarrow$ every $\tau_k$ is a stopping time (any $\eta$).
- `aldousHit_exists_short_of_eq` (P1): $\tau_N=T$, $s,t\in[0,T]$, $\lvert t-s\rvert\le\delta$, $\lvert X_t-X_s\rvert\ge3\eta$ $\Rightarrow$ $\exists k<N$ genuine hit with $\tau_{k+1}-\tau_k\le\delta$.
- `aldousHit_card_short_of_lt` (P2): $\tau_N<T$, $\delta_1>0$ $\Rightarrow$ $\#\lbrace k<N:\tau_{k+1}-\tau_k\le\delta_1,\ \lvert X_{\tau_{k+1}}-X_{\tau_k}\rvert\ge\eta\rbrace\ge N-T/\delta_1$.
- `aldous_modulus` (file `Aldous.lean`): Aldous' criterion, continuous paths, two-scale form: $\mathbb P(\exists s,t\in[0,T],\ \lvert t-s\rvert\le\delta,\ \lvert X_t-X_s\rvert\ge3\eta)\le6a_1+3Na$ (for Q4).

## Dependencies

```
TestFunctions (H1) ─► FiniteMeasureEmbed (H2) ─► PathCompact (H4)
CompactSets (H3)                       (independent)
Martingales/Stopping (Stage 2) ─► AldousTrick (H5a) ──┐
                              └─► AldousPathwise (H5b) ┴─► Aldous (H5b)
```
Import graph: `TestFunctions ← TiltedField/Defs` (for `IsC13`); `FiniteMeasureEmbed ← TestFunctions`; `PathCompact ← FiniteMeasureEmbed`; `CompactSets ← Mathlib only`; `AldousTrick, AldousPathwise ← Martingales/Stopping`; `Aldous ← AldousTrick, AldousPathwise`. All seven files are imported from `QSSEPtoKPZ.lean`. H1–H5a and H5b can run in parallel; each may use the interfaces of the files it imports (still `sorry` or not). Uses by the QSSEP tasks: Q3 uses `measurable_pathFiniteMeasure_iff_tightEmb`, `bumpTest`; Q4 uses `isC13_bumpTestRaw`, `coe_bumpTest`, `isCompact_tightCoshBall`, `pathCptTest`, `isCompact_pathCptSet`, `isCompact_pathCptModulus`, `aldous_modulus`.

## Departures from `docs/stage3-design.md`

1. **Names** (requested by the main session to avoid clashes with T0', which may define the bump family in `Tightness/Defs.lean`): `tightBump → bumpBeta`, `tightTestRaw → bumpTestRaw`, `tightTest → bumpTest`, `measEmbed → tightEmb`, `FiniteMeasure.tendsto_of_forall_tightTest → tightEmb_tendsto_of_forall`, `isEmbedding_measEmbed → isEmbedding_tightEmb`, `borel_finiteMeasure_eq → borel_finiteMeasure_eq_iSup_tightEmb`, `isCompact_coshBall → isCompact_tightCoshBall` (with a definition `tightCoshBall`), `testPath → pathCptTest`, `modulusSet → pathCptModulus`, `isCompact_pathSet → isCompact_pathCptSet` (with a definition `pathCptSet`), `isCompact_modulusSet → isCompact_pathCptModulus`, `isC13_tightTest → isC13_bumpTestRaw`, `measurable_pathFiniteMeasure_iff → measurable_pathFiniteMeasure_iff_tightEmb`. If T0' defines the same objects, the main session should keep one copy.
2. **`isC13_bumpTestRaw`** is stronger than the design's: one constant $C\ge0$ valid on every horizon $T$ (the design had horizon $1$ only). Q2/Q4 can use any horizon.
3. **`bumpTest`** is built with `BoundedContinuousFunction.ofNormedAddCommGroup` (bound 1) and its proof obligations are proved, so the definition has no `sorry`.
4. **`aldous_modulus`** has two new hypotheses `0 ≤ a`, `0 ≤ a₁`. Without them the bound `ofReal (6 a₁ + 3 N a)` can be smaller than `ofReal (6 a₁) + N · ofReal (3 a)` (when `a < 0`), and the proof sketched in the design would not give it. In Q4 the bounds come from (5.2) and are nonnegative (replace `c` by `max c 0` if needed).
5. **File split**: H5a and H5b own disjoint files. The design put `aldous_trick` and `aldous_modulus` in the same `Martingales/Aldous.lean`; here `aldous_trick` is in `Martingales/AldousTrick.lean` (H5a), `aldous_modulus` in `Martingales/Aldous.lean` (H5b), and the hitting sequence with its pathwise lemmas in `Martingales/AldousPathwise.lean` (H5b).
6. **Added interfaces**: `measurable_finiteMeasure_iff_tightEmb`, `borel_pathFiniteMeasure_eq_iSup_tightEmb` (Stage 4 will want them), `bumpTestRaw_encode_succ`, `coe_bumpTest`, `pathCptTest_apply`, the hitting-sequence lemmas of H5b (the design described them in words only).
7. **Not written**: `Tightness/Version.lean` (`exists_tiltedPath_version`, Section 2.6 of the design, listed under I0' in the design's table) is not part of this task's brief (H1–H5b); it stays with Q3. It needs only `bumpTest` and `measurable_pathFiniteMeasure_iff_tightEmb` from these files.
