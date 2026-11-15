# Stage 5: interfaces of packages L, M and of the companions (task I0‴)

Written on 13 November 2026 by the T0‴+I0‴ agent (Opus 5.5). For the main session and the proving agents. The Lean files are the reference; this list gives, for each task of `docs/stage5-design.md` (Section 4), its files (under `QSSEPtoKPZ/`), its interface lemmas (meaning, Lean name) and what it may use. All interface lemmas are `sorry` unless marked **(proved)**. Sections 2–4 of `docs/stage5-design.md` are the specification; the departures are listed at the end. The statements (task T0‴) are described for the author in `docs/stage5-statements.md`.

Conventions (as in Stages 2–4): `module`, `@[expose] public section`, `noncomputable section`, namespace `QSSEPtoKPZ`. Processes `ℝ → Ω → _`, wave functions `ℝ → Ω → ℓ²(ℤ, ℂ)`, filtrations `Filtration ℝ≥0 mΩ` without the usual conditions; $\mathcal F^a$ = `nullAug μ 𝓕` (inside `namespace IsWaveFunction` write `QSSEPtoKPZ.nullAug`). Real Itô integrals `stochInt 𝓖 μ B h t ω` against the real Brownian family $B_{(x,j)}$; a complex coefficient $c$ of $dB_i$ is written through `(c i s ω).re`, `.im`. Binder scope: every `∑`, `∫`, `∫⁻`, `⨆` followed by other terms is parenthesized (checked with `set_option pp.parens true`).

`lake build` succeeds; the 25 new files have **64 `sorry`**: 4 statements of T0‴ (`main_theorem_lib`, `exists_isWaveFunction_lib`, `isWaveFunction_unique_lib`, `exists_isWhiteNoise_lib`; the other statements quote a twin or a copy) and **60 interfaces**; no warning other than `declaration uses 'sorry'`.

## Definitions (complete, no `sorry`)

| Name | File | Meaning | Owner |
|---|---|---|---|
| `tiltedMeasureBox L n ψ ω t`, `rwTail s L` | `FiniteSystems/Defs.lean` | $\mathsf Z^L_n(t)=\sum_{x\in\Lambda_L}\mathfrak z_n(t,x)\delta_{y_n(t,x)}$; $\mathsf P(\lvert X_s\rvert\ge L)=\sum_{\lvert x\rvert\ge L}p_s(x)$ | T0‴ |
| `IsWaveIto L 𝓖 B ψ0 ψ μ` | `FiniteSystems/WaveIto.lean` | Itô form of (1.7) on $\Lambda_L$ from $\psi_0$: adapted, continuous $\ell^2$ paths, support and $\psi_0$ for every $\omega$, $\operatorname{Re}/\operatorname{Im}\psi(x)$ Itô processes up to every $N$ with drift $-\frac{D_L(x,x)}2\psi(x)$, coefficients `waveDiffRe/Im` | L1 |
| `waveDiffC ψ x i s ω` | same | complex coefficient of $dB_i$ in $d\psi(x)$: $\tfrac{1}{\sqrt2}(\mathrm i\psi(x+1),-\psi(x+1),\mathrm i\psi(x-1),\psi(x-1))$ on $(x,0),(x,1),(x-1,0),(x-1,1)$ | L1 |
| `IsCItoProcessUpTo 𝓖 μ B τ Z a b` | `ItoIntegral/ComplexIto.lean` | real and imaginary parts of $Z$ are `IsItoProcessUpTo` with the parts of $a$, $b$ | G11b |
| `IsGoodWaveBox L 𝓕 B ψ ψ' μ` | `FiniteSystems/Identification.lean` | $L$-analogue of Stage 2's `IsGoodWave` (wave function for $\mathcal F^a$, continuous, supported, $e_0$ at $0$, for every $\omega$; indistinguishable from $\psi$) | L3 |
| `picardCoord 𝓖 μ B L ψ0 φ t ω x` | `FiniteSystems/PicardIter.lean` | Picard map coordinatewise: $\psi_0(x)+I_t(\texttt{waveDiffRe}\,\varphi\,x)+\mathrm iI_t(\texttt{waveDiffIm}\,\varphi\,x)-\frac{D_L(x,x)}2\int_0^t\varphi_s(x)ds$ on $\Lambda_L$, $0$ outside | L2a |
| `IsPicardAdmissible L 𝓖 ψ0 φ μ` | same | adapted, continuous, supported, $\varphi_0=\psi_0$ (every $\omega$), $\mathbb E\sup_{[0,T]}\lVert\varphi\rVert^2<\infty$ | L2a |
| `pairingBoundaryCoef L a ψ i s ω` | `FiniteSystems/PairingAlgebra.lean` | coefficients of $\bar a(L)\,\mathrm i\psi(L+1)dW^{(L)}+\bar a(-L)\,\mathrm i\psi(-L-1)d\overline W{}^{(-L-1)}$ on $B_{(L,\cdot)}$, $B_{(-L-1,\cdot)}$ (design: `boundaryCoef`) | L4 |
| `prop81Rhs n T ε L` | `FiniteSystems/Prop81.lean` | $\frac{16}{\varepsilon^2}nT(8+\frac{nT}2)e^{2\theta_nL-rL/3}+\frac{4e^{2T}}{\varepsilon\cosh\ell}$, $r=\min(1,\frac L{nT})$, $\ell=\frac{L-n^{3/4}T}{n^{1/2}}$ | L8 |
| `pathMetricDist γ γ'` | `Assembly/PathMetric.lean` | $\sup_{t\le T}\sum_j\min(2^{-j},\lvert\gamma(t)(f_j)-\gamma'(t)(f_j)\rvert)$, $f_j$ = `bumpTest j` (design: `pathDist`) | M1 |

## Statement files (T0‴; see `docs/stage5-statements.md`)

| File | Statements | Proof |
|---|---|---|
| `FiniteSystems/Statements.lean` | `prop_2_1_existence`, `lemma_8_2`, `prop_8_1` | quote the twins `picard_isWaveFunction` (L2b), `lemma82_bound` (L6), `prop81_tendsto` (L8); this file is never edited by the proving tasks |
| `FiniteSystems/Uniqueness.lean` | `isWaveFunction_unique_lib` (U1) | L5, in place |
| `FiniteSystems/Existence.lean` | `exists_isWaveFunction_lib` (E1), `IsMildSolution.nonneg_lib` (P, **proved** from E1 and Stage 4's `nonneg_of_isWaveFunction.{0}`) | E1b, in place |
| `WhiteNoise/Existence.lean` | `exists_isWhiteNoise_lib` (E2) | E2b, in place |
| `Assembly/MainTheorem.lean` | `main_theorem_lib` | M3, in place |
| `Assembly/Corollaries.lean` | `main_theorem_fixed_time_lib`, `IsMildSolution.integral_sheMeasure_lib` (D10‴) | **proved** (proofs of `Corollaries.lean` with the `_lib` copies) |

## Generic Itô calculus

### G11a — `ItoIntegral/ContIntegrable.lean` (uses: Stage 2 `ItoIntegral/Integrands`, `Basic`)
- `isItoIntegrable_of_continuous`: $h_i$ adapted, paths continuous on $[0,\infty)$ for every $\omega$, $\sum_ih_i(s)^2$ convergent and continuous in $s\ge0$, $\mathbb E\int_0^T\sum_ih_i^2<\infty$ for all $T$ $\Rightarrow$ `IsItoIntegrable`. (Truncate $h\min(1,K/\lVert h\rVert)$, `isItoIntegrable_of_leftContinuous`, dominated convergence, `IsItoIntegrable.of_tendsto`; joint measurability from progressive measurability.)
- `lintegral_tsum_iSup_stochInt_sq_le`: $\mathbb E\sum_k\sup_{t\le T}I_t(h^k)^2\le4\sum_k\mathbb E\int_0^T\sum_i(h^k_i)^2$ (a.e.-measurability of each supremum, `lintegral_tsum`, Doob).

### G11b — `ItoIntegral/ComplexIto.lean` (uses: Stage 2 `ItoIntegral/Product`)
- `IsCItoProcessUpTo.conj_mul`: product rule for $\bar ZW$, $d(\bar ZW)=(\bar Zc+W\bar a+\sum_i\bar b_id_i)ds+\sum_i(\bar Zd_i+W\bar b_i)dB_i$; hypotheses as `IsItoProcessUpTo.mul` (bounded stopping time, continuity and adaptedness of $Z,W$, bounds $\le K$ on $[0,\tau]$) plus square-summability of $b$, $d$ at every $(s,\omega)$ (needed to split complex `tsum`s into real and imaginary parts). Four applications of `.mul`, then `.add`.
- `IsCItoProcessUpTo.add`, `.const_mul` ($k\in\mathbb C$), `.finset_sum`.

## Package L (finite systems)

### L1 — `FiniteSystems/WaveIto.lean` (uses: Stage 2 `WaveFunction/Identification`, `Good`, `ItoIntegral/Riemann`)
- `IsBrownianFamily.isProbabilityMeasure` **(proved)**; `waveDiffC_re`, `waveDiffC_im` **(proved)**; `waveDiffC_eq` (values).
- `waveDiffRe_sub`, `waveDiffIm_sub` (linearity in $\psi$, for U1).
- `measurable_norm_of_adapted`, `isStoppingTime_waveStop_of_continuous` ($\tau_R\wedge N$ is a stopping time for any adapted process with continuous $\ell^2$ paths; `isStoppingTime_hitTime`).
- `IsWaveIto.isWaveFunction` (every $L$; initial value $e_0$). **Note:** `tendsto_riemann_stochInt` needs bounded integrands, and an Itô solution is not known to be bounded here (norm conservation is L4's, and for $L=\infty$ it is a property of wave functions): localize at $\tau_R\wedge N$ (on $\lbrace\sup_{s\le t}\lVert\psi_s\rVert<R\rbrace$ the stopped and unstopped Riemann sums coincide; its probability tends to $1$ by path continuity).

### L2a — `FiniteSystems/PicardIter.lean` (uses: L1, G11a)
- `IsPicardAdmissible.isItoIntegrable_re/im` (G11a; energy $\le T\,\mathbb E\sup\lVert\varphi\rVert^2$).
- `picard_step_exists`: for $\mathcal F^a$, an admissible $\varphi$ has an admissible Picard image, equal a.s. (all $t,x$) to `picardCoord` (build $\langle c,\cdot\rangle\in\ell^2$ on the event where $\sum_x\sup_{t\le N}\lvert c_x\rvert^2<\infty$ for all $N$ and the coordinates are continuous; $\psi_0$ on a measurable null set containing the complement, as in `IsWaveFunction.exists_good`).
- `picard_step_bound`: $\mathbb E\sup_{s\le t}\lVert\varphi_1'-\varphi_2'\rVert^2\le(16+2T)\int_0^t\mathbb E\sup_{u\le s}\lVert\varphi_1-\varphi_2\rVert^2ds$, $0\le t\le T$ (`lintegral_tsum_iSup_stochInt_sq_le`, `waveDiffRe_sub`, `tsum_waveDiffRe_sq`, Cauchy–Schwarz, $D_L\le2$).
- `picard_iterates`: the admissible sequence $\varphi^{(0)}=\psi_0$, $\varphi^{(m+1)}=\Phi(\varphi^{(m)})$ a.s.

### L2b — `FiniteSystems/Picard.lean` (uses: L2a, L1)
- `exists_isWaveIto`: Itô solution for $\mathcal F^a$ from any $\psi_0\in\ell^2$ supported in $\Lambda_L$, with $\mathbb E\sup_{[0,T]}\lVert\psi\rVert^2<\infty$ (iterated `picard_step_bound` $\Rightarrow\sum_m(\mathbb E\sup\lVert\varphi^{(m+1)}-\varphi^{(m)}\rVert^2)^{1/2}<\infty$; a.s. uniform limit; null-set modification; `tendsto_lintegral_iSup_stochInt_sub` for the equation).
- `picard_isWaveFunction` (twin of `prop_2_1_existence`): `exists_isWaveIto` with `waveInit`, `IsWaveIto.isWaveFunction`, `IsBrownianFamily.isProbabilityMeasure`.

### L3 — `FiniteSystems/Identification.lean` (uses: L1, Stage 2 D1; copy-adapt `WaveFunction/Good.lean`, `Identification.lean`, D9‴)
- `IsWaveFunction.ae_init_box` ($\psi_0=e_0$ a.s., every $L$), `IsWaveFunction.exists_isGoodWaveBox`, `IsGoodWaveBox.isStoppingTime_waveStop`.
- `IsGoodWaveBox.isItoProcessUpTo_re/im`: for $x\in\Lambda_L$, Itô up to $\tau_R\wedge N$ for $\mathcal F^a$, drift $-\frac{D_L(x,x)}2\psi'(x)$, coefficients `waveDiffRe/Im ψ' x` (`isItoProcessUpTo_of_riemann`; at $x=\pm L$ the outer neighbour vanishes by `support`).

### L4 — `FiniteSystems/PairingAlgebra.lean`, `Pairing.lean`, `Frame.lean` (uses: G11b, L1, L3, Stage 2 `UnitNorm`)
- PairingAlgebra (pointwise at $(s,\omega)$, sums over `Finset.Icc (-L) L`): `pairing_coef_sum_box` ($a,b$ supported in $\Lambda_L$: $\sum_x(\bar a(x)c^b_{x,i}+b(x)\bar c^a_{x,i})=0$), `pairing_drift_sum_box` (drift $\sum_x(\bar a(x)(-\frac{D_L}2b(x))+b(x)\overline{(-\frac{D_L}2a(x))}+\sum_i\bar c^a_{x,i}c^b_{x,i})=0$), `pairing_coef_sum_restrict` (= `pairingBoundaryCoef`), `pairing_drift_sum_restrict` ($L\ge1$; $=-\frac12(\bar a(L)\psi(L)+\bar a(-L)\psi(-L))$, the drift of $\psi$ being $-\frac{D_\infty}2\psi$). Do one `ring` identity per bond, then sum; $D_L(y)=\#\lbrace x\in\Lambda_L:\lvert x-y\rvert=1\rbrace$ from the definition of `degree`.
- Pairing: `IsWaveIto.isCItoProcessUpTo`; `IsWaveIto.inner_eq` (finite $L$; localize with `isStoppingTime_waveStop_of_continuous` and `IsItoProcessUpTo.mono`, then $R\to\infty$); `IsWaveIto.inner_restrict_eq` ($L\ge1$, norms $\le1$ for every $\omega,t$; Itô-integrability of the boundary coefficients and the Duhamel identity).
- Frame: `IsWaveIto.norm_eq`; `IsWaveIto.exists_unitVersion` (finite $L$, $\mathcal F^a$, $\lVert\psi_0\rVert=1$); `IsWaveFunction.exists_unitIto` (every $L$: Stage 2's `exists_isUnitWave`, `isItoProcessUpTo_re/im`, `waveDegree_top` for $L=\infty$; L3 and norm conservation up to $\tau_R$, so $\tau_2\wedge N=N$, for finite $L$); `IsWaveIto.frame_orthonormal`; `frame_parseval` (deterministic).

### L5 — `FiniteSystems/Uniqueness.lean` (statement file; uses: L4 `exists_unitIto`, L1 `waveDiffRe_sub`, `lintegral_stochInt_sq`, `volterra_ae_eq_zero`)
- prove `isWaveFunction_unique_lib` in place ($F(t)=\mathbb E\lVert\hat\psi_t-\hat\psi'_t\rVert^2\le(4+2T)\int_0^tF$, then Volterra with $(t-s)^{-1/2}\ge T^{-1/2}$; continuity).

### L6 — `FiniteSystems/Lemma82.lean` (uses: L2b `exists_isWaveIto`, L4, L7, `prop_2_2`, G11a)
- `lemma82_bound` (twin of `lemma_8_2`). Columns: `exists_isWaveIto` with `lp.single 2 y 1`, then `exists_unitVersion`; given $\psi,\psi^L$ replaced by `exists_unitIto` versions; all for $\mathcal F^a$ (`IsBrownianFamily.nullAug`). Summability and integrability conjuncts: `summable_rwTail`, `intervalIntegrable_rwTail`.

### L7 — `FiniteSystems/RandomWalkTail.lean`, `FiniteSystems/AtomicTV.lean` (uses: Stage 2 `prop_2_2`, `lemma_2_3_linear`; Mathlib total variation)
- RandomWalkTail (hypotheses: a realization `hB`, `hψ` of the wave function on $\mathbb Z$): `rwKernel_nonneg`, `hasSum_rwKernel`, `hasSum_exp_mul_rwKernel` ($\sum_xe^{rx}p_s(x)=e^{2s(\cosh r-1)}$), `summable_rwTail`, `rwTail_nonneg`, `intervalIntegrable_rwTail`, `rwTail_le` (Chernoff), `cosh_sub_one_le` (deterministic).
- AtomicTV: `etvDist_sum_dirac_le`, `abs_integral_sum_dirac_sub_le` (real summable weights through `ENNReal.ofReal`), `tiltedMeasureBox_eq_sum` (sum over $\mathbb Z$ with the indicator of $\Lambda_L$), `tiltedMeasureBox_top`.

### L8 — `FiniteSystems/Prop81.lean` (uses: L6, L7, `lemma_5_2`)
- `prop81_bound` ($n\ge1$, $L\ge1$, $T,\varepsilon>0$, $n^{3/4}T<L$: $\mathbb P^\ast(\sup_{t\le T}\sum_x\lvert\mathfrak z^L_n-\mathfrak z_n\rvert>\varepsilon)\le$ `prop81Rhs n T ε L`), `prop81Rhs_tendsto` (integer $L_k$), `prop81Rhs_tendsto_enat` ($L_k\in\mathbb N\cup\lbrace\infty\rbrace$, hypothesis of `main_theorem`; for M3), `prop81_tendsto` (twin of `prop_8_1`; `etvDist_sum_dirac_le` + `tiltedMeasureBox_eq_sum`, a.s. summability from `lemma_5_2`, a.s. support of $\psi^L$).

## Companions E2, E1

### E2a — `WhiteNoise/Isonormal.lean` (uses: Mathlib)
- `exists_isonormal` (design 3.6, unchanged).

### E2b — `WhiteNoise/Existence.lean` (statement file; uses: E2a)
- prove `exists_isWhiteNoise_lib` in place ($H=L^2(\mathbb R^2)$, `indicatorConstLp`, rectangle masses, Gaussian-process independence; filtration generated by $S$).

### E1a — `FiniteSystems/BrownianFamily.lean` (uses: E2b, G9 `walshProc_exists_cont_rect`)
- `exists_isBrownianFamily` (continuous versions glued over $[0,N]$, filtration `nullAug ν 𝓖`).

### E1b — `FiniteSystems/Existence.lean` (statement file; uses: E1a, `prop_2_1_existence`, `IsBrownianFamily.nullAug`)
- prove `exists_isWaveFunction_lib` in place. `IsMildSolution.nonneg_lib` is already proved from it.

## Package M (assembly)

### M1 — `Assembly/PathMetric.lean`, `Assembly/Slutsky.lean` (uses: Stage 3 `FiniteMeasureEmbed`)
- `pathMetricDist_le_of_close` (needs $\lVert f_j\rVert_\infty\le1$, `abs_bumpTestRaw_le`).
- `tendstoInDistribution_of_close` (design 3.5, unchanged except parentheses): internal pseudo-metric structure from `pathMetricDist` (`replaceTopology`, `isEmbedding_tightEmb`, `ContinuousMap.isEmbedding_postcomp`; risk R4), bounded Lipschitz test functions, outer probabilities.

### M2 — `Assembly/BoxVersion.lean` (uses: L7 AtomicTV, Stage 2 `rescaledMeasure_eq`, Stage 3)
- `rescaledMeasure_eq_box` (every $L$), `exists_rescaledPath_version_box` (finite $L$; `exists_good` gives $m_\Omega$-measurable continuous paths; `measurable_pathFiniteMeasure_iff_tightEmb`), `abs_integral_rescaledMeasure_box_sub_le` (hypotheses: $\sum_x\mathfrak z_n(t,x)$ summable, $\psi^L_{nt/2}$ supported in $\Lambda_L$).

### M3 — `Assembly/MainTheorem.lean` (statement file; uses: M1, M2, `prop_2_1_existence`, `prop81_bound`, `prop81Rhs_tendsto_enat`, `main_theorem_top`, `varrhoN_bounds`, `lemma_5_2`)
- prove `main_theorem_lib` in place (design, note on M3).

## Import graph

```
ItoIntegral/Integrands, Basic ─► ContIntegrable (G11a)
ItoIntegral/Product ─► ComplexIto (G11b)
FiniteSystems/Defs (T0‴) ◄─ TiltedField/Defs, WaveFunction/Kernel
WaveFunction/Identification, Good ─► WaveIto (L1) ─┬─► Identification (L3)
                                                    ├─► PicardIter (L2a, + G11a) ─► Picard (L2b)
                                                    ├─► PairingAlgebra (L4) ─► Pairing (L4, + L3, G11b) ─► Frame (L4, + UnitNorm)
                                                    └─► RandomWalkTail (L7, + Defs, EquationP, Linear)
Defs ─► AtomicTV (L7)
Frame, ContIntegrable, Volterra ─► Uniqueness (T0‴/L5)
Frame, Picard, RandomWalkTail ─► Lemma82 (L6) ─► Prop81 (L8, + AtomicTV, ExpMoments)
Defs, Picard, Lemma82, Prop81 ─► Statements (T0‴)
Isonormal (E2a) ─► WhiteNoise/Existence (T0‴/E2b) ─► BrownianFamily (E1a, + WalshBrownian)
BrownianFamily, Statements, Theorem12 ─► FiniteSystems/Existence (T0‴/E1b)
FiniteMeasureEmbed ─► PathMetric (M1) ─► Slutsky (M1)
AtomicTV, TiltedField/Identities, FiniteMeasureEmbed ─► BoxVersion (M2)
Slutsky, BoxVersion, Statements, Theorem12 ─► Assembly/MainTheorem (T0‴/M3)
Assembly/MainTheorem, FiniteSystems/Existence, Checks ─► Assembly/Corollaries
```
No new file imports `MainTheorem.lean`, `Companions.lean` or `Corollaries.lean` (so that `Solution.lean` can import the library and restate the eight theorems, D7‴). All new files are imported by `QSSEPtoKPZ.lean`. Waves as in the design (Section 4); each task may use the interfaces of the files it imports as black boxes.

## Departures from `docs/stage5-design.md`

1. **Files.** The definitions `tiltedMeasureBox`, `rwTail` are in a separate `FiniteSystems/Defs.lean` (the design put them in `Statements.lean`, which would create a cycle: L7 and L8 need them, and `Statements.lean` imports L8's file to quote the twin). The U1 copy is in L5's file `FiniteSystems/Uniqueness.lean` (statement file proved in place), not in `Existence.lean`.
2. **Twins.** `prop_2_1_existence`, `lemma_8_2`, `prop_8_1` are proved in `Statements.lean` by quoting `picard_isWaveFunction`, `lemma82_bound`, `prop81_tendsto` (identical statements, checked: `Expr` equality and `pp.all`), so that `Statements.lean` is written once and is not touched by L2b, L6, L8 (pattern of Stage 4's `eq_7_4`).
3. **`lemma_8_2`, first conjunct:** `∀ s, 0 ≤ s → Summable …` instead of `∀ s, Summable …`. For $s<0$, `rwKernel s` ($=e^{s\Delta}\delta_0$) is not a probability and has no meaning in the lemma (the series still converges, by a Bessel-function bound, but proving it would need a deterministic study of `rwKernel` that nothing else uses).
4. **Names** (distinctive prefixes, rule 7): `boundaryCoef` → `pairingBoundaryCoef`, `pathDist` → `pathMetricDist`.
5. **L7** lemmas `rwKernel_nonneg`, `hasSum_rwKernel`, `summable_rwTail`, `rwTail_nonneg`, `intervalIntegrable_rwTail`, `rwTail_le` take a realization of the wave function on $\mathbb Z$ as hypotheses (as the design did for the exponential moment): with it, $p_s=\mathbb EP(s,\cdot)$ makes them short; every user (L6, L8) has one.
6. **L8**: the right side of `prop81_bound` is the definition `prop81Rhs`; `prop81Rhs_tendsto` (integer sizes) and `prop81Rhs_tendsto_enat` (sizes in $\mathbb N\cup\lbrace\infty\rbrace$, for M3) make the design's `prop81_bound_tendsto` precise.
7. **Signatures fixed here** for the interfaces the design described in words: L1 (`waveDiffC`, `waveDiffRe_sub`, `measurable_norm_of_adapted`, `isStoppingTime_waveStop_of_continuous`), L2a (`picardCoord`, `IsPicardAdmissible`, `picard_step_exists`, `picard_step_bound`, `picard_iterates`), L3 (`IsGoodWaveBox` and its lemmas, `ae_init_box`), L4 (the four algebra lemmas, `isCItoProcessUpTo`, `norm_eq`, `exists_unitVersion`, `frame_orthonormal`, `frame_parseval`), L7, M1 (`pathMetricDist_le_of_close`), M2 (`rescaledMeasure_eq_box`, `abs_integral_rescaledMeasure_box_sub_le`), G11a, G11b (`IsCItoProcessUpTo` and its four lemmas).
8. **D10‴ done here:** `Assembly/Corollaries.lean` with `main_theorem_fixed_time_lib`, `IsMildSolution.integral_sheMeasure_lib`, proved by the proofs of `Corollaries.lean` (no task needed; they become `sorry`-free with M3 and E1b).
9. **`docs/frozen-stage5.txt`** lists the T0‴ statements; its reference commit is to be filled in by the main session at the merge (as for Stage 4). `scripts/task_merge.sh` (`FROZEN_RE`) does not yet protect the Stage 5 statement files (`FiniteSystems/Defs.lean`, `Statements.lean`): the main session may add them.
10. Parentheses added around `⨆` inside `∫⁻ ω, (⨆ …) ∂μ` in moment statements (no change of meaning; checked with `pp.parens`).
