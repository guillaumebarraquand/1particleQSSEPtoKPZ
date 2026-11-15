# Stage 5: independent audit of the statements (task A‴)

Written on 13 November 2026 by an independent audit agent (Opus 5.5), on branch `work-s5audit` (base `3ea3611`, Stage 5 statements frozen at `afb1d44`). **Nothing was proved and no `.lean` file of the library was changed.** Scratch tests were run with `lake env lean` against the built library (scratch folder of the session, `s5audit/`); they are reproduced in the appendix.

Scope: the Stage 5 statement files of `docs/frozen-stage5.txt` (`FiniteSystems/{Defs,Statements,Uniqueness,Existence}.lean`, `WhiteNoise/Existence.lean`, `Assembly/{MainTheorem,Corollaries}.lean`), the 60 interface lemmas and 10 definitions of `docs/stage5-interfaces.md` (25 new files), the sheet `docs/stage5-statements.md`, the design `docs/stage5-design.md`, against the article (SHA-256 `3547cb86…`, 1713 lines, unchanged: checked), Sections 2.1 and 8, and the frozen `Definitions.lean`, `MainTheorem.lean`, `Companions.lean`.

**Summary: 0 ERROR, 1 WEAKNESS, 8 REMARKS.** I found no false statement, no misparse and no statement weaker than the article (beyond the listed deviations). The copies `main_theorem_lib`, E1, U1, E2, P, W, U3 and the two corollaries are identical to the frozen statements (`Expr` equality, and the kernel accepts each one as a proof of the other, in both directions). Every interface on the planned route was re-derived on paper and found true, including the four that the task named (`prop81_bound`, `tendstoInDistribution_of_close`, `IsWaveIto.isWaveFunction`, `IsCItoProcessUpTo.conj_mul`). The pointwise algebra (the pairing identities and the real/imaginary decomposition of `conj_mul`) was also checked numerically. The one WEAKNESS is a missing helper lemma on the route of task L4 (a congruence for coefficients that agree only at times $s>0$). It will cost some work but will not block the route.

## ERROR

None.

## WEAKNESS

### W1. The pairing identities hold only for $s\ge0$, but the library's congruence lemma asks for all $s\le N$

*Where.* `FiniteSystems/WaveIto.lean:52` (`IsWaveIto.support`, quantified over `t : ℝ≥0`); `FiniteSystems/PairingAlgebra.lean:56–94` (the four identities take the support of `a s ω`, `b s ω` as a hypothesis at the given real `s`); `WaveFunction/ItoLimit.lean:40` (`IsItoProcessUpTo.congr_const`, the only congruence lemma for Itô processes, asks for `b' i s ω = b i s ω` for **all** `s ≤ N`, negative `s` included); the route of L4 in `docs/stage5-interfaces.md` (`IsWaveIto.inner_eq`, `inner_restrict_eq`, and `IsWaveFunction.exists_unitIto` for finite $L$ through norm conservation).

*What is wrong.* `IsCItoProcessUpTo.conj_mul` followed by `finset_sum` produces, for $\sum_{x\in\Lambda_L}\overline{a(x)}b(x)$, the diffusion family
$$\textstyle s\mapsto\sum_{x\in\Lambda_L}\big(\overline{a_s(x)}c^b_{x,i}(s)+b_s(x)\overline{c^a_{x,i}(s)}\big)$$
and the corresponding drift. `pairing_coef_sum_box` / `_restrict` and `pairing_drift_sum_*` identify these with $0$, `pairingBoundaryCoef`, or the boundary drift. But they need $a_s,b_s$ supported in $\Lambda_L$, and `IsWaveIto` (like `IsPicardAdmissible` and `IsGoodWaveBox`) says nothing about the paths at times $s<0$. So the two families are equal only for $s\ge0$, and `congr_const` does not apply.

The statements stay true. `IsItoIntegrable` sees $h$ only on $(0,\infty)$ (field `meas` uses `if 0 < p.1`, and `energy` integrates over `Ioc 0 T`), so the result follows from `IsItoIntegrable.congr` and `stochInt_congr` (`ItoIntegral/Basic.lean:535, 551`). But no interface states this step, and each of the three L4 proofs will have to redo it.

*Fix.* Add to task G11b (`ItoIntegral/ComplexIto.lean`, or `ItoIntegral/Product.lean` for the real part) one interface:
```lean
theorem IsItoProcessUpTo.congr_pos (hB : IsBrownianFamily 𝓖 B μ) {τ : Ω → ℝ≥0}
    {X X' a a' : ℝ → Ω → ℝ} {b b' : ι → ℝ → Ω → ℝ} (h : IsItoProcessUpTo 𝓖 μ B τ X a b)
    (hX : ∀ ω (t : ℝ), 0 ≤ t → X' t ω = X t ω)
    (ha : ∀ ω (s : ℝ), 0 ≤ s → s ≤ τ ω → a' s ω = a s ω)
    (hb : ∀ i (s : ℝ) ω, 0 < s → s ≤ τ ω → b' i s ω = b i s ω) :
    IsItoProcessUpTo 𝓖 μ B τ X' a' b'
```
Add the same for `IsCItoProcessUpTo`. The `meas` field is literally the same function (the integrand is cut at `0 < s` and at `s ≤ τ`), the energy of the difference is $0$, and `stochInt_congr` gives the equation: about 30 lines. Alternatively, the L4 agent can apply `stochInt_congr` directly against the zero family, but the helper avoids doing it three times.

## REMARKS

### R1. `prop_2_1_existence` goes beyond the article in one direction and leaves out the moment bound (2.2)

`FiniteSystems/Statements.lean:47`. The statement allows $L=0$ (the article has $L\in\mathbb Z_{\ge1}\cup\lbrace\infty\rbrace$). This is harmless: $\Lambda_0=\lbrace0\rbrace$, `degree 0 0 = 0` (checked, appendix) and $\psi\equiv e_0$. The moment bound (2.2), the "Moreover" of Proposition 2.1, is not part of it. It is Stage 2's `moment_bound`, proved for every wave function on $\mathbb Z$. The sheet calls the statement "the existence half of Proposition 2.1"; it could add these two points. On the augmented filtration (deviation 3): if $\mathcal F_0$ contains the $\mu$-null sets of $m_\Omega$, then `nullAug μ 𝓕 = 𝓕`, so under the article's usual conditions this is exactly its statement. The sheet could say so in one line.

### R2. Redundant hypotheses `[IsProbabilityMeasure μ]`

`lemma_8_2` (`Statements.lean:58`) and `prop_8_1` (line 77, `[∀ k, IsProbabilityMeasure (μ k)]`) state it, although it follows from `IsBrownianFamily` (`IsBrownianFamily.isProbabilityMeasure`, proved, `WaveIto.lean:88`). It is harmless and consistent with the frozen `main_theorem`, so there is nothing to change. It is listed only because U1 deliberately omits it.

### R3. `prop81_bound` uses an unconditional `tsum`

`FiniteSystems/Prop81.lean:58`. The event is $\lbrace\varepsilon<\sup_t\sum'_x\lvert\mathfrak z^L_n-\mathfrak z_n\rvert\rbrace$. Where $x\mapsto\mathfrak z_n(t,x)$ is not summable, `tsum` is $0$, so the event is smaller there and the bound easier. This happens on a null set only (Lemma 5.2 (1) with $b=0$), so the statement is still the article's bound. The users (`prop81_tendsto`, M3) must supply the almost sure summability themselves, and the interface notes already plan this. Checked: the constant `prop81Rhs` is exactly (8.3) + Chebyshev at level $\varepsilon/2$: $\frac4{\varepsilon^2}e^{2\theta_nL}\cdot4(8+\frac{nT}2)\cdot\frac{nT}2\cdot2e^{-rL/3}$, plus Lemma 5.2 (3) with $K=\frac\varepsilon2\cosh\ell$, which gives $\frac{2e^{2T}}{K}=\frac{4e^{2T}}{\varepsilon\cosh\ell}$. The parse was checked by kernel `rfl` (appendix).

### R4. The sheet states `tiltedMeasureBox ⊤ = tiltedMeasure` as a fact

`docs/stage5-statements.md`, "Definitions". In Lean this is the interface `tiltedMeasureBox_top` (`AtomicTV.lean:64`, `sorry`). It is true (`box ⊤ = univ`, reindexing of `Measure.sum`), but the sheet should say "(interface, to be proved)".

### R5. E1a: the continuous version of G9 is not stated to be measurable

`WhiteNoise/WalshBrownian.lean:128` gives $W$ with continuous paths and $W_u=\xi((0,u]\times(a,b])$ a.s. for each $u$, but not that $W_u$ is measurable. `IsBrownianFamily.adapted` needs `Measurable[nullAug ν 𝓖 t]`, and `nullAug` adds only the measurable null sets, not their subsets. So E1a must redefine $B$ as $0$ on a measurable null set $N$ that contains the rational-time exceptions. Off $N$, $W_u$ is then a limit of rational-time rectangle masses, hence measurable for $\mathcal G_t\vee\mathcal N$. This is a planning note: `exists_isBrownianFamily` itself is true.

### R6. `lintegral_tsum_iSup_stochInt_sq_le` needs almost everywhere measurability of each supremum

`ItoIntegral/ContIntegrable.lean:54`. The lower integral is only superadditive, so pushing $\int^-$ through $\sum'_k$ needs each $\sup_{t\le T}I_t(h^k)^2$ to be a.e.-measurable. This holds by `stochInt_continuous` (`ItoIntegral/Basic.lean:179`). The statement is true; the note is for task G11a.

### R7. Slutsky: the metric must give exactly the instance topology

`Assembly/Slutsky.lean:36`. The statement is true: $\mathrm{pathMetricDist}\le\sum_j\min(2^{-j},\varepsilon)\to0$ under the closeness hypothesis, `isEmbedding_tightEmb` is proved for all of `FiniteMeasure ℝ`, and the uniform metric of a compatible metric induces the compact-open topology on $C([0,T],\cdot)$. Mathlib's `tendsto_iff_forall_lipschitz_integral_tendsto` (`Portmanteau.lean:686`) needs `[PseudoEMetricSpace E] [OpensMeasurableSpace E]` with the topology of `ProbabilityMeasure E` unchanged, so the local instance must be built with `PseudoMetricSpace.replaceTopology` (risk R4 of the design). Outer probabilities are handled by a measurable superset of equal measure, since $X_k$ and $Y_k$ are a.e.-measurable. Nothing to change.

### R8. `isItoIntegrable_of_continuous` has stronger hypotheses than needed

`ContIntegrable.lean:42`: summability for all real $s$ (negative included), and continuity for every $\omega$ of each $h_i$ and of $\sum_ih_i^2$. Progressive measurability and finite energy would suffice. Every planned use has finitely supported families (four nonzero coefficients per site, or the four boundary coefficients), so the hypotheses are met. No change needed.

## What was checked, and how

| Check | Result |
|---|---|
| Copies vs frozen (`main_theorem`, E1, U1, E2, P, W×2, U3, `main_theorem_fixed_time`, `integral_sheMeasure`): `Expr` equality of the types after aligning universe names, `isDefEq`, and kernel `example : type_of% @frozen.{u,v} := @copy.{u,v}` in **both** directions | all 10 equal (same universe parameters), 14 kernel checks pass |
| `sorry` dependencies (traversal of the constants used) | `nonneg_lib`, `integral_sheMeasure_lib`: only `exists_isWaveFunction_lib`; `main_theorem_fixed_time_lib`: only `main_theorem_lib`; `prop_2_1_existence`, `lemma_8_2`, `prop_8_1`: only their twin. `main_theorem_top`, `nonneg_of_isWaveFunction`, `ae_eq_lib`, `isometry_lib`, `isMildSolution_unique_lib`: axioms `propext, Classical.choice, Quot.sound` |
| Binder scope: every declaration of the 25 new files printed with `pp.parens`, `pp.funBinderTypes`, definitions with their bodies (107 declarations) | no misparse; every `∑`, `∑'`, `∫`, `∫⁻`, `⨆` has the intended scope; `-L` elaborates to `-(↑L : ℤ)`; `Measurable[𝓖 t]` checked with `pp.explicit` |
| Frozen files untouched (`git diff 41150ef 3ea3611`), `make_challenge.py --check` | only additions and `QSSEPtoKPZ.lean`, `task_merge.sh`; Challenge up to date |
| Definitions referenced by the Stage 5 statements are frozen | `zN`, `tiltedMeasure`, `rwKernel`, `lapOp`, `delta0`, `nullAug`, `nullSets` (Stage 2 list); `thetaN`, `lambdaN` (frozen file `Constants.lean`); `BddZ` (frozen file `Generator.lean`); `density`, `box`, `degree`, `rescaledPosition` (`Definitions.lean`) |
| `sorry` count of the 25 new files | 64, as stated |
| Pairing algebra (`pairing_coef_sum_box/restrict`, `pairing_drift_sum_box/restrict`) and the real/imaginary decomposition of `conj_mul` (drift and coefficients), numerically with random complex vectors, $L=0,1,2,3,5$ | residual $<3\cdot10^{-15}$; for $L=0$ the restricted drift is $-\bar a(0)\psi(0)$, which is why `hL : 1 ≤ L` is needed |
| Kernel probes: `degree ⊤ x = 2`, `degree 1 1 = 1`, `degree 0 0 = 0`, `itoSum f W 0 m ω = 0`, `rwTail s 0 = ∑' p_s`, the parse of `prop81Rhs` | all pass |
| Mathlib `etvDist` | $=\lvert\mu-\nu\rvert(\text{univ})$ for finite measures, $\infty$ otherwise: the article's $\lVert\cdot\rVert_{TV}$ |

### Faithfulness (statements against the article)

* **`lemma_8_2`** (8.1). The hypotheses are those of the article, with $\psi^L$ any wave function on $\Lambda_L$ instead of $U_te_0$ (stronger). The conclusion is the article's inequality, plus three genuineness conjuncts. The integrand of `rwTail` is $\mathsf P(\lvert X_s\rvert\ge L)$ for the walk with rate 1 to each neighbour, consistent with `hasSum_exp_mul_rwKernel` ($\mathsf Ee^{rX_s}=e^{2s(\cosh r-1)}$). The constant was re-derived along the planned route: columns, Parseval, Doob per $y$ with $\sum_y\lvert u^y(\pm L)\rvert^2=1$ (rows), giving $4\int\mathbb E[P(L+1)+P(-L-1)]$; Cauchy–Schwarz, giving $\frac S2\int\mathbb E[P(L)+P(-L)]$; and $(a+b)^2\le2a^2+2b^2$. This gives $(8+S)$, and the factor 4 comes from $\sum_{\Lambda_L}\lvert\Delta P\rvert\le2\lVert\delta\rVert$.
* **`prop_8_1`**. Sequences $n_k$, integer $L_k\ge1$, $L_k/n_k^{3/4}\to\infty$, and the outer probability of $\lbrace\varepsilon<\sup_t\lVert\cdot\rVert_{TV}\rbrace$ tends to $0$; `etvDist` $=\infty$ for infinite measures makes it stronger. It is faithful.
* **`main_theorem_lib`** and the companions are word for word (above). The sheet describes each statement correctly; deviations 1–7 are complete. The only additions are R1 (L = 0, (2.2)) and R4.

### Interfaces on the route (each re-derived; all true as stated)

* **L1.** `waveDiffC_eq` (from `waveDiffRe/Im`, branch by branch); `IsWaveIto.isWaveFunction`: the complex Riemann sum is the sum of the four real ones with coefficients `waveDiffC`. Localize with $f(s)\mathbf 1_{s\le\tau_R}$, which is bounded and left-continuous, so `tendsto_riemann_stochInt_finset` and `stochInt_indicator_stoppingTime` apply. At $t=0$ everything vanishes, which matches `init = waveInit`.
* **L2a/L2b.** The constant $16+2T$ of `picard_step_bound`: $2\cdot4\cdot\sum_{x,i}\lvert\sigma_{x,i}\rvert^2\le2\cdot4\cdot2\lVert\delta\rVert^2$, plus $2\cdot T$ from Cauchy–Schwarz with $D_L/2\le1$. Admissibility gives energy $\le T\,\mathbb E\sup\lVert\varphi\rVert^2<\infty$.
* **L3.** `ae_init_box` needs no Brownian hypothesis: at $t=0$ the Riemann sums are $0$, so the in-measure limit is $0$ a.s.
* **L4.** Pairing algebra (numerical check above). `inner_restrict_eq` gives the article's $d\Upsilon$ coordinatewise, with signs checked against $dW^{(L)}=(dB_{L,0}+\mathrm i\,dB_{L,1})/\sqrt2$ and $d\overline W{}^{(-L-1)}$. For `exists_unitIto` with finite $L$ there is no circularity: norm conservation is proved up to $\tau_R\wedge N$ with `conj_mul`, before `IsWaveIto` is available (see W1 for the congruence step).
* **L5 (U1).** $F(t)\le(4+2T)\int_0^tF$ and `volterra_ae_eq_zero` with $(t-s)^{-1/2}\ge T^{-1/2}$.
* **L7/L8.** Chernoff with $2s(\cosh r-1)\le\frac23nTr^2\le\frac23rL$ for $s\le nT/2$; $\cosh r-1\le\frac23r^2$ on $[0,1]$. For `prop81Rhs_tendsto(_enat)`: $r/\theta=\min(n^{1/4},Ln^{-3/4}/T)\to\infty$ and $rL\ge\min(n^{3/4},n^{1/2}/T)$; the hypothesis in $[0,\infty]$ forces $L_k\ge1$ eventually and $L_k/n_k^{3/4}\to\infty$ along the finite indices.
* **M2/M3.** `rescaledMeasure_eq_box` holds for every real $t$: $n^{-1/2}\mathrm{rescaledField}=\varrho_n\mathfrak z_n$ identically. The closeness bound follows from `abs_integral_rescaledMeasure_box_sub_le` and $\varrho_n(t)\le e^{T}$. The filtrations are consistent: `IsWaveFunction.nullAug` and `IsBrownianFamily.nullAug` put the given $\psi_k$, $\psi^L_k$ and the constructed $\psi^\infty_k$ on the same `nullAug`.
* **E2/E1.** `exists_isonormal` with Mathlib's `IsGaussianProcess.(i)IndepFun_of_covariance_eq_zero` (present in v4.35.0); E1 from `exists_isBrownianFamily`, `prop_2_1_existence` and `IsBrownianFamily.nullAug` (see R5).

## Appendix: scratch tests

`copies.lean` (imports `MainTheorem`, `Companions`, `Corollaries` and the library copies):
```lean
def cmpTypes (a b : Name) : MetaM Unit := do
  let ia ← getConstInfo a; let ib ← getConstInfo b
  let tb := ib.type.instantiateLevelParams ib.levelParams (ia.levelParams.map Level.param)
  logInfo m!"{a} vs {b}: Expr equal: {ia.type == tb}; defeq: {← isDefEq ia.type tb}"
-- run on the 10 pairs: all `Expr equal: true`
universe u v
example : type_of% @QSSEPtoKPZ.main_theorem.{u,v} := @QSSEPtoKPZ.main_theorem_lib.{u,v}
example : type_of% @QSSEPtoKPZ.main_theorem_lib.{u,v} := @QSSEPtoKPZ.main_theorem.{u,v}
-- … and likewise for E1, U1, E2, P and the two corollaries (14 examples, all accepted)
```
`probes.lean`:
```lean
example (x : ℤ) : degree ⊤ x = 2 := by simp [degree, box]
example : degree (1 : ℕ) 1 = 1 := by simp [degree, box, Set.indicator]
example : degree (0 : ℕ) 0 = 0 := by simp [degree, box, Set.indicator]
example {Ω : Type*} (f W : ℝ → Ω → ℂ) (m : ℕ) (ω : Ω) : itoSum f W 0 m ω = 0 := by simp [itoSum]
example (s : ℝ) : rwTail s 0 = ∑' x : ℤ, rwKernel s x := by simp [rwTail]
example (n T ε : ℝ) (L : ℕ) : prop81Rhs n T ε L =
    ENNReal.ofReal ((16 / ε ^ 2) * ((n * T) * (8 + (n * T) / 2)) *
      Real.exp ((2 * thetaN n * L) - ((min 1 (L / (n * T))) * L) / 3)) +
    ENNReal.ofReal ((4 * Real.exp (2 * T)) /
      (ε * Real.cosh ((L - n ^ (3 / 4 : ℝ) * T) / n ^ (1 / 2 : ℝ)))) := rfl
```
`pp.lean` (all 107 declarations of the 25 files with `pp.parens`), `deps.lean` (`sorry` traversal) and `alg.py` (numerical pairing / `conj_mul` check) are in the same scratch folder.
