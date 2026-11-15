# Audit of the Stage 3 statements (13 November 2026)

Independent audit by an Opus 5.5 agent, on commit `ca2e9da`: 0 ERROR, 1 WEAKNESS, 6 REMARK. Handled: W1 (D8' rationale) and R1 (the law of a non-measurable map) corrected in `docs/stage3-statements.md`; R2 (𝒵_n written for the tilted measure 𝖹_n in docstrings) corrected; R3–R6 recorded, no change. The report is reproduced unchanged below.

---

# Audit of the Stage 3 statements (13 November 2026)

Independent adversarial audit, 13 November 2026, 02:27–02:40 CET, by an Opus 5.5 agent.

- Project: `master`. HEAD is `631ab41`, which differs from `ca2e9da` only in `PROGRESS.md`. The four statement files are those of T0' (`cf9618f`).
- Article: SHA-256 `3547cb86…`, the expected version (1713 lines). Equation and result numbers were checked against `QSSEPtoKPZ.aux`: Prop 5.1, Lemma 5.2, (5.1), (5.2), (3.3)–(3.5), (3.8), (3.9), (4.8), (4.9), (2.2), Prop 3.1, Prop 4.3, Lemma 2.3. All docstring numbers are correct.
- Nothing in the project was modified.

## Method

- Read: `CLAUDE.md`; `docs/stage3-design.md` (all of it); `docs/stage3-statements.md`; `docs/stage2-audit.md`; the four files `Tightness/{Integral,ExpMoments,AldousCondition,Prop51}.lean`; `TiltedField/Defs.lean`; `Martingales/Defs.lean`; `Definitions.lean`; `MainTheorem.lean`; `Companions.lean` (E1); the signatures of the I0' interfaces (`Martingales/Aldous.lean`, `Tightness/{CompactSets,PathCompact,FiniteMeasureEmbed}.lean`).
- Article, read line by line: Section 5; Section 2.1 ((2.2)); Section 3.1; Prop 4.3; the beginning of 7 and 7.1; the last proof of Section 7; all of Section 8.
- Lean checks, in scratch files `S1.lean` and `S2.lean` in this folder, run with `lake env lean`:
  - **σ-algebra.** `#synth MeasurableSpace C(Set.Icc 0 1, FiniteMeasure ℝ)` gives `ContinuousMap.measurableSpace`. Also, `(inferInstance : MeasurableSpace C(Set.Icc 0 T, FiniteMeasure ℝ)) = borel _` holds by `rfl`. `BorelSpace`, `OpensMeasurableSpace` and `T2Space` are found. No Stage 3 statement uses the `MeasurableSpace` instance of `FiniteMeasure ℝ` (the Giry σ-algebra). `Measurable Zv`, `AEMeasurable (Zv k)` and `Measure.map (Zv k)` all go through the Borel instance of `C(…)`, which is the instance `main_theorem`'s `TendstoInDistribution` uses.
  - **Elaboration.** All 7 statements were printed with `pp.coercions`. `τ ω + s` is `↑(τ ω) + s` in ℝ. `tiltedMeasure n ψ ω ↑t` takes the subtype value. `↑(Zv ω t)` is the coercion `FiniteMeasure → Measure`. `IsStoppingTime` takes `Ω → WithTop ι`.
  - **Consistency.** `prop_5_1_isTight` was **derived from `prop_5_1`** (proof checked by Lean, modulo the `sorry` of `prop_5_1`). The derivation uses `hZm`, together with the fact that a compact set is closed (hence Borel). See R1.
  - **Mathlib's push-forward.** In Mathlib v4.35.0, `Measure.map f μ` for a non-`AEMeasurable` `f` is **not** `0` when `μ ≠ 0`. It is a Dirac mass `dirac Classical.ofNonempty` (`MeasureTheory/Measure/Map.lean`, `map`, `map_of_not_aemeasurable_of_ne_zero`). See R1.
- By hand:
  - Re-derived Lemma 5.2: κ, Doob's inequality with the factor $e^{\kappa^+T}$, the union bound $\cosh\le\max(e_1,e_{-1})$. Numerical check: $\max\lvert\kappa\rvert=1.2191$ over $n\in[1,10^8]$ (400 log-spaced points) and $b\in[-1,1]$ (step $0.01$).
  - Re-derived the quantitative (5.2): $\lVert\mathcal A_n\varphi\rVert_\infty\le K\lVert\varphi\rVert_{1,3}$ uniformly in $n\ge1$, and $(e^{\theta/2}\varphi(y+h)-e^{-\theta/2}\varphi(y))^2\le K\lVert\varphi\rVert_{1,3}^2\lambda_n$ (using $h^2=n^{-1}\le\lambda_n$). This gives $c(Cs/\eta+C^2\sqrt s/\eta^2)$ with $c$ depending only on $T$; the bound is invariant under $\varphi\to a\varphi$, $C\to aC$, $\eta\to a\eta$, as it must be.
  - Checked how each statement is used in Q4 (`aldous_modulus`, `isCompact_pathCptSet`), in Section 7 and in Section 8.

**Summary: 0 ERROR, 1 WEAKNESS, 6 REMARK.**

---

## ERROR

None found.

---

## WEAKNESS

### W1. Decision D8' (Polish space): the rationale omits the Lusin–Souslin step of `PLAN.md` (`docs/stage3-design.md:374`, `docs/stage3-statements.md`, deviation 8)

**Problem.** D8' tells the author that completeness of $\mathcal M_+$ is used by the article only for Skorokhod's representation, and that it can be avoided because Billingsley's Theorem 6.7 holds in separable metric spaces. That is right for Skorokhod's representation. But `PLAN.md` (Section 3, table, "End of Section 7") plans a second use of the Polish property: "the set of trajectories that come from an element of $C([0,T],\mathcal M_+)$ is Borel, by the Lusin–Souslin theorem, which is in Mathlib."

- Mathlib's Lusin–Souslin theorem (`MeasurableSet.image_of_continuousOn_injOn` and its relatives) needs a Polish domain, or at least a standard Borel one.
- Here the domain is $C([0,T],\mathcal M_+)$.
- `PLAN.md` line 52 also says the Skorokhod theorem will be "a general statement on Polish spaces".

So, if the route of `PLAN.md` is kept, Stage 4 or 5 needs $C([0,T],\mathcal M_+)$ to be Polish, hence $\mathcal M_+(\mathbb R)$ to be complete (in some compatible metric). Otherwise both steps must be redone without it.

No Stage 3 statement is affected: none asserts or needs completeness.

**Fix.**
1. Add to D8' that `PLAN.md` uses the Polish property twice (Skorokhod, and Lusin–Souslin at the end of Section 7).
2. Say plainly that deferring completeness means either the Gδ task (400–800 lines, design §5) or a different argument at both places.
3. The author should decide D8' knowing this.

---

## REMARK

### R1. Wrong statement about Lean's junk law (`docs/stage3-statements.md`, lines 11 and 60)

**What the sheet says.**
- Line 11: "the law of a non-measurable map is $0$".
- Line 60, on `prop_5_1_isTight`: "Lean gives the law $0$ to a non-measurable map, and a family of zero measures is trivially tight".

**What Mathlib v4.35.0 does.** In this version, `Measure.map f μ` with `f` not a.e.-measurable and `μ ≠ 0` is the Dirac mass at an arbitrary fixed point `Classical.ofNonempty`. This is precisely so that the push-forward of a probability measure stays a probability measure.

**Consequences for the statement.**
- The statement itself is fine. The hypothesis `hZm` makes every member of the family the genuine law.
- With `hZm`, `prop_5_1_isTight` follows from `prop_5_1` (checked in Lean, `S2.lean`).
- Without `hZm`, the statement would still be true: all junk laws are the same Dirac mass $\delta_p$, and $K\cup\{p\}$ is compact. So `hZm` is not a safeguard against a vacuous conclusion. It only makes the family the family of genuine laws, which is the natural reading.

**Fix.** Correct the two sentences, for example: "Lean gives an arbitrary Dirac mass as the law of a non-measurable map; the hypothesis makes every element of the family the true law." Keep `hZm`.

### R2. Notation in the Lean docstrings: 𝒵 for the tilted measure 𝖹 (all four files)

**Problem.** `docs/stage3-statements.md` follows the article: $\mathsf Z_n$ is the tilted measure (3.5), and $\mathcal Z_n$ is the measure (1.15) of Theorem 1.2. The docstrings of the four Lean files write `𝒵_n(t)` for `tiltedMeasure`. Examples:
- `Prop51.lean:23–27`, `:48–50` ("`𝒵_n(t)` is the measure (3.5)");
- `Integral.lean:11–35`;
- `ExpMoments.lean:15–42`;
- `AldousCondition.lean:16–47`.

The frozen `main_theorem` uses `𝒵ₙ` for `rescaledMeasure`, which differs from the tilted measure by $\varrho_n$. The Stage 2 files have the same habit. `Prop51.lean` says which measure is meant, so nothing is wrong, but a reader comparing with `main_theorem` can be misled.

**Fix.** Write `𝖹_n` in the Stage 3 docstrings, as in the sheet and the article.

### R3. `aldous_condition`: where the safeguard conjunct is placed (`AldousCondition.lean:52–55`)

**Problem.** The conjunct `∀ᵐ ω, ∀ t ≥ 0, Summable (zN n ψ ω t)` sits after the binders `C, φ, τ, s, η` and their hypotheses. To extract it, one must supply an `IsC13` function, a stopping time bounded by `T`, and `s`, `η`. When `T < 0` no such stopping time exists, so the conjunct is never asserted. Mathematically this is harmless: the bound is genuine wherever the series converges, and the same summability is already a Stage 2 result.

**Fix (optional).** State it right after `1 ≤ n →`, as `(∀ᵐ …) ∧ ∀ {C φ}, …`.

### R4. Universe of `aldous_condition` (`AldousCondition.lean:48–49`)

**Problem.** Like `prop_5_1`, `aldous_condition` has the universe of `Ω` as a parameter of the theorem. So `∃ c` is chosen for each universe level. This is harmless, as for `prop_5_1`. Deviation 12 of the sheet mentions only `prop_5_1`.

**Fix (optional).** Mention `aldous_condition` in deviation 12.

### R5. `prop_5_1_isTight` is indexed by ℕ (`Prop51.lean:90–100`)

**Problem.** The article's family of laws is indexed by the real $n\ge1$, on one probability space. `prop_5_1` covers that literally: one compact set for all $n$ and all realizations. `prop_5_1_isTight` covers sequences, which is the form `main_theorem` needs.

**Fix (optional).** An arbitrary index type `ι` in place of `ℕ`, with `Ω : ι → Type*`, would be strictly more general, with the same proof. No change is needed for later use.

### R6. Scope (D7', D6') and what later stages must still derive

None of these is a defect of the statements; each is derivable with the tools listed.

- **Passing from $\mathsf Z_n$ to $\mathcal Z_n=\varrho_n\mathsf Z_n$.** No statement is made for $\mathcal Z_n$ (D7', as in the article). Stage 5 needs:
  - that `t ↦ ϱ_n(t) • Zv ω t` is a version of `rescaledMeasure ⊤`. Mathlib has `ContinuousSMul ℝ≥0 (FiniteMeasure Ω)` (`FiniteMeasure.lean:782`), and Stage 2 proved `rescaledMeasure_eq`.
  - the transfer of convergence in distribution, for example by Slutsky (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`) followed by the continuous map $(r,\gamma)\mapsto r\gamma$.
- **Finite $L$.** `main_theorem` covers finite $L_k$, while Stage 3 covers `IsWaveFunction ⊤` only. Section 8 uses only (5.1). Lemma 5.2 is stated on an arbitrary filtered space, so it applies to the coupled $\psi^\infty$ once that process is built on the same space. That construction is not E1 (E1 gives some space), and is work for Stage 5.
- **Adaptedness of the version.** `prop_5_1_version` asserts measurability, not adaptedness to `nullAug μ (filtN n 𝓕)`. Section 7.1 needs the natural filtration of $\mathsf Z_n$ to be contained in $\mathcal F^n$ (augmented). For *any* version this follows from:
  - the version agreeing a.s. with `tiltedMeasure`;
  - `tiltZ_measurable`;
  - the Borel description of `FiniteMeasure ℝ` (H2, `borel_finiteMeasure_eq_iSup_tightEmb`).

  The design keeps it in the internal `exists_tiltedPath_version`. Nothing to change.
- **Measurability of the atoms.** The atoms $\mathfrak z_n(t,x)=\mathsf Z_n(t)(\{y_n(t,x)\})$, as functions of the path, are for Stage 4 (W3 of the Stage 2 audit). $\mu\mapsto\mu(F)$ is upper semicontinuous for closed $F$, hence Borel, so "Giry = Borel" (R2 of the design) may not be needed for this.

---

## Statements checked and found fine (apart from the items above)

### `integral_tiltedMeasure` (`Integral.lean:36–41`)
- True for every `n`, `t`, `ω` with `Summable (zN …)`. `zN ≥ 0`, so `ofReal` does not truncate.
- Finiteness, integrability and the identity follow from `Measure.sum` of weighted Diracs (`integral_sum_measure`).
- `hφm` is not needed (the measure is carried by a countable set), but it is harmless.
- No junk: integrability is asserted.
- It is what Section 7 needs to pass between `pairZ` and $\int\varphi\,d\mathsf Z_n(t)$, for bounded $\varphi$, including time-dependent $\varphi_t$.

### `lemma_5_2` (`ExpMoments.lean:43–54`)
- Conjunct 1 (a.s., for all `t ≥ 0` and all `b ∈ [-1,1]`, summability) is true:
  - the coefficient of $x$ in the exponent is $\lvert\theta_n+bn^{-1/2}\rvert\le2$;
  - (2.2) with $a=2$ holds on $[0,S]$ for every $S\in\mathbb N$.

  It makes `pairZ` genuine for $e_b$, and for $\cosh$ by domination by $e_1+e_{-1}$.
- Conjunct 2: integrability is asserted (a.e.-measurability holds through limits of partial sums). $\mathbb E=e^{\kappa t}\le e^{2t}$ for $t\ge0$.
- Conjunct 3 (5.1):
  - the supremum is taken in `ℝ≥0∞`;
  - `ofReal` of a nonnegative quantity, so no truncation;
  - outer probability;
  - the constant $2e^{2T}/K$ is that of the article.

  The proof re-derived by hand gives exactly this bound.
- This is strong enough for Section 8: $\sup_t\sum_{x\notin\Lambda_L}\mathfrak z_n\le\sup_t\mathsf Z_n(t;\cosh)/\cosh\ell_n$, convergence in outer probability. With the internal `lintegral` bridge, it is also strong enough for compact containment in `tightCoshBall`.

### `aldous_condition` (`AldousCondition.lean:48–58`)
- **Quantifier order.** `∃ c` comes before the probability space, `n`, `φ`, `C`, `τ`, `s`, `η` (c depends only on `T`, as D8 of Stage 2).
- **Test functions.** `IsC13 1 (fun _ => φ) (fun _ _ => 0) C` means $\varphi\in C_b^3$ with $\lVert\varphi\rVert_{1,3}\le C$, and forces $C\ge0$. It is satisfiable: $\varphi=0$, $C=0$ gives the bound $0$, which is true.
- **Stopping times.** Stopping times of `nullAug μ (filtN n 𝓕)` (that is, $\mathcal F_{nt/2}\vee\mathcal N$) bounded by `T` for every ω. These are more stopping times than in the article, so the statement is stronger, and it is consistent with (4.9) as approved (D4 of Stage 2).
- **Event.** Strict `η < |…|`, outer measure.
- **Truth.** The bound is true. The drift–martingale decomposition is pathwise (the definition of `MN` with $\varphi_t=0$). The martingale term follows from optional sampling for an a.s.-continuous $L^2$ martingale at stopping times of the augmented filtration, and (4.9).
- **Strength.** It implies the article's (5.2) for every τ of $\mathcal F^n$. It is strong enough for `aldous_modulus` with `𝓖 = nullAug μ (filtN n 𝓕)`:
  - apply it with horizon `T+1`, and choose $\delta_1\le1/32$ so that $2\delta_1\le1/16$;
  - pass from `≤` to `<` by halving η;
  - transfer from `pairZ` to the version, which agrees with it a.s. at all times.

### `prop_5_1_continuous` (`Prop51.lean:51–55`)
- Faithful, and stronger than the article: continuity on $[0,\infty)$.
- It also asserts finiteness of $\mathsf Z_n(t)$ for all $t$ (equality with a `FiniteMeasure`).
- It is true, by the article's uniform-convergence argument with (2.2).

### `prop_5_1_version` (`Prop51.lean:61–65`)
- `Measurable` for every ω (not only a.e.), for the Borel σ-algebra of the compact-open topology: exactly the instance and topology of `main_theorem`.
- Provable by the `toMeasurable` construction of the design, with H2.

### `prop_5_1` (`Prop51.lean:74–82`)
- One compact set $\mathcal K$ for all realizations, all real $n\ge1$ and all versions. This is stronger than the article's family indexed by $n$, and true because every constant used (Lemma 5.2, (4.8), (5.2)) is universal.
- The statement for every version is equivalent to the statement for one version (outer measure, null sets).
- `IsCompact` is for the compact-open topology, which is the topology of uniform convergence on $[0,T]$.

### `prop_5_1_isTight` (`Prop51.lean:90–101`)
- Literal Mathlib tightness of the family of laws, on the same space and σ-algebra as `main_theorem`.
- It follows from `prop_5_1` (checked in Lean).
- Together with `isCompact_closure_of_isTightMeasureSet` (which needs only `T2Space`) and the metrizability of H2, it gives the extraction of subsequences that Section 7 uses.

### Definitions used
- **Stage 2 (frozen):** `zN`, `tiltedMeasure`, `pairZ`, `WN`, `IsC13`, `filtN`, `nullAug`, `nullSets`, `timeChange`.
- **Frozen statement:** `IsBrownianFamily`, `IsWaveFunction ⊤` (`box ⊤ = ℤ`, `degree ⊤ = 2`), `density`, `rescaledPosition`.

All were re-read; nothing in them affects the Stage 3 statements.

### Junk-value scan (all 7 statements)
- Every `tsum` (`pairZ`) is genuine: summability is asserted, or follows from an asserted summability with bounded or dominated weights. Non-summable `ω` form a null set and only shrink the events bounded.
- Every Bochner integral has its integrability asserted.
- No `⨆` in ℝ: the one supremum is in `ℝ≥0∞`. `ofReal` is applied only to nonnegative quantities, or to upper bounds; a negative `c` would only make the statement stronger.
- Outer measure is used for events not claimed measurable.
- `Measure.map` is taken only of maps assumed `AEMeasurable`, and into the Borel σ-algebra.
- The Giry σ-algebra of `FiniteMeasure ℝ` is never used.

### Hypothesis sets
- No contradictory hypotheses: `IsC13` is satisfiable, bounded stopping times exist (`τ = 0` when `T ≥ 0`), and `T > 0`, `K > 0`, `ε > 0` are harmless.
- Existence of realizations is the frozen companion E1 (unproved, as for `main_theorem`).

---

Time taken: about 13 minutes (02:27–02:40 CET).
