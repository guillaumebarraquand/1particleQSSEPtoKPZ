# Stage 4: independent audit of the statements (Section 7)

Written on 13 November 2026 by an independent audit agent (Opus 5.5), on branch `work-audit4` (base `80c9fe7`). **Nothing was proved and no `.lean` file of the library was changed.** Scratch tests were run with `lake env lean` against the built library; the decisive one is reproduced in the appendix.

Scope: the 11 statements of `docs/stage4-statements.md` (`prop_7_1`, `eq_7_4`, `prop_7_2`, `prop_7_3`, `IsMildSolution.integral_sq`, `IsMildSolution.isWeakMild`, `main_theorem_top`, `IsMildSolution.nonneg_of_isWaveFunction`, `IsWalshIntegral.ae_eq_lib`, `IsWalshIntegral.isometry_lib`, `isMildSolution_unique_lib`), the definitions they use (`LimitPoints/Defs.lean`, `Uniqueness/Defs.lean`, and from Stages 2–3 `IsC13`, `HasBracket`, `IsCL2Mart`, `nullAug`, `IsMollifier`, `rhoEps`, `smoothedNormSq`, `tiltedMeasure`), the sheet, and the "Departures" of `docs/stage4-interfaces.md`. Article checked: SHA-256 `3547cb86…`, 1713 lines (unchanged).

**Summary: 1 ERROR, 1 WEAKNESS, 6 REMARKS.** The ERROR is a false statement: `prop_7_2` can be refuted (kernel-checked, appendix) because it leaves out the hypothesis $\mathcal Z(0)=\delta_0$ of Proposition 7.1 (1). Fix: one added hypothesis, which `prop_7_1` supplies; nothing else in the route changes.

## ERROR

### E1. `prop_7_2` is false as stated: the hypothesis $\mathcal Z(0)=\delta_0$ is missing

*Where.* `QSSEPtoKPZ/WhiteNoise/Prop72.lean:45–62` (hypotheses on lines 46–56). The claim that the hypothesis is not needed is in `docs/stage4-design.md:184` ("Hypothesis (1) of Prop 7.1 is not needed ($\phi_0(0)$ appears in $M^\phi$)"). The sheet says that the hypotheses are "the conclusions of Proposition 7.1" (`docs/stage4-statements.md:52` and deviation 5, line 88), which is not true of the Lean.

*What is wrong.* The article's Proposition 7.2 takes "$\mathcal Z$ and $Z$ as in Proposition 7.1", which includes (1) $\mathcal Z(0)=\delta_0$, and its proof uses it. Step 3 writes $M^\phi(t)-\phi^{(N)}\cdot M(t)$ as a sum of increments of the $M^{\phi-\phi_{s_i}}$. That sum leaves out the initial value $M^\phi(0)=\mathcal Z(0;\phi_0)-\phi_0(0)$, which is $0$ only because $\mathcal Z(0)=\delta_0$. A martingale need not start at $0$, so without (1) the other hypotheses do not force $M^\phi(0)=0$.

*Counterexample* (all hypotheses hold and the conclusion fails). Take $\Omega$ a single point, $\mathcal Z\equiv0$ (the zero path), $Z\equiv0$ and any filtration. Then:
* $M^\phi(t)=-\phi_0(0)$ is constant, so it is a martingale;
* its bracket $\int_0^t\int Z^2\phi^2=0$ is correct;
* $Z$ is predictable, nonnegative and in $L^2$;
* $\mathcal Z(t)=Z(t,x)\,dx=0$.

But for a bump $f\ge0$, (7.8) reads $0=\int g_tf+\iint(g_{t-s}\ast f)\cdot 0\,d\xi=\int g_tf>0$ almost surely, which is false. In Lean, `prop_7_2_false` (appendix) derives `False` from three things: the statement of `prop_7_2`, the companion **W** (`IsWalshIntegral.ae_eq`, taken as a hypothesis) and any white noise. `#print axioms` gives `propext, Classical.choice, Quot.sound`. So once W and E2 are proved, `prop_7_2` as written implies `False`. It can never be proved, and task J2 would be blocked.

*Fix.* Add to `prop_7_2`, after `hY`, the hypothesis
```lean
    (hY0 : ∀ᵐ ω ∂Pr, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0)
```
It is the first conclusion of `prop_7_1`, so the route does not change:
* The scratch test T4 checks that `prop_7_1` supplies every hypothesis of `prop_7_2`. It takes `𝒢 = nullAug Pr (pathFiltration Y)` and transports predictability by the monotonicity of `Filtration.predictable`, which the test proves. The new hypothesis is the conjunct `_h0`, which the test currently discards.
* The fixed statement elaborates (test T5).
* `prop72_noise` (task J1) does not need the new hypothesis: it only concerns increments $M^\varphi(v)-M^\varphi(u)$, and it is consistent with the counterexample. Task J2 uses `hY0` to get $M^\phi(0)=0$ almost surely.
* `exists_sheVersion_map_eq` (task K5) already has `hY0`.

Also correct `docs/stage4-design.md:184`, and in the sheet write "the conclusions (1)–(3) of Proposition 7.1".

## WEAKNESS

### W1. `eq_7_4`: the constant is chosen after the probability space of the limit point

*Where.* `QSSEPtoKPZ/LimitPoints/Prop71.lean:80` (and its twin `limPt_eq_7_4`). The sheet says "a constant $C$, depending only on $\rho$" (`docs/stage4-statements.md:43`).

*What.* `Ω` and `mΩ` come from the `variable` line, so they are bound **outside** `∃ C`. `#check @eq_7_4` gives `∀ {Ω : Type u_1} {mΩ} {ρ}, IsMollifier ρ → ∃ C, …`. So the Lean statement lets $C$ depend on the type and σ-algebra on which the limit $Y$ lives. This is weaker than the sheet and the article. It does no harm to the route, which only uses finiteness, but the sheet describes it wrongly.

*Fix.* In `eq_7_4` and `limPt_eq_7_4`, bind `∀ {Ω : Type*} {mΩ : MeasurableSpace Ω}` after `∃ C : ℝ,`, together with `Pr` and `Y`. The universe levels have to stay outer; say so in the sheet. Alternatively, keep the current form and write in the sheet "depending only on $\rho$ and on the space carrying $\mathcal Z$".

## REMARKS

**R1. `main_theorem_top` is exactly `main_theorem` with $L_k=\infty$** (`Uniqueness/Theorem12.lean:107`). Checked in three ways:
1. The kernel accepts `main_theorem_top` (universe-polymorphic) proved from `main_theorem` with `L := fun _ => ⊤`, `le_top` and `tendsto_size_top n`.
2. Conversely, `main_theorem_top` proves `main_theorem` instantiated at `L = fun _ => ⊤` (goal written with `(fun _ => ⊤) k`) by `exact`.
3. At the meta level: substitute `L := fun _ => ⊤` in the type of `main_theorem`, drop the two non-dependent binders `hL₁` and `hL`, and beta-reduce. The result is an `Expr` **equal** to the type of `main_theorem_top`, with the same universe parameters `[u_1, u_2]`.

The sheet's claim is correct.

**R2. The companion copies and the twins are identical.** A meta command checked `Expr` equality of the types and equal universe parameters for:
* the companion copies `IsWalshIntegral.ae_eq` / `_lib`, `IsWalshIntegral.isometry` / `_lib` and `isMildSolution_unique` / `_lib` (`[u_1]` each);
* the twins `IsMildSolution.integral_sq` / `heatMild_integral_sq`, `IsMildSolution.isWeakMild` / `heatMild_isWeakMild` and `eq_7_4` / `limPt_eq_7_4` (`[u_1, u_2]` for the last pair).

The companion **P** follows from `IsMildSolution.nonneg_of_isWaveFunction` and E1: the kernel accepts `IsMildSolution.nonneg` from `nonneg_of_isWaveFunction (exists_isWaveFunction ⊤)`, with the universe `u` of `hE` set to `0`. The frozen files have not changed since `6d27b6f`.

**R3. Traps checked; none found apart from E1.**
* *Junk values.*
  * `pathAt`: only `T>0` is used.
  * `rhoEps` is only used at $\varepsilon=1/(k+1)>0$.
  * `heatKernel` at time $\le0$ is $0$, but only positive times occur (`heatConv (t-s)` with $s<t$, and `heatKernel (t/2)`).
  * `limDensity` takes the liminf in $[0,\infty]$, so no boundedness side condition is needed, and `toReal ⊤ = 0` is exactly the article's "0 if infinite".
  * `iteratedDeriv 2 (φ s)` is only used for $s\in[0,t]\subseteq[0,T]$, where `IsC13` gives $C^3$.
  * The Bochner integrals are genuine: in `limMart` (bounded continuous integrands, finite measures) and in `smoothedNormSq` (square-integrable, at most $\lVert\rho_\varepsilon\rVert_\infty\mu(\mathbb R)^2$).
  * In `limBracket`, and in `∫ x, Z t x ω * f x` of `IsWeakMild`, the junk value $0$ can only occur on null sets of $(\omega,s)$, by (7.1). `HasBracket` (whose clauses hold almost everywhere) and `IsWalshIntegral` (whose values are defined up to null sets) ignore those sets.
* *`condExp`.* All measures are probability measures. For `prop_7_3` this is forced by `IsWhiteNoise` (`IsWhiteNoise.isProbabilityMeasure`).
* *`Measure.map`.* `TendstoInDistribution` includes the almost-everywhere measurability, so there are no junk images.
* *σ-algebras.* `C(Icc 0 T, FiniteMeasure ℝ)` carries `borel` (Mathlib instance `ContinuousMap.measurableSpace := borel _`). `pathFiltrationCan` writes `borel (FiniteMeasure ℝ)` explicitly. The Giry instance never enters a statement.
* *Smoothness.* `ContDiff ℝ (⊤ : ℕ∞)` means $C^\infty$, not analytic.
* *Series (7.15).* The terms are positive and `HasSum` asserts convergence. I re-derived $K^{\ast k}=2^{-k}t^{k/2-1}\Gamma(k/2)^{-1}g_{t/2}$ by induction with the Beta integral. Numerically, $\sum_kK^{\ast k}$ agrees with the right side of (7.15) to $10^{-15}$ for $t=0.1,1,3,10$.
* *Non-vacuity.* The hypotheses of `prop_7_1` can be met (E1, `prop_5_1_version`, a convergent subsequence). Those of `prop_7_3` are met by `IsMildSolution.isWeakMild`, given E3 (as for the frozen theorem).

**R4. Faithfulness of the other statements.**
* `prop_7_1`: conclusions (1), (2) with (7.1), and (3) with (7.2)–(7.3), as in the article. Predictability is asserted for $\mathcal G^0$ itself, which is stronger, and true: the mollified fields are continuous in $(t,x)$ and adapted, and `limField` is their liminf. "Limit point" is generalised to any limit in law, with realizations that depend on $k$, which is also stronger.
* `prop_7_3`: weaker hypotheses (no predictability) and the article's conclusion. The article's proof still goes through, because Itô's isometry W applies to the difference of the two Walsh integrals.
* `IsMildSolution.isWeakMild`: (7.13) "for every $t$", as the article says after (7.15).

All deviations are listed in the sheet, except the dropped (1) of E1.

**R5. Uniformity in the realization** (departure 16). In the article all the $\mathsf Z_n$ come from one $\psi$. `prop_7_1`, like the frozen `main_theorem`, allows a different realization of the QSSEP for each $k$. So the Lean proof needs Proposition 6.2 with $\varepsilon_0$ and $N$ independent of the realization, and the frozen `prop_6_2` does not state this. The departure is justified and recorded (sheet, "Remarks on the article", third item). It is a proof risk for task Q1b, not a defect of a statement.

**R6. One step of the route has no interface yet.** Between `prop_7_2` and `exists_sheVersion_map_eq`, task Q5 must show `IsWeakMild T 𝒢b S Z₁ (Pr.prod ν'')` for $Z_1(t,x,\omega)=$ `limField ρ Y t x ω.1`. This needs three things:
* Joint measurability on $\Omega\times\Omega''\times\mathbb R\times\mathbb R$. It follows from the predictable conjunct by composing with $t\mapsto t^+$, since `pathAt` sends negative times to $0$.
* (7.1) on the product (Tonelli).
* (7.13) from (7.8). This requires turning `hdens` ("almost surely, for almost every $t$") into "for almost every $t$, almost surely, for all $f\in C_c^\infty$", with one null set of times for all $f$. One way: Fubini on the measurable set where the two measures agree on a countable determining class of test functions, then `IsWalshIntegral.congr_ae`.

All of this is true. I suggest an interface lemma (for example `isWeakMild_of_prop_7_2`, in `Theorem12.lean` or a new file), so that the size of task Q5 is not underestimated.

The other departures (1–15) are justified as stated. In particular:
* Departure 6: the functionals of `limMart` are continuous in $t$ for every path, and the bracket functional is modified outside the measurable set $\lbrace\int_0^T\int Z^2<\infty\rbrace$, as the note on task Q4 says.
* Departure 9: `hdens` only sees $\max(Z_1,0)$, so positivity has to come from `hZ₁0`.
* Departure 10: `S` itself is not measurable with respect to the noise on the axes.

## Corrections after the audit and an external review

Done on 13 November 2026 by a repair agent (Opus 5.5), branch `work-s4repair` (base `53f89eb`). Statements still `sorry`; `lake build` succeeds. Details: `docs/stage4-interfaces.md`, departures 17–22.

* **E1 (fixed).** `prop_7_2` has the new hypothesis `hY0 : ∀ᵐ ω ∂Pr, (pathAt (Y ω) 0 : Measure ℝ) = Measure.dirac 0` after `hY`, exactly as proposed. `prop_7_1` supplies it (first conjunct); `prop72_noise` (J1) is unchanged; `exists_sheVersion_map_eq` (K5) already had it. The test T3 no longer applies (the zero path violates `hY0`). The design's claim (Section 2.3) and the sheet are corrected.
* **W1 (fixed).** In `eq_7_4` and `limPt_eq_7_4`, `∀ {Ω : Type*} {_ : MeasurableSpace Ω}` comes after `∃ C`; `#check @eq_7_4` shows `∃ C, … ∀ {Ω : Type u_2} {x : MeasurableSpace Ω} {Pr : Measure Ω} …`. The two types are still `Expr`-equal, with universe parameters `[u_2, u_3]`.
* **External review, `IsMMIntegral` (fixed).** The `limit` rule did not require the limit process to be measurable; since `∫⁻` is the lower integral, the convergence condition could hold for an error that is not a.s. $0$ (on `Bool` with the trivial σ-algebra, $q=0$, $M=0$, $h=0$: $X(t,\mathrm{true})=t$, $X(t,\mathrm{false})=0$ would be an integral of $0$), and `IsMMIntegral.hasCovariation`, `.ae_eq` were false. The rule now requires `∀ r ∈ Set.Icc 0 T, AEStronglyMeasurable (X r) μ`; `hasCovariation` and `ae_eq` also assume $\mathbb E\int_0^T\int q<\infty$ (`hq1`), which makes the Bochner integrals of the bracket genuine (J1 supplies it from (7.1)). The `block` and `add` rules have no such trap.
* **External review, projection onto the noise (fixed).** `IsWalshIntegral.condExp_noise` took Mathlib's `condExp` on $\Omega\times\mathbb R^2$ for $\nu\otimes\mathrm{Leb}^2$; an $L^2$ integrand need not be integrable for this infinite measure, and `condExp` is then $0$, whatever the σ-finiteness. With $h(s,y)=\mathbf 1_{(0,1]}(s)\mathbf 1_{[0,\infty)}(y)/(1+y)$ the statement was false. This audit's remark R3 ("all measures are probability measures" for `condExp`) had missed this interface: it only looked at the 11 statements. The projection `noiseProj` is now the conditional expectation for the probability measure $\nu\otimes\gamma\otimes\gamma$ (same null sets, $L^2(\nu\otimes\mathrm{Leb}^2)\subset L^1$, Gaussian density measurable in $(s,y)$, hence equal to the $L^2(\nu\otimes\mathrm{Leb}^2)$ projection), with interfaces for linearity, contraction, deterministic factors and conditional Fubini, which the proof that $\hat Z$ solves (7.13) needs. No other `condExp` of the Stage 4 interfaces is for an infinite measure.
* **R6 (done).** New interface `isWeakMild_prod_of_eq_7_8` (file `Uniqueness/WeakMildBridge.lean`, task Q5a): (7.8) on $\Omega\times\Omega''$, the density (with $Z\ge0$ and joint measurability) and (7.1) give `IsWeakMild` for the lifted field.
* **R5 / departure 16 (checked).** `pathPrelim_replacement` is stated so that the Stage 2 proof gives it: the constant comes from `lemma_6_4 hρ` (depends only on $\rho$) and $\varepsilon_0$, $N$ depend only on $\rho,T,C,\eta,\delta,\varepsilon$. Unchanged; Q1b is told to do it first.

## Checks run

| Test | Content | Result |
|---|---|---|
| T1 | `main_theorem_top` from `main_theorem` (universe-polymorphic); the converse at `L = fun _ => ⊤`; `Expr` equality of the companion copies and twins | all pass |
| T2 | meta level: substitute `L`, drop `hL₁` and `hL`, beta-reduce, compare with `main_theorem_top` | equal `Expr`, levels `[u_1, u_2]` |
| T3 | `prop_7_2_false`: the statement of `prop_7_2` + W + a white noise ⟹ `False` | kernel accepts; standard axioms only |
| T4 | conclusions of `prop_7_1` ⟹ hypotheses of `prop_7_2` (`predictable_mono` proved inline) | passes |
| T5 | fixed `prop_7_2` (with `hY0`) elaborates; `#check @eq_7_4` shows the binder order | as described in E1 and W1 |
| T6 | companion P from `nonneg_of_isWaveFunction` and E1 | passes |
| numerics | $\sum_kK^{\ast k}$ against (7.15), $t\in\lbrace0.1,1,3,10\rbrace$ | difference at most $2\cdot10^{-15}$ |

## Appendix: the refutation of `prop_7_2` (test T3)

Imports: `QSSEPtoKPZ.WhiteNoise.Prop72`, `QSSEPtoKPZ.Companions`, `Mathlib.Analysis.Calculus.BumpFunction.Basic`, `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct`. Then `open MeasureTheory ProbabilityTheory Filter Topology`, `open scoped NNReal ENNReal`, `namespace QSSEPtoKPZ`.

```lean
/-- The zero path. -/
noncomputable def zeroPath : C(Set.Icc (0 : ℝ) 1, FiniteMeasure ℝ) := ContinuousMap.const _ 0

lemma pathAt_zeroPath (t : ℝ) : ((pathAt zeroPath t : FiniteMeasure ℝ) : Measure ℝ) = 0 := by
  unfold pathAt zeroPath; split_ifs <;> simp

lemma limMart_zero (φ φt : ℝ → ℝ → ℝ) :
    limMart (fun _ : Unit => zeroPath) φ φt = fun _ _ => -φ 0 0 := by
  funext t ω; simp [limMart, pairFM, pathAt_zeroPath]

lemma limBracket_zero (φ : ℝ → ℝ → ℝ) :
    limBracket (fun _ _ (_ : Unit) => (0 : ℝ)) φ = fun _ _ => 0 := by
  funext t ω; simp [limBracket]

/-- `prop_7_2` as stated is refutable: the trivial data `Y ≡ 0`, `Z ≡ 0` satisfy all its
hypotheses (the martingales `M^φ ≡ -φ₀(0)` are constant), but (7.8) would force
`∫ g_1 f = 0` for every `f ∈ C_c^∞`. Uses only the companion W (`IsWalshIntegral.ae_eq`). -/
theorem prop_7_2_false (H : type_of% @prop_7_2.{0, 0})
    (W : type_of% @IsWalshIntegral.ae_eq.{0})
    {Ω'' : Type} {m'' : MeasurableSpace Ω''} {ν'' : Measure Ω''} [IsProbabilityMeasure ν'']
    {𝓖'' : Filtration ℝ≥0 m''} {S'' : ℝ → ℝ → Ω'' → ℝ} (hS'' : IsWhiteNoise 𝓖'' S'' ν'') :
    False := by
  have hmart : ∀ {φ φt : ℝ → ℝ → ℝ} {C : ℝ}, IsC13 1 φ φt C →
      HasBracket 1 (⊥ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit))
        (limMart (fun _ : Unit => zeroPath) φ φt)
        (limBracket (fun _ _ (_ : Unit) => (0 : ℝ)) φ) (Measure.dirac ()) := by
    intro φ φt C _
    rw [limMart_zero, limBracket_zero]
    refine ⟨⟨ae_of_all _ fun _ => continuousOn_const, fun _ _ => memLp_const _, fun s t _ _ => ?_⟩,
      fun _ _ => integrable_const _, ae_of_all _ fun _ => rfl,
      ae_of_all _ fun _ => monotoneOn_const, ae_of_all _ fun _ => continuousOn_const, fun s t _ _ => ?_⟩
    · rw [condExp_const (Filtration.le _ _)]
    · rw [condExp_const (Filtration.le _ _)]
  obtain ⟨𝒢b, S, -, hS, h78⟩ := H (Pr := Measure.dirac ()) (𝒢 := ⊥) (T := 1) one_pos
    (Y := fun _ : Unit => zeroPath) measurable_const (Z := fun _ _ _ => 0) measurable_const
    (fun _ _ _ => le_rfl) (by simp) (by simp [pathAt_zeroPath]) hmart hS''
  -- a bump function `f ≥ 0`, positive on `(-1, 1)`
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hX := h78 b b.contDiff b.hasCompactSupport 1 ⟨one_pos, le_rfl⟩
  simp only [mul_zero, ite_self, pairFM, pathAt_zeroPath, integral_zero_measure, zero_sub] at hX
  have h0 : IsWalshIntegral 𝒢b S ((Measure.dirac ()).prod ν'') (fun _ _ _ => 0) (fun _ => 0) := by
    have := IsWalshIntegral.block (𝓖 := 𝒢b) (S := S) (ν := (Measure.dirac ()).prod ν'')
      0 0 0 0 (fun _ => 0) le_rfl le_rfl measurable_const ⟨0, by simp⟩
    simp only [ite_self, zero_mul] at this; exact this
  have hae := W hS hX h0 (ae_of_all _ fun _ => rfl)
  have hc : ∫ x, heatKernel 1 x * b x = 0 := by
    obtain ⟨p, hp⟩ := hae.exists
    simpa using hp
  have hpos : 0 < ∫ x, heatKernel 1 x * b x := by
    have hcont : Continuous fun x => heatKernel 1 x * b x := by
      exact (by unfold heatKernel; fun_prop : Continuous fun x => heatKernel 1 x).mul b.continuous
    have hint : Integrable fun x => heatKernel 1 x * b x :=
      hcont.integrable_of_hasCompactSupport (b.hasCompactSupport.mul_left)
    rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (heatKernel_nonneg' 1 x) b.nonneg) hint]
    have : Metric.ball (0 : ℝ) 1 ⊆ Function.support fun x => heatKernel 1 x * b x := by
      intro x hx
      have hb : 0 < b x := b.pos_of_mem_ball (Metric.ball_subset_ball (by norm_num [b]) hx)
      have hg : 0 < heatKernel 1 x := by unfold heatKernel; positivity
      exact (mul_pos hg hb).ne'
    exact lt_of_lt_of_le (by simp) (measure_mono this)
  linarith
where heatKernel_nonneg' (t x : ℝ) : 0 ≤ heatKernel t x := by unfold heatKernel; positivity
```
