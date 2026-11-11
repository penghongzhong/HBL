# HBL revised 2.13 — minimal physical Hartree closure chain (2026-11-02)

## Strict count and theorem boundaries

- **Revised** 13-statement manuscript: **11/13**, previously audited 2.12 and 2.14; only 2.13 and the genuine Type-II existence/rate main theorem remain open.
- **Unmodified** manuscript: **9/13**. Historical 21-environment score: **9/21**.
- Do **not** count this ledger, unnumbered auxiliaries, or compiler module successes as original environments.
- The full Type-II concentration rate is **an output to derive**, never a hypothesis.

## Shortest surviving proof chain

1. **Actual same-PDE complex source + normalized local Green:** **ACCEPTED** revised 2.12:
   `HBL/TypeIIDynamicSelection/RevisedOneLayerPhysicalLocalSource.lean`,
   strict CI [41465373137](https://github.com/penghongzhong/HBL/actions/runs/41465373137), source commit `4aaeb115b98452a7b71577af422cf4024f9bf71b`.
   `ell*sqrt(q)=sqrt(T-t)` and fixed-annulus cutoff coverage are exact, **not** an assumed Type-II speed.
2. **Physical Kummer operator conjugation:** `HBL/TypeIIDynamicSelection/ActualHartreeKummerOperatorConjugacy.lean` verifies the frozen **linear** radial conjugacy
   `L_K[f(sqrt(q) z)] = [q Δ_rad f + (iR/2) f_R + b(mu,theta)f]_{R=sqrt(q)z}`.
   This MUST receive strict CI before marking even this substep verified.
   Remaining: full dynamic PDE time/phase/modulation plus nonlocal Hartree matching, not just the frozen operator.
3. **Both actual real channel sources and weighted estimates:** Existing `ActualOneLayerTwoChannelPDE.lean`, `ActualOneLayerSingleComplexWeightedSource.lean`, `ActualOneOrbitUniformWeightedRiesz.lean` prove source identity, conditional charge reconstruction, and the pure-radiation `ell^(2-sigma)` gain. Still OPEN: one-orbit `V_c+Z` offterminal nonlinear MIXED source estimates in the original weight space, with actual time/parameter derivatives. The terminal-only `ActualOneOrbitVcWholeWeightedL2Gain.lean` does **not** establish the offterminal source.
4. **Two endpoint trace compatibility and remote solve:** `ActualKummerTwoInterfaceObstruction.lean` establishes an iff **transfer compatibility**; normalized endpoint conditions force homogeneous coefficients to zero (`ActualKummerNormalizedNoHomogeneousFreedom.lean`). Need to construct the genuine far-field trace satisfying the transfer, **or** replace global `C^1` matching by original smooth cutoffs plus a rigorous weighted small commutator source. The local 2.12 does not make this disappear.
5. **Every newly generated source gains a strictly positive order:** Need case-by-case identities and quantitative weight bounds from the actual nonlinear 3D inverse-square quartic Hartree source, physical first/second cutoff, Kummer/Frobenius parameter derivatives, and remote Riesz interactions. Target `ord(Rnew) >= rho + min(delta, epsFlat, 2 betaMinus - 1, 1/2, rhoStar) > rho`. An abstract `GeneratedTerm` list whose order is supplied as a field is NOT enough.
6. **Actual finite recursion and quantitative profile:** Only after (3)–(5), instantiate real packet corrections in `HBL/FiniteProfile.lean`, derive source residual `O(s^-N)`, Jacobian `I_2+o(1)`, integrable slow Hessian/remainder, and the Kummer large-argument algebraic terminal branch in the stated radial Sobolev spaces. The old abstract `finiteProfile_recursion_certified` alone does NOT prove revised 2.13.
7. **Final energy convergence and Type-II rate selection:** Revised 2.14 physical complex energy gluing already strictly passed [41446185689](https://github.com/penghongzhong/HBL/actions/runs/41446185689) from actual three-region estimates. These estimates must be produced by revised 2.13. The main theorem must subsequently produce the selected physical PDE orbit and derive (not prescribe) the dynamical blowup rate.

## Noncircularity rule

Published high-regularity Hartree local theory and standard embedding facts can be explicitly cited as analytic input, but a full 2.13 matching/cancellation theorem (or equivalent) must **never** be inserted as an external assumption. Strict `#print axioms` audits alone do not certify that all declared mathematical input hypotheses are supplied by the actual PDE.

**Target next formal gain:** Complete the frozen linear physical-to-Kummer operator conjugacy in strict CI, then close the offterminal mixed weighted source/remote cutoff transfer. Only a complete physical statement of 2.13 may change the revised numerator from 11 to 12.


## 2026-11-08 strict physical Green continuation (addendum)

The exact **revised manuscript** count remains **11/13**: §2.13 and the
final PDE-derived Type-II theorem remain unaccepted. This dated addendum
updates the November 2 bridge ledger without retroactively editing its
historical findings.

- **Strict Success** [42531018076](https://github.com/penghongzhong/HBL/actions/runs/42531018076): the full original Hartree selected Green estimate; the real
  Cramer speed and actual physical source remain tied together.
- **Strict Success** [42531500587](https://github.com/penghongzhong/HBL/actions/runs/42531500587) and
  [42531450638](https://github.com/penghongzhong/HBL/actions/runs/42531450638):
  original zero-left spectral weighted-value/derivative and Cramer--Volterra
  slope; **Strict Success** [42535477786](https://github.com/penghongzhong/HBL/actions/runs/42535477786):
  unweighted slope only for the exact **inverse-linear** source class,
  not for the complete physical quartic Riesz source of order \(r^{-2}\).
- **Strict Success** [42532174429](https://github.com/penghongzhong/HBL/actions/runs/42532174429):
  same-source, same-real-speed corrected four-piece **three-C¹** joins;
  [42532363535](https://github.com/penghongzhong/HBL/actions/runs/42532363535):
  actual-source selected quadratic spectral defect and same three joins.
- **Strict Success** [42532174421](https://github.com/penghongzhong/HBL/actions/runs/42532174421):
  the **exact nonlinear finite four-piece PDE telescope only**, not a
  decay estimate. The stronger exact transitive-axiom allowlist and
  current-dependency rerun were triggered at
  [42536552509](https://github.com/penghongzhong/HBL/actions/runs/42536552509).
- **Strict Success** [42533177432](https://github.com/penghongzhong/HBL/actions/runs/42533177432):
  a moving Green source/endpoint mixed Lipschitz cross bound deduced
  from a *visible bounded physical source time-derivative hypothesis*.
  This does not prove that bound from the PDE trajectory.
- **Pending dedicated replay**: the separate *original physical quartic
  Riesz* no-left-radius energy-weighted slope
  [42536419967](https://github.com/penghongzhong/HBL/actions/runs/42536419967);
  selected derivative from critical scaled Hartree orbit
  [42536615928](https://github.com/penghongzhong/HBL/actions/runs/42536615928);
  three original Riesz source-time derivatives composed with actual real
  Cramer speed
  [42536770197](https://github.com/penghongzhong/HBL/actions/runs/42536770197).
  These are **not** recorded as accepted before Success and exact audits.

**Remaining essential edges:** the actual physical orbit must furnish
the derivative/weighted norms for all three original Riesz interactions;
one must control the moving Kummer basis, matching endpoints and real
selected speeds; prove the **complete four-domain nonlinear PDE
residual gains a strictly positive order** with parameter Lipschitz
control; induct on genuine finite physical profiles; then derive
the Type-II scale law from the resulting Hartree dynamics.
No auxiliary successful theorem can increase the original-environment numerator.


## 2026-11-09 matched-shell improvement versus the physical shell-volume barrier

The raw job log of CI [42554311787](https://github.com/penghongzhong/HBL/actions/runs/42554311787),
job **128956509687**, verified the actual same-background radial-conjugated
Hartree shell norm at commit `903b870`; original audit:
Lean 4.35.0-rc3, pinned Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`,
`--trust=0 -DwarningAsError=true`, exact `#check` and `#print axioms`,
only `propext`, `Classical.choice`, `Quot.sound`, artifact **13647485540**.
This *does not* upgrade §2.13: the coarse pointwise shell bound incurs
`20 R^(13/4)`, which for `R≈ell^-1` and `ell^(5/2)`
loses `ell^(-3/4)` rather than gaining a positive scale order.

**Non-circular improvement identified from already present Lean code.**
`ActualHartreeMatchedShellWeightedGain.lean` proves, on a
*source-matched C¹ interface* with the same scaled Kummer source equation
and its stated regularity and coefficient smallness,
\[
  \| \mathbf 1_{(R,2R)}\,r\, [\mathcal L_K(\chi_R(u-v))
     -\chi_R\mathcal L_K(u-v)]\|_{L^{2,7/4}}
  \le 20C [C_{\rm in}R^{-3/4}
    + C_{\rm K}(\mu,\theta)R^{13/4}/a^2]N_F.
\]
The `R^-4` pointwise mismatch gain is produced by **matching + common
differential equation before** applying the shell norm.
For the original canonical Hartree overlap,
`R=L/2`, `L=ell^(-1/16)>=6` and the actual uniquely selected
source condition `a>=L^3` imply
`R^(13/4)/a² <= R^(-11/4)/64 <= R^(-3/4)/64`.
Hence `R^(-3/4)=2^(3/4)*ell^(3/64)` is a genuine **scale**
gain, without assuming a blowup law. This deduction still requires
uniform spectral coefficients, the full original shell smallness
condition, and the matching equation for the **spectrally corrected**
field; a positive `ell` power is not automatically a
renormalized-time `s^(-delta)` power.
The proof accepts no independent mismatch amplitude as input.

**Next original-PDE closure gate:** instantiate that matched-shell
theorem on the *actual spectrally corrected* four-piece field.
Its exterior equation has a real quadratic spectral defect, so
first extract the exact extra defect and genuine moving time/speed
derivatives; bound all nonlocal cross-region sources and parameter
differences in their own source norms; then iterate and dynamically
derive the Type-II scale. Until that concrete same-source reduction and
time-positive original PDE norm estimate are proved, **11/13**.

The initial spectral 3-C¹ failures `42531033761/768` and joint
`42531467165/166` were traced to raw Lean elaboration errors:
`HasDerivAt` pullback mismatch and a redundant `dsimp`.
The no-progress `dsimp` is absent on the current source;
pullback source repair committed as
[068db26b](https://github.com/penghongzhong/HBL/commit/068db26babe4ba8fdf8db6c92ef05d742e9a61d2).
Current strict workflows **42558721414**, **42558721545**,
**42558721526**, **42558721390**, **42558721475** were triggered
and must be independently verified before attributing Success.
Exact selected spectral quadratic replays **42558807332**
and **42558807364**, commit
[96c00fd0](https://github.com/penghongzhong/HBL/commit/96c00fd0b0fdd5fd347c6ce8836e672c3ec44d9f),
are likewise **not yet accepted** without original jobs and axiom
reports. These are all auxiliaries, not original environments.


## 2026-11-09 later strict reruns, proof repair, and exact spectral-shell mismatch

- Raw [42558807364](https://github.com/penghongzhong/HBL/actions/runs/42558807364) **Success** at `96c00fd0`, original job `128970433558`, artifact `13648514548`: unique true Hartree source/selected-speed/frozen weighted spectral quadratic target. Its strict job invokes `--trust=0`, `warningAsError` and exact `#check` / `#print axioms`, with a three-axiom allowlist.
- Raw [42558721390](https://github.com/penghongzhong/HBL/actions/runs/42558721390) **Success** for the derivative of the actual selected quartic source from an explicitly differentiable scaled orbit; [42558721475](https://github.com/penghongzhong/HBL/actions/runs/42558721475) **Success** for the real selected moving Green cross estimate under its visible physical-time-derivative bound. Neither produces the missing PDE trajectory norm bounds.
- Raw [42558807332](https://github.com/penghongzhong/HBL/actions/runs/42558807332), [42558721414](https://github.com/penghongzhong/HBL/actions/runs/42558721414), [42558721545](https://github.com/penghongzhong/HBL/actions/runs/42558721545), and [42558721526](https://github.com/penghongzhong/HBL/actions/runs/42558721526) **FAILED** on the *same actual upstream elaboration error* at `ActualHartreeSpectralCorrectedFourPieceThreeC1.lean:98:4`: a `HasDerivAt` pullback represented by an explicit lambda was not simplified to the named `actualOriginMatchedKummerPullback`. The last workflow had already built its separate original nonlinear PDE telescope dependency; that is **not** full strict acceptance of the composite.
- Commit [d2bfb112](https://github.com/penghongzhong/HBL/commit/d2bfb1120a6d917891e24f595f4b0ddc05b5661e) changes the proof by converting the goal to the literal matched-Kummer pullback lambda *before* scalar normalization. New strict runs [42561772359](https://github.com/penghongzhong/HBL/actions/runs/42561772359), [42561772339](https://github.com/penghongzhong/HBL/actions/runs/42561772339), and [42561772340](https://github.com/penghongzhong/HBL/actions/runs/42561772340) were triggered, but **must not be credited until raw Success and axiom audit**.

**Decisive mathematical constraint:** the matched Green correction satisfies
`L_K w_delta = F_adj - delta*u0`, whereas the shifted-operator defect is only `(L_K+delta)w_delta - F_adj = -delta*u1` (quadratic after the Volterra bound). Thus, after physical pullback and the actual two-channel inner field,
```text
L_K^a (u - v_delta) = E_in - M_delta,
M_delta(y) = [Fp(y) + i Fm(y)]/y
          + a^(-2) [F_adj(y/a) - delta*u0(y/a)].
```
The `ActualHartreeMatchedShellWeightedGain` hypothesis is **not automatically satisfied**: it would require `M_delta = 0`; the actual PDE instead must bound `M_delta` in the conjugated, moving-shell `L^{2,7/4}` source norm, including derivative and two-parameter Lipschitz costs. A quadratic defect for the *shifted* Kummer operator cannot silently replace the generally first-order `-delta*u0` contribution in the *original* Hartree PDE. The source decomposition is recorded in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex` as a next proof obligation, not as a new Lean-certified theorem.

**Formal original manuscript acceptance remains 11/13.** Only complete revised §2.13 and the terminal dynamical Type-II theorem can increase it.


## 2026-11-09 strict spectral integration and exact true Hartree plateau cancellation

Confirmed independent original GitHub Actions conclusions at repaired source `d2bfb1120a6d917891e24f595f4b0ddc05b5661e`:

| Run | Exact strict target | Original job / artifact | Transitive axioms |
|---|---|---|---|
| [42561772359](https://github.com/penghongzhong/HBL/actions/runs/42561772359) **Success** | `actual_Hartree_spectral_inner_four_piece_three_C1_joins` | `128979543706` / `13649649805` | `propext`, `Classical.choice`, `Quot.sound` |
| [42561772339](https://github.com/penghongzhong/HBL/actions/runs/42561772339) **Success** | `actual_Hartree_true_source_selected_spectral_four_piece_three_C1` | `128979544093` / `13650137059` | same three |
| [42561772340](https://github.com/penghongzhong/HBL/actions/runs/42561772340) **Success** | `actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes` | `128979543745` / `13650455896` | same three |
| [42562474659](https://github.com/penghongzhong/HBL/actions/runs/42562474659) **Success** | `actual_Hartree_true_source_selected_spectral_quadratic_and_three_C1` | `128981699599` / `13649894367` | restricted by strict allowlist |

The first three artifacts were downloaded and their `audit.log` directly parsed; each reports only the three listed axioms and a **zero-byte `strict.log`**. The fourth CI strictly asserts the exact same three-axiom allowlist. All four jobs use Lean 4.35.0-rc3, pinned Mathlib, `--trust=0`, `-DwarningAsError=true`, exact `#check` and `#print axioms`.

More precise source analysis: `ActualHartreeMomentLockedPlateauSource.lean` ALREADY proves the original full nonlocal Hartree inner/outer source identity under the same physical `z` and the same two real speeds on `0<y≤L`:
```text
S_inner_adjusted(y) + a^(-2) F_adjusted(y/a) = 0.
```
Combining this with the ORIGINAL unshifted spectral equation gives
```text
M_delta(y) = -a^(-2) delta * u0(y/a),       0<y≤L,
L_K^a(u-v_delta) = E_inner + a^(-2) delta*u0(y/a).
```
This applies exactly to the backward shell `R=L/2`, `[R,2R]=[L/2,L]`: all actual quartic source and two modulation-speed terms cancel there. It is **incorrect** to replace the surviving first-order term with the smaller shifted-operator quadratic defect. The original weighted Green source estimate controls `u0(x)` for `x∈[L/a,B]`, whereas the shell needs `x∈[L/(2a),L/a]` **to the left of that interval**. This dyadic backward extension with no hidden left-radius loss, followed by the moving time/Lipschitz bound, is now the exact next analytical bottleneck.

New source-faithful spectral `ActualHartreeOnePhysicalSourceSpectralQuadraticThreeC1.lean` specializes both Fredholm channels to the same original quartic Hartree `z`; its separate strict CI is [42562872297](https://github.com/penghongzhong/HBL/actions/runs/42562872297). The exact original spectral operator lemma `ActualHartreeMatchedSpectralOriginalPDEMismatch.lean` is in [42562774111](https://github.com/penghongzhong/HBL/actions/runs/42562774111); combining it with the plateau identity in `ActualHartreePlateauSpectralOriginalSourceCancel.lean` is under [42563426525](https://github.com/penghongzhong/HBL/actions/runs/42563426525). **Do not count any of these last three as accepted before raw Success and individual axiom audit.** The new plateau source reduction is fully recorded in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`.

**Original manuscript environment count unchanged: 11/13**. A genuine full four-region `s^{-rho-kappa}` PDE residual with moving basis, speed and interface derivatives, parameter Lipschitz, and the derived finite Type-II rate remains unproved.

## 2026-11-09 source-specific backward spectral shell CI and raw failure audit

- Strict predecessor [42562872297](https://github.com/penghongzhong/HBL/actions/runs/42562872297), original job `128982904463`: **Success** for one physical quartic source, the real selected pair, frozen spectral correction and the three (C^1) interfaces. [42562774111](https://github.com/penghongzhong/HBL/actions/runs/42562774111): **Success** for the original unshifted Kummer PDE mismatch. [42561772340](https://github.com/penghongzhong/HBL/actions/runs/42561772340), original job `128979543745`: **Success**, with raw log affirming `--trust=0` and exactly `propext, Classical.choice, Quot.sound`, for the exact original four-piece PDE telescope. None is a positive-order residual theorem.
- Raw [42563548889](https://github.com/penghongzhong/HBL/actions/runs/42563548889), original job `128985003559`: **Failure**, exact compiler message `ActualHartreeBackwardMatchedValueGain.lean:118:0: unterminated comment`. The documentation string `H+/-` accidentally opened a nested `/-` Lean block comment. Replaced it with `H-plus and H-minus`, [commit fa3d78fb](https://github.com/penghongzhong/HBL/commit/fa3d78fb7681df3ee6c49cce1e17bbf079aae2e3); fresh [42564376709](https://github.com/penghongzhong/HBL/actions/runs/42564376709) requires raw success and axiom audit.
- Raw [42563426525](https://github.com/penghongzhong/HBL/actions/runs/42563426525), original job `128984637783`: **Failure**, exact Lean `warningAsError` message at `ActualHartreePlateauSpectralOriginalSourceCancel.lean:92:18: Variable name hell is not explicitly referenced`. Renamed binder `_hell`, [commit f379fbfc](https://github.com/penghongzhong/HBL/commit/f379fbfc55e714efe6b5e28789b8b6370f74bbbd), pending [42564417114](https://github.com/penghongzhong/HBL/actions/runs/42564417114).
- New physical-source composite `ActualHartreePhysicalPlateauSpectralShellSource.lean`, [commit c3ba5d79](https://github.com/penghongzhong/HBL/commit/c3ba5d79ec0bb794b41b779bc221b348f306c603), now explicitly constructs the adjusted real and imaginary quartic Hartree source memberships, genuine matching jet and original on-plateau Kummer equation, then feeds them into the first-order original spectral shell norm with the full (r)-conjugation and (L^{2,7/4}) volume. It assumes global Green-pullback measurability, **not** a free size envelope. The new strict workflow [42564445964](https://github.com/penghongzhong/HBL/actions/runs/42564445964) is **pending**; the predecessor shell CI [42564441887](https://github.com/penghongzhong/HBL/actions/runs/42564441887) is also pending. Both run exact `#check`/`#print axioms`, `--trust=0`, warning-as-error and the pinned Lean/Mathlib versions. Pending means **not accepted**.

**Mathematical remaining conditions:** independently derive and bound physical Green measurability where needed, the common uniquely selected (p(s)) and (delta(s)) at each time, moving (C^1) Kummer basis/interface/selected-speed derivatives, the outer (y>L) true nonlocal Riesz feedback, original global source norm in positive renormalized time and two-parameter Lipschitz form. Only then can an actual finite-layer PDE iteration and dynamical Type-II speed be proved. **Original 13-environment count remains 11/13 (84.62%).**


### 2026-11-09 all-finite backward spectral Neumann direction (new strict target)

At branch commit \`df33da3f\` a *genuine original Cramer-Green operator* finite recursion was introduced in
\`HBL/TypeIIDynamicSelection/ActualHartreeBackwardSpectralNeumannFiniteGain.lean\`,
with dedicated pinned workflow
\`.github/workflows/hbl-213-backward-spectral-neumann-finite-gain.yml\`.
The lemma iterates the actual zero-jet Green field
\`u_(n+1)=G_K0[delta*u_n;0,0]\`; no independent positive-order
field envelope is inserted at any step. The base input is the
already source-produced original matched field's backward-shell
value \`D_R\`, plus explicitly stated Green-source interval-integrability.

The new **target** (not accepted until its raw job and exact axiom audit
show Success) is the all-\`n\` estimate
\`sup_[r0/2,r0] |u_n| <= (2 G² r0 |delta|)^n D_R\`.
Source-level induction: the actual source \`delta*u_n(x)\` obeys
\`|delta*u_n(x)| <= (r0 |delta| (2 G² r0 |delta|)^n D_R)/x\`
because \`x<=r0\`; invoke the already strictly accepted reverse
Wronskian/Cramer theorem at each step.

Analytically, the physical conjugated shell then satisfies
\`||1_(R,2R) y a^(-2) delta u_n(y/a)||_(L^{2,7/4})
<= (5/16) (G²/2)^n R^(-(11/4+2n)) |delta|^(n+1) D_R\`
when \`a>=(2R)^3\`; the \`n=1\` coefficient is precisely
\`(5/32)G²R^(-19/4)\`, matching the separately strict one-step
source theorem. This all-\`n\` scale consequence and the
operator-residual telescoping are **not yet separate strict Lean targets**.

Only under *additional PDE-produced* time decay
\`|delta|≲s^(-(2beta-1))\`, \`D_R≲ell^(1/8)\` and
\`ell≲s^(-beta)\` does this family give the conditional order
\`rho_n=(n+1)(2beta-1)+(19+8n)beta/64\`. The finite spectral
recursion cannot be silently substituted for the *nonlinear*
finite physical Hartree profile in the retained original 2.13.
All moving-time, outer Riesz feedback, parameter-Lipschitz, global
source norm and PDE-driven rate obligations remain; the formal
13-environment count is **11/13**.

**C¹ gluing caveat:** The iterated zero-left Green correction has zero Cauchy jet at its *left* anchor by construction. It generally has a nonzero value/derivative at the *far-field* matching endpoints. Consequently it does not, by itself, propagate the accepted three physical C¹ interfaces; each new spectral correction requires a same-source outgoing/tranmission re-match and the true nonlocal quartic cross terms generated between layers. A finite Neumann sum of the frozen operator is **not** a finite nonlinear Hartree profile.

### 2026-11-09 exact backward Wronskian slope (strict pending)

New original-Cramer source module `HBL/TypeIIDynamicSelection/ActualHartreeBackwardZeroLeftSpectralVolterraSlope.lean` commits `1082defe`, strict workflow `hbl-213-backward-zero-left-spectral-volterra-slope.yml` commit `9c937adc`. It proves candidate identity `r²u'(r)=(r y'_K-y_K)[A_K(r)-A_K(r0)]+(r x'_K-x_K)B_K(r)` **also below** the original left anchor and candidate inverse-linear bound `|r²u'(r)|≤2(r0+1)G²M(r0-r)` with backward source integrals, no hidden negative powers of r0. Strict CI is pending: do not count as validated until raw job `Success`, exact #check and #print axioms. This provides a derivative counterpart to the successful backward value theorem, still not the physical time-dependent residual or nonlinear finite-profile recursion; manuscript acceptance 11/13.

### 2026-11-09 first all-finite reverse Green iteration strict audited

The **base** genuine finite spectral Neumann iteration theorem `actual_Hartree_backward_spectral_Neumann_all_finite_value_gain` has now achieved direct original [CI 42572303237](https://github.com/penghongzhong/HBL/actions/runs/42572303237) **Success** on source SHA `df33da3fbd00d08cc94b4127080654cbbeb8b924`, job `129012205405`, artifact `13654102892`. Original raw log confirms `lake env lean --trust=0 -DwarningAsError=true`, exact target `#check` and `#print axioms`, and `Transitive axiom allowlist accepted: ['propext', 'Classical.choice', 'Quot.sound']` with no `sorryAx`/admit; original `strict.log` empty. The *stronger* source-faithful Hartree-Cramer-Jet specialization was added later and is separately **pending** original strict CI 42572780271; this old success must **not** be imputed to it. No original §2.13 environment acceptance; 11/13 unchanged.


### 2026-11-09 backward radial slope strict failure and repair; current acceptance boundary

- Rechecked live branch HEAD and original strict workflow log. The pinned
  [CI 42573485568](https://github.com/penghongzhong/HBL/actions/runs/42573485568)
  failed at `ActualHartreeBackwardZeroLeftSpectralVolterraSlope.lean:34:17`
  with the Lean warning-as-error `Variable name ha is not explicitly referenced`.
  This is an unused proof binder, **not** a mathematical counterexample or
  successful axiom audit. Source commit
  [79652cdb](https://github.com/penghongzhong/HBL/commit/79652cdb23f19f188a60a3c66a06a3f9dcfe3ef1)
  changes only that binder to `_ha`, preserving the exact theorem type;
  new pinned strict [CI 42574795691](https://github.com/penghongzhong/HBL/actions/runs/42574795691)
  was triggered and must not be accepted before its raw job and exact three-axiom audit.
- The stronger true derivative estimate for **every finite spectral iterate**
  in `ActualHartreeBackwardSpectralNeumannFiniteC1.lean` imports the
  repaired slope module. Commit
  [31502ca3](https://github.com/penghongzhong/HBL/commit/31502ca300c885f1e0f371a1573111281d13d3c2)
  fixes its workflow's missing dependency-trigger paths (slope and finite-value
  producer). Independent pinned [CI 42574812863](https://github.com/penghongzhong/HBL/actions/runs/42574812863)
  is pending; the earlier [42574117292](https://github.com/penghongzhong/HBL/actions/runs/42574117292)
  was still building at recheck. **No success is imputed to these CI runs.**
- The true Green finite-value producer [CI 42572780271](https://github.com/penghongzhong/HBL/actions/runs/42572780271)
  is directly verified **Success**, original job `129013716503`, artifact
  `13654546805`. The raw job invokes pinned Mathlib and Lean,
  `--trust=0 -DwarningAsError=true`, exact `#check`/`#print axioms`, and
  an explicit allowed-axiom parser; the auxiliary status is **not** original 2.13.

Even an all-finite **spatial** spectral Neumann bound, with its true
radial derivative, does not control the new nonlinear Riesz cross terms,
far-field outgoing C¹ rematching, moving Kummer basis/endpoint and real
selected-speed derivatives, full positive **time** order and parameter
Lipschitz. In particular the global (G) in the Neumann factor
`2 G² r0 |delta|` must be tracked **uniformly along the moving physical
orbit** before it can be called a small dynamical factor. Original revised
strict theorem count remains **11/13**; the complete physical profile and
PDE-derived Type-II main theorem remain outstanding.


**Additional raw C1 audit-parser correction (2026-11-09).** The original [CI 42574117292](https://github.com/penghongzhong/HBL/actions/runs/42574117292), job `129017876206`, compiled through the strict target but **failed its final audit script** with `AssertionError: expected one exact axiom report: 2`. Its audit file intentionally contained two distinct `#print axioms` declarations, so the script expectation was erroneous. Commit [f4c65bec](https://github.com/penghongzhong/HBL/commit/f4c65bec0cf74d0a7f90c0fe4baeb11dcfef35cd) corrects `len(reports)==1` to `len(reports)==2` while still individually checking the exact three-axiom allowlist for both declarations; new strict [CI 42575319719](https://github.com/penghongzhong/HBL/actions/runs/42575319719) is **pending**. The prior failure is not a Lean proof failure, but neither is it formal acceptance. Revised original count **11/13**.

### 2026-11-09 completed raw Cramer-slope and finite weighted C¹ audit; new physical quadratic shell specialization

- **Strict Success** [42574795691](https://github.com/penghongzhong/HBL/actions/runs/42574795691), original job **129019975598**, source commit `79652cdb`. The exact original zero-left backward radial Wronskian slope **identity** and **bound** were both checked; the original raw log reports respectively `[propext, Classical.choice, Quot.sound]` and the same three with Lean universe annotations.
- **Strict Success** [42575319719](https://github.com/penghongzhong/HBL/actions/runs/42575319719), original job **129021613235**, source commit `f4c65bec`. The exact all-finite original backward spectral Neumann radial **C¹** target and its Wronskian prerequisite were each `#check`-ed and `#print axioms`-audited. The raw log reports respectively `[propext, Classical.choice, Quot.sound]` and `[propext, Classical.choice.{u}, Quot.sound.{u}]`. Strict `--trust=0`, warning-as-error, pinned Lean 4.35.0-rc3 and Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`. This resolves the old unused-binder and duplicate-axiom-parser blockers but **not** original §2.13.
- Added [actual physical plateau moving spectral quadratic backward-shell target](https://github.com/penghongzhong/HBL/blob/hbl-213-spectral-c1-trace-20261109/HBL/TypeIIDynamicSelection/ActualHartreePhysicalPlateauMovingSpectralQuadraticShellGain.lean) in commit `54c8a65`; new strict workflow in commit `d43717be`, [CI 42589214801](https://github.com/penghongzhong/HBL/actions/runs/42589214801). **Pending:** its source-faithful plateau-to-backward-Green composition must actually compile. It removes the separate same-source matching hypothesis from the quadratic shell theorem by deriving it from the genuine physical quartic Hartree plateau equation and original two Fredholm source channels. The quantitative target is
  `||1_[R,2R] y a^(-2) delta u1(y/a)||_(L^{2,7/4}) <= 20 R^(13/4) a^(-2)|delta| (2 G²(L/a)|delta|) D_R`
  for the genuine `u1=G_K[delta*u0;0,0]`, with `R=L/2`. Source continuity, weighted membership, Green-source interval integrability, basis bounds, and measurability remain visible analytical hypotheses; no positive time exponent is an input.
- This specialization must be connected to [the exact current-coefficient plateau cancellation](https://github.com/penghongzhong/HBL/blob/hbl-213-spectral-c1-trace-20261109/HBL/TypeIIDynamicSelection/ActualHartreePlateauMovingSpectralQuadraticCancellation.lean), which removes the *first-order* mismatch for the **current** Kummer operator. The source norm is still only a **frozen-shell** statement. Full moving PDE control of all four zones, all nonlocal cross interactions, parameters, real-speed derivatives and Type-II rate selection **remain open**.

**Original revised paper: strictly 11/13**, irrespective of these auxiliary statuses.

### 2026-11-09 actual source composition first build and exact Lean repair

- Original [CI 42589214801](https://github.com/penghongzhong/HBL/actions/runs/42589214801), job **129066417182**, failed at **line 205, column 31** of `ActualHartreePhysicalPlateauMovingSpectralQuadraticShellGain.lean`. The genuine elaborator error is an **application type mismatch**: the proven physical plateau source equality was stated for local `v=actualOriginMatchedKummerPullback ... (L/a)`, while the upstream source-weighted theorem expects the syntactically expanded `actualOriginMatchedKummerPullback ... (2*R/a)` at `2R=L`. All 4237 upstream dependencies built, including the original quadratic weighted Green theorem. This is not an analytic contradiction or a successful composite theorem.
- Commit [4d80785f](https://github.com/penghongzhong/HBL/commit/4d80785f87a5955b75cab12a3581cab2ca66b33b) adds explicit `hSame'`, rewriting the actual same-source equality with `hTwoR:2R=L`, then passes it into the existing physical weighted Green estimate, leaving the original mathematical statement unchanged. Triggered strict [CI 42591217589](https://github.com/penghongzhong/HBL/actions/runs/42591217589), **pending independent original job Success and exact transitive axiom audit**.
- Original manuscript **11/13** unchanged. Even after this frozen-shell spatial source-norm bridge, true moving full four-zone nonlinear Hartree PDE positive *time* order, parameter Lipschitz, real finite profile recursion, and dynamically derived Type-II scale are not yet established.

### 2026-11-09 genuine canonical-jet integrability repair (strict pending)

Original [CI 42591217589](https://github.com/penghongzhong/HBL/actions/runs/42591217589), job **129073011766**, is a **failure**, not proof acceptance. The raw compiler log pinpoints the last source module at **212:44**: the hInt' witness gives IntervalIntegrable for the local jet J at L/a, but the downstream Green theorem explicitly requires actualMomentLockedCanonicalInnerJet at 2*R/a. The equality 2*R=L is a mathematical rewrite, not automatic definitional equality under the dependent integrability binder. All 4237 upstream imports built; the original mathematical estimate is not thereby refuted.

Commit [33abb6c0](https://github.com/penghongzhong/HBL/commit/33abb6c060f9356af27a40cf8d2a9db0ad5ac56b) changes only the local proof abbreviation to the literal 2*R/a anchor, not the theorem statement or physical source. New pinned strict [CI 42595684617](https://github.com/penghongzhong/HBL/actions/runs/42595684617) is **pending original Success, exact #check and transitive allowed-axiom audit**. Independently accepted [CI 42575319719](https://github.com/penghongzhong/HBL/actions/runs/42575319719) proves all-finite backward radial C¹, not this source-specialized composite. Revised **original 11/13**; §2.13 and PDE-derived terminal Type-II theorem open. The full nonlinear moving-time weighted residual and parameter-Lipschitz estimates remain indispensable; frozen-shell Neumann powers alone cannot give positive time order.


### 2026-11-09 direct source-to-quadratic spatial shell: strictly accepted; cubic-power target pending

- [Strict CI 42595684617](https://github.com/penghongzhong/HBL/actions/runs/42595684617) **Success**, original job **129087607890**, original evidence artifact **13664491091**; source commit `33abb6c060f9356af27a40cf8d2a9db0ad5ac56b`. It checks the exact type of `actual_Hartree_true_plateau_moving_spectral_quadratic_backward_shell_norm`, the **actual same quartic Hartree source** with both real Fredholm channels and its fixed-slice quadratic spectral Volterra correction. Strict `lake env lean --trust=0 -DwarningAsError=true` and `#check`/`#print axioms`: the raw original job prints `Transitive axiom allowlist accepted: ['propext', 'Classical.choice', 'Quot.sound']`. No assumed positive time order, no independently prescribed envelope, no Type-II rate.
- The **geometric scaling consequence** of that bound and the already physical separation `a >= L^3`, `L=2R`, is
  `20 R^(13/4) a^(-2)|delta|(2G²(L/a)|delta| D_R) <= (5/32)G²R^(-19/4)|delta|²D_R`
  whenever `D_R>=0`. This is strictly a **spatial scale gain** (not an `s`-gain); `D_R` is the existing same-source weighted Fredholm budget, not a new free envelope. A precise Lean scalar lemma `actual_Hartree_quadratic_backward_shell_cubic_spatial_factor` was appended at commit `a81d44eb` and put under the pinned exact audit in workflow commit `6885164a`. Runs [42602025843](https://github.com/penghongzhong/HBL/actions/runs/42602025843) and [42602051763](https://github.com/penghongzhong/HBL/actions/runs/42602051763) were **in progress** at this audit; the scalar lemma is **not counted** before raw Success and axiom review.
- Remaining unchanged: global nonlinear cross-region source, moving Kummer basis and C¹ interface derivative, original PDE time-positive weighted remainder and parameter Lipschitz, genuine finite nonlinear profile and dynamically selected Type-II blowup. Revised **11/13**, §2.13 and final original theorem open.


### 2026-11-09 source-to-cubic negative-radius composite target: strict audit pending

- Prior strict proof [42595684617](https://github.com/penghongzhong/HBL/actions/runs/42595684617), original job `129087607890`, evidence `13664491091`: the same actual quartic physical Hartree source produces the quadratic zero-Cauchy spectral Volterra shell norm. Exactly allowed axioms `propext`, `Classical.choice`, `Quot.sound`.
- Composite source commit [931eec371](https://github.com/penghongzhong/HBL/commit/931eec3713fe1d2fc7ac1d7e8c5d3ccce227eda5) now derives **from the concrete physical Fredholm budget** that `D_R >= 0` and combines `a >= L^3`, `L=2R` with the literal original source norm to target `(5/32) G^2 R^(-19/4) |delta|^2 D_R`. It does **not** assume source-envelope magnitude, a positive time order, or a blowup rate.
- The exact `#check` and `#print axioms` audit for all three source/scalar/composite declarations is configured by [9d55ccdda](https://github.com/penghongzhong/HBL/commit/9d55ccdda242851867ef4378e39a9ca3a030585a); [strict CI 42603288411](https://github.com/penghongzhong/HBL/actions/runs/42603288411) is **pending**. Its new composite is not yet accepted and it does not count toward the original 13 environments.
- Remaining main-chain producer is a complete full-original four-region Hartree PDE moving-time weighted residual and parameter-Lipschitz estimate (including nonlocal feedback and true moving C1 interfaces), followed by actual generated-source classification and finite physical recursion, and the separate PDE-selected Type-II dynamic orbit. **Original acceptance 11/13 (84.62%).**


**2026-11-09 direct strict replay and repair:** Runs
[42602025843](https://github.com/penghongzhong/HBL/actions/runs/42602025843)
and [42602051763](https://github.com/penghongzhong/HBL/actions/runs/42602051763)
**FAILED** the *new scalar* declaration at
`ActualHartreePhysicalPlateauMovingSpectralQuadraticShellGain.lean:255:27`:
the raw Lean rewriter transformed the entire left expression to
`(R ^ 1) ^ (13/4) * R ^ 1 = (R ^ 1) ^ (17/4)`,
so no direct `R^p*R^q` pattern remained. This is a proof elaboration
failure, **not** a counterexample or a failure of the already strictly
accepted source theorem at earlier commit `33abb6c0`.
Commit [915e8952](https://github.com/penghongzhong/HBL/commit/915e8952ef165118a0e6d33489ed147ca09eaf7d)
repairs the exact `R^{13/4}R=R^{17/4}` step with
`Real.rpow_add_one`, instead of rewriting every occurrence of `R`.
New pinned [CI 42603968381](https://github.com/penghongzhong/HBL/actions/runs/42603968381)
is **pending** and includes precise three-theorem `#check` /
`#print axioms` audits. A source-composed
`actual_Hartree_true_plateau_moving_spectral_quadratic_cubic_shell_gain`
has also been added in `931eec37`, but it remains **unaccepted until
the newer strict CI succeeds**. No original environment is closed:
**11/13**.


### 2026-11-09 10:57 UTC exact source-to-cubic proof repair

- [CI 42603288411](https://github.com/penghongzhong/HBL/actions/runs/42603288411), raw job `129112754147`, evidence `13667028657`: **failure**, with two precise compiler errors on the *new composite source-to-cubic target*: (i) pre-repair raw real-power rewrite at line 255; (ii) `hBound.trans hSpatial` at line 425 failed because the source norm groups `((a^2)^-1 * |delta|) * (2 G^2 ...)` as a nested factor while the scalar cubic lemma left-associates multiplication. Neither error changes the mathematical bound.
- The scalar-power rewrite is corrected by [915e8952](https://github.com/penghongzhong/HBL/commit/915e8952ef), original follow-up [CI 42603968381](https://github.com/penghongzhong/HBL/actions/runs/42603968381) independently confirms the **scalar rewrite no longer fails**; its sole raw remaining compiler error is the second source-composite multiplication association at line 427, artifact `13666464203`.
- [a5dcde496](https://github.com/penghongzhong/HBL/commit/a5dcde496232fd90e8f7c71bc5c81914e3b10143) repairs this second error with a separate `hSpatialAssoc` ring-normalized inequality and a genuine `hBound.trans` chain. Strict three-target rerun: [CI 42605032312](https://github.com/penghongzhong/HBL/actions/runs/42605032312), pending original job `129118702633`. This composite must not be counted successful before original strict log and exact axiom readback.
- The underlying source-specific *quadratic* physical shell bound remains strictly accepted at [CI 42595684617](https://github.com/penghongzhong/HBL/actions/runs/42595684617), original job `129087607890`. Original manuscript **11/13**; the missing time-dependent all-region Hartree residual, Lipschitz, actual finite recursion, and dynamical Type-II rate have not been proved.


### Operator-scope warning (unshifted versus shifted) — 2026-11-09

The already existing **actual physical original plateau** proofs
`actual_Hartree_matched_spectral_original_unshifted_source` and
`actual_Hartree_plateau_original_Kummer_PDE_spectral_source`
force the distinction:
`L0 (u0-u1) - Fadj = -delta*u0`, whereas
`(L0+delta)(u0-u1) - Fadj = -delta*u1`.
The new `R^(-19/4)|delta|^2 D_R` estimate concerns the **shifted-operator**
quadratic correction. It does not close the original unshifted PDE unless
the moving physical operator is *proved to be* that shifted operator and
the complete nonlocal/time-dependent remainder has been accounted for.
For the physically unshifted plateau, the independent already-proved
source-faithful norm
`actual_Hartree_true_plateau_original_spectral_shell_source_norm`
retains the first-order `-delta*u0`, with `20 |delta| D_R R^(-3/4)`.
This is a main-chain mathematical gate, not a bookkeeping choice.
No extra original 13-environment acceptance is warranted.

### 2026-11-09 11:38 UTC — latest strict replay, linter repair and main-chain scope
- Earlier four-piece three-C1 and telescope runs 42531033761/768 and 42531467165/166 **failed on historical commits**; corrected replacements 42561772359, 42561772339, 42561772340 and independent exact-axiom telescope replay 42536552509 **succeeded**. The last raw job 128902012127 reports only propext, Classical.choice and Quot.sound. Telescoping is an identity, not a positive time-order estimate.
- The genuine original Riesz zero-left energy-weighted slope was eventually **strict Success** in 42538089908, original job 128906765712 (same three-axiom allowlist), superseding failure 42536419967. The scaled-orbit selected source derivative was **Success** in 42536615928; selected three-Riesz source derivative in 42536770197; exact moving-coefficient physical Kummer identity in 42566073115 (job 128992747047, three allowed axioms). None proves full §2.13.
- CI 42603968381 failed at line 427 on multiplication grouping of the source-composite bound. The newer CI 42605032312, original job **129118702633**, evidence **13667892574**, confirmed that type mismatch fixed; its **only remaining error** was warningAsError linter unnecessarySeqFocus at ActualHartreePhysicalPlateauMovingSpectralQuadraticShellGain.lean:236:22, on the tactic sequence convert h using 1 <;> ring. Commit [8496cc48](https://github.com/penghongzhong/HBL/commit/8496cc483c661dea79cd752ff040cb906e8c03f2) replaces it with convert h using 1; ring. Strict three-target [CI 42610627350](https://github.com/penghongzhong/HBL/actions/runs/42610627350) **in progress at observation**, with no proof or axiom acceptance yet attributed to this new composite.
- **Mathematical operator scope:** for actual physical Kummer plateau, L0(u0-u1)-Fadj=-delta*u0, whereas (L0+delta)(u0-u1)-Fadj=-delta*u1. The current moving-coefficient identity justifies the second cancellation in that plateau, not globally across the original four-zone moving nonlocal PDE. Thus the negative spatial radius power cannot be substituted for an original unshifted residual estimate or a positive time order. Still needed: the whole PDE time derivatives of basis, endpoints, actual real selected speeds, nonlocal cross-zone Hartree feedback, parameter Lipschitz, source generation, true finite recursion and dynamical Type-II rate.
- **Original revised manuscript strictly 11/13**. No auxiliary statement increases this numerator.


### 2026-11-09 structural bottleneck audit — stop conditional-to-original promotion

**Verified new strict success**: [CI 42610627350](https://github.com/penghongzhong/HBL/actions/runs/42610627350) at commit `8496cc483c661dea79cd752ff040cb906e8c03f2`, original job `129137812702`, artifact `13670253589`; the job's three exact theorem `#print axioms` reports each contain only `propext`, `Classical.choice`, and `Quot.sound`. It compiles with Lean 4.35.0-rc3 / Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0`, and `warningAsError`. Accepted **auxiliary only**: genuine same-source current-coefficient plateau spectral *spatial* cubic shell bound. No temporal or global estimate follows.

**Exact obstruction, confirmed by reading original Lean theorem TYPES, not by compiler-error guesses:**

1. `ActualHartreeFullFourPieceFinitePDETelescoping.lean:93-143` proves `R(U_J)-R(U_0)=sum_j [R(U_{j+1})-R(U_j)]` by induction and `ring`. It proves **no estimate** on the original four-zone nonlocal operator `R` or its time/parameter difference.
2. `ActualHartreePhysicalOneLayerGain.lean:84-125` defines a generated term's `order` from an input cause tag and nonnegative `extra`. There is **no producer here** that identifies every term in the actual nonlinear `R(U+H)-R(U)` with a certified generated term. `ActualHartreePhysicalFiniteProfile.lean:105-147` takes arbitrary packets and the genuine growth inequality `hstep` **as hypotheses**; its proof does not construct any actual physical Hartree packet from the preceding residual. In particular, even an empty packet list does not certify an approximate PDE solution.
3. `WeightedJointBackwardResidualLipschitz.lean:224-256` proves a fixed-point theorem **conditional** on `hHlip`, `hGzero`, `hGlip`, `hsmall`, etc. The required *original Hartree source* direct threshold Lipschitz estimate is not produced there. `ActualHartreeFullInteractionTimeFromOrbit.lean` proves an accurate derivative formula **conditional** on actual orbit C¹, integrable dominating functions and bounds; it does not produce such a trajectory.

**Noncircular, shortest remaining acceptance theorem (locked single-orbit target):** construct a genuine time-dependent, four-piece physical field `U_*(s,theta)` and a fixed finite list of its actual Hartree correction packets from their explicit same-PDE source, such that for `s>=s0`

```text
||R_H[U_*(s,theta)]||_X <= C s^(-9/4)
||R_H[U_*(s,theta)]-R_H[U_*(s,eta)]||_X
    <= C s^(-9/4) ||theta-eta||
regional Hdot1 convergence + actual matching + no assumed blow-up speed
```

The **first** missing producer is one actual full-PDE corrected increment with positive gain `rho -> rho+kappa` in `X`, including exact moving Kummer coefficients/interfaces, selected-speed derivatives, and all cross-zone original Riesz contributions. The frozen plateau quadratic shell result is only one part of that increment. Once the *realized* one-step gain and direct difference bound are proved, iterate only to `9/4` (not arbitrary `N`) and invoke the existing direct-residual backward fixed-point framework. For the fixed-point input set `H(s,theta)=R_H(s,theta)-R_H(s,0)` so `H(s,0)=0` follows identically; keep the nonzero base residual separate. Then construct the actual solution and derive its rate dynamically rather than assuming the orbit or its rate in a source estimate.

**Acceptance remains 11/13.** Do not launch new isolated C1/Volterra/identity CI runs except where the missing full-PDE increment theorem has a direct import edge. The next priority is the original physical one-step gain with a concrete `R_H` norm and direct threshold difference, **not** more proofs of generic termination or formal telescoping.


### 2026-11-09 physical spectral shell trapped-time conversion (NEW proof obligation)

The **existing strictly verified, genuine quartic-source** moving-coefficient plateau bound, CI [42610627350](https://github.com/penghongzhong/HBL/actions/runs/42610627350) (original job `129137812702`, artifact `13670253589`, all three axiom reports within the exact allowlist), gives

```text
||E_spec||_(X_R) <= (5/32) G^2 R^(-19/4) |delta|^2 D_R,
R=ell^(-1/16)/2,
R^(-19/4) = 2^(19/4) ell^(19/64).
```

In the **visible intermediate physical length bootstrap** `0<ell(s)<=s^(-beta)` for `beta>1/2`, `s>=1`, the same source-specific estimate gives a *derived* factor `s^(-19 beta/64)`. If the *current* original Fredholm source budget `D_R(s)` (as defined from the real two-channel weighted norms, **not** an independently assumed next residual) obeys `D_R(s)<=C_D s^(-rho)`, and the true spectral coefficient difference stays bounded `|delta(s)|<=C_delta`, then **this spectral plateau contribution** gains `kappa_spec=19 beta/64>19/128` in time, with no direct hypothesis of a higher-order corrected PDE residual. Algebraically:

```text
||E_spec(s)||_(X_R) <= (5/32) 2^(19/4) G^2 C_delta^2 C_D
                        * s^(-(rho+19 beta/64)).
```

New exact Lean source [ActualHartreePlateauSpectralTrappedGain.lean](https://github.com/penghongzhong/HBL/blob/hbl-213-spectral-c1-trace-20261109/HBL/TypeIIDynamicSelection/ActualHartreePlateauSpectralTrappedGain.lean), commit `ef37cf2cd5dd870f99901e326fbb19b6770a9d09`; new pinned strict workflow `hbl-213-physical-plateau-spectral-trapped-time-gain.yml`, CI [42619593894](https://github.com/penghongzhong/HBL/actions/runs/42619593894), was **in progress on last audit**. Its proof and transitive axioms cannot be credited until raw Success and exact three-target audits. The matching TeX manuscript update is commit `8c7da3068ddc10644e2966beeff009c624e22624`.

**Scope limit**: this helps the **spectrally quadratic original plateau**, not the entire four-region physical PDE residual. Independently, a one-global *actual* nonlinear correction source-to-next-step theorem is under [CI 42619594632](https://github.com/penghongzhong/HBL/actions/runs/42619594632), but its exact statement still takes the physical principal linear correction equation as a hypothesis. Completing that solvability from the same uniquely selected, fully C1-matched original Hartree packet, furnishing all-region original norm and parameter differences, and closing the physical bootstrap remain essential. No additional original environment accepted: **11/13**.


### 2026-11-09 explicit original-PDE principal-defect reduction

The one-global genuine Hartree (full quartic nonlocal) source now has a proposed direct Lean bridge `HBL/TypeIIDynamicSelection/ActualHartreeOneGlobalPhysicalPDEStep.lean` with two exact targets:

- `actual_Hartree_full_PDE_controlled_by_actual_linear_principal_defect`: pointwise for the SAME physical global `U,H,b,omega,db,domega`, prove
  `||R_H(U+H;b+db,omega+domega)|| <= ||R_H(U;b,omega)+P_U(H)|| + C(U,H,db,domega) s^{-(rho+kappa)}`.
  This theorem invokes the already-proved original full-nonlinear Hartree Taylor and modulation-speed cross gain; it does NOT assume the linear defect is small.
- `actual_Hartree_full_PDE_next_gain_from_principal_cancellation`: corollary when the genuine linearized Hartree PDE condition `P_U(H)=-R_H(U)` is *provided*, not assumed by the manuscript as a rate hypothesis. It directly bounds the corrected original PDE residual, but cannot be used as §2.13 acceptance until the original four-region physical packet is constructed and shown to solve this principal problem.

Explicit positive-gain factor: `kappa=actualHartreePhysicalKappa beta rhoStar >0`; coefficient `Cspeed*(CHd+CH)+63*(M+CH)^5*CH^2*bubble(r)^5`. The estimated nonlinear residual is genuine (same global quartic Hartree operator). Remaining producing edge is the original Fredholm/Kummer/outer-region linearized defect, including moving-time derivatives and pointwise-to-weighted source norms. Follow with **direct** threshold-coordinate difference and fixed `9/4` bound.

New pinned trust-zero CI runs are tracked by workflow `.github/workflows/hbl-213-one-global-physical-pde-step.yml`; these targets are **pending, not accepted** until successful original job logs and exact #check / #print axioms audits. This proposal does **not** increase the retained manuscript count (still **11/13**).


### 2026-11-09 two-scale envelope obstruction to global PDE-step instantiation

**Mathematical scope correction (independent of CI result).** The new one-global nonlocal Taylor theorem requires the explicit *global* pointwise hypothesis `||U(s,r)|| <= M*bubble(r)`, with analogous `||H|| <= C_H s^{-rho} bubble(r)`. These are not known uniformly for the physically required `U=V_c+Z_ell`, `Z_ell(r)=sqrt(ell) z(ell*r)`. For a fixed legitimate regular radiation with `z(1) != 0`, at `r=1/ell`:

```text
||Z_ell(1/ell)|| / bubble(1/ell)
 = |z(1)| sqrt(ell) sqrt(1+ell^(-2))
 >= |z(1)| / sqrt(ell).
```

Therefore a uniform `M` for `U=V_c+Z_ell` generally fails; the required envelope constant can be `Omega(ell^(-1/2))`. Substituting this into the fifth-power Taylor coefficient incurs a possible `ell^(-5/2)` cost and may destroy the positive gain. **Do not infer** the four-zone order `9/4` or a uniform-in-time `X_s` estimate from a globally bubble-bounded correction theorem.

The required actual next step is to preserve the two distinct radial scales using existing `ActualHartreeFullMixedRieszEnvelope.lean`: `(1+r)|V_c(r)| <= D` and `(1+ell*r)||Z_ell(r)|| <= E sqrt(ell)`, and to prove the full `U+H` second-order Hartree density and cubic multiplier remainder in those two envelopes across inner/Kummer/repair/remote regions. Then bound the *original linear principal defect* from the real Fredholm/Green matched field and its moving-time derivatives, integrate into the source norm, and establish direct threshold-coordinate differences. A one-scale global bubble Taylor estimate is an accepted conditional local algebraic tool, not a valid automatic global closure producer.

The conditional principal-defect reduction (pending CI) still has a legitimate use wherever its hypotheses can genuinely be produced; it is not itself the missing uniform two-scale PDE estimate. Revised original count **11/13**.


### 2026-11-09 sharpened one-global original Hartree PDE step (rho=9/8 -> 9/4)

**Proof-chain shortening, with a real PDE identity rather than an invented order tag.** The already native `ActualHartreeOneGlobalCoreCorrectionNextLayer.lean` / `ActualHartreeSpeedCrossGain.lean` proofs show that (i) original nonlocal Hartree Taylor remainders and (ii) actual speed-cross terms are **quadratic** in the current correction order: both are pointwise `O(s^(-2 rho))`. The existing general layer theorem consciously downgrades this to `O(s^(-(rho+kappa_phys)))` for arbitrary recursive bookkeeping. For the **locked single orbit**, set `rho=9/8`; then **`2 rho=9/4` exactly** and one genuine linearized physical correction could suffice, avoiding the long arbitrary-N chain. This does **not** assume the corrected residual improves; it follows from the original polynomial/quartic-Riesz Taylor identity after a *separately constructed* linearized PDE solution.

New Lean source [ActualHartreeOneGlobalPhysicalPDEQuadratic.lean](https://github.com/penghongzhong/HBL/blob/hbl-213-spectral-c1-trace-20261109/HBL/TypeIIDynamicSelection/ActualHartreeOneGlobalPhysicalPDEQuadratic.lean) pins two target statements `actual_Hartree_one_global_PDE_quadratic_remainder_sharp` and `actual_Hartree_one_global_PDE_locked_nine_fourths`; its strict workflow [CI 42620369294](https://github.com/penghongzhong/HBL/actions/runs/42620369294) is **pending** until completed and audited (no claimed Lean success yet). The exact original one-global nonlinear PDE increment with a degraded exponent is also pending on independent CI [42619594632](https://github.com/penghongzhong/HBL/actions/runs/42619594632). Paper synchronized in TeX commit `ae7783dcdcc5cd607ddec6c4cf0940a016f62466`.

**Remaining decisive physical tasks:** the exact principal cancellation equation `P_U[H]=-R_H(U)` must be furnished by the SAME true-source Cramer/Fredholm/Kummer/far-field four-zone packet, in three genuine C1 joins. A pointwise constant speed-cross bound cannot be integrated blindly in the original global `L^{2,7/4}` norm: its spatial support, weighted decay and all nonlocal cross-region terms require their actual geometric estimates. The direct two-parameter Lipschitz bound of the *full residual*, and actual modulation bootstrap, must also be closed. If and only if these inputs are proved, the sharp single-step theorem can close the fixed `9/4` target of revised §2.13, then the final true-PDE blowup rate remains to derive. **Formal original count remains 11/13**.


### True two-scale quartic density producer (independent strict CI pending)

Source: `HBL/TypeIIDynamicSelection/ActualHartreeTrueTwoScaleTaylorDensity.lean`; dedicated pinned trust-zero workflow `.github/workflows/hbl-213-true-two-scale-taylor-density.yml`. This is a real same-background specialization, not an abstract order label. It combines the actual moving-monopole radial envelope, scaled high-regularity radial Strauss bound and the already-proved original complex quartic density/cubic Taylor polynomial inequalities.

Define for the real physical `V_c` and complex actual scaled radiation `Z_ell`:

```text
M_ell(r) = [2+9*C_mon]/(1+r) + 2(B+A)*sqrt(ell)/(1+ell*r)
U_ell(r) = V_c(r) + Z_ell(r)
||U_ell(r)|| <= M_ell(r)
|densityRemainder(U_ell(r),h(r))|
 <= 6 M_ell(r)^2 e(r)^2 + 4 M_ell(r)e(r)^3 + e(r)^4
||cubicRemainder(U_ell(r),h(r))|| <= (3M_ell(r)+e(r))e(r)^2
```

Also supplies the linear-density, background-cubic and linear-cubic estimates with the same physical `M_ell(r)`. This avoids the false uniform `M*bubble` assumption. At `r~ell^-1`, `M_ell(r)=O(sqrt(ell))`, so if `e(r)=O(ell*s^-rho)` the *local* quartic-density remainder has scale `O(ell^3*s^(-2rho))`, not an artificial `ell^(-5/2)` loss. **This local scaling heuristic is not the nonlocal Riesz integral estimate.**

Acceptance gate for the new theorem: original GitHub Actions Success, raw job logs, exact Lean type and three-axiom audit. Until then the statement remains **unverified**. The next physical step is integrating the true `M_ell(r)`-weighted density remainders through the original logarithmic radial inverse-square Riesz kernel, handling all four-region supports and their time and parameter differences. Original environment count **11/13**.


### 2026-11-09 strict trapped-time factor acceptance (auxiliary only)

**Strict SUCCESS** for [CI 42619593894](https://github.com/penghongzhong/HBL/actions/runs/42619593894), source commit `f3e309db178d6a85d154435f6da1dee6bd0ffd76`, original job **129168006311**, artifact **13676876666**. Original job log confirms pinned Lean 4.35.0-rc3, exact Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0 -DwarningAsError=true`, zero-byte strict.log, exact three `#check` and `#print axioms` reports, each listing exclusively `propext`, `Classical.choice`, `Quot.sound`. The three literal accepted types are `actual_Hartree_plateau_spectral_time_gain_positive`, `actual_Hartree_plateau_spectral_shell_trapped_time_factor` and `actual_Hartree_plateau_spectral_shell_source_to_time_gain`. This is the derived **physical plateau** factor `kappa_spec=19*beta/64`, conditional on visible intermediate bootstrap `ell(s)<=s^(-beta)` and **current** source budget; no four-zone full PDE time estimate is asserted.

**Manuscript environment count remains 11/13**; this is not a paper environment and says nothing about the still-missing four-zone principal linear correction solvability, original weighted residual/Lipschitz or resulting Type-II dynamics.


### 2026-11-09 strict two-scale audit and real Riesz remainder producer

- **Strict SUCCESS**: [CI 42620707912](https://github.com/penghongzhong/HBL/actions/runs/42620707912), raw job `129171794160`, artifact `13675688627`, pinned Lean 4.35.0-rc3 and Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, trust zero / warnings-as-errors, exact one-theorem check; raw `#print axioms` allowlist contains only `propext`, `Classical.choice`, `Quot.sound`. This settles the physical pointwise *two-scale* source density/cubic polynomial, not the nonlocal integration or full time order.
- **Strict SUCCESS**: [CI 42619593894](https://github.com/penghongzhong/HBL/actions/runs/42619593894), raw job `129168006311`, artifact `13676876666`; all three axiom reports in the original job are allowlisted. Under the explicitly visible intermediate `ell(s)<=s^(-beta)` bootstrap, the actual spectral shell `R^(-19/4)` yields time gain `19*beta/64`. The source-order input and bootstrap persistence are not produced by this conversion theorem.
- **PENDING** [CI 42621587679](https://github.com/penghongzhong/HBL/actions/runs/42621587679): `ActualHartreeBoundedBackgroundQuadraticRiesz.lean`, true *nonlocal* logarithmic inverse-square Riesz potential of the polynomial quartic density remainder. It requires only `||U||_infty<=M` and `||H(r)||<=e*bubble(r)`, not a false uniform `||U||<=M*bubble`; proves original Riesz absolute integrability and `|P[densityRemainder]|<=C_row*(6M^2+4Me+e^2)*e^2`. The proposed result is NOT certified until original success and exact audit. The actual U=Vc+Zell can meet the first hypothesis under the independently proved Strauss envelope when ell<=1, but producing the **actual four-zone correction H** with the second hypothesis, weighted source bound, moving time derivatives and parameter Lipschitz remains outstanding. Do not promote §2.13 on a local source derivative, bounded Riesz potential, or frozen shell time factor alone.

**Acceptance 11/13.** The finite-order 9/4 parametrix and dynamic Type-II theorem remain mathematically open.

### 2026-11-09 original nonlocal density remainder strictly accepted

**Strict Success** [CI 42621587679](https://github.com/penghongzhong/HBL/actions/runs/42621587679), raw job **129174844836**, evidence **13676543343**, Lean 4.35.0-rc3 / pinned Mathlib, trust-zero, warning-as-error, exact #check and #print axioms accepted with only propext, Classical.choice, Quot.sound.

True nonlocal inverse-square/logarithmic Riesz kernel: when ||U||_infty <= M and |H(r)| <= e*W(r), the genuine quartic density Taylor remainder is absolutely Riesz-integrable and satisfies

    |I_2[densityRemainder(U,H)](r)| <= C_row*(6M^2+4Me+e^2)*e^2 .

This is a strict original nonlocal **quadratic density source** bound, not a full nonlinear PDE time gain or a prescribed order.
Uniform L-infinity is available for the physical high-regularity Vc+Zell background when 0<ell<=1, unlike the false uniform single-bubble envelope. The explicit physical specialization under CI **42622739092** and the general sharp (1+r)^(-1) Riesz decay under CI **42622286088** remain pending until their actual job and axiom logs are checked.

Original linearized four-zone Fredholm/Kummer principal-defect solvability, moving terms, original source norm and threshold Lipschitz, real orbit/rate remain open: **11/13**.

### 2026-11-09 strict original PDE conditional 9/4 and physical Riesz spatial closure

**New strictly audited actual original-Hartree-PDE interfaces (all auxiliary, no original-environment promotion):**

- [CI 42622366690](https://github.com/penghongzhong/HBL/actions/runs/42622366690), original job **129177480271**, artifact **13678045616**: two exact Lean targets in `ActualHartreeOneGlobalPhysicalPDEStep.lean`. Proves the same full original quartic nonlocal Hartree PDE residual <= real linearized principal defect + a higher-order actual nonlinear remainder, and a conditional corollary when the genuine linearized PDE cancels the principal defect. Both axiom audits show only propext, Classical.choice, Quot.sound. The physical four-piece field solving the principal equation is NOT produced.
- [CI 42622459316](https://github.com/penghongzhong/HBL/actions/runs/42622459316), original job **129177784657**, artifact **13677486774**: two exact Lean targets in `ActualHartreeOneGlobalPhysicalPDEQuadratic.lean`, showing an actual quadratic s^(-2rho) remainder and specifically **s^(-9/4) from rho=9/8** under explicit original-PDE principal cancellation, one-bubble U/H majorants and source regularity. Both axiom audits contain only the allowed three. The uniform U <= M*W requirement is false for a typical nonzero physical `Z_ell`; hence this theorem is conditional and CANNOT be the original §2.13 by substitution.
- [CI 42622286088](https://github.com/penghongzhong/HBL/actions/runs/42622286088), original job **129177210820**, artifact **13677084306**: original positive Riesz kernel spatial domination `|F(x)|<=C W(x)^2 => |I_2[F](r)|<=C*C_decay/(1+r)`, exact source integral and allowed-axiom audit.
- [CI 42622739092](https://github.com/penghongzhong/HBL/actions/runs/42622739092), original job **129178724385**, artifact **13677416454**: genuine physical `U=Vc+sqrt(ell)z(ell*r)` source specialized to original quartic density Riesz remainder using its proved UNIFORM L-infinity envelope, not the invalid uniform full-bubble envelope, allowed-axiom audit.

**Shortest remaining true PDE source-norm route:** use actual radial Strauss and scalar inequality `ell*(1+r)/(1+ell*r)^2<=1` to get uniform `(1+r)|Z_ell(r)|^2<=E^2`. Combine with `(1+r)|Vc(r)|<=D` to obtain `(1+r)|Vc+Z_ell|^2<=2(D^2+E^2)=K^2`. Then the actual quadratic density Riesz source term multiplied by the original cubic has bound `|I_2[D_{>=2}]*|U|^2 U|<=C e^2 K^3 (1+r)^(-5/2)`. Squared weight `(1+r)^(7/2)` gives integrable `(1+r)^(-3/2)` with integral 2: the individual ORIGINAL source norm is O(e^2), hence order 9/4 from e=O(s^-9/8). The scalar physical inequality is under pinned exact strict CI **42623592401**, and this final weighted-L2 composite has not yet been formalized. It does not control the other nonlinear Taylor products or the moving-time interface and parameter differences.

**Current original target unchanged 11/13.** Even several strict auxiliary CI successes cannot promote the numerator before genuine four-zone source and backward orbit construction.

### 2026-11-09 source-to-global-envelope half-time-order loss (decisive)

**Decisive, source-faithful obstruction to claiming an instant 9/8→9/4 physical profile:** the actual physical Kummer repair's global bubble bound is already explicitly derived in `ActualKummerPhysicalTailWeightedLipschitz.lean`, theorem `actual_Kummer_physical_outer_repair_bubble_time_gain`. From the *actual* selected upper jet `||p(s)||+R||q(s)||<=C_D*s^(-rho)` and *actual* sqrt-clock radius `a(s)R<=C_X*s^(1/2)`, it yields only

    ||H_K(s,r)|| <= (1+2*C_X)*C_D*s^(-(rho-1/2))*W(r).

The derivative-free parameter-difference theorem `actual_Kummer_outer_repair_direct_parameter_lipschitz` inherits exactly this rho-1/2 power under a jet difference of order rho. Thus a source jet of order rho=9/8 supplies at best the global W-envelope `e(s)=O(s^(-5/8))`; squaring this envelope yields `O(s^(-5/4))`, NOT the desired `s^(-9/4)` nonlinear weighted L2 order. The logical gap cannot be removed by calling the exact full nonlinear Taylor bound or a four-piece telescoping identity.

**Three legitimate ways around the loss** (none yet closed): (i) derive upper value/slope jets one extra half-order smaller so that the *physical* H_K W-envelope is O(s^-9/8); (ii) prove the full original nonlocal source norm directly from the compact *moving shell support and two-scale Hartree Riesz geometry*, recovering lost time powers without global W domination; (iii) iterate the actual physical matching/linearized solver through sufficiently many genuinely sourced layers until the selected jets exceed the needed threshold. Any of these must also handle the true moving time derivative and direct threshold-coordinate difference. The original 11/13 count remains unchanged.

**New strict mathematical inputs (original auxiliary only):** 42655852845 actual true two-scale quadratic Riesz*cubic weighted L2; 42657807431 original true nonlocal quadratic Riesz two-point Lipschitz; 42659015432 abstract exact six-product fifth-weight inequality; 42659338200 physical half-radial cubic Taylor weights; 42659596309 complete original six-product same-kernel fifth-weight from its real Riesz rows; 42660327707 full six-product original weighted L2 under visible original Riesz row bounds and actual integrability. Each passed its own trust-zero and three-axiom whitelist audit. These do not produce the missing physical H_K envelope or full four-zone linear principal equation.

## 2026-11-10 physical-scale variation resolves the moving-slit domain conditional on the original modulation orbit

The same-source Cramer radius-weighted derivative `actual_Hartree_true_moving_selected_source_radius_weighted_time_budget` was strictly accepted in [42742271094](https://github.com/penghongzhong/HBL/actions/runs/42742271094). The original same-source singular Green moving-slit Frobenius radius gain `actual_Hartree_true_moving_singular_Green_cross_Frobenius_one_inverse_radius` was strictly accepted in [42744295852](https://github.com/penghongzhong/HBL/actions/runs/42744295852), job 129592601952, raw artifact 13730793163; the latter audit uses pinned Lean, exact Mathlib, `--trust=0`, warning-as-error and allowed axioms only.

**Precise remaining domain mismatch:** the first theorem holds on `1/a(τ)≤x≤B` but the moving Green difference needs this at *all* `τ∈[min(s,t),max(s,t)]` and *all* `x` between the actual two endpoints `r₋(u)=ell(u)^(-1/16)/a(u)`. It is mathematically false without scale control. A new concrete variation bridge, `ActualHartreeMovingSlitCramerScaleVariation.lean`, proves that the mismatch disappears provided one derives from the **same physical scale path** a common variation budget `|a(τ)-a(s)|≤V`, `|a(τ)-a(t)|≤V` and the two explicit margins
`V L_s≤a(s)(L_s-1)`, `V L_t≤a(t)(L_t-1)`, where `L_u=ell(u)^(-1/16)`, plus original endpoint-in-annulus ordering. It gives `1/a(τ)≤x≤B` on the true moving slit, not an invented source envelope.

For an absolutely continuous original scale the natural choice is `V=∫ |a'|` over the time segment. The two margins are equivalently `V/a(s)≤1-ell(s)^(1/16)` and `V/a(t)≤1-ell(t)^(1/16)`. This also establishes why **local** Green differentiation can use an arbitrarily small time segment when `0<ell(s)<1`, without any imposed global Type-II rate. The analytic input `a'` must still come from the final physical modulation dynamics; the bridge does not itself supply the true source time-budget or full PDE remainder.

New strict pinned audit workflow: [42756618784](https://github.com/penghongzhong/HBL/actions/runs/42756618784), **SUCCESS** (10 November 2026 04:45 UTC), original job **129632373174**, artifact **13736666241**; exact Lean declaration and axiom audit show only `propext`, `Classical.choice`, `Quot.sound`. The prior run [42756511255](https://github.com/penghongzhong/HBL/actions/runs/42756511255) refers to an earlier proof tactic variant; no success is pre-claimed. The LaTeX proof and pending status are synchronized in `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`.

**Official original revised environments: 11/13 (84.62%).** Still open: same-PDE source/compatibility time decay, moving Kummer basis and endpoint bounds, positive *weighted* gain for every original full nonlinear four-region Hartree residual, parameter-Lipschitz, genuine finite-order recurrence, and dynamical II-type rate. No newly submitted geometric lemma changes the count.


## 2026-11-10 local continuous-orbit segment bridge (pending CI)

The quantitative total-variation conditions above are **not necessary for local Green-source MVT**. At any actual slice `s` with `a(s)>0`, `0<ell(s)<1`, `r₋(s)=ell(s)^(-1/16)/a(s)<B`, continuity of `a,ell` alone yields an open interval `J` about `s` on which, for every `t∈J`, every `τ∈[min(s,t),max(s,t)]`, and every `x` between `r₋(s)` and `r₋(t)`, one has `1/a(τ)≤x≤B`. Proof: insert the fixed middle radius `m` with `1/a(s)<m<r₋(s)`; continuity gives `1/a(τ)<m<r₋(t)<B` for both times in a sufficiently small common interval. This is the **actual physical Cramer domain**, not an abstract assumed envelope, and no prescribed rate/positive order is used.

Added exact Lean statements `actual_Hartree_original_Cramer_shell_local_from_continuous_orbit` and `actual_Hartree_original_Cramer_shell_local_segment_from_continuous_orbit` to `ActualHartreeMovingSlitCramerScaleVariation.lean`; the latter explicitly covers **all intermediate times** and is a direct input for the original moving Green cross estimate. Pinned trust-zero warning-as-error exact-type/three-axiom workflow: [42763633557](https://github.com/penghongzhong/HBL/actions/runs/42763633557), **FAILED**. Raw job 129654905436 identified three Lean expression errors: `-1/16` versus exact `-(1/16)` exponent, incorrect definitional `change` for the actual slow radius, and invalid `.le` on an already weak interval comparison. All three were repaired at [commit 18bd6dd8](https://github.com/penghongzhong/HBL/commit/18bd6dd84afd966c0ba8ae05951e50e6fe93d178), mathematical statements unchanged. Replacement full three-target strict [CI 42764968763](https://github.com/penghongzhong/HBL/actions/runs/42764968763) **SUCCESS** (2026-11-10 06:07 UTC), source commit `18bd6dd84afd966c0ba8ae05951e50e6fe93d178`, original job **129659190491**, artifact **13739737815**. Raw log confirms pinned Lean 4.35.0-rc3, Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0 -DwarningAsError=true`, exact `#check` and `#print axioms` for all three target declarations; each audit report contains only `propext`, `Classical.choice`, `Quot.sound`. This strictly closes the **local moving-slit domain inclusion** for continuously varying original physical scale/slow radius, not the source time derivative or full Hartree PDE residual. **Original revised manuscript still 11/13**.

Even after successful local geometric certification, the true one-orbit bounds for `r‖∂ₛF_adj‖`, moving Kummer/endpoint contributions, all original nonlocal four-piece weighted residual terms at positive time order, parameter Lipschitz, real finite recursion and dynamically derived Type-II exponent remain unresolved. **Official manuscript: 11/13**, unchanged.

### 2026-11-10 strict pinned coarse dynamical Type-II scalar clock (auxiliary only)

**Strict Success** [CI 42766649238](https://github.com/penghongzhong/HBL/actions/runs/42766649238), source commit `9134d8fa4329e821c9e26f2d52cdb44d149c813e`, original job **129664601628**, artifact **13739896709** (completed 06:11 UTC). The decoded original job confirms Lean 4.35.0-rc3, exact pinned Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0 -DwarningAsError=true`, exact `#check`/`#print axioms` for `HBL.TypeIIDynamicSelection.actual_Hartree_coarse_TypeII_clock_from_dynamical_mu_trap`; transitive axiom set precisely `{propext, Classical.choice, Quot.sound}`. The literal theorem takes original-modulation *hypotheses* `HasDerivAt q (4 * mu s) s` and `0 < m ≤ mu(s) ≤ M` for all `s ≥ s0`, and proves linear growth of `q` and `q^(-1/2) → 0`, without assuming a limit of `mu` or a blowup exponent. Its hypotheses are **not yet generated by an actual nonlocal Hartree orbit**, and it proves no full nonlinear residual or sharp original rate. Manuscript TeX synchronized; **original revised paper remains 11/13**.


### 2026-11-10 independently audited true-clock and trapped-scale logarithmic gain

The raw GitHub workflow run [42773792399](https://github.com/penghongzhong/HBL/actions/runs/42773792399) completed **Success** at source commit \`b3351e421aceab877e54a4aa1b08e81ce69ac4cc\`, original job **129687475318**, original evidence artifact **13742663263**. The job explicitly pins Lean \`4.35.0-rc3\`, Mathlib \`a98628e16c11f5167f16124105ddce53efa9bfe5\`, \`--trust=0\`, \`-DwarningAsError=true\` and individual exact \`#check\`/\`#print axioms\` for all four declarations in \`ActualHartreeCoarseTypeIIClockFromMuTrap.lean\`. All four axiom audits contain precisely \`{propext, Classical.choice, Quot.sound}\`, and the strict build log is empty. The four verified declarations are:

1. \`actual_Hartree_coarse_TypeII_clock_from_dynamical_mu_trap\`: trapped positive mu and q_s=4 mu imply linear bounds, q→∞, q^(-1/2)→0.
2. \`actual_Hartree_dynamic_remaining_time_from_two_channel_equations\`: the **same** q and ell equations imply (q ell²)_s=-ell².
3. \`actual_Hartree_dynamic_terminal_clock_local_conservation\`: with t_s=ell², (t+q ell²)_s=0.
4. \`actual_Hartree_dynamic_mu_trap_log_scale_gain\`: with the same positive trapped mu, original scale law, and Q(s)=q(s0)+4M(s-s0), the precise **derived** monotonicity
   \[
   \log\ell(s)+\tfrac12\log q(s)+\tfrac1{8M}\log Q(s)
   \le \log\ell(s_0)+\tfrac12\log q(s_0)+\tfrac1{8M}\log q(s_0)
   \]
   eliminates an independent assumed positive s-time scale exponent. In particular, via q(s)≥(m/M)Q(s), \(\ell(s)\le \ell(s_0)\sqrt{M/m}\,(Q(s)/q(s_0))^{-1/2-1/(8M)}\).

The last exponentiation and the true Hartree radiation-moment log-L1 primitive are **paper consequences**, not additional accepted Lean declarations. None of the four Lean proofs constructs or traps a nonlinear Hartree PDE orbit; all operate on differential equations passed as hypotheses. The original four-piece nonlocal source time positive order, its Lipschitz counterpart, real fixed-point recursion, and dynamically realized blowup remain **OPEN**. Official original revised environment count: **11/13**, not inflated by auxiliary proof successes.


### 2026-11-10 exact width-independent weighted trace lower bound for authentic C² repair (paper; not Lean-accepted)

See `verification/HBL_213_SHARP_C2_PATCH_WEIGHTED_TRACE_OBSTRUCTION_20261110.md` and synchronized `verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex`. For every compact one-sided \(C^3\) repair \(P\) with \(P(L)=P'(L)=0\), \(P''(L)=\Delta_2\), and all three jets zero at \(L+h\), write \(f=\mathcal K_aP\) for the **same original** frozen Kummer operator. The literal endpoints \(f(L)=\Delta_2\), \(f(L+h)=0\) and the weighted one-dimensional fundamental theorem of calculus prove

\[
 \|(1+y^2)(\mathcal K_aP)'\|_{L^2(L,L+h)}
 \ge\frac{|\Delta_2|}{\left(\int_L^{L+h}(1+y^2)^{-2}dy\right)^{1/2}}
 \ge\sqrt3 L^{3/2}|\Delta_2|.
\]

For the actual \(h=L/4\), the constant improves to \(\sqrt{375/61}\). The independently derived broad-patch upper bound has precisely this \(L^{3/2}|\Delta_2|\) scaling when \(a\ge L^3\) and \(Q\) is bounded. Therefore no adjustment of compact C² patch width, cutoff shape, or location can improve the **separately estimated weighted source-gradient** scaling. In particular an independent \(O(s^{-p})\) patch source derivative estimate requires \(|D_{\rm in}(s,L)+a^{-2}\delta(s)u_0(s,L/a)|\lesssim L(s)^{-3/2}s^{-p}\), **not** an inferred \(s\)-gain from geometric cutoff tuning.

This is **not** a lower bound on the entire four-piece nonlocal Hartree PDE residual: same-source cancellation with other residual pieces, spectral projection, or Hartree propagation can improve the full term. The actual \(\Delta_2\) may itself be small or zero. The sharp analytic obstruction redirects the shortest original proof chain to an actual physical source cancellation or a genuine projected inverse, rather than more auxiliary cutoff redesign. The strict Lean source-dependent C² bound from CI **42854633900**, original job **129964186672**, remains valid, with exact axioms `propext`, `Classical.choice`, `Quot.sound`, but does **not** prove the new trace inequality, time-positive residual, nonlinear orbit, or dynamic blowup rate. This new note has **no independent Lean CI**. **Original revised acceptance: 11/13.**


### HBL_LOCAL_MASS_GAUGE_RESONANCE_GATE_20261110: exact mass-gauge phase-resonance reduction (paper only)
The original Hartree bubble has \(\Lambda W=-W/2+W^3\). Combining
this with the **same-PDE** moving phase/mass flux (MP9) yields the exact
renormalized mass ODE
\[
(\lambda^{1/2}\mathscr M)_s
=\lambda^{1/2}(\mathscr S-\mathscr B+bC-\tfrac34 bQ),
\quad C=\int_0^Lr^2W^3p,\quad Q=\int_0^Lr^2(p^2+q^2).
\]
The linear \(C\) term has an \(L\)-uniform Sobolev bound.
A fixed physical-radius matching gauge, **if its matching root exists
on the concentrated branch**, is locally nondegenerate because
\(\partial_{\log\lambda}M_R=\lambda^2 I(R/\lambda)
\le-\lambda R/4\) for \(R/\lambda\ge2\pi\). The corresponding
scale derivative is then an **actual PDE mass-current quotient**,
not a prescribed explosion rate. The *unnormalized*
\(\partial_{\log\lambda}M_R\sim-\lambda R/2\) degenerates as
\(\lambda\to0\). At any matching root the equivalent mass gauge
\(M_R/\lambda=0\) has Jacobian
\(\partial_{\log\lambda}(M_R/\lambda)
 =\lambda I(R/\lambda)\le-R/4\), but its PDE flux
costs \(1/\lambda\): actual same-orbit \(O(\lambda)\) current
and parameter-Lipschitz estimates remain compulsory. Energy alone still does not control
the expanding-radius phase term: \(p=\varepsilon W\) on \([0,L]\),
cut off by \(2L\), has \(O(\varepsilon)\) homogeneous energy but
an \(\Omega(\varepsilon L)\) scaling moment. Compatibility with the
existing unique Fredholm selector and the actual differentiated
four-region Hartree residual **remain OPEN**. Details:
\`verification/HBL_213_ACTUAL_HARTREE_MOVING_BUBBLE_MASS_PHASE_FLUX_IDENTITY_20261110.md\`.
No new Lean declaration; strict algebra CI 42929423991 and current-source
PDE telescope CI 42927397872 are **auxiliary only**. **11/13**.



### 2026-11-10 radiation obstruction to fixed-physical-radius mass-gauge shortcut (HBL_FIXED_RADIUS_MASS_GAUGE_RADIATION_OBSTRUCTION_20261110)

A new finite-radius mass calculation rules out the suggested **unsubtracted fixed physical \(R\)** scalar normalization whenever a concentrating Hartree orbit retains nonzero \(L^2(r^2dr)\) radiation on an annulus inside \(R\): the bubble mass there is at most \(\ell R\to0\), while the actual field's annular radiation mass remains positive. Thus the root required for the conditional nonzero Jacobian in (MG4) **does not exist** on such a branch. The normalized gauge \(M_R/\ell=0\) has exactly the same missing roots.

A shrinking physical interface \(R_\ell=\ell L\), as in the original matched profile, avoids this particular obstruction: bounded smooth radiation produces relative mixed/self mass \(O(\sqrt\ell L)\)/\(O(\ell L^2)\), yielding \(\ell^{7/16}\)/\(\ell^{7/8}\) for \(L=\ell^{-1/16}\). Its true scale Jacobian must include the moving-endpoint term. Full proof: [HBL_213_FIXED_RADIUS_MASS_GAUGE_RADIATION_OBSTRUCTION_20261110.md](HBL_213_FIXED_RADIUS_MASS_GAUGE_RADIATION_OBSTRUCTION_20261110.md). This is a **paper-level exclusion of an invalid proof shortcut**, not a residual time-gain, an actual PDE orbit, or Lean-verified §2.13. CI 42927397872 and 42929423991 retain their strictly audited identity/algebra scope. **Accepted original environments remain 11/13**; only §2.13 and the final PDE-derived Type-II main theorem can change the numerator.


### 2026-11-10 constructive conditional shrinking mass root + exact moving Jacobian (HBL_SHRINKING_GAUGE_ROOT_JACOBIAN_20261110)

Unlike a fixed-physical-radius mass normalization, the *shrinking* interface \(R(\sigma)=\sigma^{15/16}\) can admit a well-conditioned local scalar root. For a **fixed physical field** \(u=B_a+z\) with \(\|z\|_{L^\infty(0,2a^{15/16})}\le M\), let \(\varepsilon=Ma^{7/16}+M^2a^{7/8}\le1/2048\) and \(a^{-1/16}\ge16\pi\). A complete sign/monotonicity argument, retaining the moving-endpoint contribution, proves exactly one root \(\mathcal M_u(\sigma_*)=0\) in \([ae^{-128\varepsilon},ae^{128\varepsilon}]\), with \(|\sigma_*-a|/a\le(80/3)\varepsilon\), \(\mathcal M'_u(\sigma)\le-R(\sigma)/6\), and uniform normalized root Jacobian \(\partial_{\log\sigma}[\mathcal M_u/(\sigma R)]|_{\sigma_*}\le-1/6\).

[Complete proof](HBL_213_SHRINKING_GAUGE_ROOT_JACOBIAN_20261110.md), synchronized into [§2.13 TeX](HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex). This establishes a **conditional** scalar gauge root for a pointwise near-bubble field, not a theorem for an actual Hartree orbit: the physical \(L^\infty\) control of the *true* four-region selected Fredholm/Kummer correction is unproved; its compatibility with the unique original two-real-speed selector is unproved; neither nonlocal weighted time-positive source estimates nor parameter Lipschitz, actual finite recursion, or PDE-derived blowup rate is established. No new Lean CI / new axiom / original environment acceptance. Strict historical success of CI 42927397872 and 42929423991 has only PDE-identity and jet-algebra scope. **11/13 unchanged; §2.13 and final original Type-II theorem remain OPEN.**


**Further exact conditional step (same gate):** On the stated near-bubble class, the complete moving scale derivative is two-sided:
\(-3R/5\le \partial_\sigma\mathcal M_u\le-R/6\), and the scalar root has uniformly bounded logarithmic normalized Jacobian between \(-3/5\) and \(-1/6\). If the *same field* is additionally a regular solution of the true Hartree equation, radial mass conservation gives the exact **PDE-current-selected** scale speed
\(\dot\sigma=R(\sigma)^2\Im(\bar u u_r)(t,R(\sigma))/\partial_\sigma\mathcal M_{u(t)}(\sigma)\), hence \(5R|j|/3\le|\dot\sigma|\le6R|j|\) and opposite signs of speed/outward current. This is an exact conditional local kinematic law, not the dynamically established Type-II rate. Neither actual original four-region weighted remainder nor a bound for the current or compatible two-channel Cramer speed has been proved; **11/13** unchanged. See the appended derivation in [shrinking-gauge note](HBL_213_SHRINKING_GAUGE_ROOT_JACOBIAN_20261110.md).


## HBL_INTERFACE_REGULARITY_GATE_20261111: actual source regularity gate and finite third-jet repair

Original revised acceptance remains **11/13**. The new paper proof in
`verification/HBL_213_INTERFACE_REGULARITY_GATE_20261111.md` shows that a
nonzero second-jet jump of a classical C1 matched physical Hartree field
makes its proposed Hessian--Morawetz-dual source norm infinite; temporal
smallness of a nonzero jump cannot cure this. C2 matching alone also does
not imply moving-interface H1-source Lipschitz continuity (an explicit
square-root translation counterexample is given). These analytic results
are paper proofs, not Lean certificates or a no-go for the main theorem.

Strict auxiliary CI [42944437228](https://github.com/penghongzhong/HBL/actions/runs/42944437228)
at source commit `a7403cf76be23c1654c830913c4614289785405b` checks ONLY the two precise declarations
`actual_Hartree_physical_C3_repair_endpoint_jets` and
`actual_Hartree_C3_repair_factored_kernels` in
`HBL/TypeIIDynamicSelection/ActualHartreeInterfaceC3RepairPolynomial.lean`.
The workflow requires the pinned Lean 4.35.0-rc3 and Mathlib
`a98628e16c11f5167f16124105ddce53efa9bfe5`, trust=0, warningAsError,
complete #check output and per-declaration allowed-axiom audit. Only
propext, Classical.choice and Quot.sound are permitted. The successful
Lean audit is restricted to the physical-width polynomial endpoint jets
and the factored kernels. It does NOT prove the global repaired Hartree
source, actual jet decay, parameter Lipschitz bounds, original same-speed
compatibility after the nonlocal feedback, or a physical blowup orbit.

The original numbered environments remain **11/13**. No new original
environment is accepted by the polynomial construction.


## Exact whole-space quartic Hartree feedback after C3 interface repair (paper; not Lean)

[Full original-kernel proof](HBL_213_TRUE_HARTREE_C3_NONLOCAL_FEEDBACK_20261110.md): HLS and Sobolev prove a genuine energy-dual nonlinear estimate, not a telescope, for the physical C3 repair P constructed from the actual curvature and third-jet discrepancies:
\(‖\mathcal N_H(U+P)-\mathcal N_H(U)\u2016_{\dot H^{-1}}\le C(2\u2016\nabla U\u2016_2+\u2016\nabla P\u2016_2)^6\u2016\nabla P\u2016_2\),
\(\u2016\nabla P\u2016_2\le [4\pi((L+h)^3-L^3)/3]^{1/2}(h|d_2|M'_2+h^2|d_3|M'_3)\).
This controls all nonlocal feedback, including outside the repair shell, and the note explicitly computes its moving-time derivative. It does **not** bound the differentiated source topology, moving actual jets, outgoing Cramer functional, two-speed feedback, or any time exponent. No new Lean certificate, no original §2.13 or Type-II acceptance. Revised original environments **11/13**.


### Source regularity gate: even Fredholm-compatible continuous phase forcing can lack the third jet

[Explicit phase ODE counterexample](HBL_213_C3_SOURCE_REGULARITY_NECESSITY_20261110.md): with the actual phase block \(L_-=-\partial_r^2-2r^{-1}\partial_r-3W^4\), let \(q=(4/15)\chi(r)|r-R|^{5/2}\), \(F=L_-q\). It has \(F\in C_c\cap L^2_{\rm weighted}\) and the **exact** compatibility \(\int r^2WF=0\), but \(q'''\notin L^2_{\rm loc}\) and \(F\notin H^1_{\rm loc}\). Changing the normalized solution by smooth homogeneous modes cannot cure it. Hence the accepted weighted-L²/continuous original source assumptions do not imply the third spatial jet demanded by the new strict Hermite polynomial lemma; actual Hartree source spatial differentiation and time/parameter control must be proved, or the strong differentiated source topology changed. This is a paper-level decisive gap in the **current proof strategy**, not a disproof of the Type-II theorem. No added Lean axiom or original-environment acceptance. **11/13** unchanged.


## HBL_SLOW_INNER_WEIGHTED_L2_20261111: derived full-Hartree source norm, not full original §2.13

The actual slow-inner ten-term nonlocal Hartree source has source-produced pointwise length `ell^(1/2)` and weighted squared L² bound `K(B,A)^2 ell * ∫_(0,∞)(1+r)^(-5/2)dr`; on its true backward overlap, its physical L² source component is bounded by `sqrt(127/7) K ell^(23/32)`. Proof and exact scope: `verification/HBL_213_SLOW_INNER_WEIGHTED_L2_20261111.md`. A dedicated pinned strict CI checks only `actual_Hartree_slow_inner_half_power_weighted_L2` and its three-axiom audit; no Success is claimed before inspection. Other real modulation/spectral/time/nonlocal residual components and the PDE orbit remain open. Original **11/13** unchanged.


## HBL_HALF_POWER_WEIGHTED_L2_STRICT_42952819526: exact pinned Lean Success (spatial source component only)

At source SHA `75970cf2fa21ea8dfc09ebe051ce6cf5983c9ef3`, [CI 42952819526](https://github.com/penghongzhong/HBL/actions/runs/42952819526), original job `130303403837`, evidence artifact `13826515899` (SHA256 `01e20b4ada001ca304d1a455f18318f4ef9da20dca5db76e1975e6136dea3b55`) have **strict Success**. GitHub's raw log shows the pinned Lean 4.35.0-rc3 / Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, `--trust=0`, `-DwarningAsError=true`, exact `#check` of `HBL.TypeIIDynamicSelection.actual_Hartree_slow_inner_half_power_weighted_L2` and its individual `#print axioms`, with precisely `[Classical.choice, Quot.sound, propext]`; no sorry/admit or extra axioms. The upstream physical source producer was actually rebuilt as a dependency at the repaired SHA. A separate workflow still audits the precise three upstream declarations; its earlier original run 42951761187 failed only on an extra `ring` command after a completed `field_simp`, now fixed.

**This proves the spatial weighted-square-integral estimate only.** It does not upgrade the entire selected Cramer annulus, full moving PDE residual, temporal gain, finite profile, or the final rate. Original revised **11/13**.
