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
