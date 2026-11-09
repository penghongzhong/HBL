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
Hartree shell norm at commit \`903b870\`; original audit:
Lean 4.35.0-rc3, pinned Mathlib \`a98628e16c11f5167f16124105ddce53efa9bfe5\`,
\`--trust=0 -DwarningAsError=true\`, exact \`#check\` and \`#print axioms\`,
only \`propext\`, \`Classical.choice\`, \`Quot.sound\`, artifact **13647485540**.
This *does not* upgrade §2.13: the coarse pointwise shell bound incurs
\`20 R^(13/4)\`, which for \`R≈ell^-1\` and \`ell^(5/2)\`
loses \`ell^(-3/4)\` rather than gaining a positive scale order.

**Non-circular improvement identified from already present Lean code.**
\`ActualHartreeMatchedShellWeightedGain.lean\` proves, on a
*source-matched C¹ interface* with the same scaled Kummer source equation
and its stated regularity and coefficient smallness,
\[
  \| \mathbf 1_{(R,2R)}\,r\, [\mathcal L_K(\chi_R(u-v))
     -\chi_R\mathcal L_K(u-v)]\|_{L^{2,7/4}}
  \le 20C [C_{\rm in}R^{-3/4}
    + C_{\rm K}(\mu,\theta)R^{13/4}/a^2]N_F.
\]
The \`R^-4\` pointwise mismatch gain is produced by **matching + common
differential equation before** applying the shell norm. If the actual
profile yields \`a≥R²\` with uniform spectral coefficient,
the full displayed norm gains \`R^-3/4\`; this extra premise is **not**
silently supplied for the moving physical four-piece profile.
The proof accepts no independent mismatch amplitude as input.

**Next original-PDE closure gate:** instantiate that matched-shell
theorem on the *actual spectrally corrected* four-piece field.
Its exterior equation has a real quadratic spectral defect, so
first extract the exact extra defect and genuine moving time/speed
derivatives; bound all nonlocal cross-region sources and parameter
differences in their own source norms; then iterate and dynamically
derive the Type-II scale. Until that concrete same-source reduction and
time-positive original PDE norm estimate are proved, **11/13**.

The initial spectral 3-C¹ failures \`42531033761/768\` and joint
\`42531467165/166\` were traced to raw Lean elaboration errors:
\`HasDerivAt\` pullback mismatch and a redundant \`dsimp\`.
The no-progress \`dsimp\` is absent on the current source;
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
