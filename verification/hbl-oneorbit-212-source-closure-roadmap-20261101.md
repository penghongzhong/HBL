# HBL 2.12 shortest physical-source bridge — 2026-11-01

## Scope and counting (do not inflate manuscript environments)

- **Original retained manuscript:** 9 accepted of 13; historical original: 9/21.
- Open retained environments: original 2.12, 2.13, 2.14, and Type II dynamical-rate-selection main theorem.
- The target is one genuine three-dimensional radial energy-critical Hartree Type II orbit with rate **derived from the actual modulation PDE**, not prescribed.
- No newly accepted retained manuscript environment is claimed here. Formal auxiliary source estimates are not original 2.12.

## Strictly checked and already merged into this physical-source branch

- Real complete mixed quartic density
  `F_ell=|V_{c_ell}+Z_ell|^4-|V_{c_ell}|^4-|Z_ell|^4`,
  with `c_ell=kappa_H ell m_0[g]` and selected nonzero real terminal annular radiation.
- Complete physical `L^1` source, Riesz central source, positive half-order gain; normalized physical resonance charges, compatible H+ and H− data.
- Real mixed density `L^2` source square bound `∫|F_ell|² dr ≤ C ell⁴` for `0<ell≤1`.
- Genuine source-weight estimate `∫ <r>^(2sigma) |F_ell|² dr ≤ C ell⁴ <4/ell>^(2sigma)` for `sigma≥0`, hence `≤ C_sigma ell^(4-2sigma)` for `3/2<sigma<2`, `0<ell≤1`.
- Source branch updated by a fast-forward from `hbl-oneorbit-weighted-L2-20261101` at `e6452bd380db45da29c4a68713faeb71881222f4`.
- Strict trust-zero CI SUCCESS: https://github.com/penghongzhong/HBL/actions/runs/41296974363
- Earlier concrete affine charges and half-order corrected source strict success:
  https://github.com/penghongzhong/HBL/actions/runs/41287847421
  https://github.com/penghongzhong/HBL/actions/runs/41288081743

## Two narrowly targeted subsequent physical PDE advances (NOT yet accepted)

1. Branch `hbl-oneorbit-full-center-defect-20261101`:
   proves the full genuine nonlocal interaction centre identity
   `C_full(ell)=c_ell+C_mix(ell)` and `|C_mix| ≤ C ell^(3/2)`
   from the same real source. Previously blocked by a definitional
   unfolding mismatch at Lean line 117; source corrected. CI with
   extended timeout and project build cache:
   https://github.com/penghongzhong/HBL/actions/runs/41299260432
2. Branch `hbl-oneorbit-terminal-pde-monopole-speed-20261101`:
   combines the genuine Hartree terminal quartic-moment PDE jet with
   `ell_s=-b ell, t_s=ell²` to derive `c_s=-bc` **at the selected
   terminal slice**, and obtains the full actual moving-cutoff profile
   time derivative. It does *not* infer the off-terminal identity.
   https://github.com/penghongzhong/HBL/actions/runs/41299604958

Neither branch increments the 9/13 acceptance count unless the original
complete 2.12 statement is independently matched and kernel-audited.

## The remaining original 2.12 obstruction: one physical three-region source

Manuscript original 2.12 says for the minimum unremoved weight rho:
`Pi_rho F(V_<rho+Delta V_rho)=P_rho(zeta)zeta_s`, with
`Delta V_rho=Delta_in+Delta_K+Delta_remote`,
two unique affine threshold charges, and **every** generated term
of order at least `rho+kappa_prof`, `kappa_prof>0`.

The still missing mathematical proof (not a syntax / build issue) must:

1. Use a **single actual off-terminal Hartree radiation field** on a
   shrinking/moving core; derive spatial flatness and source
   majorants from the cited high-regularity local theory. Terminal
   compact support is not preserved by Schrödinger evolution.
2. Identify both **actual PDE-projected** H+ and H− sources, not
   merely identify them with the same real quartic density.
3. Match exactly the same `F(V)` through origin-normalized
   Kummer parameter-dependent Green and remote inverses on the
   prescribed overlap, including true moving-cutoff commutators.
4. Derive every `kappa_prof` gain from source, overlap,
   and parameter derivatives; do not provide a positive order
   as a hypothesis or hide it in a `GeneratedTerm` structure.
5. Retain the dynamics-selected exponent: no fixed or prescribed
   terminal blowup rate.

No `sorry`, `admit`, added `axiom`, or replacement of a
target PDE source by an arbitrary abstract `RegionalSolver`.
Exact Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5.


## 2026-11-01 strict successes, unified branch, and next original 2.12 duties

Strict SUCCESS (pinned Lean 4.35.0-rc3, Mathlib a98628e16; full types and transitive axioms checked):
- Full physical Hartree interaction centre: https://github.com/penghongzhong/HBL/actions/runs/41299260432
- True terminal PDE monopole drift and full moving-cutoff profile time jet: https://github.com/penghongzhong/HBL/actions/runs/41299604958
- Genuine complete mixed-density L2 + weighted Fredholm quantitative source: https://github.com/penghongzhong/HBL/actions/runs/41296974363
- Actual H+/- affine-charge and half-order compatible data: https://github.com/penghongzhong/HBL/actions/runs/41287847421 and https://github.com/penghongzhong/HBL/actions/runs/41288081743

The first two SUCCESS source/audit pairs were merged verbatim into hbl-oneorbit-physical-source-joined-20261101. The closed PDE identity c_s=-b*c is valid on the chosen terminal time slice, not on an entire interval.

New pending strict physical source drafts (do NOT count without successful CI):
- hbl-oneorbit-full-potential-core-20261101: full actual self+mixed Hartree Riesz potential and positive core defect; https://github.com/penghongzhong/HBL/actions/runs/41301152580
- hbl-oneorbit-second-time-jet-20261101: genuine radial Hartree core second time jet under visible potential-time and mixed-derivative regularity; https://github.com/penghongzhong/HBL/actions/runs/41301548781

Formal PDE strategy: a smooth annular terminal datum has vanishing time jets on the strict inner core by induction: the Laplacian acts on a previously zero jet, while each time-differentiated nonlocal Hartree term retains a local cubic factor or its derivatives. Turning this into uniform moving-core smallness still requires real high-regularity estimates, uniform Taylor remainder and the derived physical clock. No off-terminal compact-support hypothesis is valid.

The existing generalized-Hartree scattering code pool in penghongzhong/open-HE gives useful exact Duhamel source coherence, fixed-point, and interval-gluing patterns, but not an automatic proof of HBL high-regularity weighted persistence or Type II dynamical modulation. Model and exponent matching must be proved.

ORIGINAL ACCEPTANCE REMAINS 9/13 (69.23%), historical 9/21. No additional original manuscript environment is accepted by auxiliary source progress. Old 2.12 still needs one physical off-terminal residual, both H+/- projections, Kummer/remote overlap, moving cutoff commutators, and each true positive generated-order gain without preset rate.


## 2026-11-01 second-time-jet success and exact original spatial source transition

- Verified original physical full nonlinear Hartree Riesz potential and positive inner core defect: strict CI SUCCESS 41304837438, merged as exact `.lean`/Audit source blobs.
- Verified the selected true radial Hartree flow's terminal second time jet at every fixed 0<r<1/4, under explicit classical PDE mixed-derivative and nonlocal-potential differentiability obligations: strict CI SUCCESS 41309108489; exact source + Audit merged into main branch at 54c80c6d57c3.
- This extra terminal time jet is **not** a replacement for the original lemma's spatial quadratic regular-radiation flatness. The manuscript requires the physical radial C2 bound for all relevant time-jet orders a<=N+1 and k<=2.
- Derived spatial MVT estimates `|z(t,r)-z(t,0)|<=M r²`, `|z_r(t,r)|<=M r`, and the true rescaling `|Zflat(s,R)|<=M ell(s)^(5/2) R²`, with fixed physical unit ball C2 regularity as explicit strong-flow input. Strict CI PENDING: https://github.com/penghongzhong/HBL/actions/runs/41309946657.
- Derived independent terminal-time quadratic bound `|z(t,r)|<=M(T-t)²` from two Banach MVT applications and the actually PDE-verified zero first terminal velocity. Strict CI PENDING: https://github.com/penghongzhong/HBL/actions/runs/41309840473.
- Original exact `j_g(t) chi(r)` center cutoff plus complex phase and physical energy-critical scaling have been connected to the spatial MVT source. Strict CI PENDING: https://github.com/penghongzhong/HBL/actions/runs/41310712743.
- The actual true-flow high Sobolev-to-radial C2 embedding and strong regularity input, k=1,2 derivatives of phased flat radiation and every a-th time jet, the full PDE H+/- forcing, Kummer/remote gluing and all generated positive weight gains remain open.

**Core original theorem acceptance count STILL 9/13, not 10/13.** Prior strict CI successes count as supporting physical theorems only. Selected blowup exponent remains a derived output and is never imposed.


## 2026-11-01 newly STRICT-accepted physical Hartree source batch

- `ActualOneOrbitTrueFlowTimeFlatQuadratic.lean`: actual chosen terminal radial Hartree PDE first jet plus visible C²-in-time bound implies pointwise `‖z(t,r)‖ <= M (T-t)²`, and actual critical rescaling `sqrt(ell)`; strict CI SUCCESS https://github.com/penghongzhong/HBL/actions/runs/41320320599. Exact accepted source + Audit merged.
- `ActualRadiationSpatialFlatness.lean`: **arbitrary nonterminal time** radial Hartree C² representative with regular origin derivative zero implies `‖z(t,r)-z(t,0)‖<=M r²` and actual rescaled source `‖Z_flat(ell,R)‖ <= M ell² sqrt(ell) R²`, from two real Banach-valued MVT applications. Strict CI SUCCESS https://github.com/penghongzhong/HBL/actions/runs/41320369793. Exact source + Audit merged.
- `ActualPhasedSpatialFlatness.lean`: replaces the centered difference with the **actual** Hartree regular-radiation center cutoff `z(t,0) χ(r)` and complex `e^{-i gamma}` phase; strict CI SUCCESS https://github.com/penghongzhong/HBL/actions/runs/41320434660. Exact source + Audit merged.
- The actual original PDE-driven terminal second time jet `z_tt(T,r)=0` on 0<r<1/4 was separately strictly accepted and merged: https://github.com/penghongzhong/HBL/actions/runs/41309108489.
- The algebraic physical moving-core `epsilon_flat=5 beta_minus/2 -2 rho_star -1>0` and actual source time weight `s^(-1-epsilon_flat)` are in a STRICT CI RECHECK (not yet accepted): https://github.com/penghongzhong/HBL/actions/runs/41322045235 and https://github.com/penghongzhong/HBL/actions/runs/41321988733.

**ORIGINAL numerator and denominator remain 9/13.** The three new physical proofs do not establish uniform C² bounds for every time jet from the Sobolev local-flow interface, do not jointly identify the two true PDE-projected H+/H- sources, and do not carry the same physical residual through Kummer/remote matching with all generated positive gains. It would be invalid to count original 2.12 as accepted.


## 2026-11-01 — Strict original-2.12 bridge audit (real numerator unchanged)

Retained original manuscript environment acceptance: **9/13**; historical original **9/21**. The original `prop:one-layer-stage3` remains OPEN. No source-only or conditional theorem is counted as an accepted original environment.

Strict native Lean 4.35.0-rc3 / pinned Mathlib successes:
- 41356512711: actual complex-phase and center-cutoff offterminal spatial-flat source has the *derived entire future-time integrable tail*, relative to visible radial C2 and modulation trapping inputs.
- 41357149079: genuinely constructed local parameter-dependent Kummer Green right inverse acts on the **same full Hartree PDE residual**, with both classical annulus Wronskian boundary conditions and norm bound.
- 41357587148: one nonterminal Hartree radiation is split by the actual smooth moving cutoff; its complete renormalized PDE source separates exactly into inner-cutoff residual and true nonlocal remote term, with the real/imaginary channel identities.
- 41358200123: **one** physically common complex weighted L2 residual source bound implies *both* H+ and H− weighted Fredholm data, unique actual real affine threshold charges and unique pair of normalized physical Fredholm solutions. Crucially the single weighted residual norm remains a hypothesis until derived from the real trajectory.
- 41356531877: common full Hartree source also gives both H± and the Kummer annulus, with exact nonlinear radiation-interaction equality under the visible actual radiation PDE condition.
- 41331077838 and 41330963439: full physical radiation PDE cancellation and actual moving-support remote core identity, each separately strictly accepted.

All source and audit files from the first four passes and the earlier strictly accepted flat positive-exponent proof are combined, without changing their theorem statements, in branch `hbl-212-physical-source-integration-20261101`. Its own joint trust-zero build and audit is Actions 41359532078; do not claim it passed before this run succeeds.

The remaining mathematical obligations for *actual manuscript 2.12* are exactly:
1. Specialize the standard high-regularity 3D Hartree local theory to the **same chosen complex, radial, offterminal orbit**, including full physical radial lift, real time/space chain rule and uniform weighted (L^{2,\sigma}) bound for the full renormalized interaction residual. Unjustified terminal support propagation is forbidden.
2. Match the **actual** corrected inner H± Fredholm solutions to the constructed normalized parameter-dependent Kummer Green solution and then the remote inverse on the prescribed moving overlap, with all boundary traces and moving commutators.
3. Classify every physically produced new Hartree/Frobenius/Riesz/moving-cutoff/parameter-source term and prove its real positive weight improvement `rho+kappa_prof` from the actual source and modulation PDE. The existing `GeneratedTerm` and `RegionalSolver` abstract packages do NOT satisfy this requirement.
4. Retain blowup-rate selection as an output from the full modulation dynamics; no assumed value of `mu_infty`, `lambda(t)`, or a terminal blowup exponent.

Other strict CI source candidates at this writing: 41358656004 (true complex-background moving-remote exterior Riesz matching), 41358694812 (physical radial Riesz critical scaling), 41358975199 (full nonlocal critical phase covariance), 41359233737 (critical radial derivative/dilation). Confirm their terminal Actions results before recording acceptance.

Next shortest physical step: after the verified Riesz/critical scaling and time/space chain rule, eliminate the visible `hRadiationPDE` conditional input by specializing the *same actual cited regular Hartree flow*. Then use its weighted source estimate to instantiate the already strictly verified single-common-complex-source H± Fredholm solve. Finally match Kummer and exterior boundary jets, not just source restrictions.


## 2026-11-02 00:05 UTC — True multi-domain source and physical-flow verification update

**Original retained environment count remains 9/13. Original 2.12 OPEN.**
Do not count a conditional exact-source identity, abstract solver, or independent
auxiliary declaration as an accepted original manuscript environment.

Additional strict trust-zero/native Lean 4.35.0-rc3 successes:
- [Actions 41363592399](https://github.com/penghongzhong/HBL/actions/runs/41363592399): all three complex-background moving-exterior Riesz statements accepted, including the *actual* O(r^2) remote-center defect with full complex inner radiation.
- [Actions 41363707916](https://github.com/penghongzhong/HBL/actions/runs/41363707916): all four full Hartree nonlinearity critical rescaling and complex unit phase covariance statements accepted; original radial Riesz integral has no local-cubic surrogate.
- [Actions 41363595082](https://github.com/penghongzhong/HBL/actions/runs/41363595082): 4079 jobs successful, all seven primary source/Kummer/Hplus/Hminus/physical-time declarations jointly checked in one dependency environment; no sorry/admit or additional axioms.

All six new source/audit files from the first two successes have been copied *verbatim* into this joint integration branch, and the joint audit expanded from seven to 17 native theorem declarations. The expanded strict verification is [Actions 41365096785](https://github.com/penghongzhong/HBL/actions/runs/41365096785), **not yet accepted**.

Further substantive candidates undergoing strict verification, NOT YET ACCEPTED:
- [41364947490](https://github.com/penghongzhong/HBL/actions/runs/41364947490): physical radial derivative + dilation under actual critical scaling; corrected a mixed real-to-complex chain rule and unreachable tactic.
- [41364157993](https://github.com/penghongzhong/HBL/actions/runs/41364157993): genuine time-dependent complex phase derivative and complete nonlocal Hartree PDE residual gauge covariance.
- [41364472602](https://github.com/penghongzhong/HBL/actions/runs/41364472602): physical joint C1 spacetime flow + actual ell_s=-b ell and time_s=ell^2 yield the exact rescaled time jet.
- [41364662279](https://github.com/penghongzhong/HBL/actions/runs/41364662279): the actual whole-radiation slow monopole minus its moving exterior center equals a concrete quartic density mismatch integral, with a sharp triangle-integral upper bound; the smallness of this mismatch remains to be derived from the selected orbit.
- [41364890422](https://github.com/penghongzhong/HBL/actions/runs/41364890422): exact source-level Kummer/inner/outer identity on one annulus inside the moving core, using the same actual Hartree PDE and complex remote Riesz density.

Remaining TRUE original 2.12 obligations (none can be replaced by a source-only identity):
A. Prove the physical selected *offterminal* Hartree regular flow is represented by the radial chain/phase scaling fields above and derives the renormalized radiation PDE, not merely assuming it.
B. Derive the uniform `InWeightedL2 sigma` source estimate for the one physical complex residual, and a quantitative small power for the true whole-to-exterior monopole mismatch, from the same orbit and time-dependent cutoff.
C. Prove genuine inner H+ and H- corrected boundary-jet matching to normalized Kummer annulus solution and moving remote inverse, including cutoff commutators and the same modulation tangent.
D. Prove every newly generated Hartree/Frobenius/parameter/slow-monopole/moving-cutoff atom has **strict** positive physical weight gain `kappa_prof`, not just a GainCause enumeration.
E. Derive the eventual Type II blowup rate from the constructed PDE and modulation system, never put an exponent or limiting speed among the premises.

No new manuscript counter or new axiom. Keep 9/13 pending exact 2.12 acceptance.
