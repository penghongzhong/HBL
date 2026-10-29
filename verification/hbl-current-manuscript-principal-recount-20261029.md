# HBL: separate historical 21-environment ledger from the current 2026-10-27 manuscript

**Source scope:** Inspected the Library snapshot `HBL_Synchronized_Repair_FiniteProfileClosed_20261027.tex` (5,727 lines) programmatically in this turn. This is a read-only metadata audit; the private manuscript was NOT uploaded or rewritten in GitHub.

## Exact current theorem-like environment count

The TeX snapshot has **12 principal named environments**: 1 `targettheorem`, 10 `lemma`, and 1 `proposition`; plus **13 `verifiedlemma` auxiliary environments**. A `verifiedlemma` designation does not independently establish a current trust-zero kernel and manuscript correspondence audit.

The 12 principal environments and their statuses, cross-referenced to the already recorded original-environment audit from 2026-10-28, are:

| Current label | Principal environment status |
|---|---|
| `thm:main` | OPEN |
| `prop:modulation` | strictly revalidated |
| `lem:affine-charge` | strictly revalidated |
| `thm:Xi-mon-tail` | strictly revalidated |
| `prop:profile-cancel-stage2` | strictly revalidated |
| `prop:kinematic-recovery-v2` | strictly revalidated |
| `prop:regular-flow-stage3` | closed using explicitly cited standard high-regularity local Hartree theory |
| `prop:one-layer-stage3` | OPEN |
| `thm:finite-profile-stage3` | OPEN |
| `prop:shooting-stage4` | strictly revalidated |
| `thm:transversality` | strictly revalidated |
| `lem:kernel-short` | strictly revalidated |

Thus the *current snapshot's principal-environment* tally is **9/12 = 75%**, **not a new proof** and not directly comparable with the **historical 9/21 = 42.86%**. There are 13 additional auxiliary `verifiedlemma` environments that must be audited separately if computing a whole-document theorem-like count (25); this audit does NOT assert 22/25 passed.

## Why the different denominators?

The ledger `verification/original-environment-audit-20261028.json` tracks **21 historical original environments**: 9 accepted, 4 open including a historical `prop:global-H1-profile-v3` (old-2.14), and 8 explicitly withdrawn. Multiple old 3.*–5.* theorem environments are no longer present as separate theorem-like environments in the current 2026-10-27 TeX. Their necessary physical PDE proof obligations have NOT all vanished: in particular global homogeneous H¹ matching, constrained Hamilton evolution, physical modulation feedback, actual radiation reconstruction, and blowup orbit existence are still load-bearing tasks even when not given standalone theorem environments.

**Counting rules:**
1. Keep historical 9/21 for original version comparisons. Never falsely announce 10/21 from a helper proof.
2. Use 9/12 only when explicitly discussing the *current 2026-10-27 snapshot's principal environments*, with the text/Lean correspondence qualification above.
3. Do not count additional 13 verifiedlemma environments as accepted without source-bound type and axiom audits.
4. The separate latest `verification/typeii-minimal-main-replacement.tex` changes the future main theorem target to **dynamically selected** (not prescribed) rate, but that corrected target has NOT been inserted into the Library manuscript. The snapshot's older broader `targettheorem` is not the already-verified current proof conclusion.
5. The current numerator did NOT increase by recounting the denominator. The next genuine increment requires strict closure of the actual `prop:one-layer-stage3` or `thm:finite-profile-stage3` or `thm:main`.

## Actual Lean work from this turn

GitHub Actions **40909725810 = success** at `986d3b4573b28f629c2fba0b2c4714bc7e8eb729`. Two additional checked auxiliary declarations integrate actual two-channel Hartree affine Fredholm and prescribed origin-gauge Kummer solves, and certify the nonlocal slow-monopole gain `2 beta - 1 > 0` for the physical R=4/|c| exterior cut-off under explicit primitive exterior L1 source data and amplitude bounds. They do NOT instantiate every actual generated source in `prop:one-layer-stage3`. They do not set the blowup rate.

Next priority: full actual moving-region nonlinearity and source classification; do not restore the old abstract regional-solver/GeneratedTerm terminal as proof of the manuscript.
