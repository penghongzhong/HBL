# HBL original 2.12 — Public strict Lean kernel checkpoint, 2026-11-02

Repository: `penghongzhong/HBL`  
Branch: `hbl-212-physical-spatial-commutator-gain-20261102`  
Toolchain: Lean `4.35.0-rc3`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.

## Newly independently verified physical PDE-bearing facts

The following are actual completed `success` GitHub Actions runs, each
strictly building the named source/audit with `--trust=0`,
`-DwarningAsError=true`, no `sorry` or new axiom, and checking
the transitive kernel axiom list:

| Exact theorem family | Strict Actions run | Result |
|---|---:|---|
| True moving-cutoff radial Laplacian, critical spatial bound | 41395549631 | success |
| Full original nonlocal quartic Riesz cutoff commutator | 41395910689 | success |
| Sharp full nonlocal Riesz source `O(ell^2 sqrt(ell))` | 41398453496 | success |
| Full local/nonlocal physical cutoff support | 41400712349 | success |
| Exact same-Hartree-PDE moving shell residual identity and bound | 41403278062 | success |
| Actual 3D Riesz integral source measurability | 41400757243 | success |
| True Riesz source belongs to original weighted `L^{2,sigma}` | 41403722028 | success |
| Quantitative actual nonlocal source weighted `L²` with `sqrt(2R)` | 41408648791 | success |
| One genuinely nonzero terminal physical Hartree radiation in weighted `L²` | 41408743104 | success |
| Actual PDE terminal nonzero quartic moment controls moving radius `R=O(ell^-1)` | 41408997770 | success |
| Exact physical moment-radius drift `R_s/R-b=-ell²*m'(t)/m(t)` | 41415142938 | success |
| Strauss radial envelope leads to actual Hartree quartic nonlocal source | 41409501725 | success |
| Strauss-to-original-weighted-Fredholm true Riesz estimate | 41415407511 | success |
| Arora--Roudenko 2020 cited local PDE theory interface (conditional high regularity) | 41405467883 | success |
| True full moving-PDE core Riesz-only and remote zero identities | 41407902222 | success |

The critical output has the exact physical scale
`f_ell(r)=sqrt(ell)*z(ell*r)`, the true inverse-square convolution,
and the true moving radius `R=4/(kappa_H*ell*m_0(t))`.
No local-cubic surrogate is used.

## Hard original acceptance rule

The reconciled private paper retains **13 original numbered environments**.
**9/13** have been strictly accepted; **4 remain open**:

1. `prop:one-layer-stage3` (old 2.12): canonical localized physical H+/H-,
   Kummer and remote correction, SAME complete source, and all positive
   generated orders in the actual original `X_f^sc` norm.
2. `thm:finite-profile-stage3` (old 2.13): actual finite dynamic PDE
   recursion, not just an abstract packet iteration.
3. `prop:global-H1-profile-v3` (old 2.14): full genuine global energy
   matching and terminal algebraic Kummer correction.
4. `thm:main`: a genuine 3D energy-critical radial Hartree Type II
   blowup orbit with its concentration-rate law DERIVED from the PDE.

The abstract `oneMinimalWeightCluster_eliminated` and auxiliary
build-success count do not upgrade old 2.12 by themselves.

## Current next gate

- Physically uniform quantitative `ell^(2-sigma)` genuine Riesz gain:
  `ActualHartreeWeightedPositiveOrder.lean`.
- Same physical one-orbit full Hartree moving-shell `ell^(5/2)`:
  `ActualHartreeOneOrbitFullShellSharp.lean`.
- Constructed Kummer Green inverse on the SAME remote-Riesz Hartree source:
  `ActualHartreeThreeRegionKummerCertificate.lean`.

These are strict-CI source branches; do not count as accepted unless
their newest GitHub Actions runs report `success`.

**Never claim old 2.12 complete without Kummer/Frobenius moving-boundary
source-to-jet estimates, remote matching, physical parameter tangents and
positive gain of all true residual classes. Do not impose the final blowup
rate as a theorem hypothesis.**
