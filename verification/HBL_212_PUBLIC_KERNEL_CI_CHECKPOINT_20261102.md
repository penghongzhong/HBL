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

## 2026-11-02 — verified positive Fredholm source order

**Strict CI success: GitHub Actions 41422910263**, commit 113a235f5ccadc535805ee1cb3e93561c4de04e4.

Verified source: HBL/TypeIIDynamicSelection/ActualHartreeWeightedPositiveOrder.lean.

With 0 < ell <= 1, 3/2 < sigma < 2, a positive lower bound on the actual Hartree physical moment, and the explicit amplitude/quartic Riesz envelope conditions, the TRUE inverse-square nonlocal cutoff commutator satisfies the quantitative original weighted Fredholm norm estimate:

    || <r>^sigma [N(chi_R f_ell) - chi_R N(f_ell)] ||_L2(0,infinity)
      <= C(m_*,B,D,sigma) * ell^(2-sigma),     2-sigma > 0,
    R = 4 / (kappa_H * ell * m(t)),    m(t) >= m_* > 0.

The critical sqrt(ell) radiation amplitude, physical moving support and full nonlocal quartic Riesz kernel are retained; no arbitrary positive source order is postulated.

New submitted CI gates (do not treat as passed without latest completed/success):

- 41422916938: full same-Hartree-PDE shell O(ell^(5/2)) with moment drift and Strauss.
- 41422926588: full three-region Hartree source supplied to constructed normalized Kummer Green inverse.
- 41424071542: exact physical 3D radial Laplacian critical rescaling.
- 41424080804: genuine physical Hartree strong solution -> renormalized radiation PDE.
- 41424509446: same physical flow with dynamical phase -> renormalized radiation PDE.
- 41424723931: Strauss+moment directly imply true positive weighted Fredholm source order.

UNPROVED original 2.12 obligations: whole mixed Vc+Z source uniform offterminal gain, physical moving Kummer/Frobenius/inner/remote jet matching, forced monopole charge, all parameter tangents and positive gains for every generated source class. Original main theorem derives Type-II rate, rather than assuming it.

Retained ORIGINAL manuscript environment count: 9/13; 2.12 NOT yet accepted.
