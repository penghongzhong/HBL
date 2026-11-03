# HBL 2.13: radial conjugation scope audit (2026-11-03)

The accepted full interaction estimate (CI 41635003260, commit 6dcf989abf7842f5e0fd9561bf8ae01a175f7844) is an estimate for the RAW radial physical nonlinear source F. It remains valid.

CI 41644827136 at commit 38f9cb4e3ce0784abb77ccbb74cde612f242326c strictly verified the unique affine-corrected H+/H- Fredholm solution with data Re F and Im F. All three declarations and their transitive axiom audits passed. This is a valid AUXILIARY half-line solve, not yet a physical radial PDE correction.

## Missing same-object interface

`HBL/MonopoleRadialLinearization.lean` proves the original relation

    radialLaplacian(q/r) + radialHartreeFirstVariation(q/r) = -Hplus(q)/r

for the actual monopole profile, and proves the local quotient Laplacian identity from derivatives. The half-line operators in `HBL/AffineTailOperators.lean` act on q=r*u. Consequently a radial residual F requires the conjugated half-line forcing r*F when cancelling with this sign convention. Solving H q = F alone does NOT cancel F in the original radial PDE.

The source-to-inner theorem added this turn uses unmultiplied F. It must not be interpreted as closing the physical PDE correction or as closing original 2.13. The corresponding raw-source affine pairings also must not be identified with the charges for r*F.

## Constructive repair under verification

Retain the required radius factor and introduce an explicit auxiliary regional cutoff:

    chi_ell(r) = 1 - cutoff(r * ell^(1/16)),
    G_ell,c(r) = r * chi_ell(r) * F_ell,c(r).

The desired elementary estimate is

    0 <= r*chi_ell(r),
    (r*chi_ell(r))*ell^(1/16) <= 2.

Together with the accepted raw-source estimate this yields the target

    <r>^(7/4) |G_ell,c(r)|
      <= 2*K(B,A)*ell^(1/16)*(1+r)^(-5/8).

It then supplies genuine conjugated localized source membership to the existing H+/H- solver. The exponent 1/16 selects a spatial matching scale only; it is not a prescribed time or blowup rate.

This auxiliary cutoff is NOT the previously constructed radiation-moment cutoff at radius 4/|c|. Its cutoff derivatives, transport terms, nonlocal commutators, complement source and compatibility with Kummer/remote matching remain separate obligations. No claim that these obligations are already solved is made.

Manuscript acceptance remains **11/13 (84.62%)**. Three-region C1 matching, actual higher-profile residual closure, finite recursion and the PDE-derived Type-II rate remain OPEN.
