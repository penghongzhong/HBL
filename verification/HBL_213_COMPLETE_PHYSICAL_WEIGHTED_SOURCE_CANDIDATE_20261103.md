# HBL revised 2.13: complete physical weighted source synthesis — CANDIDATE

## What is newly composed

Source files:
- `HBL/TypeIIDynamicSelection/ActualHartreePhysicalFullWeightedSource.lean`.
- `HBL/TypeIIDynamicSelection/ActualHartreePhysicalFullWeightedL2.lean`.
- `HBL/TypeIIDynamicSelection/ActualHartreePhysicalFullWeightedL2Audit.lean`.

The fields are not independent forcing placeholders. They are the actual moving cutoff core `monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c` and actual critically scaled radiation `rescalePhysicalRadiation ell z`. Their source is `actualOneLayerInteractionOnly`.

The explicit constant `actualHartreePhysicalWeightedSourceConstant B A` depends ONLY on physical amplitude and Strauss bounds B,A and the fixed previously proved kernel constants. It does not depend on ell, c, r, an asserted source order or a blowup-time exponent.

The candidate statement assumes only `0<ell<=1`, `|c|<=1`, `B,A>=0`, physical measurability of z, `norm(z(u))<=B` for u>0, and `u*norm(z(u))<=A` for u>=1. The proof derives all three actual Riesz-potential bounds, the monopole/radiation amplitude envelopes, the complete ten-term source inequality, source measurability, and the original weighted half-line integrability.

Writing F for that actual interaction and w(r)=(1+r²)^(7/8), the composed conclusion is

    MemLp (r ↦ w(r) * norm(F(r))) 2 halfLineMeasure,
    integral_0^infty (w(r)*norm(F(r)))² dr
      <= K(B,A)² * ell^(1/4) * integral_0^infty (1+r)^(-5/4) dr.

The final scalar integral is finite by the pinned Mathlib shifted-power integrability theorem. Its elementary value is 4, but this candidate Lean theorem retains the exact integral rather than asserting an unevaluated numerical equality as a verified fact.

## Repaired dependencies

- Scalar ten-monomial synthesis: source commit `10d1b9a27db3f5f820b3fb5c5ef67917705d3e1b`; natural-vs-real power conversion is explicit; a redundant tactic after a closed division goal was removed. Strict run 41632702166 was submitted, and its final result was not yet accepted when this note was written.
- General half-line integration: commit `58778dd63185e1e1c6627e1cb92e35d681d4561b`; preserves all hypotheses and marks two unused positivity binder names. Earlier ordinary Lake build succeeded; strict run 41632541966 was submitted and remains unaccepted until its successful conclusion is checked.
- Eight-module same-environment integration: run 41624948611 has been checked as strict SUCCESS. It proves compatibility of those auxiliary modules, not the new full source synthesis.
- The physical-source measurability module is copied unchanged from the strictly accepted source `edaea3022e5dcd751a5bd3b78d491ac782de603e` (blob `6182c2e9575a753f2b824646063402e1e78b98bc`).

## New strict synthesis run

https://github.com/penghongzhong/HBL/actions/runs/41633823199

Audited source/workflow commit: `34dcf47bb9fe7facae9721eaf158e6a9f700fc11`.
At the time of this note the run is **in progress**, not accepted. The workflow strictly checks all newly composed source modules and the full theorem types/transitive axioms with Lean 4.35.0-rc3 and Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `--trust=0`, `warningAsError=true`. Only `propext`, `Classical.choice`, `Quot.sound` are allowed. No new axiom, admitted statement or presumed source bound is introduced.

The workflow also retrieves the exact pinned `Mathlib.Tactic` and improper-integral dependency cache. Failure of that OPTIONAL download falls back to ordinary compilation; it never bypasses source compilation or the kernel audit.

## Exact acceptance boundary

Even a successful result here is a **baseline core–radiation nonlinear spatial source theorem**, not the whole residual of an arbitrary iterated V_N. It does not prove the actual matched inner/Kummer/remote correction, the endpoint compatibility equations, all derivative/parameter/Lipschitz bounds, the Kummer terminal algebraic branch, all three physical energy estimates, the slow Hessian remainder, or positive time-order gains for every generated term in the finite recursive profile. Those obligations must not be hidden in an abstract packet or shifted into a blowup-rate assumption.

The Type-II orbit and its rate must still be derived from the original PDE dynamics. Revised numbered manuscript acceptance remains **11/13**, unchanged. This note is not a 12/13 acceptance certificate.
