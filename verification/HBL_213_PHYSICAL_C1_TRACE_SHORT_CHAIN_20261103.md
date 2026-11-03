# HBL 2.13: canonical C1 traces and the shortest quantitative continuation

This note concerns the SAME radially conjugated Hartree source
`G=r*(1-cutoff(r/R))*F`, `R=ell^(-1/16)`.
It does not count a new manuscript environment. The retained count is 11/13.

## Verified input

The unified two-weight source certificate passed strict CI 41668554240
at commit `2701cef2364f7035257cdc3b8970c9a9e9eeaef7`.
Its downloaded artifact SHA256 is
`54348866a0f1d525c1f62d0f11390d6d8a6d03855f1ec72d5336836aa53566b4`.
The artifact confirms the full theorem type, Lean 4.35.0-rc3, Mathlib
`a98628e16c11f5167f16124105ddce53efa9bfe5`, and only the standard
`propext`, `Classical.choice`, `Quot.sound` axioms.

## New C1 route, without source continuity

For any real H in L1((0,infinity)), set

    q0(r) = integral_0^infinity min(r,rho)*H(rho) d rho.

At every r, the kernel corner rho=r is a null set, and

    |min(r+h,rho)-min(r,rho)| <= |h|.

Dominated differentiation therefore gives

    q0'(r) = integral_(max(r,0))^infinity H(rho) d rho,

with the half-line restriction understood. Dominated convergence shows
that this derivative is continuous. No continuity of H is needed.

For the existing normalized inner Fredholm reconstruction, the total
source is the sum of `weightedGreenDecay*g` and the corrected external
source. The first term is L1 by Cauchy--Schwarz and the second by the
existing weighted-source integrability theorem. Thus both actual
Green representatives are C1. Restore the uniquely forced affine
charges with the unchanged smooth model.

The new Lean files are:

- `HBL/InnerReconstruction/GreenC1Integrable.lean`;
- `HBL/TypeIIDynamicSelection/ActualHartreeConjugatedInnerC1Trace.lean`;
- the corresponding independent `Audit.lean`.

Strict acceptance of the new files must be checked against their own CI;
this note does not assert a successful conclusion for a pending run.

## Correct physical traces

The half-line variable is q=r*u. Consequently the actual traces to use
in the physical Kummer equation are

    u(r)  = q(r)/r,
    u'(r) = (r*q'(r)-q(r))/r^2,        r>0.

They are not q(r), q'(r). The reconstructed functions retain the
weighted almost-everywhere identities with the original normalized
Hilbert solutions and their forced affine tails. A claim of C2
regularity or a pointwise second-order equation for merely measurable
forcing is not made.

## Quantitative continuation: exact first-moment identity

The following is an analytical derivation; its full Lean specialization
is a remaining obligation.

If rho*H is also L1, then for r>0

    q0(r) - r*q0'(r) = integral_0^r rho*H(rho) d rho.

Let M=integral_0^infinity rho*|H(rho)| d rho. Then

    |q0(r)| <= M,
    |(q0(r)/r)'| <= M/r^2.

After affine restoration q=q0+alpha*model, the existing model equals r
for r>=2. Thus

    |q(r)/r-alpha| <= M/r,
    |(q(r)/r)'|    <= M/r^2,          r>=2.

This preserves alpha; it does not silently set a forced resonance
charge to zero.

For the actual reconstruction, proving M=O(ell^(1/16)) can use the
already proved fixed-operator estimate
`HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement`, together with
weighted Green/source operator norms. The constants must be independent
of ell and c. The exact analytic estimate to specialize is

    ||rho*H||_1 <= ||rho*a||_2 ||g||_2
      + ||rho*<rho>^(-sigma)||_2 ||<rho>^sigma * G_corrected||_2,
    a(rho)=(1+rho^2)^(-1), sigma=7/4.

Both fixed scalar L2 factors are finite. The corrected-source norm
must include the two actual affine charges and the norms of the
original affine model sources.

At the outer edge r=2R, R=ell^(-1/16), one would then obtain

    |u(2R)-alpha| = O(ell^(1/8)),
    |u'(2R)|     = O(ell^(3/16)).

These two rate statements are not yet asserted as Lean-accepted.
They are physical-length estimates, not a prescribed concentration-time
law.

## Remaining original manuscript obligations

1. Strict C1 reconstruction and the quantitative uniform first-moment bound.
2. The actual source-dependent Kummer and remote interface defects, with
   all canonical Wronskian conditions retained. One-ended Cauchy matching
   does not imply simultaneous two-ended compatibility.
3. Full generated PDE residual estimates and genuine positive time-order
   finite recursion, including transport/parameter/nonlocal terms.
4. Derive the Type-II blowup dynamics and rate from the PDE.

Original revised 2.13 and the final Type-II main theorem remain OPEN.
