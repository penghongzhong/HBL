# HBL 2.13: strictly accepted canonical C1 traces and quantitative continuation

This note concerns the SAME radially conjugated Hartree source
`G=r*(1-cutoff(r/R))*F`, `R=ell^(-1/16)`.
It does not count a new manuscript environment. The retained count is 11/13.

## Strict acceptance of the strengthened canonical statement

- Dedicated workflow: https://github.com/penghongzhong/HBL/actions/runs/41682848118 — completed/success.
- Audited source commit: `6901ec42c0239fae1149a609211dbc1dcd3728da`.
- Build completed successfully: 4079 Lake jobs.
- Compiler: Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Both source modules passed `--trust=0 -DwarningAsError=true`; `green-strict.log` and `physical-strict.log` are empty.
- Independent audit printed the complete exported types and transitive axioms. Both theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- Downloaded artifact: `HBL_CANONICAL_INNER_C1_STRICT_41682848118.zip`.
- Artifact ID: 13252684630; size: 10290 bytes.
- Independently checked SHA256: `6b11c63c7fbb504f05c24b5be812dc666234b7f9c112247ffa55f55ac6a6ba26`.
- The downloaded commit, compiler, Mathlib pin, both strict logs and full exported declarations were inspected.

Accepted public theorems:

1. `HBL.Modulation.Monopole.halfLineMinGreen_C1_of_integrable`.
2. `HBL.TypeIIDynamicSelection.actual_Hartree_conjugated_inner_C1_physical_traces`.

Files:

- `HBL/InnerReconstruction/GreenC1Integrable.lean`;
- `HBL/TypeIIDynamicSelection/ActualHartreeConjugatedInnerC1Trace.lean`;
- `HBL/TypeIIDynamicSelection/ActualHartreeConjugatedInnerC1TraceAudit.lean`.

The strengthened theorem explicitly exports the EXACT canonical Green
reconstruction equalities for both affine-restored representatives,
the weighted almost-everywhere identities with the normalized Hilbert
solutions, the actual forced affine charges, C1 regularity and the
physical q/r derivative formula. Thus it is not merely an existence
statement for arbitrary smooth functions with suitable affine slopes.

The preceding weaker exported statement passed run 41682061009 at
`fa04e9190398325062a2d529a990bf445152baa4`; the present acceptance uses
the stronger statement and newer successful run above.

## Previously verified input

The unified two-weight source certificate passed strict CI 41668554240
at commit `2701cef2364f7035257cdc3b8970c9a9e9eeaef7`.
Its downloaded artifact SHA256 is
`54348866a0f1d525c1f62d0f11390d6d8a6d03855f1ec72d5336836aa53566b4`.
It uses the same fixed compiler, Mathlib and standard axioms.

## Accepted C1 route, without source continuity

For any real H in L1((0,infinity)), set

    q0(r) = integral_0^infinity min(r,rho)*H(rho) d rho.

The corner rho=r is a null set for the original half-line Lebesgue
measure, and

    |min(r+h,rho)-min(r,rho)| <= |h|.

Dominated differentiation gives

    q0'(r) = integral_(max(r,0))^infinity H(rho) d rho,

with the half-line restriction understood. Dominated convergence proves
that this derivative is continuous. No continuity of H is needed.

For the actual normalized inner Fredholm reconstruction, the total
source is the sum of `weightedGreenDecay*g` and the corrected external
source. The first is L1 by Cauchy--Schwarz and the second by the existing
weighted-source integrability theorem. Both actual Green representatives
are therefore C1; the uniquely forced affine tails are then restored
with the unchanged smooth model.

## Accepted physical traces

The half-line variable is q=r*u. Consequently

    u(r)  = q(r)/r,
    u'(r) = (r*q'(r)-q(r))/r^2,        r>0.

The physical Kummer traces are not q(r), q'(r). A claim of C2 regularity
or a pointwise second-order equation for merely measurable forcing is
not made. Trace existence is not quantitative trace smallness and does
not imply simultaneous inner/Kummer/remote matching.

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

This preserves alpha; no forced resonance charge is silently set to zero.

To prove M=O(ell^(1/16)) for the actual reconstruction, one can use
`HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement` and the actual
weighted Green/source operator bounds. All constants must be independent
of ell and c. The first-moment estimate to specialize is

    ||rho*H||_1 <= ||rho*a||_2 ||g||_2
      + ||rho*<rho>^(-sigma)||_2 ||<rho>^sigma * G_corrected||_2,
    a(rho)=(1+rho^2)^(-1), sigma=7/4.

Both fixed scalar L2 factors are finite. The corrected-source norm
must include the actual affine charges and the norms of the original
affine model sources. At r=2R, R=ell^(-1/16), this would give

    |u(2R)-alpha| = O(ell^(1/8)),
    |u'(2R)|     = O(ell^(3/16)).

These quantitative trace bounds are NOT yet Lean-accepted. They are
physical-length estimates, not a prescribed concentration-time law.

## Remaining original manuscript obligations

1. The quantitative uniform first-moment and physical trace bounds.
2. Actual source-dependent Kummer and remote interface defects, retaining
   all canonical Wronskian conditions. One-ended Cauchy matching does not
   imply simultaneous two-ended compatibility.
3. Full generated PDE residual estimates and genuine positive time-order
   finite recursion, including transport, parameter and nonlocal terms.
4. Derive the Type-II blowup dynamics and rate from the original PDE.

Original revised 2.13 and the final Type-II main theorem remain OPEN.
The accepted auxiliary C1 trace theorem does not change the retained
manuscript count: 11/13 (84.62%).
