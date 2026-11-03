# HBL 2.13 — canonical first-moment and physical trace estimates: strict accepted

## Acceptance

- Dedicated CI: https://github.com/penghongzhong/HBL/actions/runs/41741745130 — completed/success.
- Audited source commit: `4b221d6c1be172291c2c3888c3aa80e3b678c543`.
- Build completed successfully: 4082 Lake jobs.
- Compiler: Lean 4.35.0-rc3, commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- All three new source files passed `lake env lean --trust=0 -DwarningAsError=true`; `green-strict.log`, `moment-strict.log`, `physical-strict.log` are empty.
- Independent audit checks the complete explicit types and transitive axioms of six declarations. All use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Artifact: `HBL_CANONICAL_MOMENT_TRACE_STRICT_41741745130.zip`, artifact ID 13282360476, size 22083 bytes.
- SHA256 independently checked after download: `d4bc4ac119e8bea40fb1ae3ed562b1d3f7653368847d90a0e5cae4c30d150653`.
- The downloaded commit, toolchain, Mathlib pin, strict logs, build result and all six full types/axiom lists were inspected.

The previous attempt had already passed all mathematical source compilations but its audit printer emitted universe-decorated names `Classical.choice.{u}` and `Quot.sound.{u}`. Only the universe-display option was corrected. The theorem assumptions and conclusions, compiler checks and axiom whitelist were not weakened.

## Exactly proved

For H integrable against the original half-line Lebesgue measure, with its first moment integrable, put

    q0(r) = integral_0^infinity min(r,rho)*H(rho) d rho.

The exact identity is

    q0(r)-r*q0'(r) = integral_(0,r] rho*H(rho) d rho.

For the ACTUAL normalized inner reconstruction, the total source is

    H = a*g + Fcorr,     a(r)=(1+r^2)^(-1),

not Fcorr alone. Its first moment is proved integrable from the real L2 datum g and original weighted source, and

    integral rho*|H(rho)| d rho <= innerGreenBound(g,Fcorr).

Here

    innerGreenBound(g,Fcorr)
      = integral |rho*a(rho)*g(rho)| d rho
        + integral |rho*Fcorr(rho)| d rho.

With the unchanged forced affine charge alpha and actual smooth affine model, set

    q = Green(H)+alpha*model,     u(r)=q(r)/r.

The accepted quantitative physical traces, for r>2, are

    |u(r)-alpha| <= innerGreenBound(g,Fcorr)/r,
    |u'(r)|     <= innerGreenBound(g,Fcorr)/r^2.

These are specialized to BOTH channels of the SAME original conjugated Hartree interaction source

    G=r*(1-cutoff(r/R))*F_{ell,c},    R=ell^(-1/16).

The exported physical theorem retains both exact affine-restored Green reconstruction identities, both weighted almost-everywhere identities with the normalized Hilbert solutions, and both original affine-tail properties. It does not substitute arbitrary functions or independent boundary data.

## Accepted declarations

1. `HBL.Modulation.Monopole.halfLineMinGreen_sub_radius_slope_eq_firstMoment`.
2. `HBL.Modulation.Monopole.halfLineMinGreen_firstMoment_bounds`.
3. `HBL.Modulation.Monopole.halfLineMinGreen_affine_physical_trace_firstMoment`.
4. `HBL.Modulation.Monopole.innerGreenRepresentative_total_source_firstMoment`.
5. `HBL.Modulation.Monopole.innerGreenRepresentative_affine_physical_trace_bounds`.
6. `HBL.TypeIIDynamicSelection.actual_Hartree_conjugated_inner_canonical_moment_traces`.

Sources: `HBL/InnerReconstruction/GreenFirstMomentTrace.lean`, `HBL/InnerReconstruction/RepresentativeFirstMomentTrace.lean`, `HBL/TypeIIDynamicSelection/ActualHartreeConjugatedInnerMomentTrace.lean`; the last has a separate `Audit.lean`.

## Boundary: what is NOT yet accepted

The finite constants above depend on the actual normalized Hilbert unknowns. Their uniform O(ell^(1/16)) estimate is not asserted as Lean-accepted here. The explicit analytic reduction through fixed Fredholm inverse norms and the corrected-source weighted norm is recorded in `verification/HBL_213_UNIFORM_FIRST_MOMENT_REDUCTION_20261104.md`.

Likewise, the two estimates O(ell^(1/8)) for u(2R)-alpha and O(ell^(3/16)) for u'(2R) remain pending that uniform specialization. The charge alpha must not be discarded.

Canonical Kummer/remote simultaneous matching, complete generated PDE residual estimates, finite nonlinear profile recursion and the dynamically derived Type-II blowup law remain separate open obligations. These six supporting declarations do not constitute the entire retained manuscript 2.13. **Numbered manuscript acceptance remains 11/13 (84.62%).**
