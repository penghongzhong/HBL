# HBL 2.13 — uniform physical inner moments and traces: strict accepted

## Accepted synthesis

The previously pending claim Mplus,Mminus=O(ell^(1/16)) is now proved for the SAME actual conjugated Hartree interaction and its normalized two-channel inner solution. This is not an added moment hypothesis.

- Dedicated CI: https://github.com/penghongzhong/HBL/actions/runs/41744999144 — completed/success.
- Audited source commit: `5acb7c854c0f09a2b9b6cc0955ce7e915972da4a`.
- Build: 4074 Lake jobs, completed successfully. Accumulated exact-toolchain compiled dependencies were reused.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Both new source files passed `--trust=0 -DwarningAsError=true`; operator-strict.log and physical-strict.log are empty.
- Three public declarations were audited transitively: only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`.
- Downloaded artifact ID 13282649945: `HBL_UNIFORM_PHYSICAL_MOMENT_STRICT_41744999144.zip`, 28586 bytes.
- Independently computed SHA256: `3f8b9acc61f328b6eaf4767c0f86313e855bf2c9f05bfd5c9031a7a76349875e`.
- The downloaded commit, toolchain, dependency pin, source hashes, empty strict logs, build result, axiom lists and quantifier order were inspected alongside the full source declarations.

The fixed-operator part also passed independent CI 41744443804 at commit `c0e36a064df2b29f7d1f7df89403d2314513086b`.

## Readable full-statement re-audit

- Subsequent CI: https://github.com/penghongzhong/HBL/actions/runs/41745426260 — completed/success.
- Re-audited commit: `f89672d00f1cc3e8d6bd23a2be3d6473bf09c828`.
- The only Lean change from the original acceptance is audit printing: instance-elaboration noise is no longer expanded, leaving all mathematical hypotheses and the uniform quantifier order readable. No mathematical source, theorem assumptions/conclusions, strict build flags or axiom whitelist changed.
- Both mathematical source SHA256 values were compared with the first successful artifact and are IDENTICAL.
- Both strict source logs remain empty; build again completed successfully with 4074 jobs.
- Artifact ID 13282584032: `HBL_UNIFORM_PHYSICAL_MOMENT_STRICT_41745426260.zip`, 10606 bytes.
- Independently computed SHA256: `c271731cd35dda586b56adea1ed5abcdaeac0862d653ad2113eeb8de6520bc62`.
- The readable exported type was checked: B,A precede the existential Cplus,Cminus, which precede ell,c,z; all physical source assumptions, both actual Fredholm equations, both canonical representatives and all four trace inequalities are visible. All three transitive axiom lists remain standard only.

## Quantifiers and the actual source

For every fixed B,A>=0, the theorem constructs finite constants Cplus,Cminus>=0 BEFORE quantifying over ell,c,z. The only subsequent assumptions are

    0<ell<=1, |c|<=1,
    z measurable,
    |z(u)|<=B for u>0,
    u*|z(u)|<=A for u>=1.

Let R=ell^(-1/16), and let

    G(r)=r*(1-cutoff(r/R))*F_{ell,c}(r),
    gp=Re G, gm=Im G,

where F is the complete ORIGINAL physical nonlocal quartic Hartree interaction. The cutoff is applied after the global convolution; the required radial factor r is retained.

The exported theorem constructs the actual weighted memberships hp,hm and a normalized x in the product of the two physical Fredholm kernel complements. BOTH original corrected-source equations are explicit conclusions, not assumptions. For

    gplus = weightedPotentialOperator(x.plus),
    gminus = 3*x.minus,
    Fplus = correctedPlusSource(gp),
    Fminus = correctedMinusSource(gm),

it proves

    innerGreenBound(gplus,Fplus) <= Cplus * ell^(1/16),
    innerGreenBound(gminus,Fminus) <= Cminus * ell^(1/16).

Thus the total reconstructed source includes both the potential part and the corrected external forcing. The unknown-dependent constants from the preceding first-moment lemma are now uniformly controlled.

For the EXACT canonical representatives

    qplus  = affineRestore(Green(gplus,Fplus), actualPlusCharge(gp)),
    qminus = affineRestore(Green(gminus,Fminus), actualMinusCharge(gm)),
    uplus(r)=qplus(r)/r, uminus(r)=qminus(r)/r,

all r>2 satisfy

    |uplus(r)-alphaPlus| <= Cplus*ell^(1/16)/r,
    |uplus'(r)|         <= Cplus*ell^(1/16)/r²,
    |uminus(r)-alphaMinus| <= Cminus*ell^(1/16)/r,
    |uminus'(r)|           <= Cminus*ell^(1/16)/r².

The original uniquely forced affine charges alphaPlus,alphaMinus have NOT been discarded. The actual fixed-point equations prevent the theorem from selecting arbitrary functions with convenient traces.

## Reuse of the accepted proof pool

The proof composes, rather than re-proves:

- the full physical source and critical tail square-integrability;
- the correct radially conjugated localized source envelope;
- the actual two-channel weighted source and forced affine charge estimates;
- the fixed compact Fredholm inverse on the true kernel complements;
- the existing model-source weighted memberships;
- the exact total first-moment and physical quotient trace estimates.

With Na=||r*a||_2, Ns=||r*<r>^(-7/4)||_2, L=||(1+r)^(-5/8)||_2, K=K(B,A), T=|physicalChargeTailConstant| and Ap,Am the fixed weighted model-source norms, the construction uses

    Dp=Na*||V||*Cp_inverse*||S||+Ns,
    Dm=3*Na*Cm_inverse*||S||+Ns,
    Cplus=Dp*(2*K*L+4*K*T*Ap),
    Cminus=Dm*(2*K*L+2*K*T*Am).

All factors except K depend only on fixed physical kernels/operators and fixed scalar weights. No concentration-time exponent or source decay rate is a new hypothesis.

Main declaration:
`HBL.TypeIIDynamicSelection.actual_Hartree_uniform_canonical_inner_moments_and_traces`.

Sources:
`HBL/InnerReconstruction/UniformMomentOperatorBound.lean` and
`HBL/TypeIIDynamicSelection/ActualHartreeUniformInnerMoment.lean`, each with an independent audit module.

## Remaining manuscript obligations

Uniform first-moment smallness and its quantitative physical trace consequences are now CLOSED. The full retained manuscript environment 2.13 is still OPEN: the same physical source must be assembled through canonical Kummer/remote compatibility and all generated residual estimates before finite recursion. The final Type-II rate must still be derived from PDE dynamics. This result is physical LENGTH smallness, not an assumed time law.

Manuscript acceptance remains 11/13 (84.62%). This record supersedes the older notes calling uniform first-moment specialization pending, but does not relabel an auxiliary theorem as full 2.13.
