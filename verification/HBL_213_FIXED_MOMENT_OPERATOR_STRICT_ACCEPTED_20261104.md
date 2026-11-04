# HBL 2.13 — fixed Fredholm inverse to uniform moment constants: strict accepted

## Immutable evidence

- CI 41744443804: completed/success.
- URL: https://github.com/penghongzhong/HBL/actions/runs/41744443804
- Audited source commit: `c0e36a064df2b29f7d1f7df89403d2314513086b`.
- Build completed successfully: 3933 Lake jobs.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Source passed `--trust=0 -DwarningAsError=true`, with an empty source-strict.log.
- Full explicit exported declarations and transitive axioms were inspected. Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Downloaded artifact ID 13283151018: `HBL_UNIFORM_MOMENT_OPERATOR_STRICT_41744443804.zip`, 17812 bytes.
- Independently computed SHA256: `2a126fa98cbf0ec11311d3af0136d6b00761ee730b68b4350a18d667bea8e3eb`.

## Exactly proved by reusing the existing code pool

Let JF be the original sigma=7/4 weighted half-line L2 source datum, S the already constructed cross-space Green operator, V the actual weighted potential operator, and

    Na = ||r*(1+r²)^(-1)||_2,
    Ns = ||r*<r>^(-7/4)||_2.

Both weights are the existing proved L2 functions, not assumed constants. The exact total first-moment bound obeys

    innerGreenBound(g,F) <= Na*||g||_2 + Ns*||JF||_2.

The previously accepted compact Fredholm kernel-complement theorem supplies Cp,Cm for the two fixed physical operators. These constants are derived from compactness and normalization, not new hypotheses. Thus for ANY normalized pair satisfying the actual two Fredholm equations,

    Mplus  <= Dplus * ||JFplus||_2,
    Mminus <= Dminus * ||JFminus||_2,

where one may take

    Dplus  = Na*||V||*Cp*||S|| + Ns,
    Dminus = 3*Na*Cm*||S|| + Ns.

The existential Dplus,Dminus precede all sources and unknowns in the formal statement. Hence they are uniform with respect to ell,c and the physical radiation field when this theorem is specialized. The potential part of the reconstructed source is retained.

Accepted public declarations:

1. `HBL.Modulation.Monopole.actual_innerGreenBound_le_fixed_weight_norms`.
2. `HBL.Modulation.Monopole.actual_inner_fixed_Fredholm_moment_constants`.

Source: `HBL/InnerReconstruction/UniformMomentOperatorBound.lean`; independent `Audit.lean` has full types and axiom lists.

## Scope boundary

The separately submitted `ActualHartreeUniformInnerMoment.lean` specializes these bounds to the SAME true conjugated Hartree source, includes the forced affine charges and aims to prove Mplus,Mminus=O(ell^(1/16)). Its dedicated run 41744999144 is pending at the time this operator-only record is written; this record does not certify that synthesis.

This operator acceptance is not the original full finite-profile environment 2.13. Simultaneous Kummer/remote matching, complete generated residual estimates and the PDE-derived Type-II law are not asserted. Retained manuscript count: 11/13.
