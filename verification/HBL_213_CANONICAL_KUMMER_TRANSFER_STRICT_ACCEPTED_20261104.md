# HBL 2.13 — canonical Hartree inner traces to same-source Kummer transfer: strict accepted

## Inspected immutable evidence

- Dedicated CI: https://github.com/penghongzhong/HBL/actions/runs/41749430663 — completed/success.
- Source commit: `9674319b2ce9c2f315ed6f945a8b3652f75abf52`.
- Complete Lake build: **4102 jobs**, success.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Both new mathematical sources passed `--trust=0 -DwarningAsError=true`; `transfer-strict.log` and `physical-strict.log` are empty.
- Full exported types and all three transitive axiom lists were inspected: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Artifact ID 13284593830, 11229 bytes: `HBL_CANONICAL_KUMMER_TRANSFER_STRICT_41749430663.zip`.
- Independently computed artifact SHA256: `5ca7fec82a1efebb5293a81d9347e05ea041089fbc1e971c69deb767ffc94f54`, equal to the GitHub digest.
- The actual commit, compiler pin, dependency pin, build result, source hashes, empty strict logs and complete mathematical quantifiers were checked after downloading.

Sources:
- `HBL/TypeIIDynamicSelection/ActualKummerSameSourceJetTransfer.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeCanonicalKummerTransfer.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeCanonicalKummerTransferAudit.lean`

## Exact mathematical scope

Let T_K[F](U,DU) be the existing physical right-boundary Kummer transfer for a genuine normalized LocalKummerPair K and the same source F on the positive annulus [z-d,z+d]. Define

    J_K(t)=|phi(t)|+|dphi(t)|+|psi(t)|+|dpsi(t)|,
    A_K(d)=J_K(d)*J_K(-d)/|W_K(-d)|.

The first two new declarations prove exact cancellation of the SAME inhomogeneous Green source and the actual nonzero Wronskian bound

    |T_K[F](U,DU)_value - T_K[F](A,DA)_value|
      + |T_K[F](U,DU)_slope - T_K[F](A,DA)_slope|
    <= A_K(d)*(|U-A|+|DU-DA|).

This is not a comparison of independently chosen sources, nor an assertion that arbitrary remote data are compatible. It is an exact difference of the previously defined physical Green transfers.

The third declaration composes this result with the STRICTLY ACCEPTED uniform physical inner moment theorem. For each B,A>=0, Cp,Cm are chosen BEFORE ell,c,z. The actual conjugated source G=r*(1-cutoff(r/R))*F_ell,c, its two weighted source memberships, and a normalized x satisfying BOTH original corrected Fredholm equations are constructed. The exact canonical affine-restored Green representatives determine uplus and uminus, and their derivatives are proved to be actual derivatives at the positive physical interface r0=z-d>2.

Put

    U=uplus(r0)+i*uminus(r0),
    DU=uplus'(r0)+i*uminus'(r0),
    alpha=actualPlusCharge(gp)+i*actualMinusCharge(gm).

The forcing in BOTH compared transfers is explicitly
`actualHartreePhysicalSliceInteraction ell c z`.
The accepted conclusion is

    |Delta value|+|Delta slope|
    <= A_K(d)*(Cp+Cm)*ell^(1/16)*(1/r0+1/r0²),

where Delta compares T_K[F](U,DU) with T_K[F](alpha,0). The forced affine charge is RETAINED in the reference solution. No smallness of an arbitrary boundary jet is assumed.

At r0=2*ell^(-1/16), elementary substitution gives the bound

    A_K(d)*(Cp+Cm)*(ell^(1/8)/2+ell^(3/16)/4).

This last scalar substitution is an analytical corollary; the audited exported theorem states the stronger all-r0>2 expression above, without assuming a scale law.

## Boundaries and next noncircular step

A_K(d) is an explicit FINITE quantity for each actual pair/annulus. This audit does NOT prove its uniform bound as the physical annulus moves to infinity. Nor does it identify T_K[F](alpha,0) with an independently constructed remote solution or with the manuscript's origin/outgoing normalization. Those compatibility conditions remain distinct.

For merely measurable radiation the theorem concerns the exact transfer expressions and the genuinely differentiable inner traces. It does not add a classical C2 claim about the inhomogeneous Kummer particular solution. The already established homogeneous difference is the useful object for the next scale-uniform estimate.

A shorter analytical route for that estimate is recorded separately in `HBL_213_SHEARED_KUMMER_UNIFORM_TRANSFER_REDUCTION_20261104.md`: a derivative shear and unit-modulus phase remove the large imaginary radial drift. This route is NOT included in the present Lean acceptance.

Full generated residual estimates, simultaneous three-region matching, finite nonlinear profile recursion and the dynamically derived Type-II blowup rate remain OPEN. **Retained manuscript environments remain 11/13 (84.62%).** No auxiliary declaration is relabeled as the entire environment 2.13.
