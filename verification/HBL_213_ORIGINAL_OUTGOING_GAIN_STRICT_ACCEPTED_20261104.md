# HBL 2.13 — actual Hartree source in the original origin-gauge Green inverse: STRICT ACCEPTED

## Independently inspected evidence

- Strict CI: https://github.com/penghongzhong/HBL/actions/runs/41764243033 — completed/success.
- Audited source commit: `2eb22b0ab20301d0f676b47a1e6d77b8f8be175f`.
- Complete integrated build: **4100 Lake jobs**, success. This is a build-job count, NOT a manuscript-environment count.
- Lean 4.35.0-rc3; compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Artifact 13291508197, 16668 bytes, downloaded as `HBL_ORIGINAL_OUTGOING_GAIN_STRICT_41764243033.zip`.
- Independently recomputed archive SHA256: `0ce07214a3b027f46806ed08bafa499e2f8d20d54d80d2fcb7900dd45f3ca4bc`, equal to the GitHub digest.
- Both mathematical sources passed `--trust=0 -DwarningAsError=true`; both archived strict logs are empty.
- All THREE archived source hashes were recomputed and checked. The TWO mathematical sources also match the independently prepared local copies byte-for-byte.
- All SIX complete exported declaration types and all SIX transitive axiom lists were inspected. Dependencies are restricted to `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or new axiom.
- The first attempt 41763903776 already compiled both mathematical sources. Its only error was an unsupported audit-printing option. The successful commit changes only the audit output, not either mathematical proof.

New mathematical sources:
- `HBL/TypeIIDynamicSelection/ActualOriginGreenIntegrable.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeOriginOutgoingGain.lean`

Audit:
- `HBL/TypeIIDynamicSelection/ActualHartreeOriginOutgoingGainAudit.lean`

## 1. Direct use of the existing original normalized inverse

The preceding accepted charge-reference result estimated an inhomogeneous Cauchy transfer. Smallness of that transfer does NOT imply the manuscript's original separated endpoint conditions. This continuation instead inserts the SAME physical forcing directly into the EXISTING origin-normalized Green inverse; it does not identify two different solutions by fiat.

Fix a compact parameter set P and a prescribed positive annulus 0 < r0 < r1. The already constructed `OriginKummerPair` provides the singular/regular origin-gauge basis Phi,Psi, with

    W(r) = Phi(r)*Psi'(r)-Phi'(r)*Psi(r)
         = r^(-2)*exp(-i*r^2/4) != 0.

The pair is constructed once for each parameter, independently of all physical sources. Its annular value/slope and inverse-Wronskian bounds use one constant C for every parameter in P.

For an interval-integrable F, use the ORIGINAL definitions

    A(r) = integral_r^r1 Psi(t)*F(t)/W(t) dt,
    B(r) = integral_r0^r Phi(t)*F(t)/W(t) dt,
    U(r) = Phi(r)*A(r)+Psi(r)*B(r),
    V(r) = Phi'(r)*A(r)+Psi'(r)*B(r).

Both Wronskian source densities are proved interval integrable, using continuity of the true basis and its nonzero Wronskian. Thus the argument does not exploit Lean's zero value for an undefined integral.

The interval Lebesgue differentiation theorem gives the actual differential system almost everywhere:

    U' = V,
    V' + (2/r+i*r/2)*V + (theta+i*(1/4-mu))*U = F.

The derivative of V is genuinely established by `HasDerivAt`; it is not merely an algebraic name for an unverified second derivative. For merely measurable forcing the formal conclusion is this a.e. first-order system, NOT an unsupported everywhere-classical C2 assertion.

The original FINITE-ANNULUS endpoint normalizations hold EXACTLY:

    U(r1)*Psi'(r1)-V(r1)*Psi(r1) = 0,
    Phi(r0)*V(r0)-Phi'(r0)*U(r0) = 0.

These are the existing separated Green conditions. They must not be reinterpreted as an independently proved radiation condition at infinity.

## 2. Same complete physical base-core/radiation Hartree source

Retain precisely the previously accepted physical interaction F_{ell,c,z}, including its three original Riesz potentials and all ten terms. Keep the explicit spatial scaling

    F_K(r) = a^2 * F_{ell,c,z}(a*r),   a > 0.

The inherited physical assumptions are B,A >= 0, 0 < ell <= 1, |c| <= 1, measurable z, |z(u)| <= B for u > 0, and u*|z(u)| <= A for u >= 1.

The already accepted radius-square bound yields

    |F_K(r)| <= Q(B,A)*ell^(1/8)/r0^2,  r0 <= r <= r1.

Measurability of F_K is derived from the SAME moving monopole and rescaled radiation. Its interval integrability is then derived from the displayed bound. Neither continuity nor interval integrability of this physical source is an added premise.

Consequently the ORIGINAL Green construction satisfies

    sup_[r0,r1] (|U|+|V|)
      <= D * Q(B,A) * ell^(1/8),
    D = 2*C^3*(r1-r0)/r0^2 > 0,

together with the genuine source integrability, a.e. equation and both exact endpoint identities above.

The constant is uniform in a,ell,c,z under fixed B,A, and uniform over P. The annulus is PRESCRIBED AND FIXED: dependence on r0,r1 is explicit, and no bound uniform as r0 tends to zero or r1 tends to infinity is claimed.

## 3. Audited public declarations

- `actual_origin_Green_source_integrability`
- `actual_origin_Green_integrable_forcing_ae_equation`
- `actual_Hartree_scaled_Kummer_source_measurable`
- `actual_Hartree_scaled_Kummer_source_intervalIntegrable`
- `actual_Hartree_origin_outgoing_gain_on_annulus`
- `exists_actual_Hartree_original_outgoing_uniform_gain`

The last theorem constructs the normalized basis BEFORE quantifying over B,A,ell,c,a,z. In particular its basis and uniform constant are not supplied by a source-dependent solver assumption.

## 4. Proof-chain simplification and exact remaining obligations

For this base-source normalized-inverse estimate, the shorter chain is now:

    accepted complete physical weighted source
      -> exact a^2 scaling and radius-square estimate
      -> constructed origin-gauge Green inverse
      -> integrable source densities and actual a.e. system
      -> exact original finite-annulus endpoint conditions and 1/8 gain.

It is unnecessary to infer the normalized conditions from a small arbitrary Cauchy reference. The earlier Cauchy/charge results remain available for the still-needed comparison with actual inner traces, but are not substitutes for that comparison.

This continuation does NOT identify the normalized Green solution with the independently selected inner or remote solution. It also does NOT complete the full time-dependent Hartree-to-frozen-operator correspondence, the moving-annulus and parameter-derivative estimates needed throughout the construction, all generated transport/cutoff/slow-Hessian/higher-profile terms, or the genuine finite-profile recursion.

The Type-II concentration law must still be obtained from the actual PDE dynamics, never imposed as a premise. No new numbered manuscript environment is introduced for these helper statements.

**Retained revised-manuscript accounting remains 11/13 (84.62%).** Full environment 2.13 and the final Type-II construction are not relabeled as accepted by this component-level result.
