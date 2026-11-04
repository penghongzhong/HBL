# HBL 2.13 — actual finite-rank compatibility lift and canonical transmission: STRICT ACCEPTED

## 1. Immutable evidence inspected

- Strict integrated CI: https://github.com/penghongzhong/HBL/actions/runs/41780127688 — completed/success, including the strict source and physical audit step.
- Audited source commit: `3cce365d8ca05965f16a91c5cf36cdebc57e842f`.
- Complete build: **4131 Lake jobs**, successful. This is NOT a manuscript-environment count.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Artifact 13299225631, **18249 bytes**, downloaded as `HBL_FINITE_RANK_TRANSMISSION_STRICT_41780127688.zip`.
- Recomputed SHA256: `e4f46f60419d4a83fe7217077eb5df48957e4ea053138aafa04eaad025b807dc`, matching GitHub's digest.
- Both mathematical source-strict logs are empty. Both sources were run with `--trust=0 -DwarningAsError=true`.
- All THREE archived Lean file hashes were recomputed and matched source-hashes.txt.
- All SEVEN exported types and transitive axiom lists were inspected. Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or added axiom.
- The complete physical statement and printed actual source / original Fredholm equation definitions were inspected. The equation explicitly contains `F + beta*S`, not F alone.
- Initial attempt 41779799478 failed on reduction of the unique-existence predicate. The successful correction adds `dsimp only` before an exact rewrite; no mathematical assumption or conclusion changed.

## 2. Constructed, source-independent unit-projection direction

For the existing origin-normalized pair Phi,Psi on [R,2R], write

    W = Phi*Psi' - Phi'*Psi,
    Pi_K(F) = integral_R^(2R) Psi*F/W,
    L_R(U,DU) = (U*Psi'(R)-DU*Psi(R))/W(R),
    B_K(F,U,DU) = L_R(U,DU)-Pi_K(F).

Use the ALREADY VERIFIED smooth affine endpoint lift with incoming data Phi(R),Phi'(R). Call that lift w_K, and retain its complete frozen residual

    S_K = w_K'' + (2/r+i*r/2)*w_K' + b*w_K.

This is an actual source function built from the true origin basis and cutoff. It is not an arbitrary abstract vector with an assumed nonzero projection. The earlier integrated Lagrange identity yields

    Pi_K(S_K) = L_R(Phi(R),Phi'(R)) = W(R)/W(R) = 1.

Both S_K and its weighted projection density are proved interval integrable. The actual nonzero Wronskian supplies the normalization. A finite annular bound M for S_K is derived from the already accepted cutoff C2 estimates, before quantifying over any forcing or incoming jet.

Consequently, for every genuinely interval-integrable F and every complex beta,

    B_K(F+beta*S_K,U,DU) = B_K(F,U,DU)-beta.

The unique cancelling amplitude is therefore

    beta = B_K(F,U,DU).

The identity is about an ADDED SOURCE AMPLITUDE. It is not the derivative with respect to the physical mu/theta parameters and is not a proof of a physical modulation Jacobian.

## 3. Exact augmented annular inverse, not an unchanged-source claim

Set

    F_aug = F + B_K(F,U,DU)*S_K.

The existing projected origin Green inverse is then applied to F_aug. WITHOUT assuming B_K(F,U,DU)=0, the new theorem proves

    U_hat(R)=U, V_hat(R)=DU,
    U_hat(2R)*Psi'(2R)-V_hat(2R)*Psi(2R)=0,
    U_hat'=V_hat,
    V_hat' + (2/r+i*r/2)*V_hat + b*U_hat = F + beta*S_K  a.e.

Both components are continuous on the closed annulus. F_aug is genuinely integrable, not an undefined integral with default zero.

Thus the added forcing has been confined to ONE fixed complex direction, equivalently the two real directions S_K and i*S_K. It is not silently deleted. The two real directions are independent because their complex combination has projection equal to the corresponding complex coefficient.

The original right FINITE-ANNULUS Wronskian condition is retained; no radiation condition at infinity or independently selected remote jet is asserted.

## 4. Composition with the SAME actual Hartree source and canonical inner solve

The physical theorem reuses the previously accepted canonical projection result. It constructs hp,hm and the SAME normalized inner correction x, retaining both actual corrected-source Fredholm equations.

The incoming pair and source remain

    J=(up(aR)+i*um(aR), a*(up'(aR)+i*um'(aR))),
    F_K(r)=a^2*F_{ell,c,z}(a*r).

The radial conjugation, forced affine charges, slope factor a and source factor a^2 are unchanged. The compatibility coefficient is exactly

    beta = actualHartreeCanonicalCompatibility(K,R,a,ell,c,z,x),

not a newly chosen small number. From the already accepted actual defect E and its exact projection, one obtains

    |beta| <= Db*ell^(1/16),
    sup_[R,2R] |F_aug-F_K| <= Ds*ell^(1/16).

Db,Ds are chosen BEFORE ell,c,a,z. For the prior bound |E|<=D0*ell^(1/16), one may take

    Db=C^2*D0*R,
    Ds=Db*M,

where M is the fixed bound for the concrete S_K. Constants may depend on the prescribed origin basis, annulus, parameters and fixed radiation bounds B,A. No uniformity over moving/unbounded annuli is asserted.

All physical hypotheses remain the inherited amplitude/Strauss/measurability assumptions, 0<ell<=1, |c|<=1, a>0, R>=1, aR>2 and the existing actual basis certificate. No vanishing compatibility, estimated incoming trace, prescribed Type-II time law or artificial inverse Jacobian is added.

## 5. Audited files and statements

- `HBL/TypeIIDynamicSelection/ActualOriginFiniteRankTransmission.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeFiniteRankTransmission.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeFiniteRankTransmissionAudit.lean`

Public declarations:

1. `actual_origin_compatibility_source_unit_projection`
2. `actual_origin_source_coefficient_add_mul`
3. `actual_origin_compatibility_amplitude_exact`
4. `actual_origin_compatibility_unique_cancellation`
5. `actual_origin_finite_rank_exact_transmission`
6. `actual_origin_compatibility_source_bounded`
7. `actual_Hartree_canonical_finite_rank_transmission`

## 6. Optimized next burden, and what is NOT proved

The frozen annular transmission can now be solved with a COMPUTED real rank-two residual, rather than repeatedly repairing an unconstrained function-valued mismatch. To use this in the original nonlinear profile equation, the finite-rank residual must still be linked to the ACTUAL admissible time-modulation directions. It cannot be declared to equal those directions by definition.

For actual physical tangent sources P1,P2, a possible next route is to compute the real 2x2 matrix with columns Re/Im Pi_K(Pj) and derive its required nondegeneracy from the original PDE. These Pj must be genuinely admissible parameter velocities, not substituted copies of S_K and i*S_K. If a source shape differs by a zero-projection component, the already proved unchanged-source matching criterion can be used to solve that component; literal equality of Pj with S_K is stronger than necessary. This is a NEXT-STEP reduction, not a certified physical determinant or modulation law.

Existing `ActualOneLayerParameterTangents.lean` identifies actual phase and moving-monopole time derivatives; whether these or the chosen mu/theta variables provide the required independent admissible velocities must be checked against the complete time-dependent construction. In particular, a moment-determined monopole amplitude must not silently become a free parameter.

The full nonlocal nonlinear residual, parameter derivatives, independent remote realization, weighted relative-order improvement, moving-annulus uniformity and finite-profile recursion remain open. An absolute O(ell^(1/16)) source bound is NOT the relative-order induction required by manuscript 2.13. The final Type-II rate remains to be derived from actual PDE dynamics.

**Retained manuscript accounting: 11/13 (84.62%).** No new numbered manuscript environments are introduced and no auxiliary result is relabeled as full 2.13 or the final Type-II theorem.
