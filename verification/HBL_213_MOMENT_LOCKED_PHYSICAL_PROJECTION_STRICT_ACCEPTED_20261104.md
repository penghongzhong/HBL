# HBL 2.13 — genuine moment-locked physical speed directions and projections: STRICT ACCEPTED

## 1. Evidence inspected in this continuation

- Integrated strict CI: https://github.com/penghongzhong/HBL/actions/runs/41788995294 — completed/success, including the strict physical-source projection and kernel audit step.
- Audited commit: `514c725e85f3445e43bd2a3ca1a027b37c1eb758`.
- Complete targeted build: **4108 Lake jobs**, successful. This is NOT a manuscript-environment count.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Artifact ID 13302835810, **18226 bytes**, downloaded as `HBL_MOMENT_LOCKED_PROJECTION_STRICT_41788995294.zip`.
- Independently recomputed archive SHA256: `dead85c2c66fd147b27e670dd6192dafa7bfe3d021acdc0c6d8bfde6a311fefb`, equal to GitHub's digest.
- Both mathematical source-strict logs are empty; both sources ran with `--trust=0 -DwarningAsError=true`.
- All FOUR archived Lean files were recomputed against source-hashes.txt and matched.
- All FIVE integrated exported theorem types and transitive axiom lists were inspected: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or new axiom.
- The printed definitions of the actual moment-locked scale profile, scaled physical source directions, original integral columns and their real determinant were inspected.
- The underlying source-identification module independently passed CI 41787955356 at commit `751db69f15f93087a23a4487d41ef69740907ac0`.

The initial failures were syntax of unspaced absolute-value bars, an exact negation elaboration, one complex unit-modulus simplification and one strict tactic-sequencing warning. No mathematical assumption or conclusion was weakened to obtain the successes.

## 2. The moment-determined monopole is not a free modulation parameter

The actual core is

    V_c(r)=W(r)+c*(1-chi(|c|r/4))*P(r),

where P is the already constructed radial monopole. Its actual amplitude tangent is

    T_c(r)=P(r)*(1-chi(|c|r/4)-(|c|r/4)*chi'(|c|r/4)).

The previously proved physical 3D moment law is retained:

    c_s=-b*c+m,
    m=kappa_H*ell^3*d_t(actual 3D inverse-square radiation moment).

Thus c_s cannot be selected as an independent second real speed to cancel an arbitrary complex interface obstruction.

The new exact source theorem proves the genuine remaining core directions are

    Q_c=Lambda V_c-c*T_c,
    P_b=i*Q_c,   P_omega=V_c.

In particular the original core residual satisfies EXACTLY

    R_core = Delta_rad V_c + N_Hartree(V_c) + i*m*T_c
             + b*P_b + omega*P_omega.

The complete original nonlocal core nonlinearity and actual moment-derivative forcing are present. The specialization derives the displayed amplitude law from the true 3D radiation moment together with ell_s=-b*ell and time_s=ell^2. Differentiability of that actual radiation moment is an explicit inherited high-regularity input. No asymptotic blowup rate is specified.

The equation here is the core residual; applying it to a complete core-plus-radiation construction still uses the already established radiation-PDE cancellation and retains the full interaction source. This module does not assert a completed nonlinear flow construction.

## 3. A global cancellation shortens the actual source estimates

For every real c and EVERY positive r, including the moving cutoff transition and c=0, Lean proves

    Q_c(r)=Lambda W(r)+c*(1-chi(|c|r/4))*(Lambda P(r)-P(r)).

The cutoff derivative chi' cancels exactly between radial dilation and the moment-determined time derivative. It is not removed by a core-support restriction or an assigned gain.

Reusing the already constructed bounds on P and Lambda P, the theorem constructs a fixed M>0 BEFORE c and r such that

    |Q_c(r)-Lambda W(r)| <= M*|c|,
    |V_c(r)-W(r)|        <= M*|c|.

These are global positive-radius bounds. This removes the need for separate transition-derivative estimates in this particular physical speed coefficient; it does not remove all cutoff errors in the full PDE residual.

## 4. Original compatibility integrals of the true source directions

Keep the SAME origin-normalized Kummer basis and its actual projection

    Pi_K(F)=integral_R^(2R) Psi(r)*F(r)/Wronskian(r) dr.

For the explicit physical coordinate conversion rho=a*r, define

    P_b^(a,c)(r)=a^2*i*Q_c(a*r),
    P_omega^(a,c)(r)=a^2*V_c(a*r),
    A_b(c)=Pi_K(P_b^(a,c)),  A_omega(c)=Pi_K(P_omega^(a,c)).

Both sources are proved measurable and interval integrable on EVERY positive annulus for a>0. Integrability is derived from the actual profiles and their bounds, not assumed; the projection does not exploit an undefined integral.

For any prescribed basis certificate OriginBasisOn(K,R,2R,C), C>=0, R>0, the new theorem gives a fixed M>0 before a,c and proves

    |A_b(c)-A_b(0)|         <= C^2*a^2*R*M*|c|,
    |A_omega(c)-A_omega(0)| <= C^2*a^2*R*M*|c|.

The zero-amplitude columns are exactly the original bubble directions i*Lambda W and W, with the same a^2 scaling and Wronskian integral. They are not auxiliary S_K,i*S_K columns or normalized test functionals whose independence is assigned by definition.

Dependence on a^2, R and C is explicit. This is NOT an estimate uniform over unbounded scaling or moving annuli.

## 5. Exact instantaneous source response; full coupled response still required

For real db,domega, genuinely integrable F and fixed incoming jet J=(U,DU), Lean proves

    B_K(F+db*P_b^(a,c)+domega*P_omega^(a,c),J)
      = B_K(F,J)-db*A_b(c)-domega*A_omega(c).

This identifies the actual forcing part of the real compatibility matrix

    [[Re A_b, Re A_omega], [Im A_b, Im A_omega]],
    Delta_source=Re A_b*Im A_omega-Re A_omega*Im A_b.

The determinant is DEFINED AND EXPLICIT, not proved nonzero by this continuation. No inverse Jacobian or solved modulation speed has been silently asserted.

More importantly, this formula freezes the incoming canonical jet and the Kummer basis. It is NOT the full derivative of the coupled canonical compatibility map. If the normalized inner correction responds to the same physical source increments, its actual trace responses J_b,J_omega must also be constructed. At fixed basis and radius the complete columns would include

    L_R(J_b)-Pi_K(P_b),  L_R(J_omega)-Pi_K(P_omega).

The response of the basis, moving interfaces and remaining parameter-dependent terms must be retained when they vary. These contributions cannot be replaced by the source-only matrix or by the earlier normalized scale/phase orthogonality Jacobian.

## 6. Verified code and next main-chain target

Sources:
- `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedSpeed.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedProjection.lean`

Each has an independent audit module. Integrated audited statements:
- `actual_Hartree_threeD_moment_core_speed_split`
- `actual_Hartree_moment_locked_speed_profiles_uniform_close`
- `actual_Hartree_moment_locked_scaled_speed_integrable`
- `actual_Hartree_moment_locked_projection_columns_close`
- `actual_Hartree_moment_locked_compatibility_speed_response`

The source-only audit additionally prints and audits the exact global cutoff cancellation, the general moment-locked core residual identity, and the true bubble reference identities.

Next decisive burden: use the existing fixed normalized Fredholm inverse to construct the TWO ACTUAL inner source responses and their traces, assemble the complete coupled real matrix, and prove the required nondegeneracy or an alternative legitimate cancellation mechanism. The present global O(c) source estimates are available inputs, not a substitute for that construction.

The full time-dependent residual, independent remote realization, parameter estimates, relative-order gain and genuine finite-profile recursion remain obligations of original 2.13. The final Type-II concentration law must still be derived from the PDE.

**Retained manuscript accounting remains 11/13 (84.62%).** No auxiliary source theorem is relabeled as either remaining complete manuscript environment.
