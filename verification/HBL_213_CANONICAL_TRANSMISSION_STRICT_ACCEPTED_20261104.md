# HBL 2.13 — canonical inner to original Green transmission: STRICT ACCEPTED

## 1. Immutable evidence actually inspected

- Integrated strict CI: https://github.com/penghongzhong/HBL/actions/runs/41769652757 — completed/success.
- Audited commit: `a6dead3a41f932c85e1aef5a879bda5343c9abdd`.
- Complete build: **4126 Lake jobs**, successful. This is NOT a manuscript-environment count.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Artifact 13293423693, 22742 bytes, downloaded as `HBL_CANONICAL_TRANSMISSION_STRICT_41769652757.zip`.
- Independently recomputed SHA256: `d069f9a12eca225587d5d54a033932521961e4a870a3bc29019ce87b04562f44`, identical to GitHub's digest.
- All THREE mathematical source-strict logs are empty; all were run using `--trust=0 -DwarningAsError=true`.
- All FOUR archived Lean source hashes were recomputed and matched.
- The full exported theorem types, the explicit definitions of the canonical two-channel equations and reconstructed fields, and all FOUR integrated transitive axiom lists were inspected. Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or new axiom.

The generic transmission component independently passed CI 41768405435 at commit `794832310a672d71415ebb6d093d79a6031c050a`: 4102 build jobs, two empty strict source logs, seven standard-only axiom lists. Its 17400-byte artifact SHA256 is `75d93f73d24ef4d6d127d42cfdc947111da08a42501d615620faa5a9f8ec5821`.

Mathematical sources:
- `HBL/TypeIIDynamicSelection/ActualKummerInterfaceRepair.lean`
- `HBL/TypeIIDynamicSelection/ActualOriginGreenTransmission.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeCanonicalTransmission.lean`

The integrated audit module prints the actual equation and jet definitions, not only opaque predicates.

## 2. The optimized construction: exact traces, retained defect

Do not require two independently normalized regional inverses to agree without proof. Instead use the original origin-normalized Green pair `(G_F,V_F)` on `[R,2R]` and the ACTUAL incoming value/slope `(U,DU)`.

Let

    p = U-G_F(R),  q = DU-V_F(R),
    eta_R(r) = 1-cutoff((r-R)/(R/3)),
    w(r) = eta_R(r)*(p+(r-R)*q).

The same previously verified smooth cutoff is identically one near R and zero near 2R. Its first and second derivatives, and the first and second derivatives of w, are genuinely proved. No piecewise jump or unproved derivative formula is inserted.

The repaired pair is

    U_tilde=G_F+w,  V_tilde=V_F+w'.

The accepted generic theorem proves

    (U_tilde(R),V_tilde(R))=(U,DU),
    (U_tilde(2R),V_tilde(2R))=(G_F(2R),V_F(2R)).

Thus the original finite-annulus right Wronskian normalization is preserved exactly. The original LEFT normalization need not survive: it has deliberately been replaced by the actual incoming pair. No independent remote trace or radiation condition at infinity is silently asserted.

For merely interval-integrable F, both members of the repaired pair are continuous on the closed annulus and satisfy the actual system almost everywhere:

    U_tilde'=V_tilde,
    V_tilde' + a_K V_tilde + b U_tilde = F + E_tr,
    a_K(r)=2/r+i*r/2, b=theta+i*(1/4-mu),
    E_tr=w''+a_K*w'+b*w.

The complete defect E_tr is retained, including the imaginary drift and zero-order coefficient. These statements do not claim everywhere classical C2 regularity for merely measurable forcing.

If D_jet=|p|+R|q| and R>=1, the derived fixed-cutoff constants C1,C2 give

    |w| <= D_jet,
    |w'| <= (3*C1+1)*D_jet/R,
    |w''| <= (9*C2+6*C1)*D_jet/R²,
    |E_tr| <= (9*C2+15*C1+3+|b|)*D_jet.

This is control by the measured mismatch, NOT an unproved relative-order gain.

## 3. Actual Hartree data produce the small defect; smallness is not a premise

The integrated theorem constructs the SAME normalized inner correction x from the actual two-channel Fredholm equations for

    G(r)=r*(1-cutoff(r/ell^(-1/16)))*F_{ell,c,z}(r).

The two corrected sources and uniquely forced affine charges are preserved. The proposition `ActualHartreeTransmissionInnerSolve` is printed in the audit and is exactly those two equations, not an external solver assumption.

The actual canonical inner fields up,um are the previously established affine-restored Green representatives divided by r. Under the explicit coordinate conversion rho=a*r, the incoming pair is

    U=up(aR)+i*um(aR),
    DU=a*(up'(aR)+i*um'(aR)).

The slope factor a is retained, and the same source is

    F_K(r)=a²*F_{ell,c,z}(a*r).

The inherited assumptions are B,A>=0, 0<ell<=1, |c|<=1, measurable z, |z(u)|<=B for u>0, u|z(u)|<=A for u>=1, a>0, R>=1 and aR>2. No assumed bound on the incoming jet, mismatch, repair source or concentration-time rate is added.

Reusing uniform first moments and the original forced charges gives

    |U|+R|DU| <= S(B,A)*ell^(1/16),
    S=6*Q(B,A)*|T_charge|+Cplus+Cminus.

For the original Green basis bound C on `[R,2R]`, the previously accepted source theorem gives

    |G_F(R)|+R|V_F(R)| <= 2*C³*Q(B,A)*ell^(1/8).

Consequently the new integrated theorem proves

    sup_[R,2R] |E_tr| <= D*ell^(1/16),
    D=(9*C2+15*C1+3+|b|)*(S+2*C³*Q).

The constant is chosen BEFORE ell,c,a,z. It may depend on the fixed-annulus basis bound C and parameters. No uniform control of C over moving or unbounded annuli is claimed.

Public integrated declarations:
- `actual_origin_Green_repaired_transmission`
- `actual_origin_Green_transmission_defect_bound`
- `actual_Hartree_canonical_scaled_inner_jet_bound`
- `actual_Hartree_canonical_origin_transmission_small_defect`

## 4. Exact next main-chain burden, not another independent inverse

This construction replaces an unsupported exact-matching assertion by a controlled approximate transmission. It does NOT eliminate the compatibility obstruction without paying a source error.

For the actual right normalized mode Psi and Wronskian W, the analytic identity for a smooth repair w is

    d[(w*Psi'-w'*Psi)/W]/dr = -Psi*E_tr/W,

using W'=-a_K W and the homogeneous Psi equation. The algebraic identity was independently checked with SymPy in this continuation. Its INTEGRATED Lean version and its physical modulation cancellation are not yet claimed.

The next explicit finite-annulus projection to formalize and place in the coupled modulation map is

    B_K(F,U,DU) = [U*Psi'(R)-DU*Psi(R)]/W(R)
                 - integral_R^(2R) Psi*F/W.

Formally integrating the preceding identity predicts

    integral_R^(2R) Psi*E_tr/W = B_K(F,U,DU).

This is one complex, hence two real, finite-annulus compatibility quantities; it is not by itself all remote boundary data or an outgoing-at-infinity theorem. Small sup-norm E_tr alone is insufficient to claim a higher residual order. The retained projection must be canceled or controlled at the required improved order through the actual parameter equations.

The full time-dependent and nonlocal Hartree residual created by this repair, its physical weighted norms and parameter estimates, the independently selected remote solution, all generated higher-profile terms and finite recursion remain obligations. The final Type-II rate must still be derived from PDE dynamics.

**Retained manuscript count: 11/13 (84.62%).** No extra numbered manuscript environments have been introduced; no auxiliary CI is relabeled as full 2.13 or the Type-II main theorem.
