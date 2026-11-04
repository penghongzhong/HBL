# HBL 2.13 — canonical interface projection and exact matching criterion: STRICT ACCEPTED

## 1. Evidence independently inspected

- Integrated strict CI: https://github.com/penghongzhong/HBL/actions/runs/41777238554 — completed/success.
- Audited commit: `7722f592bc44e731080606a91e1a895c19243f00`.
- Complete build: **4129 Lake jobs**, successful. This is not a manuscript-environment count.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Artifact ID 13296974174, 20591 bytes: `HBL_CANONICAL_PROJECTION_STRICT_41777238554.zip`.
- Downloaded archive SHA256 recomputed as `35bf1862219ef8b55d01ef458e73b170d41fba6e5bf2cb6352beb6266129177f`, equal to the GitHub artifact digest.
- All THREE mathematical source-strict logs are empty. Each source was run with `--trust=0 -DwarningAsError=true`.
- All FOUR archived Lean files were checked against source-hashes.txt.
- All SEVEN exported theorem types and transitive axiom lists were inspected: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or added axiom.
- The printed definitions of both actual Fredholm equations, the actual physical compatibility map and normalized flux were inspected as well.

The exact integrated-projection component independently passed CI 41776989830 at commit `a30740c39a803555ec38e480a2411bf86917d02c`: 4103 build jobs, one empty strict source log, five standard-only axiom lists. Its downloaded 13922-byte archive digest is `26495713c0803d0d08bde18724acbdf11dc7663620da28f069d54daef0e359f3`.

## 2. Exact retained-defect projection, not merely a small norm

Use the EXISTING origin-gauge pair Phi,Psi and W=Phi*Psi'-Phi'*Psi on [R,2R], with the actual frozen coefficient a_K=2/r+i*r/2 and b=theta+i*(1/4-mu). Define

    L_r(U,DU) = (U*Psi'(r)-DU*Psi(r))/W(r),
    B_K(F,U,DU) = L_R(U,DU) - integral_R^(2R) Psi(r)*F(r)/W(r) dr.

For the already constructed concrete repair w and its COMPLETE frozen residual

    E_tr = w'' + a_K*w' + b*w,

the new Lean theorem derives, from actual derivatives and W'=-a_K W,

    d L_r(w,w')/dr = -Psi(r)*E_tr(r)/W(r).

The source density is proved interval integrable: the repair is smooth, the actual basis is continuous and W is nonzero throughout the positive annulus. The fundamental theorem of calculus therefore proves

    integral_R^(2R) Psi*E_tr/W = B_K(F,U,DU).

For interval-integrable F the complete repaired source also satisfies

    integral_R^(2R) Psi*(F+E_tr)/W = L_R(U,DU).

No undefined integral, source continuity hypothesis, or prescribed source-order is used. The measured defect is not silently declared to have zero projection.

## 3. Shorter exact transmission after cancellation of this projection

Let (G_F,V_F) be the ORIGINAL normalized Green pair. For the actual left mismatch p=U-G_F(R), q=DU-V_F(R), set

    gamma = [Phi(R)*q-Phi'(R)*p]/W(R),
    U_hat = G_F + gamma*Psi,
    V_hat = V_F + gamma*Psi'.

The added mode is a genuine homogeneous solution of the SAME frozen Kummer operator. The new theorem proves exact identities

    U_hat(R)-U   = -B_K(F,U,DU)*Phi(R),
    V_hat(R)-DU  = -B_K(F,U,DU)*Phi'(R).

Since the actual Wronskian is nonzero, it follows in BOTH directions that

    [U_hat(R)=U and V_hat(R)=DU]  iff  B_K(F,U,DU)=0.

Independently of whether B_K vanishes, the pair preserves the original RIGHT finite-annulus Wronskian condition, is continuous on the closed annulus, and satisfies the true system almost everywhere with EXACTLY F:

    U_hat'=V_hat,
    V_hat' + a_K*V_hat + b*U_hat = F.

Thus cancelling the computed complex projection would remove the need for a cutoff-generated forcing in this frozen Kummer transmission. This is a conditional exact matching criterion; it does NOT claim that the physical parameter path already makes B_K zero. The right normalized condition is NOT an independently proved radiation condition at infinity, and the right jet need not equal the original Green pair's two coordinates after the homogeneous addition.

## 4. Same physical Hartree solution, not an abstract incoming datum

The integrated theorem reuses the already accepted canonical construction. For fixed B,A,mu,theta,scale,R,C,K, it chooses D before ell,c,a,z, and then constructs hp,hm and the SAME normalized inner correction x. Both actual corrected-source Fredholm equations are explicit in `ActualHartreeTransmissionInnerSolve`, which is printed by the audit.

The data are

    J=(up(aR)+i*um(aR), a*(up'(aR)+i*um'(aR))),
    F_K(r)=a²*F_{ell,c,z}(a*r).

The physical radial factor in the inner forcing, the forced affine charges, the slope factor a and the source factor a² are all retained. The assumptions remain the inherited measurable amplitude/Strauss bounds, 0<ell<=1, |c|<=1, a>0, R>=1 and aR>2, together with the actual prescribed-annulus basis certificate.

For this SAME x, the exported statement simultaneously proves:

1. The previous sup-norm estimate |E_tr|<=D*ell^(1/16).
2. Genuine integrability and exact projection of E_tr.
3. The iff criterion for exact left matching by (U_hat,V_hat).
4. The unchanged-source a.e. frozen equation and the original right normalization.

No free source, independently selected small jet, assumed moment bound, vanishing projection, inverse Jacobian, or Type-II time law is supplied as a new physical hypothesis.

## 5. Audited declarations and proof reuse

New sources:
- `HBL/TypeIIDynamicSelection/ActualKummerTransmissionProjection.lean`
- `HBL/TypeIIDynamicSelection/ActualOriginProjectionCancellation.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeCanonicalProjection.lean`

Integrated audited statements:
- `actual_origin_outgoing_flux_hasDerivAt`
- `actual_Kummer_interface_defect_projection_exact`
- `actual_origin_transmission_defect_projection_balance`
- `actual_origin_projected_left_defect_exact`
- `actual_origin_projected_matching_iff_zero_obstruction`
- `actual_origin_projected_transmission_same_equation`
- `actual_Hartree_canonical_projection_and_exact_matching`

The earlier source, inverse, normalized Green, first-moment and cutoff proofs are reused as actual dependencies rather than re-created as assumptions. The independent projection audit additionally checks repair forcing continuity and the exact Green trace coefficient.

## 6. Exact next obligation and manuscript counting

For THIS interface, the next nonlinear compatibility target is explicitly

    Re B_K(F_K,J)=0,   Im B_K(F_K,J)=0,

or a rigorously stronger relative-order bound at the target recursion weight. Existing abstract implicit-function lemmas can only be applied after differentiability and a nondegenerate derivative have been established for the ACTUAL full matching map. The normalized scale/phase orthogonality Jacobian is not automatically the Jacobian of this distinct mu/theta/interface map.

Cancelling this base-core/radiation interface projection alone is not full 2.13: independent remote compatibility, complete time-dependent Hartree coordinate correspondence, parameter derivatives of the new homogeneous coefficient, all generated higher-profile and nonlocal residual terms, their weighted relative-order gains and the physical packet for finite recursion remain obligations. No uniform moving-annulus bound beyond the stated fixed-basis constants is claimed. The final Type-II rate must still be derived from the PDE.

**Retained manuscript count remains 11/13 (84.62%).** This continuation closes the exact retained-error projection and its source-preserving matching criterion, not the two remaining complete manuscript environments.
