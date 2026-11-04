# HBL 2.13 — full nonhomogeneous source and actual charge reference: STRICT ACCEPTED

## Immutable evidence inspected in this continuation

The previously accepted same-source DIFFERENCE estimate did not control the charge-reference transfer itself. The present accepted result supplies that missing bound, including the original nonlocal forcing contribution.

Generic full-source CI:
- https://github.com/penghongzhong/HBL/actions/runs/41760078740 — completed/success.
- Source commit `8df08811e55734b76ed6514cf3335a96cd7e6749`.
- Complete build: 3537 Lake jobs, success.
- Artifact 13290266623, 10193 bytes, downloaded as `HBL_FULL_INHOMOGENEOUS_KUMMER_STRICT_41760078740.zip`.
- Independently recomputed SHA256 `2b1fc3a1f0fa1f061e531db569c3a01f07063ad86992cf1afbee53c8684f64b4`, equal to the GitHub digest.

Integrated original Hartree-source CI:
- https://github.com/penghongzhong/HBL/actions/runs/41760170244 — completed/success.
- Audited commit `b7cd91c85a1c248ca426c232933cd2064f94e625`.
- Complete integrated build: **4083 Lake jobs**, success.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Artifact 13289719031, **20240 bytes**, downloaded as `HBL_FULL_SOURCE_CHARGE_REFERENCE_STRICT_41760170244.zip`.
- Independently recomputed SHA256 `75f4826801bbfa569423586f094f998aa45ab792f056b629dd345105e77507e3`, equal to the GitHub digest.
- All three new mathematical sources passed `--trust=0 -DwarningAsError=true`; all THREE source-strict logs are empty.
- All FOUR archived Lean files were checked against the archive's source-hashes.txt.
- Complete readable exported declarations and SIX integrated transitive axiom lists were inspected. Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Commit, compiler pin, Mathlib pin, successful build result and artifact digest were checked directly in the downloaded evidence.

No proof-count credit is taken for the separate source-export workflow 41757905593. That workflow only exported a current source snapshot for dependency inspection.

## 1. Actual Wronskian impulse and exact Duhamel formula

For the existing genuine LocalKummerPair K, write r0=z-d, r1=z+d. The original Wronskian is W(s)=phi(s)*dpsi(s)-dphi(s)*psi(s). The actual unit-slope impulse at physical source radius z+s is

    E_value(s,t)=(-psi(s)*phi(t)+phi(s)*psi(t))/W(s),
    E_slope(s,t)=(-psi(s)*dphi(t)+phi(s)*dpsi(t))/W(s).

It has exactly value 0 and slope 1 at t=s. Reusing the ALREADY ACCEPTED homogeneous shear estimate gives, whenever 0<r0<r1<=2*r0 and s lies in [-d,d],

    max(|E_value(s,d)|,r1*|E_slope(s,d)|) <= C_b*(z+s),
    C_b=(1+2|b|)^2*exp((1+2|b|)^2),
    b=frozenZeroCoeff(mu,theta).

The bound is independent of annulus radius and basis normalization. Dependence on b is explicit; no uniformity over an unbounded parameter range is claimed.

For any shifted interval-integrable forcing F, the EXISTING physical Green transfer with zero left Cauchy data is proved equal to

    T_K[F](0,0) = integral_(-d)^d (E_value(s,d),E_slope(s,d))*F(z+s) ds.

This is derived from the original two Green integrals and Wronskian coefficient uniqueness, not used as an alternative unconnected definition. No continuity premise on F is needed for these integral identities.

## 2. Full nonhomogeneous transfer, not merely a difference

Write J_r(U,DU)=max(|U|,r*|DU|). If |F|<=M on the positive annulus and F is interval integrable, the checked conclusion is

    J_r1(T_K[F](U,DU))
      <= C_b*(J_r0(U,DU)+2*r0^2*M).

The complete particular-source term is present. This estimate is not the previous result for T_K[F](U,DU)-T_K[F](A,DA).

The formal result controls the exact Green value/slope transfer pair. It does not make an unsupported classical C2 assertion for merely measurable forcing.

## 3. True Hartree source and explicit spatial coordinate conversion

Let F_{ell,c} be the SAME complete physical base-core/radiation Hartree interaction used by the accepted weighted-L2 theorem, and let a>0 be an explicit spatial scale. Define

    F_K(r)=a^2*F_{ell,c}(a*r).

The a^2 factor is the Laplacian source scaling; physical and Kummer radii are not silently identified. This definition and its estimates alone do NOT claim the complete time-dependent renormalized PDE correspondence.

The already accepted full-source estimate

    |F_{ell,c}(rho)| <= K(B,A)*ell^(1/8)*(1+rho)^(-19/8)

implies, by rho^2<=(1+rho)^(19/8),

    r^2*|F_K(r)| <= K(B,A)*ell^(1/8),
    |F_K(r)| <= K(B,A)*ell^(1/8)/r0^2 for r>=r0>0.

The formal proof keeps the exact identity r^2*a^2=(a*r)^2. The bound is independent of a. The physical source measurability is derived from the SAME measurable moving monopole and rescaled radiation, and interval integrability is then derived from this bound. Neither source continuity nor interval-integrability is an extra hypothesis of the physical specialization.

Consequently,

    J_r1(T_K[F_K](U,DU))
      <= C_b*(J_r0(U,DU)+2*K(B,A)*ell^(1/8)).

The only physical data assumptions are the accepted ones: B,A>=0, 0<ell<=1, |c|<=1, a>0, measurable z, |z(u)|<=B for u>0 and u*|z(u)|<=A for u>=1. The genuine LocalKummerPair and explicit dyadic annulus conditions remain in the statement.

## 4. The actual forced-charge reference is now estimated

Let G=r*(1-cutoff(r/R))*F_{ell,c}, R=ell^(-1/16), and

    alpha=actualPlusCharge(Re G)+i*actualMinusCharge(Im G).

Both charges are computed from the same physical conjugated source. The existing charge estimates imply

    |alpha| <= 6*K(B,A)*|T_charge|*ell^(1/16).

Combining this with the full-source transfer and ell^(1/8)<=ell^(1/16) gives the NEW accepted conclusion

    J_r1(T_K[F_K](alpha,0))
      <= C_b*K(B,A)*(6*|T_charge|+2)*ell^(1/16).

This closes the previously unestimated magnitude of the inhomogeneous charge-reference transfer. No affine charge, nonlocal source component or Duhamel contribution is discarded. The right-hand constant is independent of ell,c,a,r0,r1 and the particular radiation z satisfying B,A.

## Files and audited statements

New mathematical sources:
- `HBL/TypeIIDynamicSelection/ActualKummerImpulseKernel.lean`
- `HBL/TypeIIDynamicSelection/ActualKummerFullSourceTransfer.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeKummerChargeReference.lean`

Public integrated audited conclusions:
- `actual_Kummer_impulse_scaled_uniform`
- `actual_Kummer_zero_data_Duhamel_exact`
- `actual_Kummer_full_source_scaled_transfer_uniform`
- `actual_Hartree_scaled_Kummer_source_annulus_bound`
- `actual_Hartree_full_scaled_source_Kummer_transfer_bound`
- `actual_Hartree_forced_charge_reference_Kummer_uniform`

The generic audit additionally checks `actual_Kummer_zero_data_scaled_source_bound`. Separate audit modules print the complete statements and axiom dependencies.

## Exact remaining boundary

A small charge-reference transfer is NOT yet an identification with the manuscript's original origin/outgoing normalization or with an independently constructed remote solution. Those two-endpoint compatibility equations still need proof, or a fully controlled coupled replacement retaining the same PDE and admissible boundary conditions.

This result treats the complete BASE-core/radiation interaction, not every generated transport, parameter, cutoff, slow-Hessian or higher-profile term. Their uniform gains and genuine finite-profile recursion remain obligations of retained environment 2.13. The Type-II concentration law must still follow from the actual PDE dynamics, never a prescribed rate.

**Retained manuscript accounting remains 11/13 (84.62%).** No auxiliary theorem or source-snapshot job is relabeled as either of the two remaining complete manuscript environments.
