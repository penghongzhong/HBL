# HBL 2.13 — shorter scale-uniform Kummer transfer proof

**Status: complete analytical reduction, with exact algebra checked in SymPy; NOT Lean-accepted by this note.** The preceding strict same-source transfer theorem is CI 41749430663. Do not increment the 11/13 manuscript count from this note.

## 1. Use the already proved homogeneous difference

The existing physical frozen Kummer equation is

    u'' +(2/r+i*r/2)*u' + b*u = F(r),
    b=frozenZeroCoeff(mu,theta),  r>0.

For two transfers driven by the SAME F, the new strict theorem identifies their difference with an exact linear combination of the actual homogeneous fundamental pair. Thus its difference h satisfies

    h'' +(2/r+i*r/2)*h' + b*h = 0.

This homogeneous difference is classical from the LocalKummerPair derivative fields, even when the source assumptions alone do not justify a classical C2 inhomogeneous particular solution. No continuity of an independently postulated F is needed for the difference estimate.

## 2. Remove the large imaginary drift exactly

Define the constant a=2*i*b and

    w(r)=r*h'(r)-a*h(r),
    P(r)=exp(i*r²/4),
    v(r)=P(r)*w(r).

The exact derivative identities are

    h'=(a*h+w)/r,
    w'=-(1+a)*w/r-a*(1+a)*h/r-i*r*w/2,

and hence, since P'=i*r*P/2,

    h'=(a*h+P^(-1)*v)/r,
    v'=(-(1+a)*v-a*(1+a)*P*h)/r.

Crucially, |P|=|P^(-1)|=1. The O(r) coefficient has disappeared; it must NOT be estimated in absolute value before applying this gauge. These algebraic identities are checked in `verification/hbl_213_kummer_shear_sympy_audit.py`.

## 3. A uniform bound on a dyadic positive annulus

Equip X=(h,v) with the product maximum norm and put

    A=|a|=2|b|,
    K=(1+A)²,
    N(r)=max(|h(r)|,|v(r)|).

The first row of the transformed system is bounded by (1+A)N/r. The second is bounded by ((1+A)+A(1+A))N/r=K*N/r. Since 1+A<=K, the actual derivative satisfies

    ||X'(r)|| <= (K/r)*||X(r)||.

On [r0,r1] with 0<r0<=r1<=2*r0 this gives the constant-coefficient inequality

    ||X'(r)|| <= (K/r0)*||X(r)||.

The usual norm Gronwall theorem therefore yields

    N(r1) <= exp(K*(r1-r0)/r0)*N(r0) <= exp(K)*N(r0).

This step can use the existing Mathlib theorem
`norm_le_gronwallBound_of_norm_deriv_right_le`
and `gronwallBound_ε0`; the exact signatures must be checked against the pinned Mathlib before claiming formal success.

Let H(r)=max(|h(r)|,r*|h'(r)|). Since

    |w|<=r*|h'|+A*|h|,
    r*h'=a*h+P^(-1)*v,

one has N<= (1+A)*H and H<= (1+A)*N. Consequently the fully derived uniform analytical estimate is

    H(r1) <= C_b*H(r0),
    C_b=(1+2|b|)²*exp((1+2|b|)²).

There is no r0 dependence. For a fixed bounded annulus ratio Lambda>=1, replace exp(K) by exp(K*(Lambda-1)). Uniform boundedness of b over the selected parameter range suffices; it must be a proved property of that range, not tacitly assumed.

## 4. Exact connection to the accepted physical Hartree trace gain

The strict canonical source/moment theorem supplies at r0=2*ell^(-1/16), 0<ell<1,

    |U-alpha| <= (Cp+Cm)/2 * ell^(1/8),
    r0*|DU|  <= (Cp+Cm)/2 * ell^(1/8).

The reference is the SAME-source Kummer transfer launched from (alpha,0), where alpha=alpha_plus+i*alpha_minus is the ACTUAL forced affine charge. It is not the zero solution.

For r1 in [r0,2*r0], the shear argument then gives

    |Delta value(r1)| <= C_b*(Cp+Cm)/2 * ell^(1/8),
    |Delta slope(r1)| <= C_b*(Cp+Cm)/4 * ell^(3/16).

These conclusions avoid bounding the potentially wasteful product of raw normalized basis norms appearing in the already checked explicit amplification A_K(d). They estimate the actual transfer in its natural scaled Cauchy norm instead.

## 5. Formal obligations that remain

The next Lean target should formalize this ONE transformed homogeneous system and instantiate Mathlib's norm Gronwall theorem, then compose it with the already accepted same-source cancellation and canonical Hartree trace theorem. Do not rebuild the nonlocal source estimates or the normalized Fredholm inverse.

Even a strict proof of the above uniform transfer will NOT by itself identify the charge-reference transfer with the original origin/outgoing Green normalization or with the independently constructed remote solution. Those two outer compatibility equations, the complete common-PDE transport/parameter/cutoff residuals, finite nonlinear profile recursion and the dynamically derived Type-II rate remain separate obligations.

**Retained manuscript acceptance: 11/13. This note is not a Lean acceptance certificate.**
