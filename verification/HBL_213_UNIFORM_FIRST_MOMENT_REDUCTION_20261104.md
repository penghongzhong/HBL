# HBL 2.13 — canonical first moments and the remaining uniform-norm specialization

This is an analytical reduction, NOT a claim that the uniform scale estimate below has already passed Lean. The retained manuscript count remains 11/13. The same original nonlocal interaction and the correct radial conjugation are used throughout.

## Same actual source and normalized reconstruction

Let sigma=7/4, a(r)=(1+r^2)^(-1), R=ell^(-1/16), and

    G(r)=r*(1-cutoff(r/R))*F_{ell,c}(r),
    Gplus=Re G, Gminus=Im G.

Let alpha_plus/minus be the uniquely forced actualPlusCharge/actualMinusCharge. Put

    Fcorr_plus = Gplus-alpha_plus*channelAffineSource(plus),
    Fcorr_minus = Gminus-alpha_minus*channelAffineSource(minus).

For the existing normalized Hilbert solutions x_plus/minus, the actual total reconstructed sources are

    Hplus  = a * weightedPotentialOperator(x_plus) + Fcorr_plus,
    Hminus = a * (3*x_minus) + Fcorr_minus.

It would be incorrect to omit the a*g terms. The canonical half-line representatives are

    q_plus/minus = Green(Hplus/minus) + alpha_plus/minus*model,
    Green(H)(r) = integral min(r,rho)*H(rho) d rho.

The new source files establish exact total-source identities, first-moment integrability, and trace estimates in terms of the existing `innerGreenBound`. Their own dedicated CI must be inspected before any formal acceptance claim.

## Exact trace mechanism

For H and rho*H integrable,

    Green(H)(r)-r*Green(H)'(r) = integral_(0,r] rho*H(rho) d rho.

Consequently, with M=integral rho*|H(rho)| d rho and r>2,

    |(Green(H)+alpha*model)(r)/r-alpha| <= M/r,
    |d/dr [(Green(H)+alpha*model)(r)/r]| <= M/r^2.

The charge alpha is retained. It cancels in the derivative only because the actual fixed affine model equals r beyond its cutoff.

## Reduction of the missing uniform smallness to fixed operator norms

All norms in this section are real L2(dr) norms on (0,infinity). Write

    Jsigma F = <r>^sigma F,
    Nsigma = ||r*<r>^(-sigma)||_2,
    Na = ||r*a||_2,
    Ssigma = weightedSourceGreenOperator(sigma),
    Vplus = weightedPotentialOperator,
    Vminus = 3*Id.

Nsigma and Na are finite: these are the actual scalar factors already covered by `weightedSource_momentWeight_memLp` and `weightedGreenOutputMajorant_memLp_two`.

By Cauchy--Schwarz, the explicit existing Green bound obeys

    innerGreenBound(g,Fcorr) <= Na*||g||_2 + Nsigma*||Jsigma Fcorr||_2.

The two concrete Fredholm operators Bplus and Bminus are fixed; they do NOT depend on ell or the moving-monopole parameter c. Their compactness and `HBL.Fredholm.one_sub_antilipschitz_on_kernelComplement` give fixed Cplus,Cminus such that, on the actual kernel complements,

    ||x_plus/minus||_2 <= Cplus/minus * ||(Id-Bplus/minus)x_plus/minus||_2.

The normalized equations give

    ||x_plus/minus||_2 <= Cplus/minus*||Ssigma||*||Jsigma Fcorr_plus/minus||_2.

Hence, with the fixed constants

    Dplus/minus = Na*||Vplus/minus||*Cplus/minus*||Ssigma||+Nsigma,

one obtains

    Mbound_plus/minus <= Dplus/minus*||Jsigma Fcorr_plus/minus||_2.

To specialize this in Lean, use the actual normalized equations, not merely a free L2 vector with an assumed norm. Preserve the same representative identities as the accepted canonical C1 theorem.

## All physical source constants are already specified

Let K=actualHartreePhysicalWeightedSourceConstant(B,A),
T=actualHartreePhysicalChargeTailConstant, and
Aplus/minus=||Jsigma(channelAffineSource(plus/minus))||_2.
The known pointwise inner bound and integral_(0,infinity)(1+r)^(-5/4)dr=4 yield

    ||Jsigma Gplus||_2, ||Jsigma Gminus||_2 <= 4*K*ell^(1/16).

The already accepted forced-charge estimate gives

    |alpha_plus| <= 4*K*T*ell^(1/16),
    |alpha_minus| <= 2*K*T*ell^(1/16).

The triangle inequality then yields the analytical targets

    Mbound_plus <= Dplus*(4*K+4*K*T*Aplus)*ell^(1/16),
    Mbound_minus <= Dminus*(4*K+2*K*T*Aminus)*ell^(1/16).

There is no unknown small trace constant on the right. All constants are fixed operator norms or explicit radiation-amplitude/Strauss constants. The full Lean specialization of these inequalities is still a distinct remaining obligation.

For 0<ell<1 and r=2R, the ensuing targets are

    |u_plus/minus(2R)-alpha_plus/minus| = O(ell^(1/8)),
    |u_plus/minus'(2R)| = O(ell^(3/16)).

Do NOT replace the first statement by |u(2R)|=O(ell^(1/8)); the forced affine charge is only O(ell^(1/16)).

## Manuscript boundary

Even after the uniform-moment specialization, this controls the inner correction driven by the complete core-radiation interaction, not every term of the common PDE residual or every later nonlinear profile. Canonical Kummer and remote traces, simultaneous two-interface compatibility, transport/parameter/commutator estimates, actual finite-profile recursion and the dynamically derived Type-II blowup law remain to be proved. No new numbered manuscript environment is counted here.
