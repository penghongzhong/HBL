# HBL 2.13: source-space obstruction at the ACTUAL interfaces, and a finite C3 repair

11 November 2026. Original revised environments remain **11/13**. The analytic statements in Sections 1--4 below are paper proofs, NOT new Lean certificates. The companion Lean module checks only the explicitly constructed polynomial endpoint jets and their factored formulas. No positive time exponent, Hartree orbit, source envelope, or blowup law is assumed or concluded.

## 1. Exact link to the retained physical four-piece field

The literal current field is `actualHartreeInnerKummerSpectralFourPiece` in `HBL/TypeIIDynamicSelection/ActualHartreeSpectralCorrectedFourPieceThreeC1.lean`. Its strict theorem certifies three C1 joins. The current source record `ActualHartreeInnerSpectralC2PlateauSourceLock.lean` proves the exact inner second-jet discrepancy

\[
 \Delta_2=u_{\rm in}''(L)-v_{\rm out}''(L)
 =\mathcal K_a u_{\rm in}(L)-a^{-2}\{F(L/a)-d u_0(L/a)\}.
\]

Its native shell-budget theorem BOUNDS this expression; it does not establish that it vanishes. It is important not to replace the inner physical Hessian by the outer Kummer operator or to discard the unshifted first-order spectral term. We do NOT claim that this discrepancy is nonzero on every possible selected physical orbit. The following is a precise obstruction whenever it is nonzero, and an acceptance condition that must be checked for the actual orbit.

Let the one-sided pieces be classical, with C1 dependence on time, piecewise spatial smoothness, and a C1 moving interface r=L(s)>0. Suppose the field and its first spatial derivative agree there. Differentiating the value matching along the moving interface gives

\[
 [U_s]+L_s[U_r]=0,\qquad [U]=[U_r]=0,\qquad [U_s]=0.
\]

Here brackets mean right minus left. Assume the genuine Hartree potential is finite and continuous near this interface; for the classical decaying fields in the intended source class this follows by splitting the locally integrable inverse-square kernel. For the SAME full renormalized physical residual

\[
 F_{\rm full}=iU_s+U_{rr}+2r^{-1}U_r
    +\kappa_H(|x|^{-2}*|U|^4)|U|^2U
    +i b(\tfrac12U+rU_r)+\omega U,
\]

all terms other than U_rr have equal one-sided traces. Thus

\[
 [F_{\rm full}]=[U_{rr}]=-\Delta_2.
\]

This concerns the actual nonlinear residual, not merely the auxiliary Kummer defect. Reversing a residual sign convention reverses both jumps and changes no norm conclusion. No Dirac mass occurs in the undifferentiated Laplacian of a C1 field, but a NONZERO jump in its residual still matters for the differentiated or energy-dual source space.

## 2. A nonzero residual jump makes the proposed source norm INFINITE

At any fixed R>0 let real F be C1 on each side of R, with one-sided jump J=F(R+)-F(R-) != 0. Localize by a smooth cutoff equal to one near R, so F is in physical radial L2. Choose real phi in C_c^infty((-1,1)) with phi'(0)=1 and put

\[
 g_\epsilon(r)=\sqrt\epsilon\,\phi((r-R)/\epsilon),\qquad 0<\epsilon<R/2.
\]

Use the actual phase Hessian L_-=-partial_r^2-2r^{-1}partial_r-3W^4 and the radial Morawetz test norm

\[
 \|g\|_{\rm Mor}^2=\int_0^\infty
 \left(\frac{|(rg)'|^2}{1+r^2}+
       \frac{|rg|^2}{(1+r^2)^2}\right)\,dr.
\]

Direct change of variables yields

\[
 \|g_\epsilon\|_{\rm Mor}^2
 =\frac{R^2}{1+R^2}\int_{-1}^{1}|\phi'|^2\,dx+O(\epsilon),
 \qquad \|g_\epsilon\|_{L^2(\mathbb R^3)}=O(\epsilon).
\]

Splitting the physical radial integral at R gives

\[
 (L_-g_\epsilon,F)_{L^2(\mathbb R^3)}
 =4\pi R^2J\epsilon^{-1/2}+O(\epsilon^{1/2}).
\]

Indeed the leading term is -4pi epsilon^(-1/2) times the integral of phi'' against R^2 F(R-) on x<0 and R^2 F(R+) on x>0; the two integrals of phi'' are 1 and -1. The radial first-derivative term and variation of r^2 F contribute O(sqrt(epsilon)); the bounded potential contributes O(epsilon^(3/2)). Hence

\[
 \boxed{\sup_{\|g\|_{\rm Mor}\le1}|(L_-g,F)|=+\infty.}
\]

For a complex jump use a nonzero real component or a constant phase rotation. The same principal-part argument applies to L_+: its additional genuine Hartree integral operator is bounded on physical L2, and therefore contributes only O(epsilon)||F||_2 in this test. For completeness its kernel is

\[
 4\kappa_H W(x)^3|x-y|^{-2}W(y)^3.
\]

Its row and column integrals are uniformly bounded: on |x-y|<=1 use W^3<=1 and integral |x-y|^(-2)=4pi; on the complement use Cauchy--Schwarz, the square integrability of |x-y|^(-2) there, and W^3 in L2. Schur's estimate follows directly from Cauchy--Schwarz and Fubini. Thus the nonlocal lower-order term cannot cancel the unbounded principal pairing. The same conclusion holds for an unlocalized original source whenever its lower-order pairing satisfies these natural source-space bounds.

There is also an endpoint fractional-Sobolev obstruction. The exact angular integral for radial functions in dimension three gives the local H^(1/2) seminorm integrand

\[
 4\pi^2 r\rho |F(r)-F(\rho)|^2
 \left(\frac1{(r-\rho)^2}-\frac1{(r+\rho)^2}\right)\,dr\,d\rho.
\]

Restrict to r=R-x, rho=R+y, 0<x,y<eta. The jump gives |F(r)-F(rho)|>=|J|/2 for small eta; the integral of (x+y)^(-2) diverges logarithmically. Consequently F is not even locally H^(1/2). A weight bounded above and below near R changes neither conclusion. Making J arbitrarily small but nonzero, or multiplying it by any positive temporal decay factor, does NOT turn the infinite per-time source norm into a finite one.

These statements obstruct the particular energy-dual/Kato source interface proposed in the proof notes. They do not disprove a distributional boundary-forcing method or the desired Type-II solution. A finite-rank projection with locally smooth range cannot remove an existing jump merely by subtracting smooth modes.

## 3. C2 matching alone does NOT imply the required moving-interface H1 Lipschitz control

Even after [U_rr]=0 removes the source jump, a moving jump in U_rrr can destroy H1 parameter Lipschitz continuity. A concrete fixed-annulus example is

\[
 U_a(r)=\chi(r-a)(r-a)_+^3/6,
\]

with chi=1 near zero and smooth compact support. This is C2 in r. Near r=a, its principal radial residual is

\[
 F_a(r)=\Delta_r U_a=(r-a)_++r^{-1}(r-a)_+^2,
\]

so F_a' has a unit jump. For small h>0, on a<r<a+h the derivatives of F_a and F_(a+h) differ by 1+O(h). Smooth pieces contribute only O(h) to the relevant L2 norm. In particular

\[
 \|F_{a+h}-F_a\|_{H^1(\text{fixed annulus})}\ge c\sqrt h,
\]

which rules out an O(h) Lipschitz bound. Fixed-annulus weighted norms are equivalent here. More generally a nonzero moving jump in F_r produces this mechanism when the one-sided source families have bounded smooth parameter derivatives. It is a counterexample to an implication from C2 matching alone, NOT a claim that every C2 family fails or that every source topology requires C3.

For the proposed H1-type source route, a sufficient local repair is to match spatial jets through order THREE. With C1 time dependence, differentiating [U_r]=0 and using [U_rr]=0 gives [U_sr]=0; hence [F_r]=[U_rrr] for the smooth nonlocal lower-order terms. C3 matching eliminates this moving first-derivative jump. Quantitative parameter Lipschitz bounds STILL require actual controls on the within-piece fourth spatial derivatives and parameter/time derivatives. No such bounds are assumed to follow from endpoint algebra.

## 4. Explicit source-dependent C3 repair, without new value or slope parameters

At one interface let

\[
 d_2=U_{\rm in}''(L)-U_{\rm out}''(L),\qquad
 d_3=U_{\rm in}'''(L)-U_{\rm out}'''(L).
\]

For h>0 and t=(r-L)/h set

\[
 \phi_2(t)=\tfrac12t^2(1-t)^4(1+4t),\qquad
 \phi_3(t)=\tfrac16t^3(1-t)^4,
 \qquad P(r)=h^2d_2\phi_2(t)+h^3d_3\phi_3(t).
\]

Exact differentiation gives

\[
 (P,P',P'',P''')(L)=(0,0,d_2,d_3),\qquad
 (P,P',P'',P''')(L+h)=(0,0,0,0).
\]

Add P to the actual right-hand piece on [L,L+h], keep the original left piece and the original right piece beyond L+h. The full field is C3 at both joins, preserves its original value and slope at L, and introduces no freely chosen d2,d3: they must be computed from the same actual fields. For complex fields apply the construction componentwise. For three ordered interfaces choose disjoint right-hand repair intervals. For k<=4, elementary scaling gives

\[
 \|P^{(k)}\|_{L^2(L,L+h)}
 \le h^{5/2-k}|d_2|\|\phi_2^{(k)}\|_{L^2(0,1)}
     +h^{7/2-k}|d_3|\|\phi_3^{(k)}\|_{L^2(0,1)}.
\]

This is a finite-jet construction, not a gain in time. In particular fourth derivatives have costs h^(-3/2)|d2| and h^(-1/2)|d3|. A moving interface also differentiates t=(r-L)/h and its jet coefficients; their true time and parameter bounds remain indispensable.

**Nonlocal compatibility warning:** preserving C1 boundary traces and retaining the numerical old speeds does NOT prove that the newly corrected field satisfies the old Hartree source compatibility equations. Its full quartic convolution changes globally. The same-source nonlinear increment, its source norms, and the two-speed selector must be recomputed or controlled together. Do not quietly promote the polynomial correction to a solved Hartree packet.

## Audit and stopping boundary

Start HEAD: `105e51300b96281983f3562f75c13486099ac8c6`. Re-read original CI 42929423991, job 130224109335: the exact three statements are jet ALGEBRA, with pinned Lean 4.35.0-rc3 and Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, trust-zero, warningAsError, permitted three-axiom audit. Its archive is 13816021136. It does not prove a flux estimate. Historical CI 42854633900 checks the exact C2 discrepancy and its native budget, not its vanishing. The later complete nonlinear telescope CI 42927397872 supersedes the initial dependency failure, but is an equality, not a source bound.

The new module `ActualHartreeInterfaceC3RepairPolynomial.lean` is restricted to the two polynomial facts just stated. Its dedicated workflow must actually succeed before these are described as Lean-verified; the source regularity obstruction, global C3 splice, nonlinear feedback, and physical orbit are NOT among its Lean conclusions. Strict CI provenance is appended to the manuscript/ledgers only after a successful audit. Original count **11/13**, unchanged.
