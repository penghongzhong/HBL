# HBL §2.13: constructive shrinking-interface mass root and its *complete* uniform Jacobian

10 November 2026 (PST). **Paper-level conditional proposition**, not an original-Hartree PDE orbit or a Lean-compiled result. This note closes a specific missing *root-existence* step in the shrinking-radius mass gauge under a stated, checkable **physical field** hypothesis. It does **not** assert that the true four-region Hartree correction satisfies that hypothesis, or that an additional scalar gauge is compatible with the unique two-speed Fredholm selector. Revised original environments: **11/13**.

## Exact statement (one time slice, no prescribed blowup law)

Set \(\beta=15/16\), \(W(r)=(1+r^2)^{-1/2}\),
\[
B_a(r)=\frac{\sqrt a}{\sqrt{a^2+r^2}},\qquad
R(\sigma)=\sigma^\beta,\qquad
L(\sigma)=\sigma^{-1/16},\qquad
{\cal M}_u(\sigma)=\frac12\int_0^{R(\sigma)}
r^2\bigl(|u(r)|^2-B_\sigma(r)^2\bigr)\,dr.
\]
Suppose \(0<a<1\), \(a^{-1/16}\ge16\pi\), and the *fixed physical field* on \([0,2a^\beta]\) admits the decomposition
\(u=B_a+z\), \(z\in C([0,2a^\beta];\mathbb C)\), \(\|z\|_\infty\le M\).
Put
\[
\varepsilon=M a^{7/16}+M^2a^{7/8},\qquad
0<\varepsilon\le1/2048,\quad
\delta=128\varepsilon,\quad
I=[a e^{-\delta},a e^\delta].
\]
Then there exists exactly one \(\sigma_*\in I\) with
\[
\boxed{{\cal M}_u(\sigma_*)=0,\qquad
 \frac{|\sigma_*-a|}{a}\le \frac{80}{3}\varepsilon .}\tag{SR1}
\]
Throughout \(I\), the **complete** derivative, including the moving endpoint, satisfies
\[
\boxed{\frac{d}{d\sigma}{\cal M}_u(\sigma)\le-\frac{R(\sigma)}6<0.}\tag{SR2}
\]
At the root the *normalized* shrinking gauge \({\cal G}(\sigma):={\cal M}_u(\sigma)/[\sigma R(\sigma)]\) has a uniform logarithmic Jacobian:
\[
\boxed{\left.\partial_{\log\sigma}{\cal G}(\sigma)\right|_{\sigma_*}
 =\frac{{\cal M}'_u(\sigma_*)}{R(\sigma_*)}\le-\frac16.}\tag{SR3}
\]
If \(M=0\), the same conclusion holds with \(\sigma_*=a\), as a local nondegenerate root (the interval defined by \(\delta=0\) degenerates).

This is a root **for a field already close in pointwise physical norm to a bubble**, not a claim of an actual Hartree orbit, source norm gain, two-parameter modulation or Type-II dynamics. In particular, a genuine Green/Fredholm inner correction is not automatically bounded in the required physical norm.

## Proof with explicit constants

For \(x,R>0\) define the exact bubble half-mass primitive
\[
J(x,R)=\int_0^Rr^2B_x(r)^2\,dr
=xR-x^2\arctan(R/x).
\]
At fixed \(R\),
\[
J_x=R-2x\arctan(R/x)+\frac{Rx^2}{x^2+R^2},
\qquad
J_R=\frac{xR^2}{x^2+R^2}.
\]
For \(x\le 2a\) and \(R\ge4\pi a\),
\[
\frac R2\le J_x(x,R)\le R,\qquad
|\partial_xJ_R(x,R)|
=\frac{R^2|R^2-x^2|}{(R^2+x^2)^2}\le1.\tag{SR4}
\]
The first lower bound uses \(\arctan(R/x)\le\pi/2\). The upper bound uses
\(\arctan v\ge v/(1+v^2)\), \(v>0\).

Split \({\cal M}_u=D+E\), where
\[
D(\sigma)=\tfrac12[J(a,R(\sigma))-J(\sigma,R(\sigma))],
\]
\[
E(\sigma)=\int_0^{R(\sigma)}r^2 B_a(r)\Re z(r)\,dr+
 \tfrac12\int_0^{R(\sigma)}r^2|z(r)|^2\,dr.
\]
For \(\sigma\in I\), \(\delta\le1/16\) implies
\[
a/2\le\sigma\le2a,\quad
\tfrac12a^\beta\le R(\sigma)\le 2a^\beta,\quad
R(\sigma)\ge4\pi a.
\tag{SR5}
\]
Since \(B_a(r)\le\sqrt a/r\) for \(r>0\),
\[
|E(\sigma)|\le\tfrac12M\sqrt aR^2+\tfrac16M^2R^3
\le \tfrac{10}{3}\varepsilon a^{1+\beta}.\tag{SR6}
\]
At either endpoint \(\sigma=a e^{\pm\delta}\),
\(|\sigma-a|\ge a\delta/2\), while (SR4) gives
\[
|D(\sigma)|\ge\tfrac14R|\sigma-a|
 \ge\tfrac{\delta}{16}a^{1+\beta}
 =8\varepsilon a^{1+\beta}.
\]
Thus \(D+E\) has strictly opposite signs at the endpoints. Continuity yields a root.

For every \(\sigma\in I\), differentiating *both* the scale and the moving endpoint gives
\[
D'=\tfrac12\{[J_R(a,R)-J_R(\sigma,R)]R'-J_x(\sigma,R)\},
\qquad R'=\beta R/\sigma.
\]
By (SR4) and \(|a-\sigma|/\sigma\le e^\delta-1\le2\delta\le1/8\),
\[
D'\le -R/4+\tfrac{\beta R}{16}\le -3R/16.
\tag{SR7}
\]
Only the **physical upper endpoint**, and not a fabricated frozen radius, contributes to
\[
E'=R^2R'[B_a(R)\Re z(R)+\tfrac12|z(R)|^2],
\qquad
\frac{|E'|}{R}\le
\beta\left(M\sqrt a\frac R\sigma+\frac{M^2R^2}{2\sigma}\right)
\le4\varepsilon.
\tag{SR8}
\]
As \(4\varepsilon\le1/512\), (SR7)–(SR8) yield
\({\cal M}_u'\le-3R/16+R/512\le-R/6\).
This proves uniqueness. At the root (SR4), (SR5) and (SR6) give
\[
\tfrac18a^\beta|\sigma_*-a|
\le |D(\sigma_*)|=|E(\sigma_*)|
\le\tfrac{10}{3}\varepsilon a^{1+\beta},
\]
which proves (SR1). Differentiating \({\cal M}/(\sigma R)\) **at a root only** proves (SR3). No uniform bound is claimed for the logarithmic derivative away from the root without controlling the normalization derivative.

## PDE/Lean acceptance boundary

The present proposition removes the *scalar* root-existence and endpoint-Jacobian obstruction **for a concrete near-bubble class**. It cannot be inserted into original §2.13 until the same nonlocal Hartree PDE and already selected Cramer/Green correction yield the required physical \(L^\infty\) remainder on the entire shrinking ball, along with differentiable parameter dependence; this may fail for the actual singular Kummer/Fredholm inner correction. Furthermore, fixing the extra scalar scale must be compatible with the two original real compatibility conditions, and the mass-flux evolution must produce quantitative time-positive and parameter-Lipschitz bounds. None of those statements is inferred from (SR1)–(SR3).

No new Lean code, CI success, added axiom or original-environment acceptance is claimed here. Historical CI [42929423991](https://github.com/penghongzhong/HBL/actions/runs/42929423991) checks only three jet-algebra declarations; [42927397872](https://github.com/penghongzhong/HBL/actions/runs/42927397872) checks only the full nonlinear PDE telescope **as an equality**, not its residual bound. **11/13**, both original §2.13 and the PDE-derived Type-II theorem remain OPEN.


## Sharpened two-sided conditioning and a genuine Hartree PDE current–speed identity

The same bounds also give the *lower* derivative estimate, since \(J_x\le R\), \(|a-\sigma|/\sigma\le1/8\), and \(|E'|\le4\varepsilon R\):
\[
-\frac{3R(\sigma)}5\le {\cal M}'_u(\sigma)\le-\frac{R(\sigma)}6,\qquad \sigma\in I.\tag{SR4a}
\]
The numerical lower constant follows from \(9/16+1/512<3/5\). Thus at the root
\[
-\frac35\le
\left.\partial_{\log\sigma}\frac{{\cal M}_u(\sigma)}
{\sigma R(\sigma)}\right|_{\sigma_*}
\le-\frac16.\tag{SR4b}
\]

Suppose **in addition** that \(u(t,r)\) is a sufficiently regular radial solution to the *actual* three-dimensional nonlocal Hartree PDE
\[
i u_t+\Delta_r u+
\kappa_H(|x|^{-2}*|u|^4)|u|^2u=0,
\]
on a time interval around \(t_0\), with local physical \(C^1\) temporal dependence and with \(u(t_0)=B_a+z\) satisfying the preceding hypotheses (so the scalar implicit function theorem applies). Then the root condition uniquely determines a local \(C^1\) scale \(\sigma(t)\) without assigning a blowup law.

Since the Hartree convolution potential is real, the original PDE gives the genuine local continuity equation
\[
\partial_t|u|^2=-2r^{-2}\partial_r(r^2j),\qquad
j=\Im(\overline u\,\partial_r u).
\]
Differentiate \({\cal M}_{u(t)}(\sigma(t))=0\) at \(t_0\), **including** the \(\sigma\)-dependent endpoint already present in \({\cal M}'_u\). Differentiating the physical field at frozen \(\sigma\) contributes \(-R^2j(t_0,R)\). Hence
\[
\boxed{\quad
\dot\sigma(t_0)=\frac{R(\sigma_*)^2
 j(t_0,R(\sigma_*))}
 {{\cal M}'_{u(t_0)}(\sigma_*)},\qquad
\frac53R(\sigma_*)|j(t_0,R(\sigma_*))|
\le |\dot\sigma(t_0)|
\le6R(\sigma_*)|j(t_0,R(\sigma_*))|.
\quad}\tag{SR5a}
\]
Whenever \(j\ne0\), the scale speed has the sign *opposite* to the outward radial current. This is a **PDE-derived local identity and comparison**, not a Type-II blowup rate, a source time-decay estimate, or a claim that the selected original two-channel modulation law equals this scalar law.

The user's original main-theorem threshold is unaffected: the actual four-region field must first be constructed in the requisite physical class, its extra gauge made consistent with the original two real Fredholm speeds, and its time-differentiated *nonlocal* residual and parameter Lipschitz bounds proved. The simple continuity equation alone provides no quantitative current \(j(t,R(t))\), and hence no dynamic rate.
