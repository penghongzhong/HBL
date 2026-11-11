# HBL revised §2.13 — exact moving-bubble mass/phase-flux identity (10 November 2026)

**Acceptance status:** (MP1)–(MP9) are a new paper proof for a smooth radial strong solution of the **complete original** quartic-density inverse-square Hartree PDE, not an actual constructed HBL four-region trajectory or a time-positive error bound. The finite-dimensional jet algebra behind (MP10) and the phase-current/Wronskian composition have now been separately certified in strict Lean; this does **not** certify the unproved physical PDE orbit or the full analytic chain. The original revised count is **11/13**, with §2.13 and the final Type-II theorem still open.

## 1. Complete physical PDE and genuinely moving bubble

For a complex radial field \(u(t,r)\), the original equation is

\[
iu_t+\Delta_r u+\mathcal V_H[u]u=0,\qquad
\mathcal V_H[u](t,r)=\kappa_H
\bigl(|x|^{-2}*|u(t)|^4\bigr)(r)|u(t,r)|^2,\quad
\kappa_H=3/\pi^2,
\]
where \(\Delta_r=\partial_r^2+2r^{-1}\partial_r\).
In particular, \(\mathcal V_H[u]\) is **real**, but it remains the complete three-dimensional nonlocal convolution; it is not replaced by a local NLS potential.

Let \(\lambda(t)>0\), \(W(y)=(1+y^2)^{-1/2}\), and
\[
B(t,r)=\lambda(t)^{-1/2}W(r/\lambda(t)),\qquad
u=B+p+iq,\quad p,q\in\mathbb R.
\]
The exact stationary Hartree bubble equation and scaling imply
\[
-\Delta_r B=\mathcal V_H[B]B,\qquad
\mathcal V_H[B]=3B^4,\qquad
B_t=-\frac{\lambda_t}{\lambda}\Lambda B,\quad
\Lambda=\frac12+r\partial_r.
\]
The true moving phase Hessian is
\[
L_{-,\lambda}=-\Delta_r-3B^4,\qquad
L_{-,\lambda}B=0.
\]

Assume \(\lambda,R\in C^1\), \(R(t)>0\); assume \(u\) is sufficiently regular in \(t,r\) for radial product differentiation and the moving-endpoint Leibniz rule on \([0,R(t)]\), and that the radial flux vanishes at the origin. Only **finite** radii are used; neither \(u\) nor \(B\) is required to be in \(L^2(\mathbb R^3)\).

## 2. Original nonlocal PDE produces the phase source, rather than postulating it

The imaginary part of the original complex PDE gives
\[
B_t+p_t+\Delta_rq+\mathcal V_H[u]q=0.
\]
Therefore the **actual** phase equation, without a separate source envelope, is
\[
\boxed{\quad
L_{-,\lambda}q
=B_t+p_t+\bigl(\mathcal V_H[u]-3B^4\bigr)q
=-\frac{\lambda_t}{\lambda}\Lambda B+
p_t+\bigl(\mathcal V_H[u]-\mathcal V_H[B]\bigr)q.
\quad}\tag{MP1}
\]
All nonlocal cross-interactions remain inside the full \(\mathcal V_H[u]\), and \(\lambda_t/\lambda\) has not been assigned a blowup law.

As \(L_{-,\lambda}B=0\), multiply (MP1) by \(r^2B\) and integrate by parts on \((0,R)\). The exact finite-radius Wronskian identity is
\[
\boxed{\quad
R^2(Bq_r-B_rq)(t,R)
=-\int_0^R r^2 B
\left[B_t+p_t+(\mathcal V_H[u]-3B^4)q\right](t,r)\,dr.
\quad}\tag{MP2}
\]
The origin boundary term is zero by regularity. This equation does **not** require global phase Fredholm-moment cancellation.

## 3. The *same* true Hartree flow supplies a localized mass-flux law

The nonlocal potential is real, so it cancels exactly in the local mass continuity identity:
\[
\partial_t|u|^2=
-\frac2{r^2}\partial_r\left[r^2
\Im(\overline u\,u_r)\right],\qquad
\Im(\overline u\,u_r)=Bq_r-B_rq+pq_r-qp_r.\tag{MP3}
\]

For a differentiable **moving physical interface** \(R=R(t)\) define the renormalized local mass
\[
M(t):=\frac12\int_0^{R(t)}
r^2\bigl(|u(t,r)|^2-B(t,r)^2\bigr)\,dr
=\int_0^{R(t)}r^2\left(Bp+\frac{p^2+q^2}{2}\right)dr.
\]
Using (MP3) and Leibniz' rule, with the full moving endpoint retained, gives
\[
\boxed{\begin{aligned}
M'(t)={}&-R^2(Bq_r-B_rq)(t,R)
          -R^2(pq_r-qp_r)(t,R)\\
&-\int_0^Rr^2BB_t\,dr
+\frac{R^2R_t}{2}\left(|u(t,R)|^2-B(t,R)^2\right).
\end{aligned}}\tag{MP4}
\]

Substitute the **same-source Wronskian** (MP2) into (MP4). The full divergent-looking dilation moment \(\int_0^Rr^2BB_t\) cancels **exactly**, giving the dynamic phase-mass compatibility law
\[
\boxed{\begin{aligned}
\int_0^{R(t)}r^2 B(t,r)
\Bigl[p_t(t,r)+\bigl(\mathcal V_H[u](t,r)-\mathcal V_H[B](t,r)\bigr)
q(t,r)\Bigr]\,dr
={}&M'(t)
-\frac{R(t)^2R_t(t)}2\bigl(|u(t,R(t))|^2-B(t,R(t))^2\bigr)\\
&+R(t)^2\bigl(pq_r-qp_r\bigr)(t,R(t)).
\end{aligned}}\tag{MP5}
\]
Equation (MP5) is a **consequence of the genuine nonlocal PDE**, not a chosen orthogonality assumption or an isolated Kummer source bound. It holds for every finite physical radius at which the hypotheses hold, including \(R'(t)\ne0\). No local NLS substitution or fake modulation-rate hypothesis is used.

**Interpretation:** the order-\(\lambda_t/\lambda\) phase-resonant forcing in (MP1) is carried by the physical mass transport and exterior current; it must not be independently projected to zero while also demanding negligible exterior C¹ flux. The explicit cancellation in (MP5) provides a natural alternative **proof interface** to annulus-only phase repair, not a decay estimate. The unknown \(M'(t)\), endpoint current, and the fully nonlocal cross-density term must still be controlled along a *constructed* matched Hartree orbit. In particular, this identity alone proves neither \(s^{-15/8}\) nor \(s^{-(17/8+\eta)}\), parameter Lipschitz, a projected propagator inverse, real finite-level recursion, or dynamically selected Type-II blowup.

## 4. Exact connection to the prior phase-Fredholm constraint

At fixed \(t\), the earlier Wronskian obstruction uses \(L_{-,\lambda}q\) as the true source. Equations (MP1)–(MP5) show **where** its required compensating finite-radius phase moment must come from: the original nonlinear PDE's local mass transport, including the physical moving boundary and the term \((\mathcal V_H[u]-\mathcal V_H[B])q\). Thus no universal annular \(H^1\) correction can be assumed to replace that transport.

The result is stated in the **unrescaled physical** time/radius frame. Converting it to the actual HBL renormalized moving Kummer frame requires the exact clock, scaling and phase chain rule. The existing exact four-piece PDE telescope (historical strict CI 42536552509) does not supply those estimates. No Lean statement has yet been compiled for (MP1)–(MP5), and these identities do not promote either outstanding original environment.

## 5. Direct renormalized moving-Kummer-frame identity: no bare scaling-moment loss

The previous sections use unrescaled physical time \(t\). A **second exact algebraic consequence** applies directly to the renormalized PDE in the moving critical-scale and phase frame. This is relevant because the original HBL \(\S2.13\) works in precisely such a frame.

The sign convention in this subsection is **\(b=\lambda_s/\lambda\)**. In the existing original HBL Lean residual, the parameter is instead \(b_{\mathrm{HBL}}=-\lambda_s/\lambda=-b\), with \(\omega=-\gamma_s\); inserting these substitutions gives exactly its \(iU_s+\Delta U+\mathcal V_H[U]U+i b_{\mathrm{HBL}}\Lambda U+\omega U=0\). This is a notation conversion, not a change of PDE.\n\nSet \(y=r/\lambda(t)\), \(ds/dt=\lambda^{-2}\), \(b(s)=\lambda_s/\lambda\), and
\(u(t,r)=\lambda^{-1/2}e^{i\gamma(s)}U(s,y)\). The exact original equation becomes
\[
\boxed{\quad
 iU_s+\Delta_y U+\mathcal V_H[U]U-i b\Lambda U-\gamma_s U=0,
 \quad \Lambda=\tfrac12+y\partial_y.
\quad}\tag{MP6}
\]
Write \(U=W+p+iq\) with \(p,q\) real. The imaginary equation is exactly
\[
\boxed{\quad
L_-q=p_s-b\Lambda W-b\Lambda p+
 [\mathcal V_H[U]-3W^4]q-\gamma_s q,
\quad L_-=-\Delta_y-3W^4.
\quad}\tag{MP7}
\]
The full nonlocal convolution is retained; the \(b\Lambda W\) term is generated by the **true scaling chain rule**, not externally assigned.

The phase-independent renormalized mass continuity identity is
\[
\partial_s|U|^2
=-\frac2{y^2}\partial_y\bigl(y^2\Im(\bar U U_y)\bigr)
+b\bigl(|U|^2+y\partial_y|U|^2\bigr).\tag{MP8}
\]
For a moving renormalized interface \(L=L(s)>0\) define
\[
\mathscr M(s):=\frac12\int_0^{L(s)}
y^2\bigl(|U(s,y)|^2-W(y)^2\bigr)\,dy.
\]
The source moment of (MP7), the finite-radius Wronskian with \(L_-W=0\),
and (MP8) give, after one integration by parts,
\[
\boxed{\begin{aligned}
\int_0^{L(s)}y^2W
\left[p_s+(\mathcal V_H[U]-3W^4)q-\gamma_s q\right]dy
={}&\mathscr M_s
 +L^2(pq_y-qp_y)(s,L)\\
&-\frac{L^2L_s}{2}\bigl(|U(s,L)|^2-W(L)^2\bigr)\\
&-\frac b2 L^3(p^2+q^2)(s,L)\\
&-b\int_0^L y^2
   \left[(\Lambda W)p-(p^2+q^2)\right]dy.
\end{aligned}}\tag{MP9}
\]
**Verification of the cancellation.** Denote \(\rho=|U|^2=(W+p)^2+q^2\). In the mass-transport expression after substituting the phase Wronskian, the terms proportional to \(b\) are
\[
\mathcal B=\int_0^L y^2
\left[-W\Lambda(W+p)+\tfrac12(\rho+y\rho_y)\right]dy.
\]
Direct expansion and the product rule give the **pointwise total-derivative identity**
\[
\boxed{\quad
y^2\left[-W\Lambda(W+p)+\tfrac12(\rho+y\rho_y)\right]
=\frac{d}{dy}\left[\frac{y^3}{2}(p^2+q^2)\right]
+y^2\left[(\Lambda W)p-(p^2+q^2)\right].
\quad}\tag{MP10}
\]
The origin endpoint vanishes for a regular radial packet. Integrating (MP10) yields the last two lines of (MP9), with the **whole bare** \(-b\int_0^L y^2W\Lambda W\,dy\) canceled exactly. No hypothetical \(L\sim\sqrt{s}\), independent source envelope, Fredholm moment vanishing, or preassigned Type-II rate is used. The algebraic equality (MP10) was independently checked by symbolic expansion and subsequently strictly Lean-certified as a pointwise jet identity; the passage from the actual nonlocal PDE through differentiability, radial integration and a moving endpoint in (MP6)–(MP9) remains a **paper proof**, not a Lean-compiled nonlinear PDE trajectory.

The remaining \(\mathscr M_s\), full Riesz cross-density term, \(L_s\), \(b\) times perturbations, and outgoing C¹ trace still require honest **quantitative estimates from one nonlinear solution**, with differentiated source norms and parameter Lipschitz. Neither (MP9) nor the historical exact PDE telescope proves that such a solution exists or that these terms gain a positive time power. The revised original count is unchanged at **11/13**.


### Exact Lean scope and current-source CI

The source [ActualHartreeRenormalizedMassPhaseFluxAlgebra.lean](../HBL/TypeIIDynamicSelection/ActualHartreeRenormalizedMassPhaseFluxAlgebra.lean) contains exactly three **auxiliary algebraic** results:

* actual_Hartree_local_mass_phase_current_splits — radial imaginary mass-current split into the true phase Wronskian plus quadratic perturbation current;
* actual_Hartree_renormalized_bare_scaling_phase_mass_jet_cancels — pointwise real-jet polynomial equality underlying (MP10), with the total derivative written as its exact derivative jet;
* actual_Hartree_same_orbit_phase_mass_source_cancels — algebraic elimination of the identical moving-bubble moment when the *two analytic flux identities are separately supplied as hypotheses*.

**Strict GitHub CI [42929423991](https://github.com/penghongzhong/HBL/actions/runs/42929423991)**: Success (2026-11-11 00:13 UTC); original job **130224109335**, evidence artifact **13816021136**. The raw job log confirms Lean 4.35.0-rc3, pinned Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, --trust=0, -DwarningAsError=true, exact three #check / #print axioms reports; their transitive axioms are limited to propext, Classical.choice, Quot.sound. No sorry, admit or new axiom was introduced.

**Crucial scope:** no amount of algebraically certified jet cancellation asserts the existence of an actual nonlinear solution with the required regularity, a parameter-Lipschitz or time-decaying differentiated **four-region Hartree residual**, a bounded projected evolution inverse, or a dynamically derived Type-II rate. The original revised manuscript stays **11/13**, and original \(\S2.13\) remains OPEN.


## 6. Exact local-mass gauge reduction and its nondegenerate scale interface (HBL_LOCAL_MASS_GAUGE_RESONANCE_GATE_20261110)

This step sharpens (MP9) **without postulating any Hartree source decay or Type-II rate**. All fields, time derivatives and endpoint traces are the same as in (MP6)–(MP9); write
\[
 Q(s)=\int_0^{L(s)}y^2(p^2+q^2)\,dy,\qquad
 C(s)=\int_0^{L(s)}y^2W^3p\,dy,\qquad
 \mathscr M(s)=\int_0^{L(s)}y^2(Wp+\tfrac12(p^2+q^2))\,dy.
\]
The explicit Hartree bubble satisfies the **exact** special identity
\[
 \Lambda W=\tfrac12W+yW'=-\tfrac12W+W^3.
\]
Therefore, without assuming \(\mathscr M=0\),
\[
\boxed{\displaystyle
\int_0^L y^2[(\Lambda W)p-(p^2+q^2)]\,dy
=-\frac12\mathscr M+C-\frac34Q. }\tag{MG1}
\]
Define the *actual same-flow* phase source moment and the explicit boundary term
\[
 \mathscr S=\int_0^L y^2W[p_s+(\mathcal V_H[U]-3W^4)q-\gamma_s q]\,dy,\quad
 \mathscr B=L^2(pq_y-qp_y)(s,L)-\frac12L^2L_s(|U|^2-W^2)(s,L)
                   -\frac b2 L^3(p^2+q^2)(s,L).
\]
Substitution into (MP9) produces the **exact** finite-radius mass ODE
\[
\boxed{\quad
\mathscr M_s+\frac b2\mathscr M
=\mathscr S-\mathscr B+bC-\frac{3b}{4}Q,\qquad b=\lambda_s/\lambda .
\quad}\tag{MG2}
\]
Equivalently,
\[
\boxed{\qquad
\frac{d}{ds}\bigl[\lambda^{1/2}\mathscr M\bigr]
=\lambda^{1/2}\left(\mathscr S-\mathscr B+bC-\frac{3b}{4}Q\right).
\qquad}\tag{MG3}
\]
The formerly exposed linear \(\int y^2W\Lambda W\sim-L/2\) is **not**
estimated in isolation: its replacement is the physical mass variable
\(\mathscr M\), an integrable-weight linear term \(C\), and genuinely
quadratic \(Q\). In three dimensions Hölder and Sobolev give
\[
 |C|\le (4\pi)^{-1}\|W^3\|_{L^{6/5}(\mathbb R^3)}
                         \|p\|_{L^6(\mathbb R^3)}
       \le C_*\|\nabla p\|_{L^2(\mathbb R^3)},
\]
where \(W^3\in L^{6/5}(\mathbb R^3)\).
**Neither \(Q\) nor \(\mathscr S,\mathscr B\) is thereby bounded** in the
needed time-weighted source space: (MG3) is a more useful exact
modulation interface, not the positive-time Hartree residual estimate.

A possible *constructive*, not automatically compatible, normalization
uses an independently prescribed **fixed physical** radius \(R>0\):
\[
 M_R(t,\lambda)=\frac12\int_0^R r^2
       \bigl(|u(t,r)|^2-\lambda^{-1}W(r/\lambda)^2\bigr)\,dr.
\]
At any smooth mass-matching root \(M_R(t_0,\lambda_0)=0\), the bubble
scaling derivative is exactly
\[
\boxed{\quad
\partial_{\log\lambda}M_R
  =\lambda^2 I(R/\lambda),\qquad
 I(X)=\arctan X-\frac X2-\frac{X}{2(1+X^2)}.
\quad}\tag{MG4}
\]
For \(X=R/\lambda\ge2\pi\), the elementary inequality
\(I(X)\le\pi/2-X/2\le-X/4\) gives the **nondegenerate** bound
\[
 \partial_{\log\lambda}M_R\le-\frac{\lambda R}{4}<0.
\]
Consequently the implicit-function theorem gives a locally unique \(C^1\)
scale \(\lambda(t)\) through that root, **provided** the actual radial
solution is regular enough and the prescribed fixed \(R\) lies in the
same concentrated branch. From the *original* physical Hartree mass
flux and \(M_R(t,\lambda(t))=0\) one obtains
\[
\boxed{\quad
\frac{\dot\lambda}{\lambda}
 =\frac{R^2\Im(\overline u\,u_r)(t,R)}
        {\lambda^2 I(R/\lambda)} .
\quad}\tag{MG5}
\]
This is a PDE-derived **local scale-speed equation**, not a guessed
Type-II rate. For a prescribed moving \(R(t)\) that is independent of
the scale selection, the numerator becomes
\(R^2\Im(\bar u u_r)-\tfrac12 R^2\dot R(|u|^2-B_\lambda^2)\).
If \(R=\lambda L\) itself depends on the selected scale, one must
differentiate that dependence and re-check the denominator; (MG4)–(MG5)
cannot be copied unchanged. Compatibility of this mass gauge with the
**existing unique real two-channel Cramer/Fredholm selector** has not
been established.

**Sharp limitation of an energy-only argument.** Choose
\(p_{\varepsilon,L}(y)=\varepsilon W(y)\chi(y/L)\), \(q=0\), where
\(\chi\equiv1\) on \([0,1]\), \(\chi\equiv0\) on \([2,\infty)\) and
\(L\ge2\pi\). Then \(\|\nabla p_{\varepsilon,L}\|_{L^2(\mathbb R^3)}
\le C_\chi\varepsilon\) uniformly in \(L\), because
\(\int_0^\infty r^2|W'|^2dr=3\pi/16\). Nevertheless the *full scaling
combination* in (MP10) has the exact value
\[
 \frac{L^3}{2}(p^2+q^2)(L)
 +\int_0^L y^2[(\Lambda W)p-(p^2+q^2)]\,dy
 =\varepsilon(1+\varepsilon)I(L),
\]
whose absolute value is at least
\(\varepsilon(1+\varepsilon)L/4\).
Thus uniformly small \(\dot H^1\) energy **alone** cannot provide
the desired small phase/transport source for expanding \(L\).
This is a test packet, **not** a constructed Hartree solution, so
the example only excludes an energy-only proof step, not same-orbit
radiation cancellations or mass-gauge selection.

**Precise remaining gate.** Derive a compatible local mass (or equivalent
symplectic) gauge from the same physical two-channel modulation system;
then prove the full source moment \(\mathscr S\), quadratic mass \(Q\),
moving C¹ boundary current and their parameter differences in the
actual weighted time spaces, consistently with the full four-region
nonlocal PDE. Neither (MG1)–(MG5) nor the already strict three-jet
algebra CI 42929423991 constitutes original §2.13, a nonlinear
finite-level orbit, or the Type-II rate. **Formal retained count: 11/13.**

