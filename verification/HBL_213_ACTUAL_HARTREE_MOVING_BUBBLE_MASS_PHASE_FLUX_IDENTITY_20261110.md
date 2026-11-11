# HBL revised §2.13 — exact moving-bubble mass/phase-flux identity (10 November 2026)

**Acceptance status:** This is a new paper proof for a smooth radial strong solution of the **complete original** quartic-density inverse-square Hartree PDE. It is not a Lean certificate, not an actual constructed HBL four-region trajectory, and not a time-positive error bound. The original revised count is **11/13**, with §2.13 and the final Type-II theorem still open.

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