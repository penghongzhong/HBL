# HBL §2.13 — exact phase Hessian zero-energy Fredholm gate (10 November 2026)

**Status:** New self-contained *paper proof* for the **actual** 3D quartic inverse-square Hartree phase Hessian; not a Lean certificate, not a full coupled-Hartree resolvent, and not a constructed nonlinear orbit. The official retained revised-original count stays **11/13**. This replaces no source estimate by an independent assumption.

## 1. Actual phase Hessian, ground-state factorization and zero mode

For the original normalized Hartree nonlinearity
\[
\mathcal N(u)=\kappa_{\rm H}(|x|^{-2}*|u|^4)|u|^2u,\quad
W(r)=(1+r^2)^{-1/2},\quad -\Delta W=3W^5=\mathcal N(W),
\]
linearization in the imaginary direction (the convolution density has zero first imaginary variation at a positive real \(W\)) gives the **exact physical phase channel**
\[
L_-=-\Delta-3W^4 .
\tag{P1}
\]
It is not an NLS substitute for the real channel: the true real Hessian is still
\(L_+=-\Delta-9W^4-4W^3\mathcal I(W^3\cdot)\), with \(\mathcal I f=\kappa_{\rm H}(|x|^{-2}*f)\).

For every complex \(g\in C_c^\infty(\mathbb R^3)\) (or a radial smooth compactly supported \(g\)), write \(g=Wv\). Using the exact stationary equation and integration by parts,
\[
\boxed{\quad
 \int_{\mathbb R^3}\left(|\nabla g|^2-3W^4|g|^2\right)dx
 =\int_{\mathbb R^3}W^2|\nabla(g/W)|^2dx\ge0 .
\quad}\tag{P2}
\]
In particular the *fixed phase channel* has no negative quadratic direction. Since \(L_-W=0\), \(W\) is a radial zero-energy resonant state:
\(W(r)\sim r^{-1}\), \(W\in\dot H^1(\mathbb R^3)\) but \(W\notin L^2(\mathbb R^3)\).
This prevents blindly using a zero-regular unprojected limiting-absorption statement. It does not settle the coupled Hamiltonian's positive-energy spectrum or Kato smoothing.

## 2. Exact radial first-order reduction and full regular zero-energy family

For a radial \(g=Wv\), the physical radial identity is
\[
\boxed{\quad L_-(Wv)
=-\frac{1}{r^2W(r)}\frac{d}{dr}\left(r^2W(r)^2v'(r)\right).\quad}
\tag{P3}
\]
For a radial regular solution of \(L_-g=F\), let
\[
M_F(r)=\int_0^r t^2W(t)F(t)\,dt .
\]
Regularity at the origin eliminates the singular homogeneous flux and yields
\[
 \boxed{\quad
 v'(r)=-\frac{M_F(r)}{r^2W(r)^2}
       =-\left(1+\frac1{r^2}\right)M_F(r).\quad}
 \tag{P4}
\]
For \(F=0\), the independent radial homogeneous solutions are
\[
 g_0(r)=W(r),\qquad
 g_{\rm sing}(r)=W(r)(r-r^{-1}).
 \tag{P5}
\]
The second is singular as \(r^{-1}\) at the origin, while the regular zero-energy family is **exactly** the span of \(W\). One can verify \(L_-g_{\rm sing}=0\) by substituting
\((r^2W^2(g_{\rm sing}/W)')'=0\) directly.

## 3. An exact Fredholm alternative for compact radial forcing

Assume \(F\in C_c^\infty(\mathbb R^3)\) is radial and real or complex, with support in \(r<R\). A necessary condition for any origin-regular \(\dot H^1\) radial solution of \(L_-g=F\) is
\[
\boxed{\qquad
 \mathcal M_-(F):=\int_0^\infty r^2W(r)F(r)\,dr=0.
 \qquad}
\tag{P6}
\]
Indeed for \(r\ge R\), (P4) gives \(v'=-\mathcal M_-(F)(1+r^{-2})\),
hence \(g(r)=W(r)[c-\mathcal M_-(F)(r-r^{-1})]\).
If \(\mathcal M_-(F)\ne0\), then \(g(r)\to-\mathcal M_-(F)\ne0\);
this violates the \(L^6\) embedding of \(\dot H^1(\mathbb R^3)\).

Conversely, if (P6) holds, define **from the actual forcing**
\[
 \boxed{\qquad
  g_F(r)=W(r)\int_r^R
     \left(1+\frac1{s^2}\right)
     \left(\int_0^s t^2W(t)F(t)\,dt\right)\,ds
 \quad (0<r<R), \qquad g_F(r)=0\quad(r\ge R).
 \qquad}
 \tag{P7}
\]
For smooth radial forcing the integrand is \(O(s)\) at \(s=0\);
it vanishes identically for \(s\ge R\) by (P6).
Thus \(g_F\) is regular, compactly supported, belongs to \(H^1\),
and solves **the exact original phase equation** \(L_-g_F=F\).
All origin-regular \(\dot H^1\) radial solutions are \(g_F+cW\);
\(g_F\) is the unique such solution in \(L^2\).

Therefore the compact-source phase Fredholm compatibility is an
**exact physical moment**, not an arbitrary independent source envelope.
In any genuinely moving four-region Hartree scheme the phase component
must produce this cancellation from the actual projected PDE or instead
use an explicitly resonance-renormalized inverse.

## 4. What is (and is not) closed

(P2)–(P7) close the **stationary radial phase-channel zero-energy algebra and its compact-source Fredholm alternative on paper**. They do not establish the nonlocal **real** Hessian resolvent, matrix-Hamiltonian eigenvalue exclusions, an \(L_s^2\) adjoint Kato estimate, moving-parameter Lipschitz, the complete four-region source's Morawetz-dual norm or its positive time order, a physical orbit, or a dynamically selected Type-II rate. The actual Hartree nonlinear phase source has **not** been proved to satisfy (P6); compactness of that source has likewise **not** been proved. This lemma may only be used under its explicit smooth compact radial forcing hypothesis (or a subsequently justified weighted extension).

**Lean audit:** This new phase reduction has no new pinned Lean --trust=0 CI and must not be counted as formally verified. Existing strict CI 42536552509 (four-piece nonlinear PDE *telescoping identity*) and 42854633900 (fixed-slice same-source \(C^2\) curvature budget) remain valid **only for their exact declared types**. The revised original §2.13 and the final Type-II theorem remain OPEN: **11/13**.
