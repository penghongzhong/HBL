# HBL §2.13 — a source-faithful interface obstruction and a C² replacement

**Date:** 10 November 2026. **Status:** Paper analysis and exact construction only. No Lean acceptance, no assertion that the original Hartree orbit exists, and no change to the strict revised-original **11/13** count.

## 1. Source of the obstruction in the *actual* code

The public, strict-successful
\`HBL/TypeIIDynamicSelection/ActualHartreeSpectralCorrectedFourPieceThreeC1.lean\`
uses
\`actualHartreeInnerKummerSpectralFourPiece\` and
\`actualKummerPhysicalInterfaceRepair\`.
The latter is literally
\[
  \mathrm{Rep}_{a,B,p,q}(y)=\chi_B(y/a)
         [p+(y/a-B)q],\qquad
  \chi_B(r)=1-\mathrm{cutoff}((r-B)/(B/3)).
\]
The existing cutoff is exactly **one on a neighbourhood of \(B\)**
and exactly **zero on a neighbourhood of \(2B\)**. In particular,
\[
 \mathrm{Rep}(aB)=p,\quad
 \partial_y\mathrm{Rep}(aB)=a^{-1}q,\quad
 \partial_y^2\mathrm{Rep}(aB+)=0.
\]
For the truly corrected source-dependent Kummer solution
\(w(r)=\mathrm{actualHartreeMatchedSpectralCorrectedValue}(r)\),
its physical continuation \(v(y)=w(y/a)\) satisfies
\[
 v(aB)=p:=w(B),\quad
 v_y(aB)=a^{-1}q,\ q:=w'(B),\quad
 v_{yy}(aB-)=a^{-2}j,\ j:=w''(B),
\]
assuming the claimed classical derivatives exist. Hence the *literal*
C¹ splice of the verified module has the **explicit one-sided second-jet jump**
\[
\boxed{
 [U_{yy}]_{aB}
 :=U_{yy}(aB+)-U_{yy}(aB-)
 =-a^{-2}w''(B).
}
\tag{G1}
\]
The three verified \(C^1\) joins impose no condition \(w''(B)=0\).
At the farther join \(y=2aB\), the repair is identically zero nearby,
so this particular second-jet obstruction is absent there. At the inner
join \(y=L\), a **separate** second-jet mismatch may occur: the current
weighted \(L^2\) Fredholm source hypotheses only certify \(C^1\), not
\(u_{\rm inner}''(L)=v_{\rm Kummer}''(L)\).

Suppose the physical modulation paths are sufficiently regular and the
true nonlocal Hartree convolution is continuous through the join. A
\(C^1\)-matched moving interface has matching **one-sided partial time
derivatives** as well: differentiate the equality of the two values along
the moving interface and cancel the equal slopes. All terms of the
renormalized Hartree residual other than its radial second derivative
therefore match. With the original convention containing \(+\Delta\),
its one-sided residual jump is
\[
 [F_{\rm full}]_{aB}=-a^{-2}w''(B)
 \quad\text{(up to any other separately constructed corrections
  touching the same join).}
\tag{G2}
\]
This is an *interface computation*, not an assertion that a particular
yet-to-be-constructed physical orbit has a nonzero jump.

## 2. A genuine jump cannot obey the proposed Morawetz-energy dual bound

Let \(R>0\), let \(F\) be piecewise \(C^1\) near \(R\), and suppose
\[
 J:=F(R+)-F(R-)\ne0.
\]
With the three-dimensional radial measure, for smooth compactly
supported test \(g\) one has the **exact integration-by-parts formula**
\[
\frac{\langle-\Delta g,F\rangle_{\mathbb R^3}}{4\pi}
=R^2 g'(R)J
 +\int_0^\infty r^2 g'(r)F'_{\rm pw}(r)\,dr .
\tag{G3}
\]
The formula is stated for real components; for a complex jump, choose
a real or imaginary component whose jump is nonzero. Choose a smooth
compactly supported \(\phi\) with \(\phi'(0)\ne0\), and set
\[
 g_\epsilon(r)=\epsilon^{1/2}\phi((r-R)/\epsilon).
\]
On a fixed annulus around \(R\), Kim's radial Morawetz norm and
the \(\mathrm{Mor},0\) norm used in the HBL paper satisfy
\[
 \sup_{0<\epsilon<\epsilon_0}\|g_\epsilon\|_{\mathrm{Mor},0}<\infty,
 \qquad
 g'_\epsilon(R)=\epsilon^{-1/2}\phi'(0).
\]
The second term in (G3) is \(O(\epsilon^{1/2})\) if \(F'_{\rm pw}\)
is locally bounded. Meanwhile its first term grows as
\(R^2 J\phi'(0)\epsilon^{-1/2}\). The short-range multiplication
terms in \(L_\pm\) are lower order for these tests. The extra
nonlocal Hartree real-Hessian term is also lower order by local
Hilbert–Schmidt boundedness (or by symmetry and smoothness of the
original fixed bubble-weighted kernel). Thus a **nonzero residual jump**
does **not** satisfy a Morawetz-dual estimate
\[
 |\langle L_\pm g,F\rangle|
 \le C\|g\|_{\mathrm{Mor},0}
 \quad\text{for every }g\in C_c^\infty
\tag{G4}
\]
with finite \(C\).

Equivalently, \(F'_{\rm distribution}\) contains \(J\delta_R\)
and is not an ordinary weighted \(L^2(dr)\) derivative. This is
**stronger and more structural** than the preceding oscillatory
counterexample: the current verified \(C^1\) matching theorem cannot
by itself put the *physical residual* into the proposed Kato energy
dual space. Projecting away a finite-dimensional smooth threshold
sector does not automatically eliminate a delta-prime singularity
produced by a jump. A genuine projection-specific cancellation
would require its own proof.

## 3. Exact source-faithful local C² repair — still needs a physical norm estimate

There is a straightforward **candidate** with no prescribed blowup
parameter, no external source or free matching curvature.
The same corrected Kummer field provides the third value
\[
  j:=w''(B)
\]
by its original source-dependent differential equation. Replace the
existing affine repair by
\[
 \boxed{
 \mathrm{Rep}^{(2)}_{a,B}(y)
  =\chi_B(y/a)\left[
     p+(y/a-B)q+\frac12(y/a-B)^2j
  \right].
 }
\tag{G5}
\]
Since the **same existing cutoff** is exactly \(1\) near \(B\) and
\(0\) near \(2B\), its endpoint jets satisfy, by direct
differentiation,
\[
\begin{array}{c|ccc}
y & \mathrm{Rep}^{(2)} & \partial_y\mathrm{Rep}^{(2)}
 &\partial_y^2\mathrm{Rep}^{(2)}\\ \hline
aB & w(B)&a^{-1}w'(B)&a^{-2}w''(B)\\
2aB&0&0&0.
\end{array}
\tag{G6}
\]
Therefore the **outer** two joins can be made \(C^2\), provided
\(w\) is \(C^2\) and the source data actually produce those
derivatives. This does **not** automatically give a positive
time-order residual. The extra correction costs a physical curvature
budget of size \(\|j\|\) (with spatial factors depending on \(B,a\)),
whose size and parameter Lipschitz bound must be derived from the
same physical original Hartree source.

The **inner join** \(y=L\) must be handled separately. If both inner
and Kummer profiles admit second derivatives, let
\(\Delta_2=u_{\rm inner}''(L)-v_{\rm Kummer}''(L)\).
A smooth one-sided correction on the Kummer side,
\[
 \mathrm{Patch}_L(y)=\frac{\Delta_2}{2}(y-L)^2
   \chi_{\rm in}((y-L)/h),\qquad y\ge L,
\tag{G7}
\]
with \(\chi_{\rm in}\equiv1\) near \(0\) and supported in a short
positive overlap interval that ends before \(aB\), matches the second
jet without altering the existing value and slope. The actual
Fredholm \(C^2\) regularity, the size of \(\Delta_2\), moving
derivatives of the cutoff, nonlocal mixed interactions and their
weighted derivative bounds all remain genuine open PDE obligations.

**Alternative:** prove an entirely different projected smoothing
bound whose source dual space permits these interfaces; do **not**
pretend (G1)–(G4) vanish merely because the pointwise PDE telescope
is a Lean identity.

## 4. Updated shortest physical closure gate

\[
\text{original physical two-channel source}
\to \text{true }w,\ w',w''\text{ and actual Fredholm C²}
\to \text{C² four-region matching}
\to
\begin{matrix}
\text{whole-nonlinear PDE residual}\\
\text{weighted derivative and parameter Lipschitz}
\end{matrix}
\to \text{Hartree projected adjoint smoothing/inversion}
\to \text{true orbit and dynamic Type-II rate}.
\]
The old exact three-\(C^1\) CI remain **valid** as stated, but
do not imply \(C^2\) or any \(O(s^{-15/8})\) or \(O(s^{-9/4})\)
dual source estimate. Any exact PDE telescope remains an identity
even if classical second derivatives do not exist at a join.

**Official revised original count: 11/13.**
