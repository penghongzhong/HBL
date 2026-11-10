# HBL 2.13: the actual moving-radius overlap on a fixed interval

**Original revised environments: 11/13.** The argument below controls the local linear inverse and exposes the actual material source derivative. It does not assume a time-decaying source, prove the full four-region nonlinear residual, construct a Hartree orbit, or select a Type-II rate. The companion Lean modules have been submitted to strict CI; only a completed exact type/axiom audit permits strict acceptance.

## 1. Do not differentiate a moving Kummer basis

For the original physical operator, write
\[
 K_{a,Q}e=e_{yy}+\left(\frac2y+\frac{iy}{2a^2}\right)e_y+\frac{Q}{a^2}e,
 \qquad Q=\mathrm{frozenZeroCoeff}(\mu,\theta).
\]
Let the *same actual matched difference* satisfy
\(e(L)=e_y(L)=0\). Put
\[
 x=y/L,\qquad E(x)=e(Lx),\qquad
 k=L^2/a^2,\quad z=kQ,\quad
 G(x)=L^2(K_{a,Q}e)(Lx).
\]
Direct differentiation gives, without an independent forcing,
\[
 \boxed{\quad
 E_{xx}+\left(\frac2x+\frac{ikx}{2}\right)E_x+zE=G,
 \qquad E(1)=E_x(1)=0.
 \quad}\tag{M1}
\]
Thus the effective Kummer scale is **a/L**, not a. The interval
\(J=[1/2,1]\) is independent of the physical radius and of its parameters.
The right side is the exact original operator applied to the same field,
not a newly chosen source envelope. For the actual inner/spectral field,
substitute the previously derived identity
\[
 K_{a,Q}(u-v)=D_{\rm inner}+a^{-2}\delta u_0(y/a).
\]

The Lean theorem
`actual_Hartree_original_moving_radius_operator_pullback`
proves the literal identity in (M1), and
`actual_Hartree_original_moving_radius_zero_jet_pullback`
proves its endpoint transformation. Their types retain explicit
classical differentiability assumptions; they are not existence theorems.

## 2. A quantitative inverse with constants 2, 4, 18

Use the already established genuine radial weak-term absorption theorem
on the **fixed** interval J, with R=1/2 and r0=1. Provided
\[
 4k(1+|Q|)\le1,
\]
it gives, for the actual source G,
\[
 \boxed{\quad
 \|E\|_{L^\infty(J)}\le2\|G\|_\infty,\qquad
 \|E_x\|_\infty\le4\|G\|_\infty,\qquad
 \|E_{xx}\|_\infty\le18\|G\|_\infty.
 \quad}\tag{M2}
\]
For the last constant, use the source-produced bound
\(\|E_{xx}+2E_x/x\|_\infty\le2\|G\|_\infty\)
and \(2/x\le4\) on J. In particular, no unproved inverse norm or
moving-radius power is hidden in these constants. The smallness condition
is explicit and has not been deduced from the final nonlinear trajectory.

For two original profiles at possibly different physical radii L1,L2,
pull both to J. Set
\[
 k_j=L_j^2/a_j^2,\quad z_j=k_jQ_j,\quad
 G_j(x)=L_j^2(K_{a_j,Q_j}e_j)(L_jx),\quad E_j(x)=e_j(L_jx).
\]
Assume the displayed weak-term condition for each j. The difference
D=E1-E2 has zero endpoint jets and satisfies the **exact** equation
\[
 K_{k_1,z_1}D
 =G_1-G_2-\frac{ix}{2}(k_1-k_2)(E_2)_x-(z_1-z_2)E_2.
\tag{M3}
\]
Here K on the left denotes the normalized expression in (M1).
By (M2) for E2, define the actual quantity
\[
 B:=\|G_1-G_2\|_\infty
  +2\bigl(|k_1-k_2|+|z_1-z_2|\bigr)\|G_2\|_\infty.
\]
The forcing in (M3) is bounded by B, so the same inverse gives
\[
 \boxed{\quad
 \|E_1-E_2\|_\infty\le2B,\quad
 \|(E_1-E_2)_x\|_\infty\le4B,\quad
 \|(E_1-E_2)_{xx}\|_\infty\le18B.
 \quad}\tag{M4}
\]
The companion theorem
`actual_Hartree_normalized_original_source_C2_stability`
uses literal suprema of the original operator evaluations as its source
sizes. There are no independently postulated source majorants or
parameter-Lipschitz assumptions. This is a nontrivial local inverse
estimate, but it does **not** yet estimate the genuine nonlinear source
G1-G2 from the PDE parameters.

## 3. The material derivative which must not be discarded

For a differentiable parameter s and a sufficiently regular *actual*
family, the endpoint conditions hold identically in s after normalization.
With E=E(s,x), G=G(s,x), k=k(s), z=z(s), differentiation of (M1) gives
\[
 K_{k,z}E_s=G_s-\frac{ix}{2}k_sE_x-z_sE,
 \qquad E_s(s,1)=(E_s)_x(s,1)=0.
\tag{M5}
\]
This uses no derivatives of a selected Kummer fundamental basis.
The source is nevertheless the genuine material derivative
\[
 \boxed{\quad
 G_s(s,x)=2L L_s f(s,Lx)
       +L^2\bigl[f_s(s,Lx)+L_s x f_y(s,Lx)\bigr],
 \qquad f=K_{a,Q}e.
 \quad}\tag{M6}
\]
The transport term L_s x f_y is essential. It is not provided by a
fixed-radius parameter-difference identity. In particular replacing G_s
by L^2 f_s silently changes the equation.

Whenever these derivatives exist and are continuous, (M2), applied to
(M5), yields
\[
 \|E_s\|_\infty\le2B_s,\quad
 \|(E_s)_x\|_\infty\le4B_s,\quad
 \|(E_s)_{xx}\|_\infty\le18B_s,
\quad
 B_s=\|G_s\|_\infty+2(|k_s|+|z_s|)\|G\|_\infty.
\tag{M7}
\]
No claim that B_s has a positive time order is made. At fixed physical y,
\[
 e_s(s,y)=E_s(s,y/L)-\frac{L_s}{L}\frac yL E_x(s,y/L),
\]
\[
 (e_s)_y(s,y)=\frac1L(E_s)_x(s,y/L)
  -\frac{L_s}{L^2}\left[E_x(s,y/L)+\frac yL E_{xx}(s,y/L)\right].
\tag{M8}
\]
Consequently the explicit physical bounds are
\[
 \|e_s\|_{L^\infty([L/2,L])}
 \le2B_s+4|L_s|\|G\|_\infty/L,
\quad
 \|(e_s)_y\|_{L^\infty([L/2,L])}
 \le4B_s/L+22|L_s|\|G\|_\infty/L^2.
\tag{M9}
\]
Equations (M5)--(M9) are paper statements under the stated joint
regularity. They are not among the strict Lean targets of the initial
normalized-radius workflow.

## 4. What this removes, and the remaining physical test

The previous need to repeatedly differentiate and re-estimate a moving
Kummer basis is replaced, on this one backward overlap, by (M1)--(M4).
But the original full source must still produce the actual norms
G, G1-G2 and the material G_s, with the unique physical selection and all
nonlocal cross terms, and must be joined to the outer and core regions.
The full Hartree evolution inverse, finite residual recurrence and
nonlinear modulation trajectory are not consequences of (M4).

In particular the already verified normalized annular energy estimate
\(\int_{L/a}^B r^2|w'(r)|^2dr\le(B-L/a)E_{\rm full}^2\)
transforms for the physical pullback w(y/a) as
\[
 \int_L^{aB}y^2\left|\partial_y w(y/a)\right|^2dy
 =a\int_{L/a}^B r^2|w'(r)|^2dr.
\tag{M10}
\]
Therefore a normalized energy certificate is **not** automatically a
uniform physical energy certificate: the factor a, or sqrt(a) in the
norm, must be paid by the same physical source. This is an explicit
remaining scale budget, not evidence of a false theorem.

**Formal original acceptance remains 11/13.** No auxiliary declaration
in this note changes the count. Record exact CI, theorem types and
transitive axioms only after their actual successful execution.
