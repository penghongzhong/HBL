# Revised HBL 2.13 — shortest full physical interaction weighted-source bridge (candidate)

Status: **mathematical reduction only, not an accepted Lean theorem**. Do not increment revised 11/13 or claim the existence of a Type-II orbit. This note specifies the next exact Lean statement and its three remaining scalar inequalities.

## Original PDE source and independent verified inputs

For the actual inverse-square 3D generalized Hartree nonlinearity, let
\[
I_2[f]=\kappa_H(|x|^{-2}*f),\qquad C(u)=|u|^2u,\qquad
F=I_2[|V+Z|^4]C(V+Z)-I_2[|V|^4]C(V)-I_2[|Z|^4]C(Z).
\]
The existing exact source-splitting lemma gives, *without modifying the PDE*,
\[
F=P_m C(V)+P_m(C(V+Z)-C(V))
 +P_z(C(V+Z)-C(Z))+P_c(C(V+Z)-C(V)),
\]
where \(P_m=I_2[|V+Z|^4-|V|^4-|Z|^4]\), \(P_c=I_2[|V|^4]\), and \(P_z=I_2[|Z|^4]\).
The complex cubic Lipschitz estimate is already in
`ActualHartreeComplexCubicLipschitz.lean`.

Let \(0<\ell\le1\), \(r\ge0\), \(d=1+r\), \(q=1+\ell r\), so
\[
1\le q\le d,\qquad \ell d\le q,\qquad d\ge1.
\]
The actual Strauss/monopole envelopes and the **already strictly accepted** mixed potential estimate yield
\[
|V(r)|\le D/d,\quad |Z(r)|\le E\sqrt\ell/q,\quad
|P_m(r)|\le C_m\sqrt\ell/d.
\]
The two new strict-audit *candidates* supply the remaining spatial estimates
\[
|P_c(r)|\le C_c/d,\qquad |P_z(r)|\le C_z\ell/q.
\]
Neither of these last two inequalities should be treated as formally accepted until the respective strict CI completes successfully.

## Only three scalar inequalities remain after expansion

From \(|C(u)-C(v)|\le(|u|+|v|)^2|u-v|\) and \(|V+Z|\le|V|+|Z|\),
\[
|F|\le |P_m|\{v^3+(2v+z)^2z\}
       +|P_z|(v+2z)^2v
       +|P_c|(2v+z)^2z,
\qquad v=|V|,\ z=|Z|.
\]
At weight \(\sigma=7/4\), all ten resulting monomials are bounded, up to a polynomial in the *derived positive constants* \(D,E,C_m,C_z,C_c\), by one of
\[
A_1=\ell^{1/2}d^{-5/4}q^{-1},\qquad
A_2=\ell d^{-1/4}q^{-2},\qquad
A_3=\ell^{3/2}d^{3/4}q^{-3}.
\]
Indeed \(q\le d\) and \(\ell^2\le\ell^{3/2}\) reduce the mixed/pure terms to these three core-type envelopes. The three required *unconditional scalar* bounds are
\[
A_1\le\ell^{1/8}d^{-5/8},\qquad
A_2\le\ell^{1/8}d^{-5/8},\qquad
A_3\le\ell^{1/8}d^{-5/8}.
\]
The first follows from \(\ell\le1\), \(d,q\ge1\).
For the second, use \(q^2\ge q^{7/8}\ge(\ell d)^{7/8}\ge\ell^{7/8}d^{3/8}\).
For the third, use \(q^3\ge q^{11/8}\ge(\ell d)^{11/8}\).
Hence the target physical source estimate is
\[
(1+r)^{7/4}|F(r)|\le C(D,E,C_m,C_z,C_c)\ell^{1/8}(1+r)^{-5/8}.
\]
The original Japanese weight satisfies \(\langle r\rangle^{7/4}\le (1+r)^{7/4}\) on \(r\ge0\).
Finally, since
\[
\int_0^\infty (1+r)^{-5/4}\,dr=4,
\]
the intended **full Hartree nonlinear interaction** conclusion is
\[
\|F\|_{L^{2,7/4}(0,\infty)}
\le 2 C(D,E,C_m,C_z,C_c)\ell^{1/8}.
\]

## Remaining obligations before accepting revised 2.13

1. Strictly audit both new core/pure spatial potentials and the resulting full ten-monomial weighted-L2 theorem, including exact measurability and source norms.
2. Apply the *same physical PDE source* to the original H+/H- Fredholm, origin-normalized Kummer and true remote inverse with quantitative interface C1 compatibility (or a proved coupled alternative).
3. Prove all generated cutoff, phase/parameter, Frobenius, slow-monopole and nonlocal source classes have uniform **time** positive order along the true selected solution. Length \(\ell^{1/8}\) by itself is not a prescribed decay \(s^{-\kappa}\).
4. Invoke the already compiled finite-profile recursion only after the physical source-to-packet map and the noncircular trapping/dynamics input have been justified; derive, never assume, the Type-II concentration exponent.

The exact original manuscript finite-profile environment and the final PDE-dynamical-rate theorem remain OPEN. Revised acceptance: **11/13**.
