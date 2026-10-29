# HBL: correction of the actual slow-monopole source (2026-10-30)

Main theorem and original manuscript one-layer proposition 2.12 remain OPEN.
Historical original manuscript strict acceptance remains 9/21.

## Original definition, not an external parameter

From the October 27 manuscript, lines 2525–2552:

\[
m_0[z]=\int_{\mathbb R^3}|x|^{-2}|z(x)|^4 dx,\qquad
c_g(s)=\kappa_H\lambda(s)^{-1}m_0[z_g(t(s))].
\]

For a radial complex radiation field, polar integration yields
\(m_0[z]=4\pi\int_0^\infty|z(\rho)|^4d\rho\).
Set \(\ell=\lambda^{-1}>0\), \(Z_\ell(r)=\sqrt{\ell}\,e^{-i\gamma}z(\ell r)\).
Then the TRUE full-radiation Hartree center obeys

\[
C[Z_\ell]=4\pi\kappa_H\int_0^\infty|Z_\ell(r)|^4dr
=\kappa_H\ell\,m_0[z]=c_g(s).
\]

This is an exact change of variables, not a prescribed limit or a blowup
rate hypothesis. The original physical time identity is

\[
(c_g)_s=-b\,c_g+\kappa_H\ell^3\,\partial_t m_0[z_g].
\]

The previously certified physical radial center theorem gives
\(P(|Z_\ell|^4)(r)=c_g+O(r^2)\) under primitive boundedness, finite radial
mass, and quadratic flatness of the radiation amplitude. The new Lean
candidates in the TypeIIDynamicSelection directory verify the center,
physical scaling, and actual moment derivative. Count them only after
strict source compilation, full types and transitive axioms pass.

## A critical correction to the preceding remote-matching interpretation

The earlier certified exterior-only Riesz lemmas are valid conditional
theorems for a radiation *cutoff piece supported beyond a moving radius*.
However, the original c_g is the self-potential of ALL regular radiation.
No proof establishes that all its density lies outside R_c=4/|c_g|,
and no such support property should be imposed on a true Hartree orbit.

Consequently the equality of c_g to the exterior cross-density mass
is NOT an established physical matching condition. It must not replace
the original whole-radiation c_g. The correct leading slow source is
the self-radiation Hartree quartic center plus its O(r²) remainder,
together with the mixed bubble/radiation nonlocal interactions and
the independent regular center jet A_g.

## Actual pending PDE-to-rate proof chain

(1) Verify full-radiation center and exact c_g scaling/time-derivative.
(2) Derive the complete first physical Hartree source including mixed
A_g and c_g terms; prove actual generated time orders.
(3) Instantiate the physical two-channel Fredholm and true origin-gauge
Kummer/remote inverses in original 2.12 with matched overlap data.
(4) Close finite profile 2.13, actual constrained evolution, nonlinear
fixed point and one exact radial type-II Hartree orbit.
(5) Derive the selected modulation limit and physical blowup rate
FROM the constructed orbit, not from prescribed infinity data.

No new original theorem environment is claimed by this correction.
