# HBL 2.13 — explicit algebraic source ledger (mathematical reduction, not yet accepted as complete PDE theorem)

For the genuine 3D inverse-square quartic generalized-Hartree nonlinearity, define
\[
C(u)=|u|^2u,\quad
P_c=I_2[|V|^4],\quad
P_z=I_2[|Z|^4],\quad
P_m=I_2[|V+Z|^4-|V|^4-|Z|^4].
\]
The already strictly checked source decomposition is
\[
F=P_m C(V)+P_m(C(V+Z)-C(V))
  +P_z(C(V+Z)-C(Z))+P_c(C(V+Z)-C(V)).
\]
Let \(d=1+r\), \(q=1+\ell r\), \(0<\ell\le1\), \(r\ge0\). The intended prerequisites, **with distinct statuses**, are:
\[
|V|\le D/d,\quad |Z|\le E\sqrt\ell/q,\quad
|P_m|\le C_m\sqrt\ell/d\quad(\text{strictly accepted});
\]
\[
|P_c|\le C_c/d,\quad
|P_z|\le C_z\ell/q\quad(\text{separate Lean candidates, NOT accepted pending CI}).
\]
Here \(D,E,C_m,C_c,C_z\ge0\) depend only on separately specified physical radial/Strauss bounds and the radial-kernel constants, not on any **prescribed** Type-II exponent.

Set \(v=|V|,z=|Z|\). The complex cubic difference estimate yields the **exact upper bound**
\[
|F|\le |P_m|\{v^3+4v^2z+4vz^2+z^3\}
      +|P_z|\{v^3+4v^2z+4vz^2\}
      +|P_c|\{4v^2z+4vz^2+z^3\}.
\]
Its ten monomials reduce to precisely three scale envelopes
\[
A_1=\ell^{1/2}d^{-5/4}q^{-1},\quad
A_2=\ell d^{-1/4}q^{-2},\quad
A_3=\ell^{3/2}d^{3/4}q^{-3},
\]
with explicit nonnegative constants
\[
\begin{aligned}
K_1&=C_m D^3+4C_mD^2E+C_z D^3+4C_cD^2E,\\
K_2&=4C_mDE^2+4C_zD^2E+4C_cDE^2,\\
K_3&=C_m E^3+4C_zDE^2+C_c E^3.
\end{aligned}
\]
More precisely,
\[
d^{7/4}|F|\le K_1 A_1+K_2 A_2+K_3 A_3.
\]
To verify the comparison **without assigning a generated source order**, note
\[
1\le q\le d,\quad \ell d\le q,\quad
A_j\le\ell^{1/8}d^{-5/8}\quad(j=1,2,3).
\]
The three inequalities are now stated as an independent Lean theorem
`HBL.TypeIIDynamicSelection.actual_Hartree_three_Fredholm_scalar_envelopes`
in `ActualHartreeThreeFredholmEnvelopes.lean`, with strict CI pending.

Once that theorem, both core/pure Riesz decay candidates and the physical-to-envelope specialization are genuinely checked, one obtains the **candidate whole-interaction** estimate
\[
\langle r\rangle^{7/4}|F(r)|\le
(K_1+K_2+K_3)\ell^{1/8}(1+r)^{-5/8}.
\]
With \(\int_0^\infty(1+r)^{-5/4}\,dr=4\),
\[
\|F\|_{L^{2,7/4}(0,\infty)}
\le2(K_1+K_2+K_3)\ell^{1/8}.
\]
This is still *physical-length* smallness. It must not be reported as \(s^{-\kappa}\) without a **derived** modulation-time relation, nor as a matched finite Hartree profile.

## Current noncircular closure requirements

1. Pass independent strict Lean audits of core/pure spatial potentials and three scalar inequalities; formalize the ten-term source reduction and actual weighted integral.
2. Construct one same-source coupled inner Fredholm / origin-normalized Kummer / remote correction with genuine \(C^1\) interfacial matching. The exact two-endpoint transfer is already audited, but does **not** supply outer compatibility for free.
3. Prove the actual generated-term time order and transport/parameter/Frobenius estimates from that same physical PDE orbit before applying the existing abstract `finiteProfile_recursion_certified`.

No artificial `GeneratedTerm` order, assumed Type-II rate, new Lean axiom, or claim of full manuscript 2.13 acceptance is made. **Formal revised count remains 11/13.**
