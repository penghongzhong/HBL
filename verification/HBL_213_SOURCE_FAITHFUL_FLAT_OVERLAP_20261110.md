# HBL §2.13: source-faithful smooth-overlap alternative to point-jet C² repair

**10 November 2026.** A mathematical construction and exact commutator
identity, **not** a Lean theorem or original-paper acceptance.
The previously proved three C¹ interfaces and original finite PDE
telescoping remain valid, but do not yield the physically required
weighted derivative norm. Original count **11/13**.

## 1. Why the naive second-jet repair is not yet a controlled PDE step

The literal affine repair in
\`ActualHartreeSpectralCorrectedFourPieceThreeC1.lean\` has
\([U_{yy}]_{aB}=-a^{-2}w''(B)\). The quadratic curvature repair
constructed in the accompanying paper note matches this jet
*algebraically*. However, the original source only belongs to
weighted \(L^2_{7/4}\). This does not bound \(F(B)\): the fixed-radius
bumps \(F_\epsilon(r)=\epsilon^{-1/2}\phi((r-B)/\epsilon)\)
have bounded \(L^2_{7/4}\) but \(F_\epsilon(B)\to\infty\).
The exact genuine corrected spectral equation expresses
\(w''(B)\) in terms of this trace and the source-dependent Green
values/slopes. No numerical C² repair budget follows from its
algebraic endpoint matching alone.

We can instead eliminate *both* artificial derivative interfaces
by using a **flat smooth overlap**, without introducing an
independent second-jet datum or point-source trace.

## 2. Exact geometry in the original physical coordinate

Assume the actual original geometric input
\[
 0<L<aB,\qquad a>0,\qquad 0<L/a<B<\mathrm{scale},
 \quad D=aB-L>0,\quad h=D/8.
\]
Use the **existing fixed \(C^\infty\) cutoff**
\(c(z)=\mathrm{cutoff}(z)\), with \(c(z)=0\) on \(z\le1\)
and \(c(z)=1\) on \(z\ge2\). Define
\[
 \eta(y)=c((y-L-h)/h),\qquad
 \chi(y)=1-c((y-(aB-4h))/h).
\tag{S1}
\]
Then, purely by the literal cutoff definition,
\[
 \begin{array}{rcl}
 \eta=0&\text{on}& y\le L+2h,\\
 \eta=1&\text{on}& y\ge L+3h,\\
 \chi=1&\text{on}& y\le aB-3h=L+5h,\\
 \chi=0&\text{on}& y\ge aB-2h=L+6h.
 \end{array}
\tag{S2}
\]
Thus the inner transition lies in \([L+2h,L+3h]\)
and the outer transition lies in \([L+5h,L+6h]\);
they are strictly disjoint and both lie in \((L,aB)\).
At every point where the Kummer field is used nontrivially,
\(y/a<B<\mathrm{scale}\): no **unproved continuation to
\(2B\)** is required.

Set \(u(y)=\) the actual original two-channel Fredholm inner field,
\(v(y)=w(y/a)\), where \(w\) is the **same-source, true selected,
spectral-corrected** original Kummer solution, and
\[
 W(y)=\chi(y)v(y),\qquad
 \boxed{U(y)=(1-\eta(y))u(y)+\eta(y)W(y).}
\tag{S3}
\]
Then the formula is identically \(u\) on \(y\le L+2h\),
identically \(v\) on \([L+3h,L+5h]\), and identically
zero for \(y\ge L+6h\). If \(u\) and \(v\) are \(C^k\)
on their respective original interiors, \(U\) has no
new artificial jumps at either transition, for any
\(k\le\) their actual interior regularity. In particular,
this architecture does **not** ask for the pointwise number
\(w''(B)\) as an added interface datum.

**Important:** the currently available
\(\mathrm{InWeightedL2}(7/4)\) hypotheses do not establish
global \(C^2\)/\(H^3\) regularity of both genuine fields.
When \(u\) is merely \(H^2_{\rm loc}\), (S3) is a
\(H^2_{\rm loc}\) splice, not automatically \(H^3\).
The weighted derivative source estimate remains a real
regularity and nonlinear-PDE task.

## 3. Exact second-order commutator; no source cancellation is assumed

For the same frozen radial differential expression
\(\mathcal L_0 f=f''+c_1(y)f'+c_0(y)f\), write
\(\eta,\chi\) for the physical cutoffs (S1) and
\(W=\chi v\). The complete, **algebraically exact**
product rule on the smooth interiors is
\[
\begin{aligned}
\mathcal L_0U={}&
 (1-\eta)\mathcal L_0u+\eta\chi\mathcal L_0v\\
 &+2\eta'(W'-u')+(\eta''+c_1\eta')(W-u)\\
 &+\eta\bigl[2\chi'v'+(\chi''+c_1\chi')v\bigr].
\end{aligned}
\tag{S4}
\]
Consequently the commutator depends on actual *field and first
derivative mismatches*, rather than artificially prescribed
endpoint curvatures. No \(w''(B)\) or \(F(B)\) is sampled to
construct the field. The derivatives of \(\eta,\chi\) obey
\[
 \|\partial_y^j\eta\|_\infty+
 \|\partial_y^j\chi\|_\infty
 \le 2C_jh^{-j},\quad j=1,2,3,
\tag{S5}
\]
with \(C_j\) derived from the already available genuine smooth
cutoff. The explicit denominator
\(h^{-j}=8^j(aB-L)^{-j}\) must be carried into source
estimates: this scheme must **not** silently claim
uniform bounds as \(aB-L\to0\).

For time-dependent \(L,a,B\), including \(B\) if permitted,
the full time/transport operation
\(T_b=\partial_s+b\,y\partial_y\) gives
\[
\begin{aligned}
 T_bU={}& (1-\eta)T_bu+\eta\chi T_bv\\
 &+(T_b\eta)(W-u)+\eta(T_b\chi)v.
\end{aligned}
\tag{S6}
\]
Together, (S4) and (S6) retain the actual moving-cutoff
material derivative; the complete nonlocal term must be
evaluated as \(\mathcal N_{\rm H}(U)\), *not* as a linear
combination of \(\mathcal N_{\rm H}(u)\) and
\(\mathcal N_{\rm H}(v)\). If one decomposes it for a
telescoping estimate, the exact nonlinear cross-density
\[
 \mathcal N_{\rm H}(U)
 -(1-\eta)\mathcal N_{\rm H}(u)
 -\eta\chi\mathcal N_{\rm H}(v)
\tag{S7}
\]
must remain in the source and be bounded from the same
physical three-dimensional Riesz convolution.

At the level of an \(H^1\) residual, differentiating
(S4) uses \(u'',v''\) and up to \(\eta''',\chi'''\).
A genuine local \(H^3\) or source \(H^1\) estimate is still
needed. The construction removes **uncontrolled boundary
point traces**, not the underlying PDE regularity requirement.

## 4. Strict next acceptance gate

The economically shortest possible replacement of the original
piecewise three-\(C^1\) outer matching is:

\[
\begin{gathered}
 \text{same actual Hartree two-channel source + Cramer selector}\\
 \downarrow\\
 \text{existing true Fredholm and spectral Green fields
       in the overlapping domain}\\
 \downarrow\\
 \text{flat two-cutoff field (S3), geometry (S2)
       and exact commutators (S4),(S6)}\\
 \downarrow\quad\boxed{\text{OPEN: local physical source }H^1
                   \text{ and all radius/motion derivative budgets}}\\
 \text{OPEN: all four-region nonlinear Hartree source
       in projected smoothing-dual space}\\
 \downarrow\\
 \text{OPEN: actual Hartree adjoint Kato / nonresonant stable inverse}\\
 \downarrow\\
 \text{OPEN: real PDE orbit, Lipschitz recursion, emergent II rate}.
\end{gathered}
\]

This scheme avoids an *extra* second-jet trace
\(w''(B)\), but it may or may not be preferable to the
quadratic repair if the forced physical source already
has a strong point trace. Select based on a **quantitative
physical source comparison**, not on the mere existence of
a C² endpoint identity.

**No new \`#check\`, no independent Lean CI and no revised-original
environment acceptance are claimed for (S1)–(S7). The original
acceptance remains exactly 11/13.**
