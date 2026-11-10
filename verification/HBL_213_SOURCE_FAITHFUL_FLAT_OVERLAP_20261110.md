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

## 2. Corrected geometry: keep the inner transition on the ORIGINAL backward overlap [L/2,L]

A source audit of \`actual_Hartree_moment_locked_pullback_actual_inner_jet\`
in \`ActualHartreeMomentLockedKummerPullback.lean\` proves equality
of the actual Fredholm and same-source Kummer **value and slope at y=L**
and explicitly identifies the available backward shell
\([L/2,L]\). The originally proposed transition
\([L+2h,L+3h]\), with \(h=(aB-L)/8\), improperly demands
Fredholm inner *physical estimates to the right of L*, where
the inner region has not been justified. It is therefore **withdrawn**:
the mere fact that the inner formula is defined globally does
not validate its approximation estimates there.

For the original physical geometry
\[
 0<L<aB,\quad a>0,\quad 0<L/a<B<\mathrm{scale},\quad
 h_{\rm in}=L/8,\quad h_{\rm out}=(aB-L)/8,
\]
use the SAME fixed smooth cutoff \(c\) and set instead
\[
 \boxed{\begin{aligned}
 \eta(y)&=c\left(\frac{y-L+4h_{\rm in}}{h_{\rm in}}\right),\\
 \chi(y)&=1-c\left(\frac{y-aB+4h_{\rm out}}{h_{\rm out}}\right),\\
 U(y)&=(1-\eta(y))u(y)+\eta(y)\chi(y)v(y).
 \end{aligned}}\tag{S1'}
\]
Here \(u\) is the genuine Fredholm inner field and \(v=w(y/a)\)
is the same true source-selected, spectral-corrected Kummer field
already verified on \(0<y<a\,\mathrm{scale}\), including **to the
left of** \(y=L\). Their first two matching traces at L are
not inserted as free data.

Because \(c=0\) below \(1\) and \(c=1\) above \(2\),
\[
 \begin{array}{rcl}
 \eta=0&\text{on}&y\le L-3h_{\rm in}=5L/8,\\
 \eta=1&\text{on}&y\ge L-2h_{\rm in}=3L/4,\\
 \chi=1&\text{on}&y\le aB-3h_{\rm out}=L+5h_{\rm out},\\
 \chi=0&\text{on}&y\ge aB-2h_{\rm out}=L+6h_{\rm out}.
 \end{array}\tag{S2'}
\]
The two transition intervals are now
\[
 I_{\rm in}=[5L/8,\,3L/4]\subset[L/2,L],\qquad
 I_{\rm out}=[L+5h_{\rm out},\,L+6h_{\rm out}]
            \subset(L,aB).
\]
Thus the genuine inner profile is needed only where its
physical approximation is actually intended,
the Kummer field is evaluated only in its proven
positive domain, and the original spectral upper endpoint B
is not crossed. The field is identically \(u\) before
\(I_{\rm in}\), identically \(v\) on the long middle plateau,
and zero after \(I_{\rm out}\), with no artificial interface
curvature or point evaluation \(F(B)\).

This corrected construction exposes BOTH true geometric
denominators \(h_{\rm in}^{-j}=(8/L)^j\) and
\(h_{\rm out}^{-j}=(8/(aB-L))^j\); it does not
silently hide a dependency on L or on \(aB-L\).
The still-open issue is whether the genuine source and
physical spectral profile have sufficient regularity and
a small enough \emph{actual} mismatch on the backward
shell. The pre-existing weighted \(L^2\) assumptions do
not themselves furnish a time-decaying nonlinear residual.

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
 \|\partial_y^j\eta\|_\infty\le C_jh_{\rm in}^{-j},
 \qquad
 \|\partial_y^j\chi\|_\infty\le C_jh_{\rm out}^{-j},
 \quad j=1,2,3,
\tag{S5'}
\]
where the fixed constants \(C_j\) come from the genuine
already established smooth cutoff. Both
\(h_{\rm in}^{-j}=8^jL^{-j}\) and
\(h_{\rm out}^{-j}=8^j(aB-L)^{-j}\)
are retained in all source estimates.

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

At the level of a spatial \(H^1\) commutator, differentiating
(S4) uses only the actual \(u'',v''\) and up to
\(\eta''',\chi'''\); no third derivative of \(u,v\)
occurs in these *cutoff commutators*. Derivatives of the
unlocalized original PDE sources, however, still require
their own legitimate local Sobolev control. The construction removes **uncontrolled boundary
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
 \text{flat two-cutoff field (S1'), geometry (S2')
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



## 5. Quantitative inner-glue estimate from the **already-proved** true zero C¹ jet

The proof \`actual_Hartree_moment_locked_pullback_actual_inner_jet\`
produces \(e(L)=e'(L)=0\) for the genuine difference
\(e=u-v\). Under the additional, **not yet certified on
the full nonlinear PDE orbit**, local \(e\in H^2([L/2,L])\),
let \(E=\|e''\|_{L^2([L/2,L])}\).
The one-dimensional fundamental theorem of calculus gives
for every \(y\in[L/2,L]\)
\[
 e'(y)=-\int_y^L e''(t)\,dt,\qquad
 e(y)=\int_y^L(t-y)e''(t)\,dt ,
\]
hence, by Cauchy--Schwarz,
\[
 |e'(y)|\le\sqrt{L-y}\,E,\qquad
 |e(y)|\le\frac{(L-y)^{3/2}}{\sqrt3}\,E .
 \tag{S8}
\]
On the ACTUAL backward inner transition
\(I_{\rm in}=[L-3h,L-2h]\), \(h=h_{\rm in}=L/8\),
\[
 \sup_{I_{\rm in}}|e'|\le\sqrt{3h}\,E,\qquad
 \sup_{I_{\rm in}}|e|\le3h^{3/2}E .
 \tag{S9}
\]
Since \(\chi\equiv1\) on this interval, the **complete
linear inner cutoff commutator**, without dropping the drift,
is exactly
\[
 \mathcal C_{\rm in}
 =-2\eta'e'-(\eta''+c_1\eta')e
\]
with \(c_1\) the original physical first-derivative
coefficient. Let \(M_0=\sup_{I_{\rm in}}|c_1|\)
and \(M_1=\sup_{I_{\rm in}}|c_1'|\), keeping their true
physical parameter dependence explicit. If
\(\|\eta^{(j)}\|_\infty\le C_jh^{-j}\), then
(S9) and the exact transition length \(h\) imply
\[
 \boxed{\quad
 \|\mathcal C_{\rm in}\|_{L^2(I_{\rm in})}
 \le\bigl[2\sqrt3 C_1+3C_2+3C_1M_0h\bigr]E .
 \quad}\tag{S10}
\]
This is an important structural saving: matching the **genuine**
zero value and slope at L cancels the naive \(h^{-2}\)
commutator amplification. The resulting unweighted
\(L^2\) estimate costs no negative power of \(h\).

One further spatial derivative, requiring only the same
\(e''\in L^2\) (not \(e'''\)), yields the *exact*
\[
 \begin{aligned}
 -\partial_y\mathcal C_{\rm in}
 ={}&2\eta'e''+3\eta''e'+\eta'''e
  +c_1\eta'e'+(c_1'\eta'+c_1\eta'')e .
 \end{aligned}
\]
Consequently
\[
 \boxed{\begin{aligned}
 \|\partial_y\mathcal C_{\rm in}\|_{L^2(I_{\rm in})}
 \le\biggl[
   \frac{2C_1+3\sqrt3 C_2+3C_3}{h}
   +(\sqrt3C_1+3C_2)M_0
   +3C_1M_1h\biggr] E .
 \end{aligned}}\tag{S11}
\]
In a weighted target,
multiply the RHS by the *actual maximum*
of the weight over the moving interval, rather than
writing \(O(1)\) for the entire radial range.
Both (S10) and (S11) are paper deductions from
same-source zero-jet matching, with **one concrete
remaining producer**: estimate \(E=\|u''-v''\|_{L^2}\)
from the true two-region Hartree PDE sources and
tracked physical coefficients. A bound on \(E\)
is not supplied by the previous \(C^1\) Lean proof
alone, and no decay exponent is asserted here.
The outer cutoff and complete nonlocal quartic
Hartree interaction must still be bounded independently.

This corrected backward-overlap route is substantially
more economical than the invalid forward-inner-overlap
construction. It also avoids needing the source trace
\(F(B)\) just to define a globally smooth profile.
**No original-environment gain: 11/13.**


## 6. Exact physical PDE producer of the inner mismatch curvature

The \(E\) in (S8)--(S11) need not remain an abstract
independently bounded packet: it can be expressed using **the
two actual, previously formalized Hartree PDE equations**.
The original source declarations are
\`actual_Hartree_moment_locked_inner_physical_equations\`
in \`ActualHartreeMomentLockedInnerClassical.lean\`,
and \`actual_Hartree_matched_spectral_original_physical_source\`
in \`ActualHartreeMatchedSpectralOriginalPDEMismatch.lean\`.
Importantly, the latter is the **unshifted ORIGINAL**
Kummer/PDE source \(F-\delta u_0\), rather than the
quadratic source arising from a shifted spectral operator.

To avoid silently changing the source, fix the same physical
moment-locked parameters \((R,c)\) used in the first theorem,
and define the physical Fredholm component fields
\[
 U_{\rm re}(y)=q_\omega(y)/y,\qquad
 U_{\rm im}(y)=q_b(y)/y,\qquad
 u=U_{\rm re}+iU_{\rm im}.
\]
Here the same true Fredholm responses
\(q_\omega,q_b\) and their source cutoff
\(\chi_R(y)=\mathrm{actualHartreeInnerSourceCutoff}(R,y)\)
are used; **do not confuse this \(R\) with the later
Cramer overlap radius B**. Let
\[
 S_{\rm re}(y)=\chi_R(y)\,
   \mathrm{actualMomentLockedCore}(c,y),\qquad
 S_{\rm im}(y)=\chi_R(y)\,
   \mathrm{actualMomentLockedScaleProfile}(c,y).
\]
Set \(W(y)=(1+y^2)^{-1/2}\) and
\(\mathcal I f=\kappa_{\rm H}(|x|^{-2}*f)\)
with the actual original coupling.
Then the two exact physical inner Hartree equations give
\[
 \begin{aligned}
 u''+\frac2y u'={}&
 -S_{\rm re}-iS_{\rm im}
 -9W^4 U_{\rm re}-3iW^4 U_{\rm im}\\
 &-4W^3\mathcal I(W^3 U_{\rm re}).
 \end{aligned}\tag{S12}
\]
The nonlocal integral cannot be omitted. For the
**same-original-source selected Kummer** field
\(v(y)=w(y/a)\), where \(u_0\) is the
original matched Green value before the spectral correction,
the previously proved physical source identity gives
\[
 v''+\frac2y v'
 =a^{-2}\{F(y/a)-\delta\,u_0(y/a)\}
 -a^{-2}\left\{\frac{iy}{2}v'(y)+c_0v(y)\right\},
 \qquad c_0=\mathrm{frozenZeroCoeff}(\mu,\theta).
 \tag{S13}
\]
Both displays hold on the physically admissible smooth
positive-radius domains of their actual source theorems.
**Notice the FIRST-order \(-\delta u_0\) error.**
The shifted-spectral quadratic estimate cannot erase it
from the original unshifted Hartree PDE.

For the true backward-overlap mismatch \(e=u-v\),
(S12)--(S13) yield the **exact same-orbit curvature identity**
\[
 \boxed{\begin{aligned}
 e''={}&-\frac2y e'
  -S_{\rm re}-iS_{\rm im}
  -9W^4U_{\rm re}-3iW^4U_{\rm im}
  -4W^3\mathcal I(W^3U_{\rm re})\\
 &-a^{-2}\{F(y/a)-\delta\,u_0(y/a)\}
  +a^{-2}\left\{\frac{iy}{2}v'(y)+c_0v(y)\right\}.
 \end{aligned}}\tag{S14}
\]
This is a real physical source identity (not an
independently assumed mismatch envelope), so it
reduces \(E=\|e''\|_{L^2([L/2,L];dy)}\) to the
explicit \(L^2\) norms of the **exact** seven displayed
source/coefficient groups. Under genuine integrability,
the triangle inequality gives
\[
 \begin{aligned}
 E\le{}&
 \|2e'/y\|_{L^2(I)}
 +\|S_{\rm re}+iS_{\rm im}\|_{L^2(I)}
 +9\|W^4U_{\rm re}\|_{L^2(I)}
 +3\|W^4U_{\rm im}\|_{L^2(I)}\\
 &+4\|W^3\mathcal I(W^3U_{\rm re})\|_{L^2(I)}
 +a^{-2}\|F(\cdot/a)-\delta u_0(\cdot/a)\|_{L^2(I)}\\
 &+a^{-2}\|iyv'/2+c_0v\|_{L^2(I)},
 \qquad I=[L/2,L].
 \end{aligned}\tag{S15}
\]
The **unclosed gate is now quantitative**: prove that
the RHS on the actual moving scales is small enough,
including its selected-speed derivative and parameter
Lipschitz dependence, for the physical finite
recursion. Previous Volterra/Cramer bounds control
some terms but not their full common moving and
nonlocal nonlinear source norm. Equation (S14)
does not itself yield any \(s^{-\nu}\) gain: the
genuine rate of the RHS must be established.
It also does not provide an adjoint Kato estimate
for the full coupled Hartree Hamiltonian.

This exact deduction is at the **paper level**; no new
strict Lean theorem or original environment has been
certified for (S14)--(S15). **11/13**.
