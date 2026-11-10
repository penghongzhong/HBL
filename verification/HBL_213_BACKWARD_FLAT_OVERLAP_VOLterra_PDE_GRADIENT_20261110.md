# HBL §2.13 — SOURCE-FAITHFUL backward-Volterra control of the original flat-overlap PDE-gradient

**10 November 2026. Status:** a complete *paper-level conditional-on-actual-classical-source* estimate for **one physical inner backward transition**, obtained from already established source-to-PDE and same-physical-source plateau identities. It is **not** a new strict Lean theorem or a claim of the complete four-region nonlinear Hartree source, PDE orbit, or final Type-II rate. Formal original revised acceptance stays **11/13**.

## 1. Original, genuinely source-matched equation on [L/2,L]

Let \(L>4\), \(a>0\), and the original physical two-channel Fredholm inner field
\[
 u(y)=\mathrm{actualHartreeTwoChannelInner}(F_+,F_-)(y)
\]
and the **same-source spectrally corrected** Kummer field
\[
 v(y)=w(y/a),\qquad
 w(r)=u_0(r)-u_1(r),\quad
 \mathcal K u_0=F_o,\quad \mathcal K u_1=\delta u_0.
\]
Use the existing *original* Cramer/Fredholm matching interface:
\(u(L)=v(L)\), \(u'(L)=v'(L)\). These are strict previously verified
source-selected **C¹** identities; no independent boundary jet is
provided. Let \(e=u-v\).

The original scaled operator really is
\[
 \mathcal K_a f=f''+\left(\frac2y+\frac{iy}{2a^2}\right)f'
                 +\frac{Q}{a^2}f,\qquad
 Q=\mathrm{frozenZeroCoeff}(\mu,\theta).
 \tag{V1}
\]
By the **actual physical quartic Hartree plateau identity**, for
\(y\in[L/2,L]\) the two original source terms cancel
\[
 S_{\rm inner}(y)+a^{-2}F_o(y/a)=0.
\]
Writing the **existing actual Fredholm defect**
\[
 D_{\rm inner}=\mathcal K_a u+S_{\rm inner},
\]
the original corrected source equation gives **without an independent
forcing hypothesis**
\[
 \boxed{\ 
   \mathcal K_a e=f,\quad
   f(y)=D_{\rm inner}(y)+a^{-2}\delta u_0(y/a),
   \qquad e(L)=e'(L)=0 .
 \ }\tag{V2}
\]
The equation is an exact consequence of the original *same* Hartree
source and two real selection directions, assuming enough classical
continuity for the already published source identities and their
pointwise representatives. It is **not** a generic norm packet.

The strict \`actual_Hartree_two_channel_inner_Kummer_defect_bound\`
can be used at the **actual backward-shell base**
\(R=L/2>2\), for every \(y\in[L/2,L]\). For the true combined
two-channel source norm
\[
 N=\|F_+\|_{2,7/4}+\|F_-\|_{2,7/4}
\]
and its genuine fixed constants \(C_{\rm in}>0\),
\(C_K=|\mathrm{actualInnerShellKummerConstant}(\mu,\theta)|\),
the resulting pointwise forcing bound is
\[
 |f(y)|\le
 16C_{\rm in}L^{-4}N+
  a^{-2}\left(C_KN+|\delta||u_0(y/a)|\right).
 \tag{V3}
\]
Define the *actual*, not assumed, Green trace functional
\[
 M_0=\sup_{r\in[L/(2a),L/a]}|u_0(r)| .
\]
For continuous matched Green data \(M_0<\infty\), and existing
zero-left Volterra/Cramer bounds can be used to estimate it.
Writing \(E_f=\|f\|_{L^2(L/2,L;dy)}\), the exact interval length gives
\[
 \boxed{\ 
 E_f\le\sqrt{L/2}
 \left[16C_{\rm in}L^{-4}N+
 a^{-2}(C_KN+|\delta|M_0)\right].
 \ }\tag{V4}
\]
No point evaluation \(F_o(B)\), \(w''(B)\), or third derivative of
the original rough source is required anywhere in (V1)–(V4).

## 2. An explicit backward Gronwall inverse with no spectral assumption

Set \(h(y)=ye(y)\). The **exact** radial conjugation of (V2) is
\[
 h''+\frac{iy}{2a^2}h'
       +\frac{Q-i/2}{a^2}h=yf,\qquad
 h(L)=h'(L)=0.
 \tag{V5}
\]
For \(y\in I=[L/2,L]\), define
\(Z(y)=|h'(y)|+2|h(y)|/L\).
Absolute integration of the **true differential equation** from
\(L\) backward gives
\[
 Z(y)\le\int_y^L
 \left[t|f(t)|+\beta Z(t)\right]dt,
 \qquad
 \beta=\frac2L+\frac{L(|Q|+3/2)}{2a^2}.
 \tag{V6}
\]
Indeed \(|h'|\le Z\), \(|h|\le LZ/2\),
\(|iy/(2a^2)|\le L/(2a^2)\),
\(|(Q-i/2)/a^2|\le(|Q|+1/2)/a^2\);
the \(2/L\) term comes from differentiating the \(2|h|/L\)
portion of \(Z\) under the integral estimate.
Backward Volterra–Gronwall (not a dispersive Hartree
spectral theorem) therefore yields
\[
 \begin{gathered}
 Z(y)\le e^{\beta(L-y)}\int_y^Lt|f(t)|dt,\\
 M_{\rm V}:=\exp\left(1+\frac{(|Q|+3/2)L^2}{4a^2}\right),\\
 \boxed{\quad
 \sup_{y\in I}Z(y)
 \le \frac{M_{\rm V}L^{3/2}}{\sqrt2} E_f .
 \quad}\tag{V7}
 \end{gathered}
\]
In particular, since \(y\ge L/2\),
\[
 |e(y)|\le Z(y),\qquad
 |e'(y)|\le\frac4LZ(y).
 \tag{V8}
\]
Substituting these **derived** bounds back into (V2),
and using \(|2/y+iy/(2a^2)|\le4/L+L/(2a^2)\),
gives the complete actual \(H^2\) control
\[
\boxed{
 \begin{aligned}
 E:=\|e''\|_{L^2(I)}
 &\le C_E(L,a,Q) E_f,\\
 C_E(L,a,Q)
 &=1+M_{\rm V}\left[
       8+\frac{(|Q|+2)L^2}{2a^2}
    \right].
 \end{aligned}
}\tag{V9}
\]
**No small-denominator or independent inverse norm has been
postulated:** (V7)–(V9) hold for every \(a>0\),
\(L>0\), and finite \(Q\), provided the original
source equation (V2) holds with \(f\in L^2\) and
the actual terminal data vanish. The exponential
records the **real** dependence on \(Q L^2/a^2\).

The stronger uniformity used in the original slow geometry,
\(a\ge L^3\), \(L>4\) and \(|Q|\le Q_0\)
(the last bound must be established from the modulation
dynamics, not postulated for the final main theorem), gives
the derived uniform constant
\[
 C_E\le C_E^*(Q_0):=
 1+\exp\left(1+\frac{Q_0+3/2}{4^5}\right)
    \left[8+\frac{Q_0+2}{2\cdot4^4}\right].
 \tag{V10}
\]
Here \(L^2/a^2\le L^{-4}\le4^{-4}\), so the displayed
exponent coefficient may equally be written
\((Q_0+3/2)/(4\cdot4^4)\); it is deliberately
not hidden in a generic constant.

## 3. Actual radial commutator gradient and the L^(-5/2) gain — WITHOUT a C² point-jet patch

Use the **already defined real physical flat inner transition**
\(\eta(y)=\mathrm{actualHartreeFlatInnerTransition}(L,y)\),
whose derivative support is exactly
\[
 I_{\rm tr}=[5L/8,\,3L/4]\subset I,\quad
 h_{\rm in}=L/8.
\]
On this transition the outer \(\chi\equiv1\) by the verified
\`actual_Hartree_same_source_backward_flat_overlap_regions\`.
The field is \(u-\eta e\). The original frozen scaled
Kummer differential expression therefore has the true
cutoff commutator
\[
 \mathcal C_{\rm in}
 =-2\eta'e'-
  \left(\eta''+
     \left(\frac2y+\frac{iy}{2a^2}\right)\eta'\right)e .
 \tag{V11}
\]
It is **not** the entire nonlinear Hartree commutator; the
original quartic Riesz interaction is estimated separately
from its full physical fields.

From the already paper-derived exact derivative (S11) in
\`HBL_213_SOURCE_FAITHFUL_FLAT_OVERLAP_20261110.md\`,
letting \(C_1,C_2,C_3\) denote the actual smooth
fixed cutoff derivative constants,
\[
 \|\mathcal C_{\rm in}'\|_{L^2(I_{\rm tr})}
 \le\left[\frac{A_0}{L}
          +A_1\frac{L}{a^2}\right]E,
 \tag{V12}
\]
where the **fully explicit** fixed coefficients are
\[
 \begin{aligned}
 A_0&=(19+4\sqrt3)C_1+(12+24\sqrt3)C_2+24C_3,\\
 A_1&=\left(\frac{\sqrt3}2+\frac3{16}\right)C_1+\frac32C_2 .
 \end{aligned}
 \tag{V13}
\]
This is merely substitution of
\(\sup|c_1|\le4/L+L/(2a^2)\),
\(\sup|c_1'|\le8/L^2+1/(2a^2)\),
and \(h_{\rm in}=L/8\) into (S11).
For \(L>4\), \(a\ge L^3\),
\(1+y^2\le1+L^2\le2L^2\), (V12) gives
\[
 \|(1+y^2)\mathcal C_{\rm in}'\|_{L^2(I_{\rm tr})}
 \le2(A_0+A_1)L E .
\]
Combining (V4) and (V9) **closes the previous missing
backward-overlap \(E=\|e''\|_2\) producer**:
\[
 \boxed{\ 
 \begin{aligned}
 &\|(1+y^2)\mathcal C_{\rm in}'\|_{L^2(I_{\rm tr})}\\
 &\quad\le
 \sqrt2(A_0+A_1)C_E(L,a,Q)
 \left[
 16C_{\rm in}L^{-5/2}N+
 L^{-9/2}(C_KN+|\delta|M_0)
 \right].
 \end{aligned}
 \ }\tag{V14}
\]
The last step uses \(a\ge L^3\) **only** to bound
\(a^{-2}\le L^{-6}\). The leading \(L^{-5/2}\)
is a genuine physical spatial gain from **the original same
Hartree source**, the existing Fredholm shell bound, actual
Cramer Green normalization, and the backward zero-Cauchy
Volterra equation. It involves **no new independent
\(C^2\) trace datum, no \(F_o(B)\) point trace, and no
assumed positive time exponent**.

## 4. Strict limits of this new proof

(V1)–(V14) are a self-contained paper chain; they **remain
to be integrated into a new real Lean theorem** with
the original source inputs, an exact printed type
and pinned three-axiom CI. The premise that the actual
Hartree source has continuous representatives and
classical two-channel radial ODEs is required; these
properties must be proved for the ultimately constructed
moving PDE orbit. If original projection parameters
are not yet trapped, retain the explicit finite
\(C_E(L,a,Q)\) and do **not** silently replace it by
\(C_E^*(Q_0)\).

This completes only the **inner moving smooth-overlap
local Kummer commutator gradient**. The original full
Hartree finite-layer residual must still combine:
the outer cutoff commutator, all global nonlocal mixed
Riesz interactions, the true material time derivatives
and selected-speed/endpoint Lipschitz, the spectral
inverse (or another valid physical energy inverse),
the full finite PDE recursion, and the true nonlinear
modulation flux producing Type-II rates.
The original revised §2.13 and final main theorem
remain **UNPROVED, 11/13 (84.62%)**.

The previous dedicated outer \(C^2\) jet route was
also strictly validated (CI 42825266426), but this
flat-overlap route **avoids** the historic \(F_o(B)\)
point-trace obstruction altogether; the two routes
should not be conflated or double-counted.
