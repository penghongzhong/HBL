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


## 5. NEW exact physical parameter Lipschitz of the backward Green mismatch at fixed L

The same radial Volterra inverse gives a **quantitative
coefficient-stability estimate**, not just a one-parameter
bound. Fix the same physical \(L>4\) and two original
parameter/source tuples \((a_j,Q_j,f_j)\), \(j=1,2\),
with \(a_j>0\), and let the **actual original**
Fredholm/Kummer differences \(e_j\) satisfy
\[
 \mathcal K_{a_j,Q_j}e_j=f_j,\qquad
 e_j(L)=e_j'(L)=0,\qquad
 \mathcal K_{a,Q}
 =\partial_y^2+\left(\frac2y+\frac{iy}{2a^2}\right)\partial_y
    +\frac{Q}{a^2}.
\]
No independently chosen solution operator is inserted:
\(e_j\) are the actual source-matched fields whenever
the previously established physical source identities
hold. The difference \(d=e_1-e_2\) has zero terminal jet
and satisfies the **exact** same-physical-region equation
\[
 \boxed{
 \mathcal K_{a_1,Q_1}d
 =f_1-f_2
  -\frac{iy}{2}(a_1^{-2}-a_2^{-2})e_2'
  -(Q_1a_1^{-2}-Q_2a_2^{-2})e_2 .
 }\tag{V15}
\]
This is an algebraic identity for the original operator,
not an *assumed Lipschitz estimate*.

The same actual backward Gronwall inequality (V7),
with \(M_{\rm V,2}\) evaluated at \((a_2,Q_2)\),
also proves the concrete zero-jet bounds
\[
 \|e_2'\|_{L^2(I)}
 \le 2L M_{\rm V,2}\|f_2\|_{L^2(I)},\qquad
 \|e_2\|_{L^2(I)}
 \le \frac12 L^2M_{\rm V,2}\|f_2\|_{L^2(I)} .
 \tag{V16}
\]
Consequently the **actual** right-hand side \(g\) of
(V15) obeys
\[
 \boxed{\quad
 \|g\|_{L^2(I)}
 \le\|f_1-f_2\|_2
 +M_{\rm V,2}L^2
 \left(
 |a_1^{-2}-a_2^{-2}|
 +\frac12|Q_1a_1^{-2}-Q_2a_2^{-2}|
 \right)\|f_2\|_2 .
 \quad}\tag{V17}
\]
Applying (V9) to \(d\) yields the fully explicit
**fixed-original-radius parameter stability**
\[
 \boxed{\quad
 \|(e_1-e_2)''\|_{L^2(I)}
 \le C_E(L,a_1,Q_1)
 \left[\|f_1-f_2\|_2+
 M_{\rm V,2}L^2
 \left(|a_1^{-2}-a_2^{-2}|+
 \tfrac12|Q_1a_1^{-2}-Q_2a_2^{-2}|\right)
 \|f_2\|_2\right].
 \quad}\tag{V18}
\]
The corresponding \(L^2\) and \(H^1\) bounds follow
with the precise \(L^2M_{\rm V,1}/2\) and
\(2LM_{\rm V,1}\) factors from (V16),
applied to \(d\) and the new right side \(g\).

Thus **the local linear coefficient/parameter
Lipschitz obstruction is removed on paper
for a common physical \(L\)**, conditional only on
the *genuine nonlinear source difference*
\(\|f_1-f_2\|_2\) and actual original coefficients.
A moving \(L=L(s,\alpha)\) requires pulling both
solutions to one normalized interval, including
its time and parameter derivatives and true
source-domain transport. Likewise the original
quartic Hartree source difference must be derived
from the PDE profiles using the already calculated
nonlocal Lipschitz estimate, not supplied as a
new unverified hypothesis. This is **not** the
global four-region PDE parameter-Lipschitz or a
new strict Lean theorem. Formal original count
remains **11/13**.


## 6. Moving-radius parameter transport: normalize the genuine Cauchy points BEFORE comparing

The fixed-\(L\) equation (V15)–(V18) does **not** compare
two parameter values whose actual slow inner radii differ.
There is nevertheless an exact *source-faithful* repair of
that domain mismatch, with no new abstract solution operator.

Let \(L_j>4\), \(a_j>0\), \(Q_j\in\mathbb C\),
\(I_j=[L_j/2,L_j]\), and suppose the **actual**
Fredholm–Kummer field differences \(e_j\in H^2(I_j)\)
satisfy the physical original equation
\[
 \mathcal K_{a_j,Q_j}e_j=f_j\in L^2(I_j),\qquad
 e_j(L_j)=e_j'(L_j)=0,\quad
 \mathcal K_{a,Q}
 =\partial_y^2+
   (2/y+iy/(2a^2))\partial_y+Q/a^2.
\tag{V19}
\]
The \(f_j\) are precisely the physical same-source defects
from (V2), evaluated at the respective parameter values;
there is no newly assumed forcing norm.

Define the **exact moving Cauchy coordinate**
\[
 x=y/L_j\in I_\ast=[1/2,1],\qquad
 E_j(x)=e_j(L_jx),\quad
 \tau_j=L_j^2/a_j^2,\quad
 G_j(x)=L_j^2 f_j(L_jx).
\tag{V20}
\]
The ordinary chain rule gives
\[
 \boxed{\;
 E_j''+\left(\frac2x+\frac{i\tau_j x}2\right)E_j'
       +\tau_jQ_jE_j=G_j,\qquad
 E_j(1)=E_j'(1)=0.
 \;}
\tag{V21}
\]
The same transform \(H_j=xE_j\) now gives
\[
 H_j''+\frac{i\tau_jx}2H_j'
 +\tau_j(Q_j-i/2)H_j=xG_j.
\tag{V22}
\]
For the two **actual** normalized fields \(D=E_1-E_2\)
the difference equation, with no lost moving-interface
boundary term, is exactly
\[
 \boxed{\quad
 \begin{aligned}
 \mathscr K_{\tau_1,Q_1}D={}&G_1-G_2
 -\frac{ix}{2}(\tau_1-\tau_2)E_2'\\
 &-(\tau_1Q_1-\tau_2Q_2)E_2,\qquad
 D(1)=D'(1)=0,
 \end{aligned}\quad}
\tag{V23}
\]
where
\(\mathscr K_{\tau,Q}
 =\partial_x^2+(2/x+i\tau x/2)\partial_x+\tau Q\).
In particular, variations of the true Fredholm
radius enter only through the explicit
\(\tau_j=L_j^2/a_j^2\) coefficients and the
**genuinely transported** physical sources \(G_j\);
the zero Cauchy traces remain exactly zero at \(x=1\).

The same already derived Volterra bound (V7)–(V9),
now on \(I_\ast\), gives
\[
 \begin{gathered}
 M_j=\exp\{1+(|Q_j|+3/2)\tau_j/4\},\\
 C_j=1+M_j[8+(|Q_j|+2)\tau_j/2],\\
 \|E_2'\|_{L^2(I_\ast)}\le2M_2\|G_2\|_2,\qquad
 \|E_2\|_2\le\tfrac12M_2\|G_2\|_2,
 \end{gathered}
\tag{V24}
\]
and hence the **full true moving-radius coefficient budget**
\[
 \boxed{\begin{aligned}
 \|E_1''-E_2''\|_{L^2(I_\ast)}
 \le C_1\Big[&
 \|G_1-G_2\|_2\\
 &+M_2\big(
   |\tau_1-\tau_2|+
   \tfrac12|\tau_1Q_1-\tau_2Q_2|
  \big)\|G_2\|_2\Big].
 \end{aligned}}
\tag{V25}
\]
Here \(C_1\) denotes the explicit \(C_j\) at \(j=1\),
**not** a cutoff derivative constant. The physical
rescaling gives exactly
\(\|G_j\|_{L^2(I_\ast)}
 =L_j^{3/2}\|f_j\|_{L^2(I_j)}\) and
\(\|E_j''\|_{L^2(I_\ast)}
 =L_j^{3/2}\|e_j''\|_{L^2(I_j)}\).
No identification between \(I_1\) and \(I_2\)
was made before their exact pullbacks.

For a smooth real parameter \(\alpha\), the remaining
*source* transport is also explicit:
\[
 \boxed{\;
 \partial_\alpha G_\alpha(x)
 =2L L_\alpha f_\alpha(Lx)
 +L^2(\partial_\alpha f_\alpha)(Lx)
 +L^2 x L_\alpha(\partial_y f_\alpha)(Lx).
 \;}
\tag{V26}
\]
Thus the **remaining original-PDE parameter Lipschitz
producer is sharply identified:** the three source
terms in (V26), including the local derivative of the
full actual Hartree nonlocal source, and the
\(L_\alpha,a_\alpha,Q_\alpha\) variation must be
estimated using the real modulation equations and
the true moving four-region profiles. It cannot be
replaced by a free Lipschitz assumption on \(G_j\).

(V19)–(V26) are **paper-level conditional-on-the-actual-source
identities and quantitative Volterra bounds**; they do
not construct the original Hartree physical PDE orbit,
give a time-positive residual, or replace the projected
Hartree dispersive inverse. The coefficient identities
are not yet separately audited in Lean. The source
regularity for (V26), the global four-region nonlinear
terms, the spectral inverse and modulation selection
remain **open**. Revised original count: **11/13**.
