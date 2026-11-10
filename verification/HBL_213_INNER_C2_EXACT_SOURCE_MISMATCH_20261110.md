# HBL §2.13: exact same-source *inner* \(C^2\) interface defect and repair budget

**10 November 2026. Paper analysis; no new formal proof or original environment acceptance. The strict revised-original count remains 11/13.**

## 1. The inner second-jet defect is completely determined by the original physical sources

This calculation uses the **actual** modules
\`ActualHartreeTwoChannelMatchedShell.lean\` (the exact two-channel
Fredholm-inner equation and its shell bound),
\`ActualHartreeMomentLockedKummerPullback.lean\` (the original normalized
Green physical pullback),
\`ActualHartreeMatchedSpectralOriginalPDEMismatch.lean\` (the original
source-dependent spectral correction), and
\`ActualHartreeSpectralCorrectedFourPieceThreeC1.lean\` (the exact
first-jet match). It is *not* a claim that the four-piece moving Hartree
orbit has been constructed.

Let \(a,L>0\), \(r_0=L/a\), and let
\[
 u(y)=\mathrm{actualHartreeTwoChannelInner}(F_+,F_-)(y),
 \quad
 u_0(r)=\mathrm{actualOriginMatchedKummerValue}(F)(r),
 \quad
 w(r)=\mathrm{actualHartreeMatchedSpectralCorrectedValue}(F,\delta)(r),
 \quad v(y)=w(y/a).
\]
The same original actual inner physical source is
\[
 S_{\rm in}(y)=\frac{F_+(y)+iF_-(y)}y,
 \qquad
 F_{\rm cor}(r)=F(r)-\delta u_0(r).
\]
Here \(F_+,F_-\) are the two *actual* real Fredholm sources,
not independently imposed envelopes. Assume the original
weighted \(L^{2,7/4}\) memberships and, for classical evaluation
of the second derivatives, continuity of \(F_+\), \(F_-\), and
\(F\) on the positive physical matching neighbourhood.
The existing Cramer/moment-locked source normalization gives
\[
 u(L)=v(L),\qquad u_y(L)=v_y(L).
 \tag{I1}
\]
Let
\[
 \mathcal K_a h
 =h_{yy}+
  \left(\frac2y+\frac{iy}{2a^2}\right)h_y
  +\frac{Q}{a^2}h,\qquad
 Q=\mathrm{frozenZeroCoeff}(\mu,\theta).
\]
The **actual** Fredholm-inner defect is
\[
 D_{\rm in}(y):=(\mathcal K_a u)(y)+S_{\rm in}(y).
 \tag{I2}
\]
The original spectrally corrected Kummer source, without a fictitious
free curvature parameter, gives
\[
 (\mathcal K_a v)(L)=a^{-2}F_{\rm cor}(r_0).
 \tag{I3}
\]
Subtract (I2) and (I3) and use both equalities in (I1).
All identical first- and zeroth-order coefficients cancel,
so the **exact** missing second Cauchy jet is
\[
 \boxed{\;
 \Delta_2
 :=u_{yy}(L)-v_{yy}(L)
 =D_{\rm in}(L)-S_{\rm in}(L)
     -a^{-2}F_{\rm cor}(r_0).
 \;}
 \tag{I4}
\]
No unknown curvature datum appears on the right. On an
actual shell \(L>2\), the existing bound
\`actual_Hartree_two_channel_inner_Kummer_defect_bound\`
with \(R=L\) yields the direct conditional consequence
\[
 \boxed{
 |\Delta_2|
 \le \underbrace{\left(
     \frac{C_{\rm in}}{L^4}+
     \frac{C_{\rm K}(\mu,\theta)}{a^2}\right)
     \bigl(\|F_+\|_{2,7/4}+\|F_-\|_{2,7/4}\bigr)}_{\text{existing actual Fredholm defect shell bound}}
 +\left|S_{\rm in}(L)+a^{-2}F_{\rm cor}(L/a)\right|.
 }
 \tag{I5}
\]
The named \(C_{\rm in}\) and \(C_{\rm K}\) are the actual
\`actualInnerShellEquationConstant\` and
\`actualInnerShellKummerConstant\` of the Lean source,
not new physical assumptions.

**Decisive interface gate:** The genuine same-physical-PDE
source identity must control
\[
 S_{\rm in}(L)+a^{-2}\bigl(F(L/a)-\delta u_0(L/a)\bigr)
 \tag{I6}
\]
and its moving-time / parameter derivatives. Neither Cramer
selection nor first-jet matching forces (I6) to be small.
If (I6) is shown to cancel by the true original Hartree
source construction, the inner curvature defect is bounded
*directly* by the already proven small Fredholm shell defect.
If not, it is precisely the remaining source mismatch that
the new \(C^2\) repair must absorb.

## 2. Cost of a *real* one-sided curvature patch

Let \(0<h<aB-L\), and take a fixed \(C^\infty\) cutoff
\(\eta\colon[0,\infty)\to[0,1]\) equal to \(1\) near \(0\),
identically \(0\) on \(z\ge1\), flat at its outer edge.
Set on \(y\ge L\)
\[
 P_h(y)=\frac{\Delta_2}{2}(y-L)^2
          \eta\!\left(\frac{y-L}{h}\right).
 \tag{I7}
\]
Use \(P_h=0\) to the left solely when forming the total
corrected field. At \(L\), its right-hand value, slope,
and curvature are \(0,0,\Delta_2\). The total field
\(u\) on the left and \(v+P_h\) on the right is then
genuinely \(C^2\) at \(L\). The correction vanishes
before the separately corrected outer interface \(aB\).

For \(z=(y-L)/h\in[0,1]\), define
\[
 \begin{aligned}
 E_1(z)&=z\eta+\frac{z^2}{2}\eta',
 \\
 E_2(z)&=\eta+2z\eta'+\frac{z^2}{2}\eta'',
 \\
 E_3(z)&=3\eta'+3z\eta''+\frac{z^2}{2}\eta''' ,
 \qquad M_j=\sup_{z\in[0,1]}|E_j(z)|.
 \end{aligned}
\]
Direct differentiation gives the *exact* costs
\[
 P_h'=\Delta_2 h E_1,\qquad
 P_h''=\Delta_2 E_2,\qquad
 P_h'''=\Delta_2 h^{-1}E_3.
 \tag{I8}
\]
Consequently, using the real physical scaled coefficient
\(A_a(y)=2/y+iy/(2a^2)\),
\[
 (\mathcal K_aP_h)'
 =P_h'''+A_aP_h''
    +(A_a'+a^{-2}Q)P_h'.
 \tag{I9}
\]
Since \(y\in[L,L+h]\), \(a,L>0\), and
\(|A_a|\le2/L+(L+h)/(2a^2)\),
\(|A_a'|\le2/L^2+1/(2a^2)\), the *actual*
weighted derivative of the new repair source obeys
\[
 \boxed{
 \begin{aligned}
 &\|(1+y^2)(\mathcal K_aP_h)'\|_{L^2(L,L+h;dy)}
 \\
 &\quad\le
  (1+(L+h)^2)|\Delta_2|\sqrt h
  \left[
   \frac{M_3}{h}
   +\left(\frac2L+\frac{L+h}{2a^2}\right)M_2
   +h\left(\frac2{L^2}+\frac{1/2+|Q|}{a^2}\right)M_1
  \right].
 \end{aligned}
 }
 \tag{I10}
\]
The first term scales as
\((1+L^2)|\Delta_2|/\sqrt h\) for \(h\ll L\).
**Making the patch arbitrarily narrow worsens, rather than
automatically improves, the gradient source norm.**
The geometric overlap \(h<aB-L\) and all moving derivatives
of \(h,L,a,\Delta_2\) must be controlled by the original PDE,
not imposed as an independent smallness condition.
Equation (I10) is an upper bound, not a universal lower bound.

## 3. What this proves and what it does not

The algebraic identity (I4) and explicit estimate (I10) give a
**shortest measurable analytic target** for closing the original
inner \(C^2\) interface and expose the single exact source
cancellation (I6). They are not yet Lean-formalized and are not
full nonlocal Hartree residual estimates: the original quartic
convolution, moving cutoffs, two-channel speed/time derivatives,
the inner/outer patch interaction, the genuine projected Hartree
inverse, a PDE orbit and dynamically selected Type-II rate
remain load-bearing obligations.

Existing original environments: **11/13**, not 12/13.
