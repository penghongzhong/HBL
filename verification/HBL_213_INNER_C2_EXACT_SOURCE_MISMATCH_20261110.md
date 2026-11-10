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


## 4. The actual HBL original plateau ALREADY CANCELS the entire unmatched physical source

**This refines §1 from a general source-mismatch criterion to a
strictly source-aligned identity.** The source \(F\) in §1
is not arbitrary in the original HBL selected-speed construction:
the current, already developed
\`ActualHartreeMomentLockedPlateauSource.lean\`
contains the exact theorem
\`actual_Hartree_moment_locked_plateau_scaled_source\`.

At any \(0<y\le L=\mathrm{actualHartreeSlowInnerRadius}(\ell)\),
and with the original selected real speed coefficients
\(d_b,d_\omega\), that theorem gives, **before spectral
correction**, the exact equality
\[
 \boxed{
 S_{\rm in}(y)+a^{-2}F_o(y/a)=0,
 }\tag{I11}
\]
where
\[
 \begin{aligned}
 F_+(y)&=
  \mathrm{actualHartreeTransmissionPlusSource}(\ell,c,z)(y)
    +d_\omega\,\mathrm{actualMomentLockedInnerPhaseSource}(L,c)(y),\\
 F_-(y)&=
  \mathrm{actualHartreeTransmissionMinusSource}(\ell,c,z)(y)
    +d_b\,\mathrm{actualMomentLockedInnerScaleSource}(L,c)(y),\\
 F_o(r)&=-\mathrm{actualHartreeLaplacianScaledKummerSource}(a,\ell,c,z)(r)
 -d_b\,\mathrm{actualMomentLockedScaledScaleSource}(a,c)(r)
 -d_\omega\,\mathrm{actualMomentLockedScaledPhaseSource}(a,c)(r).
 \end{aligned}
\]
The full quartic nonlocal Riesz interaction is inside these
definitions; they are not an NLS surrogate, a separate
source envelope or an additional axiom.

For the spectrally corrected **same original Green field**,
\[
 F_{\rm cor}(r)=F_o(r)-\delta u_0(r),
 \qquad
 u_0=\mathrm{actualOriginMatchedKummerValue}(F_o).
\]
The prior exact statement (I11) immediately yields
\[
 \boxed{
 S_{\rm in}(L)+a^{-2}F_{\rm cor}(L/a)
 =-a^{-2}\delta u_0(L/a).
 }\tag{I12}
\]
Substituting this into (I4) **completely eliminates**
the formerly open independent original-source mismatch:
\[
 \boxed{
 \Delta_2=D_{\rm in}(L)+a^{-2}\delta u_0(L/a).
 }\tag{I13}
\]
Thus the true inner spectral \(C^2\) curvature mismatch is
bounded by **already-existing physical source norms and the actual
spectral coefficient only**:
\[
 \boxed{
 |\Delta_2|
 \le\left(\frac{C_{\rm in}}{L^4}
      +\frac{C_{\rm K}(\mu,\theta)}{a^2}\right)
      \bigl(\|F_+\|_{2,7/4}+\|F_-\|_{2,7/4}\bigr)
  +\frac{|\delta|}{a^2}|u_0(L/a)| .
 }\tag{I14}
\]
Here the \(F_\pm\) have the literal source definitions above,
the old shell bound requires continuity and \(L>2\), and
the actual spectral Green field must have its stated \(C^2\)
regularity. **No pointwise bound on the independent outer value
\(F_o(L/a)\) survives the cancellation.**

A dedicated no-new-axiom Lean module now encodes the *exact*
same-source spectral cancellation (I12):
\`HBL/TypeIIDynamicSelection/ActualHartreeInnerSpectralC2PlateauSourceLock.lean\`;
workflow \`hbl-213-inner-spectral-c2-plateau-source-lock.yml\`.
Its new strict CI must be checked for completion before a successful
audit is claimed. The composite full curvature identity (I13),
the complete four-region global \(C^2\) field and quantitative
time/parameter derivative gains have **not** yet been
formally checked by a new strict CI.

**This closes the paper-level original-source identification
for the inner \(C^2\) jet. It does not close §2.13,
the genuine finite PDE orbit or the dynamically selected
Type-II rate; original strict accepted count remains 11/13.**


## 5. The retained \(a\ge L^3\) geometry DOES make the inner \(C^2\) patch small spatially

This is distinct from the earlier correctly rejected attempt to
repair the **whole** Duhamel time deficit using geometry alone.
Here we study *only the new curvature patch generated by the actual
same-source inner interface*.

Keep a fixed admissible \(B>0\), and suppose
\[
 L>2,\qquad a\ge L^3,\qquad
 L^2\ge \frac{5}{4B},\qquad
 |Q|\le Q_0,\qquad Q_0\ge0 .
 \tag{I15}
\]
These imply \(aB\ge L^3B\ge5L/4\), so the concrete choice
\[
 h=L/4\quad\text{satisfies}\quad L+h\le aB.
 \tag{I16}
\]
The (fixed) smooth patch can be supported strictly before \(aB\)
by taking \(\eta\) vanishing on a neighbourhood of \(z=1\)
and choosing the left overlap endpoint accordingly.

On \([L,5L/4]\), because \(a\ge L^3\),
\[
 \begin{aligned}
 1+(L+h)^2 &\le \frac{29}{16}L^2,\\
 |A_a| &\le \frac{21}{8L},\\
 |A_a'|+|Q|/a^2 &\le \frac{5/2+Q_0}{L^2}.
 \end{aligned}
\]
Insert these into the *exact* inequality (I10):
\[
 \boxed{
 \|(1+y^2)(\mathcal K_aP_{L/4})'\|_{L^2(L,5L/4)}
 \le C_{\eta,Q_0}L^{3/2}|\Delta_2|,
 }\tag{I17}
\]
where the explicit constant is
\[
 C_{\eta,Q_0}=
 \frac{29}{32}\left[
 4M_3+\frac{21}{8}M_2+
  \left(\frac58+\frac{Q_0}{4}\right)M_1
 \right].
 \tag{I18}
\]
Apply the true same-source curvature cancellation (I13)
and original Fredholm shell estimate (I14):
\[
 \boxed{
 \begin{aligned}
 \|(1+y^2)(\mathcal K_aP_{L/4})'\|_2
 &\le C_{\eta,Q_0}\Big[
  C_{\rm in}L^{-5/2}N\\
 &\quad+
 L^{-9/2}\bigl(C_{\rm K}(\mu,\theta)N+
     |\delta|\,|u_0(L/a)|\bigr)\Big],
 \quad N=\|F_+\|_{2,7/4}+\|F_-\|_{2,7/4}.
 \end{aligned}
 }\tag{I19}
\]

**Interpretation.** Unlike a narrow artificial interface
patch, this exact \(h=L/4\) repair is spatially small
with a derived \(L^{-5/2}\) principal factor, using
the true physical source and its pre-existing Fredholm
budget. There is **no independent \(F_o(L/a)\) trace
or prescribed time decay**. This is a concrete positive
paper-level route to a complete physical \(C^2\) splice.

**Remaining real PDE work:** derive moving-time and parameter
Lipschitz versions of the source cancellation and jet trace;
make the \(C^2\) correction into the same selected *four-region*
complex field; compute its full quartic nonlocal Hartree
cross interactions; prove a stable projected inverse and
the genuine \(s\)-positive time order. This *one patch*
estimate is not an \(O(s^{-15/8})\) or \(O(s^{-9/4})\)
estimate for the full PDE residual. Strict original acceptance
remains **11/13**.
