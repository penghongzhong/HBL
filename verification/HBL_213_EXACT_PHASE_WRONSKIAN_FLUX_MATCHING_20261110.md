# HBL revised §2.13 — exact phase-Wronskian flux and mandatory outgoing C¹ trace (10 November 2026)

**Status:** A new, fully specified paper-level boundary-flux identity and necessary matching estimate for the *original* 3D quartic-density inverse-square Hartree phase channel. No new Lean certificate or original-paper environment acceptance is claimed. **11/13 unchanged.** In particular this does not construct the missing time-dependent full nonlocal orbit.

## 1. Zero-energy original Hartree phase channel: exact finite-radius flux

For the normalized physical bubble and phase linearization, set
\[
W(r)=(1+r^2)^{-1/2},\quad \Lambda W=\frac{1-r^2}{2(1+r^2)^{3/2}},\quad
L_-g=-g''-\frac2r g'-3W^4g.
\]
Here \(L_-\) is the **true imaginary-channel linearization** of
\(\mathcal H(u)=-\Delta u-\kappa_{\rm H}(|x|^{-2}*|u|^4)|u|^2u\)
at the real profile \(W\): the first variation of \(|u|^4\) in the imaginary direction is zero. No local approximation of the real Hartree channel is made.

**Lemma (exact phase Wronskian flux).** If \(g\) is origin-regular (\(g,g'\) finite, \(g'(0)=0\)) and \(L_-g=F\) on \((0,R)\), with \(F\) continuous or locally integrable in the natural radial weight, then
\[
\boxed{\quad
R^2[W(R)g'(R)-W'(R)g(R)]
=-\int_0^R r^2W(r)F(r)\,dr.
\quad}\tag{F1}
\]
Indeed, \(L_-W=0\) and multiplication of \(L_-g=F\) by \(r^2W\) gives
\[
\frac{d}{dr}\left\{r^2(Wg'-W'g)\right\}=-r^2WF.
\]
The regular origin flux vanishes. Equation (F1) holds at **each finite radius**, without assuming global Fredholm moment cancellation, compactly supported forcing, or a stationary energy-class inverse.

For \(F=b\Lambda W+E\) on \([0,R]\), where \(E\) is the *actual* remainder of any subsequently derived phase-channel PDE (not an independently postulated envelope), define
\[
I(R)=\int_0^Rr^2W\Lambda W\,dr
=\arctan R-\frac R2-\frac{R}{2(1+R^2)},\quad
M_E(R)=\int_0^Rr^2WE\,dr.
\]
Then
\[
\boxed{\quad
R^2(Wg'-W'g)(R)=-bI(R)-M_E(R).
\quad}\tag{F2}
\]
For \(R\ge 2\pi\), \(I(R)\le-R/4\).
Since \(R^2W(R)\le R\) and \(R^2|W'(R)|\le1\), the reverse triangle inequality in (F2) yields the **necessary physical outgoing jet budget**
\[
\boxed{\quad
|g'(R)|+\frac{|g(R)|}{R}
\ge\frac{|b|}{4}-\frac{|M_E(R)|}{R}.
\quad}\tag{F3}
\]
In particular, if the original Hartree remainder produces \(|M_E(R)|\le\delta |b|R\) with \(0\le\delta<1/4\), a genuinely \(C^1\) matched exterior field has
\[
|g_{\rm out}'(R)|+|g_{\rm out}(R)|/R
\ge(1/4-\delta)|b|.\tag{F4}
\]
There is **no new assumption** of small \(M_E\) in (F1)–(F3); the extra bound in (F4) is only a conditional quantitative consequence. Conversely, if a proposed outer radiative jet were \(o(|b|)\) along a family with \(R\to\infty\), the **same PDE** must furnish a phase moment \(M_E(R)=-bI(R)+o(|b|R)\). These two alternatives are the precise balance between outgoing radiation flux and global phase-source cancellation. One cannot demand *both* negligible outgoing C¹ flux and negligible true phase-source moment.

## 2. Explicit regular response to the untruncated dilation forcing

For \(F=\Lambda W\) on \((0,\infty)\), the regular solution with \(g(0)=0\) is \(g_*(r)=W(r)V(r)\), where
\[
\boxed{\quad
V(r)=\frac{r^2}{4}
-\left(r-\frac1r\right)\arctan r
+\log(1+r^2)-1.
\quad}\tag{F5}
\]
The origin extension satisfies \(V(r)=-r^2/12+O(r^4)\). Direct differentiation gives
\[
V'(r)=\frac r2+\frac1r-\left(1+\frac1{r^2}\right)\arctan r
=-\frac{1+r^2}{r^2}\,I(r).
\]
Consequently \((r^2W^2V')'=-r^2W\Lambda W\), hence \(L_-(WV)=\Lambda W\) **exactly**. All origin-regular solutions for \(b\Lambda W\) are \(b g_*+cW\), and
\[
g_*(r)=\frac r4-\frac\pi2+O(\log r/r),\qquad
g_*'(r)=\frac14+O(\log r/r^2)\quad(r\to\infty).
\tag{F6}
\]
Thus no origin-regular solution for a nonzero *untruncated* bare dilation source lies in \(\dot H^1(\mathbb R^3)\). The explicit growing response supplies the missing normalization of the resonant outgoing flux. This is a stationary linear phase-channel calculation, not a proof of instability, nonlinear blowup, or a bound on any constructed Hartree four-region remainder.

## 3. Direct relevance to the original four-region §2.13 closure

The existing strict Lean three-\(C^1\) interface theorem ensures **continuity** of the matched value and first derivative, not a new smallness bound on the common boundary flux. Formula (F1) shows the exact finite-radius datum that its real two-speed Cramer/Green construction must transport. It rules out a proof shortcut that projects away the divergent bare dilation moment while simultaneously requiring the physical outgoing radiation jet to be negligible. A legitimate proof must instead show, from the *same complete nonlocal Hartree PDE*, either (a) the required compensating \(M_E\) through actual all-region cross interactions, or (b) a radiation/selected-speed interface jet carrying the mandatory flux, with the full differentiated source and time/parameter control.

This exact identity does not close the moving Kummer basis/endpoint/speed derivatives, genuine positive time-power residual, parameter Lipschitz estimate, projected evolution inverse, finite-level PDE recursion, physical orbit or dynamically derived Type-II blowup rate. The paper-level check here used symbolic differentiation of (F5) and direct Wronskian algebra, **not** Lean 4.35.0-rc3. The strict historical PDE telescope is CI 42536552509 (job 128902012127, exact identity only); the true inner spectral \(C^2\) jump budget is CI 42854633900 (job 129964186672). Both original audit logs contain only propext, Classical.choice and Quot.sound. They do not formally verify (F1)–(F6).

**Formal acceptance:** revised original environment **11/13 (84.62%)**, both §2.13 and final Type-II original theorem OPEN.
