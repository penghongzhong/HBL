# HBL revised §2.13: sharp obstruction to an annulus-only phase-resonance repair (10 November 2026)

**Verification boundary.** This is a newly derived **paper-level necessary estimate** for the exact three-dimensional Hartree bubble and its physical phase zero mode. It is not a proof about the full nonlocal Hartree residual, not a new Lean declaration, and not an original retained paper theorem. The accepted count is **11/13**, unchanged.

## 1. Exact physical input

Fix
\[
 W(r)=(1+r^2)^{-1/2},\qquad
 \Lambda W=\frac12W+rW'
 =\frac{1-r^2}{2(1+r^2)^{3/2}},\qquad
 L_-=-\Delta_r-3W^4 .
\]
The phase Fredholm moment for a radial source \(F\) is
\[
 \mathcal M_-(F)=\int_0^\infty r^2W(r)F(r)\,dr.
\]
The original Hartree phase Hessian is exactly \(L_-\), since the first variation of the quartic Riesz density in an imaginary direction vanishes at the real bubble. Its regular zero-energy solution is \(W\). The moment \(\mathcal M_-(F)=0\) is necessary for a regular finite-energy stationary inverse **when the source is compactly supported**.

The exact bare-dilation moment is
\[
 I(R)=\int_0^R r^2W(r)\Lambda W(r)\,dr
 =\arctan R-\frac R2-\frac{R}{2(1+R^2)}.
\]
For \(R\ge 2\pi\), \(I(R)\le -R/4\).

## 2. Necessary quantitative cost of a local phase repair

**Proposition (conditional annular-only repair lower bound).**
Let \(R\ge2\pi\), \(b\in\mathbb R\), and let
\(\chi\colon[0,\infty)\to[0,1]\) satisfy
\(\chi=1\) on \([0,R]\) and \(\chi=0\) on \([2R,\infty)\).
Let \(G\in H^1_0((R,2R);\mathbb C)\), extended by zero, and assume the **exact phase compatibility**
\[
 \mathcal M_-\bigl(b\chi\Lambda W+G\bigr)=0.
 \tag{A1}
\]
Then, with no hidden \(R\)-dependent constant,
\[
 \boxed{\quad
 \|(1+r^2)G'(r)\|_{L^2(R,2R)}
 \ge\frac{|b|}{2}\,R^{1/2}.
 \quad}
 \tag{A2}
\]

**Proof.**
Since \(r^2W\Lambda W\le0\) for \(r\ge R\ge2\pi\) and \(0\le\chi\le1\),
\[
 \mathcal M_-(\chi\Lambda W)
 \le I(R)\le -R/4.
\]
The compatibility equation (A1) therefore implies
\[
 \left|\int_R^{2R}r^2W(r)G(r)\,dr\right|
 \ge|b|R/4.
 \tag{A3}
\]
Set
\[
 A_R(r)=\int_R^r\frac{t^2}{\sqrt{1+t^2}}\,dt.
\]
For \(R\le r\le2R\),
\[
 0\le A_R(r)\le\int_R^r t\,dt
 =\frac{r^2-R^2}{2}\le\frac{1+r^2}{2}.
\]
The two \(H^1_0\) endpoint traces make integration by parts exact:
\[
 \int_R^{2R}r^2W(r)G(r)\,dr
 =-\int_R^{2R}A_R(r)G'(r)\,dr .
\]
Cauchy--Schwarz gives
\[
 \left|\int_R^{2R}r^2WG\,dr\right|
 \le\left\|\frac{A_R}{1+r^2}\right\|_{L^2(R,2R)}
 \|(1+r^2)G'\|_2
 \le\frac{\sqrt R}{2}\|(1+r^2)G'\|_2.
\]
Combining with (A3) proves (A2). \(\square\)

No Hartree nonlinearity has been replaced by a local NLS term; the phase mode and dilation are those of the *actual* quartic-density inverse-square Hartree bubble. The assumption (A1) is an explicitly stated **test of an annulus-only compensation mechanism**, not a condition asserted for the full physical PDE.

## 3. Consequence for the actual scalar HBL clock, conditional on a coarse trap

Suppose a genuine HBL modulation coordinate (once constructed) satisfies
\[
 q_s=4\mu,\qquad
 b=\lambda_s/\lambda=\frac{1+4\mu}{2q},\qquad
 q(s_0)=q_0>0,\qquad
 0<m\le\mu(s)\le M
\]
for \(s\ge s_0>0\). Then
\[
 b(s)\ge\frac{1+4m}{2(q_0+4M(s-s_0))}
 \ge\frac{1+4m}{2C_qs},\qquad
 C_q=q_0/s_0+4M.
\]
If (A1) is used as a phase repair at \(R=R(s)\ge2\pi\), the corresponding \(G_s\) obeys
\[
 \boxed{\quad
 \|(1+r^2)\partial_rG_s\|_{L^2(R(s),2R(s))}
 \ge\frac{1+4m}{4C_q}\frac{\sqrt{R(s)}}s .
 \quad}
 \tag{A4}
\]
Consequently this *isolated local annular repair* cannot also satisfy
\(\|(1+r^2)G_s'\|_2=O(s^{-17/8-\eta})\)
for any \(\eta>0\), because \(R(s)\ge2\pi\) makes its required lower bound at least \(c/s\). This is a **genuine incompatibility of those two conditional requirements**, not a lower bound on the full nonlocal residual.

## 4. Exact scope and what is still required

The full HBL source includes the actual nonlocal Hartree coupling, other four-region fields, long-range radiation, selected two speeds, and modulation feedback. Their phase moments need not be localized to \([R,2R]\). A global cancellation, a resonance-renormalized source space, or a projected Hamiltonian normal form could evade (A2). This estimate therefore eliminates the **annulus-only small weighted-derivative phase repair** as a route to the target \(s^{-17/8-\eta}\) absolute-Duhamel bound; it does **not** eliminate genuine Hartree Type-II blowup.

The missing steps remain a constructive same-PDE global phase cancellation, the full four-region differentiated nonlocal residual with actual positive time order and parameter Lipschitz, a genuinely applicable projected evolution inverse, finite PDE recursion, a true orbit, and a dynamically derived Type-II rate.

**Formal audit reference (not a certificate for A1--A4):**
- CI 42536552509, original job 128902012127: strict --trust=0 nonlinear spectral four-piece PDE *telescoping identity*, audited axioms exactly propext / Classical.choice / Quot.sound.
- CI 42854633900, original job 129964186672: strict original-source inner spectral C² jump budget, same pinned toolchain/axiom policy.
- The old CI 42530158681 failed due to upstream source-module compilation; it is superseded by the first success, not itself accepted.
- The paper-level proposition (A2) was checked algebraically, but has **no** Lean 4.35.0-rc3 / pinned-Mathlib CI, #check, or #print axioms. No original environment increments.
