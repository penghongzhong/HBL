# §2.13 — time differentiation of the **actual zero-left spectral correction** at a moving Kummer endpoint

11 November 2026 (US Pacific). **Paper derivation, not Lean acceptance.** The retained original revised environments are still **11/13**. This note refines MJ1–MJ3 in \`HBL_213_MOVING_JET_OPERATOR_REDUCTION_20261111.md\` for the literal Green correction defined in \`ActualHartreeMatchedSpectralLeftC1Exact.lean\`. It identifies a boundary slope that cannot be silently treated as zero after time differentiation.

## 1. Same original Cramer/Green response and spectral correction

On a swept open positive-radius interval, assume classical commuting derivatives and
\[
\mathcal L_s f=f_{rr}+p(s,r)f_r+q(s,r)f,\qquad \rho(s)>0.
\]
No time-order, independent forcing envelope or prescribed II-type scale is assumed. Let \(\delta(s)\in\mathbb C\) be the **actual spectral parameter of the same packet**, not an independently small error symbol, and let
\[
\mathcal L_su_0=F,\quad u_0(s,\rho(s))=U(s),\quad
(u_0)_r(s,\rho(s))=D(s).
\]
The literal Cramer zero-left response and corrected field are
\[
\mathcal L_su_1=\delta u_0,\qquad
u_1(s,\rho(s))=(u_1)_r(s,\rho(s))=0,\qquad w=u_0-u_1.\tag{SZ1}
\]
These equations are exactly the abstract differential interfaces of
\`actualHartreeMatchedSpectralFirstSource\` and
\`actualHartreeMatchedSpectralCorrectedValue\`; the actual origin-normalized Green operator supplies their solution, subject to the regularity needed for differentiation. Hence
\[
\mathcal L_sw=F-\delta u_0,\qquad
(\mathcal L_s+\delta)w=F-\delta u_1,\qquad
w(s,\rho)=U,\quad w_r(s,\rho)=D.\tag{SZ2}
\]
In particular, one must **not** infer that the corrected strong PDE residual is \(O(|\delta|^2)\) without the genuine weighted bound for \(u_1\), and one must not treat (SZ2) as the full Hartree residual.

## 2. Moving left boundary: zero spatial jets DO NOT imply zero temporal slope

Differentiate the two zero-left Cauchy identities in (SZ1) **along the moving curve**:
\[
0=\frac{d}{ds}u_1(s,\rho)= (u_1)_s+\rho'(u_1)_r,
\quad
0=\frac{d}{ds}(u_1)_r(s,\rho)
  =(u_1)_{sr}+\rho'(u_1)_{rr}.
\]
Since \((u_1)_{rr}(s,\rho)=\delta(s)U(s)\) by the actual equation and the two zero spatial jets,
\[
\boxed{(u_1)_s(s,\rho)=0,\qquad
(u_1)_{sr}(s,\rho)=-\rho'(s)\delta(s)U(s).}\tag{SZ3}
\]
Thus \(\partial_su_1\) is generally **NOT** a zero-value-and-zero-slope Cramer response at \(\rho(s)\). Applying the previously accepted zero-left weighted Volterra theorem directly to \(\partial_su_1\) would omit the nonzero slope in (SZ3).

The exactly regularized left data are
\[
\rho(u_1)_s(s,\rho)=0,\qquad
\rho^2(u_1)_{sr}(s,\rho)+\rho(u_1)_s(s,\rho)
=-\rho'\rho^2\delta U,\tag{SZ4}
\]
with no explicit factor \(\rho^{-1}\). This still requires estimates for the **actual** \(\rho',\delta,U\).

For the corrected spectral field, the chain rule and (SZ2) yield
\[
\boxed{\begin{aligned}
w_s(s,\rho)&=U'-\rho'D,\\
w_{sr}(s,\rho)&=D'-\rho'\{F(s,\rho)-p(s,\rho)D
-[q(s,\rho)+\delta]U\}.
\end{aligned}}\tag{SZ5}
\]
Consequently
\[
\boxed{\begin{aligned}
\rho^2w_{sr}(s,\rho)+\rho w_s(s,\rho)
={}&\rho^2D'+\rho U'\\
&-\rho'\{\rho^2F-\rho^2pD-\rho^2(q+\delta)U+\rho D\}_{r=\rho}.
\end{aligned}}\tag{SZ6}
\]
The original Kummer radial coefficient has the form
\(p(s,r)=2/r+\alpha(s)ir/2\) in the moving regularized operator of MJ1. There (SZ6) becomes
\[
\rho^2D'+\rho U'-\rho'
  \{\rho^2F-(\rho+i\alpha\rho^3/2)D
    -\rho^2(q+\delta)U\}_{r=\rho}.\tag{SZ7}
\]
No basis-normalization or hidden inverse-left-radius factor has been inserted; this is an exact identity only, not a bound on the data.

## 3. Triangular time-differentiated Green system (without directly differentiating Kummer modes)

At **fixed** \(r\), use product differentiation of the actual operator equations:
\[
\boxed{\begin{aligned}
\mathcal L_s(u_0)_s
 &=F_s-p_s(u_0)_r-q_su_0,\\
\mathcal L_s(u_1)_s
 &=\delta'u_0+\delta(u_0)_s-p_s(u_1)_r-q_su_1.
\end{aligned}}\tag{SZ8}
\]
Here \(p_s,q_s\) denote fixed-radius partial derivatives of the *coefficients*, not the full time derivative of the operator. Equations (SZ3), (SZ5) specify the actual moving Cauchy data.

Let \(h_s(r)\) solve the **same homogeneous equation**
\[
\mathcal L_sh_s=0,\quad h_s(\rho(s))=0,\quad
\partial_rh_s(\rho(s))=1.
\]
Then the corrected temporal response
\[
\widetilde v_s(r):=(u_1)_s(s,r)+\rho'(s)\delta(s)U(s)h_s(r)\tag{SZ9}
\]
has **both** Cauchy jets zero at \(\rho(s)\) and satisfies the second source equation in (SZ8) unchanged. Thus it is \(\widetilde v_s\), **not** \((u_1)_s\), to which a zero-left Volterra estimate can be applied. Any uniform bound on the additional homogeneous mode \(h_s\) must be obtained from the original normalized Kummer IVP; it is not an independent envelope.

The complete source in (SZ8) contains three essential physical producers: \(F_s\), \(\delta'\) and the moving-operator coefficient derivatives. This source is **not** bounded by a frozen \(|\delta|^2\) spectral estimate. The previous weak Hartree PDE flux note controls one separated, truncated component of \(F_s\), not the full untruncated four-region forcing.

## 4. Rigorous insufficiency of all fixed-time spectral/C¹ estimates alone

Fix any admissible time-independent \(\mathcal L,\rho,F,U,D\) with \(u_0\not\equiv0\), and let \(h=\mathcal G_\rho[u_0]\) be its genuine zero-left Green response, so \(\mathcal Lh=u_0\) and \(h\not\equiv0\). For each integer \(N\), choose
\[
\delta_N(s)=\varepsilon\sin(Ns),\quad
u_{1,N}(s,r)=\delta_N(s)h(r).
\]
At every time, \(\|u_{1,N}(s,\cdot)\|_X\le\varepsilon\|h\|_X\) in any finite spatial Green norm \(X\), and the literal left C¹ jets vanish. Yet at \(s=0\),
\[
\delta_N(0)=u_{1,N}(0,\cdot)=0,\qquad
\|\partial_su_{1,N}(0,\cdot)\|_X
=\varepsilon N\|h\|_X\longrightarrow\infty.\tag{SZ10}
\]
This is a counterexample **only to deducing temporal control from the existing fixed-time theorem types**: in the actual Lean packet \`ActualHartreeSpectralFourPieceMovingPacket\`, the \`delta : ℝ → ℂ\` field carries no continuity, differentiated selection equation, or PDE velocity constraint. It is **not** a counterexample to the sought physically selected Hartree orbit. To repair the type-to-theorem bridge, derive \(\delta'\) from the same two-real-speed compatibility system and PDE, and establish time-regularity of the genuine source and moving Kummer coefficients.

## 5. Strict acceptance boundary

Directly checked GitHub CI 43124289518 / original job 130872307063 is **Success** under Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, \`--trust=0\`, \`-DwarningAsError=true\`, exact \`#check\` and \`#print axioms\` on four specified existing targets; the only axioms are \`propext\`, \`Classical.choice\`, \`Quot.sound\`. That target is the exact nonlinear telescope, and does NOT certify (SZ1)–(SZ10).

The missing original \(\S2.13\) chain remains: actual Hartree source \(F_s\) and unique real selector \(\delta'\) with time-positive weighted bounds; moving \(p_s,q_s,\rho'\) and source-matched regular IVP mode; full untruncated seven-linear Hartree commutator; complete four-region positive-order strong residual and parameter Lipschitz; finite profile recurrence. The final PDE-derived Type-II rate remains separate. **No new Lean declaration is claimed; original retained count stays 11/13 (84.62%).**
