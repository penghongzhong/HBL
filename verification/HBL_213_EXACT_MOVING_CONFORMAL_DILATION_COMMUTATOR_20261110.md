# HBL §2.13 — exact MOVING conformal Hartree transport and dilation commutator (10 November 2026)

**Status and boundary.** This is a direct, unformalized paper calculation for the *same original* three-dimensional quartic-density inverse-square Hartree equation. It produces the exact moving-scale/phase terms and a nonlinear scaling commutator that does not lose spatial derivatives. It is **not** a projected Kato estimate, positive-time residual gain, actual finite-profile recursion, or a PDE-derived Type-II rate. **Original revised theorem environments remain 11/13.** No new \`--trust=0\` Lean theorem or CI is claimed.

## 1. Physical PDE, nonlinear derivative and exact homogeneity

Take \(\kappa_{\mathrm H}=3/\pi^2\), \(K(x)=|x|^{-2}\), and
\[
\mathcal H(u)=-\Delta u-\mathcal N(u),\quad
\mathcal N(u)=\kappa_{\mathrm H}(K*|u|^4)|u|^2u,\quad
iu_t=\mathcal H(u).
\]
For smooth rapidly decaying complex \(u,v\), the **real** Fréchet derivative is
\[
\begin{aligned}
\mathcal N'(u)[v]={}&
4\kappa_{\mathrm H}
 \bigl(K*(|u|^2\operatorname{Re}(\bar u v))\bigr)|u|^2u\\
&+\kappa_{\mathrm H}(K*|u|^4)
 \bigl(|u|^2v+2\operatorname{Re}(\bar u v)u\bigr).
\end{aligned}
\tag{M1}
\]
This retains the complete nonlocal real-channel coupling. Define the physical energy-critical dilation
\[
(\mathsf S_\rho u)(x)=\rho^{1/2}u(\rho x),\qquad
\Lambda u=\left.\partial_\rho\mathsf S_\rho u\right|_{\rho=1}
 =\tfrac12u+x\cdot\nabla u.
\]
Changing variables \(z=\rho y\) in the *actual* Riesz convolution gives
\[
(K*|\mathsf S_\rho u|^4)(x)
 =\rho(K*|u|^4)(\rho x),\qquad
\mathcal H(\mathsf S_\rho u)=\rho^{5/2}\mathcal H(u)(\rho x).
\tag{M2}
\]
Differentiate in \(\rho\) at \(1\) to obtain the exact **nonlinear** commutator identity
\[
\boxed{\quad
\mathcal H'(u)[\Lambda u]-\Lambda\mathcal H(u)
 =2\mathcal H(u).
\quad}
\tag{M3}
\]
Here \(\mathcal H'(u)\) differentiates the genuinely nonlocal quartic convolution; (M3) is **not** linearity of Hartree, a cancellation assumption, or a residual size estimate. It holds first for Schwartz fields (or smooth fields with sufficient absolute integrability) and then on any domain where these operations are justified.

## 2. Exact sphere coordinate form of the moving scaling vector field

Let \(W(x)=(1+|x|^2)^{-1/2}\),
\[
\Xi(x)=\left(\frac{2x}{1+|x|^2},
\frac{|x|^2-1}{1+|x|^2}\right)\in\mathbb S^3,\quad
h(\xi)=\xi_4,\quad m(\xi)=\frac{(1-h)^2}{4}.
\]
Since \(h(\Xi(x))=(r^2-1)/(r^2+1)\), direct differentiation gives
\[
x\cdot\nabla_x\Xi(x)
 =(\nabla_{\mathbb S^3}h)(\Xi(x)),\qquad
x\cdot\nabla_x\log W=-(1+h\circ\Xi)/2.
\tag{M4}
\]
Thus if \(u=W(\Phi\circ\Xi)\),
\[
\boxed{\quad
\Lambda u=W\bigl((D\Phi)\circ\Xi\bigr),\qquad
D=\nabla_{\mathbb S^3}h\cdot\nabla_{\mathbb S^3}-\frac h2.
\quad}
\tag{M5}
\]
The conformal elliptic operator is \(A=3-4\Delta_{\mathbb S^3}\). The sphere identities
\(\Delta h=-3h\), \(\nabla^2h=-h\,g_{\mathbb S^3}\) imply
\[
[\Delta_{\mathbb S^3},D]f=-2h\Delta f+\tfrac32hf,\qquad
\boxed{[A,D]f=-2hAf}.
\tag{M6}
\]
Also \((\nabla h)\cdot\nabla m=-2(1+h)m\), so
\[
\boxed{\quad[mA,D]f=2mAf.\quad}
\tag{M7}
\]
Both identities are verified independently in the radial variable \(h\), where
\(\Delta f=(1-h^2)f''-3hf'\), \(Df=(1-h^2)f'-hf/2\).
The commutator of the *moving scaling generator* with the **actual** conformal Laplacian has an exact controlled form, rather than a generic unbounded second-order error.

Set
\[
\mathscr K f(\xi)=\int_{\mathbb S^3}|\xi-\eta|^{-2}f(\eta)\,d\omega(\eta),\quad
B(\Phi)=\mathscr K(|\Phi|^4)|\Phi|^2\Phi,\quad
\mathcal M(\Phi)=A\Phi-\frac{\kappa_{\mathrm H}}2B(\Phi).
\tag{M8}
\]
The exact original Hartree identity is
\(\mathcal H(W\Phi\circ\Xi)=W^5(\mathcal M(\Phi)\circ\Xi)\).
By (M3)–(M5), using the correct output weight \(W^5\), one obtains for the **full nonlocal nonlinear operator**
\[
\boxed{\quad
\mathcal M'(\Phi)[D\Phi]
 =(\nabla h)\cdot\nabla\mathcal M(\Phi)
  -\frac{5h}{2}\mathcal M(\Phi).
\quad}
\tag{M9}
\]
Equivalently, for \(\mathcal R(\Phi)=m\mathcal M(\Phi)\),
\[
\boxed{\quad
\mathcal R'(\Phi)[D\Phi]-D\mathcal R(\Phi)
 =2\mathcal R(\Phi).
\quad}
\tag{M10}
\]
This is the exact derivative-level nonlocal cancellation needed to avoid **inventing** a separate scaling-commutator source envelope. Crucially, it gives no bound on \(\mathcal R(\Phi)\) or \(\Phi_s\) without an actual PDE orbit.

## 3. True time-dependent scale and phase, with NO omitted Hartree terms

Let \(\lambda(t)>0\) be \(C^1\), \(s_t=\lambda^{-2}\), \(\vartheta(s)=\gamma(t(s))\),
\(y=x/\lambda(t)\), and write a genuine moving field
\[
u(t,x)=e^{i\gamma(t)}\lambda(t)^{-1/2}
 W(y)\Phi(s,\Xi(y)),\qquad
 b(s)=\lambda_s/\lambda.
\tag{M11}
\]
The chain rule (using the **same** \(\Lambda\) as above) gives exactly
\[
i\partial_tu
=e^{i\gamma}\lambda^{-5/2}W(y)
  [i\Phi_s-\vartheta_s\Phi-i bD\Phi]\circ\Xi(y).
\tag{M12}
\]
Since the complete quartic-density convolution scales exactly as in (M2),
\[
\mathcal H(u)=e^{i\gamma}\lambda^{-5/2}W(y)^5
 \mathcal M(\Phi)(s,\Xi(y)).
\]
Therefore the complete moving-frame physical equation, **without replacing the Hartree kernel**, is
\[
\boxed{\quad
i\Phi_s=\mathcal R(\Phi)+\vartheta_s\Phi+i bD\Phi,\qquad
\mathcal R(\Phi)=m\left[(3-4\Delta_{\mathbb S^3})\Phi
-\frac{3}{2\pi^2}\mathscr K(|\Phi|^4)|\Phi|^2\Phi\right].
\quad}
\tag{M13}
\]
In particular, the previously derived *fixed-frame* equation is recovered when \(b=\vartheta_s=0\). The exact commutator (M10) removes a generic second-derivative **scaling-transport commutator** in this frame; it does **not** remove the explicit \(ibD\Phi\), moving piecewise interfaces, selected two-speed derivatives or source norms.

## 4. Precisely what three genuine C¹ interfaces imply (and do not imply)

Suppose at each \(s\), a four-region radial \(U(s,r)\) is piecewise \(C^3_r\), piecewise \(C^1_s\) with smooth moving interfaces \(R_j(s)>0\), and actual traces satisfy
\([U]_{R_j}=[\partial_rU]_{R_j}=0\). In the distributional spatial variable,
\[
\partial_r^2U=(\partial_r^2U)_{\mathrm{piecewise}},
\qquad
(\partial_r^2+2r^{-1}\partial_r)U
 =(\Delta_rU)_{\mathrm{piecewise}},
\tag{M14}
\]
and the moving-time derivative has no interface measure because its coefficient is
\(-R'_j(s)[U]_{R_j}=0\). Thus the already verified actual three-C¹ joins suffice to eliminate interface Dirac measures from the **undifferentiated physical PDE residual**.

But a further radial derivative produces
\[
\boxed{\quad
\partial_r^3U=(\partial_r^3U)_{\mathrm{piecewise}}
 +\sum_j[\partial_r^2U]_{R_j}\,\delta_{R_j}.
\quad}
\tag{M15}
\]
Accordingly, to place the **spatial derivative of the PDE residual** in an ordinary weighted \(L^2\), the true C² jumps must vanish or be repaired; alternatively one must **prove** a compatible distributional Morawetz-dual estimate controlling these exact interface measures. Three C¹ conditions or nonlinear telescoping alone do not give this estimate.

**Next genuine proof obligation:** Insert the *same-source* selected Fredholm/Green/spectral four-region packet into (M13), exploit (M10) for the full nonlinear dilation commutator, and control the remaining interface curvature measures, modulation and endpoint derivatives, all nonlocal cross interactions, projected dual Kato source norm and time/parameter powers. Only after actual positive-order and Lipschitz bounds, a full nonlinear orbit and finite recursion, can §2.13 and the dynamic Type-II theorem be accepted.


## 5. Explicit obstruction: the untruncated dilation forcing is NOT phase Fredholm-compatible

For the exact physical bubble and critical scaling mode,
\[
W(r)=(1+r^2)^{-1/2},\qquad
\Lambda W=\frac12W+rW'
 =\frac{1-r^2}{2(1+r^2)^{3/2}}
 =-\frac h2 W.
\tag{M16}
\]
The phase-channel zero-resonance moment of the bare scale-transport forcing can be **integrated exactly**:
\[
\begin{aligned}
\mathcal M_{\Lambda}(R)
 &:=\int_0^Rr^2W(r)\Lambda W(r)\,dr\\
 &=\int_0^R\frac{r^2(1-r^2)}{2(1+r^2)^2}\,dr\\
 &=\boxed{\arctan R-\frac R2-\frac{R}{2(1+R^2)}}
 =-\frac R2+\frac\pi2+O(R^{-1}).
\end{aligned}
\tag{M17}
\]
In particular the whole-space moment \(\int_0^\infty r^2W\Lambda W\,dr\) **does not exist as a finite quantity** (it diverges to \(-\infty\)), and
\((1+r^2)\Lambda W\notin L^2(\mathbb R^3)\).
For a nonzero modulation slope \(b=\lambda_s/\lambda\), the bare bubble \(\Phi\equiv1\) has the exact moving-source mismatch
\[
i\Phi_s-\mathcal R(\Phi)-\vartheta_s\Phi-ibD\Phi
 =-\vartheta_s+\frac{ib}{2}h.
\tag{M18}
\]
The real scalar phase speed \(\vartheta_s\) cannot cancel the imaginary spatially varying transport term \(ibh/2\). This is a **failure of the bare untruncated bubble strategy**, not a nonexistence result for a corrected four-region Hartree orbit.

**Consequences for the shortest chain:** the previously derived weighted-source elliptic phase inverse, whose domain requires \((1+r^2)F\in L^2\) and \(\int WF=0\), cannot be applied to this isolated bare scaling source. The genuine Fredholm/Kummer correction and the physical outer radiation must be shown to cancel the phase-resonant far-field moment *in the complete same-orbit residual*. No independent moment orthogonality, artificial cutoff or presumed smallness can replace that proof. This is the exact place where a stationary-resolvent shortcut would otherwise smuggle in a missing hypothesis.

**Strict acceptance:** existing exact-target CI 42536552509 (nonlinear spectral finite-PDE telescoping) and 42854633900 (original source C² jump) have succeeded in their actual prior statements; neither proves (M13)–(M15) in Lean. No new axiom, sorry, admit or acceptance increment is asserted. **11/13 (84.62%).**
