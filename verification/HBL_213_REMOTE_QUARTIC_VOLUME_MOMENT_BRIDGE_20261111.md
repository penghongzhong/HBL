# HBL §2.13: exact remote Hartree monopole and the missing volume-weighted quartic moment

11 November 2026. **Paper-level mathematical lemma only; not a new strict Lean declaration. Revised original count remains 11/13.**

## 1. Genuine inverse-square radial kernel; rank-one exterior asymptotic

For a real radial density \(\rho\), write
\[
Q_\rho(r)=(|x|^{-2}*\rho)(r)
=\frac{2\pi}{r}\int_0^\infty s\,\rho(s)
  \log\frac{r+s}{|r-s|}\,ds,\qquad r>0. \tag{RM1}
\]
If \(\rho\) is supported in \([0,R]\), \(r>R\), and
\[
m_0(\rho)=\int_0^R s^2\rho(s)\,ds,\quad
m_{2j}(\rho)=\int_0^R s^{2j+2}\rho(s)\,ds,\quad
M_2(\rho)=\int_0^R s^4|\rho(s)|\,ds,
\]
then the geometric logarithm expansion, uniform for \(s/r\le R/r<1\), gives the **exact** series
\[
Q_\rho(r)=\frac{4\pi}{r^2}\sum_{j=0}^\infty
 \frac{m_{2j}(\rho)}{(2j+1)r^{2j}}. \tag{RM2}
\]
In particular,
\[
\boxed{
\left|Q_\rho(r)-\frac{4\pi m_0(\rho)}{r^2}\right|
 \le\frac{4\pi M_2(\rho)}{3r^4[1-(R/r)^2]},\quad
\left|Q_\rho'(r)+\frac{8\pi m_0(\rho)}{r^3}\right|
 \le\frac{16\pi M_2(\rho)}{3r^5[1-(R/r)^2]}. }\tag{RM3}
\]
The derivative estimate follows by termwise differentiation; for \(j\ge1\), \((2j+2)/(2j+1)\le4/3\).

For the **literal backward overlap** of (WG9), take \(R=L/3\) and \(3L/4\le r\le L\). Then \(R/r\le4/9\), and
\[
\boxed{
\left|Q_\rho(r)-\frac{4\pi m_0}{r^2}\right|
 \le \frac{1024\pi}{195 L^4}M_2,\qquad
\left|Q_\rho'(r)+\frac{8\pi m_0}{r^3}\right|
 \le \frac{16384\pi}{585 L^5}M_2. }\tag{RM4}
\]
These explicit constants use only \(4/9\), not a fictitious compactly supported full Hartree interaction.

## 2. The exact nonlocal overlap error is linear in this remote moment

Let \(f=u-v\) be supported in \(0<r<L/3\), let \(\eta_L\) be the original flat cutoff with \(\eta_L=0\) on \(r\le5L/8\) and \(\eta_L=1\) on \(r\ge3L/4\), and assume \(u=v\) outside \(\mathrm{supp}\,f\). Then \(U=u-\eta_Lf=u\) **globally**, but the original seven-linear nonlinearity still has, for \(3L/4<r<L\),
\[
\begin{split}
{\cal C}_{\eta_L}(u,v)(r)
 &=\kappa_H |u(r)|^2u(r)\,
     (|x|^{-2}*\rho)(r),\\
\rho(s)&=|u(s)|^4-|v(s)|^4. \tag{RM5}
\end{split}
\]
Consequently,
\[
\boxed{
\left|{\cal C}_{\eta_L}(u,v)(r)
 -4\pi\kappa_H |u(r)|^2u(r)\,\frac{m_0(\rho)}{r^2}\right|
\le|\kappa_H||u(r)|^3
    \frac{1024\pi}{195L^4}M_2(\rho). }\tag{RM6}
\]
This identifies the exact leading **rank-one monopole obstruction** behind the no-go in (NC6)--(NC8): even identically zero local mismatch \(f=f'=\Delta_rf=0\) on the overlap does not remove the remote quartic-density moment. If \(m_0(\rho)=0\), the remote-inner contribution gains two spatial powers, with the explicit remainder (RM4). Neither \(m_0=0\) nor its smallness has been deduced from the selected real two-speed compatibility equations.

For general noncompact remote differences, (RM2)--(RM6) apply only to the **inner** part \(\rho_{<}=\rho\,{\bf1}_{[0,L/3]}\); the outer part \(Q_{\rho_{\ge}}\), including the singular interaction near \(s=r\), must still be estimated with the genuine full kernel. The moment expansion must never be used to discard this remaining nonlocal contribution.

## 3. This moment is NOT the already-audited inverse-square moment

The repository's
\`HBL/TypeIIDynamicSelection/ActualRadiation3DMoment.lean\` proves
\[
m_{\mathrm{inv}}(z)=\int_{\mathbb R^3}|x|^{-2}|z(|x|)|^4dx
=4\pi\int_0^\infty|z(r)|^4\,dr. \tag{RM7}
\]
The coefficient in (RM2), by contrast, is
\[
m_{\mathrm{vol}}(z)=\int_{\mathbb R^3}|z(|x|)|^4dx
=4\pi\int_0^\infty r^2|z(r)|^4\,dr
=4\pi m_0(|z|^4). \tag{RM8}
\]
These are **different physical moments**. The strictly verified evolution of \(m_{\mathrm{inv}}\) and its center-radius identity do not, by their theorem types, prove the far-field \(m_{\mathrm{vol}}\) estimate. This is not a claim of an error in the former statements; it is a missing interface for the latter.

Indeed choose nonzero \(\phi\in C_c^\infty((1,2))\), \(z_R(r)=R^{-1}\phi(r/R)\) for \(R\ge1\). The Strauss bound \(\sup_{r>0}r|z_R(r)|\le 2\|\phi\|_\infty\) is uniform, but
\[
m_{\mathrm{inv}}(z_R)=4\pi R^{-3}\int_1^2|\phi(q)|^4dq,\qquad
m_{\mathrm{vol}}(z_R)=4\pi R^{-1}\int_1^2q^2|\phi(q)|^4dq. \tag{RM9}
\]
Thus their ratio grows like \(R^2\), even within such a Strauss-bounded family.

## 4. A genuine PDE producer for the new moment, with no assigned time rate

If a sufficiently smooth decaying complex field solves the **actual** three-dimensional quartic-density Hartree equation
\[
 i\partial_t z+\Delta z+
 \kappa_H(|x|^{-2}*|z|^4)|z|^2z=0,
\]
then, with \(J=\operatorname{Im}(\bar z\nabla z)\), the real Hartree potential cancels in the mass-density identity,
\[
 \partial_t|z|^2=-2\nabla\!\cdot J,\qquad
 \boxed{\frac{d}{dt}m_{\mathrm{vol}}(z)
 =4\int_{\mathbb R^3}\nabla(|z|^2)\cdot J\,dx,\quad
 \left|\frac{d}{dt}m_{\mathrm{vol}}(z)\right|
 \le8\int_{\mathbb R^3}|z|^2|\nabla z|^2dx.} \tag{RM10}
\]
All integrations by parts require genuine integrability/decay. The right side is not controlled by homogeneous \(\dot H^1\) alone. If a parametrix instead satisfies \(i z_t+\Delta z+{\cal N}_H(z)={\cal R}\), the exact additional term is
\[
4\int_{\mathbb R^3}|z|^2\operatorname{Im}(\bar z{\cal R})\,dx. \tag{RM11}
\]
No estimate of \({\cal R}\) or of the integral in (RM10) is inserted as an independent time-order premise.

**Shortest next physical link:** use the existing real-source/selected-speed and moment-flux modules to construct (i) a same-orbit far-density **difference** moment with the time and parameter bounds actually implied by the PDE, (ii) the weighted second moment and near-diagonal outer kernel, and (iii) the weak-C¹ backward-overlap source in a common topology. Only after their insertion into the full four-region residual may a positive time order, finite recursion, or dynamic II-type rate be claimed. No new strict Lean run audits (RM1)--(RM11). Original environment acceptance stays 11/13.
