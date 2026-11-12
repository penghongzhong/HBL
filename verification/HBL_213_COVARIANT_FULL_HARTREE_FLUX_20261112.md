# HBL §2.13 — covariant full Hartree flux: exact cancellation of moving-scale transport

12 November 2026. **Paper proof, not strict Lean. Original revised environment count remains 11/13.** This note strengthens the earlier untruncated near-diagonal weak-flux estimate. It makes no claim that the full four-zone nonlinear PDE remainder has gained positive renormalized-time order.

Let \(K(x)=|x|^{-2}\) on \(\mathbb R^3\), \(\Lambda u=\frac12u+x\cdot\nabla u\) and \(\Phi(u)=|u|^2\overline u\). For smooth compactly supported \(\rho\), a change of variables gives
\[
 K*[\lambda^2\rho(\lambda\cdot)](x)=\lambda(K*\rho)(\lambda x).
\tag{CF1}
\]
Consequently, upon differentiating at \(\lambda=1\),
\[
 K*(2\rho+x\cdot\nabla\rho)=(1+x\cdot\nabla)(K*\rho).
\tag{CF2}
\]
The identity holds distributionally under natural integrability and approximation assumptions; in particular it does not replace the singular gradient of \(K\) by an absolutely integrable kernel.

Let \(U=V+Z\), \(\rho=|U|^4-|V|^4\) and \(Q=K*\rho\). Since
\(4\operatorname{Re}(\Phi(u)\Lambda u)=2|u|^4+x\cdot\nabla|u|^4\),
\[
 \boxed{[\partial_s+b(1+x\cdot\nabla)]Q
  =K*4\operatorname{Re}\{\Phi(U)(Z_s+b\Lambda Z)
       +(\Phi(U)-\Phi(V))(V_s+b\Lambda V)\}.}
\tag{CF3}
\]
All fields here are the same actual physical orbit, with no independent source or time-order assumption.

Now impose the **genuine physical** three-dimensional critical Hartree equation
\[
 iz_t+\Delta z+\mathcal N_H(z)=0,\qquad
 \mathcal N_H(z)=\kappa_H(K*|z|^4)|z|^2z,\quad \kappa_H\in\mathbb R,
\]
and \(Z(s,x)=\sqrt{\ell(s)}z(t(s),\ell(s)x)\),
\(\ell_s=-b\ell,\ t_s=\ell^2\). Critical scaling gives the exact
\[
 Z_s+b\Lambda Z=i(\Delta Z+\mathcal N_H(Z)).
\tag{CF4}
\]
Integration by parts in distributions, followed by the homogeneity identity, proves
\[
 \boxed{[\partial_s+b(1+x\cdot\nabla)]Q
       =\sum_{j=1}^3(\partial_j K)*J_j+K*R_{\rm cov},}
\tag{CF5}
\]
where
\[
\begin{aligned}
J&=4\operatorname{Re}(i\Phi(U)\nabla Z),\\
R_{\rm cov}&=-4\operatorname{Re}(i\nabla\Phi(U)\cdot\nabla Z)
 +4\operatorname{Re}(i\Phi(U)\mathcal N_H(Z))\\
&\qquad+4\operatorname{Re}((\Phi(U)-\Phi(V))(V_s+b\Lambda V)).
\end{aligned}
\tag{CF6}
\]
The bare term \(b\Phi(U)\Lambda Z\) from the noncovariant derivative estimate **cancels exactly**. This is a constructive simplification, not a bound on the remaining covariant reference velocity.

With the Fourier convention \(\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)dx\), one has \(\widehat K=2\pi^2/|\xi|\). Plancherel for the vector Riesz multiplier and \(K:L^{6/5}\to L^2\) give
\[
\boxed{
\|[\partial_s+b(1+x\cdot\nabla)]Q\|_2
\le 2\pi^2\|J\|_2+C_{\rm HLS}\|R_{\rm cov}\|_{6/5}.}
\tag{CF7}
\]
If \(M=\max(\|U\|_\infty,\|V\|_\infty)\) and all displayed products have sufficient integrability, then
\[
\begin{aligned}
\|[\partial_s+b(1+x\cdot\nabla)]Q\|_2
\le{}&8\pi^2M^3\|\nabla Z\|_2\\
&+C_{\rm HLS}\{12M^2\|\nabla U\|_3\|\nabla Z\|_2
 +4M^3\|\mathcal N_H(Z)\|_{6/5}\\
&\hspace{28mm}+4\|(\Phi(U)-\Phi(V))(V_s+b\Lambda V)\|_{6/5}\}.
\end{aligned}
\tag{CF8}
\]

For **pure actual physical radiation**, set \(H(t,y)=K*|z(t)|^4(y)\) and \(Q_Z=K*|Z|^4\). Directly from CF1,
\[
 Q_Z(s,x)=\ell H(t,\ell x),\qquad
 \boxed{[\partial_s+b(1+x\cdot\nabla)]Q_Z
   =\ell^3 H_t(t,\ell x).}
\tag{CF9}
\]
Thus, if the genuine physical trajectory has \(H_t(t)\in L^2\),
\[
 \boxed{\|[\partial_s+b(1+x\cdot\nabla)]Q_Z\|_2
 =\ell^{3/2}\|H_t(t)\|_2.}
\tag{CF10}
\]
This is derived from the original PDE rather than a postulated smallness order. For a physical Hartree solution with a justified locally uniform \(H^2\) bound, the \(V=0,b=0\) version of CF7 gives local uniform \(L^2\) control on \(H_t\): use \(H^2\hookrightarrow L^\infty\), \(\nabla z\in L^2\cap L^6\), HLS and \(\mathcal N_H(z)\in L^{6/5}\). No uniform physical \(H^2\) bound is being claimed here without a legitimate initial-data/flow argument.

The scaled physical source \(E_{\ell,t}(x)=\ell^3H_t(t,\ell x)\) also has the following **conditional** precise parameter bounds. If \(H_t,y\cdot\nabla H_t\in L^2\), then
\[
 \|E_{\ell_1,t}-E_{\ell_0,t}\|_2
 \le\int_{\ell_0}^{\ell_1}\lambda^{1/2}
 \|3H_t(t)+y\cdot\nabla H_t(t)\|_2\,d\lambda,
 \quad 0<\ell_0\le\ell_1.
\tag{CF11}
\]
If \(H_{tt}\in L^\infty_tL^2_x\) between \(t\) and \(t'\), then
\[
 \|E_{\ell,t}-E_{\ell,t'}\|_2
 \le\ell^{3/2}|t-t'|\sup_\tau\|H_{tt}(\tau)\|_2.
\tag{CF12}
\]

**Unclosed original-paper gate:** CF5 must be matched with the actual moving Kummer transport operator, including its endpoints and the unique real Cramer selector. Bound the genuine covariant reference velocity \(V_s+b\Lambda V\), its full mixed Hartree interactions, all four-zone PDE residuals in the *original weighted norm*, plus parameter Lipschitz and finite physical recursion. No relation \(\ell(s)\lesssim s^{-c}\) or Type-II rate may be assumed. An \(\ell^{3/2}\) **scale gain** is not automatically a positive **renormalized-time** \(s^{-\delta}\) gain. Existing strict CIs 43135036481 (fixed-time three C1 joins) and 43124289518 (nonlinear PDE telescope) do not certify CF1–CF12. **Formal original acceptance: 11/13.**
