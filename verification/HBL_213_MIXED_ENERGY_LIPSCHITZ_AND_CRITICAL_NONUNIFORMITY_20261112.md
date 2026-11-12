# HBL §2.13: critical mixed channel in the physical energy topology

12 November 2026 UTC. **Analytic proof only; not a Lean theorem. Revised original acceptance remains 11/13.**

## 1. Strong-energy well-posedness and Lipschitz bound of the genuine mixed term

Work on \(\mathbb R^3\), with the **original** quartic inverse-square Hartree kernel \(K(x)=|x|^{-2}\). For complex-valued \(z\in\dot H^1(\mathbb R^3)\), put
\[
 {\cal C}(z)=K*\left(|x|^{-1}\operatorname{Re}z\,|z|^2\right).
 \tag{EL1}
\]
Here \(z\) is an energy-class radiation snapshot, *not* an independently stipulated error envelope. Let \(S_3\) denote the homogeneous Sobolev constant \(\|u\|_6\le S_3\|\nabla u\|_2\), and \(C_{\rm HLS}\) the constant for \(K*:L^{6/5}\to L^2\). Define \(A_H=2C_{\rm HLS}S_3^2\).

**Proposition.** The nonlinear map \({\cal C}:\dot H^1(\mathbb R^3;\mathbb C)\to L^2(\mathbb R^3;\mathbb R)\) is a continuous cubic polynomial and is Fréchet smooth as a real map. For all \(z,w,h\in\dot H^1\),
\[
 \boxed{\ \|{\cal C}(z)\|_2\le A_H\|\nabla z\|_2^3,\quad
 \|{\cal C}(z)-{\cal C}(w)\|_2
 \le A_H(\|\nabla z\|_2^2+\|\nabla z\|_2\|\nabla w\|_2+
                  \|\nabla w\|_2^2)\|\nabla(z-w)\|_2.\ }\tag{EL2}
\]
The **actual** Fréchet derivative and its bound are
\[
 D{\cal C}(z)[h]
 =K*\left[\frac{\operatorname{Re}h\,|z|^2+
       2\operatorname{Re}z\,\operatorname{Re}(\bar z h)}{|x|}\right],
 \qquad
 \|D{\cal C}(z)[h]\|_2\le3A_H\|\nabla z\|_2^2\|\nabla h\|_2.
 \tag{EL3}
\]
For a physical Hartree path differentiable in \(\dot H^1\), its mixed-channel derivative is (EL3) with \(h=z_t\); energy-class continuity alone yields parameter continuity but does not yield such time differentiability.

**Proof.** Define the real trilinear map
\[
 {\cal T}(a,b,c)=K*\left[\frac{\operatorname{Re}a\,
                   \operatorname{Re}(b\bar c)}{|x|}\right].
\]
The *three-dimensional Hardy* and homogeneous Sobolev inequalities, followed by Hölder and the genuine HLS estimate, give
\[
 \begin{split}
 \|{\cal T}(a,b,c)\|_2
 &\le C_{\rm HLS}\|a/|x|\|_2\,\|b\|_6\|c\|_6\\
 &\le 2C_{\rm HLS}S_3^2
  \|\nabla a\|_2\|\nabla b\|_2\|\nabla c\|_2.
 \end{split}\tag{EL4}
\]
Since \({\cal C}(z)={\cal T}(z,z,z)\), a three-slot telescoping of the trilinear product proves (EL2), and real polynomial differentiation proves (EL3). No radial, Schwartz, \(L^\infty\), or \(H^2\) hypothesis enters these inequalities.

The exact energy-critical scaling \(z_\lambda(x)=\lambda^{1/2}z(\lambda x)\) satisfies
\[
 \boxed{\ {\cal C}(z_\lambda)(x)=\lambda^{3/2}{\cal C}(z)(\lambda x),\quad
 \|{\cal C}(z_\lambda)\|_2=\|{\cal C}(z)\|_2,\quad
 \|\nabla z_\lambda\|_2=\|\nabla z\|_2.\ }\tag{EL5}
\]
Thus (EL2) provides a **source-faithful energy/Lipschitz bridge**, but no small factor solely from critical scaling.

## 2. Static scale derivative: fixed-energy convergence, no uniform energy-ball rate

To make the precise limitation of the earlier global mixed-flux estimate explicit, set
\[
 g_\ell(x)=\frac{\sqrt\ell}{\sqrt{\ell^2+|x|^2}},\quad
 \rho_{\ell,z}=|z+g_\ell|^4-g_\ell^4,\quad
 {\cal E}_\ell(z)=K*\left[
 \ell^{1/2}\partial_\ell\rho_{\ell,z}
 -2|x|^{-1}\operatorname{Re}z\,|z|^2\right],\quad 0<\ell\le1.
 \tag{EL6}
\]
**The derivative holds \(z\) fixed**: it is the spatial-scale partial derivative in the exact critical-clock identity, not a total derivative of a family of radiations. The terms of \(\ell^{1/2}\partial_\ell\rho_{\ell,z}\) are
\[
 4k_{1,\ell}\operatorname{Re}z\,|z|^2
 +k_{2,\ell}\bigl(2|z|^2+4(\operatorname{Re}z)^2\bigr)
 +4k_{3,\ell}\operatorname{Re}z,\tag{EL7}
\]
where
\[
 k_{1,\ell}=\ell^{1/2}\partial_\ell g_\ell,\quad
 k_{2,\ell}=\ell^{1/2}\partial_\ell(g_\ell^2),\quad
 k_{3,\ell}=\ell^{1/2}\partial_\ell(g_\ell^3).
\]
Exact radial scaling shows
\[
 |k_{1,\ell}(x)|\le\frac{3}{2|x|},\qquad
 \sup_{\ell>0}\|k_{2,\ell}\|_2<\infty,\qquad
 \sup_{\ell>0}\|k_{3,\ell}\|_{3/2}<\infty.
 \tag{EL8}
\]
Moreover \(k_{1,\ell}(x)\to(2|x|)^{-1}\), while \(k_{2,\ell},k_{3,\ell}\to0\) pointwise for \(x\ne0\).

For **each fixed** \(z\in\dot H^1\), the first term in (EL7), after subtracting the term in (EL6), tends to zero in \(L^{6/5}\) by dominated convergence using (EL4). The second and third terms also tend to zero in \(L^{6/5}\): prove this first for bounded compactly supported \(z\) (uniform \(L^2\) and \(L^{3/2}\) kernel norms plus convergence in every smaller exponent on bounded sets), then approximate an arbitrary energy-class \(z\) in \(L^6\). HLS therefore yields
\[
 \boxed{\ {\cal E}_\ell(z)\longrightarrow0\quad\hbox{in }L^2
       \quad(\ell\downarrow0),\ \text{for each fixed }z\in\dot H^1.\ }\tag{EL9}
\]
The same estimates give local energy-Lipschitz continuity **uniformly** over \(0<\ell\le1\):
\[
 \|{\cal E}_\ell(z)-{\cal E}_\ell(w)\|_2
 \le C_{\rm HLS,S_3}(1+R+R^2)\|\nabla(z-w)\|_2,
 \quad\|\nabla z\|_2+\|\nabla w\|_2\le R.
 \tag{EL10}
\]
Thus (EL9) is uniform if \(z\) ranges over a *compact subset* of \(\dot H^1\), but not over a merely bounded subset.

**Sharp obstruction: no uniform \(o(1)\) on energy balls.** Fix a nonnegative nonzero radial \(\psi\in C_c^\infty(\{2<|x|<3\})\), chosen small in amplitude, and define \(z_\ell(x)=\ell^{-1/2}\psi(x/\ell)\). Then \(\|\nabla z_\ell\|_2=\|\nabla\psi\|_2\), but exact scaling of (EL6) gives
\[
 \boxed{\ {\cal E}_\ell(z_\ell)(x)
       =\ell^{-3/2}{\cal E}_1(\psi)(x/\ell),\qquad
       \|{\cal E}_\ell(z_\ell)\|_2=\|{\cal E}_1(\psi)\|_2>0.\ }\tag{EL11}
\]
To verify strict positivity, write
\[
 g_1(r)=(1+r^2)^{-1/2},\quad
 k_{1,1}(r)=\frac{r^2-1}{2(1+r^2)^{3/2}},
\]
so the density defining \({\cal E}_1(\psi)\), for real \(\psi\), equals
\[
 (4k_{1,1}-2/r)\psi^3
 +12k_{1,1}g_1\psi^2+12k_{1,1}g_1^2\psi.
 \tag{EL12}
\]
For \(2<r<3\), \(k_{1,1}>0\), and the linear term is strictly positive on the support of \(\psi\). Choosing its amplitude sufficiently small makes (EL12) nonzero; its convolution with the positive inverse-square kernel cannot vanish identically. The resulting \(\psi\) can be used as smooth finite-energy initial data for a local physical Hartree trajectory, so this is an obstruction to an **energy-only uniform analytic estimate**, not an assertion about the unknown selected HBL solution.

In particular the exact covariant original mixed-potential identity from the preceding note reads
\[
 T_\ell^{-1}D_bQ+2b{\cal C}(z)
  =-b{\cal E}_\ell(z)
   +\ell^{3/2}K*\partial_t\rho_{\ell,z},\qquad
 (T_\ell f)(x)=\ell^{3/2}f(\ell x).
 \tag{EL13}
\]
(EL9) can control the **static** derivative for a fixed energy-class radiation or a compact physical energy path; it does **not** quantify the time term nor produce a positive renormalized-time exponent. (EL11) proves that an estimate uniform over all energy-bounded radiation snapshots with a scale-only decaying prefactor is impossible. For the original HBL theorem one must establish quantitative selected-orbit compactness/regularity or an actual Cramer/Kummer cancellation and then the weighted four-region nonlinear residual gain.

## 3. Exact verification boundary

GitHub strict fixed-time source-selection + quadratic spectral/three-C1 run [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481) and strict finite full-PDE telescope run [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518) are Success. The latter only proves the nonlinear telescope **identity**, not an improved residual. Their original logs audit Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, --trust=0, -DwarningAsError=true, exact #check/#print axioms, and only propext/Classical.choice/Quot.sound for those *existing* precise declarations. **(EL1)–(EL13) have not been Lean-verified.**

The original revised 13-environment ledger remains **11/13**. The original §2.13 is not accepted (no time-order gain, selected moving Kummer compatibility or full parameter Lipschitz/finite recursion), and the final dynamically selected Type-II blowup theorem remains unproved.
