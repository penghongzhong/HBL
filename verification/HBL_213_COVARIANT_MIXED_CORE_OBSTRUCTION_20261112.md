# HBL §2.13 — mixed core–radiation covariant-flux obstruction at the physical origin

12 November 2026 UTC. **Original revised manuscript: 11/13. Paper analysis only; NOT Lean-accepted.**

## 1. Exact original inverse-square quartic Hartree source

Let \(K(x)=|x|^{-2}\) on \(\mathbb R^3\), \(W(r)=(1+r^2)^{-1/2}\), and let \(z(t,y)\) be a smooth radial solution of the **actual** equation
\[
 iz_t+\Delta z+\kappa_H(K*|z|^4)|z|^2z=0.
\tag{MC1}
\]
At an observation time \(t\), assume \(z(t,\cdot)\) and \(z_t(t,\cdot)\) are radial Schwartz functions, with norms locally uniform in \(t\). These assumptions justify the following asymptotic calculation; they are **not** asserted for the unknown final HBL physical orbit. Define the actual critical scaling
\[
 Z_{\ell,t}(x)=\ell^{1/2}z(t,\ell x),\quad
 U_{\ell,t}=W+Z_{\ell,t},\quad
 Q_{\ell,t}=K*(|U_{\ell,t}|^4-|W|^4),\qquad 0<\ell\ll1.
\tag{MC2}
\]
The nonlinearity uses the genuine full nonlocal convolution and no local-NLS replacement.

At \(x=0\), the exact three-dimensional volume element cancels the original inverse-square kernel:
\[
 Q_{\ell,t}(0)=4\pi\int_0^\infty
 \bigl(|W(r)+\sqrt\ell\,z(t,\ell r)|^4-W(r)^4\bigr)\,dr.
\tag{MC3}
\]
Writing \(c(t)=\operatorname{Re}z(t,0)\), the exact **mixed quartic** expansion is
\[
\begin{aligned}
 |W+Z|^4-W^4={}&4W^3\operatorname{Re}Z\\
 &+2W^2|Z|^2+4W^2(\operatorname{Re}Z)^2\\
 &+4W(\operatorname{Re}Z)|Z|^2+|Z|^4.
\end{aligned}
\tag{MC4}
\]
Since \(\int_0^\infty W^3\,dr=1\), \(\int_0^\infty rW^3\,dr=1\) and \(\int_0^\infty W^2\,dr=\pi/2\), smoothness and Schwartz decay yield, locally uniformly in \(t\),
\[
\begin{aligned}
 Q_{\ell,t}(0)&=16\pi c(t)\sqrt\ell+O_t(\ell),\\
 \ell\partial_\ell Q_{\ell,t}(0)&=8\pi c(t)\sqrt\ell+O_t(\ell),\\
 \partial_tQ_{\ell,t}(0)&=16\pi c'(t)\sqrt\ell+O_t(\ell).
\end{aligned}
\tag{MC5}
\]
Here derivatives in \(\ell\) are taken **at fixed physical time** \(t\). To verify the errors, the linear term differs from \(16\pi c\sqrt\ell\) by at most \(16\pi\ell^{3/2}\|\partial_r z(t)\|_\infty\int rW^3dr\); the two quadratic terms are \(O(\ell)\) using \(W^2\in L^1(dr)\); the cubic term is \(O(\ell^{3/2}(1+|\log\ell|))\) using the Schwartz tail; and the pure term is exactly
\(4\pi\ell\int_0^\infty |z(t,y)|^4\,dy\).
Differentiation of each term gives the second line of (MC5) with the same \(O(\ell)\) remainder; the derivative of the cubic term remains \(O(\ell^{3/2}(1+|\log\ell|))\). The last line follows by the same expansion with one \(z_t\) factor.

## 2. Same critical clock and exact covariant derivative

Let \(s\mapsto(\ell(s),t(s))\) be \(C^1\) and satisfy the original critical clock
\[
 \ell_s=-b(s)\ell,\qquad t_s=\ell^2.
\tag{MC6}
\]
For \(D_bQ=[\partial_s+b(1+x\cdot\nabla)]Q\), the observer at the origin is fixed and \(x\cdot\nabla Q(s,0)=0\). The chain rule (without assigning any blowup rate) is therefore
\[
 D_bQ(s,0)=
 b(s)\,[Q_{\ell,t}(0)-\ell\partial_\ell Q_{\ell,t}(0)]
 +\ell^2\partial_tQ_{\ell,t}(0).
\tag{MC7}
\]
Consequently,
\[
 \boxed{\displaystyle
 D_bQ(s,0)=8\pi b(s)c(t(s))\sqrt{\ell(s)}
       +O_t\bigl(|b(s)|\ell(s)+\ell(s)^{5/2}\bigr).}
\tag{MC8}
\]
For \(\kappa_H K\), multiply the display by \(\kappa_H\).
For any fixed nonzero \(b\) and \(c(t)\neq0\), this is genuinely of order
\(|b|\sqrt\ell\), **not** \(O(\ell^{3/2})\). A concrete admissible initial snapshot is \(z(0,y)=e^{-|y|^2}\), with \(c(0)=1\) and the physical PDE fixing \(z_t(0,y)\); no fictitious source is used. Choosing a \(C^1\) clock with \(b(0)=1\) illustrates the obstruction. This clock is **not** asserted to be the unique selected HBL Cramer clock.

In sharp contrast, for the pure radiation potential
\(Q_Z=K*|Z_{\ell,t}|^4=\ell(K*|z(t)|^4)(\ell x)\), the previously established exact covariance yields
\[
 D_bQ_Z=\ell^3\partial_t(K*|z|^4)(t,\ell x),
 \qquad \|D_bQ_Z\|_2=\ell^{3/2}\|\partial_t(K*|z|^4)\|_2.
\tag{MC9}
\]
Thus **MC9 cannot be substituted for the full mixed source** in the selected four-region Hartree residual. The mixed linear-in-radiation density in MC4 has a distinct \(\sqrt\ell\) leading channel at fixed physical radius, and its \(b\)-transport does not cancel merely by applying the pure-radiation critical scaling identity.

## 3. Precise repair obligation, not a counterexample to Type II

This calculation rules out the shortcut
\[
 \|D_b(K*(|W+Z|^4-|W|^4))\|
 \stackrel{\text{unsupported}}{\lesssim}
 \ell^{3/2}\,\|\partial_t(K*|z|^4)\|
\]
on the basis of the pure-radiation estimate alone. It does **not** rule out a cancellation on the **genuinely selected Hartree trajectory**, nor does an origin trace give a lower bound in the original weighted four-piece forcing norm. A valid closure must either derive a nontrivial cancellation of the mixed channel from the same true real Cramer selector, moving core/phase and Kummer transport, or retain and bound this mixed channel at its actual scale together with all six nonlocal and cutoff/transport residual pieces.

The next load-bearing calculation is to insert the true \(V_s+b\Lambda V\) and the true two selected real speeds into the exact covariant flux (CF5–CF8) of \`HBL_213_COVARIANT_FULL_HARTREE_FLUX_20261112.md\`, **before** assigning any positive renormalized-time power. This is a quantitative insufficiency result for a proposed inference, not an impossibility theorem for the original HBL main theorem.

**Verification:** No new Lean theorem/CI for (MC3)–(MC9). Existing strict successful audited source: [selected spectral quadratic/three C1 43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481), job 130908225390, and [finite nonlinear PDE telescope 43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518), job 130872307063. In both, fixed Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, \`--trust=0\`, \`warningAsError\`, exact \`#check\` and \`#print axioms\` confirmed only \`propext\`, \`Classical.choice\`, \`Quot.sound\` on their audited targets. These audits do **not** validate (MC3)–(MC9). Revised original manuscript remains **11/13 (84.62%)**.
