# HBL §2.13 — exact two-scale profiles of the full, untruncated mixed Hartree potential

12 November 2026 UTC. **Paper calculation; not a strict Lean acceptance.** Revised original manuscript: **11/13**. The result identifies a *spatially nonconstant* first-order mixed potential and separates it from a second-order constant pure-radiation contribution. All products use the original three-dimensional inverse-square, quartic-density Hartree kernel.

## 1. Statement and admissible data

Let \(K(x)=|x|^{-2}\), \(W(x)=(1+|x|^2)^{-1/2}\), and let \(z=z(t,y)\) be a radial smooth **actual** solution, on a time interval, of
\[
 iz_t+\Delta z+\kappa_H(K*|z|^4)|z|^2z=0,\qquad \kappa_H\in\mathbb R.
 \tag{TS1}
\]
For the asymptotic statement at a given time \(t\), assume \(z(t),z_t(t)\) are Schwartz (uniform Schwartz bounds on a compact time interval for uniform-in-\(t\) versions). This is a regularity hypothesis for a test trajectory, **not** a derived property of the unknown Type-II HBL orbit.

Write \(c(t)=\operatorname{Re}z(t,0)\), \(d(t)=2|z(t,0)|^2+4c(t)^2\), \(H(t,x)=K*|z(t)|^4(x)\), and set
\[
 Z_{\ell,t}(x)=\sqrt{\ell}\,z(t,\ell x),\qquad
 Q_{\ell,t}(x)=K*(|W+Z_{\ell,t}|^4-W^4)(x),\quad 0<\ell<1.
 \tag{TS2}
\]
Define two *fixed* radial potentials
\[
 A(r)=(K*W^3)(r),\qquad B(r)=(K*W^2)(r).
\]
Their exact closed forms, including values at the origin, are
\[
 \boxed{ A(r)=\frac{4\pi\,\operatorname{arsinh}r}{r\sqrt{1+r^2}},
 \quad A(0)=4\pi,\qquad
 B(r)=\frac{2\pi^2\arctan r}{r},\quad B(0)=2\pi^2. }
 \tag{TS3}
\]

For every *fixed* compact spatial set \(\mathcal K\subset\mathbb R^3\),
\[
 \boxed{\quad
 Q_{\ell,t}(x)=4\sqrt{\ell}\,c(t) A(|x|)
 +\ell\,[d(t)B(|x|)+H(t,0)]+o_{t,\mathcal K}(\ell),
 \qquad x\in\mathcal K.\quad}
 \tag{TS4}
\]
The remainder is locally uniform, as is its \(\ell\partial_\ell\)-derivative under the stated smoothness and decay hypotheses; in particular, the derivative of the \(o(\ell)\) term is \(o(\ell)\). The same statement holds after one \(t\)-derivative if \(z_t\) enjoys the stipulated bounds.

**Important:** (TS4) is only a fixed-core expansion. It is NOT a global \(L^3\) expansion and cannot be applied unchanged to a moving matching radius comparable to \(1/\ell\). Indeed, the pure-radiation potential \(Q_Z=\ell H(t,\ell x)\) has critical \(\|Q_Z\|_3=\|H(t)\|_3\), which is generally not small.

## 2. Exact convolution evaluation

For radial \(\rho\), the original three-dimensional angular integral is
\[
 (K*\rho)(r)=\frac{2\pi}{r}\int_0^\infty
 s\,\rho(s)\log\frac{r+s}{|r-s|}\,ds,\qquad r>0.
 \tag{TS5}
\]
With \(\rho=W^3\), use \(s(1+s^2)^{-3/2}=-\partial_s(1+s^2)^{-1/2}\). Integration by parts, interpreting the derivative of the logarithm as a principal value, gives
\[
 \begin{aligned}
 A(r)&=4\pi\,\mathrm{p.v.}\!\int_0^\infty
 \frac{ds}{\sqrt{1+s^2}(r^2-s^2)}
 =4\pi\,\mathrm{p.v.}\!\int_0^1
 \frac{du}{r^2-(1+r^2)u^2}\\
 &=\frac{4\pi\,\operatorname{arsinh}r}{r\sqrt{1+r^2}}.
 \end{aligned}
 \tag{TS6}
\]
Here the second equality follows from \(s=\sinh v\), \(u=\tanh v\). The improper principal value is the one obtained by removing a symmetric interval around the logarithmic singularity in (TS5), and the endpoint contributions in the integration by parts vanish. The value at \(r=0\) also follows directly from \(4\pi\int_0^\infty W^3\,ds=4\pi\).

For \(B\), the Fourier convention \(\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx\) gives the distributional identities
\[
 \widehat K(\xi)=\frac{2\pi^2}{|\xi|},
 \qquad
 \widehat{W^2}(\xi)=\frac{2\pi^2e^{-|\xi|}}{|\xi|}.
\]
The radial inverse Fourier transform yields
\[
 B(r)=\frac{2\pi^2}{r}\int_0^\infty
 \frac{e^{-\sigma}\sin(r\sigma)}{\sigma}\,d\sigma
 =\frac{2\pi^2\arctan r}{r}.
 \tag{TS7}
\]
The distributional transform can be justified by exponential or compact cutoffs, followed by monotone/dominated convergence in the positive radial convolution. 

A useful positive representation for all \(r\ge0\) is
\[
 \frac{A(r)}{4\pi}
 =\int_0^1\frac{du}{\sqrt{(1+r^2)(1+r^2u^2)}}.
 \tag{TS8}
\]
Consequently,
\[
 0<A(r)\le4\pi,\qquad A'(r)\le0,\qquad
 |A'(r)|\le\frac{2r}{1+r^2}A(r),\qquad
 |A''(r)|\le\frac{6}{1+r^2}A(r).
 \tag{TS9}
\]
The last two inequalities follow by logarithmically differentiating the integrand in (TS8):
\(\lvert\partial_r\log g_u\rvert\le2r/(1+r^2)\) and
\(\lvert\partial_r^2\log g_u\rvert\le2/(1+r^2)\).
In particular \(A(r)=4\pi[1-\frac23r^2+O(r^4)]\) at the origin and
\(A(r)\sim4\pi\log(2r)/r^2\) at infinity. The logarithm is the precise borderline effect of \(W^3(r)\sim r^{-3}\).

## 3. Exact expansion of the original quartic nonlocal density

For \(Z=Z_{\ell,t}\), the *exact* complex-valued quartic identity is
\[
 |W+Z|^4-W^4
 =4W^3\operatorname{Re}Z
 +W^2(2|Z|^2+4(\operatorname{Re}Z)^2)
 +4W(\operatorname{Re}Z)|Z|^2+|Z|^4.
 \tag{TS10}
\]
The first term, after convolution, equals
\(4\sqrt{\ell}c A+O_{\mathcal K}(\ell^{3/2})\), because
\[
 |z(t,\ell y)-z(t,0)|\le \ell|y|\|\nabla z(t)\|_\infty,
 \quad
 \sup_{x\in\mathcal K}\int_{\mathbb R^3}
 \frac{|y|W(y)^3}{|x-y|^2}\,dy<\infty .
 \tag{TS11}
\]
For the quadratic terms, \(K(x-y)W(y)^2\) is uniformly integrable for \(x\) on compact sets, and dominated convergence gives
\[
 \ell^{-1}K*\{W^2[2|Z|^2+4(\operatorname{Re}Z)^2]\}
 \longrightarrow d B
 \quad\text{uniformly on compact sets}.
 \tag{TS12}
\]
The cubic term is \(O_{\mathcal K}(\ell^{3/2}(1+|\log\ell|))=o(\ell)\); split \(|y|\le 2\sup_{\mathcal K}|x|+2\), the intermediate range \(1\ll|y|\lesssim\ell^{-1}\), and the rapidly decaying tail. Finally, **without any truncation**,
\[
 K*|Z_{\ell,t}|^4(x)=\ell H(t,\ell x)
 =\ell H(t,0)+o_{\mathcal K}(\ell).
 \tag{TS13}
\]
These four estimates prove (TS4), including the global nonlocal pure-radiation contribution \(H(t,0)\), which cannot be dropped. Differentiating the same dominated-convergence argument in \(\ell\) and in \(t\) proves the stated differentiability of the remainder.

In particular,
\[
 Q_{\ell,t}(0)
 =16\pi c\sqrt\ell
 +\ell\bigl[2\pi^2d+H(t,0)\bigr]+o_t(\ell).
 \tag{TS14}
\]
This sharpens the preceding \(O(\ell)\) term in the origin-only obstruction (MC5) and identifies the distinct mixed and pure contributions.

## 4. Exact covariant time interface and necessary cancellation

Assume the **original** critical clock \(\ell_s=-b\ell,\ t_s=\ell^2\) and denote \(D_b=\partial_s+b(1+x\cdot\nabla)\). At fixed compact \(x\),
\[
 D_bQ=b[(1+x\cdot\nabla)Q-\ell\partial_\ell Q]
       +\ell^2\partial_tQ .
 \tag{TS15}
\]
Inserting (TS4) and its differentiated expansion yields
\[
 \boxed{\quad
 D_bQ(s,x)=4b c\sqrt\ell\,\mathcal M(r)
       +b\ell d\,rB'(r)
       +o_{\mathcal K}(|b|\ell)
       +O_{\mathcal K}(\ell^{5/2}),\quad r=|x|,\quad}
 \tag{TS16}
\]
where
\[
 \boxed{
 \mathcal M(r)=\left(\tfrac12+r\partial_r\right)A(r)
 =4\pi\left[
 \frac1{1+r^2}
 -\frac{(1+3r^2)\operatorname{arsinh}r}
 {2r(1+r^2)^{3/2}}\right],\qquad
 \mathcal M(0)=2\pi.}
 \tag{TS17}
\]
The spatially constant \(\ell H(t,0)\) cancels at order \(b\ell\) in (TS15); the nonconstant mixed \(\sqrt\ell\) term **does not**. At \(x=0\), \(rB'(r)=0\), hence
\[
 D_bQ(s,0)=8\pi b c\sqrt\ell
       +o(|b|\ell)+O(\ell^{5/2}).
 \tag{TS18}
\]
The function \(\mathcal M\) is not a constant mode: for \(r\to\infty\),
\[
 \mathcal M(r)=\frac{4\pi}{r^2}
      \left(1-\frac32\log(2r)+o(1)\right).
 \tag{TS19}
\]
Thus a purely *spatially constant* phase/frequency correction cannot, by itself, cancel the mixed covariant potential on an entire matching annulus. This does not rule out a nonconstant genuine Kummer correction or cancellation from the unique full Cramer path.

## 5. Scope and precise remaining gate

(TS4)–(TS19) are **not** a positive-\(s\)-order four-region residual estimate. The test Schwartz trajectory is not shown to be the selected HBL orbit; no relation between \(b(s),\ell(s)\) and \(s\) is presumed. To upgrade the original §2.13 one must insert \(\mathcal M\) and the \(rB'\) channel into the **same** uniquely real two-speed Cramer selector, moving core, moving Kummer operator, three \(C^1\) joins and full nonlocal residual. One must prove either source-faithful cancellation or its weighted positive-time estimate, together with parameter Lipschitz and finite recursion; the final Type-II rate must be derived from PDE dynamics.

Strict GitHub CIs already independently checked: [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481), job 130908225390 (selected spectral quadratic and three \(C^1\) interfaces); [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518), job 130872307063 (exact four-piece finite nonlocal PDE telescope). Both compile with Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, \`--trust=0\`, \`-DwarningAsError=true\`, exact \`#check\` and \`#print axioms\`; the audited declarations have only \`propext\`, \`Classical.choice\`, \`Quot.sound\`. **Those CIs do not verify this new two-scale lemma. Revised original count stays 11/13.**
