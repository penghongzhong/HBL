# HBL §2.13 — a quantitative finite-rank obstruction for the genuine mixed Hartree channel

12 November 2026 UTC. **Mathematical proof only; no new Lean theorem. Retained revised paper environments: 11/13.**

## 1. Infinite rank of the original nonlocal mixed term in the physical energy class

For the **untruncated** three-dimensional inverse-square Hartree kernel \(K(x)=|x|^{-2}\), define
\[
  \mathcal C(z):=K*\bigl(|x|^{-1}\operatorname{Re}z\,|z|^2\bigr),
  \qquad z\in\dot H^1(\mathbb R^3;\mathbb C).
  \tag{FR1}
\]
By Hardy, Sobolev and HLS, \(\mathcal C(z)\in L^2\) and
\[
 \|\mathcal C(z)\|_2\le 2C_{\rm HLS}S_3^2\|\nabla z\|_2^3.
 \tag{FR2}
\]
This is the **same** cubic mixed potential that survives in the full original quartic Hartree covariant flux (previous global \(L^2\) computation); it is not a local-NLS surrogate.

Choose three nonnegative, nonzero, real, radial test functions
\(\phi_j\in C_c^\infty(\mathbb R^3)\) supported in **pairwise disjoint** annuli bounded away from zero, \(j=1,2,3\), and put
\[
 f_j(x)=|x|^{-1}\phi_j(x)^3,\qquad
 g_j=\mathcal C(\phi_j)=K*f_j.
 \tag{FR3}
\]
**Proposition.** \(g_1,g_2,g_3\) are linearly independent in real \(L^2(\mathbb R^3)\).

**Proof.** The Riesz Fourier identity in dimension three (with
\(\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx\)) reads, as tempered distributions,
\[
 \widehat K(\xi)=2\pi^2|\xi|^{-1},\qquad \xi\ne0.
 \tag{FR4}
\]
If \(\sum_{j=1}^3 a_jg_j=0\) in \(L^2\), then
\[
 0=|\xi|\sum_{j=1}^3a_j\widehat g_j(\xi)
   =2\pi^2\sum_{j=1}^3a_j\widehat f_j(\xi)
 \quad\text{a.e. on }\mathbb R^3\setminus\{0\}.
 \tag{FR5}
\]
The \(f_j\) are smooth compactly supported and have disjoint supports, so Fourier injectivity gives \(\sum a_jf_j=0\) and then \(a_j=0\) for each \(j\). There is no appeal to an assumed source envelope.

## 2. A uniform positive lower bound against ANY two real correction directions

Define the actual Gram matrix \(G\in\mathbb R^{3\times3}\) by
\[
 G_{jk}=\int_{\mathbb R^3}g_j(x)g_k(x)\,dx,\qquad
 \gamma=\sqrt{\lambda_{\min}(G)/3}>0.
 \tag{FR6}
\]
**Theorem.** For every real linear subspace \(V\subset L^2(\mathbb R^3;\mathbb R)\) of dimension at most two,
\[
 \boxed{\max_{j=1,2,3}\operatorname{dist}_{L^2}(g_j,V)\ge\gamma.}
 \tag{FR7}
\]
**Proof.** Let \(P_V\) be the orthogonal projection onto \(V\). The map
\[
  A:\mathbb R^3\to V,\qquad A a=P_V\sum_{j=1}^3a_jg_j
\]
has a nonzero kernel. For a unit vector \(a\in\ker A\),
\[
 \sqrt{\lambda_{\min}(G)}
 \le \left\|\sum_j a_jg_j\right\|_2
 =\left\|\sum_j a_j(I-P_V)g_j\right\|_2
 \le\sqrt3\max_j\|(I-P_V)g_j\|_2.
 \tag{FR8}
\]
This yields (FR7), including the case when the two correction directions are not orthogonal.

For \(0<\ell\le1\), let \(U_\ell f(x)=\ell^{-3/2}f(x/\ell)\) (unitary on \(L^2\)), and take the critical-energy physical snapshots
\[
 z_{\ell,j}(x)=\ell^{-1/2}\phi_j(x/\ell),\qquad
 \|\nabla z_{\ell,j}\|_2=\|\nabla\phi_j\|_2.
 \tag{FR9}
\]
The **exact original Hartree scaling** gives
\[
 \mathcal C(z_{\ell,j})=U_\ell g_j,\qquad
 \boxed{\max_j\operatorname{dist}_{L^2}
    \bigl(\mathcal C(z_{\ell,j}),V_\ell\bigr)\ge\gamma}
 \tag{FR10}
\]
for **every** family of real subspaces \(V_\ell\subset L^2\) of dimension at most two. To prove (FR10), apply (FR7) to \(U_\ell^{-1}V_\ell\). All three snapshots have a common finite energy bound; the lower bound survives \(\ell\downarrow0\).

Thus no estimate uniform over an entire bounded \(\dot H^1\) ball can eliminate the *full* leading cubic mixed potential merely by choosing two real coefficients in two fixed (or scale-moving) spatial correction directions. More strongly, the lower bound holds even if the two-dimensional subspace is chosen optimally at each scale, provided it is shared by the three tests. Its value is fixed by the positive definite Gram matrix, not by any conjectural dynamical asymptotics.

## 3. Precise scope for the HBL proof

The two real Cramer speeds are a rank-two **modulation correction** at a fixed background. Their uniqueness and the accepted spatial three-\(C^1\) joins do **not alone** imply cancellation of the infinite-dimensional mixed component in (FR1). The next acceptable main-chain estimate must control the *nonresonant complementary component* by the genuine Kummer/Hartree resolvent or projected PDE dynamics, while deriving the time-weight from the same selected orbit.

This is **not** a no-go theorem for the full nonlinear four-region packet: the source-dependent Green correction is not confined to a two-dimensional subspace, the true speed/basis may depend on the physical orbit, and the selected blowup solution is not known to range over the energy ball or through these three initial snapshots. In particular (FR10) neither precludes a specially constructed orbit nor assigns an order to the final residual. The preceding exact global mixed flux formula is used only to identify the source, not to claim that the whole residual equals \(\mathcal C(z)\).

## 4. Strict acceptance boundary

The historical initial finite telescope run [42530158681](https://github.com/penghongzhong/HBL/actions/runs/42530158681) failed on genuine upstream \`InWeightedL2\` and type errors. The corrected, source-identical finite nonlinear PDE telescope [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518) succeeded; job \`130872307063\`. The selected fixed-time quadratic spectral + three-\(C^1\) audit [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481) succeeded; job \`130908225390\`. Original job logs confirm Lean 4.35.0-rc3, Mathlib \`a98628e16c11f5167f16124105ddce53efa9bfe5\`, \`--trust=0 -DwarningAsError=true\`, exact checks and only \`propext\`, \`Classical.choice\`, \`Quot.sound\` for their named targets. **(FR1)–(FR10) are paper mathematics only and have no new Lean CI.**

**Retained original paper count stays 11/13**. Revised §2.13 awaits full same-orbit four-region positive-time residual, parameter Lipschitz and physical finite recursion; final original dynamically derived Type-II blowup theorem remains unclosed.
