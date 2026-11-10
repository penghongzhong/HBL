# §2.13 global radial Hartree Riesz-gradient bound without an artificial inner-radius loss

**10 November 2026 — analytical theorem from an established weighted Calderón–Zygmund result.**
This removes the \(R^{-1}\) loss in the *linearized nonlocal real-Hessian derivative* estimated previously only on \((R,\infty)\). It is **not a new Lean theorem**, not an allowed extra axiom, not a full nonlinear Hartree residual estimate, and does **not** change acceptance: **11/13**.

## 1. Weighted three-dimensional Riesz estimate

Use the ORIGINAL exact Hartree coupling and the non-unitary Fourier convention
\[
  \mathcal If=\kappa_{\rm H}(|x|^{-2}*f),\qquad
  \kappa_{\rm H}=3/\pi^2,\qquad
  \widehat{|x|^{-2}}(\xi)=2\pi^2|\xi|^{-1}.
\]
Therefore for the Riesz-transform vector \(\mathbf R=(R_1,R_2,R_3)\),
\[
 \widehat{\nabla\mathcal I f}(\xi)
      =6i\,\frac{\xi}{|\xi|}\widehat f(\xi),
 \qquad \nabla\mathcal I f=6\mathbf R f .
 \tag{A1}
\]

The **crucial norm** is \(L^2(dr)\), not physical \(L^2(r^2dr)\).
The associated \(\mathbb R^3\) weight is
\[
  \omega(x)=|x|^{-2}.
\]
It belongs to the classical Muckenhoupt \(A_2(\mathbb R^3)\), with a
completely explicit elementary bound. For any ball \(B(x_0,R)\):
- If \(|x_0|\ge2R\), then \(|x_0|/2\le|x|\le3|x_0|/2\) on \(B\), hence
  \[
   \Bigl(\fint_B\omega\Bigr)\Bigl(\fint_B\omega^{-1}\Bigr)\le9.
  \]
- If \(|x_0|<2R\), then \(B\subset B(0,3R)\), so
  \[
  \fint_B|x|^{-2}\,dx\le9R^{-2},\qquad
  \fint_B|x|^2\,dx\le9R^2.
  \]
  Thus the **ball-based** \(A_2\) characteristic is at most \(81\). For the standard **cube-based** \(A_2\) characteristic, enclose each cube of side \(\ell\) in its circumscribed ball of radius \(R=\sqrt3\ell/2\). The enclosing-ball/cube volume ratio is \(\pi\sqrt3/2\), so the identical two-case argument yields the explicit cube-based bound \(81\pi\sqrt3/2\). Both estimates are nonsharp, but verify the exact classical \(A_2\) condition required by Hytönen's theorem.

The standard (already published) **weighted \(A_2\) theorem for
Calderón–Zygmund/Riesz transforms** supplies a finite constant \(C_{\rm A2}\),
depending only on dimension and the above fixed \(A_2\) characteristic, such that
\[
 \|\mathbf R f\|_{L^2(\omega\,dx)}
 \le C_{\rm A2}\|f\|_{L^2(\omega\,dx)} .
 \tag{A2}
\]
A directly published primary source is **T. P. Hytönen,**
*The sharp weighted bound for general Calderón–Zygmund operators*,
**Annals of Mathematics 175** (2012), 1473–1506,
DOI **10.4007/annals.2012.175.3.9**,
https://annals.math.princeton.edu/2012/175-3/p09 .
The theorem is stated for **cube-based classical \(A_2\)** and hence applies by the explicit cube check above.
**Do not miscite the smaller Poisson-\(A_2\) class** as if it comprised
all classical \(A_2\) weights.

If \(f(x)=f_0(|x|)\) is radial, the exact change of variables is
\[
 \|f\|_{L^2(\omega\,dx)}^2
 =4\pi\int_0^\infty|f_0(r)|^2dr,\quad
 \|\nabla\mathcal If\|_{L^2(\omega\,dx)}^2
 =4\pi\int_0^\infty|\partial_r\mathcal I f(r)|^2dr.
\]
Consequently, initially for smooth compactly supported radial \(f\),
then by density,
\[
 \boxed{\quad
 \|\partial_r\mathcal I f\|_{L^2(0,\infty;dr)}
 \le6C_{\rm A2}\|f\|_{L^2(0,\infty;dr)}.
 \quad}
 \tag{A3}
\]
**There is no \(R^{-1}\), no restriction \(r>R\), no new weighted source
gradient envelope, and no assumption on a moving left interface.**
This is a direct application of an external published harmonic-analysis
theorem, not a formally compiled consequence of the existing HBL Mathlib.

## 2. Uniform global \(H^1(dr)\) estimate for the *actual* nonlocal Hessian

Let
\[
 W(r)=(1+r^2)^{-1/2},\quad
 T F=\mathcal I(W^3F),\quad
 N(F)=W^3\,\mathcal I(W^3F).
\]
For real radial \(F\in L^2(dr)\), \(\|W^3F\|_2\le\|F\|_2\).
Equation (A3) gives the global bound
\[
 \|(T F)'\|_{L^2(dr)}\le6C_{\rm A2}\|F\|_{L^2(dr)}.
 \tag{A4}
\]
Independently, the exact **radial Hilbert–Schmidt** result already
derived in \`HBL_213_DUAL_KATO_SOURCE_NORM_OBSTRUCTION_20261110.md\` is
\[
 \|T F\|_{L^2(dr)}\le3\|F\|_{L^2(dr)}.
 \tag{A5}
\]
Since
\[
 (1+r^2)W^3=W\le1,\quad
 \sup_{r>0}(1+r^2)|(W^3)'|
 =\sup_{r>0}\frac{3r}{(1+r^2)^{3/2}}
 =\frac2{\sqrt3},
\]
the ordinary/weak product derivative satisfies the **full half-line**
estimate
\[
 \begin{aligned}
 \|(1+r^2)N(F)\|_{L^2(dr)}
 &\le3\|F\|_2,\\
 \boxed{\quad
 \|(1+r^2)(N(F))'\|_{L^2(dr)}
 &\le(6C_{\rm A2}+2\sqrt3)\|F\|_2.
 \quad}
 \end{aligned}
 \tag{A6}
\]
In particular, the earlier \(4/(\sqrt3R)\) derivative
estimate is **correct but unnecessarily lossy** for the
linearized nonlocal Hartree term. Its apparent divergence
near \(r=0\) was caused by replacing the natural weighted
three-dimensional Riesz estimate by an unweighted \(L^2(dx)\)
estimate followed by a crude restriction \(r>R\).

The real Hessian term is \(-4N(F)\), so multiply both constants
by \(4\) when applying (A6) to the full \(L_+\) block.

## 3. What this does and does not close

The nonlocal **linearized** Riesz-gradient producer is now
a theorem-level **paper consequence** of a standard published
\(A_2\) result and the previously derived explicit
Hilbert–Schmidt identity. Its domain is the true radial
\(L^2(dr)\) source space and it is uniform down to \(r=0\),
**not** a hypothesized independent envelope.

However:
1. For the actual nonlinear, time-moving four-piece Hartree residual,
   density factors and cross interactions depend on the constructed
   physical field and are not generally \(W^3F\). Equation (A6)
   cannot by itself control those.
2. The weighted source gradient of the **complete residual**
   still contains local \(\partial_rF\), moving cutoffs,
   spectral parameter/time derivatives and nonlinear density products.
   The flat-overlap source mismatch \(E=\|u''-v''\|_{L^2}\)
   must still be estimated with *the same PDE source*;
   no time-positive exponent or parameter Lipschitz is produced here.
3. The projected **full coupled non-selfadjoint Hartree Hamiltonian**
   limiting-absorption / homogeneous-adjoint Kato estimate remains
   independent and currently unproved, as does the actual orbit and
   PDE-dynamically generated Type-II rate.
4. A later Lean verification must formalize or cite the weighted
   Riesz transform theorem **without postulating a new Lean axiom**.
   No \`#check\`, \`#print axioms\`, or strict CI for (A2)–(A6)
   is claimed from this paper calculation.

**Original revised 13-environment acceptance remains 11/13 (84.62%).**


## 4. Exact moving-bubble scale covariance — no imposed physical rate

The original energy-critical stationary family is
\[
 W_\lambda(r)=\lambda^{-1/2}W(r/\lambda),
 \qquad \lambda>0.
\]
Define its **actual** nonlocal real-Hessian operator
\[
 N_\lambda(F)(r):=
 W_\lambda(r)^3\,\mathcal I(W_\lambda^3F)(r),
 \qquad F^\sharp_\lambda(\rho):=F(\lambda\rho).
\]
The true physical convolution, with its original
\(\mathbb R^3\) measure, obeys exactly
\[
 \mathcal I(W_\lambda^3 F)(\lambda\rho)
  =\lambda^{-1/2}\mathcal I(W^3 F^\sharp_\lambda)(\rho),
 \qquad
 \boxed{\quad
 N_\lambda(F)(\lambda\rho)
  =\lambda^{-2}N(F^\sharp_\lambda)(\rho).
 \quad}
 \tag{A7}
\]
Indeed, the convolution change of variables contributes
\(\lambda^3\) from volume, \(\lambda^{-2}\) from
the inverse-square kernel and \(\lambda^{-3/2}\)
from \(W_\lambda^3\), yielding \(\lambda^{-1/2}\).
The exterior \(W_\lambda^3\) supplies the remaining
\(\lambda^{-3/2}\).

Using \(\|F^\sharp_\lambda\|_{L^2(d\rho)}
=\lambda^{-1/2}\|F\|_{L^2(dr)}\) and (A6)
gives the *uniform in all positive \(\lambda\)* bounds
\[
 \boxed{\begin{aligned}
 \|(\lambda^2+r^2)N_\lambda(F)\|_{L^2(dr)}
   &\le3\|F\|_{L^2(dr)},\\
 \|(\lambda^2+r^2)\partial_rN_\lambda(F)\|_{L^2(dr)}
   &\le(6C_{\rm A2}+2\sqrt3)\lambda^{-1}
     \|F\|_{L^2(dr)} .
 \end{aligned}}\tag{A8}
\]
For the first line, \(\lambda^2+r^2\) exactly compensates
the \(\lambda^{-2}\) profile factor. For the
derivative line, the chain rule supplies an extra
\(\lambda^{-1}\). This is a *moving-spatial-scale*
estimate in the precise scale-covariant weight;
it **does not** bound \(\partial_sN_{\lambda(s)}\),
nor infer any \(\lambda_s\), selected speed, Lipschitz
control or blowup rate. Any application to moving
time needs the correct PDE-dynamical modulation law.
No new independent source estimate, axiom or strict
Lean acceptance is inserted; the original count is 11/13.
