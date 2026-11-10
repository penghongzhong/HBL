# HBL §2.13 — exact conformal spectrum of the FULL nonlocal Hartree bubble Hessian (10 November 2026)

**Status:** Original-Hartree **paper proof**, NOT a Lean certificate and NOT a dynamical Kato/resolvent estimate. Original revised acceptance remains **11/13**.

## 1. Stereographic and original physical convolution identities

Fix the precise original focusing 3D quartic inverse-square Hartree data
\[
 W(x)=(1+|x|^2)^{-1/2},\qquad
 \mathcal If=\kappa_{\rm H}(|x|^{-2}*f),\qquad
 \kappa_{\rm H}=3/\pi^2,\qquad
 -\Delta W=3W^5=\mathcal I(W^4)W^3.
\tag{C1}
\]
The stereographic map into the round \(\mathbb S^3\) is
\[
 \Xi(x)=\left(\frac{2x}{1+|x|^2},
             \frac{|x|^2-1}{1+|x|^2}\right).
\]
Exactly
\[
 d\omega=8W(x)^6dx,\quad
 |\Xi(x)-\Xi(y)|=2W(x)W(y)|x-y|,\quad
 4W^4(\Delta_{\mathbb S^3}\Phi)\circ\Xi
   =\Delta_x(\Phi\circ\Xi)+2\nabla\log W\cdot\nabla(\Phi\circ\Xi).
\tag{C2}
\]
For the spherical Riesz operator
\((\mathscr K\Phi)(\xi)=\int_{\mathbb S^3}|\xi-\eta|^{-2}\Phi(\eta)d\omega(\eta)\),
and the original physical field \(g=W(\Phi\circ\Xi)\), the **full genuine nonlocal convolution** is
\[
 \boxed{\quad
 \mathcal I(W^3g)=\frac{\kappa_{\rm H}}2 W^2
                     (\mathscr K\Phi)\circ\Xi.\quad}
\tag{C3}
\]
Since \(\mathscr K1=2\pi^2\), this also gives \(\mathcal I(W^4)=3W^2\);
no local NLS nonlinearity has been substituted.

## 2. Exact two-channel operators and all spherical eigenvalues

Actual quartic-Hartree real/imaginary linearization at \(W\):
\[
 L_-=-\Delta-3W^4,\qquad
 L_+=-\Delta-9W^4-4W^3\mathcal I(W^3\cdot).
\tag{C4}
\]
The ground-state and conformal identities give the **exact** original physical operators
\[
 \boxed{\begin{aligned}
 L_-[W(\Phi\circ\Xi)]
 &=W^5[-4\Delta_{\mathbb S^3}\Phi]\circ\Xi,\\
 L_+[W(\Phi\circ\Xi)]
 &=W^5[-4\Delta_{\mathbb S^3}\Phi-6\Phi
                 -(6/\pi^2)\mathscr K\Phi]\circ\Xi.
 \end{aligned}}\tag{C5}
\]
For a degree \(k\) harmonic \(Y_k\), \(-\Delta_{\mathbb S^3}Y_k=k(k+2)Y_k\).
Funk–Hecke with \(C_k^1(\cos\theta)=\sin((k+1)\theta)/\sin\theta\) yields
\[
 \begin{aligned}
 \lambda_k(\mathscr K)
  &=\frac{4\pi}{k+1}
    \int_0^\pi \cos^2(\theta/2)C_k^1(\cos\theta)\,d\theta\\
  &=\boxed{\frac{2\pi^2}{k+1}} .
 \end{aligned}\tag{C6}
\]
The last integral is \(\pi/2\) for every \(k\): the Chebyshev expansion
has constant coefficient \(1\) for even \(k\) and \(\cos\theta\)
coefficient \(2\) for odd \(k\); cosine orthogonality gives the identity.
Therefore the entire static Hessian is diagonal on spherical harmonics with coefficients
\[
 \boxed{\quad h_k^-=4k(k+2),\qquad
 h_k^+=4k(k+2)-6-\frac{12}{k+1}.\quad}
\tag{C7}
\]
In particular
\[
 h_0^-=0,\quad h_{k\ge1}^->0;\qquad
 h_0^+=-18,\quad h_1^+=0,\quad h_{k\ge2}^+\ge22.
\]
**Spectral interpretation:** The coefficients \(h_k^\pm\) are the exact
diagonal entries of the **conformally conjugated generalized elliptic
problem** \(W^{-5}L_\pm W\) and of the physical energy quadratic forms.
They are **NOT the eigenvalues of \(L_\pm\) on physical
\(L^2(\mathbb R^3,dx)\)**: the map \(g=W\Phi\circ\Xi\) and output
weight \(W^5\) do not implement a unitary \(L^2\) conjugation.
In particular these numbers alone say nothing about the positive-energy
limiting-absorption estimate or the time-dependent matrix Hamiltonian.

Thus the original nonlocal **real** Hessian has exactly one negative
quadratic direction (degree-zero), four neutral directions
(degree-one, three translations plus scaling), and a positive complement.
The **radial** sector has only one of the degree-one real neutral
modes, \(\Lambda W=-W(\Xi_4\circ\Xi)/2\).
The phase null mode is \(W\in\dot H^1\setminus L^2\).

## 3. Quantitative exact stationary energy coercivity

For \(g=W(\Phi\circ\Xi)\) and the round-sphere degree projections \(\Pi_k\),
\[
 \|g\|_{\dot H^1(\mathbb R^3)}^2
   =\frac18\sum_{k\ge0}[4k(k+2)+3]\|\Pi_k\Phi\|_2^2,
 \qquad
 \langle g,L_\pm g\rangle
   =\frac18\sum_{k\ge0}h_k^\pm\|\Pi_k\Phi\|_2^2.
\tag{C8}
\]
Hence (valid for smooth modes and, by density, the energy completion)
\[
 \boxed{\begin{aligned}
 \Pi_0\Phi=0
   &\Longrightarrow
   \langle g,L_-g\rangle\ge\frac45\|g\|_{\dot H^1}^2,\\
 \Pi_0\Phi=\Pi_1\Phi=0
   &\Longrightarrow
   \langle g,L_+g\rangle\ge\frac{22}{35}\|g\|_{\dot H^1}^2.
 \end{aligned}}\tag{C9}
\]
The quotients \(h_k^-/[4k(k+2)+3]\ge4/5\) for \(k\ge1\)
and \(h_k^+/[4k(k+2)+3]\ge22/35\) for \(k\ge2\)
are monotone; equality occurs on \(k=1\) and \(k=2\), respectively.
These are *exact stationary* constants in the genuine original Hartree
energy space, with no hidden left-radius loss.

## 4. Full physical projected **elliptic** inverse, not a time inverse

Suppose the actual physical source \(F\) obeys
\((1+|x|^2)F\in L^2(\mathbb R^3)\), and set
\(\widetilde F=(F/W^5)\circ\Xi^{-1}\) on \(\mathbb S^3\). Then
\[
 \|\widetilde F\|_{L^2(\mathbb S^3)}^2
 =8\|(1+|x|^2)F\|_{L^2(\mathbb R^3)}^2.
\tag{C10}
\]
For the phase block the **necessary and sufficient** weighted-source
solvability condition is
\[
 \boxed{\quad\Pi_0\widetilde F=0
  \ \Longleftrightarrow\
  \int_{\mathbb R^3}W(x)F(x)\,dx=0.\quad}\tag{C11}
\]
For radial \(F\) this is exactly
\(4\pi\int_0^\infty r^2W(r)F(r)\,dr=0\),
the original-phase Fredholm moment found in
HBL_213_EXACT_PHASE_RESONANCE_FREDHOLM_GATE_20261110.md.
Set \(\Phi_k=\Pi_k\widetilde F/[4k(k+2)]\) for \(k\ge1\),
\(\Phi_0=0\), and \(g_-=W\Phi\circ\Xi\). Then \(L_-g_-=F\)
distributionally and
\[
 \boxed{\quad
 \|g_-\|_{\dot H^1}
 \le\sqrt{\frac5{48}}\|(1+|x|^2)F\|_{L^2}.
 \quad}\tag{C12}
\]
The sharp squared spectral ratio
\([4k(k+2)+3]/[4k(k+2)]^2\) is \(5/48\) at \(k=1\).

For the real block, if
\(\Pi_0\widetilde F=\Pi_1\widetilde F=0\),
put \(\Phi_k=\Pi_k\widetilde F/h_k^+\), \(k\ge2\).
Then \(L_+g_+=F\) distributionally for \(g_+=W\Phi\circ\Xi\)
and
\[
 \boxed{\quad
 \|g_+\|_{\dot H^1}
 \le\frac{\sqrt{35}}{22}\|(1+|x|^2)F\|_{L^2}.
 \quad}\tag{C13}
\]
Indeed \([4k(k+2)+3]/(h_k^+)^2\le35/22^2\), \(k\ge2\).
The degree-zero real negative mode can algebraically be inverted
as \(1/h_0^+=-1/18\), but is excluded from the coercive inverse.
These are *constructive true-Hartree projected stationary elliptic*
bounds, not arbitrarily assumed propagator estimates.

## 5. Strict scope: the actual moving Hartree PDE remains OPEN

Although the static elliptic maps are diagonal under stereography,
the physical time derivative \(\partial_t(W\Phi)=W\partial_t\Phi\)
has a **different** weight from the \(W^5\) Hessian output:
the transformed time-dependent operator contains the nonconstant
multiplier \(W^4\). Therefore the coupled Hartree Hamiltonian
\(J\,\mathrm{diag}(L_+,L_-)\) is NOT diagonal in those spherical
harmonics. The exact stationary result gives neither its
positive-energy limiting absorption nor homogeneous adjoint
Kato smoothing, moving-spectral Lipschitz, actual nonlinear
four-region source order, true orbit, finite profile recurrence,
or dynamically obtained Type-II blowup rate.

The new **physical phase/real projection moments** must be derived
from the same true moving Hartree PDE; they are not independent
source assumptions. The only rigorous claims here are (C1)–(C13)
under explicit stationary-bubble and weighted-source hypotheses.

**Formal verification:** Independent symbolic/radial derivative checks
and direct Funk–Hecke integrals for degrees 0–4 were performed.
No new Lean 4.35.0-rc3 --trust=0 build, exact #check or #print axioms
exists for this computation. Earlier CI 42536552509 and 42854633900
remain exact-target Success but do not establish this result.
Original 13 environments accepted: **11/13 (84.62%)**.


## 6. Exact *full nonlinear* conformal Hartree PDE and a concrete dynamical obstruction

The same change of variables is valid for the **whole original
nonlocal Hartree equation**, not only its Hessian. For any sufficiently
regular complex field \(u(t,x)=W(x)\Phi(t,\Xi(x))\) (with *fixed*
stereographic coordinates) and the original physical equation
\[
 i\partial_tu+\Delta_xu+
   \mathcal I(|u|^4)|u|^2u=0,
\]
the true convolution and conformal Laplacian identities yield exactly
\[
 \mathcal N(W\Phi\circ\Xi)
 =\frac{\kappa_{\rm H}}2W^5
   \bigl[\mathscr K(|\Phi|^4)|\Phi|^2\Phi\bigr]\circ\Xi ,
 \qquad
 -\Delta_x(W\Phi\circ\Xi)
 =W^5[(3-4\Delta_{\mathbb S^3})\Phi]\circ\Xi.
 \tag{C14}
\]
Thus the **unabridged** nonlinear physical PDE is
\[
 \boxed{\quad
 i\partial_t\Phi(t,\xi)
 =\frac{(1-\xi_4)^2}{4}
  \left[(3-4\Delta_{\mathbb S^3})\Phi
      -\frac{\kappa_{\rm H}}2
       \mathscr K(|\Phi|^4)|\Phi|^2\Phi\right](t,\xi).
 \quad}
 \tag{C15}
\]
All quartic-density nonlocal mixed interactions are retained in the
literal nonlinear convolution. The factor
\(W^4=(1-\xi_4)^2/4\) is **not optional**: at the north pole
\(\xi_4=1\) (physical spatial infinity) it vanishes
quadratically as a function of spherical height. Therefore the
round-sphere spatial elliptic spectral gap **cannot** simply be
reinterpreted as uniform sphere \(L^2\) dynamical coercivity or
a positive-energy limiting-absorption/Kato estimate.
Multiplication by \((1-\xi_4)^2\) mixes spherical harmonics and
degenerates at the compactification point.

For the exact equilibrium \(\Phi\equiv1\), the bracket in (C15)
vanishes since
\((3-4\Delta_{\mathbb S^3})1=3\) and
\(\frac{\kappa_{\rm H}}2\mathscr K1
=(3/2\pi^2)(2\pi^2)/2=3\).
Linearization recovers (C5), including the full nonlocal real block.
This is a useful **same-equation** stationary/dynamic consistency
check, not an extra external model or physical blowup construction.

Caveats: (C15) uses a fixed bubble/physical coordinate frame;
the actual HBL time-dependent scaling, gauge, moving four interfaces,
and selected velocity introduce material transport/parameter terms.
They **must** be derived and estimated independently. This exact
nonlinear coordinate identity is **not** a positive-time residual
estimate, a nonlinear orbit, or a validated Lean theorem.
Original revised acceptance remains 11/13.
