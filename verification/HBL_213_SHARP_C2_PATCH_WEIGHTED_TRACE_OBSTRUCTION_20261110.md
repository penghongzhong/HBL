# HBL §2.13 — sharp lower bound for any one-sided C² curvature repair (2026-11-10)

**Paper-level rigorous lemma; no new Lean compile and no original-environment acceptance. Original revised strict count: 11/13.** This note complements the original same-source inner/spectral C² identity and broad-patch upper bound in `HBL_213_INNER_C2_EXACT_SOURCE_MISMATCH_20261110.md`.

## 1. A source derivative trace obstruction independent of repair width and shape

Let \(L,h,a>0\), \(Q\in\mathbb C\), and \(P\in C^3([L,L+h];\mathbb C)\) satisfy

\[
 P(L)=P'(L)=0,\quad P''(L)=\Delta_2,\qquad
 P(L+h)=P'(L+h)=P''(L+h)=0 .
 \tag{S1}
\]

These are precisely the left one-sided curvature data required to upgrade a genuine \(C^1\) inner/spectral Hartree join to \(C^2\), and the right zero jets of a compact curvature repair that does not modify the next interface. Define the **same original frozen Kummer operator**

\[
 \mathcal K_aP=P''+\left(\frac2y+\frac{iy}{2a^2}\right)P'
    +\frac{Q}{a^2}P,\qquad f:=\mathcal K_aP .
 \tag{S2}
\]

By the endpoint jets in (S1), irrespective of \(Q,a\),

\[
 f(L)=\Delta_2,\qquad f(L+h)=0.
 \tag{S3}
\]

The fundamental theorem of calculus and the *weighted* Cauchy--Schwarz inequality give the exact trace inequality

\[
 \begin{aligned}
 |\Delta_2|
 &=\left|\int_L^{L+h} f'(y)\,dy\right|\\
 &\le
 \left(\int_L^{L+h}(1+y^2)^2|f'(y)|^2\,dy\right)^{1/2}
 \left(\int_L^{L+h}(1+y^2)^{-2}\,dy\right)^{1/2}.
 \end{aligned}
 \tag{S4}
\]

Consequently,

\[
 \boxed{\quad
 \|(1+y^2)(\mathcal K_aP)'\|_{L^2(L,L+h)}
 \ \ge\
 \frac{|\Delta_2|}
 {\bigl[\int_L^{L+h}(1+y^2)^{-2}\,dy\bigr]^{1/2}}
 \ \ge\ \sqrt3\,L^{3/2}|\Delta_2|.
 \quad}
 \tag{S5}
\]

The last inequality uses only
\(\int_L^{L+h}(1+y^2)^{-2}dy
\le\int_L^\infty y^{-4}dy=(3L^3)^{-1}\).
There is **no dependence on the left-endpoint radius \(L/a\), the repair width \(h\), the Kummer parameter \(Q\), or the scale \(a\)**. The first bound is the sharp weighted endpoint trace bound for general \(f\) with these endpoint values; no claim is made that its optimizer necessarily lies in the more restricted image \(f=\mathcal K_aP\) with all the prescribed jets.

For the actual broad patch \(h=L/4\), the stronger elementary bound

\[
 \int_L^{5L/4}(1+y^2)^{-2}dy
 \le\frac{1-(4/5)^3}{3L^3}=\frac{61}{375L^3}
\]

implies

\[
 \boxed{\quad
 \|(1+y^2)(\mathcal K_aP)'\|_{L^2(L,5L/4)}
 \ge\sqrt{\frac{375}{61}}\,L^{3/2}|\Delta_2|.
 \quad}
 \tag{S6}
\]

Under the *explicit* broad-patch hypotheses \(a\ge L^3\), \(|Q|\le Q_0\), \(L>2\), and \(aB\ge5L/4\), the already derived construction has the matching **upper** scale
\(\|(1+y^2)(\mathcal K_aP_{L/4})'\|_2
\le C_{\eta,Q_0}L^{3/2}|\Delta_2|\).
Thus the \(L^{3/2}|\Delta_2|\) factor is **optimal in scale for the local compact C² curvature-repair mechanism**. Widening the patch, choosing a different smooth cutoff, or moving its outer edge cannot eliminate this factor.

## 2. Actual physical selected-source interpretation

For the original physical two-channel Hartree inner profile and its same-source spectrally corrected Green profile, the exact interface cancellation already yields

\[
 \Delta_2(s)
 =D_{\rm in}(s,L(s))
 +a(s)^{-2}\delta(s)u_0(s,L(s)/a(s)).
 \tag{S7}
\]

The strict Lean CI 42854633900 verifies a source-dependent curvature-jump **bound** at a fixed slice, subject to its visible same-source and regularity hypotheses. It does **not** prove temporal decay or justify a nonlinear orbit.

If one wishes to estimate **the patch forcing derivative as a separate source term** by \(O(s^{-p})\), (S5) imposes the genuine **necessary** trace condition

\[
 \boxed{\quad
 |D_{\rm in}(s,L(s))
  +a(s)^{-2}\delta(s)u_0(s,L(s)/a(s))|
 \lesssim L(s)^{-3/2}s^{-p}.
 \quad}
 \tag{S8}
\]

Here \(p\) may be \(15/8\), \(17/8+\eta\), or \(9/4\), according to the *stated* target norm. The modulation law yields only a slowly growing \(L(s)\), not \(L\sim s^{1/2}\); see `HBL_213_ACTUAL_MODULATION_PATCH_GEOMETRY_CORRECTION_20261110.md`.

**Exact scope.** (S5)–(S8) are **not** a lower bound for the complete four-region nonlinear Hartree PDE residual: the original source may cancel the local patch forcing at the same spatial location, and a projected propagator might exploit further structure. Nor does this imply \(\Delta_2\ne0\). What is decisively ruled out is a proposed shortcut that makes the *separately estimated C² patch derivative* arbitrarily cheaper by only optimizing its cutoff shape or support length. A shorter genuine closure route must instead exploit the **same-source curvature cancellation/physical \(\Delta_2\)** or prove a cancellation **after combining the full nonlocal PDE residual**, together with true moving-parameter derivatives and a Hartree-specific projected inverse. The revised-original counter stays **11/13**.
