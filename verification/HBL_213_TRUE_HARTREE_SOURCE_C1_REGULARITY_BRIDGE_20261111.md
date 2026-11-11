# HBL §2.13 — exact regularity threshold for the genuine Hartree forcing

11 November 2026. **Paper-only result; no new Lean compilation, no change to the original 11/13.** This checks a *logical implication* needed to instantiate the verified three-C¹ joins from the verified measurable-source selector, and supplies a constructive sufficient source-regularity bridge. Neither part proves a PDE time-gain or a blowup rate.

## 1. The precise mismatch in existing kernel statements

- \`actual_Hartree_true_nonlocal_source_selects_unique_real_speed\` takes \`Measurable z\` together with positive-radius bounds \`‖z y‖ ≤ Bz\` and \`y‖z y‖ ≤ Az\` for \`y ≥ 1\`. It produces a unique two-real-parameter Cramer selector, not spatial continuity of the source.
- \`actual_Hartree_origin_outgoing_gain_on_annulus\` gives \`IntervalIntegrable F\` and a volume-a.e. Green ODE, not an everywhere classical forcing identity.
- \`actual_Hartree_spectral_inner_four_piece_three_C1_joins\` explicitly takes \`hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r\`; its conclusion is exactly three \`HasDerivAt\` statements, not a C³ trace or a dynamic source estimate.
- \`actual_Hartree_adjusted_Kummer_source_continuousAt\` only propagates *already-established* continuity of the unadjusted physical forcing through the speed terms. It cannot create continuity from measurability.

Thus the exact \`hF\` bridge is not present in these theorem types. More strongly, it is FALSE without extra regularity of the original radiation, as the following example shows.

## 2. A counterexample using the SAME complete inverse-square Hartree interaction

Fix the genuine c=0 positive real bubble V(r)>0, a radius R>0, and t>0. In physical variables let
\[
 Z(r)=t\,{\bf1}_{[R,2R]}(r),\qquad
 K(x)=|x|^{-2},\quad Q_H=K*|H|^4,\quad C(H)=|H|^2H.
\]
The original complete mixed physical interaction is exactly
\[
 {\cal S}_H(V,Z)= Q_{V+Z}C(V+Z)-Q_V C(V)-Q_Z C(Z).
 \tag{SC1}
\]
This follows by algebraically combining all three Riesz potentials in the original \`actualOneLayerInteractionOnly\`, not by replacing the nonlocal physics with an arbitrary forcing.

All three potentials are continuous on \(\mathbb R^3\): their densities belong to \(L^1\cap L^\infty\), and \(K\) is locally integrable. The local cubic factor is discontinuous at R. Write \(v=V(R)>0\). The right-minus-left radial jump of the *complete* source at R is
\[
 \begin{aligned}
 J_R
 &=Q_{V+Z}(R)\big((v+t)^3-v^3\big)-Q_Z(R)t^3\\
 &\ge Q_Z(R)\big(3v^2t+3vt^2\big)>0,
 \end{aligned}\tag{SC2}
\]
since \(Q_{V+Z}\ge Q_Z>0\) for these nonnegative fields. In particular the genuine three-potential structure does **not** cancel the jump.

To fit the literal radiation bounds, choose \(z(y)=\varepsilon{\bf1}_{[1,2]}(y)\), \(Z_\ell(r)=\sqrt\ell\,z(\ell r)\), \(0<\ell<1/L\), \(c=0\), \(B_z=\varepsilon\), \(A_z=2\varepsilon\). This z is measurable and satisfies both original pointwise envelopes. Its source jump occurs at \(R=\ell^{-1}>L\). Choose an allowed sufficiently large \(a\) with \(L/a<R/a<B\) (in particular \(a\ge L^3\)); the original scaled forcing
\[
 F_a(r)=a^2\,{\cal S}_H(V,Z_\ell)(ar)
 \tag{SC3}
\]
has a nonzero jump at \(r=R/a\), strictly inside the selected annulus. The sign convention \(-F_a\) in the speed selector changes only the sign of the jump. Therefore the measurable original source class does **not** imply the continuity premise \`hF\` of the classical three-C¹ theorem.

This is an obstruction to composing existing **unrestricted theorem types**, NOT a counterexample to the smoother physical orbit that the paper aims to construct.

## 3. A constructive sufficient C¹ source-regularity bridge

Let \(\rho:\mathbb R^3\to\mathbb R\) be in \(L^1\cap L^\infty\), and locally \(C^{0,\alpha}\) on the unit neighborhood of a compact positive-radius annulus \(A\), with \(0<\alpha\le1\). Put \(P=K*\rho\). By splitting at \(|x-y|=1\),
\[
 \sup_{x\in A}|P(x)|
 \le 4\pi\|\rho\|_\infty+\|\rho\|_1 .
 \tag{SC4}
\]
The odd singular derivative kernel has zero integral over centered balls. For \(x\in A\) its exact compensated gradient is
\[
 \nabla P(x)=-2\int_{\mathbb R^3}
 \frac{x-y}{|x-y|^4}\big[
 \rho(y)-\rho(x){\bf1}_{\{|x-y|<1\}}\big]\,dy.
 \tag{SC5}
\]
The near-field integrand is absolutely integrable by the Hölder difference; the far-field part by \(L^1\). If \(H_A\) is a common \(C^{0,\alpha}\) seminorm for \(\rho\) on the unit neighborhood of \(A\), then
\[
 \sup_{x\in A}|\nabla P(x)|
 \le\frac{8\pi}{\alpha}H_A+2\|\rho\|_1.
 \tag{SC6}
\]
The standard symmetric truncation of \(K\), followed by dominated convergence after the local subtraction, proves \(P\in C^1(A)\) with gradient (SC5). No uniform smallness in time follows from these pointwise bounds.

For a complex radial \(W\), if \(|W|^4\in L^1\cap L^\infty\) and \(W\) is locally \(C^1\) on a positive-radius annulus, then \(|W|^4\) is locally Lipschitz there; consequently
\[
 {\cal N}_H(W)=\kappa_H (K*|W|^4)|W|^2W\in C^1(A),
\]
and
\[
 \partial_r{\cal N}_H(W)
 =\kappa_H\big[
  (\partial_rP_W)|W|^2W+
  P_W\{2\operatorname{Re}(\overline W W_r)W+|W|^2W_r\}
 \big].
 \tag{SC7}
\]
The *actual* complete interaction (SC1) is a difference of three such terms, so it is \(C^1\) whenever the genuine physical core and radiation satisfy the stated local \(C^1\) regularity and the global density integrability. In physical-to-Kummer coordinates \(F_a(r)=a^2{\cal S}_H(ar)\), this gives \(F_a\in C^1\) locally and
\(\partial_rF_a(r)=a^3(\partial_R{\cal S}_H)(ar)\). The \(a^3\) factor is explicit: it must not be silently treated as a uniform gain.

## 4. Remaining exact proof obligations

The selected Hartree **orbit**, not the measurable speed-selector source class, must produce the local \(C^1_r\) radiation estimates and sufficient source moment bounds needed by (SC5)–(SC7). The positive temporal decay of those bounds must arise from the physical PDE. One then needs differentiated two-dimensional compatibility, three one-sided C³ physical jets or a justified lower-regularity overlap argument, moving endpoints/Kummer basis, full four-region strong source gain and parameter Lipschitz, finite-layer recursion, and the dynamically derived Type-II rate.

The accepted four-piece PDE telescope [CI 42958494409](https://github.com/penghongzhong/HBL/actions/runs/42958494409), job 130319187052, has a trust-zero exact-type/axiom audit (only \`propext\`, \`Classical.choice\`, \`Quot.sound\`). It proves the algebraic identity, not the source regularity or temporal gain above. The prior failed [CI 42530158681](https://github.com/penghongzhong/HBL/actions/runs/42530158681) is superseded for that **same** telescoping module, not for revised original §2.13.

**No newly accepted original environment. Revised §2.13 remains unclosed; formal count 11/13 (84.62%).**