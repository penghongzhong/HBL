# HBL §2.13: source-produced half-power weighted L² and backward-shell gain

11 November 2026. This is a spatial estimate **for the actual original inverse-square quartic Hartree ten-term interaction**, *conditional only on the genuine physical radiation amplitude/Strauss hypotheses already present in the source producer*. No positive time power or physical PDE orbit is postulated. Original theorem environments remain **11/13**.

Let \(0<\ell\le1\), \(L=\ell^{-1/16}\), and \(\mathcal S_H(\ell,c,z;r)\) be the original ten-term Hartree interaction, with the full convolution evaluated before applying the cutoff. Define
\[
G(r)=r(1-\chi(r/L))\mathcal S_H(\ell,c,z;r),\quad
S(r)=\langle r\rangle^{7/4}|G(r)|,\quad
K=C_{\rm slow}(B,A).
\]
The new source-produced *pointwise* theorem in \`ActualHartreeSlowInnerHalfPowerSource.lean\` gives
\[
0\le S(r)\le K\ell^{1/2}(1+r)^{-5/4},\qquad r>0.
\]
Integrating its square (with the actual half-line \(dr\) measure) yields
\[
\boxed{\int_0^\infty S(r)^2\,dr\le K^2\ell
\int_0^\infty(1+r)^{-5/2}\,dr=\frac23K^2\ell.}
\]
Thus \(\|S\|_2\le\sqrt{2/3}\,K\ell^{1/2}\). The stronger length exponent \(1/2\) is **derived**; the previous general localized bound yielded only \(1/16\). The companion Lean theorem \`actual_Hartree_slow_inner_half_power_weighted_L2\` states exactly the integral inequality and weighted membership. It is a new CI target, **not accepted until its raw job and axioms are successful**.

There is a complementary *physical* backward-shell gain. The same genuine ten-term pointwise theorem gives \(|\mathcal S_H(r)|\le K\ell^{1/2}(1+r)^{-4}\) on the true source region \((0,2L]\). Therefore, on the actual Cramer/Volterra backward overlap \(I=[L/2,L]\),
\[
\begin{aligned}
\|\mathcal S_H\|_{L^2(I)}^2
&\le K^2\ell\int_{L/2}^{L}(1+r)^{-8}\,dr\\
&\le K^2\ell\int_{L/2}^{L}r^{-8}\,dr
=\frac{127}{7}K^2\ell L^{-7},
\end{aligned}
\]
hence
\[
\boxed{\|\mathcal S_H\|_{L^2([L/2,L])}
\le\sqrt{127/7}\;K\ell^{23/32}.}
\]
This is a genuine source component in the same overlap used by the radius-uniform Volterra curvature estimate. It **does not bound the full curvature mismatch** \(K_{a,Q}(u-v)\), which also includes selected-speed, spectral correction, and frozen-to-physical Hartree-Hessian discrepancy terms. Nor does it give source derivatives (the stated amplitude/Strauss hypotheses on \(z\) do not imply them).

The existing C³ repair is still uninstantiable from mere weighted L² plus continuous source inputs, as proved by the Fredholm-compatible \(C^2\) counterexample. The source-faithful *smooth backward overlap*, which does not sample \(F(B)\) or \(F'(B)\), remains the shorter candidate; the actual curvature RHS and full nonlocal time/parameter estimates must be proved. The earlier exact four-piece PDE telescope remains an identity only.

**Acceptance:** §2.13 and the final PDE-derived Type-II rate are open; formal original count **11/13**. No auxiliary Lean pass raises that count.
