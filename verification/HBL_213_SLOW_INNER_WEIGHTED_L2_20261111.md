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

## HBL_HALF_POWER_NOT_OUTER_SELECTOR_20261111: the selected-speed outer annulus is NOT covered

The stronger square-root source bound is valid on the **actual slow-inner domain** (0<r\le2L), (L=\ell^{-1/16}), and for its radially conjugated cutoff. It cannot replace the (Q=C_{\rm phys}(B,A)\ell^{1/8}) bound in `actual_Hartree_true_nonlocal_source_selects_unique_real_speed` on its **full original outer Cramer interval**: there (F(\rho)=-a^2\mathcal S_H(a\rho)) and physical (y=a\rho\in[L,aB]), with admissible choices (aB\gg2L). Thus the selector's original (\ell^{1/8}) constant must be retained until a separate all-annulus source argument is proved. This spatial support restriction prevents an illegitimate global time-gain upgrade.


## HBL_HALF_POWER_WEIGHTED_L2_STRICT_42952819526: exact pinned Lean Success (spatial source component only)

At source SHA `75970cf2fa21ea8dfc09ebe051ce6cf5983c9ef3`, [CI 42952819526](https://github.com/penghongzhong/HBL/actions/runs/42952819526), original job `130303403837`, evidence artifact `13826515899` (SHA256 `01e20b4ada001ca304d1a455f18318f4ef9da20dca5db76e1975e6136dea3b55`) have **strict Success**. GitHub's raw log shows the pinned Lean 4.35.0-rc3 / Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, `--trust=0`, `-DwarningAsError=true`, exact `#check` of `HBL.TypeIIDynamicSelection.actual_Hartree_slow_inner_half_power_weighted_L2` and its individual `#print axioms`, with precisely `[Classical.choice, Quot.sound, propext]`; no sorry/admit or extra axioms. The upstream physical source producer was actually rebuilt as a dependency at the repaired SHA. A separate workflow still audits the precise three upstream declarations; its earlier original run 42951761187 failed only on an extra `ring` command after a completed `field_simp`, now fixed.

**This proves the spatial weighted-square-integral estimate only.** It does not upgrade the entire selected Cramer annulus, full moving PDE residual, temporal gain, finite profile, or the final rate. Original revised **11/13**.


## HBL_HALF_POWER_INNER_NORM_BRIDGE_20261111: the genuine two real Fredholm inputs

For the *exact same* radially conjugated physical source \(G\) above (rather than an independently introduced pair), define \(g_+=\Re G\) and \(g_-=\Im G\). The existing \`actual_Hartree_conjugated_slow_inner_unique_solve\` theorem uses precisely these two functions. Positivity of the Japanese weight and \(|G|^2=g_+^2+g_-^2\) yield, with the actual \`innerWeightedNorm\` definition,
\[
\|g_+\|_{2,7/4}^2+\|g_-\|_{2,7/4}^2
=\|\langle r\rangle^{7/4}G\|_2^2
\le \frac23 K^2\ell .
\]
By Cauchy–Schwarz,
\[
\boxed{N_{\rm H}:=\|g_+\|_{2,7/4}+\|g_-\|_{2,7/4}
\le\frac{2}{\sqrt3}K\ell^{1/2}.}
\]
On the actual backward overlap the previously derived source-faithful flat-cutoff estimate has an inner Fredholm-source term \(L^{-5/2}N\). **Only for this actual localized Hartree contribution**,
\[
L^{-5/2}N_{\rm H}\le\frac2{\sqrt3}K\ell^{21/32},
\qquad L=\ell^{-1/16}.
\]
This is an explicit bridge to the original two real half-line source norms and eliminates any invented second source envelope, but is *paper-only* (no additional strict Lean check). The total \(N\) in the full two-channel selected-speed/residual field also includes genuine modulation, spectral and off-slow-inner contributions, which are NOT covered by this inequality. No selected-speed or dynamical time-gain theorem follows.
