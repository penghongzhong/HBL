# HBL §2.13 — sharp strong-source cost of a moving C³ Hermite interface patch

11 November 2026. **Paper-level source-space gate, not a new Lean theorem or original §2.13 acceptance.** This is a quantitative continuation of \`HBL_213_MOVING_C3_REPAIR_L2_TIME_AND_HARTREE_20261111.md\`. It isolates the local second-order PDE source cost *before* estimating the genuine Hartree convolution, and shows why shrinking an interface layer cannot by itself produce a small time-differentiated strong residual.

Write \(t=(r-L(s))/h(s)\), \(0<h\le L\), and
\[
 \phi_2(t)=\tfrac12t^2(1-t)^4(1+4t),\qquad
 \phi_3(t)=\tfrac16t^3(1-t)^4,\qquad
 P=h^2d_2\phi_2(t)+h^3d_3\phi_3(t)
\]
on \(L<r<L+h\), with zero extension. Here \(d_2,d_3\) must ultimately be the **actual** interface jets of the same selected four-region physical Hartree field, not independently postulated small parameters. Put \(N_j=\|\phi_j'\|_{L^2(0,1)}\), \(C_j=\|\phi_j''\|_{L^2(0,1)}\), \(T_j=\|\phi_j'''\|_{L^2(0,1)}\). Direct exact polynomial integration gives
\[
\begin{array}{c|ccc}
j&N_j^2&C_j^2&T_j^2\\\hline
2&73/18018&50/231&100/7\\
3&1/90090&2/3465&4/63
\end{array}. \tag{SS1}
\]
(The six rational values were independently recomputed by exact symbolic polynomial integration, not numerically fitted.)

## 1. Actual local Laplacian source norm

Inside the physical shell the *exact* radial Laplacian is
\[
 \Delta_rP=d_2\phi_2''+h d_3\phi_3''
   +\frac2r(hd_2\phi_2'+h^2d_3\phi_3'). \tag{SS2}
\]
Using \(4\pi r^2dr\) and \(L\le r\le L+h\), this implies the derived, non-hypothesized bound
\[
 \|\Delta P\|_{L^2(\mathbb R^3)}
 \le \sqrt{4\pi}(L+h)\sqrt h\left[
 |d_2|\Big(C_2+\frac{2h}{L}N_2\Big)
 +h|d_3|\Big(C_3+\frac{2h}{L}N_3\Big)\right].\tag{SS3}
\]
The radial \(\Delta P\) has an ordinary \(L^2\) representative, since \(P\) and \(P_r\) are continuous at both boundaries. This does **not** yet estimate the complete selected Hartree PDE residual, which includes \(W_s\), \(\Delta W\), and the nonlocal interaction.

## 2. Exact moving-time derivative, including interface measures

At fixed physical radius on the open shell,
\[
\begin{aligned}
(\partial_s\Delta_rP)_{\rm reg}
={}&d_2'\phi_2''+(h'd_3+hd_3')\phi_3''
-\frac{L'+th'}h(d_2\phi_2'''+hd_3\phi_3''')\\
&+\frac2r\left[
 (h'd_2+hd_2')\phi_2'
 +(2hh'd_3+h^2d_3')\phi_3'
 -(L'+th')(d_2\phi_2''+hd_3\phi_3'')
\right]. \tag{SS4}
\end{aligned}
\]
All basis functions in (SS4) are evaluated at \(t\). Set \(M=|L'|+|h'|\), and
\[
\begin{aligned}
\mathfrak T_{\rm reg}:={}&|d_2'|C_2+(|h'||d_3|+h|d_3'|)C_3
 +M\left(\frac{|d_2|}{h}T_2+|d_3|T_3\right)\\
 &+\frac2L\left[
 (|h'||d_2|+h|d_2'|)N_2+
 (2h|h'||d_3|+h^2|d_3'|)N_3+
 M(|d_2|C_2+h|d_3|C_3)\right].
\end{aligned}
\]
Then
\[
 \|(\partial_s\Delta_rP)_{\rm reg}\|_{L^2(\mathbb R^3)}
 \le \sqrt{4\pi}(L+h)\sqrt h\,\mathfrak T_{\rm reg}. \tag{SS5}
\]
There is also the **distributional** term
\[
 \partial_s(\Delta_rP)
 =(\partial_s\Delta_rP)_{\rm reg}\mathbf1_{(L,L+h)}
 -L'd_2\,\delta_{r=L}. \tag{SS6}
\]
The outgoing \(L+h\) endpoint has \(\Delta_rP=0\), hence no measure. As already checked in the preceding note, the *same* unrepaired \(C^1\) physical field \(W\) has exactly the opposite \(+L'd_2\,\delta_{r=L}\), so \(\partial_s\Delta_r(W+P)\) has no interface measure. **Never** estimate the separate full distribution (SS6) in \(L^2\); it is not in that space when \(L'd_2\ne0\).

## 3. Sharp width tradeoff and an obstruction to thin-layer optimization alone

Consider the fully explicit admissible moving family \(d_3=0\), \(h'=d_2'=0\), \(d_2\ne0\), \(L'\ne0\), and \(0<h\le L/10\) at one time. Reverse triangle inequalities in (SS2) and (SS4) give
\[
\begin{aligned}
\|\Delta P\|_2
&\ge\sqrt{4\pi}L\sqrt h\,|d_2|
 \left[C_2-\frac{2h(L+h)}{L^2}N_2\right]
 \ge\frac{\sqrt{4\pi}}2C_2 L\sqrt h\,|d_2|,\\
\|(\partial_s\Delta P)_{\rm reg}\|_2
&\ge\sqrt{4\pi}\frac{L}{\sqrt h}|L'd_2|
 \left[T_2-\frac{2h(L+h)}{L^2}C_2\right]
 \ge\frac{\sqrt{4\pi}}2T_2\frac{L}{\sqrt h}|L'd_2|.
\end{aligned}\tag{SS7}
\]
The last inequalities follow from the exact rational constants (SS1) and \(2h(L+h)/L^2\le11/50\). Therefore
\[
\boxed{\quad
 \|\Delta P\|_2\,\|(\partial_s\Delta P)_{\rm reg}\|_2
 \ge \pi C_2T_2 L^2|L'|\,|d_2|^2.
 \quad}\tag{SS8}
\]
Meanwhile \(P_s=-L'hd_2\phi_2'\) on the shell gives
\[
 \|P_s\|_2\le\sqrt{4\pi}(L+h)h^{3/2}|L'd_2|N_2,\qquad
 \frac{\|(\partial_s\Delta P)_{\rm reg}\|_2}{\|P_s\|_2}
 \ge\frac{5T_2}{11N_2}\,h^{-2}. \tag{SS9}
\]
Thus \(\|P_s\|_2\to0\) at rate \(h^{3/2}\) as a shell is narrowed, while its individual strong second-order source-time cost can grow like \(h^{-1/2}\). Making the repair shell thin **does not by itself** establish both a small spatial PDE residual and a small time-differentiated strong residual. Genuine smallness or cancellation of the actual \(d_2,d_2',L',h'\) and compensation by the same physical \(W\) is necessary.

This is a *counterexample to an attempted geometry-only inference*, **not** a no-go for the complete Hartree blowup construction: the full \(W\) may cancel regular terms as well as the interface measure. It does show that CR3/CR4 \(L^2\)-velocity and energy estimates alone cannot imply the original required strong residual gain.

## 4. Honest acceptance boundary

All formulas (SS1)–(SS9) are paper calculations. No new \`--trust=0\` Lean build, axiom audit, completed four-region temporal gain, parameter Lipschitz, original §2.13 theorem, or dynamic Type-II rate is asserted. The verified four-region PDE telescope is algebraic and does not remove this analytic requirement. The **only valid original-environment count remains 11/13**. The next essential producer is the *same selected physical PDE orbit*: actual \(d_j,d_j',L',h'\), full \(W_s\), two-real-speed Jacobian, and a joint strong residual estimate **after** distributional cancellation; then finite-layer induction and a dynamically derived Type-II law.