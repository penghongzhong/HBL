# HBL §2.13 — moving physical C³ repair: exact L² time cost, genuine Hartree feedback, and cancellation of interface measures

11 November 2026. **Paper-level calculation; no new Lean certificate or original-environment acceptance.** This links the pre-existing actual second/third-jet Hermite repair to the genuine seven-factor inverse-square Hartree radial \(L^2\)-velocity estimate (RV1–RV4). The original revised count is **11/13**.

## 1. A moving repair with no independent boundary parameters

Let \(s\mapsto L(s),h(s)>0\) and the **actual** curvature and third-jet discrepancies \(d_2(s),d_3(s)\in\mathbb C\) be \(C^1\), with \(0<h\le L\). Put
\[
\phi_2(t)=\tfrac12t^2(1-t)^4(1+4t),\qquad
\phi_3(t)=\tfrac16t^3(1-t)^4,\qquad t=(r-L)/h.
\]
On \(L\le r\le L+h\), set
\[
P(s,r)=h^2d_2\phi_2(t)+h^3d_3\phi_3(t),
\]
and extend \(P=0\) otherwise. The endpoint identities are
\[
 (P,P_r,P_{rr},P_{rrr})(L+)=(0,0,d_2,d_3),\qquad
 (P,P_r,P_{rr},P_{rrr})((L+h)-)=(0,0,0,0).
\]
Thus if the *actual* uncorrected piecewise field has jumps \([W_{rr}]_L=-d_2\), \([W_{rrr}]_L=-d_3\), then \(W+P\) is \(C^3\) at this interface, without modifying the matched value and slope. These actual jumps must still be computed from the same four-region physical PDE source and uniquely selected real speeds; they are not freely chosen or assumed small.

Differentiate at **fixed physical radius**. Writing primes for \(d/ds\),
\[
\boxed{\begin{aligned}
 P_s={}&h^2d_2'\phi_2+h^3d_3'\phi_3\\
 &+hh'd_2(2\phi_2-t\phi_2')
   +h^2h'd_3(3\phi_3-t\phi_3')\\
 &-L'(hd_2\phi_2'+h^2d_3\phi_3').
\end{aligned}}\tag{CR1}
\]
Since both endpoint values of \(P\) vanish, differentiating its moving support creates **no Dirac term in \(P_s\)**. The expression (CR1), extended as zero outside the shell, is an \(L^2\)-velocity whenever the indicated jets and moving parameters are finite.

## 2. Explicit shell geometry and exact polynomial constants

For physical radial \(L^2(\mathbb R^3)\), using \(4\pi r^2dr\) and \(r\le L+h\) on the shell, set
\[
M_j=\|\phi_j\|_{L^2(0,1)},\quad
N_j=\|\phi_j'\|_{L^2(0,1)},\quad
Q_j=\|j\phi_j-t\phi_j'\|_{L^2(0,1)}.
\]
Elementary polynomial integration gives **exactly**
\[
\begin{array}{c|ccc}
j&M_j^2&N_j^2&Q_j^2\\ \hline
2&43/180180&73/18018&20/9009\\
3&1/1621620&1/90090&4/405405
\end{array}\tag{CR2}
\]
(the identities follow by expanding the two displayed polynomials, not by numerical fitting). Consequently, defining **derived**, not hypothesized, instantaneous budgets
\[
\boxed{\begin{aligned}
\mathfrak G(s)&:=\sqrt{4\pi}(L+h)\sqrt h\,
        (h|d_2|N_2+h^2|d_3|N_3),\\
\mathfrak V(s)&:=\sqrt{4\pi}(L+h)\sqrt h\,[\,
     h^2|d_2'|M_2+h^3|d_3'|M_3\\
&\hspace{1.5cm}+|h'|(h|d_2|Q_2+h^2|d_3|Q_3)
 +|L'|(h|d_2|N_2+h^2|d_3|N_3)\,],
\end{aligned}}\tag{CR3}
\]
one has
\[
\boxed{\|\nabla P(s)\|_{L^2(\mathbb R^3)}\le\mathfrak G(s),
\qquad \|P_s(s)\|_{L^2(\mathbb R^3)}\le\mathfrak V(s).}\tag{CR4}
\]
Here \(\nabla P\) is the gradient of the radial field \(P(|x|)\), not a one-dimensional unweighted derivative. There is no singular negative power of the Kummer left endpoint \(L/a\). On the other hand the actual \(d_2',d_3',L',h'\) have not yet been obtained from the selected PDE dynamics.

## 3. Hartree feedback derivative actually produced by these jets

Let \(W(s)\) be the *literal uncorrected* radial physical field (including the original selected two-channel source), assume \(W\in C^1_sL^2_{\rm rad}\cap C_s\dot H^1_{\rm rad}\), and compare \(U=W+P\) with \(V=W\) in the genuine inverse-square quartic Hartree expression
\(\mathcal N_H(Z)=\kappa_H(|x|^{-2}*|Z|^4)|Z|^2Z\).
With
\[
E:=2\|\nabla W\|_2+\mathfrak G,\qquad
V_W:=\|W_s\|_2,
\]
the *actual* fields satisfy
\[
D=\|\nabla(U-V)\|_2\le\mathfrak G,\quad
D_2=\|U_s-V_s\|_2\le\mathfrak V,\quad
V_2\le2V_W+\mathfrak V.
\]
Substitution into the previously proved real-seven-multilinear radial bound (RV3) now eliminates the formerly uncomputed repair velocity:
\[
\boxed{\begin{aligned}
\left|\int_L^{T_{\rm out}}r B(s,r)
       \partial_s[\mathcal N_H(W+P)-\mathcal N_H(W)](r)\,dr\right|
\le {}&
7\kappa_H A_0C_{\rm wk}L^{-3/2}\\
&\cdot\left[
 E^6\mathfrak V+6E^5(2V_W+\mathfrak V)\mathfrak G\right].
\end{aligned}}\tag{CR5}
\]
Here \(T_{\rm out}>L\) is the genuine selected outgoing Green endpoint, \(B\) its origin-normalized oscillatory Kummer weight, and \(A_0=\sup_{[L,T_{\rm out}]}|B|\). The estimate controls the **full nonlocal feedback**, not just points in the repair shell: the Hartree potential is integrated on all \(\mathbb R^3\). Nothing assumes that the nonlinear increment is compactly supported.

For the *moving* singular Cramer coefficient of this feedback, insert \(\mathfrak G,\mathfrak V\) into the exact physical-coordinate Leibniz identity (MT4) and estimate (RV4). Writing \(A_t,A_r\) for the **observed** moving Kummer basis suprema,
\[
\boxed{\begin{aligned}
|\mathcal C_{\rm repair}'(s)|\le{}&
 7C_0A_0E^6\mathfrak G
   (|L'|L^{-3/2}+|T_{\rm out}'|T_{\rm out}^{-3/2})\\
&+7\kappa_H A_0C_{\rm wk}L^{-3/2}
 [E^6\mathfrak V+6E^5(2V_W+\mathfrak V)\mathfrak G]\\
&+14C_0E^6\mathfrak G L^{-1/2}
 [A_t+|a'/a|(A_r+T_{\rm out}^2A_0/(2a^2))].
\end{aligned}}\tag{CR6}
\]
Here \(C_0=\kappa_Hc_*^3C_*\) is as in (MT1)–(MT5). This is **an inequality in genuine physical jets and velocities**, not an assumed small time-order. It does not bound the second real Cramer channel automatically, nor the remaining linear/transmission residual.

## 4. Distributional moving-interface gate: the correction must remain attached to the physical field

Although \(P_s\in L^2\), it is generally **false** that its second spatial derivative has an ordinary \(L^2\) time derivative by itself. For the radial Laplacian \(\Delta_r=\partial_r^2+2r^{-1}\partial_r\),
\[
 [\Delta_rP]_{r=L}=d_2,\qquad
 \partial_s(\Delta_rP)
 =-L'd_2\,\delta_{r=L}+\text{piecewise regular terms}.
 \tag{CR7}
\]
There is no such measure at \(L+h\), where the second jet of \(P\) vanishes. By the definition \(d_2=W_{rr}(L-)-W_{rr}(L+)\) and \(C^1\) matching of \(W\),
\[
[\Delta_rW]_{r=L}=-d_2,\qquad
\partial_s(\Delta_rW)=+L'd_2\,\delta_{r=L}
 +\text{piecewise regular terms}.
\]
Therefore the two interface measures cancel **exactly** in the corrected *same-orbit* field:
\[
\boxed{\bigl(\partial_s\Delta_r(W+P)\bigr)_{\rm interface\ measure}=0.}\tag{CR8}
\]
This is a distributional calculation with \(\delta_{r=L}\) relative to the \(dr\) coordinate; when paired in radial three-dimensional measure the factor \(4\pi L^2\) is included. The \(C^3\) jet repair also removes the spatial derivative jump of \(\Delta_r(W+P)\). A proof that estimates \(\partial_s\Delta_rP\) and \(\partial_s\Delta_rW\) separately in a strong source space without first taking (CR8) is invalid: their individual norms may be infinite.

## 5. Acceptance boundary

(CR1)–(CR8) are paper calculations. The polynomial integrations have been independently checked symbolically, but **no newly built Lean module or strict CI** proves this moving-time bridge. The previously strictly certified finite spectral four-piece PDE telescope (CI 42958494409) remains an identity, not a residual gain. Its Lean source blob at the latest HEAD is unchanged from the certified run.

**True remaining original gates:** derive \(d_2,d_3,d_2',d_3',L',h',W_s\) from the *same* physical selected Hartree orbit, including both real compatibility speeds; construct the full \(C^3\) repair at all three interfaces without corrupting the Fredholm selector; derive the two real-speed Jacobian and genuine moving Kummer basis bounds; prove positive time order and parameter Lipschitz of the entire **strong** four-region nonlocal Hartree PDE residual after (CR8); close real finite-layer induction; and infer the II-type law from the dynamics. **No independent temporal decay, assumed source envelope, or prescribed blowup rate.** Formal original acceptance stays **11/13**.
