# HBL §2.13 — moving regularized Kummer left jet and nonzero-jet source stability

11 November 2026. Paper-level calculation, **not a new Lean theorem**. Revised original acceptance **11/13**.

## Moving operator, genuine physical source, and weighted left jet

Let \(a(s)>0\), \(c(s)\in\mathbb C\), \(\alpha=a^{-2}\), and let \(u(s,r)\) solve the *same actual* selected-source equation
\[
 \mathcal K_su:=u_{rr}+2r^{-1}u_r+
 \alpha(s)(\tfrac{i}{2}ru_r+c(s)u)=F(s,r).
\]
All temporal and spatial derivatives below are classical on the swept positive-radius overlap. Differentiate at **fixed** radius, and use \(\alpha_s=-2(a_s/a)\alpha\):
\[
 \boxed{\mathcal K_su_s=F_s+
  2(a_s/a)\alpha(\tfrac{i}{2}ru_r+cu)-\alpha c_su.}\tag{MJ1}
\]
This does not differentiate the Kummer fundamental solutions. It is a source identity; it does *not* estimate \(F_s\) for the selected Hartree orbit.

For a \(C^1\) moving left endpoint \(\rho(s)>0\), denote the **total** matching traces by \(U(s)=u(s,\rho(s))\), \(V(s)=u_r(s,\rho(s))\). The chain rule gives \(u_s(s,\rho)=U_s-\rho_sV\), \(u_{sr}(s,\rho)=V_s-\rho_su_{rr}(s,\rho)\). Insert the *same* equation into the last term to obtain
\[
 \boxed{\rho u_s(s,\rho)=\rho U_s-\rho\rho_sV,}\tag{MJ2}
\]
\[
 \boxed{\begin{aligned}
 \rho^2u_{sr}(s,\rho)+\rho u_s(s,\rho)
 ={}&\rho^2V_s+\rho U_s\\
 &-\rho_s\{\rho^2 F(s,\rho)-\rho V
 -\alpha(\tfrac{i}{2}\rho^3V+c\rho^2U)\}.
 \end{aligned}}\tag{MJ3}
\]
These are precisely the origin-regularized value and slope coordinates already used in the successful zero-left Volterra Lean chain. Neither right-hand side has an explicit negative power of the shrinking Kummer left radius. However, the actual \(\rho_s,U_s,V_s,F_s,a_s,c_s\) remain *uncontrolled*, and the total trace derivatives cannot be replaced by fixed-radius derivatives.

## Nonzero Cauchy data: fixed-annulus comparison using existing Lean-certified absorption

Fix \(R>0\), \(I=[R,2R]\), and a **common** anchor \(\rho\in I\). For \(j=1,2\), let \(\mathcal K_j=\Delta_r+\alpha_j(\tfrac{i}{2}r\partial_r+c_j)\), \(\alpha_j=a_j^{-2}>0\), and let the actual classical fields obey \(\mathcal K_ju_j=F_j\) on a neighborhood of \(I\). Put \(U_j=u_j(\rho)\), \(V_j=u_j'(\rho)\). Assume only the same frozen-operator smallness as the strict existing zero-jet absorption theorem:
\[
16R^2\alpha_j(1+|c_j|)\le1\quad(j=1,2).\tag{MJ4}
\]
Write \(A_j=\sup_I|F_j|\), \(B=\sup_I|F_1-F_2|\), \(\delta U=U_1-U_2\), \(\delta V=V_1-V_2\), and for any complex \(U,V\) define
\[
 H_{U,V}(r)=U+\rho V(1-\rho/r),\qquad
 H^0(U,V)=|U|+2R|V|,\quad H^1(U,V)=4|V|,
\]
\[
 J_j(U,V)=\alpha_j[|c_j||U|+2R(1+|c_j|)|V|].
\]
Direct computation gives \(H(\rho)=U\), \(H'(\rho)=V\), \(\Delta_rH=0\), and
\[
\sup_I|H|\le H^0,\quad\sup_I|H'|\le H^1,\quad
\sup_I|\mathcal K_jH|\le J_j.\tag{MJ5}
\]
The already strictly compiled **zero-Cauchy-jet** absorption theorem applies to \(z_2=u_2-H_{U_2,V_2}\), with \(Q_2=A_2+J_2(U_2,V_2)\), giving
\[
\sup_I|u_2|\le H^0(U_2,V_2)+8R^2Q_2,\qquad
\sup_I|u_2'|\le H^1(U_2,V_2)+8RQ_2.\tag{MJ6}
\]
By the exact *already certified* difference-of-operators formula
\[
 (\mathcal K_1-\mathcal K_2)u_2
 =(\alpha_1-\alpha_2)\tfrac{ir}{2}u_2'
   +(\alpha_1c_1-\alpha_2c_2)u_2,
\]
define the computed physical source budget
\[
\begin{aligned}
 Q_\delta={}&B+|\alpha_1-\alpha_2|R
 (H^1(U_2,V_2)+8RQ_2)\\
 &+|\alpha_1c_1-\alpha_2c_2|
 (H^0(U_2,V_2)+8R^2Q_2)
 +J_1(\delta U,\delta V).
\end{aligned}\tag{MJ7}
\]
Since \(w=u_1-u_2-H_{\delta U,\delta V}\) has both Cauchy values zero at the **same** \(\rho\) and satisfies
\[
\mathcal K_1w=F_1-F_2-(\mathcal K_1-\mathcal K_2)u_2
-\mathcal K_1H_{\delta U,\delta V},
\]
the same zero-jet theorem yields, for each \(r\in I\),
\[
\boxed{\begin{aligned}
|\Delta_r(u_1-u_2)(r)|&\le2Q_\delta,\\
|u_1(r)-u_2(r)|&\le|\delta U|+2R|\delta V|+8R^2Q_\delta,\\
|u_1'(r)-u_2'(r)|&\le4|\delta V|+8RQ_\delta .
\end{aligned}}\tag{MJ8}
\]
The first bound uses the exact \(\Delta_rH_{\delta U,\delta V}=0\). No independent basis derivative, zero value/slope assumption on *individual* physical fields, or invented time decay was used.

**Limits.** (MJ1)–(MJ8) are new *paper-level consequences* of real equations and earlier Lean-accepted operators, **not** a new strict CI acceptance. They compare a common fixed anchor; changes of the physical left endpoint require an additional moving pullback and real trace variation. \(A_j,B,\delta U,\delta V\) are observed source sizes, not derived positive time orders. The full genuine Hartree source derivative, two-real-speed Jacobian, strong \(C^2/C^3\) interface repair, positive-time-order full four-region residual, parameter Lipschitz, finite recurrence, and PDE-generated blowup rate remain open. Do not infer original §2.13 closure. **11/13.**
