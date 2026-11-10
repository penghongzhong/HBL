# HBL §2.13: same-source moving-overlap `L² → C¹ ∩ H²` Volterra gate (10 November 2026)

**Mathematical paper derivation; not an accepted Lean theorem.** The 13 revised-original environments remain **11/13**. This estimate removes an *unnecessary* (L^\infty) source-norm and second-spatial-source-derivative requirement from the backward inner (C^1) overlap, but proves neither a time gain nor a complete Hartree orbit.

## 1. Original radial source and its fixed-radius conjugation

Fix a **positive actual physical radius** (L>0), original Kummer scale (a>0) and complex (Q=\mathrm{frozenZeroCoeff}(\mu,\theta)), with
\[
k=L^2/a^2>0,\qquad z=kQ,\qquad 4(k+|z|)\le1.
\tag{V1}
\]
Let the *actual same-source inner-minus-spectral field* (e\in C^2([L/2,L])) have the already-matched boundary jets (e(L)=e_y(L)=0). **Define the source, do not postulate an independent one:**
\[
f(y)=K_{a,Q}e(y)
=e_{yy}+\left(\frac2y+\frac{iy}{2a^2}\right)e_y
+\frac{Q}{a^2}e .
\tag{V2}
\]
With (x=y/L\in J=[1/2,1]), put (E(x)=e(Lx)), (G(x)=L^2f(Lx)). The exact original physical equation gives
\[
E_{xx}+\left(\frac2x+\frac{ikx}{2}\right)E_x+zE=G,
\qquad E(1)=E_x(1)=0.
\tag{V3}
\]
Crucially set (w=xE), *not* a separately selected Kummer fundamental solution. The radial (2/x) drift cancels:
\[
w_{xx}+\frac{ikx}{2}w_x+
          \left(z-\frac{ik}{2}\right)w=xG,
\qquad w(1)=w_x(1)=0.
\tag{V4}
\]
The \(-ik/2\) shift in (V4) is essential; it is the literal conjugated original operator, not the shifted spectral equation.

## 2. Explicit (L²\)-source (C¹\) estimate, independent of the physical left radius

Let (M=\|w_x\|_{L^\infty(J)}). Since (w(1)=0),
\[
|w(x)|\le(1-x)M.
\]
Integrating (V4) backward and using
\(\int_{1/2}^1x\,dx=3/8\),
\(\int_{1/2}^1(1-x)\,dx=1/8\), we get
\[
\begin{aligned}
M
&\le\int_J x|G(x)|\,dx+
\frac{k}{2}\!\int_Jx|w_x|\,dx+
\left(|z|+\frac{k}{2}\right)\!\int_J|w|\,dx\\
&\le\sqrt{7/24}\,\|G\|_{L^2(J)}
+\left(\frac{k}{4}+\frac{|z|}{8}\right)M\\
&\le\sqrt{7/24}\,\|G\|_{L^2(J)}+\frac1{16}M .
\end{aligned}
\tag{V5}
\]
Thus define the **numerical universal constant**
\[
C_0=\frac{16}{15}\sqrt{\frac7{24}}<1.
\tag{V6}
\]
Since (E=w/x\) and (E_x=w_x/x-w/x^2\), on (J\) we have
\[
\boxed{\quad
\|E\|_\infty\le C_0\|G\|_2,\qquad
\|E_x\|_\infty\le4C_0\|G\|_2.
\quad}\tag{V7}
\]
There is **no independently assumed (\|G\|_\infty\)**, no left-radius loss, and no differentiated Kummer basis.

Finally (V3), (2/x\le4\), (kx/2\le1/8\), \(|z|\le1/4\) imply
\[
\boxed{\quad
\|E_{xx}\|_{L^2(J)}
\le C_2\|G\|_{L^2(J)},\qquad
C_2:=1+\frac{67}{4\sqrt2}C_0<8 .
\quad}\tag{V8}
\]
Indeed, use (\|E_x\|_2\le\|E_x\|_\infty/\sqrt2\) and the same for E. In **original physical coordinates**,
\[
\begin{aligned}
\|G\|_{L^2(J)}
 &=L^{3/2}\|f\|_{L^2([L/2,L])},\\
\|e_{yy}\|_{L^2([L/2,L])}
 &=L^{-3/2}\|E_{xx}\|_{L^2(J)} .
\end{aligned}
\]
Consequently
\[
\boxed{\quad
\|e_{yy}\|_{L^2([L/2,L])}
\le C_2\|K_{a,Q}e\|_{L^2([L/2,L])},
\qquad C_2<8 .
\quad}\tag{V9}
\]
This is a *same-source radius-uniform curvature producer* on the actual backward overlap. The RHS is the **literal difference of the existing inner and original Kummer PDE equations**. Equation (V9) feeds the (E=\|u''-v''\|_2\) input in the verified paper calculation (S8)–(S11) of `HBL_213_SOURCE_FAITHFUL_FLAT_OVERLAP_20261110.md`. It has not yet bounded the complete nonlinear (K_{a,Q}e\) along a true Hartree orbit or produced any (s\)-positive order.

## 3. True two-field coefficient stability, with (L²\) rather than (L^\infty\) sources

For two original, normalized fields satisfying (V1)–(V3) let (D=E_1-E_2\), (H=G_1-G_2-ix(k_1-k_2)(E_2)_x/2-(z_1-z_2)E_2\). The difference is *exactly*
\[
 K_{k_1,z_1}D=H,\qquad D(1)=D_x(1)=0 .
\tag{V10}
\]
The fixed interval has measure (1/2\); therefore (V7) for (E_2\) gives
\[
\|H\|_2
\le \|G_1-G_2\|_2
+\frac{C_0}{\sqrt2}
\bigl(2|k_1-k_2|+|z_1-z_2|\bigr)\|G_2\|_2.
\tag{V11}
\]
Applying (V7) to D yields **genuine original-source**
\[
\boxed{\begin{aligned}
\|D\|_\infty&\le C_0 B_2,\\
\|D_x\|_\infty&\le4C_0 B_2,
\end{aligned}\quad
B_2:=\|G_1-G_2\|_2+
\frac{C_0}{\sqrt2}(2|\Delta k|+|\Delta z|)\|G_2\|_2 .
}\tag{V12}
\]
Again the source difference itself is **not** asserted to have a prescribed smallness or parameter order.

## 4. What the moving geometry actually preserves, and what it does not

For an actual (f\in H^1(I)\) on (I=[L_-/2,L_+]\) with (0<L_-\le L_+\), define (G_L(x)=L^2f(Lx)\) on (J\). The one-dimensional chain rule in the Bochner (L^2(J)\) topology gives
\[
\partial_LG_L=2Lf(Lx)+L^2xf_y(Lx),
\]
hence the exact geometric estimate
\[
\boxed{\quad
\|G_{L_1}-G_{L_2}\|_{L^2(J)}
\le |L_1-L_2|
\left(2\sqrt{L_+}\|f\|_{L^2(I)}
 +L_+^{3/2}\|f_y\|_{L^2(I)}\right).
\quad}\tag{V13}
\]
For two **different actual physical sources** (f_1,f_2\) the triangle inequality adds the explicit comparison term
\(L_2^{3/2}\|f_1-f_2\|_{L^2(I)}\), with no assumed source envelope.

By contrast, (H^1\) regularity alone does **not** yield a uniform Lipschitz bound of (G_L\) in (L^\infty(J)\). Indeed for fixed (L\) choose (x_0\in(1/2,1)\), (y_0=Lx_0\) and
\[
f(y)=\chi(y)|y-y_0|^\alpha,\qquad
\tfrac12<\alpha<1,quad\chi=1\text{ near }y_0.
\]
Then (f\in H^1\) but
\(
|G_{L+h}(x_0)-G_L(x_0)|\asymp|h|^\alpha
\), not (O(|h|)\). Smooth approximants give the same obstruction to any **uniform (H^1\)-controlled** (L^\infty\)-Lipschitz constant. Thus a proof strategy that requires moving-radius Lipschitz of **supremum source norms** from just the published weighted-H¹ Hartree source bounds cannot close. (V12)–(V13) recover the genuinely Lipschitz (C^1\) inverse in the appropriate (L^2\) source topology.

**Scope:** (V1)–(V13) are direct paper derivations under explicitly stated classical/Bochner regularity assumptions and a genuine source-defined (f\). The user-requested `--trust=0`, `warningAsError`, exact `#check` and three-axiom Lean audit have **not** yet been run for this new (L^2\) theorem. In particular, the **same physical** four-piece nonlocal Hartree PDE residual, its *actual* time-positive order, moving parameter source differences, projected Hamiltonian smoothing, a strong orbit and the dynamically selected Type-II rate are still OPEN. There is **no increase in original 13-environment acceptance: 11/13**.
