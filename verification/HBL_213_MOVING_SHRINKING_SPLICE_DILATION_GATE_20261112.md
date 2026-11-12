# HBL §2.13 — moving shrinking splice: exact dilation obstruction and energy concentration test

12 November 2026. **Paper-level analysis only; no Lean claim and no increment to the 11/13 original revised environments.** This note examines the most recent genuine inverse-square quartic Hartree *mixed cubic potential* splice and isolates the missing moving-time term. It is not a constructed four-region Hartree orbit.

## 1. Setup: one original nonlocal mixed source

Let \(K(x)=|x|^{-2}\) on \(\mathbb R^3\), let
\[
 {\cal C}(z)=K*\bigl(|x|^{-1}\operatorname{Re}z\,|z|^2\bigr),\quad
 {\mathscr H}=L^2((0,\infty),4\pi r^2\,dr;\mathbb C).
\]
For \(\theta,\mu\in\mathbb R\) with \(\mu>1/4\), put
\[
 \beta=\theta+i(1/4-\mu),\quad p=2i\beta,\quad
 \eta=\mu+1/2,\quad A=\tfrac i2 r\partial_r+\beta.
\]
For fixed nonzero radial real \(z\in C_c^\infty(\mathbb R^3)\), write
\(F={\cal C}(z)\), \(G=A^{-1}F\), with the unique full-radial-\(L^2\)
Mellin inverse described in the preceding notes. Thus
\[
 AG=F,\qquad rG'=pG-2iF,\qquad
 \|G\|_{\mathscr H}\le\eta^{-1}\|F\|_{\mathscr H}. \tag{DG1}
\]
Let \(0\le\chi\le1\) be smooth, zero on \([0,1]\), one on \([2,\infty)\).
For \(0<\gamma<1\), set \(\epsilon=\ell^\gamma\),
\(h_\ell(r)=\chi(r/\epsilon)G(r)\), and
\[
 (\mathsf U_\ell f)(r)=\ell^{3/2}f(\ell r),\qquad
 \Lambda_{L^2}=\tfrac32+r\partial_r.
\]
The preceding shrinking-shell note proves the *static* estimate
\[
 \|(A+\ell^2\Delta_{\rm rad})h_\ell-F\|_{\mathscr H}
 \le C_z(1+|\log\ell|)
       \bigl(\ell^{3\gamma/2}+\ell^{2-\gamma/2}\bigr). \tag{DG2}
\]
Its constant depends on higher regularity and spatial localization
of this **fixed** \(z\).

## 2. A quantitative no-go for promoting (DG2) on energy balls

Choose \(0\ne\psi\ge0\) smooth radial supported in \(2<|x|<3\),
and define
\[
 z_\epsilon(x)=\epsilon^{-1/2}\psi(x/\epsilon),\quad
 F_\epsilon={\cal C}(z_\epsilon),\quad
 G_\epsilon=A^{-1}F_\epsilon.
\]
Original critical scaling and the dilation commutation of \(A\) give
\[
 \|\nabla z_\epsilon\|_2=\|\nabla\psi\|_2,\quad
 F_\epsilon(x)=\epsilon^{-3/2}F_\psi(x/\epsilon),\quad
 G_\epsilon(x)=\epsilon^{-3/2}G_\psi(x/\epsilon). \tag{DG3}
\]
The inverse is unique because its Fourier multiplier has imaginary
part \(-\eta\), so the last equality follows rigorously from \(AG=F\).
For the original cut-off transport/Kummer residual
\[
 {\cal R}_{\ell,\epsilon}(z)
   =(A+\ell^2\Delta_{\rm rad})
       [\chi(\cdot/\epsilon)A^{-1}{\cal C}(z)]-{\cal C}(z),
\]
the correction is identically zero on \(0<r<\epsilon\); hence
\[
 \boxed{\ \|{\cal R}_{\ell,\ell^\gamma}(z_{\ell^\gamma})\|_{\mathscr H}
 \ge\|1_{(0,\epsilon)}F_\epsilon\|_{\mathscr H}
 =\|1_{(0,1)}F_\psi\|_{\mathscr H}=:\delta_\psi>0. \ } \tag{DG4}
\]
The last strict inequality holds because the positive Riesz kernel
convolved with \(\psi^3/|x|\) is positive on the unit ball.

Therefore (DG2) **cannot** hold with a uniform \(o(1)\) bound depending
only on a bounded \(\dot H^1\) norm of \(z\).
This is a counterexample to the *energy-only shrinking-splice estimate*,
not to the HBL theorem or to the special PDE-selected orbit. For the latter
one must derive actual quantitative nonconcentration or a compensating
inner Green solution from the PDE.

## 3. Exact time derivative of the moving source-dependent inverse

Now let \(z=z(t(s))\) be \(C^1\) into \(\dot H^1\) with \(t_s=\ell^2\),
and let \(\mu(s),\theta(s),\ell(s)\) be \(C^1\), with
\(\ell_s=-b\ell,\ \mu>1/4\), locally uniformly separated from the
spectral threshold. Set \(F(s)={\cal C}(z(t(s)))\),
\(G(s)=A_{\mu(s),\theta(s)}^{-1}F(s)\).
The real Fréchet derivative of the *original mixed source* is
\[
 D{\cal C}(z)[v]=K*\left[|x|^{-1}
  \bigl(\operatorname{Re}v\,|z|^2+
        2\operatorname{Re}z\,\operatorname{Re}(\bar z v)\bigr)\right].
 \tag{DG5}
\]
By differentiating \(A_{\mu,\theta}G=F\) in \(\mathscr H\),
\[
 G_s=A^{-1}\left[
   \ell^2D{\cal C}(z)[z_t]-(\theta_s-i\mu_s)G\right].
 \tag{DG6}
\]
Since \(\epsilon_s/\epsilon=-\gamma b\), the entire cutoff derivative is
\[
 \boxed{\quad
 \partial_s h_\ell
   =\chi_\epsilon A^{-1}
     \left[\ell^2D{\cal C}(z)[z_t]-(\theta_s-i\mu_s)G\right]
     +\gamma b(r/\epsilon)\chi'(r/\epsilon)G .
 \quad} \tag{DG7}
\]
Hardy–Sobolev–HLS and the full Mellin gap imply
\[
 \|\partial_s h_\ell\|_{\mathscr H}
 \le {C\ell^2\over\eta}\|\nabla z\|_2^2\|\nabla z_t\|_2
  +{|\theta_s|+|\mu_s|\over\eta^2}\|F\|_{\mathscr H}
  +C_\chi\gamma|b|\|1_{\epsilon<r<2\epsilon}G\|_{\mathscr H}.
 \tag{DG8}
\]
For uniformly smooth fixed-scale radiation,
\(\|1_{\epsilon<r<2\epsilon}G\|_{\mathscr H}
 \le C\epsilon^{3/2}(1+|\log\epsilon|)\).
Neither the selected speed derivatives nor uniform physical-time
regularity have been derived for the original HBL orbit.

The **original moving Kummer radius** also dilates. The exact unitary
chain rule, which is distinct from (DG7), is
\[
 \boxed{\quad
 \partial_s(\mathsf U_\ell h_\ell)
 =\mathsf U_\ell\left[\partial_s h_\ell
                        -b\Lambda_{L^2}h_\ell\right].
 \quad} \tag{DG9}
\]
By (DG1), both \(G\) and \(rG'\) are in \(\mathscr H\). For a *fixed*
smooth nonzero \(z,\mu,\theta\),
\[
 \|\Lambda_{L^2}h_\ell-\Lambda_{L^2}G\|_{\mathscr H}\to0,
 \qquad \|\Lambda_{L^2}G\|_{\mathscr H}>0. \tag{DG10}
\]
Indeed, dominated convergence treats the terms with \(\chi_\epsilon-1\),
and the shell derivative is
\(O(\epsilon^{3/2}(1+|\log\epsilon|))\).
If \(\Lambda_{L^2}G=0\), then \(G=cr^{-3/2}\), which belongs to
\(\mathscr H\) only when \(c=0\); but \(AG=F\ne0\).

Consequently, even when the static (DG2) tends to zero, the moving
field has the **potentially non-small** transport contribution
\(-b\mathsf U_\ell\Lambda_{L^2}G\). Shrinking the splice cannot
eliminate it. The *complete covariant renormalized Hartree PDE* might
cancel it against its own modulation transport; that cancellation
must be shown for the **same selected speed and corrected four-piece
field**, not suppressed by an estimate on the static Kummer defect.

## 4. Exact acceptance boundary

These are source-faithful paper identities and a rigorous energy-ball
counterexample for the far-principal cut-off method, **not** a proof of
the positive-time four-region residual. The required next original step
is a joint covariant identity involving (DG9), the actual selected
Cramer modulation, the moving Kummer basis/endpoints, and the
nonlinear seven-factor Hartree residual, followed by a genuine weighted
\(s^{-9/4}\) (or correctly closed alternative norm) estimate and
parameter Lipschitz bound. Then a real finite profile recursion and
PDE-derived blowup law are still required.

Previously successful strict sources remain CI
[43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518)
(full nonlinear *telescoping identity*) and
[43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481)
(frozen selected quadratic plus three \(C^1\) joins). Both original
job logs were re-read for exact \`--trust=0\`,
\`-DwarningAsError=true\`, exact \`#check\`, exact \`#print axioms\`
and precisely \`propext\`, \`Classical.choice\`, \`Quot.sound\`.
(DG1)–(DG10) **have no new Lean CI acceptance**.
Revised original environment count remains **11/13 (84.62%)**.
