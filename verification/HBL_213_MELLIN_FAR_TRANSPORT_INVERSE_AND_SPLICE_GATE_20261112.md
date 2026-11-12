# HBL §2.13 — exact Mellin inverse of the far Kummer transport and its genuine splice obstruction

12 November 2026 UTC. **New analytic reduction only, NOT a Lean theorem or an accepted original environment. Formal revised count: 11/13.** This note uses the literal coefficients in \`HBL/KummerFrozenAnnulus.lean\` and the *untruncated* cubic Hartree mixed potential from the preceding same-source analyses. It neither assumes nor asserts the missing time-positive residual.

## 1. The nonresonant full-line far transport operator has an explicit spectral gap

The original physical frozen radial Kummer operator is
\[
\mathcal L_{\mu,\theta}u
 =u_{rr}+\left(\frac2r+\frac{ir}{2}\right)u_r
  +\left(\theta+i\left(\frac14-\mu\right)\right)u.
\tag{MI1}
\]
Its far transport principal part, **not the entire operator**, is
\[
A_{\mu,\theta}:=\frac{i}{2}r\partial_r+\beta,\qquad
\beta=\theta+i\left(\frac14-\mu\right),\qquad
\eta=\mu+\frac12.
\tag{MI2}
\]
Let \(\mathscr H=L^2((0,\infty),4\pi r^2\,dr;\mathbb C)\), and define the unitary logarithmic radial transform
\[
(\mathsf M f)(x)=\sqrt{4\pi}\,e^{3x/2}f(e^x),
\qquad \mathsf M:\mathscr H\to L^2(\mathbb R,dx).
\]
On \(C_c^\infty(0,\infty)\),
\[
\mathsf M A_{\mu,\theta}\mathsf M^{-1}
 =\frac i2\partial_x+\theta-i\eta.
\]
Thus, with the Fourier convention \(\widehat h(\xi)=\int e^{-ix\xi}h(x)\,dx\),
\[
\widehat{\mathsf M A_{\mu,\theta} f}(\xi)
 =\left(\theta-\frac\xi2-i\eta\right)\widehat{\mathsf M f}(\xi).
\tag{MI3}
\]
For every **real** \(\theta\) and \(\mu>-1/2\), \(A_{\mu,\theta}:D(A)\subset\mathscr H\to\mathscr H\) is bijective and
\[
\boxed{\quad
\|A_{\mu,\theta}^{-1}F\|_{\mathscr H}
 \le \eta^{-1}\|F\|_{\mathscr H}.
\quad}\tag{MI4}
\]
Indeed the imaginary part of the exact Fourier multiplier is \(-\eta\). This is the source of the gap; **it is not** a Kummer Laplacian estimate or a global four-region inverse.

For \(\eta_j\ge\eta_*>0\), the resolvent identity gives the actual two-parameter estimate
\[
\boxed{\begin{aligned}
\|A_{\mu_1,\theta_1}^{-1}F_1-A_{\mu_2,\theta_2}^{-1}F_2\|_{\mathscr H}
&\le\eta_*^{-1}\|F_1-F_2\|_{\mathscr H}\\
&\quad+\eta_*^{-2}(|\mu_1-\mu_2|+|\theta_1-\theta_2|)
\|F_2\|_{\mathscr H}.
\end{aligned}}\tag{MI5}
\]
If the input and parameters are strongly \(C^1\) in \(s\), then
\[
\left\|\partial_s(A_{\mu,\theta}^{-1}F)\right\|_{\mathscr H}
\le\eta^{-1}\|F_s\|_{\mathscr H}
 +\eta^{-2}(|\mu_s|+|\theta_s|)\|F\|_{\mathscr H}.
\tag{MI6}
\]
None of \(\mu_s,\theta_s,F_s\) has been bounded from the selected physical HBL orbit here.

## 2. Actual original quartic mixed source, not two-mode projection

For the original inverse-square kernel \(K(x)=|x|^{-2}\), let
\[
\mathcal C(z)=K*\left(|x|^{-1}\operatorname{Re}z\,|z|^2\right),
\qquad z\in\dot H^1_{\mathrm{rad}}(\mathbb R^3;\mathbb C).
\]
The already proved Hardy--Sobolev--HLS estimate gives
\[
\|\mathcal C(z)\|_2
 \le2C_{\rm HLS}S_3^2\|\nabla z\|_2^3,\qquad
\|D\mathcal C(z)[h]\|_2
 \le6C_{\rm HLS}S_3^2\|\nabla z\|_2^2\|\nabla h\|_2.
\tag{MI7}
\]
Consequently
\[
G_{\mu,\theta,z}:=A_{\mu,\theta}^{-1}\mathcal C(z)
\]
is a genuine **infinite-dimensional source-dependent** far transport response, with
\[
\|G_{\mu,\theta,z}\|_{\mathscr H}
\le\frac{2C_{\rm HLS}S_3^2}{\mu+1/2}\|\nabla z\|_2^3.
\tag{MI8}
\]
This does not contradict the previously established rank-two Cramer no-go: the response is not confined to two modulation directions. A \(C^1_s\dot H^1\) *actual* trajectory would also feed (MI6) through the explicit derivative (MI7), but the necessary trajectory and its velocity bounds remain unconstructed.

## 3. Exact singular-core obstruction to naively using this as a *global* Kummer corrector

For a real-valued, smooth, rapidly decaying radial physical radiation snapshot \(z\) with
\(
a:=\operatorname{Re}z(0)|z(0)|^2\ne0,
\)
its **actual** mixed density is \(a/r+O(r)\) as \(r\downarrow0\). Angular integration of the exact inverse-square kernel (or splitting \(2r<|y|<1\)) gives
\[
\boxed{\quad
\mathcal C(z)(r)=4\pi a\log(1/r)+O(1),\quad r\downarrow0.
\quad}\tag{MI9}
\]
For \(\mu>1/4\), put \(p=2i\beta=2(\mu-1/4)+2i\theta\), so \(\operatorname{Re}p>0\).
The unique \(\mathscr H\)-inverse above has the explicit Volterra representation
\[
G(r)=2i\int_r^\infty (r/\rho)^p\mathcal C(z)(\rho)\,\frac{d\rho}{\rho}.
\tag{MI10}
\]
Differentiating (MI10) gives \(A_{\mu,\theta}G=\mathcal C(z)\), and the Mellin spectral bound selects this solution uniquely. Inserting (MI9) gives, because \(p\ne0\),
\[
\boxed{\quad
G(r)=\frac{4\pi a}{\beta}\log(1/r)+O(1),\quad r\downarrow0.
\quad}\tag{MI11}
\]
In particular \(G\) is unbounded near \(0\) and cannot belong to \(H^2(B_1)\), by the three-dimensional \(H^2\hookrightarrow C^{0,1/2}\) embedding. Thus even for **smooth** nonzero-core radiation the transport inverse cannot simply be used as a globally regular \(L^2\)-Laplacian Kummer profile. This does *not* invalidate the far-zone inverse or an actual matched inner Green correction.

## 4. Exact cutoff commutator — why a shell splice does not automatically gain a power

Let \(\mathsf U_\ell f(r)=\ell^{3/2}f(\ell r)\), unitary on \(\mathscr H\), and \(y=\ell r\). Then
\[
\mathcal L_{\mu,\theta}\mathsf U_\ell g
 =\mathsf U_\ell\bigl(A_{\mu,\theta}g+\ell^2\Delta_{\rm rad}g\bigr),
\qquad \Delta_{\rm rad}g=g''+2y^{-1}g'.
\tag{MI12}
\]
For a smooth radial cutoff \(\chi(y)\), with \(\chi'=0\) off a fixed shell \(a<y<2a\), the **exact** commutator is
\[
\boxed{\begin{aligned}
[\ A_{\mu,\theta}+\ell^2\Delta_{\rm rad},\chi\ ]g
&=\frac{iy}{2}\chi'(y)g(y)\\
&\quad+\ell^2\left(2\chi'(y)g'(y)
 +\left[\chi''(y)+\frac{2\chi'(y)}y\right]g(y)\right).
\end{aligned}}\tag{MI13}
\]
For a chosen \(g=G_{\mu,\theta,z}\) and \(\chi\), its leading term is **independent of \(\ell\)**. In particular, for a nonnegative nonzero smooth \(z\), \(\mathcal C(z)>0\) at positive radii, and wherever \(\chi'\ne0\) on an open interval \(G\) cannot vanish identically (otherwise \(A G=\mathcal C(z)>0\)). Hence this shell term is genuinely nonzero. A generic localization of the far resolvent therefore **does not** convert an \(O(b)\) mixed forcing into \(o(b)\); the missing cancellation must come from the *actual* matched Cramer/Fredholm/Green/Kummer interface, not from critical scaling alone.

This is a precise no-shortcut obstruction, **not** a counterexample to a specially selected full HBL orbit.

## 5. Main-chain decision and audit boundary

The potentially useful nonresonant part is the explicit transport spectral gap (MI4)--(MI8): an actual source-dependent infinite-dimensional correction is available in the *far principal model*. The two missing physical producers are now unambiguous: (a) a source-faithful inner/outer gluing that cancels the order-\(b\) transport commutator (MI13) while retaining all three actual \(C^1\) traces and the full Hartree convolution; (b) regularity/weighted estimates of the physical response and its moving time derivative adequate to control \(\ell^2\Delta G\), the actual nonlinear remainder, and the full time-positive projected residual. The real positive \(\mu\) bootstrap must also be derived from the PDE, not supplied as a rate hypothesis.

Original historical CI [42530158681](https://github.com/penghongzhong/HBL/actions/runs/42530158681) failed on upstream types; corrected strict [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518) (job 130872307063) **Success**, exact finite four-piece nonlinear PDE *identity*. Strict [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481) (job 130908225390) **Success** for selected frozen spectral quadratic and three C1 interfaces. Re-read original logs this run: Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, \`--trust=0\`, \`-DwarningAsError=true\`; the four telescope checks and two selected spectral checks use only \`propext\`, \`Classical.choice\`, \`Quot.sound\`. **(MI1)--(MI13) are paper-only; no new Lean #check, axiom audit or strict CI.**

**Retained revised original environments: 11/13**. §2.13 remains open; its source-derived full four-region positive-time gain, parameter Lipschitz and actual finite recursion have not been constructed. Original dynamically selected Type-II blowup theorem remains open.