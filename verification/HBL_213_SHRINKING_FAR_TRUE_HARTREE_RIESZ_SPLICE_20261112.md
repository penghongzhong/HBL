# HBL §2.13 — a shrinking far-zone splice for the genuine cubic mixed Riesz channel

12 November 2026. **New paper-level constructive reduction, not a Lean theorem or a proved §2.13 environment. Strict original count: 11/13.** This corrects the tempting but overly broad extrapolation from the previous fixed-rescaled-annulus cutoff obstruction: the commutator has no small *pointwise* coefficient, but its **radial three-dimensional L² mass can have a positive spatial scale gain if its support shrinks to the singular origin in the far rescaled coordinate**. The construction is valid for an explicit smooth class of the actual, nontruncated inverse-square Hartree mixed source. It is not yet an admissible matched whole-PDE correction.

## 1. Literal nonlocal source and its core/far regularity

Fix a radial complex-valued z in C_c^\infty(R³) and put

\[
 f_z(x)=|x|^{-1}\operatorname{Re}z(x)|z(x)|^2,\quad
 F_z=|x|^{-2}*f_z,\quad
 \alpha=4\pi\operatorname{Re}z(0)|z(0)|^2 .
 \tag{SF1}
\]

This is the genuine mixed cubic term from the **original quartic Hartree density**, not an NLS-local replacement or an independently hypothesized forcing envelope. Its exact radial convolution is

\[
 F_z(r)=\frac{2\pi}{r}\int_0^\infty
 \rho f_z(\rho)\log\frac{r+\rho}{|r-\rho|}\,d\rho.
 \tag{SF2}
\]

Smooth radiality gives \(f_z(\rho)=\alpha/(4\pi\rho)+O(\rho)\) near 0. Splitting the integral into this explicit singular density and a regular remainder yields, for 0<r<1/2,

\[
 F_z(r)=\alpha\log(1/r)+O_z(1),\qquad
 |rF_z'(r)|\le C_z.
 \tag{SF3}
\]

For clarity, the local model \(f(\rho)=c\,\mathbf1_{(0,1)}(\rho)/\rho\) has the **exact** convolution

\[
 F_{\mathrm{model}}(r)=\frac{2\pi c}{r}
 \big[(1+r)\log(1+r)-(1-r)\log(1-r)-2r\log r\big],
 \quad 0<r<1,
 \tag{SF4}
\]
so \(F_{\mathrm{model}}=4\pi c(1-\log r)+O(r^2)\) and
\(rF_{\mathrm{model}}'=-4\pi c+O(r^2)\).
The smooth radial remainder in (SF1), together with the source supported away from zero, obeys the bounded-error assertions in (SF3); the far multipole expansion yields
\[
 |F_z(r)|+|rF_z'(r)|\le C_zr^{-2},\qquad r\ge R_z.
 \tag{SF5}
\]
Consequently \(F_z\in\mathscr H=L^2((0,\infty),4\pi r^2dr)\).

## 2. Exact transport inverse: remove a second-derivative hypothesis

For real \(\theta\), \(\mu>1/4\), let
\[
 \beta=\theta+i(1/4-\mu),\quad
 p=2i\beta=2(\mu-1/4)+2i\theta,\quad
 A_{\mu,\theta}=\tfrac i2r\partial_r+\beta .
\]
Then \(\operatorname{Re}p>0\). For the **same F_z** set
\[
 G(r)=2i\int_r^\infty (r/\rho)^pF_z(\rho)\,\frac{d\rho}{\rho}.
 \tag{SF6}
\]
The preceding Mellin inverse gives \(AG=F_z\) and
\(\|G\|_{\mathscr H}\le(\mu+1/2)^{-1}\|F_z\|_{\mathscr H}\).
The actual first and second radial derivatives satisfy the **exact** identities
\[
 rG'=pG-2iF_z,\qquad
 \boxed{r^2\Delta_{\mathrm{rad}}G
 =(p+1)(pG-2iF_z)-2irF_z'},\quad
 \Delta_{\mathrm{rad}}=\partial_r^2+2r^{-1}\partial_r .
 \tag{SF7}
\]
Thus the unscaled Kummer Laplacian of the far inverse can be controlled using **only the original source and its first radial derivative**, not an independent bound on \(G''\).

The near-origin expansion follows directly from (SF6):
\[
 G(r)=(\alpha/\beta)\log(1/r)+O_{z,\mu,\theta}(1),\quad
 |rG'(r)|+|r^2\Delta_{\mathrm{rad}}G(r)|\le C_{z,\mu,\theta}
 \quad(0<r<1/2).
 \tag{SF8}
\]
In the exterior \(r\ge R_z\),
\[
 |G(r)|+|rG'(r)|+|r^2\Delta_{\mathrm{rad}}G(r)|
 \le C_{z,\mu,\theta}r^{-2}.
 \tag{SF9}
\]
The local singularity remains logarithmic; this does **not** assert that the uncut inverse is in \(H^2(\mathbb R^3)\).

## 3. Main new estimate: shrink the splice shell in the far variable

Let \(\chi\in C^\infty([0,\infty))\), \(\chi=0\) on [0,1], \(\chi=1\) on [2,\infty), and \(\chi_\epsilon(r)=\chi(r/\epsilon)\). For \(0<\epsilon<1/4\) define \(G_\epsilon=\chi_\epsilon G\). It vanishes near the singular origin, is smooth across **both** shell endpoints, and lies in radial \(H^2(\mathbb R^3)\) for each fixed \(\epsilon>0\).

The exact operator error is
\[
 \begin{aligned}
 (A_{\mu,\theta}+\ell^2\Delta_{\mathrm{rad}})G_\epsilon-F_z
  ={}&-(1-\chi_\epsilon)F_z
     +\tfrac{ir}{2}\chi_\epsilon'G\\
    &+\ell^2\chi_\epsilon\Delta_{\mathrm{rad}}G
     +\ell^2\big(2\chi_\epsilon'G'
        +(\chi_\epsilon''+2r^{-1}\chi_\epsilon')G\big).
 \end{aligned}
 \tag{SF10}
\]
In particular, no nonlocal term has been set to zero, and this is not a linear-superposition claim for the full Hartree PDE.

From (SF3), (SF8), (SF9), the radial volume measure \(4\pi r^2dr\), and the support \(\epsilon\le r\le2\epsilon\) of \(\chi_\epsilon'\), one obtains
\[
 \begin{split}
 \|(1-\chi_\epsilon)F_z\|_{\mathscr H}
 +\|\tfrac{ir}{2}\chi_\epsilon'G\|_{\mathscr H}
 &\le C\epsilon^{3/2}(1+|\log\epsilon|),\\
 \|\chi_\epsilon\Delta_{\mathrm{rad}}G\|_{\mathscr H}
 +\|[\Delta_{\mathrm{rad}},\chi_\epsilon]G\|_{\mathscr H}
 &\le C\epsilon^{-1/2}(1+|\log\epsilon|).
 \end{split}
 \tag{SF11}
\]
For the second line, use the *derived* (SF7), not an assumed \(H^2\) bound. Therefore
\[
 \boxed{
 \|(A_{\mu,\theta}+\ell^2\Delta_{\mathrm{rad}})G_\epsilon-F_z\|_{\mathscr H}
 \le C(1+|\log\epsilon|)
        (\epsilon^{3/2}+\ell^2\epsilon^{-1/2}).
 }
 \tag{SF12}
\]

Take any \(0<\gamma<1\), \(\epsilon=\ell^\gamma\). For \(0<\ell<\ell_0\),
\[
 \boxed{
 \|(A_{\mu,\theta}+\ell^2\Delta_{\mathrm{rad}})
       G_{\ell^\gamma}-F_z\|_{\mathscr H}
 \le C_\gamma(1+|\log\ell|)
  (\ell^{3\gamma/2}+\ell^{2-\gamma/2}).
 }
 \tag{SF13}
\]
For example \(\gamma=2/3\) gives \(O(\ell(1+|\log\ell|))\) with a matching radius \(r=\epsilon/\ell=\ell^{-1/3}\to\infty\) in the **original Kummer radius**. Thus the transition sits genuinely in the far principal region; the fixed-annulus \(O(1)\) commutator objection alone is insufficient to rule out an \(L^2\) spatial gain.

By the **exact original Kummer scaling**
\[
 \mathsf U_\ell h(r)=\ell^{3/2}h(\ell r),\qquad
 \mathcal L_{\mu,\theta}\mathsf U_\ell h
 =\mathsf U_\ell(A_{\mu,\theta}+\ell^2\Delta_{\mathrm{rad}})h,
 \tag{SF14}
\]
the same estimate is valid in the original physical radial norm for
\(\mathcal L_{\mu,\theta}\mathsf U_\ell G_{\ell^\gamma}
-\mathsf U_\ell F_z\). There is no hidden loss from the origin because the two radial norms are related unitarily.

## 4. Why this is a constructive candidate, NOT §2.13 closure

This shows a **true, source-generated positive spatial \(\ell\)-power** for one infinite-dimensional mixed Riesz channel of the far principal Kummer model, even though its uncut inverse is logarithmically singular. It repairs one specific logical shortcut in the preceding fixed-shell discussion: moving the shell changes the radial L² mass. It does not contradict that discussion, which concerned a shell fixed in the rescaled variable.

The profile above is **not** the original four-piece selected Fredholm/Cramer/Kummer field. The far matching radius moves to \(r=\ell^{\gamma-1}\), and a genuine selected inner/outer solution with the *same* physical two-speed Cramer source must be built and joined there. In addition, the actual Hartree radiation is not known to remain in a uniform high-regularity compact class along the desired PDE orbit; bounds (SF3)--(SF9) have not been made uniform in its time/parameters. The entire nonlinear seven-factor Hartree source, the moving basis/endpoint/time derivatives, the three original physical interfaces, the real parameter Lipschitz estimate, and the finite physical PDE recursion remain load-bearing. A positive power of \(\ell\) is **not** a positive power of physical time without a PDE-derived modulation law.

**Formal audit:** This is mathematics on paper only; no new Lean declaration, no new CI and no original-environment promotion. Exact original job evidence rechecked on 12 November: [43124289518](https://github.com/penghongzhong/HBL/actions/runs/43124289518), job 130872307063, strictly verifies the *identity* of the corrected full nonlinear four-piece telescope; [43135036481](https://github.com/penghongzhong/HBL/actions/runs/43135036481), job 130908225390, strictly verifies the static selected quadratic/three-C¹ chain. Their target source blobs match current HEAD, both use Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, trust=0, warningAsError and precisely the permitted propext/Classical.choice/Quot.sound audit. No claim that these runs prove (SF1)--(SF14).

**Original revised acceptance: 11/13 (84.62%). §2.13 and the final PDE-derived Type-II theorem are OPEN.**
