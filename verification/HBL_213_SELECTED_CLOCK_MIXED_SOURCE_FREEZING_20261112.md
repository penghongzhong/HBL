# HBL §2.13: selected-clock freezing of the actual mixed Hartree channel

12 November 2026. **Conditional paper derivation only. Original revised Lean acceptance remains 11/13. No new Lean audit.**

## 1. Rate-free physical clock

Assume that one genuinely constructed radial Hartree solution admits absolutely continuous selected modulation variables satisfying, for s >= s0,

\[
q_s=4\mu,\qquad 0<m\le\mu(s)\le M,\qquad
b(s)=\frac{1+4\mu(s)}{2q(s)},\qquad
\ell_s=-b\ell,\qquad t_s=\ell^2,
\]
with q(s0)=q0>0 and ell(s0)=ell0>0. These are NOT supplied by the existing fixed-time Cramer theorem: the actual PDE-selected orbit and the uniform modulation trap remain to be proved.

Put h=s-s0, qminus=q0+4mh, H=1+4Mh/q0, alpha=1/(4M), tau0=q0*ell0^2. Direct differentiation, not an assumed rate, yields

\[
q_0+4mh\le q(s)\le q_0+4Mh,\qquad
(q\ell^2)_s=-\ell^2.
\]
Consequently

\[
T:=t(s_0)+q_0\ell_0^2,\qquad
T-t(s)=q(s)\ell(s)^2
=\tau_0\exp\left(-\int_{s_0}^s\frac{du}{q(u)}\right),
\]
\[
0<T-t(s)\le\tau_0H^{-\alpha},\qquad
0<\ell(s)^2\le\frac{\tau_0H^{-\alpha}}{qminus},
\qquad
0<b(s)\le\frac{1+4M}{2qminus}. \tag{1}
\]

Indeed, q(u) <= q0+4M(u-s0) implies the integral is at least alpha log H. In particular T and the coarse power of ell are **dynamically deduced under the modulation trap**, not stipulated as a Type-II rate.

## 2. Genuine inverse-square Hartree mixed channel

For K(x)=|x|^{-2} on R^3, let

\[
\mathcal C(z)=K*\left(|x|^{-1}\operatorname{Re}z\,|z|^2\right). \tag{2}
\]

The real trilinear Hardy--Sobolev--HLS estimate already proved on paper in HBL_213_MIXED_ENERGY_LIPSCHITZ_AND_CRITICAL_NONUNIFORMITY_20261112.md is

\[
\|\mathcal C(z)-\mathcal C(w)\|_2
\le A_H\left(\|\nabla z\|_2^2+
\|\nabla z\|_2\|\nabla w\|_2+\|\nabla w\|_2^2\right)
\|\nabla(z-w)\|_2. \tag{3}
\]

Suppose in addition the SAME physical regular radiation z(t) extends through the derived time T as a path in W^{1,infinity}([t(s0),T]; dot H^1), with uniform bounds E on \|\nabla z(t)\|_2 and V on \|\nabla z_t(t)\|_2. This regularity is an **explicit unproved physical-orbit producer**, not implied by the fixed-time spatial C1 interfaces.

Writing z_s=z(t(s)) and z_*=z(T), the Banach-space fundamental theorem of calculus and (1) give
\[
\|\nabla(z_s-z_*)\|_2
\le V(T-t(s))\le V\tau_0H^{-\alpha}.
\]
Thus the **exact nonlocal physical mixed source**, not a synthetic error envelope, satisfies
\[
\boxed{\;
\|\mathcal C(z_s)-\mathcal C(z_*)\|_2
\le3A_HE^2V\tau_0H^{-\alpha};
\quad
\|2b(s)(\mathcal C(z_s)-\mathcal C(z_*))\|_2
\le\frac{3A_H(1+4M)E^2V\tau_0H^{-\alpha}}{qminus}.
\;} \tag{4}
\]
The latter is O(s^{-1-1/(4M)}). This is a genuine positive time order for the **difference from the nonzero terminal mixed channel**, conditional on the actual PDE-derived trap and strong terminal radiation. The frozen infinite-dimensional term 2b(s)*C(z_*) generally stays O(s^{-1}); the proof DOES NOT eliminate it or build a full four-region PDE residual.

If z is only continuous into dot H^1 up to T, a modulus omega_z gives the weaker estimate 3 A_H E^2 omega_z(tau0 H^{-alpha}), without an unjustified power.

## 3. Covariant scale collision and actual unmatched source

Keep the genuine original potential
\[
Q=K*(|W+\sqrt{\ell}\,z(t,\ell\cdot)|^4-W^4),\quad
W(x)=(1+|x|^2)^{-1/2},
\quad
(T_\ell f)(x)=\ell^{3/2}f(\ell x).
\]
Previous exact covariance yields
\[
T_\ell^{-1}D_bQ+2b\mathcal C(z_s)
=-b\mathcal E_\ell(z_s)
+\ell^{3/2}K*\partial_t\rho_{\ell,z_s},\qquad
\rho_{\ell,z}=|z+g_\ell|^4-g_\ell^4,
\quad g_\ell(x)=\frac{\sqrt\ell}{\sqrt{\ell^2+|x|^2}}. \tag{5}
\]
The exact error \mathcal E_\ell is defined in (EL6) of the preceding energy note. Its proved-on-paper local energy Lipschitz estimate is uniform over 0<ell<=1. Therefore
\[
\|\mathcal E_{\ell(s)}(z_s)\|_2
\le\|\mathcal E_{\ell(s)}(z_*)\|_2+
C_E V\tau_0H^{-\alpha}. \tag{6}
\]
For each fixed z_* in dot H^1 the first term tends to zero, even though the same assertion is FALSE uniformly over all bounded energy balls, as the earlier explicit critical concentration example shows.

If the terminal z_* additionally is Schwartz, the explicit original kernel/HLS calculation yields
\[
\|\mathcal E_{\ell(s)}(z_s)\|_2
\le C_*\sqrt{\ell(s)}+C_EV\tau_0H^{-\alpha},
\]
and, without any independently assumed decay exponent,
\[
\|b(s)\mathcal E_{\ell(s)}(z_s)\|_2
\le\frac{1+4M}{2qminus}
\left[
C_*\left(\frac{\tau_0H^{-\alpha}}{qminus}\right)^{1/4}
+C_EV\tau_0H^{-\alpha}\right]. \tag{7}
\]
Combining (4)--(7) proves the exact **conditional remainder** identity
\[
\begin{split}
&T_\ell^{-1}D_bQ+2b\mathcal C(z_*)
-\ell^{3/2}K*\partial_t\rho_{\ell,z_s}\\
&\qquad=-b\mathcal E_\ell(z_s)
 +2b\bigl(\mathcal C(z_*)-\mathcal C(z_s)\bigr),
\end{split}
\]
whose L2 norm is O(s^{-1-delta}) with
\[
\delta=\min\{1/(4M),1/4+1/(16M)\}>0. \tag{8}
\]

The **source terms subtracted in (8) are not small by this proof**. The nonzero frozen potential channel, the actual physical-time Hartree density derivative, moving Kummer basis/endpoints/spectral variation, time derivative of the actual Cramer selector, original outer-interface commutators, nonlocal seven-factor residual and finite profile recursion remain. In particular ell^{3/2} is at best bounded from (1) by O(s^{-3/4-3/(16M)}), which is not necessarily O(s^{-1-delta}). It is mathematically invalid to promote (8) to an O(s^{-9/4}) estimate for the full Hartree PDE.

## 4. Exact verification boundary

Existing successfully audited fixed-time selected spectral quadratic + three C1 joins: https://github.com/penghongzhong/HBL/actions/runs/43135036481 (job 130908225390). Existing audited four-piece nonlinear PDE **telescoping identity**, not positive remainder gain: https://github.com/penghongzhong/HBL/actions/runs/43124289518 (job 130872307063). Their original job logs establish pinned Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5, trust=0, warningAsError, exact target type checks and only propext, Classical.choice, Quot.sound.

The new estimates (1)--(8) are PAPER ONLY; no Lean code or CI presently validates them. The open genuine-original steps are the PDE construction/trap for the very same orbit, its sufficient terminal regularity, infinite-dimensional frozen-channel Kummer cancellation, ALL four regional residual bounds and parameter Lipschitz, real finite-layer iteration, and dynamically derived Type-II asymptotic. **Strict original revised acceptance stays 11/13, not 12/13.**
