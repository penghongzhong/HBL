# HBL §2.13 — a source-faithful interface obstruction and a C² replacement

**Date:** 10 November 2026. **Status:** Paper analysis and exact construction only. No Lean acceptance, no assertion that the original Hartree orbit exists, and no change to the strict revised-original **11/13** count.

## 1. Source of the obstruction in the *actual* code

The public, strict-successful
\`HBL/TypeIIDynamicSelection/ActualHartreeSpectralCorrectedFourPieceThreeC1.lean\`
uses
\`actualHartreeInnerKummerSpectralFourPiece\` and
\`actualKummerPhysicalInterfaceRepair\`.
The latter is literally
\[
  \mathrm{Rep}_{a,B,p,q}(y)=\chi_B(y/a)
         [p+(y/a-B)q],\qquad
  \chi_B(r)=1-\mathrm{cutoff}((r-B)/(B/3)).
\]
The existing cutoff is exactly **one on a neighbourhood of \(B\)**
and exactly **zero on a neighbourhood of \(2B\)**. In particular,
\[
 \mathrm{Rep}(aB)=p,\quad
 \partial_y\mathrm{Rep}(aB)=a^{-1}q,\quad
 \partial_y^2\mathrm{Rep}(aB+)=0.
\]
For the truly corrected source-dependent Kummer solution
\(w(r)=\mathrm{actualHartreeMatchedSpectralCorrectedValue}(r)\),
its physical continuation \(v(y)=w(y/a)\) satisfies
\[
 v(aB)=p:=w(B),\quad
 v_y(aB)=a^{-1}q,\ q:=w'(B),\quad
 v_{yy}(aB-)=a^{-2}j,\ j:=w''(B),
\]
assuming the claimed classical derivatives exist. Hence the *literal*
C¹ splice of the verified module has the **explicit one-sided second-jet jump**
\[
\boxed{
 [U_{yy}]_{aB}
 :=U_{yy}(aB+)-U_{yy}(aB-)
 =-a^{-2}w''(B).
}
\tag{G1}
\]
The three verified \(C^1\) joins impose no condition \(w''(B)=0\).
At the farther join \(y=2aB\), the repair is identically zero nearby,
so this particular second-jet obstruction is absent there. At the inner
join \(y=L\), a **separate** second-jet mismatch may occur: the current
weighted \(L^2\) Fredholm source hypotheses only certify \(C^1\), not
\(u_{\rm inner}''(L)=v_{\rm Kummer}''(L)\).

Suppose the physical modulation paths are sufficiently regular and the
true nonlocal Hartree convolution is continuous through the join. A
\(C^1\)-matched moving interface has matching **one-sided partial time
derivatives** as well: differentiate the equality of the two values along
the moving interface and cancel the equal slopes. All terms of the
renormalized Hartree residual other than its radial second derivative
therefore match. With the original convention containing \(+\Delta\),
its one-sided residual jump is
\[
 [F_{\rm full}]_{aB}=-a^{-2}w''(B)
 \quad\text{(up to any other separately constructed corrections
  touching the same join).}
\tag{G2}
\]
This is an *interface computation*, not an assertion that a particular
yet-to-be-constructed physical orbit has a nonzero jump.

## 2. A genuine jump cannot obey the proposed Morawetz-energy dual bound

Let \(R>0\), let \(F\) be piecewise \(C^1\) near \(R\), and suppose
\[
 J:=F(R+)-F(R-)\ne0.
\]
With the three-dimensional radial measure, for smooth compactly
supported test \(g\) one has the **exact integration-by-parts formula**
\[
\frac{\langle-\Delta g,F\rangle_{\mathbb R^3}}{4\pi}
=R^2 g'(R)J
 +\int_0^\infty r^2 g'(r)F'_{\rm pw}(r)\,dr .
\tag{G3}
\]
The formula is stated for real components; for a complex jump, choose
a real or imaginary component whose jump is nonzero. Choose a smooth
compactly supported \(\phi\) with \(\phi'(0)\ne0\), and set
\[
 g_\epsilon(r)=\epsilon^{1/2}\phi((r-R)/\epsilon).
\]
On a fixed annulus around \(R\), Kim's radial Morawetz norm and
the \(\mathrm{Mor},0\) norm used in the HBL paper satisfy
\[
 \sup_{0<\epsilon<\epsilon_0}\|g_\epsilon\|_{\mathrm{Mor},0}<\infty,
 \qquad
 g'_\epsilon(R)=\epsilon^{-1/2}\phi'(0).
\]
The second term in (G3) is \(O(\epsilon^{1/2})\) if \(F'_{\rm pw}\)
is locally bounded. Meanwhile its first term grows as
\(R^2 J\phi'(0)\epsilon^{-1/2}\). The short-range multiplication
terms in \(L_\pm\) are lower order for these tests. The extra
nonlocal Hartree real-Hessian term is also lower order by local
Hilbert–Schmidt boundedness (or by symmetry and smoothness of the
original fixed bubble-weighted kernel). Thus a **nonzero residual jump**
does **not** satisfy a Morawetz-dual estimate
\[
 |\langle L_\pm g,F\rangle|
 \le C\|g\|_{\mathrm{Mor},0}
 \quad\text{for every }g\in C_c^\infty
\tag{G4}
\]
with finite \(C\).

Equivalently, \(F'_{\rm distribution}\) contains \(J\delta_R\)
and is not an ordinary weighted \(L^2(dr)\) derivative. This is
**stronger and more structural** than the preceding oscillatory
counterexample: the current verified \(C^1\) matching theorem cannot
by itself put the *physical residual* into the proposed Kato energy
dual space. Projecting away a finite-dimensional smooth threshold
sector does not automatically eliminate a delta-prime singularity
produced by a jump. A genuine projection-specific cancellation
would require its own proof.

## 3. Exact source-faithful local C² repair — still needs a physical norm estimate

There is a straightforward **candidate** with no prescribed blowup
parameter, no external source or free matching curvature.
The same corrected Kummer field provides the third value
\[
  j:=w''(B)
\]
by its original source-dependent differential equation. Replace the
existing affine repair by
\[
 \boxed{
 \mathrm{Rep}^{(2)}_{a,B}(y)
  =\chi_B(y/a)\left[
     p+(y/a-B)q+\frac12(y/a-B)^2j
  \right].
 }
\tag{G5}
\]
Since the **same existing cutoff** is exactly \(1\) near \(B\) and
\(0\) near \(2B\), its endpoint jets satisfy, by direct
differentiation,
\[
\begin{array}{c|ccc}
y & \mathrm{Rep}^{(2)} & \partial_y\mathrm{Rep}^{(2)}
 &\partial_y^2\mathrm{Rep}^{(2)}\\ \hline
aB & w(B)&a^{-1}w'(B)&a^{-2}w''(B)\\
2aB&0&0&0.
\end{array}
\tag{G6}
\]
Therefore the **outer** two joins can be made \(C^2\), provided
\(w\) is \(C^2\) and the source data actually produce those
derivatives. This does **not** automatically give a positive
time-order residual. The extra correction costs a physical curvature
budget of size \(\|j\|\) (with spatial factors depending on \(B,a\)),
whose size and parameter Lipschitz bound must be derived from the
same physical original Hartree source.

The **inner join** \(y=L\) must be handled separately. If both inner
and Kummer profiles admit second derivatives, let
\(\Delta_2=u_{\rm inner}''(L)-v_{\rm Kummer}''(L)\).
A smooth one-sided correction on the Kummer side,
\[
 \mathrm{Patch}_L(y)=\frac{\Delta_2}{2}(y-L)^2
   \chi_{\rm in}((y-L)/h),\qquad y\ge L,
\tag{G7}
\]
with \(\chi_{\rm in}\equiv1\) near \(0\) and supported in a short
positive overlap interval that ends before \(aB\), matches the second
jet without altering the existing value and slope. The actual
Fredholm \(C^2\) regularity, the size of \(\Delta_2\), moving
derivatives of the cutoff, nonlocal mixed interactions and their
weighted derivative bounds all remain genuine open PDE obligations.

**Alternative:** prove an entirely different projected smoothing
bound whose source dual space permits these interfaces; do **not**
pretend (G1)–(G4) vanish merely because the pointwise PDE telescope
is a Lean identity.

## 4. Updated shortest physical closure gate

\[
\text{original physical two-channel source}
\to \text{true }w,\ w',w''\text{ and actual Fredholm C²}
\to \text{C² four-region matching}
\to
\begin{matrix}
\text{whole-nonlinear PDE residual}\\
\text{weighted derivative and parameter Lipschitz}
\end{matrix}
\to \text{Hartree projected adjoint smoothing/inversion}
\to \text{true orbit and dynamic Type-II rate}.
\]
The old exact three-\(C^1\) CI remain **valid** as stated, but
do not imply \(C^2\) or any \(O(s^{-15/8})\) or \(O(s^{-9/4})\)
dual source estimate. Any exact PDE telescope remains an identity
even if classical second derivatives do not exist at a join.

**Official revised original count: 11/13.**


## 5. Exact derivative-budget scaling of an actual \(a^{-2}\) physical pullback

This calculation supplies a **concrete possible gain**, without postulating
that the whole four-region residual has the required form.
Let \(a\ge1\) and \(G\) be an absolutely continuous radial function
with \(G\in L^2(0,\infty;dr)\) and
\((1+r^2)G'(r)\in L^2(0,\infty;dr)\). Put
\[
 E_a(y)=a^{-2}G(y/a).
\]
The exact physical derivative and change of variables are
\[
 \partial_yE_a(y)=a^{-3}G'(y/a),\qquad
 \|E_a\|_{L^2(dy)}=a^{-3/2}\|G\|_{L^2(dr)},
\]
\[
 \begin{aligned}
 \|(1+y^2)\partial_yE_a\|_{L^2(dy)}
 &=a^{-5/2}\!
   \left(\int_0^\infty
           (1+a^2r^2)^2|G'(r)|^2\,dr\right)^{1/2}\\
 &\le a^{-1/2}
       \|(1+r^2)G'\|_{L^2(dr)},
       \qquad a\ge1.
 \end{aligned}
 \tag{G8}
\]
The last inequality is simply
\(1+a^2r^2\le a^2(1+r^2)\).

Combining this **exact scale calculation** with the previously
derived true Hartree Hessian sufficient source norms yields
\[
 \begin{aligned}
 \mathcal D_-(E_a)
 &\le2a^{-1/2}\|(1+r^2)G'\|_2
     +\tfrac32a^{-3/2}\|G\|_2,\\
 \mathcal D_+(E_a)
 &\le2a^{-1/2}\|(1+r^2)G'\|_2
     +\tfrac{33}2a^{-3/2}\|G\|_2 .
 \end{aligned}
 \tag{G9}
\]
The factors \(a^{-1/2}\), \(a^{-3/2}\) are **not assumed**:
they come from \(dy=a\,dr\), the exact physical \(a^{-2}\)
Kummer residual factor, and the Morawetz weight.
The existing Lean producer
\`actual_Kummer_physical_interface_repair_scaled_residual_exact\`
already proves the \(a^{-2}\) pullback identity for the
**original affine physical Kummer repair**. The corresponding
full source derivative, curvature-modified repair, and
four-region nonlinear Hartree source remain open.

If an actual physical forcing admits
\[
 F_{\rm full}(s,y)=a(s)^{-2}G_s(y/a(s))
\]
*in exactly the norm consumed by the intended linear inverse*,
the genuine same-source bound
\(\|(1+r^2)G_s'\|_2+\|G_s\|_2\lesssim s^{-15/8}\)
and a PDE-derived scale \(a(s)\gtrsim s^\rho\)
would yield a spatial source factor \(s^{-\rho/2}\).
In an **absolute** time-integral norm, if its propagator
is actually bounded on that *same* source/energy space,
one needs \(\rho>1/2\) to overcome the original quarter-power
deficit: \(\int_s^\infty u^{-15/8-\rho/2}\,du
=O(s^{-7/8-\rho/2})=o(s^{-9/8})\).
**This is a conditional exponent comparison, not a Hartree inversion**.
The source norm \(\mathcal D_\pm\) does **not** automatically give
bounded absolute Duhamel evolution into energy, so (G9) alone
cannot replace the required spectral/dual-Kato estimate.
Moving-modulation, inner region, nonlocal cross terms,
the unknown physical derivative of \(G_s\), and the actual
growth rate of \(a(s)\) must be derived, not imposed.

**Remaining acceptance: 11/13. No new strict Lean CI claimed.**


## 6. No C² curvature budget follows from the existing weighted-L² source hypotheses

The obstacle is not solely a missing Lean differentiability lemma:
the **pointwise source trace \(F(B)\)** appearing in the C² curvature
budget is not controlled by the previously accepted
\(L^2_{7/4}\) (or any local bounded-weight \(L^2\)) assumption.

Fix \(0<B<\mathrm{scale}\) away from the zero-radius singularity,
and choose a smooth nonzero real bump
\(\phi\in C_c^\infty(-1,1)\) with \(\phi(0)=1\).
For \(0<\varepsilon\ll B\), set
\[
 F_\varepsilon(r)=\varepsilon^{-1/2}
                     \phi((r-B)/\varepsilon).
\]
Because the HBL radial weights are uniformly equivalent to constants
on any fixed annulus around \(B\),
\[
 \|F_\varepsilon\|_{L^2_{7/4}}
   \le C_B \|\phi\|_{L^2(\mathbb R)},\qquad
 |F_\varepsilon(B)|=\varepsilon^{-1/2}\to\infty,
\tag{G10}
\]
and all \(F_\varepsilon\) are continuous and smooth. In the
*already-proved true Kummer spectral-corrected differential equation*,
\[
 w''(B)
 =F(B)-d\,w_1(B)-c_1(B)w'(B)
       -(c_0+d)w(B),
\quad c_1(B)=\mathrm{frozenFirstCoeff}(B),\
c_0=\mathrm{frozenZeroCoeff}(\mu,\theta),
\tag{G11}
\]
where \(w_1\) is the same genuine first spectral correction, and
\(w,w_1\) are the actual Cramer/Green fields, not free coefficients.
Thus any claimed bound for the quadratic repair
\(\chi_B(y/a)\frac12(y/a-B)^2w''(B)\)
**based solely** on \(\|F\|_{L^2_{7/4}}\) would require either
a new pointwise source trace theorem or a demonstrable cancellation
of the peak \(F(B)\) by the other source-dependent Cramer values.
Neither is furnished by the old \(C^1\) or Volterra weighted
value/derivative estimates.

This does **not** assert \(w_\varepsilon''(B)\to\infty\) for
every \(\varepsilon\)-dependent selected spectral parameter:
proving that requires a uniform bound for all the other terms
on the right-hand side of (G11) and the correct same-source selection.
The rigorous obstruction already established by (G10) is that
the required trace is **not** a consequence of the advertised
current source regularity. The shortest legitimate fix is to
extract a stronger \(W^{1,2}\) / physical PDE source-derivative
estimate (which also supplies a trace locally), or to prove a
special physical cancellation at the genuinely selected interface.
Do not insert \(\|F(B)\|\lesssim\|F\|_{L^2_{7/4}}\) as an axiom
or mistake a formal endpoint C² jet identity for a budget.

**Source theorem:** \`actual_Hartree_matched_spectral_corrected_left_C1_and_exact_equation\`
in \`ActualHartreeMatchedSpectralLeftC1Exact.lean\` supplies (G11);
its strict historical successes remain auxiliary. No claim that
the original four-region strong PDE residual is now in \(H^1\).
The revised original count remains **11/13**.


## 7. A *derived*, radius-explicit source-trace bound when the genuine H¹ producer is available

The spike obstruction in §6 does not mean the source curvature
can never be estimated. It identifies exactly how the missing
**physical derivative bound** must enter. Under the original
strict Kummer geometry \(0<r_0<B<\mathrm{scale}\), put
\[
 \ell=\tfrac12\min\{B-r_0,\mathrm{scale}-B\}>0,
 \qquad I_B=[B-\ell,B+\ell]\subset(r_0,\mathrm{scale}).
\]
For any actual absolutely continuous complex radial forcing
\(F\in H^1(I_B)\), the one-dimensional fundamental theorem of
calculus and averaging yield the **fully explicit**
\[
 \boxed{
 |F(B)|\le(2\ell)^{-1/2}\|F\|_{L^2(I_B)}
             +\sqrt{2\ell}\,\|F'\|_{L^2(I_B)}.
 }\tag{G12}
\]
Indeed, average \(F(t)\) over \(t\in I_B\), write
\(F(B)-F(t)=\int_t^B F'(\tau)d\tau\) and apply
Cauchy--Schwarz; the \(L^2\) average contributes the
first term. This is a *paper proof*, not a Lean-compiled theorem.

Insert (G12) into the genuine corrected spectral Kummer equation
\[
 \begin{aligned}
 |w''(B)| \le {}&
 (2\ell)^{-1/2}\|F\|_{L^2(I_B)}
  +\sqrt{2\ell}\,\|F'\|_{L^2(I_B)}
  +|d|\,|w_1(B)|\\
 &+|c_1(B)|\,|w'(B)|
  +\bigl(|c_0|+|d|\bigr)|w(B)|.
 \end{aligned}\tag{G13}
\]
Thus the source-trace/curvature budget is *not* a separate
fundamental analytic gate **if and only if** one first derives
the missing \(H^1\) physical source estimate and controls
the **explicit margin cost** \(\ell^{-1/2}\) on the moving
selected scales. In contrast, no version of (G13) with a
constant independent of \(\ell\) follows from the old source
\(L^2\) estimate. The same actual Kummer/Volterra Cramer
value-slope budgets may bound \(w(B),w'(B),w_1(B)\) when
their true hypotheses and parameters match, but that
has not yet been composed into (G13) in Lean.

**Practical branch choice:** if the physical residual already
supplies \(H^1\) source regularity with a sufficiently wide
Kummer margin, use the explicit C² repair and (G13);
otherwise the flat interior-overlap scheme in
\`HBL_213_SOURCE_FAITHFUL_FLAT_OVERLAP_20261110.md\`
avoids sampling \(F(B)\), at the cost of explicit
\((aB-L)^{-j}\) cutoff commutators. Both routes still
require the full actual Hartree projected inverse,
nonlocal interactions, and modulation/parameter bounds.
This does not prove revised §2.13, and the
**original acceptance remains 11/13**.


## 6. A deeper independent obstruction: C² matching alone does not produce \(H^1\) forcing

The **actual code contract**, not an abstract Taylor model, is
\`actual_Hartree_matched_spectral_original_unshifted_source\`
in \`ActualHartreeMatchedSpectralOriginalPDEMismatch.lean\`.
For the same real source \(F\), original selected Cramer field \(u_0\),
and spectral-corrected field \(w\), it proves on \(0<r<\mathrm{scale}\)
\[
 w''(r)+p(r)w'(r)+q\,w(r)=F(r)-\delta\,u_0(r),\quad
 p(r)=\mathrm{frozenFirstCoeff}(r),\quad
 q=\mathrm{frozenZeroCoeff}(\mu,\theta).
\tag{R1}
\]
The **original unshifted** right hand side is
\(F-\delta u_0\), *not* merely the shifted quadratic
\(-\delta u_1\). The current Lean source hypotheses demand
\(F\in C^0_{\mathrm{loc}}((0,\mathrm{scale}))\);
they do not demand \(F\in H^1_{\mathrm{loc}}\).

On an open interval \(J\Subset(0,\mathrm{scale})\) where the
source-selected flat-overlap construction equals the genuine
spectral Kummer continuation, \(v(y)=w(y/a)\), the *actual
scaled Kummer operator* has the identity
\[
 \mathcal K_a v(y)
   =a^{-2}(F(y/a)-\delta u_0(y/a)).
\tag{R2}
\]
This identity is already a Lean theorem,
\`actual_Hartree_matched_spectral_original_physical_source\`.
**Conditional on** \(F\in H^1(J)\) and the true \(u_0\in H^1(J)\),
the weak derivative is exactly
\[
 \partial_y(\mathcal K_a v)(y)
  =a^{-3}(F'-\delta u_0')(y/a)
\]
and the exact change-of-variables formula is
\[
 \boxed{
 \|(1+y^2)\partial_y(\mathcal K_a v)\|_{L^2(aJ)}
 =a^{-5/2}
 \|(1+a^2r^2)(F'-\delta u_0')\|_{L^2(J)}.
 }
\tag{R3}
\]
For \(a\ge1\) this gives the radius-free sufficient upper bound
\[
 \|(1+y^2)\partial_y(\mathcal K_a v)\|_{L^2(aJ)}
 \le a^{-1/2}\|(1+r^2)(F'-\delta u_0')\|_{L^2(J)}.
\tag{R4}
\]
These are **paper calculus identities**; only (R1)–(R2)
have the cited prior Lean proofs. They do *not* imply
the physical right-hand norm is bounded at any time rate.

**Explicit insufficiency of the current source regularity:**
fix \(r_*\in J\), take
\(F(r)=\psi(r)|r-r_*|^{1/4}\) for a smooth
\(\psi\in C_c^\infty(J)\) with \(\psi(r_*)\ne0\).
Then \(F\in C^0(J)\cap L^2(J)\) but
\[
 F'(r)\sim\frac14\psi(r_*)
  \operatorname{sgn}(r-r_*)|r-r_*|^{-3/4},
 \qquad F'\notin L^2(J).
\]
The matched Green \(u_0\) and the corrected \(w\)
are \(C^2\) from the genuine continuous forcing,
so \(u_0'\in L^2(J)\). Consequently
\((F-\delta u_0)'\notin L^2(J)\) and (R2) shows that
**even on a perfectly smooth flat plateau, with no
gluing interfaces at all**, the scaled Kummer source
need not lie in the required weighted \(H^1\)
spatial source class. Thus neither adding the source-locked
outer \(C^2\) curvature nor proving a globally \(C^2\) splice
can establish the Morawetz-dual forcing estimate under
the current \(C^0\)/weighted-\(L^2\) producer hypotheses.

The inner Fredholm forcing is currently only in
\`InWeightedL2 (7/4)\`, so the analogous stronger
derivative producer is also genuinely missing there.

**Smallest noncircular repair**: derive \(F'\) and the
inner Fredholm source derivatives with quantitatively
correct *weighted* norms from the SAME original moving
quartic Hartree source and the unique physical two-real
channel selection; or replace the Kato-dual space with
a separately proved projected Hartree smoothing estimate
that permits these lower regularity sources. A bare
assumption \(F\in H^1\), an independently inserted time
power, or the phrase "smooth PDE source" would not
close original §2.13. The source-locked outer endpoint
curvature is separately being Lean-tested, but cannot
by itself eliminate (R1)–(R4)'s quantitative gap.

**Formal original acceptance remains 11/13, no new
Hartree nonlinear time-order or Type-II orbit.**


## 7. Exact moving-physical-repair transport identity; no independent speed envelope

The source-locked \(C^2\) repair has a particularly useful
time-transport cancellation. Keep the Kummer outer radius \(B\)
**fixed**, as it is in the actual four-piece Lean packet; let
\(a(s)>0\) and let
\[
 P_0(s)=w(s,B),\quad P_1(s)=\partial_r w(s,B),\quad
 J(s)=\partial_r^2w(s,B).
\]
Write
\[
 G(s,z)=\chi_B(z)
     \bigl[P_0(s)+(z-B)P_1(s)+\tfrac12(z-B)^2J(s)\bigr],
 \quad R(s,y)=G(s,y/a(s)),\quad z=y/a(s).
\]
For differentiable physical parameters, **no separate upper-jet
velocity parameter** is introduced. The exact partial derivative
at fixed physical \(y\) is
\[
 \partial_sR(s,y)
 =\chi_B(z)
   [P_0'(s)+(z-B)P_1'(s)+\tfrac12(z-B)^2J'(s)]
  -\frac{a_s}{a}z\,\partial_zG(s,z).
\tag{M1}
\]
Since \(yR_y=zG_z\), the actual radial dilation
material derivative obeys the **exact cancellation**
\[
 \boxed{
 (\partial_s+b(s)y\partial_y)R(s,y)
  =\chi_B(z)
   [P_0'+(z-B)P_1'+\tfrac12(z-B)^2J']
   +\left(b-\frac{a_s}{a}\right)zG_z.
 }
\tag{M2}
\]
Thus the moving-cutoff transport is not an independent source:
it is precisely a mismatch between the **true physical**
dilation velocity \(b\) and the derivative of the **actual**
physical scale \(a\). Whether this mismatch is small is a
separate original Hartree modulation-PDE statement, not a
definition or free assumption.

The exact unshifted Kummer identity (R1) determines \(J\)
from the same physical source. At fixed \(B\), differentiating
it in the parameter/time variable gives, **provided the actual
derivatives are produced by the PDE**,
\[
 \begin{aligned}
 J'(s)={}&\partial_s F(s,B)
 -\delta_s(s)u_0(s,B)-\delta(s)\partial_su_0(s,B)\\
 &-p(B)\partial_s P_1(s)
 -q_s(s)P_0(s)-q(s)\partial_sP_0(s).
 \end{aligned}
\tag{M3}
\]
Here \(p(r)=\mathrm{frozenFirstCoeff}(r)\) is fixed and
\(q(s)=\mathrm{frozenZeroCoeff}(\mu(s),\theta(s))\).
This formula identifies exactly where the moving
Kummer basis and selected source time derivatives enter,
rather than hiding them in a presumed bound for \(J_s\).

**Analytic consequence:** proving the *material*
source estimate for (M2) may be shorter than estimating
separately \(\partial_sR\) and \(byR_y\). The real remaining
inputs are \(b-a_s/a\), \(P_0',P_1',\partial_sF\),
\(\delta_s\), the original Hartree nonlocal source gradients
and the current physical \(L^2\)/Lipschitz budgets.

(M1)–(M3) are **paper calculus identities**. They are
not a Lean CI acceptance or a time-positive PDE residual
bound; they prescribe no physical scale or Type-II rate.
Original theorem acceptance remains **11/13**.
