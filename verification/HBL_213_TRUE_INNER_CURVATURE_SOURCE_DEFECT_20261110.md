# HBL §2.13: the true Fredholm/spectral inner C² jump and the non-free patch cost (10 November 2026)

**Original revised theorem count stays 11/13.** The two original-source curvature-jump algebra declarations have now passed a strict pinned Lean job [42851609990](https://github.com/penghongzhong/HBL/actions/runs/42851609990), raw job 129953504774; the concrete two-profile Fredholm-to-spectral instantiation is subject to a separate later strict audit. Neither is an acceptance of §2.13 or the final theorem.

## 1. Source-exact curvature defect at the genuine left interface

Let `u` be the original physical two-channel Fredholm inner response, `J` its canonical physical value/slope, `u_0` the same-source Cramer–Green continuation, and `v(y)=w_\delta(y/a)` the zero-left-jet *spectrally corrected* continuation with original spectral source `F`. The original normalized equation is

\[
w_\delta''+p w_\delta'+Qw_\delta
=F-\delta u_0,
\quad
K_{a,Q}v(y)=a^{-2}\{F(y/a)-\delta u_0(y/a)\}.
\]

The already verified same-source C¹ endpoint matching gives `u(L)=v(L)`, `u'(L)=v'(L)`. The **literal** original physical Kummer operator, with no auxiliary source norm or independent curvature input, therefore satisfies

\[
\boxed{
\Delta_2:=u''(L)-v''(L)
= K_{a,Q}u(L)-a^{-2}F(L/a)+a^{-2}\delta u_0(L/a).
}
\tag{CJ}
\]

The first term `K_{a,Q}u(L)-a^{-2}F(L/a)` is **not known to vanish** merely because `u` solves the original Hartree Hessian Fredholm equations: those equations and the frozen Kummer operator are different operators. In particular, the spectral shift produces a **first-order** term `a^{-2}delta*u_0`, not solely the `delta²` shifted-operator defect.

The Lean target `actual_Hartree_true_inner_spectral_C1_curvature_jump` is intended to instantiate (CJ) with the actual `actualHartreeTwoChannelInner`, `actualMomentLockedCanonicalInnerJet`, `actualOriginMatchedKummerValue` and `actualHartreeMatchedSpectralPhysicalValue`. The concrete profile instantiation is **not independently accepted until its later four-target CI succeeds**. The two algebraic bridge theorems have passed exact `#check` / `#print axioms` under Lean 4.35.0-rc3, pinned Mathlib, `--trust=0` and `warningAsError`, using only `propext`, `Classical.choice`, `Quot.sound` (including the previously accepted first target).

## 2. A C² correction is possible, but making its support arbitrarily thin worsens the derivative source

Choose a fixed smooth `chi∈C_c^∞([0,1))` equal to one near zero, `phi(t)=t²chi(t)/2`. On `L≤y≤L+h`, let the right-hand correction be

\[
P_{L,h}(y)=\Delta_2 h^2\phi((y-L)/h),\qquad 0<h<L.
\]

The exact left jets are `P(L)=P'(L)=0`, `P''(L)=Delta_2`; the patch and all its derivatives vanish at the other end, so the actual field is C² at the inner join and unchanged beyond `L+h`. Changing variables gives for `m=0,1,2,3`

\[
\boxed{
\|\partial_y^mP_{L,h}\|_{L^2([L,L+h])}
=|\Delta_2|\,h^{5/2-m}\|\phi^{(m)}\|_{L^2([0,1])}.
}
\tag{PC}
\]

In particular, `∥P''∥₂ ∼ |Delta_2|√h` but `∥P'''∥₂ ∼ |Delta_2|/√h`. Thus (unlike a C¹ splice) a C² splice eliminates the artificial distributional delta produced by a jump of curvature, but the *classical derivative* of the full Kummer source contains a real cost `|Delta_2|/sqrt(h)`. Simply shrinking the patch width does not produce positive time order in a weighted source norm requiring one spatial derivative. For a generic nonconstant plateau cutoff, `∥phi'''∥₂>0`.

To close the original physical PDE norm, one must prove (CJ)'s same-source `Delta_2(s)` bound, choose the actual moving `h(s)`, differentiate `L(s)` and `h(s)` in the patch, include the Hartree cross interactions from this patch, and close the entire weighted derivative and parameter-Lipschitz budget. These remain **unproved**.

## 3. What counts

Existing three C¹ joins, exact nonlinear PDE telescoping and source-locked outer C² jets are useful prerequisites but **not** proof of actual inner C² matching or a positive-order four-region residual. The retained manuscript numerator remains **11/13**, with §2.13 and the final PDE-generated Type-II theorem open. The original nonlocal Hartree PDE trajectory, projected inverse, finite recurrence and rate are still absent.


## 4. Exact material-time source cost (paper identity)

With \(L=L(s)\), \(h=h(s)>0\) and \(\Delta_2=\Delta_2(s)\), work **inside** the actual moving open patch \(L(s)<y<L(s)+h(s)\). Set
\[
\xi(s,y)=\frac{y-L(s)}{h(s)},\qquad
\partial_s\xi=-\frac{L_s+\xi h_s}{h}.
\]
Since \(P_{yy}=\Delta_2\phi''(\xi)\), differentiating **at fixed physical \(y\)** gives exactly
\[
\boxed{\partial_s P_{yy}
=(\Delta_2)_s\phi''(\xi)
-\frac{\Delta_2}{h}(L_s+\xi h_s)\phi'''(\xi).}
\tag{MT}
\]
Thus the physical moving-patch contribution to the \(L^2_y\) time derivative of its curvature satisfies
\[
\boxed{
\|\partial_s P_{yy}\|_{L^2([L,L+h])}
\le |\Delta_{2,s}|\sqrt h\|\phi''\|_2
+|\Delta_2|h^{-1/2}
\bigl(|L_s|\|\phi'''\|_2+|h_s|\|\xi\phi'''\|_2\bigr).
}
\tag{MC}
\]
The \(h^{-1/2}|L_s|\) term is the true physical interface-transport cost. It is not a Kummer-basis artifact and cannot be omitted by invoking source C¹ matching or the finite nonlinear PDE telescope. Formula (MT) is an interior classical identity; distributional differentiation across the moving join must be performed for the **full C² glued field**, where matching conditions can cancel interface measures. No claimed positive time exponent or Lipschitz control follows from (MC) alone.


## 5. A quantitative, two-sided *local-operator* obstruction to thin C² patching

The cost \(\|P'''\|_2=|\Delta_2|h^{-1/2}\|\phi'''\|_2\) is not just a formal term. For the **original physical local Kummer part**
\[
K_{a,Q}P=P''+A(y)P'+BP,\qquad
A(y)=\frac2y+\frac{iy}{2a^2},\quad B=\frac{Q}{a^2},
\]
its derivative on \(I=[L,L+h]\), \(0<h<L\), is *exactly*
\[
(K_{a,Q}P)'=P'''+A P''+(A'+B)P',
\quad A'=-\frac2{y^2}+\frac{i}{2a^2}.
\]
Let \(c_j=\|\phi^{(j)}\|_{L^2([0,1])}\), \(j=1,2,3\), and define
\[
A_*=\frac2L+\frac{L+h}{2a^2},\qquad
B_*=\frac2{L^2}+\frac{1/2+|Q|}{a^2}.
\]
The reverse triangle inequality gives a **genuine lower bound**
\[
\boxed{
\|(1+y^2)(K_{a,Q}P)'\|_{L^2(I)}
\ge(1+L^2)|\Delta_2|h^{-1/2}
\bigl(c_3-A_*c_2h-B_*c_1h^2\bigr)_+ .
}\tag{LB}
\]
Because \(\phi\) is not quadratic on all of \([0,1]\) (it must be compactly cut off), \(c_3>0\). Therefore in any regime where
\(A_*c_2h+B_*c_1h^2\le c_3/2\),
\[
\|(1+y^2)(K_{a,Q}P)'\|_2
\ge \tfrac12(1+L^2)c_3|\Delta_2|h^{-1/2}.
\tag{LB'}
\]
This rules out the *specific* strategy of making the **local original-source derivative** arbitrarily small merely by taking a thin curvature-matching patch with fixed nonzero \(\Delta_2\). It does **not** prove a lower bound for the entire Hartree nonlinear residual: the nonlocal and moving pieces would have to be shown unable to cancel the local term. Conversely, a genuine cancellation must be established in that full residual rather than assumed. The missing producer is a sufficiently small same-source \(\Delta_2\) and a compatible thickness \(h\), plus the exact nonlocal and time-dependent terms.


## 6. Shorter chain: reuse the *already proved* inner Kummer defect bound

The exact source curvature mismatch (CJ) can be **bounded by a previously verified native theorem**, without deriving a new independent \(C^2\) Fredholm envelope. Define the *actual physical two-channel source*
\[
S(y)=\operatorname{actualHartreeTwoChannelPhysicalSource}(F_+,F_-)(y).
\]
The existing Lean declaration
\(\texttt{actual_Hartree_two_channel_inner_Kummer_defect_bound}\)
establishes, when \(F_\pm\) are continuous and in the actual weighted inverse domain, \(2<R\le L\),
\[
\|K_{a,Q}u(L)+S(L)\|
\le \mathcal B_{\rm inner}
:=\left(\frac{C_{\rm inner}}{R^4}
 +\frac{C_{\rm Kummer}(\mu,\theta)}{a^2}\right)
 \bigl(\|F_+\|_{7/4}+\|F_-\|_{7/4}\bigr).
\tag{IB}
\]
For the **same real selected-speed physical channels** in the existing
\(\texttt{actual_Hartree_moment_locked_plateau_scaled_source}\),
the original Hartree source identity on \(0<L\) is
\[
a^{-2}F(L/a)+S(L)=0.\tag{SC}
\]
Thus (CJ) yields the completely source-faithful bound
\[
\boxed{\quad
|\Delta_2|\le \mathcal B_{\rm inner}
+a^{-2}|\delta|\,|u_0(L/a)|.
\quad}\tag{CB}
\]
The right side is not an independently postulated curvature envelope: both \(\mathcal B_{\rm inner}\) and the source equality are present as proven **producers** in the repository. To instantiate them together one must identify \(F_\pm\) exactly with the *same* physical transmission and real speed channels and confirm their continuity and weighted membership for the actual selected PDE orbit. The size of their actual weighted norms and the spectral factor \(a^{-2}\delta u_0(L/a)\) along that orbit remains unproved. The condition \(R>2\), \(R\le L\) is necessary for directly invoking the existing shell estimate; do not quietly use it for \(L\le 2\).

Inserting (CB) into (LB) quantifies the precise source-size and patch-width budget. Note that (LB) is a **lower** bound on the actual local Kummer patch derivative, while (CB) is an **upper** bound on \(|\Delta_2|\): one cannot combine the two to infer decay of the entire nonlinear residual without an upper bound on the total patch source and its nonlocal interactions.
