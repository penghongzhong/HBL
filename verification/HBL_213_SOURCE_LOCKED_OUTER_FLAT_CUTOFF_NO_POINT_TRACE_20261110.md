# HBL §2.13 — source-faithful *flat outer Kummer cutoff* that bypasses the unbounded Cramer curvature point trace

**10 November 2026.** This is a **new alternative paper construction** for the original spectral Kummer region, not a modification of the accepted \`ActualHartreeSpectralSourceOuterSecondJet.lean\` declarations. No new Lean CI or original numbered environment is claimed. **11/13** remains the strict acceptance.

## 1. Why the previously accepted affine/quadratic outer repair is not the shortest source-norm route

The existing original \(C^2\) repair has its quadratic coefficient
\(j=w''(B)\), correctly determined by the actual original
source \(F(B)-\delta u_0(B)\). Under only weighted \(L^2\)
source control that point trace is unbounded (the explicit
Green-inverted spike counterexample is in
\`HBL_213_SOURCE_LOCKED_OUTER_C2_DERIVATIVE_BUDGET_20261110.md\`).
No amount of further \(C^2\) endpoint algebra supplies its
missing quantitative PDE-gradient estimate.

One can instead **keep the true same-source spectral Green
solution itself throughout the outer overlap**, multiply
it by the existing physical smooth cutoff, and stop
before the Kummer domain endpoint. The third jet is
then inherited by multiplication, not extracted as an
unbounded trace at \(B\).

## 2. Actual flat cutoff entirely INSIDE the original Kummer existence interval

Fix \(0<r_0<B<\mathrm{scale}\). Let
\[
 h=(B-r_0)/4,\qquad r_*=r_0+h,\qquad
 \chi(r)=1-\operatorname{cutoff}\!\left(\frac{r-r_*}{h}\right),
\]
where \(\operatorname{cutoff}\in C^\infty\) is **the
same actual cutoff used in the existing HBL Lean
physical repair and its strict C³ certification**:
\(\operatorname{cutoff}=0\) on \((-\infty,1]\)
and \(=1\) on \([2,\infty)\). Thus
\[
 \chi(r)=1\quad(r\le r_0+2h),\qquad
 \chi(r)=0\quad(r\ge r_0+3h).
\]
The entire derivative support lies in
\[
 J=[r_0+2h,\,r_0+3h]\Subset(r_0,B),
\]
and leaves the margin \(B-(r_0+3h)=h\).
For the genuine spectrally corrected same-source
solution \(w(r)=u_0(r)-u_1(r)\) on
\((0,\mathrm{scale})\), set the **physical**
outer field
\[
 U_{\rm flat}(y)=\chi(y/a)\,w(y/a),\qquad a>0.
\tag{O1}
\]
At the left physical location \(y=a(r_0+2h)\),
\(U_{\rm flat}=w(y/a)\) on an actual neighbourhood
on the Kummer side; at
\(y=a(r_0+3h)\), the function is zero on an actual
neighbourhood on the outer side. Since \(\chi\) is
smooth and \(w\) is \(C^2\) on the **open** domain
containing \(J\), the resulting physical field and
its first two derivatives match automatically.
There is **no \(F(B)\) point evaluation or independent
curvature parameter**. If stronger source regularity
makes \(w\) \(C^k\), the flat cutoff preserves that
regularity through the outer interface.

The earlier selected real two-channel Cramer boundary
data remain valid; this changes only the *auxiliary*
outer repair geometry. Whether the revised original
\(\S2.13\) permits this replacement without altering
the final stated construction must be checked at
the complete PDE and parameter-recursion level.

## 3. Exact ORIGINAL Kummer commutator and its spatial derivative

In the normalized radial variable, the unshifted
operator is
\[
 \mathcal K w=w''+A(r)w'+Qw,\quad
 A(r)=\frac2r+\frac{ir}2,\qquad
 \mathcal K w=f,\quad f=F-\delta u_0.
\]
For the **actual** source-selected \(w\) and the
same cutoff \(\chi\),
\[
 \boxed{\quad
 \mathcal K(\chi w)-\chi\mathcal Kw
 =2\chi'w'+(\chi''+A\chi')w=:\mathcal C.
 \quad}\tag{O2}
\]
Differentiating on \(J\), then substituting the
TRUE inhomogeneous Kummer equation for \(w''\)
produces the exact **no-source-point-trace** identity
\[
 \boxed{\begin{aligned}
 \mathcal C'={}&2\chi'f
 +(3\chi''-A\chi')w'\\
 &+(\chi'''+A\chi''+A'\chi'-2Q\chi')w,
 \qquad A'=-2/r^2+i/2 .
 \end{aligned}}\tag{O3}
\]
This uses the original *unshifted* source
\(f=F-\delta u_0\), not the shifted quadratic
\(\delta^2u_1\) and not a local NLS approximation.
It requires only \(f\in L^2(J;dr)\) and the actual
\(w,w'\in L^2(J;dr)\), plus the fixed \(C^3\)
cutoff derivatives; **no derivative of \(F\) or
point trace \(F(B)\) is introduced by this commutator**.

Let \(C_k=\sup_{\mathbb R}|
\operatorname{cutoff}^{(k)}|\) for \(k=1,2,3\),
which exist by compact support of derivatives.
Set
\[
 r_{\min}=r_0+2h,\quad
 A_{\max}=2/r_{\min}+B/2,\quad
 A'_{\max}=2/r_{\min}^2+1/2 .
\]
Since \(\|\chi^{(k)}\|_\infty\le C_k h^{-k}\),
the genuine weighted derivative estimate is
\[
 \boxed{\begin{aligned}
 \|(1+r^2)\mathcal C'\|_{L^2(J)}
 \le(1+B^2)\bigg\{&
 \frac{2C_1}{h}\|f\|_{L^2(J)}\\
 &+\left(\frac{3C_2}{h^2}
  +\frac{A_{\max}C_1}{h}\right)\|w'\|_{L^2(J)}\\
 &+\left(\frac{C_3}{h^3}
  +\frac{A_{\max}C_2}{h^2}
  +\frac{A'_{\max}C_1}{h}
  +\frac{2|Q|C_1}{h}\right)\|w\|_{L^2(J)}
 \bigg\}.
 \end{aligned}}\tag{O4}
\]
Everything on the right is an **original physical
source/Green field norm**, not a free envelope.
The only explicit geometric cost is \(h^{-1}\)
(and \(h^{-2},h^{-3}\)); the left radius enters
through the true \(r_{\min}\), not a hidden
\(r_0^{-1}\) in a fabricated constant.
If the original geometry yields \(B\ge2r_0\),
then \(h\ge B/8\) and \(r_{\min}\ge B/2\),
so (O4) contains **no \(r_0^{-1}\) loss**.

Under the physical pullback \(y=ar\),
the second-order Kummer commutator is
\(a^{-2}\mathcal C(y/a)\); its derivative has
the **exact** \(a^{-3}\mathcal C'(y/a)\)
factor. Consequently
\[
 \|(1+y^2)\partial_y[a^{-2}\mathcal C(y/a)]\|_{L^2(aJ)}
 =a^{-5/2}
 \|(1+a^2r^2)\mathcal C'(r)\|_{L^2(J)}
 \le a^{-1/2}\|(1+r^2)\mathcal C'\|_2
\]
for \(a\ge1\), just as in the already checked
physical scale norm computation.

## 4. Exact limits

This route **genuinely removes the source curvature
point-trace obstruction in the *outer cutoff
commutator***; it does not give a full \(Y\)-norm
of the four-region Hartree PDE residual for free.
In particular, the term
\(\chi\mathcal Kw=\chi f\) still has the
derivative \(\chi'f+\chi f'\). Its \(f'\) part must
cancel against the true physical nonlinear source
or be estimated from original PDE derivative
regularity. The entire nonlocal cross interaction
is controlled only **conditionally** by the true
profile-\(X\) estimate in
\`HBL_213_FINITE_NONLOCAL_HARTREE_MIXED_TERMS_SHORT_CHAIN_20261110.md\`;
physical \(X\)-size and time decay are not yet proved.
The selected \(db,dw\), all moving endpoints,
outer profile time derivatives and finite Hartree
PDE orbit remain genuine obligations.

**Next most direct Lean producer:** first formalize
(O2)–(O3) for
\`actualOriginMatchedKummerValue\` and
\`actualHartreeMatchedSpectralCorrectedValue\`
using their already verified original-source equation
and existing strict \(C^3\) physical cutoff; then
prove the literal flat-interface \(C^2\) gluing in
the public code before replacing the old repair
in any original theorem. This is a proof-route
revision **not a current replacement of accepted
statements**. Do not mark \(\S2.13\) closed.

**Original revised theorem acceptance: 11/13.**
