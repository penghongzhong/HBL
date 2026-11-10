# HBL §2.13 — exact SAME-source outer C² repair derivative and the point-trace gate

**10 November 2026.** Analysis of the original inverse-square quartic Hartree source and genuinely source-selected spectral Kummer correction. This is a **paper proof only** of a **local outer repair** bound; not a new Lean theorem, full Hartree residual time gain, original §2.13 acceptance, or Type-II orbit. Strict original count **11/13**.

## 1. Verified actual inputs, not new curvature assumptions

The exact original nonlocal Hartree source enters
\`ActualHartreeSpectralSourceOuterSecondJet.lean\`
through one continuous actual Kummer forcing \(F\), the same Cramer
Green solution \(u_0\), and first spectral coefficient \(\delta\).
The *source-determined* corrected solution \(w\) has curvature
\[
 j=w''(B)
 =F(B)-\delta u_0(B)-A(B)w'(B)-Qw(B),\qquad
 A(r)=\frac2r+\frac{ir}{2},\quad Q=\mathrm{frozenZeroCoeff}(\mu,\theta).
 \tag{O1}
\]
For \(B>0\) define \(p=w(B)\), \(q=w'(B)\) and the actual
existing radial cutoff \(\chi_B(r)=1-\mathrm{cutoff}(3(r-B)/B)\).
The new original-source quadratic repair is
\[
 P(r)=p+(r-B)q+\tfrac12(r-B)^2j,\quad
 S(r)=\chi_B(r)P(r).
 \tag{O2}
\]
Unlike the historical affine repair, this matches the true \(w''(B)\).
The **actual CI 42825266426** proves the exact same-source curvature,
the six endpoint jets and both \(C^2\) outer interfaces in \(r\).
This is auxiliary to original §2.13; source SHA
\`23359602dd5f34921b2f3cb23aaeb1a153c41fff\`,
job **129860806977**, evidence artifact **13768179716**.
The job log contains
\`lake env lean --trust=0 -DwarningAsError=true\`,
exact \`#check\` and \`#print axioms\` for all three specified
theorems; its final allowlist is exactly
\`[propext, Classical.choice, Quot.sound]\` for each of the three.
The original ZIP evidence is recorded in GitHub Actions for this run.
This paragraph reports the original job audit; it does not claim a
fresh build of the later HEAD.

## 2. Complete local residual derivative: no hidden omitted drift term

Let \(C_k\) be global bounds for the actual existing smooth cutoff
\(\mathrm{cutoff}^{(k)}\), \(k=1,2,3\), respectively.
The third derivative \(\chi_B'''\) is explicitly available from
the pinned \`ActualHartreePhysicalCutoffC3\` producer
(CI 42812564318, Success). On the **actual repair annulus**
\(B\le r\le2B\):
\[
 |\chi_B|\le1,\quad
 |\chi_B'|\le\frac{3C_1}B,\quad
 |\chi_B''|\le\frac{9C_2}{B^2},\quad
 |\chi_B'''|\le\frac{27C_3}{B^3}.
\]
Define the genuine source-controlled jet budget
\[
 D=|p|+B|q|+B^2|j|.
\]
Elementary polynomial calculus on this annulus gives
\[
 |P|\le D,\quad |P'|\le D/B,\quad |P''|\le D/B^2,
\]
and therefore
\[
\begin{aligned}
 |S|&\le D,\\
 |S'|&\le A_1D/B,\qquad A_1=3C_1+1,\\
 |S''|&\le A_2D/B^2,\quad A_2=9C_2+6C_1+1,\\
 |S'''|&\le A_3D/B^3,\quad
       A_3=27C_3+27C_2+9C_1.
\end{aligned}\tag{O3}
\]
For the **full actual frozen original Kummer operator**
\(\mathcal K S=S''+A(r)S'+QS\) with the physical drift included,
\[
 (\mathcal K S)'=S'''+A'S'+AS''+QS',
 \qquad A'(r)=-\frac2{r^2}+\frac i2.
 \tag{O4}
\]
In particular, \(|A'|\le2/B^2+1/2\),
\(|A|\le2/B+B\), and
\[
 \boxed{\ 
 |(\mathcal KS)'(r)|\le D\left[
 \frac{A_3+2A_1+2A_2}{B^3}
 +\frac{\frac12A_1+A_2+|Q|A_1}{B}
 \right],\quad B\le r\le2B.
 \ }\tag{O5}
\]
All contributions from the derivative of the radial drift and
the nonconstant first-order coefficient are accounted for.
There is no unsupported independent source envelope.

## 3. The physical weighted derivative costs precisely a^(-1/2)

The physical repair is \(\mathcal R_a(y)=S(y/a)\).
By the exact scaling of the *same original* frozen Kummer operator,
\[
 E_a(y):=(\mathcal K_a\mathcal R_a)(y)
 =a^{-2}(\mathcal KS)(y/a),\quad
 \partial_y E_a=a^{-3}(\mathcal KS)'(y/a).
\]
For \(a\ge1\), **restricted to the physical repair branch**
\(aB\le y\le2aB\), in the radial measure \(dy\), (O5) gives
\[
 \boxed{\ 
 \begin{aligned}
 &\|(1+y^2)\partial_y E_a\|_{L^2(aB,2aB;dy)}\\
 &\le a^{-1/2}(1+4B^2)\sqrt B\,D
 \left[
 \frac{A_3+2A_1+2A_2}{B^3}
 +\frac{\frac12A_1+A_2+|Q|A_1}{B}
 \right].
 \end{aligned}
 \ }\tag{O6}
\]
Proof: \(dy=a\,dr\), \((1+a^2r^2)\le
a^2(1+r^2)\) for \(a\ge1\), and
\(1+r^2\le1+4B^2\) on \([B,2B]\).
The coefficient \(a^{-1/2}\) is **derived**, not postulated.
The shell estimate is local and does not yet handle
the inner profile, time derivatives, mixed nonlocal interactions,
moving \(B,\delta,\mu,\theta\), or the true Hamiltonian inverse.
The matching at \(2aB\) is \(C^2\); no delta-interface source
is inserted at that endpoint.

## 4. NEW decisive source-trace gate: continuous weighted L² does NOT control F(B)

The exact original curvature (O1) implies
\[
\begin{aligned}
 D
 &\le(1+B^2|Q|)|w(B)|
 +(3B+\tfrac12B^3)|w'(B)|\\
 &\quad+B^2\bigl(|F(B)|+|\delta|\,|u_0(B)|\bigr).
\end{aligned}\tag{O7}
\]
The \(|F(B)|\) term is **unavoidable in this Taylor-jet source norm**.
The historical norm \(\|F\|_{L^2_{7/4}}\), plus continuity of \(F\),
does **not** control point evaluation at an arbitrary fixed \(B>0\).

Indeed, fix \(B>0\) and a nonzero real smooth compactly supported
\(\psi\) with \(\psi(0)=1\), and set
\[
 F_N(r)=\sqrt N\,\psi(N(r-B)),\qquad N\to\infty .
\]
For all sufficiently large \(N\), the supports stay in a fixed
compact annulus about \(B\), and the original weighted \(L^2\)
norms of \(F_N\) are uniformly bounded:
\[
 \int_0^\infty \langle r\rangle^{7/2}|F_N(r)|^2dr
 =\int \langle B+s/N\rangle^{7/2}|\psi(s)|^2ds
 =O_{B,\psi}(1).
\]
But \(F_N(B)=\sqrt N\to\infty\).
Therefore **no universal bound** for the true source-derived
\(|j|\), or for (O6) via (O7), follows solely from old
weighted \(L^2\) membership plus continuity, unless the
specific PDE-dependent source enjoys extra regularity or
cancellation. The true quartic Hartree forcing is more structured
than an arbitrary \(F_N\); the example establishes exactly
the missing implication, **not** nonexistence of the desired orbit.



For fixed \(K,r_0,B,\mu,\theta\), one can make the preceding
failure of the source-to-curvature estimate quantitative using the
\emph{original matched} integral solution. Take \(\delta=0\),
\(U=DU=0\), with \(F_N\) as above. On a fixed compact
neighbourhood of \(B>r_0>0\), the two normalized Cramer Green
integrands are a smooth bounded Kummer basis times \(F_N\)
divided by a nonzero continuous Wronskian. Therefore
\[
 |u_{0,N}(B)|+|u_{0,N}'(B)|
 \lesssim_{K,r_0,B}\|F_N\|_{L^1(B-\varepsilon,B+\varepsilon)}
 =O(N^{-1/2}).
\]
The exact unshifted Kummer equation at \(B\) gives
\[
 |u_{0,N}''(B)|
 \ge |F_N(B)|-|A(B)|\,|u_{0,N}'(B)|
   -|Q|\,|u_{0,N}(B)|
 =\sqrt N-O(N^{-1/2})\longrightarrow\infty.
\]
Thus the original **source-selected** curvature \(j\) itself
cannot be bounded by the previous weighted \(L^2\) source norm
alone, even after the Cramer inversion. This is a norm-level
counterexample, not merely an inability to estimate a chosen
right-hand side of (O7), and it does **not** apply to the yet-to-be-proved
special regularity of the actual moving nonlinear Hartree source.

**Next non-negotiable original PDE producer:** a source-aligned,
moving-parameter-uniform trace/Sobolev control such as
\[
 |F(B,s)|\lesssim
 \|F(s)\|_{H^1(B/2,3B)}
 \lesssim \text{actual selected four-region Hartree source budget},
 \tag{O8}
\]
where the second bound must be *proved from the genuine
nonlocal quartic PDE*, not assumed. The same higher regularity
must control the whole nonlinear residual derivative, and moving
modulation derivatives and Lipschitz in the appropriate norm;
separate projected Hartree homogeneous smoothing remains open.

## 5. Acceptance and CI boundary

- Original 13 manuscript environments: **11/13 (84.62%)**.
- Pinned CI 42825266426 proves actual same-source **outer C² joins**
  and source-to-curvature identity; no full four-region C², source
  derivative, time gain, or PDE orbit.
- CI 42824686940 proves actual inner plateau source cancellation.
- CI 42536552509 already strictly proves the exact spectral finite
  *nonlinear PDE telescope*; repeat CI 42530158681's broken
  original SHA is unnecessary, but the identity gives **zero**
  residual gain by itself.
- (O3)–(O8) are **new human paper calculations**; not compiled
  Lean declarations, no new axioms, no artificial original
  environment count. **§2.13 and final Type-II theorem remain OPEN**.
