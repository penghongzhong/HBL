# HBL 2.13 — actual speed-source bridge and sharp physical-region growth

2026-11-04. **Formal revised manuscript count remains 11/13 (84.62%).** These are strictly audited intermediate producers, not acceptance of the finite-profile theorem.

## Immutable successful Lean runs

1. Actual original-to-adjusted source norm bridge: code commit \`5a408f3f84367c52adf4c8d96a527e4b9ece45f2\`; strict CI [41854939119](https://github.com/penghongzhong/HBL/actions/runs/41854939119) **success**.
2. Sharper, actual speed-source growth and negative-radius-power obstruction cost: code commit \`99697529c57d69976a4488a5369cb79a77d99557\`; strict CI [41856746274](https://github.com/penghongzhong/HBL/actions/runs/41856746274) **success**. Evidence artifact id \`13338391686\`, SHA-256 \`6e4e410cf7831848296b210e769366d05bbf111b44e87d2d2d6330724444a144\`.

Both use pinned Lean 4.35.0-rc3 / Mathlib a98628e16, target \`--trust=0 -DwarningAsError=true\` and whole-type / \`#print axioms\` checks. The source-norm bridge added four public theorems and exposed the already proved weighted-source representative linearity. The sharp growth round added two public theorems and exposed three previously proved profile/cutoff helpers. Their statement audit does not report new axioms or sorry.

## Actual mathematical statements

Let \`F_{+,0}\`, \`F_{-,0}\` be the real and imaginary parts of the original conjugated Hartree source; let the genuine scale and phase corrections be \`G_b=r eta_L Q_c\` and \`G_omega=r eta_L V_c\`, with \`eta_L=1-cutoff(r/L)\`. Thus

\[
F_+=F_{+,0}+\delta\omega G_\omega,\qquad
F_-=F_{-,0}+\delta b G_b .
\]

The already audited full coupled compatibility inversion gives

\[
|\delta b|+|\delta\omega|
\le \frac{1024}{a B^2}\,\|Z\|,\qquad
Z=T_{L/a}(J_0)-\Pi_{[L/a,B]}(F_0),
\]

where both the actual Fredholm baseline jet \`J_0\` and the entire original outer Green source \`F_0\` are retained.

The first new Lean producer proved the actual Hilbert-space norm inequality and its physical specialization

\[
N_{\rm adjusted}
\le N_0+\frac{1024C L^4}{aB^2}\|Z\|.
\]

The second new producer removes a gratuitous power of \`L\`: from the previously proved uniform closeness \`|Q_c-\Lambda W|+|V_c-W|\lesssim |c|\`, the actual cutoff range \`0\le\eta_L\le1\`, and the real bubble inequalities \`|rW(r)|\le1\`, \`|r\Lambda W(r)|\le3\`, one derives on \`0<r\le2L\`

\[
|G_b(r)|+|G_\omega(r)|\le C_0,\qquad L|c|\le1.
\]

The source vanishes for \`r\ge2L\`. Its **same original** \`L^{2,7/4}(dr)\` norm is therefore at most \`C L^{5/2}\`. The power \`5/2\` is a deliberately safe bound (the exact weight and \`dr\` volume would allow further improvement). This is now a kernel-checked theorem of the explicit physical source, not an abstract source-size premise.

For \`L\ge1\`, \`L|c|\le1\` and \`a\ge L^3\`, the actual speed inverse bound yields

\[
\boxed{\quad N_{\rm adjusted}
\le N_0+\frac{1024C}{B^2}L^{-1/2}\|Z\|. \quad}
\]

The speed inverse inequality is a premise in this last producer, but was proved in the separate full compatibility-matrix module, and must be applied to the **same** \`K, B, a, c, F_0, J_0\` in the final construction.

## Precise remaining obligation for manuscript 2.13

The new factor is small **relative to the complete obstruction** \`Z\`; it does **not** independently prove \`Z\` small in the original PDE norm. The next nontrivial producer is

\[
\|T_{L/a}(J_0)\|+\|\Pi_{[L/a,B]}(F_0)\|
\le C\,{\cal N}_{\rm original}(\ell,z)
\]

with the exact source weights and uniform moving-parameter constants, followed by actual full PDE residual reconstruction, Kummer-to-infinity matching and finite-profile iteration.

There is a concrete candidate for the integral half. The original physical source \`S(y)\` already has the verified envelope

\[
(1+y^2)^{7/8}|S(y)|\le K\ell^{1/8}(1+y)^{-5/8}.
\]

For \`y\ge L\ge1\`, this implies \`y^2|S(y)|\lesssim\ell^{1/8}\`. The origin-normalized Kummer Green density has an \`r^2\` factor, and \`F_0(r)=-a^2S(ar)\`; hence the target integral is

\[
\|\Pi_{[L/a,B]}F_0\|\lesssim B\ell^{1/8}.
\]

**This last bound is a mathematical candidate, not a new Lean acceptance.** Its exact Green density, interval FTC / integrability, and uniform origin basis constants must be joined with the same baseline jet. The baseline jet cannot be replaced by an unrelated existential Fredholm solution. In the physical parameter region, \`L|c|\le1\` should be derived from \`a\ge L^3\` and a choice \`0<\varepsilon\le1\` with \`a|c|\le\varepsilon\`, not added to the final PDE theorem without proof.

Even after such an \`Z\` bound, the full three-domain PDE correction must include nonlocal feedback, actual time dependence, moving basis/interface, remote radiation and nonlinear remainder in \`X_f^{sc}\`. Only then can the existing structural finite recursion become the actual finite-profile theorem. The concentration rate must still be **derived from the Hartree dynamics**, not postulated.
