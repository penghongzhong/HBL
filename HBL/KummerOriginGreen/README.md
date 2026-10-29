# HBL Kummer origin-gauge Green bridge — strict evidence

Target: original manuscript `prop:one-layer-stage3` (old-2.12). It remains open; original accepted environments remain **9/21**.

The Green kernel is constructed using the **actual origin-normalized** singular/regular pair, not the previously certified but differently normalized center-annulus pair. On each prescribed positive annulus `[a,b]`, its determinant is `W(r)=r^(-2)exp(-i*r^2/4)`; the two outgoing endpoint functionals are those of the actual manuscript.

- `GreenBridge.lean`: exact ODE, coefficient and solution derivatives, separated endpoint conditions; nine audited theorem declarations.
- `UniformBound.lean`: source, integral, C1, compact-parameter uniform bounds; four audited theorem declarations.
- `GreenTerminal.lean`: physical ODE and compact-uniform bounds in one terminal, strictly certified by Actions 40849544799.
- `GreenUnique.lean`: physical homogeneous boundary uniqueness from two endpoint functionals, strictly certified by Actions 40849544799.

The first attempt (Actions 40846020063) failed at a no-progress `dsimp` and has been repaired. **Actions 40847465327 succeeded**: the first 13 supporting theorem statements compiled under Lean 4.35.0-rc3, Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `trust=0`, warning-as-error, and passed exported-type and transitive-axiom checking with no `sorryAx`. The full original paper was not rebuilt by this targeted run.

**Actions 40849544799 succeeded** on source commit 116e309585a406cf724fb9bddeb6a13a0125603d: all **16 auxiliary theorems** compiled and their complete types and transitive axioms were audited under pinned Lean/Mathlib, trust=0, and warning-as-error. The only axioms were propext, Classical.choice, and Quot.sound; no sorryAx. The branch's later changes prior to this README update were documentation and workflow caching only, not Lean source edits.

**Open original obligations:** the prescribed annulus parameter derivatives through all required orders; finite Frobenius overlap and actual Hartree source/regularity identification; threshold-charge/remote-region matching; proof of genuine positive gain for the physical residual. In particular the structural `OneLayerElimination.lean` interface is not an independent proof that the physical PDE source satisfies its generated-term classifications. Do not count this subresult as original theorem environment 10/21. 

## Shortest remaining derivative bridge

The physical Green endpoint functionals depend on `(mu,theta)` through the origin-normalized `Phi,Psi`. Therefore do **not** apply the fixed-boundary inverse-resolvent identity directly to the family of physical outgoing Green maps: it would omit parameter derivatives of those endpoint functionals. Instead prove all-order parameter jets for the regularized origin IVP with its genuinely fixed initial data, then differentiate the explicit two-integral physical Green formula. The physical Wronskian inverse `r^2 exp(i r^2/4)` is independent of the parameters, so its parameter derivatives vanish. The resulting finite binomial convolution of basis jets gives the required compact-uniform `C^1` estimates without changing the manuscript's physical boundary conditions. No extra numbered theorem is claimed here.

## 2026-10-29 — source stability and finite Frobenius jets

Actions **40853755059 succeeded**: four physical source-stability declarations in HBL/KummerOriginGreen/SourceStability.lean passed pinned Lean 4.35.0-rc3, Mathlib a98628e16, trust-zero, warnings-as-errors, exact type and transitive-axiom checks. The origin-normalized Green map is complex-linear in the source; on any prescribed positive annulus its real radial value/derivative sum has Lipschitz constant at most 2 C^3 (b-a), with one C for an arbitrary compact real parameter set.

Actions **40857582165 succeeded**: thirteen Frobenius declarations prove the actual frozen-equation finite-jet cancellations and compact-uniform residual bounds. Let q=theta-i(mu+1/4) and

\[
 c_1=-q/2,\quad c_3=q(q+i)/24,\quad b_2=-(q+i/2)/6.
\]
For nonzero complex z,

\[
 \mathscr S_{\mu,\theta}(z^{-1}+c_1z+c_3z^3)=c_3(q+2i)z^3,
 \qquad
 \mathscr S_{\mu,\theta}(1+b_2z^2)=b_2(q+3i/2)z^2.
\]

For any compact parameter set A, the two physical residuals are bounded by C_A r^3 and C_A r^2 for all r>0. The coefficient vector (c1,c3,b2) is genuinely smooth; every finite Frechet parameter derivative has one uniform bound on A. THIS IS ONLY A RESULT FOR FINITE POLYNOMIAL JETS. It does not yet prove all-order differentiability of the infinite exact origin basis or a remainder bound against the exact basis.

The origin Green proof block now has **33 strictly audited auxiliary declarations**. The verified source commit is 30d64a5b20b13460d2fd2cc5a6cf1f0735b174b6. Allowed transitive axioms: propext, Classical.choice, Quot.sound; no sorryAx. The certified declaration names and scope are recorded in verification/origin-green-frobenius-strict-status-20261029.json. Original manuscript acceptance stays **9/21**.

### Shortest next proof chain

For the true origin-normalized IVP, use the recurrences

\[
a_{n+1}= -\frac{q+in}{(2n+2)(2n+1)}a_n,\qquad
b_{n+1}= -\frac{q+i(n+\frac12)}{(2n+3)(2n+2)}b_n,\qquad a_0=b_0=1.
\]

These complete recurrences remain mathematical candidates, not yet Lean-certified for arbitrary n. Prove uniform convergence of the exact series and its parameter/radial derivatives, then differentiate the actual two-integral Green formula with its parameter-dependent endpoint conditions. Finally identify the actual Hartree source in the inner/Kummer/remote regions, establish the weighted overlap and prove the true positive *time*-weight gain for all generated terms. A spatial O(r^3) finite-jet residual alone does not imply the required time-weight gain in original prop:one-layer-stage3.
