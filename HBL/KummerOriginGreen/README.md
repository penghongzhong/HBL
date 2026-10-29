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
