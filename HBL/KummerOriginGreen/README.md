# HBL Kummer origin-gauge Green bridge — strict evidence

Target: original manuscript `prop:one-layer-stage3` (old-2.12). It remains open; original accepted environments remain **9/21**.

The Green kernel is constructed using the **actual origin-normalized** singular/regular pair, not the previously certified but differently normalized center-annulus pair. On each prescribed positive annulus `[a,b]`, its determinant is `W(r)=r^(-2)exp(-i*r^2/4)`; the two outgoing endpoint functionals are those of the actual manuscript.

- `GreenBridge.lean`: exact ODE, coefficient and solution derivatives, separated endpoint conditions; nine audited theorem declarations.
- `UniformBound.lean`: source, integral, C1, compact-parameter uniform bounds; four audited theorem declarations.
- `GreenTerminal.lean`: physical ODE and compact-uniform bounds in one terminal, pending strict audit at time of this commit.
- `GreenUnique.lean`: physical homogeneous boundary uniqueness from two endpoint functionals, pending strict audit at time of this commit.

The first attempt (Actions 40846020063) failed at a no-progress `dsimp` and has been repaired. **Actions 40847465327 succeeded**: the first 13 supporting theorem statements compiled under Lean 4.35.0-rc3, Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`, `trust=0`, warning-as-error, and passed exported-type and transitive-axiom checking with no `sorryAx`. The full original paper was not rebuilt by this targeted run.

The next strict run includes all 16 declarations, notably the combined terminal and the uniqueness of the actual origin-basis Green boundary problem. Its outcome must not be presumed.

**Open original obligations:** the prescribed annulus parameter derivatives through all required orders; finite Frobenius overlap and actual Hartree source/regularity identification; threshold-charge/remote-region matching; proof of genuine positive gain for the physical residual. In particular the structural `OneLayerElimination.lean` interface is not an independent proof that the physical PDE source satisfies its generated-term classifications. Do not count this subresult as original theorem environment 10/21. 
