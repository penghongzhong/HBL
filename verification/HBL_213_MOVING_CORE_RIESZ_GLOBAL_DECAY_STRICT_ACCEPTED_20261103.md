# HBL revised 2.13 — actual moving-core Riesz global decay, strict accepted

- **Dedicated strict CI:** https://github.com/penghongzhong/HBL/actions/runs/41610711049 — `completed/success`.
- **Audited source commit:** `7f9e4e199a19df76e5122800d111d9ff20fb576f`.
- **File:** `HBL/TypeIIDynamicSelection/ActualHartreeCoreRieszSpatialDecay.lean` and `ActualHartreeCoreRieszSpatialDecayAudit.lean`.
- Compiler and dependencies: Lean 4.35.0-rc3, pinned Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Checks: complete `lake build`, `lake env lean --trust=0 -DwarningAsError=true`, exported theorem `#check`, transitive `#print axioms`, and prohibition of `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`.

The actual moving-monopole radial core
`V_c(r)=monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c r` satisfies
`(1+r)*|V_c(r)| <= 2+9*monopoleRadialBoundConstant`
for `r>0` and `|c|<=1`. The physical positive inverse-square Hartree radial kernel then implies the **genuine convolution bound**
```math
|I_2[V_c^4](r)|
\le \frac{(2+9 C_{mon})^4 C_{W^2}}{1+r},\quad r>0.
```
This rigorously supplies one of the full four-term interaction's three spatial potentials and preserves the far-field radius instead of using only the older uniform \(O(\ell)\) Taylor defect.

**Not proved by this environment:** the pure-radiation spatial potential (separate audit), ten-term full interaction weighted \(L^2\) integrability, actual inner/Kummer/remote \(C^1\) compatibility, finite generated residual recursion, or the dynamically selected Type-II blowup law. Numbered manuscript remains **11/13** until a whole manuscript environment closes.
