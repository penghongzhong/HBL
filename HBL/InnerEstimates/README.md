# Quantitative bounds for the actual inner inverses

For fixed weights `3/2 < sigma < 2` and `tau > 3/2`, the actual normalized
H-plus/H-minus inverses satisfy

    ||u_pm(F)||_(2,-tau) <= C_pm(sigma,tau) ||F||_(2,sigma),
    ||u_pm(F)-u_pm(G)||_(2,-tau) <= C_pm(sigma,tau) ||F-G||_(2,sigma).

The constants are independent of the sources. They are built from the verified
compact Fredholm lower bounds on the actual kernel complements, norms of the
actual Green and potential operators, weighted physical resonance/affine-source
norms, and the L2 norms of the explicit scalar decay weights. No inverse or
coercivity estimate is supplied as an external hypothesis.

The remainders have the stronger positive-half-line pointwise stability bound
and weighted stability in `L^{2,-tau}` for every `tau > 1/2`. The full outputs
retain the forced physical affine slopes, zero origin values, finite affine
tails, and membership in every `L^{2,-tau}` for `tau > 3/2`.

`normalizedPlusInner` and `normalizedMinusInner` choose the existing unique
solutions in the actual Hilbert kernel complements. Their equations are proved
in `PlusEquation.lean` and `MinusEquation.lean`. For continuous input sources,
`PlusOutputClassical.lean` and `MinusOutputClassical.lean` establish pointwise
first and second differentiability and the original equations `H_pm u_pm = F`.
The norm and stability bounds themselves require only the weighted L2 source
assumption. The terminal `ActualBoundedSolvers.lean` collects these results.

Each new theorem is in its own Lean file. Run
`python verification/inner_weighted_estimates_validation.py` in the pinned
Lean 4.35.0-rc3 environment, with Mathlib revision
`a98628e16c11f5167f16124105ddce53efa9bfe5`. The validator checks every source with
`--trust=0 -DwarningAsError=true` and exports complete theorem types and
transitive axioms. Untruncated type output is stored as reproducible gzip,
with both compressed and uncompressed SHA256 values in the report.

This establishes source-independent constants at fixed weights; it does not
establish uniformity as sigma or other parameters vary, parameter jets,
weighted derivative bounds, quantitative tail rates, or the nonlinear regional
matching required by the original one-layer theorem. Original manuscript
acceptance remains 9/21; `prop:one-layer-stage3` and the main PDE theorem remain
open.
