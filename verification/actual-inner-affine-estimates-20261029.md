# Quantitative stability of the actual affine corrections

This extension uses the canonical definitions from
`HBL.ActualInnerAffinelyCorrected`. It adds no duplicate existence solver.
The strict original-environment count remains **9/21**.

For `1/2 < sigma <= 2`, set

\[
\|F\|_{2,\sigma}=\|\langle r\rangle^\sigma F\|_{L^2(0,\infty)},
\qquad e_\pm=\langle r\rangle^{-\sigma}\psi_\pm,
\qquad B_\pm=H_\pm(\chi_{\rm aff}r).
\]

All these weighted resonance and affine-source norms are finite by the
existing concrete Hartree estimates. The charges and corrected sources are

\[
a_+(F)=2\int_0^\infty\psi_+F\,dr,
\qquad a_-(F)=-\int_0^\infty\psi_-F\,dr,
\qquad P_\pm F=F-a_\pm(F)B_\pm.
\]

Writing `c_plus = 2` and `c_minus = 1`, the new estimates are

\[
|a_\pm(F)-a_\pm(G)|
\le c_\pm\|e_\pm\|_2\|F-G\|_{2,\sigma},
\]

\[
\|P_\pm F-P_\pm G\|_{2,\sigma}
\le
\bigl(1+c_\pm\|e_\pm\|_2\|B_\pm\|_{2,\sigma}\bigr)
\|F-G\|_{2,\sigma}.
\]

The constants are independent of `F` and `G`. The charge estimates use the
proved identities between physical resonance pairings and Hilbert inner
products. The correction estimates additionally prove the exact weighted
data identity in `L2`, then apply the triangle inequality. No pointwise
choice of an `L2` representative is assumed.

The two terminal Lean theorems are
`HBL.Profile.ActualInner.correctedPlusDataL2_difference_le` and
`HBL.Profile.ActualInner.correctedMinusDataL2_difference_le`.
Seven further lemmas prove the charge signs, charge difference bounds, and
the weighted data identities used by these estimates.

Reproduce with the pinned dependencies:

```bash
python3 verification/actual_inner_affine_estimates_validation.py
```

The validator checks all dependency revisions, uses
`--trust=0 -DwarningAsError=true`, exports all nine complete theorem types,
rejects truncated output, and checks the transitive axiom lists against
`propext`, `Classical.choice`, and `Quot.sound`. Its status and source hashes
are saved in `verification/actual-inner-affine-estimates-status.json`.

These are source-space estimates. They do not establish the classical
`H_±` solution, its affine tail and `L^{2,-sigma}` bounds, the parameter
uniform Kummer inverse, or the complete one-layer residual cancellation.
