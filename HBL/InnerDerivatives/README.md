# Actual inner derivative estimates

This batch continues the actual two-channel affine inverse from `HBL.InnerEstimates`.
For fixed `3/2 < sigma < 2`, continuous sources `F` in `L^{2,sigma}`, and every
`beta < 1/2`, let `q_±(F)` be the canonical normalized remainders and
`u_±(F) = q_±(F) + a_±(F) model` the actual affine outputs.
The constants below depend on the fixed weights and actual operators, not on the source.

The verified estimates are

\[
 (1+r)|q_\pm'(F)(r)|\le C_\sigma^\pm\|F\|_{2,\sigma}\quad(r>0),
 \qquad \|q_\pm'(F)\|_{2,\beta}\le C_{\sigma,\beta}^\pm\|F\|_{2,\sigma},
\]
\[
 \|q_\pm''(F)\|_{2,\sigma}\le D_\sigma^\pm\|F\|_{2,\sigma},
 \qquad \|u_\pm''(F)\|_{2,\sigma}\le E_\sigma^\pm\|F\|_{2,\sigma}.
\]

Weighted membership is proved with every norm bound. Both first and second
remainder derivatives satisfy the corresponding weighted Lipschitz bounds in
`F - G`; the first derivative also satisfies the pointwise Lipschitz bound
with multiplier `1+r`.
For the actual outputs,

\[
 (1+r)|u_\pm'(F)(r)-a_\pm(F)|\le C_\sigma^\pm\|F\|_{2,\sigma}\quad(r>2),
 \qquad u_\pm'(F)(r)\longrightarrow a_\pm(F).
\]

`ActualDerivativeSolvers.lean` packages the source-independent nonnegative
constants and both actual channels in `exists_actualInner_derivative_estimates`.
It imports all 35 new theorem files; the other two source files contain definitions.

The first derivative is identified with the tail integral of the actual reconstructed
source. Its zeroth and first absolute moments give the inverse-linear bound.
The second derivative is identified almost everywhere with the negative total source;
`<r>^sigma (1+r^2)^(-1) <= 1` for `sigma <= 2` transfers the existing Hilbert norm
bounds. Affine restoration uses the existing compactly supported model second derivative.

Run `python verification/inner_derivative_estimates_validation.py` in the pinned
Lean environment. It builds the terminal module, checks all 37 source files with
`--trust=0 -DwarningAsError=true`, prints complete types and transitive axiom lists
for all 35 theorems, and retains their reproducible compressed output and hashes.

These are supporting certificates. Original manuscript acceptance remains **9/21**;
`prop:one-layer-stage3` and the main PDE theorem remain **OPEN**. This batch does not
establish uniformity over varying weight/parameter families, parameter derivatives,
stronger source-specific tail asymptotics, the actual Kummer annulus inverse, or the
nonlinear regional source and cutoff matching required by the one-layer construction.
