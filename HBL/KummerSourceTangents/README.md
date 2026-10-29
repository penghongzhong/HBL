# Source-dependent Kummer parameter tangents and coupled residual bounds

Fix `z > 0` and a compact set `A` in the real `(mu, theta)` parameter plane.
The terminal `exists_actual_compact_kummer_source_tangent_family` retains the
actual inverse family from `KummerBoundaryUnique` on one common positive
annulus `I=[z-d,z+d]`, with the same fixed separated endpoint conditions.
Write

\[
L_pu=u''+\left(\frac2r+\frac{ir}{2}\right)u'
 +\left(\theta+i\left(\frac14-\mu\right)\right)u,
\qquad p=(\mu,\theta),\qquad P(u,v)=u.
\]

The operator family satisfies `||S_p|| <= 2B`; its analyticity, parameter
Lipschitz bound, all finite operator parameter-jet bounds and classical
boundary uniqueness remain part of the terminal statement.

## Actual derivatives for varying sources

Let `F_p` be a continuous radial source with Banach-valued partial derivatives
`F_mu` and `F_theta` at `p`. No joint differentiability is needed. With
`U_p=S_p F_p=(u_p,u_p')`, the theorem proves

\[
\partial_\mu U_p=S_p(F_\mu+iP U_p),\qquad
\partial_\theta U_p=S_p(F_\theta-P U_p).
\]

These are actual derivatives in `C(I; C^2)`. Evaluation at every radial point
also gives the parameter derivatives of both `u_p(r)` and `u_p'(r)`, including
both endpoints. The two tangent jets uniquely solve

\[
L_p(\partial_\mu u_p)=F_\mu+i u_p,\qquad
L_p(\partial_\theta u_p)=F_\theta-u_p
\]

with the same homogeneous endpoint conditions. Each tangent carries the
original classical certificate: genuine first and second radial derivatives
and the equation at every point of the closed annulus. Thus the spatial
linearized equation is proved from the constructed inverse and the actual
parameter derivative; no derivative-interchange or tangent-equation
assumption is introduced.

For either `j=mu` or `j=theta`, the bound is

\[
\|\partial_j U_p\|\le 2B\|F_j\|+4B^2\|F_p\|.
\]

The jet norm is the maximum of the value and first radial derivative sup
norms. All constants and the annulus are common to `p in A`.

## Residual propagation through the tangent equation

The generic result also permits any `q in C`; take `q=i` for `mu` and `q=-1`
for `theta`. For target source `F` and target source derivative `G`, define

\[
X=S_p(G+qP S_pF).
\]

Let `U,V` be arbitrary classical jets obeying the fixed endpoint conditions,
with actual equation sources `H,J`. Define the two equation residuals by

\[
R_0=H-F,\qquad R_1=J-G-qP U.
\]

Lean proves

\[
\|V-X\|\le 2B\|R_1\|+4|q|B^2\|R_0\|.
\]

The first residual is fed into the tangent estimate exactly once. This is a
bound for arbitrary approximate primal/tangent jets satisfying the boundary
conditions; `V` need not be a parameter derivative. For either physical
parameter, `|q|=1`. Endpoint mismatches are outside the statement.

## Proof and validation

The real product rule is applied after restricting the complex-linear
operator family to real scalars. Continuous evaluation then gives pointwise
derivatives. The actual inverse certificate and boundary uniqueness identify
the tangent equation. The norm bound follows from `||P U|| <= ||U||` and the
operator norm. The coupled residual estimate uses the exact identity

\[
J-(G+qP S_pF)=R_1+qP(U-S_pF)
\]

and the previously proved primal residual estimate.

Seven new theorems occupy seven separate files, alongside one definition
file. All eight sources are on the terminal dependency chain. The validator
`verification/kummer_source_tangents_validation.py` recompiles these eight
sources and 63 foundation sources into a fresh isolated directory, using
Lean `4.35.0-rc3`, mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`,
`--trust=0 -DwarningAsError=true`. The audit prints all three new definition
bodies as well as every new theorem's full type and transitive axioms.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Reproducible
compressed evidence and source/artifact hashes accompany the validator.

This closes the source-dependent Kummer tangent equations and their coupled
residual estimate on the constructed local annulus. It does not identify the
manuscript's nonlinear Hartree source or prove its parameter differentiability.
The prescribed matching annulus, weighted overlap matching and actual
nonlinear residual remain open. Original manuscript acceptance stays **9/21**;
`prop:one-layer-stage3` and the main PDE theorem remain **OPEN**.
