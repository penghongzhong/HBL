# Unique local Kummer boundary solutions, uniform on compact parameter sets

For every fixed `z > 0` and compact `A` in the real `(mu, theta)` plane,
`exists_actual_compact_parameter_kummer_unique_family` constructs one positive
closed annulus `I = [z-d,z+d]`, one actual reference pair `K` at `(0,0)`, and one
bounded complex-linear family

\[
T_p:C(I;\mathbb C)\to C(I;\mathbb C^2),\qquad p=(\mu,\theta).
\]

For every continuous source `F` and `p in A`, the jet `T_p F = (u,u')` solves

\[
u''+\left(\frac2r+\frac{ir}{2}\right)u'
 +\left(\theta+i\left(\frac14-\mu\right)\right)u=F
\]

with the fixed separated endpoint conditions

\[
u(z+d)\psi'(d)-u'(z+d)\psi(d)=0,\qquad
\phi(-d)u'(z-d)-\phi'(-d)u(z-d)=0.
\]

The original classical right-inverse certificate, including genuine first and
second radial derivatives at both endpoints, is retained. The new result is
an exact characterization for arbitrary classical boundary jets:

\[
\operatorname{IsKummerBoundarySolution}(K,d,c_p,F,U)
\quad\Longleftrightarrow\quad U=T_pF.
\]

Here a boundary solution has representatives `u,v : R -> C` with
`U=(u,v)` on `I`, genuine derivatives `u'=v` and
`v'=F-a v-c_p u` at every point of `I`, and the two displayed endpoint
conditions. Uniqueness concerns the continuous jet on `I`; representatives
outside `I` need not agree. No uniqueness hypothesis is assumed.

## Residual error estimate

If an arbitrary classical jet `U` obeys the same endpoint conditions and its
actual source is `G`, then, uniformly for `p in A`,

\[
\|U-T_pF\|_{C(I;\mathbb C^2)}\le 2B\|G-F\|_{C(I;\mathbb C)}.
\]

The jet norm uses the maximum of the value and first derivative norms. Thus
the equation residual controls both errors. This statement requires the
homogeneous endpoint conditions; it does not estimate endpoint mismatches.

The same family retains all previously constructed quantitative properties:

\[
\|T_p\|\le2B,\quad
\|T_p-T_q\|\le4B^2(|\mu-\nu|+|\theta-\varphi|),
\]
\[
\partial_\mu T_p=iT_pPT_p,\quad
\partial_\theta T_p=-T_pPT_p,\quad P(u,v)=u,
\]

real analyticity at every `p in A`, and uniform bounds on all finite
operator-valued parameter derivatives. Neither the annulus nor the family
depends on the derivative order.

## Proof of uniqueness

For a homogeneous solution of the reference equation in the coordinate
`t=r-z`, the two Cramer coefficients

\[
A(t)=\frac{u(t)\psi'(t)-v(t)\psi(t)}{W(t)},\qquad
B(t)=\frac{\phi(t)v(t)-\phi'(t)u(t)}{W(t)}
\]

have derivative zero. The actual ODE gives `W'=-a W`; the already constructed
nonvanishing Wronskian permits division. The mean value inequality shows that
`A` and `B` are constant on the entire closed interval. Their respective
endpoint values vanish, and Cramer's identities give `u=v=0`.

For a perturbed coefficient `c_0+delta`, any solution satisfies the base
problem with source `G=F-delta P U`. Base uniqueness gives `U=T_0 G`, hence
`(Id+delta P T_0)G=F`. The verified Neumann inverse identifies `G` and therefore
`U`. The radius construction makes this argument valid simultaneously on
all of `A`. The residual estimate then follows from the actual operator norm.

## Validation and scope

Ten new theorems occupy ten separate files, alongside one definition file.
All eleven sources are used on the terminal dependency chain.
`verification/kummer_boundary_unique_validation.py` recompiles these sources
and their 52 required foundation sources in a fresh isolated directory with
Lean `4.35.0-rc3`, pinned mathlib, `--trust=0 -DwarningAsError=true`.
The complete types and transitive axioms are audited and retained in
`verification/kummer-boundary-unique-types-and-axioms.txt.gz`, with source and
artifact hashes in `verification/kummer-boundary-unique-status.json`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The subsequent [source tangent block](../KummerSourceTangents/README.md)
identifies both physical parameter derivatives for varying sources as unique
classical tangent solutions and proves a coupled primal/tangent residual bound.

The annulus is constructed and may shrink with the parameter set. A prescribed
matching annulus, the manuscript's spatially weighted overlap estimates, and
its actual nonlinear Hartree residual are still separate open obligations.
Original manuscript acceptance remains **9/21**. `prop:one-layer-stage3` and
the main PDE theorem remain **OPEN**.
