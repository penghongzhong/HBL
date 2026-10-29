# Actual Kummer inverse on a common local parameter neighborhood

For every real base parameter `(mu0, theta0)` and positive physical radius `z`,
the terminal `exists_actual_localKummer_uniform_physical_family` constructs
`eps, B, rho > 0`, a fixed normalized base pair, and bounded complex linear
operators on one common positive annulus `I = [z-eps/2,z+eps/2]`.
For `|mu-mu0| + |theta-theta0| <= rho`, the output is the actual jet `(u,u')` and
satisfies, including at the annulus endpoints,

\[
 u''+\left(\frac2r+\frac{ir}{2}\right)u'
 +\left(\theta+i\left(\frac14-\mu\right)\right)u=F.
\]

The two endpoint conditions use the same base pair throughout the parameter
neighborhood. They are genuine homogeneous endpoint jet conditions, inherited
from the previously verified actual local inverse. No inverse or fundamental
pair is assumed by either terminal theorem.

Let `P(u,u')=u`, let `T0` be the previously constructed inverse, and write
`delta = (theta-theta0)-i(mu-mu0)`. The construction is

\[
 V=PT_0,\qquad R_\delta=(I+\delta V)^{-1},\qquad
 T_\delta=T_0R_\delta.
\]

For `||T0|| <= B` and `|delta| B <= 1/2`, strict proofs give

\[
 \|R_\delta\|\le2,\qquad \|T_\delta\|\le2B,\qquad
 \|T_\delta F-T_\delta G\|\le2B\|F-G\|.
\]

The exact resolvent identity and parameter estimates are

\[
 T_\delta-T_\eta=(\eta-\delta)T_\delta PT_\eta,
 \qquad \|T_\delta-T_\eta\|\le4B^2|\delta-\eta|,
\]
\[
 \frac{dT_\delta}{d\delta}=-T_\delta PT_\delta,
 \qquad \left\|\frac{dT_\delta}{d\delta}\right\|\le4B^2.
\]

The physical family has genuine operator-valued real parameter derivatives,

\[
 \partial_\mu T_{\mu,\theta}=iT_{\mu,\theta}PT_{\mu,\theta},
 \qquad \partial_\theta T_{\mu,\theta}=-T_{\mu,\theta}PT_{\mu,\theta},
\]

and is Lipschitz in `|mu-nu|+|theta-phi|`, with constant `4B^2`.
The complex-family terminal uses the explicit choice `rho = 1/(2B)` internally.

There are 17 new theorems, each in its own file, and one definitions file.
Every new source lies on the final physical-family terminal's import chain.
`verification/kummer_parameter_inverse_validation.py` recompiles all 18 new
sources and the 31-source local inverse foundation into an isolated temporary
directory, with `--trust=0 -DwarningAsError=true`. It audits the full types and
transitive axioms, verifies unchanged source and artifact hashes, and retains
the full audit in reproducible compressed form.

Scope: a common constructed local annulus and a neighborhood of each fixed
base parameter. A prescribed larger matching annulus, uniform constructions
over an entire compact parameter graph, and higher or mixed parameter jets
remain open. Original manuscript acceptance remains **9/21**;
`prop:one-layer-stage3` and the main PDE theorem remain **OPEN**.
