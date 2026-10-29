# One Kummer inverse family for an arbitrary compact parameter set

Fix a positive physical radius `z` and any compact set `A` in the real
`(mu, theta)` parameter plane. The terminal
`exists_actual_compact_parameter_kummer_family` constructs one positive closed
annulus `I = [z-d,z+d]`, one normalized reference pair at `(0,0)`, and a family

\[
 T_p:C(I;\mathbb C)\longrightarrow C(I;\mathbb C^2),\qquad p=(\mu,\theta),
\]

with the following properties for every `p in A`:

\[
 T_pF=(u,u'),\qquad
 u''+\left(\frac2r+\frac{ir}{2}\right)u'
 +\left(\theta+i\left(\frac14-\mu\right)\right)u=F.
\]

The derivatives are genuine radial derivatives, including at the endpoints.
All parameters use the same two homogeneous endpoint jet conditions from the
reference pair. The family obeys

\[
 \|T_p\|\le2B,\qquad
 \|T_pF-T_pG\|\le2B\|F-G\|,
\]
\[
 \|T_p-T_q\|\le4B^2\bigl(|\mu-\nu|+|\theta-\varphi|\bigr),
 \qquad q=(\nu,\varphi).
\]

The actual operator family is real analytic at every point of `A`
(`ContDiffAt` of order `omega`), with the explicit first derivatives

\[
 \partial_\mu T_p=iT_pPT_p,\qquad
 \partial_\theta T_p=-T_pPT_p,\qquad P(u,u')=u.
\]

Every finite parameter jet is uniformly bounded:

\[
 \forall n\in\mathbb N\quad\exists C_n>0\quad
 \forall p\in A,\qquad\|D_p^nT_p\|\le C_n.
\]

The annulus and the family are chosen before `n`; they are the same for all
orders. These are operator-valued Frechet derivatives, so the constants are
independent of the source. The higher-order constants are obtained by
compactness; no explicit growth rate in `n` is claimed.

## Why one annulus suffices

Compactness supplies `M >= 0` with `|mu|+|theta| <= M` on `A`. The actual
reference IVPs supply `eps > 0` and a uniform basis/Wronskian bound `C > 0`.
Choose

\[
 d=\min\left\{\frac{\varepsilon}{2},
       \frac{1}{16C^3(M+1)}\right\},\qquad B=4dC^3.
\]

The already constructed base inverse then satisfies

\[
 \|T_0\|\le B,\qquad (M+1)B\le\frac14.
\]

With `delta = theta-i mu`, the verified resolvent construction
`T_p = T0 (Id + delta P T0)^(-1)` applies simultaneously throughout `A`.
Analytic inversion and the actual coefficient map give parameter analyticity;
compactness bounds the continuous iterated Frechet derivatives. There is no
pointwise patch selection, gluing hypothesis, assumed fundamental pair, or
assumed inverse in the terminal statement.

## Validation and scope

Eight new theorems are in eight separate files, all on the terminal's import
chain. `verification/kummer_compact_family_validation.py` recompiles those eight
files and the 46 required local/parameter inverse sources into an isolated
fresh directory, using the pinned Lean/mathlib versions and
`--trust=0 -DwarningAsError=true`. It checks complete types, transitive axioms,
import closure, and unchanged source and compiled-artifact hashes. The full
audit is stored in reproducible compressed form with hashes.

The subsequent [boundary uniqueness block](../KummerBoundaryUnique/README.md)
proves that these fixed endpoint problems have unique classical jets, and
controls the error of any classical boundary jet by its equation residual.

This closes compact-parameter uniformity and all finite parameter jets for a
constructed local annulus at any fixed `z > 0`. Its width depends on the compact
parameter set. A prescribed larger matching annulus, the required spatially
weighted overlap estimates, and the actual one-layer Hartree nonlinear
residual remain open. Original manuscript acceptance remains **9/21**;
`prop:one-layer-stage3` and the main PDE theorem remain **OPEN**.
