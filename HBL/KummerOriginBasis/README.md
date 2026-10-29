# Actual Kummer basis normalized at the origin

This block constructs the singular/regular basis needed by the manuscript's Kummer region. The input positive annulus and compact real parameter set are fixed before construction. It does not shrink the annulus and does not assume a fundamental pair.

For the actual frozen operator

\[
L_{\mu,\theta}u=u''+(2/r+ir/2)u'+(\theta+i(1/4-\mu))u,
\]
put \(y=ru\). The regularized equation is

\[
y''+ir\,y'/2+(\theta-i(\mu+1/4))y=0.
\]

`RegularIVP.lean` constructs this equation on any prescribed finite interval, using the already verified finite-dimensional linear IVP theorem. `Existence.lean` takes the initial data

\[
(y(0),y'(0))=(1,0),\qquad (x(0),x'(0))=(0,1).
\]

`PhysicalJets.lean` verifies the actual derivatives of \(\Phi=y/r\) and \(\Psi=x/r\), and the exact frozen equation away from zero. `Wronskian.lean` proves the regularized determinant by its integrating factor; `PhysicalWronskian.lean` then proves

\[
\Phi\Psi'-\Phi'\Psi=r^{-2}e^{-ir^2/4}.
\]

The multiplicative constant is exactly one, fixed by the initial data. `Uniqueness.lean` proves that any two regularized pairs with these initial data agree throughout their common prescribed interval (the theorem takes the same interval for both). It asserts no equality outside that interval.

`Normalization.lean` proves the right limits at zero:

\[
\Phi-r^{-1}\to0,\quad \Psi\to1,\quad r^2\Phi'\to-1,\quad r\Psi'\to0.
\]

`AsymptoticBound.lean` strengthens the value limits to actual quantitative estimates from the ODE. If both regularized jets are bounded by \(G\), and the sum of the two coefficient norms is bounded by \(D\), then for \(0<r\le R\),

\[
|\Phi-r^{-1}|\le DG r,\qquad |\Psi-1|\le(D+1)G r^2.
\]

These bounds are derived by repeated mean-value estimates, with no Frobenius remainder assumption.

## Terminal statement

`exists_compact_origin_kummer_basis` in `CompactBasis.lean` takes arbitrary compact \(A\subset\mathbb R^2\) and prescribed \(0<a<b\). It returns common constants \(C,H>0\) and, for every parameter in \(A\), an actual origin-normalized pair on \([0,b+1]\), with:

- both physical second-order equations on the closed input annulus \([a,b]\), including full derivatives at its endpoints;
- the exact nonzero physical Wronskian above;
- the same bound \(C\) for \(|\Phi|,|\Phi'|,|\Psi|,|\Psi'|,|W^{-1}|\) throughout that annulus;
- the four origin limits and uniqueness among regularized pairs with the prescribed initial data;
- the same \(H\) in \(|\Phi-r^{-1}|\le Hr\), \(|\Psi-1|\le Hr^2\) for all \(0<r\le b+1\).

The uniform regularized bound is \(G=e^{(D+1)(b+1)}\), where compactness bounds the zero-order coefficient and the first-order coefficient has norm \(r/2\). One annular bound is \(C=G(a^{-1}+a^{-2})+b^2+1\); \(|W^{-1}|=r^2\) exactly. This is a finite uniform estimate, not an optimized constant.

## Scope of original-environment acceptance

The zero-point singular/regular normalization and determinant now have an actual constructed basis with uniform zeroth-parameter-order bounds. The prior center-normalized inverse cannot be silently relabelled as the manuscript inverse: the basis also determines its two endpoint conditions. The Green operator in this origin-normalized basis still needs its own actual construction/certificate or a proved conversion from the existing inverse.

Still open for original `prop:one-layer-stage3` are: actual parameter derivatives and all finite orders uniformly on the prescribed annulus; the full finite Frobenius expansion and weighted overlap; the above Green operator/endpoint correspondence; actual regional Hartree source and residual matching; and the genuine positive-gain classification. The \(r\)-coefficient in the singular expansion and higher remainders are not included in this block's theorem statements. No explicit hypergeometric formula or large-radius radiation asymptotic is asserted.

Original acceptance remains **9/21**. This block adds **11 supporting theorems**, each in its own file, and **zero** accepted original environments.

## Verification

Run `python3 verification/kummer_origin_basis_validation.py` with the pinned Lean and Lake environment. The validator checks the dependency revisions, rebuilds the three unchanged finite-IVP foundation files and all thirteen new source files into a fresh isolated artifact directory under `--trust=0 -DwarningAsError=true`, then audits all full theorem types, the actual definition bodies and the structure constructor fields. Transitive axioms are restricted to `propext`, `Classical.choice`, and `Quot.sound`.

The earlier flat HBL imports come from the normal pinned build; this is explicitly not a fresh strict audit of every file in the repository. The new sources introduce no `sorry`, `admit`, new axioms, `unsafe`, `native_decide`, or disabled linters. The report and compressed complete audit are `verification/kummer-origin-basis-status.json` and `verification/kummer-origin-basis-types-and-axioms.txt.gz`.
