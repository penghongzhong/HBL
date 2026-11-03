# Revised HBL 2.13 — correct radially conjugated inner Hartree affine charges: STRICT ACCEPTED

- **Dedicated strict CI:** https://github.com/penghongzhong/HBL/actions/runs/41666667907 — completed/success; its strict physical inner build/full type and axiom audit step is success.
- **Audited source commit:** \`5945fbb2dda365bc4070e00fa0f47f283c4a1e44\`.
- **Module:** \`HBL/TypeIIDynamicSelection/ActualHartreeConjugatedInnerChargeGain.lean\`.
- **Audit:** \`HBL/TypeIIDynamicSelection/ActualHartreeConjugatedInnerChargeGainAudit.lean\`.
- Lean 4.35.0-rc3, Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5; no \`sorry\`, \`admit\`, \`native_decide\`, \`unsafe\` or added axiom. Strict check uses \`lake env lean --trust=0 -DwarningAsError=true\` and \`#print axioms\`; the audited theorem permits only \`propext\`, \`Classical.choice\`, \`Quot.sound\`.

## Exact mathematical statement

Use the original critical inverse-square Hartree nonlocal core-radiation interaction
\[
F_{\ell,c}=\mathcal N(V_c+Z_\ell)-\mathcal N(V_c)-\mathcal N(Z_\ell),
\qquad Z_\ell(r)=\sqrt\ell\,z(\ell r),
\]
the original radial half-line conjugation \(q=ru\), and the genuine smooth cutoff
\[
R_\ell=\ell^{-1/16}, \qquad
G_\ell(r)=r[1-\chi(r/R_\ell)]F_{\ell,c}(r).
\]
Here \(\chi=\mathrm{cutoff}\) is zero on \((-\infty,1]\) and one on \([2,\infty)\). For \(0<\ell\le1\), \(|c|\le1\), measurable \(z\), \(\|z(r)\|\le B\) for \(r>0\), and \(r\|z(r)\|\le A\) for \(r\ge1\), the two **actual forced** physical \(H_\pm\) affine resonance charges satisfy
\[
\begin{split}
\left|a_+(\Re G_\ell)\right|&\le
4K(B,A)J\,\ell^{1/16},\\
\left|a_-(\Im G_\ell)\right|&\le
2K(B,A)J\,\ell^{1/16},\\
J&=\int_0^\infty(1+r)^{-19/8}\,dr<\infty,
\end{split}
\]
with \(K(B,A)=\mathrm{actualHartreePhysicalWeightedSourceConstant}(B,A)\), the **already derived** original source constant. No source charge or decay is an additional hypothesis. The proof combines the strictly accepted raw unweighted Hartree source envelope, true radial cutoff multiplier bound \(|r\chi_{\rm in}|\le 2R_\ell\), exactly verified power identity \(R_\ell\ell^{1/8}=\ell^{1/16}\), actual channel resonance pairing integral, and the previously checked conjugated weighted source membership.

## Scope

This closes the important previous mismatch between the forced charges for raw \(F\) and those for the PDE-relevant *radially conjugated* \(r\chi_{\rm in}F\). It does **not** by itself imply small \(C^1\) boundary jets, existence of a global remote PDE solution, exact Kummer/remote interface compatibility, all other transport/parameter/Frobenius PDE residual bounds, positive order along physical time, or Type-II blowup. The exterior companion source \(r\chi_{\rm out}F\) and its weaker \(L^2\) membership are under separate strict CI.

Revised retained manuscript acceptance remains **11/13 (84.62%)** until the **entire** 2.13 physical finite-profile environment is proved. No count is increased for this auxiliary theorem.
