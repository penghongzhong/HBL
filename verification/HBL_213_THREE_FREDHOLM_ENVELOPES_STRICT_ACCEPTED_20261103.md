# HBL revised 2.13 — three scalar Fredholm envelopes, STRICT Lean acceptance

- The audited source commit is `474c1d20456089592343e9047ca73dbd5533bccd`.
- GitHub Actions **41611828903 completed/success**:
  https://github.com/penghongzhong/HBL/actions/runs/41611828903
- Lean 4.35.0-rc3, pinned Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5.
- 3118 Lake build tasks completed; the module and independent audit were checked with `--trust=0 -DwarningAsError=true`.
- The source and audit files are `HBL/TypeIIDynamicSelection/ActualHartreeThreeFredholmEnvelopes.lean` and `ActualHartreeThreeFredholmEnvelopesAudit.lean`.
- Audited theorem: `HBL.TypeIIDynamicSelection.actual_Hartree_three_Fredholm_scalar_envelopes`.
- `#check`, `#print axioms` and the scripted transitive axiom audit succeeded; only `propext`, `Classical.choice`, `Quot.sound` occur. No `sorry`, `admit`, `unsafe`, `native_decide` or added axiom.

For `d=1+r`, `q=1+ell*r`, `0<ell<=1`, `r>=0`, the exact three inequalities checked by Lean are:
```math
\begin{aligned}
  A_1&=\ell^{1/2}d^{-5/4}q^{-1},\\
  A_2&=\ell d^{-1/4}q^{-2},\\
  A_3&=\ell^{3/2}d^{3/4}q^{-3},\\
  \max(A_1,A_2,A_3)&\le\ell^{1/8}d^{-5/8}.
\end{aligned}
```

The companion mathematical ten-term physical Hartree source coefficient ledger is
`verification/HBL_213_EXACT_FOUR_TERM_WEIGHTED_SOURCE_LEDGER_20261103.md`.
The SymPy algebra audit is `verification/hbl_213_ten_term_sympy_audit.py`, which checks all ten monomial coefficients and that each residual domination factor is either `1`, `sqrt(ell)`, or `q/d`.

**Acceptance boundary:** This strict Lean result is a scalar source-weight lemma, not a proof that the full physical Hartree interaction has the claimed weighted \(L^2\) norm. Actual core/pure Riesz spatial tails, the physical-to-scalar combination, the integral, synchronized inner/Kummer/remote \(C^1\) matching, generated time-order gains, the finite nonlinear recursion, and the emergent Type-II PDE rate remain distinct obligations. The revised numbered manuscript count remains **11/13**.
