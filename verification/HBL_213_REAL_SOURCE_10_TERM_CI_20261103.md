# HBL revised 2.13 — original physical nonlinear source: 10-term strict Lean chain

Acceptance basis: fixed Lean 4.35.0-rc3 + Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5; dedicated trust-zero full type/axiom audit. Separate *auxiliary* modules do not increase 13-label manuscript acceptance.

**Strictly accepted supporting proofs** on 2026-11-03:

- https://github.com/penghongzhong/HBL/actions/runs/41608607915 — one actual physical Hartree radiation, original complete 4-product quartic-Riesz×complex-cubic source identity and the core/mixed/pure PDE potential estimates.
- https://github.com/penghongzhong/HBL/actions/runs/41617242503 — all four complex cubic products bounded by ten nonnegative scalar monomials.
- https://github.com/penghongzhong/HBL/actions/runs/41617848319 — those ten monomials are the norm majorant of the **actual** nonlocal Hartree PDE interaction, not an abstract source.
- https://github.com/penghongzhong/HBL/actions/runs/41618191854 — the actual ten-monomial polynomial is monotone in three nonnegative Riesz-potential magnitudes and two field amplitudes.
- https://github.com/penghongzhong/HBL/actions/runs/41600258796 — original scalar radial bubble-squared Riesz logarithmic row bound.
- https://github.com/penghongzhong/HBL/actions/runs/41606060215 — full true mixed-quartic Riesz potential has O(sqrt(ell)/(1+r)) spatial decay.
- https://github.com/penghongzhong/HBL/actions/runs/41610711049 — original moving-core quartic Riesz potential has O(1/(1+r)) spatial decay.
- https://github.com/penghongzhong/HBL/actions/runs/41616669571 — original pure-radiation quartic Riesz potential has O(ell/(1+ell*r)) spatial decay.
- https://github.com/penghongzhong/HBL/actions/runs/41611828903 — all three limiting radial Fredholm powers \(A_j\) bounded by \(\ell^{1/8}(1+r)^{-5/8}\).

**Single dependency-tree integration:**
https://github.com/penghongzhong/HBL/actions/runs/41624948611
was submitted to check eight source/audit modules in one pinned Lean environment. Its final conclusion has not been verified as of this note. No successful conclusion is asserted.

**Mathematical next step**: apply the core/mixed/pure potential bounds and core/Strauss amplitude envelopes to the ten physical monomials, establish a genuine positive \(\ell^{1/8}\) bound in the original \(L^{2,7/4}(0,\infty)\) source space, using the original half-line measure and actual Riesz-integral measurability. The three critical *scalar* inequalities are already strict; the full ten-monomial weighted source specialization and L² integral are separately under verification.

**Still open**: the same original PDE source must enter and close physical H+/H−, normalized Kummer and remote-region \(C^1\) interfaces; all generated cutoff/transport/parameter/Frobenius terms must gain a genuine **time** order; the actual finite-profile packet must be constructed before abstract finite recursion is invoked. The blowup rate must be dynamically **derived**, not assumed.

**Retained revised manuscript accounting: 11/13 (84.62%)**, with original 2.13 and Type-II main theorem OPEN.
