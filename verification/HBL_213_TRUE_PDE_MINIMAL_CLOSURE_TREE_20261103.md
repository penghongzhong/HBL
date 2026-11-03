# HBL revised 2.13 — minimal true-Hartree-PDE closure tree (2026-11-03)

**Counting rule:** only 13 retained revised manuscript environments, with full scope, compiled Lean theorem statement and accepted dedicated CI, count as verified. All entries marked **auxiliary** do not increment the revised 11/13.

```text
ORIGINAL physical 3D inverse-square quartic Hartree PDE
│
├── Complete physical source identity: 4 genuine nonlocal Riesz products
│   SUCCESS (auxiliary): CI 41608607915
│   HBL.TypeIIDynamicSelection.actual_Hartree_one_radiation_full_nonlinear_source_gain
│
├── Real kernel / spatial estimates
│   ├── bubble² scalar Riesz: SUCCESS (auxiliary) 41600258796
│   ├── full mixed quartic Riesz O(sqrt(ell)/(1+r)):
│   │   SUCCESS (auxiliary) 41606060215
│   ├── actual moving-core Riesz O(1/(1+r)):
│   │   SUCCESS (auxiliary) 41610711049
│   └── pure-radiation Riesz O(ell/(1+ell*r)):
│       CANDIDATE (unaccepted); strict run 41616669571
│
├── Full same-source cubic nonlinear envelope
│   ├── three critical scalar Fredholm bounds: SUCCESS (auxiliary) 41611828903
│   ├── 4-product complex cubic 10-monomial norm:
│   │   CANDIDATE, run 41617242503
│   ├── actual PDE source -> actual 10-monomial Riesz envelope:
│   │   CANDIDATE, run 41617848319
│   ├── envelope monotonicity in physical |V|, |Z|, |P*|:
│   │   CANDIDATE, run 41618191854
│   └── ACTUAL fully composed weighted L² source with measurability
│       OPEN — must prove real 10-term coefficient reduction and
│       integrability of (1+r)^(-5/4) on the half-line
│
├── Original H+/H- inner Fredholm ↔ normalized Kummer ↔ remote solution
│   ├── exact origin-normalized Kummer source Green transfer:
│   │   SUCCESS (auxiliary) 41604443539
│   └── true physical C¹ interface compatibility / boundary mismatch smallness
│       OPEN — 2 Wronskian normalization constraints cannot be discarded
│
├── Complete same-PDE generated transport/cutoff/parameter/
│   Frobenius/slow-monopole residual, quantitative positive *time* order
│   OPEN — physical scale gain alone is not a dynamical s^-kappa law
│
└── One genuinely coupled three-region correction, uniform positive
    time gain, source-to-physical-profile packet and finite recursion
    OPEN — retained revised manuscript environment 2.13
    │
    └── Dynamical trapping + true PDE shooting, λ(t) blowup rate
        derived, not prescribed
        OPEN — final Type-II main theorem
```

Strict boundaries:
- Lean 4.35.0-rc3 and pinned Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5.
- No sorry, admit, new axiom, unsafe, guessed physical matching or assumed blowup exponent.
- The abstract `HBL.FiniteProfile.finiteProfile_recursion_certified` cannot replace a real physical packet constructor.
- No ratio increase from accepted auxiliary lemmas. Retained **11/13 (84.62%)**; unchanged original labels and historical counts separate.
