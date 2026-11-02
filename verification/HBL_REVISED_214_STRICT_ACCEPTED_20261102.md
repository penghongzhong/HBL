# HBL retained 13-chain — revised 2.14 strict Lean acceptance (2026-11-02)

## Two separate, noninterchangeable numerical ledgers

- **Exact unchanged 2026-11-01 manuscript statements:** **9/13** accepted; `prop:global-H1-profile-v3` remains **OPEN** because genuine large-argument Kummer terminal extraction and actual Hartree three-region energy estimates are not proved.
- **Precisely revised 2026-11-02 13-environment manuscript:** **10/13** accepted (**76.92%**) after a theorem-boundary reorganization, **with the same 13 manuscript labels**. Revised 2.14 is the real-and-imaginary *physical radial homogeneous-energy gluing and convergence criterion* with explicit actual-region assumptions. **This must never be reported as unchanged-original 10/13.**
- Still-open revised original slots: **2.12**, **2.13** (now carries the genuine Hartree finite-profile, Kummer zero-time algebraic branch, three physical regional energy estimates, and actual error bound), and **main theorem** (genuine nonprescribed Type-II dynamical rate).
- No historical 21-item ledger figure is changed.

## Exact accepted theorem, not a generic abstract surrogate

Source: `HBL/ComplexGlobalH1PhysicalAssembly.lean`; audit: `HBL/ComplexGlobalH1PhysicalAssemblyAudit.lean`.

Exported Lean theorem:
`HBL.Profile.GlobalH1.physical_complex_three_region_H1_gluing_and_convergence`.

Its space `PhysicalComplexRadialEnergyPair = FullRadialEnergyL2 × FullRadialEnergyL2` is the **actual real/imaginary completed physical radial-gradient energy coordinate**, not a made-up regional inverse.

Inputs are the exact physical complex profile decomposition `hSplit`, positive regional exponents `hmIn, hmK, hmRem` and actual energy bounds `hIn, hK, hRem`, plus a genuine error estimate `hErr` and positive error exponent `hM`. All these unproved *actual Hartree profile* obligations must be delivered by original 2.13 and are **NOT** cited literature facts.

Lean then constructs a common strictly positive exponent, proves the global positive-energy bound with error, obtains the **actual 3D physical gradient identity for both channels**, and proves `Tendsto ... atTop (𝓝 0)`. No Type-II rate is assumed.

## Strict reproducible CI

- Source commit: [`83d41e7ad6887519afa67020a6286570e2d58122`](https://github.com/penghongzhong/HBL/commit/83d41e7ad6887519afa67020a6286570e2d58122).
- CI: [`41446185689`](https://github.com/penghongzhong/HBL/actions/runs/41446185689) **completed SUCCESS**.
- Compiler Lean **4.35.0-rc3** and pinned Mathlib **a98628e16c11f5167f16124105ddce53efa9bfe5**, full lake build; `lean --trust=0 -DwarningAsError=true`; full exported `#check` and `#print axioms`.
- The checked theorem has only `propext, Classical.choice, Quot.sound` as transitive logical dependencies; no `sorryAx`, `sorry`, `admit`, `unsafe`, or new axiom in the added theorem source.
- The related real single-channel gluing CI [`41444924209`](https://github.com/penghongzhong/HBL/actions/runs/41444924209) **SUCCESS**; genuine Kummer shell commutator CI [`41446006169`](https://github.com/penghongzhong/HBL/actions/runs/41446006169) **SUCCESS**. Neither is counted as an extra original environment.

## Privacy and strict scope

The full private Chinese TeX manuscript is retained outside the public repository, with **all 13 original labels unchanged** and the exact 2.13/2.14 division of obligations explicitly revised. This verification note does **not** upload the private TeX/PDF. Original 2.12, original unrevised 2.14, and the full Type-II blowup theorem remain open. A verified revised gluing criterion does not certify the pending Hartree–Kummer analytic estimates or a prescribed blowup rate.
