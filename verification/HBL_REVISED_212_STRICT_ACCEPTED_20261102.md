# HBL revised manuscript 2.12 — strict Lean acceptance, 2026-11-02

## Exact status and version boundaries

- **Revised 13-label manuscript**: **11/13 (84.62%)** formally accepted: previously revised 2.14 (strict Actions 41446185689) plus NOW revised 2.12 (strict Actions **41465373137**).
- **Unmodified 2026-11-01 13-label original**: **9/13**, unchanged. Its full original minimum-weight physical four-region cancellation is **NOT** proved by revised 2.12.
- Historic 21-environment ledger remains **9/21**, unchanged.
- Revised remaining main environments: **2.13** and **the Type-II dynamical-rate main theorem**, both OPEN. This is not a theorem of Hartree Type-II blowup.
- Manuscript Theorem/Proposition/Lemma labels and denominator remain unchanged at 13. The proven LOCAL Kummer/source result is mathematically separated out as revised 2.12. All former global 2.12 obligations plus actual finite profile, endpoint algebraic Kummer branch, and regional energy prerequisites remain explicitly part of revised 2.13. No unproved PDE claim is silently discarded.

## Exact audited Lean source

- Repo: `penghongzhong/HBL`
- Strict audited branch: `hbl-revised-212-local-source-20261102`
- Source commit **4aaeb115b98452a7b71577af422cf4024f9bf71b**
- Workflow run **41465373137**, `completed/success`, `strict-joint` success.
- Theorem: `HBL.TypeIIDynamicSelection.revised_one_layer_physical_local_source_certified`
- Source: `HBL/TypeIIDynamicSelection/RevisedOneLayerPhysicalLocalSource.lean`
- Audit: `HBL/TypeIIDynamicSelection/RevisedOneLayerPhysicalLocalSourceAudit.lean`
- Compiler: Lean **4.35.0-rc3**, pinned Mathlib **a98628e16c11f5167f16124105ddce53efa9bfe5**.
- Full build, `lake env lean --trust=0 -DwarningAsError=true` source/audit, exported `#check` and `#print axioms`. Only transitive kernel axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, `unsafe`, or new axiom in the audited declaration.
- Original audited source commit remains valid even if a subsequent workflow-only cache optimization commit changes the branch head.

## Exact mathematical content

A real high-regularity radial energy-critical 3D generalized-Hartree trajectory `z(t,r)` (under explicit local PDE, radial, dominated-moment, and positive-annulus source continuity premises) supplies the actual 3D inverse-square quartic moment
`m(t)=4*pi*integral_0^infty |z(t,r)|^4 dr`.
The positive selected terminal datum and genuine moment differentiation show eventual
`m(T)/2 < m(t) < 2*m(T)`.

For the actual physical clock `q=(T-time)/ell^2`, the exact identity
`ell*sqrt(q)=sqrt(T-time)` makes the Kummer-coordinate physical cutoff
`R_K=4/(kappa_H*m(t)*sqrt(T-time))` tend to infinity, independently of the unknown type-II concentration exponent.

The genuine complex physical residual `Fphys = Res(V+Z)-Res(V)` is pulled back via `R_bubble=sqrt(q)*z`. Its positive-annulus continuity is sufficient: define the globally continuous extension by clamping source arguments to the fixed annulus endpoints. No global continuity of the singular `2/r` radial operator at zero is assumed.

The previously **constructed** two-Wronskian-normalized local Kummer Green inverse `U` then satisfies the exact local frozen equation
`L_K(chi_RK U)=Fphys(sqrt(q)*z)` on every prescribed fixed positive Kummer annulus, eventually at renormalized time infinity. The genuinely common two Fredholm source channels are its real and imaginary physical-PDE projections. No prescribed blowup rate, surrogate cubic, independent abstract regional inverse, free homogeneous matching constants, or artificially assigned positive source orders are used.

**CRITICAL LIMITS**: The theorem is local to a fixed Kummer annulus and conditional on the visible regularity/PDE premises. It does not prove physical Hartree-to-Kummer operator conjugacy beyond the explicitly stated source pullback, full inner/remote `C^1` jet matching, nonlocal Riesz mixed source higher-order bounds, full generated-term positive-order gain, finite nonlinear profile recursion, or existence/selection of a Type-II blowup orbit. Those remain under revised 2.13 and the main theorem. The rate must ultimately be *derived* from the physical PDE and modulation system.

## Manuscript candidate provenance

Private synchronized Chinese TeX candidate `HBL_DynamicTypeII_Revised11of13_CANDIDATE_20261102.tex`, SHA-256
`b1cb0889b46896d53468e3bb0be494b03f14a454e1edbbd1bd51ea23c0357e73`.
This file is not uploaded to the public repository. Labels verified in the manuscript remain the same 13 original label strings.
