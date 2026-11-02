# HBL 2.12 — 外部权威定理适用范围审计（2026-11-02）

## 采用来源

A. K. Arora and S. Roudenko, **Well-posedness and blow-up properties for the generalized Hartree equation**, *Journal of Hyperbolic Differential Equations* **17** (2020), 727–763, DOI: **10.1142/S0219891620500228**. Original preprint: *On well-posedness and blow-up in the generalized Hartree equation*, arXiv:1910.01085.

**Theorem 1.1**: critical homogeneous Sobolev wellposedness and local Lipschitz dependence; **Theorem 3.1**: inhomogeneous critical Sobolev wellposedness. Their equation is

```math
  i u_t+\Delta u+(|x|^{-b}*|u|^p)|u|^{p-2}u=0,
  \qquad N=3,\quad b=2,\quad p=4.
```

The critical Sobolev exponent calculated from their exact scaling is

```math
 s_c=\frac{N}{2}-\frac{N-b+2}{2(p-1)}
 =\frac32-\frac{3}{6}=1.
```

The integer even exponent `p=4` satisfies their differentiability restriction. Hence the **critical local existence, uniqueness, and local Lipschitz solution dependence** may be treated as an explicitly cited external theorem. This matches the full 3D inverse-square quartic density and cubic factor, NOT the standard p=2 Hartree equation.

## Existing Lean interface

- `HBL/RegularRadiationFlow.lean`: `GeneralizedHartreeRegularLocalTheory κ`.
- `HBL/RegularRadiationOriginalEnvironment.lean`: `CitedHighRegularityHartreeLocalTheory κ` and `regularRadiationFlow_originalEnvironment_closed`.
- The Lean proof treats `LT : CitedHighRegularityHartreeLocalTheory κ` as a **theorem parameter**, not a new axiom. The current manuscript 2.10 uses this explicit literature-interface convention.
- `#print axioms` audits Lean dependencies; it does **not** certify the cited literature supplies each structure field. That correspondence requires this separate analytic ledger.

## Explicit boundaries NOT automatically covered by Theorem 1.1 or 3.1

1. Local persistence in arbitrarily high `H^L`, `C^1` parameter-dependence in the high-order norm, and uniform finite time jets must be cited under **their own** precise external regularity theorem or derived; critical `H^1` local wellposedness alone does not prove them.
2. Actual 3D radial Sobolev-to-pointwise `C^2` identification, positive-radius radial Laplacian, and dominated differentiation for the quartic moment require explicit Sobolev/radial equivalence and integrability estimates. They are not a free consequence of a generic local wellposedness theorem.
3. Uniform offterminal tail envelope `|z(t,r)|^4 <= D W(r)^2`, weighted `L^{2,σ}` full source bounds, and moving physical overlap/Kummer/Frobenius source-to-jet matching are **not** supplied by the cited LWP theorem. These must be proved for the actual single selected orbit, or be traced to distinct authoritative theorems with exact hypotheses.
4. The rate-selecting modulation trapping `ell(s) <= C s^(-β)` and the Type II rate must ultimately be derived from the physical PDE. A cited LWP theorem is not a replacement for rate-selection.
5. **Never** use manuscript original `prop:one-layer-stage3` itself, its entire minimum-weight cancellation, or an equivalent putative Hartree gluing result as an external premise. That would be circular and invalidate the original numerator.

## Hard acceptance criterion

The first original `9/13 -> 10/13` gain requires a Lean terminal that matches the **complete** manuscript 2.12 conclusion (canonical physical normalized correction, same-PDE source cancellation, every generated term of positive order); all non-cited analytical imports must be proven from the actual field. CI for isolated source estimates or conditional source membership is auxiliary only.

**Original accepted environments: 9/13; historical 9/21. This ledger changes neither count.**

## Lean foundational integration (2026-11-02)

- `HBL/Literature/AroraRoudenko2020Parameters.lean`: formal verification of the exact `N=3,b=2,p=4,s_c=1` specialization. This contains proved arithmetic, not an external axiom.
- `HBL/Literature/AroraRoudenko2020Interface.lean`: reusable conditional theorems over `LT : CitedHighRegularityHartreeLocalTheory κ`, including the actual physical Hartree equation, genuine Riesz kernel integrability, strong uniqueness and radiality.
- `HBL/RegularRadiationOriginalEnvironment.lean` now imports the parameter module, and `HBL.lean` exports the full literature interface for downstream use.
- `HBL/Literature/AroraRoudenko2020ParametersAudit.lean` and `AroraRoudenko2020InterfaceAudit.lean`: explicit exported type and transitive axiom audits.
- CI: `.github/workflows/hbl-literature-hartree-critical.yml`, pinned Lean 4.35.0-rc3 and Mathlib a98628e16, `--trust=0`, `-DwarningAsError=true`, no `sorry`, `admit`, `axiom`, or `unsafe`.

**Scope guarantee:** the published critical local theory is admissible as an EXTERNAL mathematical premise, but `CitedHighRegularityHartreeLocalTheory` also has higher Sobolev persistence, uniform finite jets, and `C^1` dependence fields. A valid Lean object of that type must still be supplied from separately justified analysis. Neither the paper citation nor this Lean interface constructs such an object. There is no unconditional proof of original HBL 2.12 or a predetermined Type-II rate.
