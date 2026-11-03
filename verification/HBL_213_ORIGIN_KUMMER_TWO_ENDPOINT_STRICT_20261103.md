# HBL 2.13: origin-normalized Kummer two-endpoint transfer — strict acceptance

- Source commit: `9b555ed9473d245140f588581c38fd7d041d38f0`.
- Strict GitHub Actions workflow: https://github.com/penghongzhong/HBL/actions/runs/41604443539 — completed/success; 3774 Lake build jobs.
- Compiler: Lean 4.35.0-rc3; pinned Mathlib a98628e16c11f5167f16124105ddce53efa9bfe5.
- Complete source: `HBL/TypeIIDynamicSelection/ActualHartreeOriginKummerEndpointTransfer.lean`.
- Audit: `HBL/TypeIIDynamicSelection/ActualHartreeOriginKummerEndpointTransferAudit.lean`.
- Strict checks: source/audit `lake env lean --trust=0 -DwarningAsError=true`, full type and `#print axioms`; only transitive `propext`, `Classical.choice`, `Quot.sound`, no added axiom, sorry, admit or unsafe.

Audited declarations:

1. `HBL.TypeIIDynamicSelection.actual_origin_Kummer_physical_Wronskian_ne_zero`.
2. `HBL.TypeIIDynamicSelection.actual_origin_Kummer_two_endpoint_center_Green_transfer`.

The second theorem identifies the **exact difference** between the already constructed physical origin-normalized, two-endpoint Kummer Green solution and the centered Cauchy Green solution. Both homogeneous endpoint coefficients are explicit integrals of the **same** source; none is arbitrarily assigned. The hypotheses include the necessary source interval-integrability assumptions.

**Boundary of acceptance:** no statement that the original physical inner and remote C1 traces satisfy the two outer transfer compatibility equations has been proved. The actual weighted full Hartree interaction, moving-region corrections and finite nonlinear profile are not closed by this scalar Green transfer alone. Thus revised 2.13 remains **OPEN**, the dynamical Type-II blowup main theorem remains **OPEN**, and the revised 13-environment acceptance remains **11/13**.
