# HBL revised 2.13: complete physical core–radiation interaction, weighted L2 — STRICT ACCEPTED

This records a completed **spatial nonlinear source theorem**, not acceptance of the whole retained finite-profile manuscript environment 2.13. It supersedes the pending status of the source synthesis in `HBL_213_COMPLETE_PHYSICAL_WEIGHTED_SOURCE_CANDIDATE_20261103.md`.

## Immutable verification

- Dedicated strict CI: https://github.com/penghongzhong/HBL/actions/runs/41635003260 — **completed/success**, all strict build and axiom-audit steps successful.
- Audited source commit: `6dcf989abf7842f5e0fd9561bf8ae01a175f7844`.
- Compiler: Lean **4.35.0-rc3**, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Mathlib: `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Full Lake build: **4044 jobs completed successfully**.
- Four source modules rechecked with `lake env lean --trust=0 -DwarningAsError=true`; no warnings or errors in those strict logs. The ten-monomial source has an informational tactic suggestion only.
- Six exported theorem declarations passed full `#check` and transitive `#print axioms`. Allowed dependencies only: `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, admitted proof, unsafe declaration, native_decide or new axiom.
- Evidence artifact: `13230038195`, `hbl-213-complete-physical-weighted-L2-audit`.
- Downloaded evidence ZIP independently hashed as **`3044a84be573b27d858d5083db817ee7a9617d2f7122cd6cd4656dac023cf41c`**, matching the GitHub artifact digest. Its commit, Mathlib commit, compiler version, theorem types and all four strict logs were inspected.

## Actual source and quantified inputs

`actualHartreePhysicalSliceInteraction ell c z` is the existing `actualOneLayerInteractionOnly` for the **actual** moving cutoff monopole

    V_c = monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c

and the critically rescaled physical radiation

    Z_ell(r) = sqrt(ell) * z(ell*r).

All original inverse-square radial Hartree potentials, pure/core/mixed quartic densities and complex cubic products are retained. The theorem does not replace the nonlocal PDE interaction with a local-cubic model.

Inputs of the final exported theorem are exactly:

    B,A >= 0; 0 < ell <= 1; |c| <= 1;
    Measurable z;
    forall u > 0, norm(z(u)) <= B;
    forall u >= 1, u * norm(z(u)) <= A.

There is **no hypothesis asserting a Riesz-potential bound, pointwise source decay, source-space membership, independent source measurability, matching data, or a prescribed blowup rate**. The relevant Riesz bounds, the actual source envelope and its measurability are derived.

`actualHartreePhysicalWeightedSourceConstant B A` is explicit and independent of ell,c,r. The fixed kernel constants and the physical amplitude/Strauss bounds B,A determine it.

## Complete accepted conclusion

For w(r)=(1+r^2)^(7/8), F=actualHartreePhysicalSliceInteraction ell c z and K=actualHartreePhysicalWeightedSourceConstant B A, Lean proves

    MemLp (r ↦ w(r) * norm(F(r))) 2 halfLineMeasure,

    integral_(0,infinity) (w(r)*norm(F(r)))^2 dr
      <= K^2 * ell^(1/4) * integral_(0,infinity) (1+r)^(-5/4) dr.

The last fixed integral is proved finite inside the argument. Thus the full source has weighted L2 size O_{B,A}(ell^(1/8)), not merely one component of it. The exported inequality retains the exact integral; this run does **not** claim that a separate Lean theorem evaluating that integral to 4 was checked.

Exported final theorem:

    HBL.TypeIIDynamicSelection.actual_Hartree_physical_full_interaction_weighted_L2

Supporting declarations audited in this same run:

    actualHartreePhysicalWeightedSourceConstant_nonneg
    actual_Hartree_all_ten_monomials_weighted_one_eighth_gain
    actual_Hartree_physical_full_interaction_weighted_pointwise
    actual_Hartree_physical_full_interaction_Japanese_pointwise
    actual_Hartree_physical_complete_interaction_measurable

## Source SHA-256

    2fa64b1d3583f61f572da33be10a409de345f4d610d3dd7710fc453a831ebbd7  ActualHartreeTenMonomialWeightedGain.lean
    08715d6a05a7772c06f459250be6df94d58b9e1c41a44c4d8f753c666679f0dd  ActualHartreePhysicalFullWeightedL2.lean
    55988d37b9492a15dde577e71bd96913bb0cf1e68fdc3266c9db29fa8932e771  ActualHartreePhysicalFullWeightedL2Audit.lean
    dec185788e133fd67c9fa372f53dd6d46fd1f63fcb5bda64a1d0117aa3cecb4e  ActualHartreePhysicalFullWeightedSource.lean
    ddd1d7ec74d93db4b7ff24e1ebbb83c71a23531723e9bd483bfdab91822ed38d  ActualHartreePhysicalInteractionMeasurable.lean

All files are under `HBL/TypeIIDynamicSelection/`.

## Acceptance boundary and manuscript accounting

This closes the baseline **core–radiation full nonlinear spatial weighted source estimate**. It does not close the full residual for an arbitrary iterated V_N. Still required are the actual coupled inner/Fredholm, normalized Kummer and remote correction, physical C1 interface compatibility, all iterated residual/cutoff/transport/parameter/Frobenius gains, parameter derivative/Lipschitz bounds, slow-Hessian remainder and physical regional energy estimates. The real physical source-to-profile realization is required before invoking the abstract finite recursion. Physical length smallness does not by itself supply a positive dynamical time order.

The chosen trajectory must supply the stated physical regularity inputs. The existence of a Type-II orbit and its concentration rate remain to be derived from the original PDE, not assumed.

**Retained revised manuscript acceptance remains 11/13 (84.62%).** Neither the final blowup theorem nor the whole manuscript 2.13 is counted as accepted by this spatial source result. Historical unchanged-original accounting is not modified.
