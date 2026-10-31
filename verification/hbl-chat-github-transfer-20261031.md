# HBL Chat + GitHub continuity record — 2026-10-31

Repository: penghongzhong/HBL (public)
Active branch: hbl-typeii-minimal-main-20261029
Pinned Lean: 4.35.0-rc3
Pinned Mathlib: a98628e16c11f5167f16124105ddce53efa9bfe5

## Manuscript theorem status (strict, not auxiliary counts)
Historical **9 / 21** accepted original environments as recorded in
verification/original-environment-audit-20261028.json and
verification/typeii-minimal-revised-main-20261029.md.
No newly accepted original environment is claimed by this note.
The dynamical-rate-selection main PDE theorem is **OPEN**.

The corrected target is verification/typeii-minimal-main-replacement.tex:
derive the concentrating exponent from the *actual* Hartree modulation
dynamics, not a prescribed final rate. Do not resurrect the withdrawn
fixed-nu / fixed-mu-infinity candidate as a main result.

## GitHub corrections and current code work
1. 4c9ab9bcd72e02e1f65b160de6d8f58e14c65b74:
   Correct Lean coercion from `r ∈ Ioi 0` to `0 < r` and then `r ≠ 0`
   before clearing denominators in
   HBL/TypeIIDynamicSelection/ActualRadiation3DMoment.lean.
   Previous failing Actions run: 40962206240.
2. 9b01dbe70956e00f3c480f8dc69bd36dba903159:
   Add `actual_physical_threeD_radiation_slow_coefficient_hasDerivAt`,
   bridging the genuine 3D inverse-square whole-radiation moment to the
   physical-clock derivative of c_g, and add its type/axiom audit in
   ActualRadiation3DMomentAudit.lean.
   This is a conditional exact identity: actual radiation-moment
   differentiability remains a stated regular-flow input, and it does
   not assert existence of an exact blowup solution.
3. The strict GitHub Actions run for the second commit is
   https://github.com/penghongzhong/HBL/actions/runs/41177452875
   (pending at time of recording). The code changes must **not** be
   counted as compiled/accepted until this run passes.

## Shortest original proof-chain bottleneck
Next original theorem: `prop:one-layer-stage3` (old 2.12).
Verified components include genuine physical Hartree source projections,
actual affine-corrected +/- Fredholm inverses, Kummer/Green regional
constructions, and spatial center matching.
Missing: assemble those solutions into the complete *same* physical
three-region Hartree residual with cutoff commutators, generated-order
weighted estimates, parameter tangents and genuine two-channel source
cancellation. The existing `ActualRegionalBridge.lean` explicitly
disclaims complete closure.

After that: finite profile (2.13), global H1 matching (2.14),
common-domain constrained Hamiltonian flow and backward nonlinear
reconstruction, emergent positive mu-infinity from the true orbit,
and finite-time strong Type II PDE blowup main theorem.

## Counting and quality rules
No sorry, admit or added axiom. Real trust=0 compilation,
warning-as-error, exported type and transitive axiom inspection
(propext / Classical.choice / Quot.sound allowed), and exact manuscript
statement alignment before incrementing the original environment ledger.
Do not label conditional implication proofs as full PDE existence.

## 2026-10-31 continued strict proof progress

The earlier mixed-potential proof failed twice at Lean's elaboration of
`integral_add` on function-valued additions (not at a false analytic
identity). The final source normalizes `Pi.add_apply` before rewriting.

- Commit `475f78c8425fb13216d4594414a89c63c7fd81b3`:
  both exact whole-radiation mixed Hartree center and potential integral
  decompositions **strictly passed** run `41184068892`.
- Commit `52814b898353c38a3ae49ecdf91c18d862ef31b1`:
  `actual_whole_radiation_complete_Hartree_nonlinearity_difference`
  strictly passed run `41184369976`, together with revised CI checks
  of the new whole-radiation, original 3D moment and physical-clock
  declarations. The statement is the exact same-equation identity
  `N(V+Z)-N(V) = (P_Z+P_mix) C(V+Z) + P_V(C(V+Z)-C(V))`
  with `P_mix = I(|V+Z|^4-|V|^4-|Z|^4)` and genuine radial integral
  hypotheses. There is no artificial local Hartree term and no
  exterior-support assumption.

### Open original manuscript environment 2.12 — no increment to 9/21

These completed statements are physical source **components** and do
not certify the original `prop:one-layer-stage3`. The missing proof
must (1) instantiate each current-weight source in the actual three-region
parametrix, (2) control the full mixed bubble-radiation potential and
moving-cutoff commutators with the manuscript's precise time weights,
(3) derive the nontrivial parameter-tangent projection identity on the
same physical profile, (4) apply the actual normalized +/- Fredholm,
Kummer and remote solvers to remove the complete layer, and (5) derive
positive order `rho+kappa_prof` for **every** generated term.

The known 3D physical expansion at
`HBL/HartreePhysicalLinearization.lean` already proves
`HBL.RegularRadiation.PhysicalExpansion.physical_hartree_expansion`;
reuse it instead of building another abstract source package.

The dynamical rate must still be proved to **emerge** from a real Type II
Hartree orbit; it may not be fixed as an initial theorem parameter.

Strict historical original-paper ledger: **9/21**, main PDE theorem open.
