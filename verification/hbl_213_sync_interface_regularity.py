"""Append the audited interface note without rewriting historical manuscript text.

Run only after the dedicated two-declaration Lean audit.  This changes no
acceptance counts and does not certify the analytic source-space proof.
"""
from pathlib import Path
import os

ROOT = Path(__file__).resolve().parents[1]
MARK = 'HBL_INTERFACE_REGULARITY_GATE_20261111'
TARGETS = [
    'verification/HBL_213_GREEN_MOVING_TWO_CHANNEL_20261108.tex',
    'verification/HBL_213_SHORTEST_MAIN_CHAIN_CI_20261108.md',
    'verification/HBL_REVISED_213_MINIMAL_PHYSICAL_CLOSURE_TREE_20261102.md',
]
run = os.environ['GITHUB_RUN_ID']
sha = os.environ['GITHUB_SHA']
assert run.isdigit() and len(sha) == 40
snippet = (ROOT / 'verification/HBL_213_INTERFACE_REGULARITY_GATE_20261111.tex').read_text()
tex_path = ROOT / TARGETS[0]
old = tex_path.read_text()
if MARK not in old:
    assert old.count(r'\end{document}') == 1, 'Ambiguous TeX endpoint; no edits made'
    tex_path.write_text(old.replace(r'\end{document}', snippet + '\n' + r'\end{document}'))
entry = f'''\n\n## {MARK}: actual source regularity gate and finite third-jet repair\n\nOriginal revised acceptance remains **11/13**. The new paper proof in\n`verification/HBL_213_INTERFACE_REGULARITY_GATE_20261111.md` shows that a\nnonzero second-jet jump of a classical C1 matched physical Hartree field\nmakes its proposed Hessian--Morawetz-dual source norm infinite; temporal\nsmallness of a nonzero jump cannot cure this. C2 matching alone also does\nnot imply moving-interface H1-source Lipschitz continuity (an explicit\nsquare-root translation counterexample is given). These analytic results\nare paper proofs, not Lean certificates or a no-go for the main theorem.\n\nStrict auxiliary CI [{run}](https://github.com/penghongzhong/HBL/actions/runs/{run})\nat source commit `{sha}` checks ONLY the two precise declarations\n`actual_Hartree_physical_C3_repair_endpoint_jets` and\n`actual_Hartree_C3_repair_factored_kernels` in\n`HBL/TypeIIDynamicSelection/ActualHartreeInterfaceC3RepairPolynomial.lean`.\nThe workflow requires the pinned Lean 4.35.0-rc3 and Mathlib\n`a98628e16c11f5167f16124105ddce53efa9bfe5`, trust=0, warningAsError,\ncomplete #check output and per-declaration allowed-axiom audit. Only\npropext, Classical.choice and Quot.sound are permitted. The successful\nLean audit is restricted to the physical-width polynomial endpoint jets\nand the factored kernels. It does NOT prove the global repaired Hartree\nsource, actual jet decay, parameter Lipschitz bounds, original same-speed\ncompatibility after the nonlocal feedback, or a physical blowup orbit.\n\nThe original numbered environments remain **11/13**. No new original\nenvironment is accepted by the polynomial construction.\n'''
for rel in TARGETS[1:]:
    p = ROOT / rel
    text = p.read_text()
    if MARK not in text:
        p.write_text(text + entry)
print('Append-only manuscript/ledger synchronization complete; original count 11/13.')
for rel in TARGETS:
    print(rel)
