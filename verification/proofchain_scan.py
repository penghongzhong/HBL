#!/usr/bin/env python3
"""Read-only, pinned HBL dependency scan. Not a proof of the main PDE theorem."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = '9d1c825880f90f4efa31f6bd32d90c5ad591ea90'
CANDIDATE = 'HBL.WeightedArctanEnergyCore'
ROOTS = [
    'HBL.FirstModulationLemma', 'HBL.AffineTailLemmaClosed',
    'HBL.MonopoleFirstCorrectionCertified', 'HBL.MonopoleThresholdProjection',
    'HBL.KinematicSynchronizedSliceCertified', 'HBL.RegularRadiationFlow',
    'HBL.FiniteProfile', 'HBL.FiniteProfileResidualLedger', 'HBL.GlobalH1Matching',
    'HBL.PhysicalEnergySurjectivity', 'HBL.PhysicalL6Realization',
    'HBL.PhysicalWeakRadial', 'HBL.PhysicalVectorGradient',
    'HBL.PhysicalNonlocalForm', 'HBL.PhysicalPhaseHessian',
    'HBL.CompactTwoChannelCoercivity', 'HBL.ConstrainedCenterSpace',
    'HBL.DomainTriangularDynamics', 'HBL.ResidualTangentDerivative',
    'HBL.SlowFrameConnection', 'HBL.SpectralBridgeTypes',
    'HBL.ResidualDecayFromFiniteAtoms', 'HBL.ResidualDecayFromLipschitz',
    'HBL.RetainedThresholdBackward', 'HBL.RetainedFeedbackTail',
    'HBL.StableInitialPropagation', 'HBL.UnstableShootingTerminal',
    'HBL.WeightedJointBackward', 'HBL.WeightedAffineForcing',
    'HBL.WeightedStrongDynamics', 'HBL.WeightedTailIdentities',
    'HBL.LocalizedCenterNonlinearMap', 'HBL.HartreeFullDifferenceBounds',
    'HBL.ParametricFixedPointC1', 'HBL.TriangularReconstruction',
    'HBL.BlowupNonextension', 'HBL.MainRateSelection',
    'HBL.TransversalityExact', 'HBL.HartreeKernelShortRange'
]


def mask_comments_and_strings(text: str) -> str:
    """Preserve line positions while masking nested Lean comments and strings."""
    chars = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                chars[i:i+2] = [' ', ' ']; depth += 1; i += 2
            elif text.startswith('-/', i):
                chars[i:i+2] = [' ', ' ']; depth -= 1; i += 2
            else:
                if text[i] != '\n': chars[i] = ' '
                i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                chars[i] = ' '
                if text[i+1] != '\n': chars[i+1] = ' '
                i += 2
            else:
                if text[i] == '"': quoted = False
                if text[i] != '\n': chars[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            chars[i:i+2] = [' ', ' ']; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            chars[i:end] = [' '] * (end-i); i = end
        elif text[i] == '"':
            chars[i] = ' '; quoted = True; i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated Lean comment or string')
    return ''.join(chars)


def main() -> None:
    root = Path('.')
    paths = sorted(root.glob('HBL/**/*.lean'))
    modules = {'.'.join(p.with_suffix('').parts): p for p in paths}
    code = {m: mask_comments_and_strings(p.read_text()) for m, p in modules.items()}
    graph = {}
    for module, text in code.items():
        deps = []
        for line in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)', text, re.M):
            deps += re.findall(r'\bHBL(?:\.[A-Za-z_][A-Za-z0-9_]*)*\b', line)
        graph[module] = sorted(set(deps))
    missing_roots = sorted(set(ROOTS) - set(modules))
    assert not missing_roots, missing_roots
    unresolved_imports = sorted({d for ds in graph.values() for d in ds if d not in modules and d != 'HBL'})
    assert not unresolved_imports, unresolved_imports
    closure, todo = set(), list(ROOTS)
    while todo:
        name = todo.pop()
        if name in closure: continue
        closure.add(name)
        todo.extend(d for d in graph[name] if d in graph)
    production = {m for m in modules if not m.endswith('Audit') and m != 'HBL.Audit'}
    outside = sorted(production - closure)
    candidate_path = Path('HBL/WeightedArctanEnergyCore.lean')
    original = subprocess.check_output(['git', 'show', f'{BASE}:{candidate_path}'], text=True)
    candidate_code = mask_comments_and_strings(original)
    declarations = re.findall(r'^(?:def|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_\']*)', candidate_code, re.M)
    references = []
    for path in [Path('HBL.lean'), *paths]:
        if path == candidate_path: continue
        masked = mask_comments_and_strings(path.read_text())
        for number, line in enumerate(masked.splitlines(), 1):
            if CANDIDATE in line or any(re.search(r'(?<![A-Za-z0-9_\'])'+re.escape(n)+r'(?![A-Za-z0-9_\'])', line) for n in declarations):
                references.append({'path': str(path), 'line': number, 'code': line.strip()})
    report = {
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'review_base': BASE,
        'method': 'Exact-revision source import closure plus lexical named-declaration references; NOT Lean proof-term dependency extraction.',
        'main_theorem_closed': False,
        'main_theorem_root_exists': False,
        'main_proof_obligations_removed': 0,
        'manuscript_acceptance_percentage_recomputed': False,
        'protected_component_roots': ROOTS,
        'all_HBL_directory_lean_files': len(paths),
        'production_modules_excluding_audits': len(production),
        'protected_import_closure_count': len(closure),
        'outside_protected_closure_candidates_NOT_auto_deletable': outside,
        'candidate': {
            'module': CANDIDATE,
            'source_sha256_at_base': hashlib.sha256(original.encode()).hexdigest(),
            'declarations_at_base': declarations,
            'theorems_at_base': re.findall(r'^(?:theorem|lemma)\s+(\w+)', candidate_code, re.M),
            'in_protected_closure': CANDIDATE in closure,
            'direct_importers': sorted(m for m, ds in graph.items() if CANDIDATE in ds),
            'all_external_lexical_references': references,
        },
        'imports': graph,
        'warning': 'Disconnected current components are not necessarily irrelevant: final physical assembly and several analytic obligations are still missing. Archive only individually reviewed alternatives; preserve all five manuscript conclusions.'
    }
    Path('evidence').mkdir(exist_ok=True)
    Path('evidence/proofchain-import-audit.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    brief = {k: v for k, v in report.items() if k != 'imports'}
    print('HBL_DEPENDENCY_AUDIT_BEGIN')
    print(json.dumps(brief, ensure_ascii=False, indent=2))
    print('HBL_DEPENDENCY_AUDIT_END')

if __name__ == '__main__':
    main()
