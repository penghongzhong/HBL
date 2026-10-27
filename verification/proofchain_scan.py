#!/usr/bin/env python3
"""Pinned source-level dependency scan, not kernel proof-term extraction."""
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
    'HBL.KinematicSynchronizedSliceCertified', 'HBL.KinematicPhysicalDynamics',
    'HBL.KinematicPhaseDynamics', 'HBL.KinematicPhysicalTimeInverseDeriv',
    'HBL.RadialHartreeAmplitudeCenter', 'HBL.RadialHartreeCenter', 'HBL.RadialHartreeMultipole',
    'HBL.RegularRadiationFlow', 'HBL.FiniteProfile', 'HBL.FiniteProfileResidualLedger',
    'HBL.GlobalH1Matching', 'HBL.PhysicalEnergySurjectivity', 'HBL.PhysicalL6Realization',
    'HBL.PhysicalWeakRadial', 'HBL.PhysicalVectorGradient', 'HBL.PhysicalNonlocalForm',
    'HBL.PhysicalPhaseHessian', 'HBL.CompactTwoChannelCoercivity',
    'HBL.ConstrainedCenterSpace', 'HBL.DomainTriangularDynamics',
    'HBL.ResidualTangentDerivative', 'HBL.SlowFrameConnection',
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
    if depth or quoted: raise ValueError('Unterminated Lean comment or string')
    return ''.join(chars)


def main() -> None:
    paths = [Path('HBL.lean'), *sorted(Path('HBL').rglob('*.lean'))]
    modules = {'.'.join(p.with_suffix('').parts): p for p in paths}
    code = {m: mask_comments_and_strings(p.read_text()) for m, p in modules.items()}
    graph = {}
    for module, text in code.items():
        deps = []
        for line in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)', text, re.M):
            deps += re.findall(r'\bHBL(?:\.[A-Za-z_][A-Za-z0-9_]*)*\b', line)
        graph[module] = sorted(set(deps))
    assert not (set(ROOTS)-set(modules)), sorted(set(ROOTS)-set(modules))
    missing = sorted({d for ds in graph.values() for d in ds if d not in modules})
    assert not missing, missing
    closure, todo = set(), list(ROOTS)
    while todo:
        name = todo.pop()
        if name in closure: continue
        closure.add(name); todo.extend(graph[name])
    diagnostics = {m for m in modules if m.endswith('Audit') or m == 'HBL.SpectralBridgeTypes'}
    production = set(modules) - diagnostics - {'HBL'}
    assert 'HBL.SpectralBridgeTypes' not in ROOTS
    candidate_path = Path('HBL/WeightedArctanEnergyCore.lean')
    original = subprocess.check_output(['git', 'show', f'{BASE}:{candidate_path}'], text=True)
    candidate_code = mask_comments_and_strings(original)
    declarations = re.findall(r'^(?:def|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_\']*)', candidate_code, re.M)
    references = []
    for module, path in modules.items():
        if module == CANDIDATE: continue
        for number, line in enumerate(code[module].splitlines(), 1):
            if CANDIDATE in line or any(re.search(r'(?<![A-Za-z0-9_\'])'+re.escape(n)+r'(?![A-Za-z0-9_\'])', line) for n in declarations):
                references.append({'path': str(path), 'line': number, 'code': line.strip()})
    report = {
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'review_base': BASE,
        'method': 'Source import closure (including HBL umbrella transitively) plus lexical declaration references; NOT kernel proof-term dependency extraction.',
        'complete_main_PDE_root_constructed_in_this_audit': False,
        'main_theorem_closed': False,
        'main_proof_obligations_removed': 0,
        'manuscript_acceptance_percentage_recomputed': False,
        'protected_component_roots': ROOTS,
        'all_HBL_directory_lean_files': len(paths)-1,
        'production_modules_excluding_named_diagnostics': len(production),
        'protected_import_closure_count': len(closure),
        'umbrella_in_protected_closure': 'HBL' in closure,
        'outside_protected_closure_NOT_auto_deletable': sorted(production-closure),
        'candidate': {
            'module': CANDIDATE,
            'active_source_exists': candidate_path.exists(),
            'source_sha256_at_base': hashlib.sha256(original.encode()).hexdigest(),
            'declarations_at_base': declarations,
            'theorems_at_base': re.findall(r'^(?:theorem|lemma)\s+(\w+)', candidate_code, re.M),
            'in_protected_closure': CANDIDATE in closure,
            'direct_importers_including_umbrella': sorted(m for m, ds in graph.items() if CANDIDATE in ds),
            'all_external_lexical_references': references,
        },
        'imports': graph,
        'warning': 'Disconnected modules are not automatically irrelevant. The final physical assembly and several analytic obligations remain open; all five manuscript conclusions are protected.'
    }
    Path('evidence').mkdir(exist_ok=True)
    Path('evidence/proofchain-import-audit.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'imports'}, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
