#!/usr/bin/env python3
"""Archive one reviewed off-chain branch; leave every retained proof byte-identical."""
from pathlib import Path
import hashlib
import json
import subprocess
from proofchain_scan import BASE, mask_comments_and_strings

SOURCE = Path('HBL/WeightedArctanEnergyCore.lean')
ARCHIVE = Path('archive/proofchain-20261028/WeightedArctanEnergyCore.lean.txt')
NAMES = [
    'arctanEnergyPullback_hasDerivAt',
    'arctanEnergyPullback_energy_identity',
    'arctanEnergyPullback_dirichlet_energy',
]
REMOVALS = {
    Path('HBL.lean'): ['import HBL.WeightedArctanEnergyCore'],
    Path('HBL/Audit.lean'): ['#print axioms HBL.Modulation.Monopole.'+n for n in NAMES],
    Path('HBL/SpectralBridgeTypes.lean'): ['#check @HBL.Modulation.Monopole.'+n for n in NAMES],
}


def at_base(path: Path) -> bytes:
    return subprocess.check_output(['git', 'show', f'{BASE}:{path}'])


def main() -> None:
    original = at_base(SOURCE)
    assert SOURCE.read_bytes() == original, 'Candidate changed since the reviewed revision'
    names = ['arctanEnergyPullback', *NAMES]
    for path in [Path('HBL.lean'), *sorted(Path('HBL').rglob('*.lean'))]:
        if path == SOURCE: continue
        for line in mask_comments_and_strings(path.read_text()).splitlines():
            if 'HBL.WeightedArctanEnergyCore' in line or any(n in line for n in names):
                assert line.strip() in REMOVALS.get(path, []), (str(path), line)
    changed = []
    for path, removal_lines in REMOVALS.items():
        prior = at_base(path)
        assert path.read_bytes() == prior, f'Concurrent change in {path}'
        lines = prior.decode().splitlines(keepends=True)
        for line in removal_lines:
            assert sum(s.strip() == line for s in lines) == 1, (str(path), line)
        result = ''.join(s for s in lines if s.strip() not in removal_lines)
        path.write_text(result)
        changed.append({'path': str(path), 'removed_lines': removal_lines,
                        'before_sha256': hashlib.sha256(prior).hexdigest(),
                        'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    ARCHIVE.parent.mkdir(parents=True, exist_ok=True)
    ARCHIVE.write_bytes(original)
    SOURCE.unlink()
    for path in [Path('HBL.lean'), *sorted(Path('HBL').rglob('*.lean'))]:
        clean = mask_comments_and_strings(path.read_text())
        assert 'WeightedArctanEnergyCore' not in clean, str(path)
        assert not any(name in clean for name in names), str(path)
    report = {
        'base': BASE,
        'active_module_removed': str(SOURCE),
        'archive': str(ARCHIVE),
        'archive_byte_identical_to_base': ARCHIVE.read_bytes() == original,
        'removed_public_lean_theorems': NAMES,
        'removed_public_lean_definitions': ['arctanEnergyPullback'],
        'removed_mathematical_main_obligations': 0,
        'newly_verified_original_manuscript_environments': 0,
        'retained_proof_bodies_changed': 0,
        'modified_entrypoint_and_diagnostic_files': changed,
        'manuscript_source_modified_by_this_script': False,
        'note': 'Only imports and diagnostic commands are removed outside the archived module. Manuscript pruning is a separate guarded local script; no private paper is uploaded.'
    }
    out = Path('verification/proofchain-pruning-applied-20261028.json')
    out.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps(report, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
