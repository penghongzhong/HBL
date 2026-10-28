#!/usr/bin/env python3
"""Reuse the pinned validation driver with the exact expanded assembly inventory."""
from pathlib import Path
import subprocess

DRIVER_COMMIT = 'cf4ae7fae69a28dfaa32ac68483bf2a9bfeeef1e'
LOCALIZED = [
    'radialClip', 'radialClip_eq_of_norm_le', 'radialClip_norm_le',
    'radialClip_difference_le', 'radialClip_continuous',
    'lateRadius', 'lateRadius_pos', 'lateRadius_continuous',
    'localizedCenterNonlinearity', 'LocalCenterLipschitz',
    'localizedCenter_continuous', 'localizedCenter_zero', 'localizedCenter_global_bound',
    'localizedCenter_agrees_on_path', 'localizedCenter_tail_eq',
    'localizedCenterMap', 'localizedCenterMap_norm_le',
    'localizedCenterMap_difference_norm', 'localizedCenterMap_apply',
    'affine_fixedPoint_ball', 'localizedCenter_solution',
]


def main():
    code = subprocess.check_output([
        'git', 'show', DRIVER_COMMIT + ':verification/selected_graph_validation.py'
    ], text=True)
    changes = {
        "'selected_local_fixedPoint_contDiffAt', 'selected_fixedPoint_shooting_data_rate_C1']),":
            "'selected_local_fixedPoint_contDiffAt', 'selected_fixedPoint_shooting_data_rate_C1', 'construct_local_fixedPoint_C1_family']),",
        "def main():":
            "GROUPS['LocalizedCenterNonlinearMap'] = ('HBL.MainBackward.Localized.', " + repr(LOCALIZED) + ")\n\ndef main():",
        "report['new_public_calculus_terminals'] = 2":
            "report['new_public_calculus_terminals'] = 3",
        "'existing selected solution family: no second fixed-point construction'":
            "'LocalizedCenterNonlinearMap.affine_fixedPoint_ball: construct the selected family with a strict interior margin'",
    }
    for before, after in changes.items():
        assert code.count(before) == 1, before
        code = code.replace(before, after)
    Path('evidence').mkdir(exist_ok=True)
    Path('evidence/selected-graph-expanded-driver.py').write_text(code)
    exec(compile(code, 'selected-graph-expanded-driver.py', 'exec'), {'__name__': '__main__'})

if __name__ == '__main__':
    main()
