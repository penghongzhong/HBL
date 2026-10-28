#!/usr/bin/env python3
"""Reuse the audited validation driver, with an exact additional theorem inventory."""
from pathlib import Path

BASE = 'dfd259d57d5b3008d719f8617b3dd46bd08b2137'
TARGET = 'HartreeGradientDifference'
NAMES = ['quarticDensity_fderiv_difference', 'quartic_potential_first_order_difference']

def main():
    code = Path('verification/first_order_validation.py').read_text()
    changes = {
        "BASE = '53274ac98628f02ee0a69d36223c7677f663802c'": "BASE = '"+BASE+"'",
        "TARGET = 'HartreeFirstOrderSource'": "TARGET = '"+TARGET+"'",
        "NAMES = ['hartree_differential_noncompact', 'hartree_first_order_source_noncompact', 'hartree_weak_first_order_source']": 'NAMES = '+repr(NAMES),
        "groups[TARGET]=('HBL.RegularRadiation.FirstOrderSource.', NAMES)": "groups['HartreeFirstOrderSource']=('HBL.RegularRadiation.FirstOrderSource.', ['hartree_differential_noncompact', 'hartree_first_order_source_noncompact', 'hartree_weak_first_order_source'])\n            groups[TARGET]=('HBL.RegularRadiation.GradientDifference.', NAMES)",
        "'boundary': 'The complete nonlinearity and its first differential are proved L2, and the weak-derivative test identity is derived with all product integrability conditions discharged. The input is a C1 field in L4 and bounded, with L2 and bounded differential. No field L2, support or approximation hypothesis is introduced. Identification with higher Bessel Sobolev spaces, higher-order and Taylor-remainder difference estimates, and the actual constrained evolution remain separate obligations.'": "'boundary': 'Both actual quartic potentials and their actual Frechet differentials have linear difference bounds derived from C1/L4 fields, L2 derivatives, and bounded fields and derivatives; the difference and its differential have the displayed L2 and uniform bounds. Neither field is assumed L2 or compactly supported. Full nonlinear Taylor-remainder gradient differences, higher Sobolev closure and the actual constrained evolution are not concluded.'",
    }
    for before, after in changes.items():
        assert code.count(before)==1, before
        code=code.replace(before,after)
    code=code.replace('first-order-current-', 'gradient-difference-current-')
    code=code.replace('first-order-build.log', 'gradient-difference-build.log')
    Path('evidence').mkdir(exist_ok=True)
    Path('evidence/gradient-difference-expanded-driver.py').write_text(code)
    exec(compile(code, 'gradient-difference-expanded-driver.py', 'exec'), {'__name__':'__main__'})

if __name__=='__main__':
    main()
