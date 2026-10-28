#!/usr/bin/env python3
"""Reuse the pinned strict validator for the exact physical interpolation target."""
from pathlib import Path
import subprocess

BASE = '4dbc0a1171189f73cd3335a983f9a0b618a34eb4'
NAMES = ['interpolationCoefficients', 'remainderWeight', 'interpolationBound',
         'remainderWeight_bound', 'sampleField', 'sample_kernel_integrable',
         'physical_remainder_interpolation']

def main():
    code = subprocess.check_output(['git','show', BASE+':verification/density_remainder_gradient_validation.py'], text=True)
    start=code.index('GROUPS = {')
    stop=code.index('\n}\n',start)+3
    groups={'HartreeRemainderInterpolation':('HBL.RegularRadiation.PhysicalInterpolation.',NAMES)}
    code=code[:start]+'GROUPS = '+repr(groups)+'\n'+code[stop:]
    before="BASE = 'c7e0e3458f8adffd764e5793b591f2f32c6afd16'"
    assert code.count(before)==1
    code=code.replace(before,'BASE = '+repr(BASE))
    code=code.replace("TARGET = 'HartreeDensityRemainderGradient'", "TARGET = 'HartreeRemainderInterpolation'")
    code=code.replace('density-remainder-gradient','remainder-interpolation')
    code=code.replace("report['new_public_theorems']=5", "report['new_public_theorems']=3")
    old="Native spatial differentiation of the actual quadratic quartic-density remainder. Its gradient mass and supremum, and the actual noncompact gradient potential, are O(r^2) on the mixed first-order perturbation ball. Real background C1/bounded/bounded derivative; no background L2 or L4. This is not the full seventh-order remainder difference, high Sobolev closure, actual constrained evolution or main blow-up theorem."
    new="Exact physical seventh-order Taylor remainder as t^2 times eight actual nonlinear source samples. Coefficients and identities are checked by Lean, and kernel integrability is derived from the original field bounds. This reduces differentiated remainder estimates to previously proved whole-source estimates, but does not by itself instantiate every Sobolev sample bound or construct the constrained evolution. No original manuscript environment is newly accepted."
    assert old in code
    code=code.replace(old,new)
    Path('evidence').mkdir(exist_ok=True)
    Path('evidence/interpolation-expanded-validator.py').write_text(code)
    exec(compile(code,'interpolation-expanded-validator.py','exec'), {'__name__':'__main__'})

if __name__ == '__main__': main()
