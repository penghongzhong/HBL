#!/usr/bin/env python3
"""Reproduce the fixed rational proof and normalize its Bochner assembly."""
from pathlib import Path
import subprocess

PIN = 'e06f1137b580f72752f2b34c5f36b8b45fc478d7'

def main():
    code = subprocess.check_output(
        ['git', 'show', PIN + ':verification/generate_remainder_interpolation.py'], text=True)
    exec(compile(code, 'pinned-interpolation-repair.py', 'exec'), {'__name__': '__main__'})
    path = Path('HBL/HartreeRemainderInterpolation.lean')
    src = path.read_text()
    replacements = {
        '  have hint := integral_congr_ae (Filter.Eventually.of_forall hz)':
            '  have hint := integral_congr_ae (μ := (volume : Measure Space))\n    (Filter.Eventually.of_forall hz)',
        '''  rw [integral_sub ((hFi t).sub (hFi 0)) (hGi.const_mul (t : ℂ)),
    integral_sub (hFi t) (hFi 0), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun j _ => (hFi (j : ℕ)).const_mul (remainderWeight t j : ℂ))] at hint''':
            '''  have hsub := integral_sub ((hFi t).sub (hFi 0)) (hGi.const_mul (t : ℂ))
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_sub (hFi t) (hFi 0), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun (j : Fin 8) _ => (hFi (j : ℕ)).const_mul (remainderWeight t j : ℂ))] at hint''',
    }
    for old, new in replacements.items():
        assert src.count(old) == 1, (old, src.count(old))
        src = src.replace(old, new)
    path.write_text(src)

if __name__ == '__main__':
    main()
