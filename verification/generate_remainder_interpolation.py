#!/usr/bin/env python3
"""Deterministic repairs of the pinned exact-rational source generator."""
from pathlib import Path
import subprocess

PIN = 'eec9538fab39cf3bf66ec49445bb65b5bc6eb004'

def main():
    code=subprocess.check_output(['git','show',PIN+':verification/generate_remainder_interpolation.py'],text=True)
    exec(compile(code,'pinned-rational-generator.py','exec'),{'__name__':'__main__'})
    path=Path('HBL/HartreeRemainderInterpolation.lean')
    src=path.read_text()
    replacements={
      '    Fin.sum_univ_succ]\n  push_cast\n  ring':
        '    Fin.sum_univ_succ]\n  ring',
      '    simpa only [Pi.smul_apply, smul_eq_mul] using hh.const_smul (s : ℂ)':
        '    apply (hh.const_smul (s : ℂ)).congr\n    filter_upwards with y\n    rfl',
      '    simpa only [Pi.smul_apply, smul_eq_mul] using hh.const_smul (t : ℂ)':
        '    apply (hh.const_smul (t : ℂ)).congr\n    filter_upwards with y\n    rfl',
      '    rw [integral_mul_const]\n    rfl':
        '    rw [integral_mul_const]\n    dsimp [hartreeNonlinearity, potential, C]\n    ring',
      '    have h := polynomial_remainder_identity':
        '    have hpoly := polynomial_remainder_identity',
      '    simp_rw [polynomial_is_actual] at h':
        '    simp_rw [polynomial_is_actual] at hpoly',
      '      norm_num [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow]':
        '''      have heven : |w y| ^ 4 = (w y) ^ 4 := by
        calc
          _ = (|w y| ^ 2) ^ 2 := by ring
          _ = ((w y) ^ 2) ^ 2 := by rw [sq_abs]
          _ = _ := by ring
      simpa only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_pow] using
        congrArg (fun z : ℝ => (z : ℂ)) heven''',
      '    simp only [densityLinear, cubicZero, cubicLinear] at *\n    push_cast at h ⊢':
        '    simp only [densityLinear, cubicZero, cubicLinear] at hpoly ⊢\n    push_cast at hpoly ⊢',
      '        rw [h, Finset.mul_sum, Finset.mul_sum]':
        '        rw [hpoly, Finset.mul_sum, Finset.mul_sum]',
    }
    for old,new in replacements.items():
        assert src.count(old)==1,(old,src.count(old))
        src=src.replace(old,new)
    path.write_text(src)

if __name__=='__main__': main()
