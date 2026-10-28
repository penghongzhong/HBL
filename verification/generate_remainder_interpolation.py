#!/usr/bin/env python3
"""Deterministic elaboration repairs of the pinned rational Lean generator."""
from pathlib import Path
import subprocess

PIN = 'eec9538fab39cf3bf66ec49445bb65b5bc6eb004'

def main():
    code = subprocess.check_output(
        ['git', 'show', PIN + ':verification/generate_remainder_interpolation.py'], text=True)
    exec(compile(code, 'pinned-rational-generator.py', 'exec'), {'__name__': '__main__'})
    path = Path('HBL/HartreeRemainderInterpolation.lean')
    src = path.read_text()
    replacements = {
        '    Fin.sum_univ_succ]\n  push_cast\n  ring':
            '    Fin.sum_univ_succ]\n  ring',
        '    simpa only [Pi.smul_apply, smul_eq_mul] using hh.const_smul (s : ℂ)':
            '''    have heq : (fun y => (s : ℂ) * h y) = (s : ℂ) • h := by
      funext y
      rfl
    rw [heq]
    exact hh.const_smul (s : ℂ)''',
        '    simpa only [Pi.smul_apply, smul_eq_mul] using hh.const_smul (t : ℂ)':
            '''    have heq : (fun y => (t : ℂ) * h y) = (t : ℂ) • h := by
      funext y
      rfl
    rw [heq]
    exact hh.const_smul (t : ℂ)''',
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
        '    simp only [Complex.ofReal_zero, zero_mul, add_zero]\n    rw [h0, hc0]':
            '    simp only [zero_mul, add_zero]\n    rw [h0, hc0]',
        '    simp only [densityLinear, cubicZero, cubicLinear] at *\n    push_cast at h ⊢':
            '    simp only [densityLinear, cubicZero, cubicLinear] at hpoly ⊢\n    push_cast at hpoly ⊢',
        '              (4 * (w y : ℂ) ^ 3 * ((h y).re : ℂ)) * (w x : ℂ) ^ 3)) := by ring':
            '              (4 * (w y : ℂ) ^ 3 * ((h y).re : ℂ)) * (w x : ℂ) ^ 3)) := by\n        push_cast\n        ring',
        '        rw [h, Finset.mul_sum, Finset.mul_sum]':
            '        push_cast\n        rw [hpoly, Finset.mul_sum, Finset.mul_sum]',
    }
    for old, new in replacements.items():
        assert src.count(old) == 1, (old, src.count(old))
        src = src.replace(old, new)
    path.write_text(src)

if __name__ == '__main__':
    main()
