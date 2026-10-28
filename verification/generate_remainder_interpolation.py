#!/usr/bin/env python3
"""Generate rational interpolation certificates; Lean ring checks every identity.
No numerical approximation or trusted external certificate is used.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def mul(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += a*b
    return out


def lit(x):
    return f'({x.numerator} / {x.denominator} : ℝ)'


def main():
    rows = []
    for j in range(8):
        p = [F(1)]
        for k in range(8):
            if k != j:
                p = mul(p, [F(-k, j-k), F(1, j-k)])
        assert len(p) == 8
        for k in range(8):
            assert sum(a * F(k)**i for i, a in enumerate(p)) == (1 if k == j else 0)
        rows.append(p[2:])
    bound = max(sum(abs(x) for x in row) for row in rows)
    B = bound.numerator // bound.denominator + 1
    matrix = '![' + ',\n    '.join('![' + ', '.join(map(lit, row)) + ']' for row in rows) + ']'
    src = r'''import HBL.HartreeDensitySourceBounds

/-!
# Exact degree-seven extraction of the physical Taylor remainder

The coefficients are rational Lagrange coefficients at 0,...,7 with the
constant and first-order coefficients removed. This file checks the exact
polynomial identity using ring, not a numerical interpolation assertion.
The weights are uniformly bounded on [0,1]. This allows previously proved
full-source difference estimates to be reused for the quadratic remainder.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace HBL.RegularRadiation.PhysicalInterpolation
open PhysicalExpansion

def interpolationCoefficients : Fin 8 → Fin 6 → ℝ :=
    MATRIX

def remainderWeight (t : ℝ) (j : Fin 8) : ℝ :=
  ∑ k : Fin 6, interpolationCoefficients j k * t ^ (k : ℕ)

def interpolationBound : ℝ := BOUND

/-- Exact uniform coefficient bound, checked over all eight rational rows. -/
theorem remainderWeight_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (j : Fin 8) :
    |remainderWeight t j| ≤ interpolationBound := by
  have hp (k : ℕ) : |t ^ k| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg ht _)]
    exact pow_le_one₀ ht ht1
  have hc : (∑ k : Fin 6, |interpolationCoefficients j k|) ≤ interpolationBound := by
    fin_cases j <;> norm_num [interpolationCoefficients, interpolationBound, Fin.sum_univ_succ]
  unfold remainderWeight
  calc
    _ ≤ ∑ k : Fin 6, |interpolationCoefficients j k * t ^ (k : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin 6, |interpolationCoefficients j k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hp k) (abs_nonneg _)
    _ ≤ _ := hc

private def integrandPolynomial (a c : ℝ) (b d : ℂ) (t : ℝ) : ℂ :=
  (((a ^ 2 + 2 * a * t * b.re + t ^ 2 * ‖b‖ ^ 2) ^ 2 : ℝ) : ℂ) *
    ((c ^ 2 + 2 * c * t * d.re + t ^ 2 * ‖d‖ ^ 2 : ℝ) : ℂ) *
    ((c : ℂ) + (t : ℂ) * d)

private theorem norm_sq_affine (a : ℝ) (b : ℂ) (t : ℝ) :
    ‖(a : ℂ) + (t : ℂ) * b‖ ^ 2 = a ^ 2 + 2 * a * t * b.re + t ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_sq_real_add]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem polynomial_is_actual (a c : ℝ) (b d : ℂ) (t : ℝ) :
    integrandPolynomial a c b d t =
      ((‖(a : ℂ) + (t : ℂ) * b‖ ^ 4 : ℝ) : ℂ) *
        (((‖(c : ℂ) + (t : ℂ) * d‖ ^ 2 : ℝ) : ℂ) * ((c : ℂ) + (t : ℂ) * d)) := by
  rw [show ‖(a : ℂ) + (t : ℂ) * b‖ ^ 4 =
    (‖(a : ℂ) + (t : ℂ) * b‖ ^ 2) ^ 2 by ring, norm_sq_affine, norm_sq_affine]
  unfold integrandPolynomial
  ring

set_option maxHeartbeats 2000000 in
private theorem polynomial_remainder_identity (a c : ℝ) (b d : ℂ) (t : ℝ) :
    integrandPolynomial a c b d t - (a : ℂ) ^ 4 * (c : ℂ) ^ 3 -
      (t : ℂ) * ((a : ℂ) ^ 4 * ((c : ℂ) ^ 2 * (2 * (d.re : ℂ) + d)) +
        (4 * (a : ℂ) ^ 3 * (b.re : ℂ)) * (c : ℂ) ^ 3) =
      (t : ℂ) ^ 2 * ∑ j : Fin 8, (remainderWeight t j : ℂ) *
        integrandPolynomial a c b d (j : ℕ) := by
  norm_num [integrandPolynomial, remainderWeight, interpolationCoefficients,
    Fin.sum_univ_succ]
  push_cast
  ring

/-- The actual affine physical field used for the eight source samples. -/
def sampleField (w : Space → ℝ) (h : Space → ℂ) (s : ℝ) : Space → ℂ :=
  fun x => (w x : ℂ) + (s : ℂ) * h x

/-- All sampled kernel integrals converge from the original field bounds. -/
theorem sample_kernel_integrable
    (w : Space → ℝ) (h : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ R) (s : ℝ) (x : Space) :
    Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * quarticDensity (sampleField w h s) y) := by
  have hs2 : MemLp (fun y => (s : ℂ) * h y) 2 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hh.const_smul (s : ℂ)
  have hsb : ∀ᵐ y, ‖(s : ℂ) * h y‖ ≤ |s| * R := by
    filter_upwards [hhb] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have he := physical_hartree_expansion_from_function_bounds 1 w
    (fun y => (s : ℂ) * h y) hw hw4 hs2 hM (mul_nonneg (abs_nonneg _) hR) hwb hsb x
  have hi := (he.1.add he.2.1).add he.2.2.1
  have eqf : (fun y : Space => (kernel (x - y) : ℂ) * quarticDensity (sampleField w h s) y) =
      (fun y => ((kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y +
        (kernel (x - y) : ℂ) * densityLinear w (fun v => (s : ℂ) * h v) y) +
        (kernel (x - y) : ℂ) * densityRemainder w (fun v => (s : ℂ) * h v) y) := by
    funext y
    unfold sampleField
    rw [quartic_density_split]
    ring
  rw [eqf]
  exact hi

private theorem linearTerm_scale (κ s : ℝ) (w : Space → ℝ) (h : Space → ℂ) (x : Space) :
    linearTerm κ w (fun y => (s : ℂ) * h y) x = (s : ℂ) * linearTerm κ w h x := by
  have hd : densityLinear w (fun y => (s : ℂ) * h y) =
      fun y => (s : ℂ) * densityLinear w h y := by
    funext y
    simp only [densityLinear, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    push_cast
    ring
  have hp : potential (densityLinear w (fun y => (s : ℂ) * h y)) x =
      (s : ℂ) * potential (densityLinear w h) x := by
    rw [hd]
    unfold potential
    simp_rw [show ∀ y, (kernel (x - y) : ℂ) * ((s : ℂ) * densityLinear w h y) =
      (s : ℂ) * ((kernel (x - y) : ℂ) * densityLinear w h y) from fun y => by ring]
    exact integral_const_mul _ _
  unfold linearTerm
  rw [hp]
  simp only [cubicLinear, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  push_cast
  ring

/-- Exact physical Taylor remainder as eight values of the EXISTING source.
No derivative of an abstract nonlinear map is assumed. All kernel integrability
obligations have been proved from L4/bounded background and L2/bounded increment. -/
theorem physical_remainder_interpolation
    (κ t : ℝ) (w : Space → ℝ) (h : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4)) (hh : MemLp h 2)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ R) (x : Space) :
    remainder κ w (fun y => (t : ℂ) * h y) x =
      (t : ℂ) ^ 2 * ∑ j : Fin 8, (remainderWeight t j : ℂ) *
        hartreeNonlinearity κ (sampleField w h (j : ℕ)) x := by
  let C : ℝ → ℂ := fun s =>
    ((‖sampleField w h s x‖ ^ 2 : ℝ) : ℂ) * sampleField w h s x
  let F : ℝ → Space → ℂ := fun s y =>
    ((kernel (x - y) : ℂ) * quarticDensity (sampleField w h s) y) * C s
  let G : Space → ℂ := fun y =>
    ((kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y) * cubicLinear (w x) (h x) +
    ((kernel (x - y) : ℂ) * densityLinear w h y) * cubicZero (w x)
  have hFi (s : ℝ) : Integrable (F s) :=
    (sample_kernel_integrable w h hw hw4 hh hM hR hwb hhb s x).mul_const (C s)
  have he := physical_hartree_expansion_from_function_bounds κ w h hw hw4 hh hM hR hwb hhb x
  have hGi : Integrable G :=
    (he.1.mul_const (cubicLinear (w x) (h x))).add (he.2.1.mul_const (cubicZero (w x)))
  have hfval (s : ℝ) : (κ : ℂ) * (∫ y, F s y) =
      hartreeNonlinearity κ (sampleField w h s) x := by
    dsimp [F]
    rw [integral_mul_const]
    rfl
  have hgval : (κ : ℂ) * (∫ y, G y) = linearTerm κ w h x := by
    dsimp [G]
    rw [integral_add (he.1.mul_const _) (he.2.1.mul_const _),
      integral_mul_const, integral_mul_const]
    rfl
  have hz (y : Space) : F t y - F 0 y - (t : ℂ) * G y =
      (t : ℂ) ^ 2 * ∑ j : Fin 8, (remainderWeight t j : ℂ) * F (j : ℕ) y := by
    have h := polynomial_remainder_identity (w y) (w x) (h y) (h x) t
    simp_rw [polynomial_is_actual] at h
    have h0 : ((‖(w y : ℂ)‖ ^ 4 : ℝ) : ℂ) = (w y : ℂ) ^ 4 := by
      norm_num [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow]
    have hc0 := cubic_base (w x)
    dsimp [F, G, C, sampleField, quarticDensity]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [h0, hc0]
    simp only [densityLinear, cubicZero, cubicLinear] at *
    push_cast at h ⊢
    rw [Finset.mul_sum]
    calc
      _ = (kernel (x - y) : ℂ) *
          (((‖(w y : ℂ) + (t : ℂ) * h y‖ ^ 4 : ℝ) : ℂ) *
            (((‖(w x : ℂ) + (t : ℂ) * h x‖ ^ 2 : ℝ) : ℂ) * ((w x : ℂ) + (t : ℂ) * h x)) -
            (w y : ℂ) ^ 4 * (w x : ℂ) ^ 3 - (t : ℂ) *
            ((w y : ℂ) ^ 4 * ((w x : ℂ) ^ 2 * (2 * ((h x).re : ℂ) + h x)) +
              (4 * (w y : ℂ) ^ 3 * ((h y).re : ℂ)) * (w x : ℂ) ^ 3)) := by ring
      _ = _ := by
        rw [h, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hint := integral_congr_ae (Filter.Eventually.of_forall hz)
  rw [integral_sub ((hFi t).sub (hFi 0)) (hGi.const_mul (t : ℂ)),
    integral_sub (hFi t) (hFi 0), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun j _ => (hFi (j : ℕ)).const_mul (remainderWeight t j : ℂ))] at hint
  simp_rw [integral_const_mul] at hint
  have hscaled : MemLp (fun y => (t : ℂ) * h y) 2 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hh.const_smul (t : ℂ)
  have hscaledb : ∀ᵐ y, ‖(t : ℂ) * h y‖ ≤ |t| * R := by
    filter_upwards [hhb] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have hex := (physical_hartree_expansion_from_function_bounds κ w
    (fun y => (t : ℂ) * h y) hw hw4 hscaled hM (mul_nonneg (abs_nonneg _) hR)
    hwb hscaledb x).2.2.2
  rw [linearTerm_scale] at hex
  have hmul := congrArg (fun z : ℂ => (κ : ℂ) * z) hint
  have hleft : (κ : ℂ) * ((∫ y, F t y) - (∫ y, F 0 y) - (t : ℂ) * ∫ y, G y) =
      remainder κ w (fun y => (t : ℂ) * h y) x := by
    calc
      _ = (κ : ℂ) * (∫ y, F t y) - (κ : ℂ) * (∫ y, F 0 y) -
          (t : ℂ) * ((κ : ℂ) * ∫ y, G y) := by ring
      _ = _ := by
        rw [hfval t, hfval 0, hgval]
        simpa only [sampleField, Complex.ofReal_zero, zero_mul, add_zero] using
          (show hartreeNonlinearity κ (fun y => (w y : ℂ) + (t : ℂ) * h y) x -
            hartreeNonlinearity κ (fun y => (w y : ℂ)) x - (t : ℂ) * linearTerm κ w h x =
            remainder κ w (fun y => (t : ℂ) * h y) x from by rw [hex]; ring)
  rw [hleft] at hmul
  rw [hmul]
  calc
    _ = (t : ℂ) ^ 2 * ∑ j : Fin 8,
        (remainderWeight t j : ℂ) * ((κ : ℂ) * ∫ y, F (j : ℕ) y) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp_rw [hfval]

end HBL.RegularRadiation.PhysicalInterpolation
'''
    src = src.replace('MATRIX', matrix).replace('BOUND', str(B))
    Path('HBL/HartreeRemainderInterpolation.lean').write_text(src)
    Path('evidence').mkdir(exist_ok=True)
    Path('evidence/interpolation-rationals.json').write_text(json.dumps({
        'nodes': list(range(8)), 'rows': [[str(x) for x in row] for row in rows],
        'weight_bound': B, 'arithmetic': 'exact fractions; independently checked by Lean ring'
    }, indent=2))

if __name__ == '__main__':
    main()
