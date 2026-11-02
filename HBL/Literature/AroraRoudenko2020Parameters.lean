import Mathlib.Tactic

/-!
# Arora--Roudenko (2020): published 3D energy-critical Hartree parameters

Reference: A. K. Arora and S. Roudenko,
"Well-posedness and blow-up properties for the generalized Hartree
equation", J. Hyperbolic Differential Equations 17 (2020), 727--763.
DOI 10.1142/S0219891620500228; original preprint arXiv:1910.01085.

The published generalized Hartree model is
  i u_t + Delta u + (|x|^(-b) * |u|^p)|u|^(p-2) u = 0.
Here we specialize N=3, b=2, p=4. Its critical scaling index is
  s_c = N/2 - (N-b+2)/(2*(p-1)) = 1.

This file contains the EXACT parameter specialization and simple arithmetic
only. It adds NO axiom, opaque constant, existence witness, or postulated
blow-up law. The external local well-posedness result itself remains an
explicitly supplied published-theorem input in the higher interface.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Literature.AroraRoudenko2020

def dimension : ℕ := 3

def rieszExponent : ℕ := 2

def hartreePower : ℕ := 4

/-- Scaling-critical Sobolev index for the 3D inverse-square p=4
generalized Hartree equation studied in the cited reference. -/
def criticalSobolevIndex : ℝ :=
  (dimension : ℝ) / 2 -
    ((dimension : ℝ) - (rieszExponent : ℝ) + 2) /
      (2 * ((hartreePower : ℝ) - 1))

theorem criticalSobolevIndex_eq_one :
    criticalSobolevIndex = 1 := by
  norm_num [criticalSobolevIndex, dimension, rieszExponent, hartreePower]

theorem exponent_parameters_are_admissible :
    0 < (rieszExponent : ℝ) ∧
    (rieszExponent : ℝ) < (dimension : ℝ) ∧
    2 ≤ (hartreePower : ℝ) := by
  norm_num [dimension, rieszExponent, hartreePower]

/-- The local polynomial factor is |u|^2*u and the convolution
density is |u|^4, not |u|^2*u or the cubic Hartree model. -/
theorem local_power_reduction :
    (hartreePower : ℝ) - 2 = 2 := by
  norm_num [hartreePower]

end HBL.Literature.AroraRoudenko2020
