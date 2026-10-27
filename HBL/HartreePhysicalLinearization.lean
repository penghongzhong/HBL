import HBL.RegularRadiationKernel
import Mathlib.Tactic

/-!
# Exact expansion of the physical seventh-order Hartree nonlinearity

This file uses the actual inverse-square convolution from
`RegularRadiationKernel`, not an abstract nonlinear map. All uses of integral
additivity retain explicit integrability hypotheses. The expansion identifies
the real-linear term and the nonlinear remainder; it does not claim an
unbounded propagator, a contraction estimate, or the main blow-up theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
namespace HBL.RegularRadiation.PhysicalExpansion

/-- Squared modulus about an arbitrary real background. -/
theorem norm_sq_real_add (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) + z‖ ^ 2 = a ^ 2 + 2 * a * z.re + ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, zero_add]
  ring

def cubicZero (a : ℝ) : ℂ := (a : ℂ) ^ 3

def cubicLinear (a : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) ^ 2 * (2 * (z.re : ℂ) + z)

def cubicRemainder (a : ℝ) (z : ℂ) : ℂ :=
  (2 * (a : ℂ) * (z.re : ℂ)) * z +
    ((‖z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z)

/-- Exact cubic-factor expansion, with the full complex perturbation. -/
theorem cubic_split (a : ℝ) (z : ℂ) :
    ((‖(a : ℂ) + z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z) =
      cubicZero a + cubicLinear a z + cubicRemainder a z := by
  rw [norm_sq_real_add]
  unfold cubicZero cubicLinear cubicRemainder
  push_cast
  ring

theorem cubic_base (a : ℝ) :
    ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ) * (a : ℂ) = cubicZero a := by
  simpa [cubicLinear, cubicRemainder] using cubic_split a 0

def densityLinear (w : Space → ℝ) (h : Space → ℂ) (y : Space) : ℂ :=
  ((4 * (w y) ^ 3 * (h y).re : ℝ) : ℂ)

def densityRemainder (w : Space → ℝ) (h : Space → ℂ) (y : Space) : ℂ :=
  ((2 * (w y) ^ 2 * ‖h y‖ ^ 2 +
    (2 * w y * (h y).re + ‖h y‖ ^ 2) ^ 2 : ℝ) : ℂ)

/-- Exact quartic density expansion. The remainder begins at degree two. -/
theorem quartic_density_split (w : Space → ℝ) (h : Space → ℂ) (y : Space) :
    quarticDensity (fun x => (w x : ℂ) + h x) y =
      quarticDensity (fun x => (w x : ℂ)) y +
        densityLinear w h y + densityRemainder w h y := by
  have hbase : ‖(w y : ℂ)‖ ^ 2 = (w y) ^ 2 := by
    simpa using norm_sq_real_add (w y) 0
  have hfour :
      ‖(w y : ℂ) + h y‖ ^ 4 = ‖(w y : ℂ)‖ ^ 4 +
        4 * (w y) ^ 3 * (h y).re +
        (2 * (w y) ^ 2 * ‖h y‖ ^ 2 +
          (2 * w y * (h y).re + ‖h y‖ ^ 2) ^ 2) := by
    calc
      _ = (‖(w y : ℂ) + h y‖ ^ 2) ^ 2 := by ring
      _ = ((w y) ^ 2 + 2 * w y * (h y).re + ‖h y‖ ^ 2) ^ 2 := by
        rw [norm_sq_real_add]
      _ = _ := by
        rw [show ‖(w y : ℂ)‖ ^ 4 = (‖(w y : ℂ)‖ ^ 2) ^ 2 by ring, hbase]
        ring
  unfold quarticDensity densityLinear densityRemainder
  exact_mod_cast hfour

/-- Actual convolution expansion; all three integrability obligations are visible. -/
theorem potential_split (w : Space → ℝ) (h : Space → ℂ) (x : Space)
    (h0 : Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y))
    (h1 : Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * densityLinear w h y))
    (hR : Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * densityRemainder w h y)) :
    potential (quarticDensity (fun y => (w y : ℂ) + h y)) x =
      potential (quarticDensity (fun y => (w y : ℂ))) x +
        potential (densityLinear w h) x + potential (densityRemainder w h) x := by
  calc
    _ = ∫ y : Space,
        (((kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y) +
          (kernel (x - y) : ℂ) * densityLinear w h y) +
          (kernel (x - y) : ℂ) * densityRemainder w h y := by
      unfold potential
      apply integral_congr_ae
      filter_upwards with y
      rw [quartic_density_split]
      ring
    _ = (∫ y : Space, (kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y) +
        (∫ y : Space, (kernel (x - y) : ℂ) * densityLinear w h y) +
        (∫ y : Space, (kernel (x - y) : ℂ) * densityRemainder w h y) := by
      rw [integral_add (h0.add h1) hR, integral_add h0 h1]
    _ = _ := rfl

def linearTerm (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ) (x : Space) : ℂ :=
  (κ : ℂ) *
    (potential (quarticDensity (fun y => (w y : ℂ))) x * cubicLinear (w x) (h x) +
      potential (densityLinear w h) x * cubicZero (w x))

def remainder (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ) (x : Space) : ℂ :=
  (κ : ℂ) *
    (potential (quarticDensity (fun y => (w y : ℂ))) x * cubicRemainder (w x) (h x) +
      potential (densityLinear w h) x *
        (cubicLinear (w x) (h x) + cubicRemainder (w x) (h x)) +
      potential (densityRemainder w h) x *
        (cubicZero (w x) + cubicLinear (w x) (h x) + cubicRemainder (w x) (h x)))

/-- Exact identification with the physical seventh-order Hartree nonlinearity.
No differentiability, spectral evolution, or nonlinear estimate is assumed or concluded. -/
theorem physical_hartree_expansion (κ : ℝ) (w : Space → ℝ) (h : Space → ℂ) (x : Space)
    (h0 : Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * quarticDensity (fun v => (w v : ℂ)) y))
    (h1 : Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * densityLinear w h y))
    (hR : Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) * densityRemainder w h y)) :
    hartreeNonlinearity κ (fun y => (w y : ℂ) + h y) x =
      hartreeNonlinearity κ (fun y => (w y : ℂ)) x +
        linearTerm κ w h x + remainder κ w h x := by
  rw [hartreeNonlinearity, potential_split w h x h0 h1 hR]
  rw [cubic_split]
  rw [hartreeNonlinearity, cubic_base]
  unfold linearTerm remainder
  ring

#print axioms norm_sq_real_add
#print axioms cubic_split
#print axioms cubic_base
#print axioms quartic_density_split
#print axioms potential_split
#print axioms physical_hartree_expansion

end HBL.RegularRadiation.PhysicalExpansion
