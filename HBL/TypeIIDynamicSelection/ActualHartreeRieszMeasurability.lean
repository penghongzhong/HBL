import HBL.TypeIIDynamicSelection.ActualHartreeFullCutoffSupport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Measurability of the FULL actual inverse-square radial Hartree Riesz map

Unlike a hypothesis about an abstract region solver, this proves
measurability of the physical potential and of the actual nonlinear
cutoff commutator for every measurable complex radiation.

The proof uses the original logarithmic radial Riesz kernel, and
measurability of Lebesgue integrals in the observation radius.
Pointwise integrability is covered separately by the existing
physical quartic envelope estimates. No axiom is introduced.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Modulation

/-- The original radial inverse-square quartic Riesz convolution
is a measurable function of the observation radius. -/
theorem actual_radialHartreePotential_measurable
    (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (radialHartreePotential F) := by
  have hJoint : Measurable (fun p : ℝ × ℝ =>
      p.2 * hartreeRadialLog p.1 p.2 * F p.2) := by
    unfold hartreeRadialLog
    fun_prop
  have hInt : StronglyMeasurable (fun r : ℝ =>
      ∫ rho in Ioi (0 : ℝ), rho * hartreeRadialLog r rho * F rho) := by
    have hUncurry : StronglyMeasurable
        (Function.uncurry (fun r rho : ℝ =>
          rho * hartreeRadialLog r rho * F rho)) := by
      change StronglyMeasurable (fun p : ℝ × ℝ =>
        p.2 * hartreeRadialLog p.1 p.2 * F p.2)
      exact hJoint.stronglyMeasurable
    exact hUncurry.integral_prod_right
  unfold radialHartreePotential
  exact (measurable_const.div measurable_id).mul hInt.measurable

/-- Measurability of the actual nonlinear Hartree operator, including
its full quartic nonlocal density and exact local cubic factor. -/
theorem actual_complexRadialHartreeNonlinearity_measurable
    (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (complexRadialHartreeNonlinearity f) := by
  have hp := actual_radialHartreePotential_measurable
    (fun rho => ‖f rho‖ ^ 4) (hf.norm.pow_const 4)
  have hpC : Measurable
      (fun r : ℝ =>
        (radialHartreePotential (fun rho => ‖f rho‖ ^ 4) r : ℂ)) :=
    Complex.measurable_ofReal.comp hp
  have hSqC : Measurable
      (fun r : ℝ => ((‖f r‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (hf.norm.pow_const 2)
  unfold complexRadialHartreeNonlinearity
  exact (hpC.mul hSqC).mul hf

/-- The complete Hartree nonlocal cutoff commutator is itself
measurable, without introducing a new analytic measurability input. -/
theorem actual_Hartree_nonlocal_cutoff_error_measurable
    (R ell : ℝ) (z : ℝ → ℂ) (hz : Measurable z) :
    Measurable (actualHartreeNonlocalCutoffError R ell z) := by
  have hc : Continuous (fun r : ℝ => 1 - cutoff (r / R)) :=
    continuous_const.sub
      (cutoff_contDiff_infty.continuous.comp
        (continuous_id.div_const R))
  have hchi : Measurable (actualOneLayerInnerOverlapCutoff R) := by
    change Measurable (fun r : ℝ => ((1 - cutoff (r / R) : ℝ) : ℂ))
    exact Complex.measurable_ofReal.comp hc.measurable
  have hscale : Measurable (rescalePhysicalRadiation ell z) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hcut : Measurable (fun x => actualOneLayerInnerOverlapCutoff R x *
      rescalePhysicalRadiation ell z x) := hchi.mul hscale
  unfold actualHartreeNonlocalCutoffError
  exact (actual_complexRadialHartreeNonlinearity_measurable _ hcut).sub
    (hchi.mul (actual_complexRadialHartreeNonlinearity_measurable _ hscale))

end HBL.TypeIIDynamicSelection
