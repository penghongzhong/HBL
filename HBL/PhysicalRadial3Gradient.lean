import HBL.PhysicalRadial3LocalPotential
import HBL.RadialEnergyBilinear
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
The genuine three-dimensional radial gradient energy in the physical
Euclidean space, with no radial-coordinate gradient postulate.

The gradient of a real scalar map is measured by the operator norm of
its actual Fréchet derivative. Away from the origin, composition with
the Euclidean norm and the unit norm of its Fréchet derivative identify
this with the absolute radial derivative. The origin is null for actual
three-dimensional Lebesgue measure.

The 4π polar factor is from the independently compiled Mathlib integral
theorem. This does not identify the full three-dimensional Hessian until
the compact-core radial energy completion and nonlocal kernel bridge
have also been supplied.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- An actual radial scalar field on physical Euclidean three-space. -/
def physicalRadial3_radialLift (f : ℝ → ℝ) :
    PhysicalRadialSpace3 → ℝ := fun x => f ‖x‖

/-- Away from the origin, the operator norm of the actual 3D Fréchet
gradient equals the magnitude of the actual one-dimensional derivative. -/
theorem physicalRadial3_radial_fderiv_norm
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (x : PhysicalRadialSpace3) (hx : x ≠ 0) :
    ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ =
      |deriv f ‖x‖| := by
  have hn : DifferentiableAt ℝ (norm : PhysicalRadialSpace3 → ℝ) x :=
    (contDiffAt_norm ℝ (n := 1) hx).differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ f ‖x‖ :=
    hf.differentiable (by norm_num) ‖x‖
  have hcomp :
      fderiv ℝ (physicalRadial3_radialLift f) x =
        (fderiv ℝ f ‖x‖).comp
          (fderiv ℝ (norm : PhysicalRadialSpace3 → ℝ) x) := by
    simpa only [physicalRadial3_radialLift, Function.comp_def] using
      (fderiv_comp (x := x) hfd hn)
  have hmap :
      (fderiv ℝ f ‖x‖).comp
          (fderiv ℝ (norm : PhysicalRadialSpace3 → ℝ) x) =
        (deriv f ‖x‖) •
          (fderiv ℝ (norm : PhysicalRadialSpace3 → ℝ) x) := by
    ext v
    change (fderiv ℝ f ‖x‖)
        ((fderiv ℝ (norm : PhysicalRadialSpace3 → ℝ) x) v) =
      deriv f ‖x‖ *
        ((fderiv ℝ (norm : PhysicalRadialSpace3 → ℝ) x) v)
    exact fderiv_eq_deriv_mul
  calc
    ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ =
        ‖(deriv f ‖x‖) •
          (fderiv ℝ (norm : PhysicalRadialSpace3 → ℝ) x)‖ := by
      rw [hcomp, hmap]
    _ = |deriv f ‖x‖| := by
      rw [norm_smul, norm_fderiv_norm hn]
      simp only [Real.norm_eq_abs, mul_one]

/-- Genuine 3D Euclidean gradient norm squared: the radial chain rule
holds for every nonzero physical point. -/
theorem physicalRadial3_radial_fderiv_norm_sq
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (x : PhysicalRadialSpace3) (hx : x ≠ 0) :
    ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2 =
      (deriv f ‖x‖) ^ 2 := by
  rw [physicalRadial3_radial_fderiv_norm f hf x hx, sq_abs]

/-- Exact physical three-dimensional radial gradient energy identity.
It uses the actual Fréchet derivative and actual Lebesgue integral. -/
theorem physicalRadial3_gradient_energy_integral
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x : PhysicalRadialSpace3,
      ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) =
      (4 * Real.pi) *
        (∫ r in Ioi (0 : ℝ), r ^ 2 * (deriv f r) ^ 2) := by
  have hne : ∀ᵐ x : PhysicalRadialSpace3
      ∂(volume : Measure PhysicalRadialSpace3), x ≠ 0 := by
    simp [ae_iff]
  calc
    (∫ x : PhysicalRadialSpace3,
        ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) =
        ∫ x : PhysicalRadialSpace3, (deriv f ‖x‖) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hne] with x hx
      exact physicalRadial3_radial_fderiv_norm_sq f hf x hx
    _ = (4 * Real.pi) *
          (∫ r in Ioi (0 : ℝ), r ^ 2 * (deriv f r) ^ 2) :=
      physicalRadial3_integral (fun r => (deriv f r) ^ 2)

/-- The true 3D local phase-Hessian quadratic energy, including both
the physical gradient and the local W^4 potential, has the exact radial
form with the same 4π coefficient. -/
theorem physicalRadial3_phase_local_quadratic_integral
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x : PhysicalRadialSpace3,
        ‖fderiv ℝ (physicalRadial3_radialLift f) x‖ ^ 2) -
      3 * (∫ x : PhysicalRadialSpace3,
        bubble (‖x‖) ^ 4 * f (‖x‖) * f (‖x‖)) =
      (4 * Real.pi) *
        ((∫ r in Ioi (0 : ℝ), r ^ 2 * (deriv f r) ^ 2) -
          3 * (∫ r : ℝ,
            weightedGreenDecay r ^ 2 * radialU f r * radialU f r
            ∂halfLineMeasure)) := by
  rw [physicalRadial3_gradient_energy_integral f hf,
    physicalRadial3_localHartreePotential_pairing f f]
  ring

end HBL.Modulation.Monopole
