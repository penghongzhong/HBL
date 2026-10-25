import HBL.WeightedVolterraAMinus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
The genuine three-dimensional Lebesgue radial integral and exact angular
normalization of the local Hartree Hessian term.

The 4π factor follows from the pinned Mathlib Haar polar-integration
theorem and the actual unit-ball volume, not by definition.
The nonlocal angular Hartree kernel and 3D gradient identity are still
separate from the supporting results below.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

abbrev PhysicalRadialSpace3 := EuclideanSpace ℝ (Fin 3)

/-- Actual volume of the Euclidean three-dimensional unit ball. -/
theorem physicalRadial3_volume_unitBall_real :
    (volume : Measure PhysicalRadialSpace3).real
      (ball (0 : PhysicalRadialSpace3) 1) = Real.pi * 4 / 3 := by
  simp [measureReal_def, EuclideanSpace.volume_ball_fin_three,
    (by positivity : 0 ≤ Real.pi * 4 / 3)]

/-- The exact radial reduction of an arbitrary real scalar integrand
on the physical space, including the angular coefficient 4π. -/
theorem physicalRadial3_integral (F : ℝ → ℝ) :
    (∫ x : PhysicalRadialSpace3, F ‖x‖) =
      (4 * Real.pi) * (∫ r in Ioi (0 : ℝ), r ^ 2 * F r) := by
  have hdim : Module.finrank ℝ PhysicalRadialSpace3 = 3 := by
    simp [PhysicalRadialSpace3]
  have hpolar := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure PhysicalRadialSpace3)) F
  have hpolar' :
      (∫ x : PhysicalRadialSpace3, F ‖x‖) =
        (3 : ℝ) * (volume : Measure PhysicalRadialSpace3).real
          (ball (0 : PhysicalRadialSpace3) 1) *
        (∫ r in Ioi (0 : ℝ), r ^ 2 * F r) := by
    simpa [hdim, smul_eq_mul, nsmul_eq_mul, mul_assoc] using hpolar
  rw [hpolar', physicalRadial3_volume_unitBall_real]
  ring

/-- Exact transfer of the W⁴ potential of the genuine three-dimensional
radial lift to the existing half-line weighted Hartree profile. -/
theorem physicalRadial3_localHartreePotential_pairing
    (f g : ℝ → ℝ) :
    (∫ x : PhysicalRadialSpace3,
      bubble (‖x‖) ^ 4 * f (‖x‖) * g (‖x‖)) =
      (4 * Real.pi) *
        (∫ r : ℝ,
          weightedGreenDecay r ^ 2 * radialU f r * radialU g r
          ∂halfLineMeasure) := by
  rw [physicalRadial3_integral
    (fun r => bubble r ^ 4 * f r * g r)]
  congr 1
  change (∫ r in Ioi (0 : ℝ),
      r ^ 2 * (bubble r ^ 4 * f r * g r)) =
    ∫ r in Ioi (0 : ℝ),
      weightedGreenDecay r ^ 2 * radialU f r * radialU g r
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hweight : weightedGreenDecay r = bubble r ^ 2 := by
    simp only [weightedGreenDecay, bubble_sq]
  rw [hweight]
  dsimp [radialU]
  ring

/-- Actual 3D local potential normalization in the verified phase form.
The separate 3D gradient pairing remains an unproved interface. -/
theorem weightedVolterraAMinus_threeD_localPotential_bridge
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    (4 * Real.pi) *
        inner ℝ (weightedVolterraAMinus (smoothToRadialDotH1 f hfmem))
          (smoothToRadialDotH1 g hgmem) =
      (4 * Real.pi) *
        (∫ r : ℝ, deriv (radialU f) r * deriv (radialU g) r
          ∂halfLineMeasure) -
      3 * (∫ x : PhysicalRadialSpace3,
        bubble (‖x‖) ^ 4 * f (‖x‖) * g (‖x‖)) := by
  rw [weightedVolterraAMinus_radial_profile_pairing f g hf hg hfmem hgmem,
    physicalRadial3_localHartreePotential_pairing f g]
  ring

end HBL.Modulation.Monopole
