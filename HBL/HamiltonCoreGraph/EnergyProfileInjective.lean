import HBL.RadialDotH1Model
import HBL.RadialEnergyCompletion
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff
namespace HBL.Modulation
/-- Equality in radial energy determines smooth profiles on the positive half-line. -/
theorem smoothEnergy_profile_injective
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hmf : MemLp (deriv (radialU f)) 2 (volume.restrict (Ioi (0 : ℝ))))
    (hmg : MemLp (deriv (radialU g)) 2 (volume.restrict (Ioi (0 : ℝ))))
    (he : smoothToRadialDotH1 f hmf = smoothToRadialDotH1 g hmg) :
    EqOn f g (Ioi (0 : ℝ)) := by
  have hd : deriv (radialU f) =ᵐ[volume.restrict (Ioi (0 : ℝ))] deriv (radialU g) := by
    have h := smoothToRadialDotH1_ae f hmf
    rw [he] at h
    exact h.symm.trans (smoothToRadialDotH1_ae g hmg)
  intro r hr
  have hac := Measure.absolutelyContinuous_of_le (finiteRadialMeasure_le_full r)
  have hi : (∫ t in (0 : ℝ)..r, deriv (radialU f) t) =
      ∫ t in (0 : ℝ)..r, deriv (radialU g) t := by
    rw [intervalIntegral.integral_of_le hr.le, intervalIntegral.integral_of_le hr.le]
    exact integral_congr_ae (hac.ae_eq hd)
  rw [radialU_integral_deriv f hf, radialU_integral_deriv g hg] at hi
  exact mul_left_cancel₀ (ne_of_gt hr) hi
end HBL.Modulation
