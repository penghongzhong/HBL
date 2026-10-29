import HBL.TestedHamiltonCoupling.NormalizedDefinitions
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace HBL.MainBackward
open HBL.Modulation HBL.Modulation.AffineTail

theorem normalizedHamiltonCoupling_actual_identity
    (f v : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hv : ContDiff ℝ 2 v)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hvmem : MemLp (deriv (radialU v)) 2 halfLineMeasure) :
    normalizedHamiltonCoupling
      (smoothToRadialDotH1 f hfmem, smoothToRadialDotH1 v hvmem) =
      ((∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaPlus r * hMinusApply (radialU v) r),
       -(∫ r in (0 : ℝ)..Real.exp 1, normalizedZetaMinus r * hPlusApply (radialU f) r)) ∧
    (∀ q : ConstrainedCenterSpace,
      normalizedConstrainedHamiltonCoupling q = normalizedHamiltonCoupling q.val ∧
      ‖normalizedConstrainedHamiltonCoupling q‖ ≤
        ‖normalizedConstrainedHamiltonCoupling‖ * ‖q‖) := by
  have hp := normalizedHamiltonTest_profiles
  have hi := (testedHamiltonCoupling_actual_identity
    (Real.exp 1) (Real.exp_pos 1).le normalizedZetaPlus
    (normalizedZetaPlus_contDiff_infty.of_le (by simp))
    hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    normalizedPhaseTestProfile hp.1 hp.2.2.1 f v hf hv hfmem hvmem).1
  refine ⟨?_, fun q => ⟨rfl, ContinuousLinearMap.le_opNorm _ q⟩⟩
  simpa only [normalizedHamiltonCoupling, hp.2.1] using hi
end HBL.MainBackward
