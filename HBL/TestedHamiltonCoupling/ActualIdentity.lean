import HBL.TestedHamiltonCoupling.Definitions
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
namespace HBL.MainBackward
open HBL.Modulation HBL.Modulation.AffineTail HBL.Modulation.Monopole
open HBL.Modulation.TriangularRepair

/-- Both actual tested channels, including the real nonlocal Hartree term,
form one energy-bounded Hamilton observation with its correct signs. -/
theorem testedHamiltonCoupling_actual_identity
    (R : ℝ) (hR : 0 ≤ R) (zeta : ℝ → ℝ) (hzeta : ContDiff ℝ 2 zeta)
    (hz0 : zeta 0 = 0) (hzR : zeta R = 0) (hdzR : deriv zeta R = 0)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hcut : ∀ r : ℝ, R ≤ r → g r = 0)
    (f v : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hv : ContDiff ℝ 2 v)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hvmem : MemLp (deriv (radialU v)) 2 halfLineMeasure) :
    let B := testedHamiltonCoupling R hR zeta hzeta g hg hcut
    B (smoothToRadialDotH1 f hfmem, smoothToRadialDotH1 v hvmem) =
      ((∫ r in (0 : ℝ)..R, zeta r * hMinusApply (radialU v) r),
       -(∫ r in (0 : ℝ)..R, radialU g r * hPlusApply (radialU f) r)) ∧
    (∀ q : CenterPair, ‖B q‖ ≤ ‖B‖ * ‖q‖) ∧
    (∀ q : ConstrainedCenterSpace,
      constrainedTestedHamiltonCoupling R hR zeta hzeta g hg hcut q = B q.val) := by
  dsimp only
  refine ⟨?_, fun q => ContinuousLinearMap.le_opNorm _ q, fun _ => rfl⟩
  have hp := (phaseThresholdCoupling_certified R hR zeta hzeta hz0 hzR hdzR).1
    v hv hvmem
  have hr := ((realThresholdCoupling_certified g hg R hR hcut).1 f hf hfmem).2
  exact Prod.ext hp.symm (congrArg Neg.neg hr.symm)
end HBL.MainBackward
