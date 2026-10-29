import HBL.KummerParameterInverse.Definitions
import Mathlib.Analysis.Complex.RealDeriv
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_physical_parameter_derivatives {z d : ℝ}
    (S : ℂ → (AnnulusSource z d →L[ℂ] AnnulusJet z d))
    (S' : AnnulusSource z d →L[ℂ] AnnulusJet z d) (mu theta mu0 theta0 : ℝ)
    (hS : HasDerivAt S S' (frozenZeroCoeff mu theta - frozenZeroCoeff mu0 theta0)) :
    HasDerivAt (fun m : ℝ => S (frozenZeroCoeff m theta - frozenZeroCoeff mu0 theta0))
      ((-Complex.I) • S') mu ∧
    HasDerivAt (fun t : ℝ => S (frozenZeroCoeff mu t - frozenZeroCoeff mu0 theta0)) S' theta := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hrm : HasDerivAt (fun m : ℝ => (m : ℂ)) 1 mu := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt (x := mu)
  have hrt : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 theta := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt (x := theta)
  have hm : HasDerivAt (fun m : ℝ => frozenZeroCoeff m theta - frozenZeroCoeff mu0 theta0) (-Complex.I) mu := by
    unfold frozenZeroCoeff
    simpa only [zero_sub, mul_neg, mul_one, zero_add] using!
      (((hasDerivAt_const mu (theta : ℂ)).add
        (((hasDerivAt_const mu (1 / 4 : ℂ)).sub hrm).const_mul Complex.I)).sub_const
        (frozenZeroCoeff mu0 theta0))
  have ht : HasDerivAt (fun t : ℝ => frozenZeroCoeff mu t - frozenZeroCoeff mu0 theta0) (1 : ℂ) theta := by
    unfold frozenZeroCoeff
    simpa only [frozenZeroCoeff] using!
      (hrt.add_const (Complex.I * (1 / 4 - (mu : ℂ)))).sub_const (frozenZeroCoeff mu0 theta0)
  constructor
  · simpa only [Function.comp_def] using!
      hS.scomp (𝕜 := ℝ) (𝕜' := ℂ) (F := AnnulusSource z d →L[ℂ] AnnulusJet z d) mu hm
  · simpa only [Function.comp_def, one_smul] using!
      hS.scomp (𝕜 := ℝ) (𝕜' := ℂ) (F := AnnulusSource z d →L[ℂ] AnnulusJet z d) theta ht
end HBL.Profile.Kummer
