import HBL.KummerVariationOfParameters

/-!
# Exact two-endpoint Kummer annulus inverse

This is the normalization used in the manuscript:
  Phi(z) * ∫_z^{z+} Psi F / W
  + Psi(z) * ∫_{z-}^z Phi F / W.

For any genuine C2 fundamental pair with nonvanishing Wronskian, the file
proves the two derivatives and the exact inhomogeneous equation.  No
one-layer cancellation or profile conclusion is assumed.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HBL.Profile.Kummer

def annulusCoeffPhi
    (K : FundamentalPair) (zPlus : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ r in z..zPlus, sourceA K F r

def annulusCoeffPsi
    (K : FundamentalPair) (zMinus : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ r in zMinus..z, sourceB K F r

theorem annulusCoeffPhi_hasDerivAt
    (K : FundamentalPair) (zPlus : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (annulusCoeffPhi K zPlus F) (-sourceA K F z) z := by
  have hc := sourceA_continuous K F hF
  have hi := intervalIntegral.integral_hasDerivAt_left
    (hc.intervalIntegrable z zPlus)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt
    (fun u : ℝ => ∫ r in u..zPlus, sourceA K F r)
    (-sourceA K F z) z
  exact hi

theorem annulusCoeffPsi_hasDerivAt
    (K : FundamentalPair) (zMinus : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (annulusCoeffPsi K zMinus F) (sourceB K F z) z := by
  have hc := sourceB_continuous K F hF
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable zMinus z)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt
    (fun u : ℝ => ∫ r in zMinus..u, sourceB K F r)
    (sourceB K F z) z
  exact hi

def annulusSolution
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.phi z * annulusCoeffPhi K zPlus F z +
    K.psi z * annulusCoeffPsi K zMinus F z

def annulusSolutionDeriv
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.dphi z * annulusCoeffPhi K zPlus F z +
    K.dpsi z * annulusCoeffPsi K zMinus F z

def annulusSolutionSecondDeriv
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.ddphi z * annulusCoeffPhi K zPlus F z +
    K.ddpsi z * annulusCoeffPsi K zMinus F z + F z

theorem annulusSolution_hasDerivAt
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (annulusSolution K zMinus zPlus F)
      (annulusSolutionDeriv K zMinus zPlus F z) z := by
  have hA := annulusCoeffPhi_hasDerivAt K zPlus F hF z
  have hB := annulusCoeffPsi_hasDerivAt K zMinus F hF z
  have h := (K.phi_hasDeriv z).mul hA |>.add
    ((K.psi_hasDeriv z).mul hB)
  convert h using 1
  · rfl
  · unfold annulusSolutionDeriv sourceA sourceB
    ring

theorem annulusSolutionDeriv_hasDerivAt
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (annulusSolutionDeriv K zMinus zPlus F)
      (annulusSolutionSecondDeriv K zMinus zPlus F z) z := by
  have hA := annulusCoeffPhi_hasDerivAt K zPlus F hF z
  have hB := annulusCoeffPsi_hasDerivAt K zMinus F hF z
  have h := (K.dphi_hasDeriv z).mul hA |>.add
    ((K.dpsi_hasDeriv z).mul hB)
  convert h using 1
  · rfl
  · unfold annulusSolutionSecondDeriv sourceA sourceB wronskian
    field_simp [K.wronskian_ne z]
    ring

theorem annulusSolution_equation
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (z : ℝ) :
    annulusSolutionSecondDeriv K zMinus zPlus F z +
        K.a z * annulusSolutionDeriv K zMinus zPlus F z +
        K.b z * annulusSolution K zMinus zPlus F z = F z := by
  calc
    _ =
        (K.ddphi z + K.a z * K.dphi z + K.b z * K.phi z) *
            annulusCoeffPhi K zPlus F z +
          (K.ddpsi z + K.a z * K.dpsi z + K.b z * K.psi z) *
            annulusCoeffPsi K zMinus F z + F z := by
              unfold annulusSolutionSecondDeriv annulusSolutionDeriv annulusSolution
              ring
    _ = F z := by
      rw [K.phi_homogeneous z, K.psi_homogeneous z]
      ring

theorem annulus_endpoint_normalization
    (K : FundamentalPair) (zMinus zPlus : ℝ) (F : ℝ → ℂ) :
    annulusCoeffPhi K zPlus F zPlus = 0 ∧
    annulusCoeffPsi K zMinus F zMinus = 0 := by
  simp [annulusCoeffPhi, annulusCoeffPsi]

theorem annulusVariationOfParameters_certified
    (K : FundamentalPair) (zMinus zPlus : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ z, HasDerivAt (annulusSolution K zMinus zPlus F)
      (annulusSolutionDeriv K zMinus zPlus F z) z) ∧
    (∀ z, HasDerivAt (annulusSolutionDeriv K zMinus zPlus F)
      (annulusSolutionSecondDeriv K zMinus zPlus F z) z) ∧
    (∀ z, annulusSolutionSecondDeriv K zMinus zPlus F z +
      K.a z * annulusSolutionDeriv K zMinus zPlus F z +
      K.b z * annulusSolution K zMinus zPlus F z = F z) ∧
    annulusCoeffPhi K zPlus F zPlus = 0 ∧
    annulusCoeffPsi K zMinus F zMinus = 0 := by
  exact ⟨annulusSolution_hasDerivAt K zMinus zPlus F hF,
    annulusSolutionDeriv_hasDerivAt K zMinus zPlus F hF,
    annulusSolution_equation K zMinus zPlus F,
    (annulus_endpoint_normalization K zMinus zPlus F).1,
    (annulus_endpoint_normalization K zMinus zPlus F).2⟩

#print axioms annulusCoeffPhi_hasDerivAt
#print axioms annulusCoeffPsi_hasDerivAt
#print axioms annulusSolution_hasDerivAt
#print axioms annulusSolutionDeriv_hasDerivAt
#print axioms annulusSolution_equation
#print axioms annulusVariationOfParameters_certified

end HBL.Profile.Kummer
