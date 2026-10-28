import HBL.KummerAnnulusInverse
import HBL.KummerFrozenBridge

/-!
# Actual frozen Hartree Kummer annulus equation

This file identifies the generic variation-of-parameters certificate with the
actual frozen annular operator occurring in the manuscript.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Kummer

def frozenFirstCoeff (z : ℝ) : ℂ :=
  2 / (z : ℂ) + Complex.I * (z : ℂ) / 2

def frozenZeroCoeff (mu theta : ℝ) : ℂ :=
  (theta : ℂ) + Complex.I * (1 / 4 - mu)

def IsFrozenHartreePair
    (mu theta : ℝ) (K : FundamentalPair) : Prop :=
  (∀ z : ℝ, 0 < z → K.a z = frozenFirstCoeff z) ∧
  (∀ z : ℝ, 0 < z → K.b z = frozenZeroCoeff mu theta)

theorem annulusSolution_actual_frozen_equation
    (mu theta : ℝ) (K : FundamentalPair)
    (hK : IsFrozenHartreePair mu theta K)
    (zMinus zPlus : ℝ) (F : ℝ → ℂ)
    {z : ℝ} (hz : 0 < z) :
    annulusSolutionSecondDeriv K zMinus zPlus F z +
        frozenFirstCoeff z * annulusSolutionDeriv K zMinus zPlus F z +
        frozenZeroCoeff mu theta * annulusSolution K zMinus zPlus F z =
      F z := by
  have h := annulusSolution_equation K zMinus zPlus F z
  rw [hK.1 z hz, hK.2 z hz] at h
  exact h

theorem annulusSolution_actual_frozenResidual
    (mu theta : ℝ) (K : FundamentalPair)
    (hK : IsFrozenHartreePair mu theta K)
    (zMinus zPlus : ℝ) (F : ℝ → ℂ)
    {z : ℝ} (hz : 0 < z) :
    frozenRadialJetResidual mu theta (z : ℂ)
      (annulusSolution K zMinus zPlus F z)
      (annulusSolutionDeriv K zMinus zPlus F z)
      (annulusSolutionSecondDeriv K zMinus zPlus F z) = F z := by
  have h := annulusSolution_actual_frozen_equation
    mu theta K hK zMinus zPlus F hz
  unfold frozenRadialJetResidual frozenFirstCoeff frozenZeroCoeff at h ⊢
  push_cast at h ⊢
  simpa [mul_assoc] using h

theorem actualKummerAnnulus_certified
    (mu theta : ℝ) (K : FundamentalPair)
    (hK : IsFrozenHartreePair mu theta K)
    (zMinus zPlus : ℝ) (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ z : ℝ, 0 < z →
      frozenRadialJetResidual mu theta (z : ℂ)
        (annulusSolution K zMinus zPlus F z)
        (annulusSolutionDeriv K zMinus zPlus F z)
        (annulusSolutionSecondDeriv K zMinus zPlus F z) = F z) ∧
    (∀ z, HasDerivAt (annulusSolution K zMinus zPlus F)
      (annulusSolutionDeriv K zMinus zPlus F z) z) ∧
    (∀ z, HasDerivAt (annulusSolutionDeriv K zMinus zPlus F)
      (annulusSolutionSecondDeriv K zMinus zPlus F z) z) ∧
    annulusCoeffPhi K zPlus F zPlus = 0 ∧
    annulusCoeffPsi K zMinus F zMinus = 0 := by
  have hv := annulusVariationOfParameters_certified K zMinus zPlus F hF
  exact ⟨fun z hz => annulusSolution_actual_frozenResidual
      mu theta K hK zMinus zPlus F hz,
    hv.1, hv.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

#print axioms annulusSolution_actual_frozen_equation
#print axioms annulusSolution_actual_frozenResidual
#print axioms actualKummerAnnulus_certified

end HBL.Profile.Kummer
