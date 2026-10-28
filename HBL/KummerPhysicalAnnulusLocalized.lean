import HBL.KummerFrozenAnnulus
import Mathlib.Tactic

/-!
# Physical Kummer right inverse localized to a positive annulus

The old predicate IsFrozenHartreePair required the singular physical
coefficient 2/z+i z/2 on ALL z>0, while a FundamentalPair had globally
differentiable functions and a globally nonzero Wronskian. Abel's
identity shows these global assumptions cannot be instantiated together:
W(z)=C z^(-2) exp(-i z^2/4), which diverges at z=0 for C ne 0.

This file instead asks that the globally defined auxiliary fundamental pair
agree with the genuine frozen Hartree coefficients ONLY on the fixed compact
positive annulus. Such an interface can be instantiated by a regularized
extension of the coefficients to the rest of the real axis.

The exact physical residual and both endpoint normalizations are obtained
on that annulus. Constructing a global auxiliary pair with a valid regularized
coefficient remains an independent existence obligation, not a hidden axiom.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace HBL.Profile.Kummer

/-- The correct matching condition, only over the physical positive annulus. -/
def IsFrozenHartreePairOn
    (mu theta zMinus zPlus : ℝ) (K : FundamentalPair) : Prop :=
  (∀ z ∈ Icc zMinus zPlus, K.a z = frozenFirstCoeff z) ∧
  (∀ z ∈ Icc zMinus zPlus, K.b z = frozenZeroCoeff mu theta)

/-- A continuous regularization of 2/z below the annulus; it agrees with
the physical coefficient whenever z≥zMinus>0. -/
def regularizedFirstCoeff (zMinus z : ℝ) : ℂ :=
  (2 : ℂ) / ((max (zMinus / 2) z : ℝ) : ℂ) +
    Complex.I * (z : ℂ) / 2

theorem regularizedFirstCoeff_eq_physical
    (zMinus z : ℝ) (hmin : 0 < zMinus) (hz : zMinus ≤ z) :
    regularizedFirstCoeff zMinus z = frozenFirstCoeff z := by
  have hhalf : zMinus / 2 ≤ z := by linarith
  simp only [regularizedFirstCoeff, frozenFirstCoeff, max_eq_right hhalf]

theorem regularizedFirstCoeff_continuous
    (zMinus : ℝ) (hmin : 0 < zMinus) :
    Continuous (regularizedFirstCoeff zMinus) := by
  have hmax : Continuous (fun z : ℝ => max (zMinus / 2) z) :=
    continuous_const.max continuous_id
  have hpos (z : ℝ) : 0 < max (zMinus / 2) z :=
    lt_of_lt_of_le (half_pos hmin) (le_max_left _ _)
  unfold regularizedFirstCoeff
  have hdiv : Continuous
      (fun z : ℝ =>
        (2 : ℂ) / ((max (zMinus / 2) z : ℝ) : ℂ)) := by
    have hc : Continuous
        (fun z : ℝ => ((max (zMinus / 2) z : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hmax
    exact continuous_const.div hc (fun z =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos z)))
  exact hdiv.add
    ((continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id)).div_const _)

/-- The precise physical ODE residual, without any coefficient identity
outside [zMinus,zPlus]. -/
theorem annulusSolution_frozen_residual_on
    (mu theta zMinus zPlus : ℝ) (K : FundamentalPair)
    (hK : IsFrozenHartreePairOn mu theta zMinus zPlus K)
    (F : ℝ → ℂ) (z : ℝ) (hz : z ∈ Icc zMinus zPlus) :
    frozenRadialJetResidual mu theta (z : ℂ)
      (annulusSolution K zMinus zPlus F z)
      (annulusSolutionDeriv K zMinus zPlus F z)
      (annulusSolutionSecondDeriv K zMinus zPlus F z) = F z := by
  have h := annulusSolution_equation K zMinus zPlus F z
  rw [hK.1 z hz, hK.2 z hz] at h
  unfold frozenFirstCoeff frozenZeroCoeff at h
  unfold frozenRadialJetResidual
  push_cast at h ⊢
  linear_combination h

/-- All verified annular facts, localized so they do not invoke a
contradictory all-positive-half-line coefficient match. -/
theorem actualKummerAnnulus_localized_certified
    (mu theta zMinus zPlus : ℝ) (K : FundamentalPair)
    (hK : IsFrozenHartreePairOn mu theta zMinus zPlus K)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ z ∈ Icc zMinus zPlus,
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
  exact ⟨fun z hz => annulusSolution_frozen_residual_on
      mu theta zMinus zPlus K hK F z hz,
    hv.1, hv.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

#print axioms regularizedFirstCoeff_eq_physical
#print axioms regularizedFirstCoeff_continuous
#print axioms annulusSolution_frozen_residual_on
#print axioms actualKummerAnnulus_localized_certified

end HBL.Profile.Kummer
