import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Variation of parameters for the Kummer regional block

This is the analytic core behind the manuscript formula `G^K_zeta`.
The special-function input is reduced to a genuine C2 fundamental pair with
nonvanishing Wronskian and the exact homogeneous equation. From those inputs
Lean constructs the normalized variation-of-parameters solution and proves
its first and second derivatives and the inhomogeneous equation.

No one-layer cancellation statement and no PDE profile conclusion is assumed.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HBL.Profile.Kummer

/-- A C2 fundamental pair for a scalar complex second-order equation on the
real radial variable. The coefficient functions may themselves be complex. -/
structure FundamentalPair where
  a : ℝ → ℂ
  b : ℝ → ℂ
  phi : ℝ → ℂ
  psi : ℝ → ℂ
  dphi : ℝ → ℂ
  dpsi : ℝ → ℂ
  ddphi : ℝ → ℂ
  ddpsi : ℝ → ℂ
  phi_hasDeriv : ∀ z, HasDerivAt phi (dphi z) z
  psi_hasDeriv : ∀ z, HasDerivAt psi (dpsi z) z
  dphi_hasDeriv : ∀ z, HasDerivAt dphi (ddphi z) z
  dpsi_hasDeriv : ∀ z, HasDerivAt dpsi (ddpsi z) z
  phi_homogeneous : ∀ z, ddphi z + a z * dphi z + b z * phi z = 0
  psi_homogeneous : ∀ z, ddpsi z + a z * dpsi z + b z * psi z = 0
  wronskian_ne : ∀ z, phi z * dpsi z - dphi z * psi z ≠ 0

def wronskian (K : FundamentalPair) (z : ℝ) : ℂ :=
  K.phi z * K.dpsi z - K.dphi z * K.psi z

theorem phi_continuous (K : FundamentalPair) : Continuous K.phi := by
  exact continuous_iff_continuousAt.mpr fun z => (K.phi_hasDeriv z).continuousAt

theorem psi_continuous (K : FundamentalPair) : Continuous K.psi := by
  exact continuous_iff_continuousAt.mpr fun z => (K.psi_hasDeriv z).continuousAt

theorem dphi_continuous (K : FundamentalPair) : Continuous K.dphi := by
  exact continuous_iff_continuousAt.mpr fun z => (K.dphi_hasDeriv z).continuousAt

theorem dpsi_continuous (K : FundamentalPair) : Continuous K.dpsi := by
  exact continuous_iff_continuousAt.mpr fun z => (K.dpsi_hasDeriv z).continuousAt

theorem wronskian_continuous (K : FundamentalPair) :
    Continuous (wronskian K) := by
  exact ((phi_continuous K).mul (dpsi_continuous K)).sub
    ((dphi_continuous K).mul (psi_continuous K))

theorem wronskian_ne_zero (K : FundamentalPair) (z : ℝ) :
    wronskian K z ≠ 0 := by
  exact K.wronskian_ne z

def sourceA (K : FundamentalPair) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.psi z * F z / wronskian K z

def sourceB (K : FundamentalPair) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.phi z * F z / wronskian K z

theorem sourceA_continuous (K : FundamentalPair) (F : ℝ → ℂ)
    (hF : Continuous F) : Continuous (sourceA K F) := by
  unfold sourceA
  exact ((psi_continuous K).mul hF).div (wronskian_continuous K)
    (fun z => wronskian_ne_zero K z)

theorem sourceB_continuous (K : FundamentalPair) (F : ℝ → ℂ)
    (hF : Continuous F) : Continuous (sourceB K F) := by
  unfold sourceB
  exact ((phi_continuous K).mul hF).div (wronskian_continuous K)
    (fun z => wronskian_ne_zero K z)

/-- Fixed-base coefficient for the first homogeneous solution. -/
def coeffA (K : FundamentalPair) (z0 : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  -(∫ r in z0..z, sourceA K F r)

/-- Fixed-base coefficient for the second homogeneous solution. -/
def coeffB (K : FundamentalPair) (z0 : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ r in z0..z, sourceB K F r

theorem coeffA_hasDerivAt (K : FundamentalPair) (z0 : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (coeffA K z0 F) (-sourceA K F z) z := by
  have hc := sourceA_continuous K F hF
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable z0 z)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [coeffA] using hi.neg

theorem coeffB_hasDerivAt (K : FundamentalPair) (z0 : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (coeffB K z0 F) (sourceB K F z) z := by
  have hc := sourceB_continuous K F hF
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable z0 z)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [coeffB] using hi

def solution (K : FundamentalPair) (z0 : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.phi z * coeffA K z0 F z + K.psi z * coeffB K z0 F z

def solutionDeriv (K : FundamentalPair) (z0 : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.dphi z * coeffA K z0 F z + K.dpsi z * coeffB K z0 F z

def solutionSecondDeriv
    (K : FundamentalPair) (z0 : ℝ) (F : ℝ → ℂ) (z : ℝ) : ℂ :=
  K.ddphi z * coeffA K z0 F z +
    K.ddpsi z * coeffB K z0 F z + F z

theorem solution_hasDerivAt (K : FundamentalPair) (z0 : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (solution K z0 F) (solutionDeriv K z0 F z) z := by
  have hA := coeffA_hasDerivAt K z0 F hF z
  have hB := coeffB_hasDerivAt K z0 F hF z
  have h := (K.phi_hasDeriv z).mul hA |>.add ((K.psi_hasDeriv z).mul hB)
  convert h using 1
  · rfl
  · unfold solutionDeriv sourceA sourceB
    ring

theorem solutionDeriv_hasDerivAt (K : FundamentalPair) (z0 : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) (z : ℝ) :
    HasDerivAt (solutionDeriv K z0 F)
      (solutionSecondDeriv K z0 F z) z := by
  have hA := coeffA_hasDerivAt K z0 F hF z
  have hB := coeffB_hasDerivAt K z0 F hF z
  have h := (K.dphi_hasDeriv z).mul hA |>.add ((K.dpsi_hasDeriv z).mul hB)
  convert h using 1
  · rfl
  · unfold solutionSecondDeriv sourceA sourceB wronskian
    field_simp [K.wronskian_ne z]
    ring

theorem solution_equation (K : FundamentalPair) (z0 : ℝ)
    (F : ℝ → ℂ) (z : ℝ) :
    solutionSecondDeriv K z0 F z +
        K.a z * solutionDeriv K z0 F z +
        K.b z * solution K z0 F z = F z := by
  calc
    solutionSecondDeriv K z0 F z +
          K.a z * solutionDeriv K z0 F z +
          K.b z * solution K z0 F z =
        (K.ddphi z + K.a z * K.dphi z + K.b z * K.phi z) *
            coeffA K z0 F z +
          (K.ddpsi z + K.a z * K.dpsi z + K.b z * K.psi z) *
            coeffB K z0 F z + F z := by
              unfold solutionSecondDeriv solutionDeriv solution
              ring
    _ = F z := by
      rw [K.phi_homogeneous z, K.psi_homogeneous z]
      ring

theorem solution_initial_value (K : FundamentalPair) (z0 : ℝ)
    (F : ℝ → ℂ) :
    solution K z0 F z0 = 0 ∧ solutionDeriv K z0 F z0 = 0 := by
  simp [solution, solutionDeriv, coeffA, coeffB]

/-- Full variation-of-parameters certificate used by the Kummer regional
inverse: exact two derivatives, exact source equation, and a fixed
normalization at the base point. -/
theorem variationOfParameters_certified
    (K : FundamentalPair) (z0 : ℝ) (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ z, HasDerivAt (solution K z0 F) (solutionDeriv K z0 F z) z) ∧
    (∀ z, HasDerivAt (solutionDeriv K z0 F)
      (solutionSecondDeriv K z0 F z) z) ∧
    (∀ z, solutionSecondDeriv K z0 F z +
      K.a z * solutionDeriv K z0 F z +
      K.b z * solution K z0 F z = F z) ∧
    solution K z0 F z0 = 0 ∧ solutionDeriv K z0 F z0 = 0 := by
  exact ⟨solution_hasDerivAt K z0 F hF,
    solutionDeriv_hasDerivAt K z0 F hF,
    solution_equation K z0 F, (solution_initial_value K z0 F).1,
    (solution_initial_value K z0 F).2⟩

end HBL.Profile.Kummer
