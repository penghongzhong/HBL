import HBL.KummerOriginBasis.Existence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- The origin initial data fix the Abel constant to exactly one. -/
theorem origin_kummer_wronskian_exact {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {r : ℝ} (hr : r ∈ Icc 0 R) :
    K.y r * K.dx r - K.dy r * K.x r =
      Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) := by
  let W := fun s => K.y s * K.dx s - K.dy s * K.x s
  let E := fun s : ℝ => Complex.exp (Complex.I * (s : ℂ) ^ 2 / 4)
  have hW (s : ℝ) (hs : s ∈ Icc 0 R) :
      HasDerivWithinAt W (-originFirstCoeff s * W s) (Icc 0 R) s := by
    convert ((K.y_deriv s hs).mul (K.dx_deriv s hs)).sub
      ((K.dy_deriv s hs).mul (K.x_deriv s hs)) using 1
    dsimp [W]
    ring
  have hE (s : ℝ) : HasDerivAt E (E s * originFirstCoeff s) s := by
    have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        Complex.ofRealCLM.hasDerivAt (x := s)
    convert (((hc.pow 2).const_mul Complex.I).div_const 4).cexp using 1
    dsimp [E, originFirstCoeff]
    ring
  have hI (s : ℝ) (hs : s ∈ Icc 0 R) :
      HasDerivWithinAt (fun t => E t * W t) 0 (Icc 0 R) s := by
    convert (hE s).hasDerivWithinAt.mul (hW s hs) using 1
    ring
  have hi := constant_of_has_deriv_right_zero
    (HasDerivWithinAt.continuousOn hI)
    (fun s hs => (hI s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) r hr
  have hone : E r * W r = 1 := by
    simpa [E, W, K.y_zero, K.dy_zero, K.x_zero, K.dx_zero] using hi
  have hprod : E r * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) = 1 := by
    dsimp [E]
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (hone.trans hprod.symm)
end HBL.Profile.Kummer
