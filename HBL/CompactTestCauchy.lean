import HBL.CompactTestLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Cauchy--Schwarz on the finite radial interval used by the compact threshold
tests in the first manuscript lemma.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation

/-- The finite-interval Cauchy--Schwarz estimate in the exact form needed for
the compact threshold test functions. -/
theorem compactTest_cauchySchwarz
    (R : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ) (hzeta : Continuous zeta) (hf : Continuous f) :
    (∫ r, ‖zeta r‖ * ‖f r‖ ∂(volume.restrict (Ioc 0 R))) ≤
      (∫ r, ‖zeta r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ^ ((1 : ℝ) / 2) *
      (∫ r, ‖f r‖ ^ (2 : ℝ) ∂(volume.restrict (Ioc 0 R))) ^ ((1 : ℝ) / 2) := by
  have hzeta2 :
      MemLp zeta (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioc 0 R)) :=
    continuous_memLp_restrict_Ioc 0 R hR zeta hzeta (ENNReal.ofReal (2 : ℝ))
  have hf2 :
      MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioc 0 R)) :=
    continuous_memLp_restrict_Ioc 0 R hR f hf (ENNReal.ofReal (2 : ℝ))
  exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hzeta2 hf2

end HBL.Modulation
