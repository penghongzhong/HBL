import HBL.KummerOriginBasis.Wronskian
import HBL.KummerOriginBasis.PhysicalJets

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

/-- The physical pair has precisely the manuscript Wronskian, with no unknown constant. -/
theorem origin_physical_wronskian_exact {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {r : ℝ} (hr : r ∈ Icc 0 R) (hr0 : r ≠ 0) :
    originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
        originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) := by
  rw [← origin_kummer_wronskian_exact K hr]
  dsimp [originPhysicalValue, originPhysicalSlope]
  field_simp [Complex.ofReal_ne_zero.mpr hr0]
  ring
end HBL.Profile.Kummer
