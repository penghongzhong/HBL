import HBL.KummerOriginBasis.Definitions

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- The manuscript's singular/regular gauge at the origin. -/
def OriginBasisNormalization {mu theta R : ℝ} (K : OriginKummerPair mu theta R) : Prop :=
  Tendsto (fun r : ℝ => originPhysicalValue K.y r - (r : ℂ)⁻¹) (𝓝[>] 0) (𝓝 0) ∧
  Tendsto (originPhysicalValue K.x) (𝓝[>] 0) (𝓝 1) ∧
  Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * originPhysicalSlope K.y K.dy r)
    (𝓝[>] 0) (𝓝 (-1)) ∧
  Tendsto (fun r : ℝ => (r : ℂ) * originPhysicalSlope K.x K.dx r)
    (𝓝[>] 0) (𝓝 0)

/-- Genuine physical equations, the exact determinant, and a uniform C1 basis bound. -/
def OriginBasisOn {mu theta R : ℝ} (K : OriginKummerPair mu theta R)
    (a b C : ℝ) : Prop :=
  ∀ r ∈ Icc a b,
    HasDerivAt (originPhysicalValue K.y) (originPhysicalSlope K.y K.dy r) r ∧
    HasDerivAt (originPhysicalSlope K.y K.dy)
      (-(frozenFirstCoeff r * originPhysicalSlope K.y K.dy r +
        frozenZeroCoeff mu theta * originPhysicalValue K.y r)) r ∧
    HasDerivAt (originPhysicalValue K.x) (originPhysicalSlope K.x K.dx r) r ∧
    HasDerivAt (originPhysicalSlope K.x K.dx)
      (-(frozenFirstCoeff r * originPhysicalSlope K.x K.dx r +
        frozenZeroCoeff mu theta * originPhysicalValue K.x r)) r ∧
    (originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
      originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)) ∧
    (originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
      originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r ≠ 0) ∧
    ‖originPhysicalValue K.y r‖ ≤ C ∧ ‖originPhysicalSlope K.y K.dy r‖ ≤ C ∧
    ‖originPhysicalValue K.x r‖ ≤ C ∧ ‖originPhysicalSlope K.x K.dx r‖ ≤ C ∧
    ‖(originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
      originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r)⁻¹‖ ≤ C
end HBL.Profile.Kummer
