import HBL.KummerOriginGreen.InverseLinearRegularSourceRadiusGain
import HBL.KummerOriginGreen.GreenBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Sharpen the actual zero-left Cramer A-moment, not merely its coefficient norms

The original zero-left Green/Cramer field contains A_F(r)-A_F(a).
Estimating these two coefficients separately destroys the cancellation
at the shrinking left interface. The original integral algebra gives
  A_F(r)-A_F(a) = - integral_a^r X(s) F(s)/W_K(s) ds.

The original regular Kummer mode and exact Wronskian give the
pointwise density bound |X(s)F(s)/W(s)| <= J M s
for actual inverse-linear forcing |F(s)|<=M/s. Retaining s<=r
inside the integral proves
  |A_F(r)-A_F(a)| <= J M r(r-a).
There is no 1/a or 1/a^2 constant. This extra factor r is the
missing input for a uniform UNWEIGHTED physical radial slope/Hdot1
bound, not just the weaker previously verified r^2-weighted slope.

The source continuity assumed here is only on the actual positive
Kummer interval, matching the original classical C1 PDE interface.
No Type-II rate or false full-Hartree source gain is inserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Profile.Kummer

theorem originGreen_inverse_linear_regular_A_moment_difference_radius_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C D G M : ℝ)
    (ha : 0 < a) (_hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hFCont : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M / x)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖originGreenCoeffA K b F r - originGreenCoeffA K b F a‖ ≤
      (1 + (D + 1) * G * b ^ 2) * M * r * (r - a) := by
  let q : ℝ → ℂ := originGreenSourceA K F
  let J : ℝ := 1 + (D + 1) * G * b ^ 2
  have hr0 : 0 < r := ha.trans_le hr.1
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hJM : 0 ≤ J * M := mul_nonneg hJ hM
  have hCont (x : ℝ) (hx : x ∈ Icc a b) :
      ContinuousAt q x := by
    have hxOpen : x ∈ Ioo (0 : ℝ) scale :=
      ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
    rcases hK x hx with ⟨hy, hdy, hxmode, hdx, _, hW, _, _, _, _, _⟩
    have hWr : ContinuousAt (originGreenWronskian K) x :=
      (hy.continuousAt.mul hdx.continuousAt).sub
        (hdy.continuousAt.mul hxmode.continuousAt)
    change ContinuousAt
      (fun t => originPhysicalValue K.x t * F t /
        originGreenWronskian K t) x
    exact (hxmode.continuousAt.mul (hFCont x hxOpen)).div hWr hW
  have hContinuous : ContinuousOn q (Icc a b) :=
    fun x hx => (hCont x hx).continuousWithinAt
  have hIar : IntervalIntegrable q volume a r :=
    (hContinuous.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1
  have hIrb : IntervalIntegrable q volume r b :=
    (hContinuous.mono (Icc_subset_Icc_left hr.1)).intervalIntegrable_of_Icc hr.2
  have hAdd := intervalIntegral.integral_add_adjacent_intervals hIar hIrb
  have hDifference :
      originGreenCoeffA K b F r - originGreenCoeffA K b F a =
        -(∫ x in a..r, q x) := by
    change (∫ x in r..b, q x) - (∫ x in a..b, q x) =
      -(∫ x in a..r, q x)
    rw [← hAdd]
    abel
  have hIntegrand (x : ℝ) (hx : x ∈ Icc a r) :
      ‖q x‖ ≤ (J * M) * r := by
    have hxa : x ∈ Icc a b := ⟨hx.1, hx.2.trans hr.2⟩
    have hxPos : 0 < x := ha.trans_le hx.1
    have hRad :=
      originGreen_inverse_linear_regular_density_one_extra_radius
        K D G b M hD hG hM hb.le hcoeff hbound
        F x ⟨hxPos, hxa.2⟩ (hF x hxa)
    calc
      ‖q x‖ ≤ (J * M) * x := by simpa only [q, J, mul_assoc] using hRad
      _ ≤ (J * M) * r :=
        mul_le_mul_of_nonneg_left hx.2 hJM
  have hIntegral :
      ‖∫ x in a..r, q x‖ ≤ (J * M * r) * |r - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.1] at hx
    exact hIntegrand x ⟨hx.1.le, hx.2⟩
  rw [hDifference, norm_neg]
  simpa only [J, abs_of_nonneg (sub_nonneg.mpr hr.1), mul_assoc] using hIntegral

end HBL.Profile.Kummer
