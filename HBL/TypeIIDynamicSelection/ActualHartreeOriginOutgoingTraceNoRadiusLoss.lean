import HBL.TypeIIDynamicSelection.ActualKummerTransmissionProjection
import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Tactic

/-!
# Genuine compatible origin outgoing trace without shrinking-interface loss

For the ACTUAL normalized physical Kummer basis, the regular radial mode
X(r) has |X(r)|=O(1) and |X'(r)|=O(r) as r tends to zero, uniformly
for frozen compact Kummer parameters. The exact physical Wronskian has
inverse norm r^2. Therefore the original outgoing source/inner-jet
compatibility trace is O(r) times the scaled left Fredholm Cauchy norm
|U|+r|DU|. The apparent inverse radius loss does not occur.

This is a real two-channel physical estimate, not a synthetic Green
coefficient label or a statement presupposing a Type-II blowup rate.
To deduce a whole Green-field positive time gain, the adjacent local
source moment and actual time-dependent physical profile still require
the matching estimates and full nonlinear residual control.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_origin_outgoing_trace_without_inverse_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B r : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hScale : B ≤ scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hr : r ∈ Ioc 0 B)
    (U DU : ℂ) :
    ‖actualOriginOutgoingTrace K r U DU‖ ≤
      (1 + (D + 1) * G * (B ^ 2 + 2)) *
        r * (‖U‖ + r * ‖DU‖) := by
  let J : ℝ := 1 + (D + 1) * G * (B ^ 2 + 2)
  have hrpos : 0 < r := hr.1
  have hrOne : r ≤ 1 := hr.2.trans hBOne
  have hrScale : r ≤ scale := hr.2.trans hScale
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hDGN : 0 ≤ (D + 1) * G := by positivity
  have hReg :=
    origin_kummer_regular_physical_bound K D G hD hG
      hScale hcoeff hbound r hr
  have hValue : ‖originPhysicalValue K.x r‖ ≤ J := by
    calc
      _ ≤ 1 + (D + 1) * G * B ^ 2 := hReg.1
      _ ≤ J := by dsimp [J]; nlinarith [mul_nonneg hDGN (sq_nonneg B)]
  have hSlope : ‖originPhysicalSlope K.x K.dx r‖ ≤ J := by
    calc
      _ ≤ 2 * ((D + 1) * G) * r := hReg.2
      _ ≤ 2 * ((D + 1) * G) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hrOne
            (show 0 ≤ 2 * ((D + 1) * G) by positivity))
      _ ≤ J := by
        dsimp [J]
        nlinarith [mul_nonneg hDGN (sq_nonneg B)]
  have hWr :
      originGreenWronskian K r =
        (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K ⟨hrpos.le,hrScale⟩ hrpos.ne'
  have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hWinv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    simp
  have hNum :
      ‖U * originPhysicalSlope K.x K.dx r -
        DU * originPhysicalValue K.x r‖ ≤
      J * (‖U‖ + ‖DU‖) := by
    calc
      _ ≤ ‖U * originPhysicalSlope K.x K.dx r‖ +
            ‖DU * originPhysicalValue K.x r‖ := norm_sub_le _ _
      _ = ‖U‖ * ‖originPhysicalSlope K.x K.dx r‖ +
            ‖DU‖ * ‖originPhysicalValue K.x r‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ ‖U‖ * J + ‖DU‖ * J :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSlope (norm_nonneg U))
          (mul_le_mul_of_nonneg_left hValue (norm_nonneg DU))
      _ = J * (‖U‖ + ‖DU‖) := by ring
  have hrSq : r ^ 2 ≤ r := by
    nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hrOne)]
  calc
    ‖actualOriginOutgoingTrace K r U DU‖ =
        ‖U * originPhysicalSlope K.x K.dx r -
          DU * originPhysicalValue K.x r‖ * r ^ 2 := by
      unfold actualOriginOutgoingTrace
      rw [div_eq_mul_inv, norm_mul, hWinv]
    _ ≤ (J * (‖U‖ + ‖DU‖)) * r ^ 2 :=
      mul_le_mul_of_nonneg_right hNum (sq_nonneg r)
    _ = J * (r ^ 2 * ‖U‖ + r ^ 2 * ‖DU‖) := by ring
    _ ≤ J * (r * ‖U‖ + r ^ 2 * ‖DU‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hrSq (norm_nonneg U))
          (le_refl _)) hJ
    _ = (1 + (D + 1) * G * (B ^ 2 + 2)) *
        r * (‖U‖ + r * ‖DU‖) := by dsimp [J]; ring

end HBL.TypeIIDynamicSelection
