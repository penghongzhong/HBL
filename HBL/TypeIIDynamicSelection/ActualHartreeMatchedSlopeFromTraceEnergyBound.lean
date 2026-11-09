import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSlopeFromZeroLeftAndPhysicalJet
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedRegularJetNoRadiusLoss
import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Tactic

/-!
# Full matched Kummer radial-energy slope: the correct Fredholm outgoing trace

The full compatible source-selected Kummer continuation retains a singular
Wronskian Green branch with coefficient equal to its ORIGINAL Fredholm left
outgoing trace. Compatibility cancels only the separate HOMOGENEOUS singular
amplitude. Omitting the physical jet trace is mathematically invalid.

The exact Cramer identity decomposes the true matched radial slope into:
  zero-left Volterra slope + left outgoing trace * singular physical slope
  + regular left Cramer coefficient * regular physical slope.

Using the verified original Kummer normalization, the genuinely needed
trace budget is |J_-| <= Ct*a at the moving radius a, while the singular
radial derivative is O(r^-2). The factor a/r <= 1 cancels the only possible
inverse-left-radius loss in the 3D radial-energy coordinate r*|u'(r)|.
The regular Cramer channel is bounded by the original Fredholm left jet.

The hypotheses hZero and hTrace are explicitly the quantitative inputs
that must be produced by the SAME physical Hartree/Cramer data in the
later source-locked theorem. This intermediate lemma does not assume
any time gain, nonlinear all-region PDE residual or Type-II blowup rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Physical radial-energy control for the complete compatible matched
Cramer field, from an already bounded zero-left Green response and the
original O(a) Fredholm outgoing trace. All constants have no 1/a loss. -/
theorem actual_Hartree_full_matched_radial_energy_from_zero_left_and_jet
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C D G E Ct : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hCt : 0 ≤ Ct)
    (hK : OriginBasisOn K a b C)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ) (U DU : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (hTrace : ‖actualOriginOutgoingTrace K a U DU‖ ≤ Ct * a)
    (r : ℝ) (hr : r ∈ Icc a b)
    (hZero : ‖(r : ℂ) * actualOriginMatchedKummerSlope
      K a b F 0 0 r‖ ≤ E) :
    ‖(r : ℂ) * actualOriginMatchedKummerSlope K a b F U DU r‖ ≤
      E + (b + 1) * G * Ct +
        2 * (D + 1) * G ^ 2 * b ^ 2 *
          (a * ‖DU‖ + (a + 1) * ‖U‖) := by
  have hrp : 0 < r := ha.trans_le hr.1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrp.ne'
  have hrscale : r ∈ Icc 0 scale := ⟨hrp.le, hr.2.trans hb.le⟩
  have hb0 : 0 ≤ b := (ha.trans_le hab).le
  have hModes := hbound r hrscale
  have hOutgoingMode :
      (r : ℂ) ^ 2 * originPhysicalSlope K.y K.dy r =
        (r : ℂ) * K.dy r - K.y r := by
    unfold originPhysicalSlope
    field_simp [hrC]
  have hY : ‖(r : ℂ) ^ 2 * originPhysicalSlope K.y K.dy r‖ ≤
      (b + 1) * G := by
    rw [hOutgoingMode]
    calc
      _ ≤ ‖(r : ℂ) * K.dy r‖ + ‖K.y r‖ := norm_sub_le _ _
      _ = r * ‖K.dy r‖ + ‖K.y r‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      _ ≤ r * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hModes.2.1 hrp.le)
          hModes.1
      _ ≤ b * G + G :=
        add_le_add (mul_le_mul_of_nonneg_right hr.2 hG) (le_refl _)
      _ = (b + 1) * G := by ring
  have hYCoef : 0 ≤ (b + 1) * G := by positivity
  let Z : ℂ := actualOriginOutgoingTrace K a U DU
  let Y : ℂ := originPhysicalSlope K.y K.dy r
  have hTraceRad2 :
      ‖(r : ℂ) ^ 2 * (Z * Y)‖ ≤ ((b + 1) * G) * ‖Z‖ := by
    have hEq : (r : ℂ) ^ 2 * (Z * Y) =
        ((r : ℂ) ^ 2 * Y) * Z := by ring
    rw [hEq, norm_mul]
    exact mul_le_mul_of_nonneg_right hY (norm_nonneg Z)
  have hTraceRad2Bound :
      ‖(r : ℂ) ^ 2 * (Z * Y)‖ ≤ ((b + 1) * G) * (Ct * a) := by
    exact hTraceRad2.trans
      (mul_le_mul_of_nonneg_left (by simpa only [Z] using hTrace) hYCoef)
  have hTraceRadNorm :
      ‖(r : ℂ) ^ 2 * (Z * Y)‖ =
        r * ‖(r : ℂ) * (Z * Y)‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrp]
    ring
  have hCtRadius : Ct * a ≤ Ct * r :=
    mul_le_mul_of_nonneg_left hr.1 hCt
  have hTraceRad :
      ‖(r : ℂ) * (Z * Y)‖ ≤ (b + 1) * G * Ct := by
    apply (mul_le_mul_iff_of_pos_left hrp).mp
    calc
      r * ‖(r : ℂ) * (Z * Y)‖ =
          ‖(r : ℂ) ^ 2 * (Z * Y)‖ := hTraceRadNorm.symm
      _ ≤ ((b + 1) * G) * (Ct * a) := hTraceRad2Bound
      _ ≤ ((b + 1) * G) * (Ct * r) :=
        mul_le_mul_of_nonneg_left hCtRadius hYCoef
      _ = r * ((b + 1) * G * Ct) := by ring
  let R : ℂ := actualOriginMatchedRegularCoeff K a b F U DU
  let X : ℂ := originPhysicalSlope K.x K.dx r
  let J : ℝ := a * ‖DU‖ + (a + 1) * ‖U‖
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hRegular : ‖R‖ ≤ G * J := by
    simpa only [R, J] using
      (actual_Hartree_matched_regular_coefficient_no_left_radius_loss
        K a b G ha hab hb.le
        (fun x hx => ⟨(hbound x hx).1, (hbound x hx).2.1⟩)
        F U DU)
  have hRegularPhysical : ‖X‖ ≤ 2 * ((D + 1) * G) * r := by
    simpa only [X] using
      (origin_kummer_regular_physical_bound K D G hD hG hb.le
        hcoeff hbound r ⟨hrp, hr.2⟩).2
  have hRegularRad :
      ‖(r : ℂ) * (R * X)‖ ≤
        2 * (D + 1) * G ^ 2 * b ^ 2 * J := by
    have hSq : r ^ 2 ≤ b ^ 2 :=
      pow_le_pow_left₀ hrp.le hr.2 2
    have hCoef : 0 ≤ 2 * (D + 1) * G ^ 2 * J := by positivity
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrp]
    calc
      r * (‖R‖ * ‖X‖) ≤
          r * ((G * J) * (2 * ((D + 1) * G) * r)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hRegular hRegularPhysical
            (norm_nonneg _) (mul_nonneg hG hJ)) hrp.le
      _ = (2 * (D + 1) * G ^ 2 * J) * r ^ 2 := by ring
      _ ≤ (2 * (D + 1) * G ^ 2 * J) * b ^ 2 :=
        mul_le_mul_of_nonneg_left hSq hCoef
      _ = 2 * (D + 1) * G ^ 2 * b ^ 2 * J := by ring
  have hExact :=
    actual_Hartree_matched_slope_zero_left_plus_original_jet_exact
      K a b C hab hK F U DU hCompatible r
  have hTriangle :
      ‖(r : ℂ) * actualOriginMatchedKummerSlope K a b F U DU r‖ ≤
        ‖(r : ℂ) * actualOriginMatchedKummerSlope K a b F 0 0 r‖ +
        ‖(r : ℂ) * (Z * Y)‖ +
        ‖(r : ℂ) * (R * X)‖ := by
    rw [hExact]
    change ‖((r : ℂ) * actualOriginMatchedKummerSlope K a b F 0 0 r +
        (r : ℂ) * (Z * Y)) + (r : ℂ) * (R * X)‖ ≤ _
    calc
      _ ≤ ‖(r : ℂ) * actualOriginMatchedKummerSlope K a b F 0 0 r +
          (r : ℂ) * (Z * Y)‖ + ‖(r : ℂ) * (R * X)‖ :=
        norm_add_le _ _
      _ ≤ (‖(r : ℂ) * actualOriginMatchedKummerSlope K a b F 0 0 r‖ +
            ‖(r : ℂ) * (Z * Y)‖) + ‖(r : ℂ) * (R * X)‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
  have hFinal := hTriangle.trans
    (add_le_add (add_le_add hZero hTraceRad) hRegularRad)
  simpa only [Z, Y, R, X, J] using hFinal

end HBL.TypeIIDynamicSelection
