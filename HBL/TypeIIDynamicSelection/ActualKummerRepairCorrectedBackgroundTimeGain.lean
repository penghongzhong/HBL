import HBL.TypeIIDynamicSelection.ActualKummerMovingCorrectedBackgroundPDE
import HBL.TypeIIDynamicSelection.ActualKummerRepairCenterTimeGainSqrtRadius
import HBL.TypeIIDynamicSelection.ActualKummerRepairFullDensityFeedback
import HBL.TypeIIDynamicSelection.ActualKummerRepairBackgroundEnvelope
import Mathlib.Tactic

/-!
# Full Hartree repair feedback after a genuine nonlinear profile correction

The physical background in a finite Hartree recursion is V_c + Z_ell + H,
not merely V_c + Z_ell. The replacement field changes the FULL quartic
density of this corrected background. A bubble envelope for H increases the
shell monopole constant explicitly by 2*CH.

The exact sqrt-clock estimate then controls the complete corrected density
feedback at order rho + kappa_center, with all D, D², D³, D⁴ contributions.
The correction H is never declared to vanish in the repair annulus.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Positive radius and the actual shrinking physical scale imply that
a bubble envelope for an existing correction costs only (1+aR)^(-1)
on the moving outer Kummer shell. -/
theorem actual_Hartree_bubble_corrected_Kummer_shell_bound
    (ell a R CH y : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha : 0 < a) (hR : 0 < R) (hCH : 0 ≤ CH)
    (hXlow : actualHartreeSlowInnerRadius ell ≤ a * R)
    (hy : y ∈ Ioc (a * R) (2 * a * R))
    (H : ℝ → ℂ)
    (hH : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u) :
    ‖H y‖ ≤ (2 * CH) / (1 + a * R) := by
  let X : ℝ := a * R
  have hLone : 1 ≤ actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have hXone : 1 ≤ X := hLone.trans hXlow
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hypos : 0 < y := hXpos.trans hy.1
  have hSqrtSq : (Real.sqrt (1 + y ^ 2)) ^ 2 = 1 + y ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hSqrtNonneg : 0 ≤ Real.sqrt (1 + y ^ 2) :=
    Real.sqrt_nonneg _
  have hSqrt : y ≤ Real.sqrt (1 + y ^ 2) := by
    nlinarith only [hSqrtSq, hSqrtNonneg, hypos.le]
  have hBubble : bubble y ≤ y⁻¹ := by
    change (Real.sqrt (1 + y ^ 2))⁻¹ ≤ y⁻¹
    exact inv_anti₀ hypos hSqrt
  have hDen : 0 < 1 + X := by linarith
  have hInv :
      y⁻¹ ≤ 2 / (1 + X) := by
    rw [← one_div]
    apply (div_le_div_iff₀ hypos hDen).2
    have hOne : 1 + X ≤ 2 * y := by
      have hLower : X ≤ y := hy.1.le
      linarith
    simpa only [one_mul] using hOne
  calc
    ‖H y‖ ≤ CH * bubble y := hH y hypos
    _ ≤ CH * y⁻¹ :=
      mul_le_mul_of_nonneg_left hBubble hCH
    _ ≤ CH * (2 / (1 + X)) :=
      mul_le_mul_of_nonneg_left hInv hCH
    _ = (2 * CH) / (1 + a * R) := by
      dsimp [X]
      ring

/-- TRUE monopole + whole radiation + an existing nonlinear correction H
has a controlled common Kummer shell envelope. -/
theorem actual_Hartree_Kummer_corrected_background_shell_envelope
    (ell a R B A CH c y : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hc : |c| ≤ 1)
    (hXlow : actualHartreeSlowInnerRadius ell ≤ a * R)
    (z H : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hH : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u)
    (hy : y ∈ Ioc (a * R) (2 * a * R)) :
    ‖((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y‖ ≤
      actualKummerRepairAbstractShellEnvelope ell (a * R)
        (2 + 9 * monopoleRadialBoundConstant + 2 * CH)
        (2 * (B + A)) := by
  have hOriginal :=
    actual_Hartree_Kummer_repair_background_shell_envelope
      ell a R B A c y hell ha hR hB hA hc z hSup hStrauss hy
  have hHCorr :=
    actual_Hartree_bubble_corrected_Kummer_shell_bound
      ell a R CH y hell hellOne ha hR hCH hXlow hy H hH
  calc
    ‖((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y‖ ≤
      ‖(actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y‖ + ‖H y‖ :=
      norm_add_le _ _
    _ ≤ actualHartreeKummerRepairBackgroundEnvelope ell a R B A +
        (2 * CH) / (1 + a * R) :=
      add_le_add hOriginal hHCorr
    _ = actualKummerRepairAbstractShellEnvelope ell (a * R)
        (2 + 9 * monopoleRadialBoundConstant + 2 * CH)
        (2 * (B + A)) := by
      dsimp [actualHartreeKummerRepairBackgroundEnvelope,
        actualKummerRepairAbstractShellEnvelope]
      ring

/-- Explicit center polynomial for the corrected Hartree background;
the new correction contributes to the true cubic and quadratic
shell-density terms, not as a formal source label. -/
def actualKummerRepairCorrectedTimeConstant
    (B A CH CX CD : ℝ) : ℝ :=
  let M := 2 + 9 * monopoleRadialBoundConstant + 2 * CH
  let S := 2 * (B + A)
  16 * (M ^ 3 + S ^ 3) * CD +
    12 * (M ^ 2 + S ^ 2) * CD ^ 2 +
    4 * M * CD ^ 3 +
    4 * CX * S * CD ^ 3 +
    CX * CD ^ 4

/-- The entire nonlocal quartic density feedback of the replacement tail
against V_c+Z_ell+H has an actual positive time gain. Neither the
correction H, its mixed density terms nor the full D^3,D^4 polynomial
are suppressed. -/
theorem actual_Hartree_Kummer_repair_corrected_background_full_potential_time_gain
    (ell a R B A CH c s beta rho CX CD r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (ha : 0 < a) (hR : 0 < R)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hc : |c| ≤ 1)
    (hs : 1 ≤ s) (hbeta : 1 / 2 < beta)
    (hrho : (1 / 2 + actualKummerRepairCenterTimeGain beta) / 2 ≤ rho)
    (htrap : ell ≤ s ^ (-beta))
    (hXlow : actualHartreeSlowInnerRadius ell ≤ a * R)
    (hCX : 0 ≤ CX) (hXup : a * R ≤ CX * s ^ (1 / 2 : ℝ))
    (hCD : 0 ≤ CD)
    (p q : ℂ)
    (hDtime : ‖p‖ + R * ‖q‖ ≤ CD * s ^ (-rho))
    (z H : ℝ → ℂ) (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hHCorr : ∀ u : ℝ, 0 < u → ‖H u‖ ≤ CH * bubble u)
    (hr : 0 < r) (hrOne : r ≤ 1) (hsep : 2 * r ≤ a * R) :
    let U : ℝ → ℂ := fun y =>
      ((actualMomentLockedCore c y : ℂ) +
        rescalePhysicalRadiation ell z y) + H y
    let F := actualKummerPhysicalRepairOuterDensityDifference U a R p q
    let Ct := actualKummerRepairCorrectedTimeConstant B A CH CX CD
    let k := actualKummerRepairCenterTimeGain beta
    |radialHartreeExteriorPotential F (a * R) r| ≤
      (2 * (4 * Real.pi * hartreeKappa) * Ct) *
        s ^ (-(rho + k)) := by
  dsimp only
  let X : ℝ := a * R
  let M : ℝ := 2 + 9 * monopoleRadialBoundConstant + 2 * CH
  let S : ℝ := 2 * (B + A)
  let D0 : ℝ := ‖p‖ + R * ‖q‖
  let A0 : ℝ := actualKummerRepairAbstractShellEnvelope ell X M S
  let P0 : ℝ := actualKummerRepairDensityPolynomial A0 D0
  let Ct : ℝ := actualKummerRepairCorrectedTimeConstant B A CH CX CD
  let k : ℝ := actualKummerRepairCenterTimeGain beta
  let U : ℝ → ℂ := fun y =>
    ((actualMomentLockedCore c y : ℂ) +
      rescalePhysicalRadiation ell z y) + H y
  let F : ℝ → ℝ :=
    actualKummerPhysicalRepairOuterDensityDifference U a R p q
  have hMono : 0 ≤ monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hD0 : 0 ≤ D0 := by dsimp [D0]; positivity
  have hXpos : 0 < X := by dsimp [X]; exact mul_pos ha hR
  have hLone : 1 ≤ actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have hXone : 1 ≤ X := hLone.trans hXlow
  have hA0 : 0 ≤ A0 := by
    dsimp [A0, actualKummerRepairAbstractShellEnvelope]
    positivity
  have hP0 : 0 ≤ P0 :=
    actual_Kummer_repair_density_polynomial_nonneg A0 D0 hA0 hD0
  have hCt : 0 ≤ Ct := by
    dsimp [Ct, actualKummerRepairCorrectedTimeConstant, M, S]
    positivity
  have hCenterRaw :=
    actual_Kummer_repair_full_center_time_gain_sqrt_radius
      ell X M S D0 s beta rho CX CD
      hell hellOne hXlow hXup hM hS hD0 hCX hCD
      hs hbeta hrho htrap hDtime
  have hCenter :
      X * P0 ≤ Ct * s ^ (-(rho + k)) := by
    dsimp [P0, A0, Ct, k, X, M, S,
      actualKummerRepairCorrectedTimeConstant,
      actualKummerRepairAbstractShellEnvelope] at hCenterRaw ⊢
    simpa only [mul_assoc] using hCenterRaw
  have hCoreMeas :
      Measurable (fun y : ℝ => (actualMomentLockedCore c y : ℂ)) := by
    change Measurable
      (fun y : ℝ => (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c y : ℂ))
    exact Complex.continuous_ofReal.measurable.comp
      (actual_Hartree_moving_monopole_measurable c)
  have hZmeas : Measurable (rescalePhysicalRadiation ell z) := by
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hUmeas : Measurable U :=
    (hCoreMeas.add hZmeas).add hHmeas
  have hUShell : ∀ y ∈ Ioc X (2 * X), ‖U y‖ ≤ A0 := by
    intro y hy
    have hy' : y ∈ Ioc (a * R) (2 * a * R) := by
      simpa only [X, mul_assoc] using hy
    simpa only [U, A0, X, M, S] using
      actual_Hartree_Kummer_corrected_background_shell_envelope
        ell a R B A CH c y hell hellOne ha hR
        hB hA hCH hc hXlow z H hSup hStrauss hHCorr hy'
  have hCenterRaw' :=
    actual_Kummer_physical_repair_outer_density_center_bound
      U hUmeas a R A0 ha hR hA0 p q
      (by
        intro y hy
        exact hUShell y (by simpa only [X, mul_assoc] using hy))
  have hGapRaw' :=
    actual_Kummer_physical_repair_outer_density_core_gap
      U hUmeas a R A0 r ha hR hA0 hr hsep p q
      (by
        intro y hy
        exact hUShell y (by simpa only [X, mul_assoc] using hy))
  have hHartree : 0 ≤ 4 * Real.pi * hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hCenterRawBound :
      |radialHartreeExteriorCenter F X| ≤
        (4 * Real.pi * hartreeKappa) * (X * P0) := by
    simpa only [F, X, U, P0, D0] using hCenterRaw'
  have hGapRawBound :
      |radialHartreeExteriorPotential F X r -
          radialHartreeExteriorCenter F X| ≤
        (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / X)) * P0 := by
    simpa only [F, X, U, P0, D0] using hGapRaw'
  have hCenterTime :
      |radialHartreeExteriorCenter F X| ≤
        ((4 * Real.pi * hartreeKappa) * Ct) *
          s ^ (-(rho + k)) := by
    calc
      _ ≤ (4 * Real.pi * hartreeKappa) * (X * P0) := hCenterRawBound
      _ ≤ (4 * Real.pi * hartreeKappa) *
          (Ct * s ^ (-(rho + k))) :=
        mul_le_mul_of_nonneg_left hCenter hHartree
      _ = _ := by ring
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg r]
  have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hXone
  have hratio : r ^ 2 * (1 / X) ≤ X := by
    have hq : r ^ 2 / X ≤ X := by
      apply (div_le_iff₀ hXpos).2
      have : r ^ 2 ≤ X ^ 2 := hr2.trans hXsq
      simpa only [pow_two] using this
    simpa only [div_eq_mul_inv, one_mul] using hq
  have hGapToCenterPoly :
      (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / X)) * P0 ≤
        (4 * Real.pi * hartreeKappa) * (X * P0) := by
    have hratio' :
        (4 * Real.pi * hartreeKappa) * (r ^ 2 * (1 / X)) ≤
          (4 * Real.pi * hartreeKappa) * X :=
      mul_le_mul_of_nonneg_left hratio hHartree
    have hp := mul_le_mul_of_nonneg_right hratio' hP0
    ring_nf at hp ⊢
    exact hp
  have hGapTime :
      |radialHartreeExteriorPotential F X r -
          radialHartreeExteriorCenter F X| ≤
        ((4 * Real.pi * hartreeKappa) * Ct) *
          s ^ (-(rho + k)) := by
    calc
      _ ≤ (4 * Real.pi * hartreeKappa * r ^ 2 * (1 / X)) * P0 :=
        hGapRawBound
      _ ≤ (4 * Real.pi * hartreeKappa) * (X * P0) :=
        hGapToCenterPoly
      _ ≤ (4 * Real.pi * hartreeKappa) *
          (Ct * s ^ (-(rho + k))) :=
        mul_le_mul_of_nonneg_left hCenter hHartree
      _ = _ := by ring
  calc
    |radialHartreeExteriorPotential F X r| =
        |(radialHartreeExteriorPotential F X r -
            radialHartreeExteriorCenter F X) +
          radialHartreeExteriorCenter F X| := by
      congr 1
      ring
    _ ≤ |radialHartreeExteriorPotential F X r -
          radialHartreeExteriorCenter F X| +
        |radialHartreeExteriorCenter F X| :=
      abs_add_le _ _
    _ ≤ ((4 * Real.pi * hartreeKappa) * Ct) *
          s ^ (-(rho + k)) +
        ((4 * Real.pi * hartreeKappa) * Ct) *
          s ^ (-(rho + k)) :=
      add_le_add hGapTime hCenterTime
    _ = (2 * (4 * Real.pi * hartreeKappa) * Ct) *
        s ^ (-(rho + k)) := by ring

end HBL.TypeIIDynamicSelection
