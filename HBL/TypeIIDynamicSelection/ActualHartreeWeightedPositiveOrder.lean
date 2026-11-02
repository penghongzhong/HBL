import HBL.TypeIIDynamicSelection.ActualHartreeNonlocalWeightedQuantitative
import HBL.TypeIIDynamicSelection.ActualHartreeMomentRadiusWindow
import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import Mathlib.Tactic

/-!
# Strict positive physical Fredholm gain from TRUE Hartree moving cutoff

The first upper bound in the original weighted L^(2,sigma) space is
already kernel-checked. Its geometric radius loss is explicit:
  <2R>^sigma * ell^2 * sqrt(ell) * sqrt(2R).
Here we prove by REAL-POWER arithmetic, for 0<ell<=1,
0<=sigma<2 and the actual whole-radiation moment radius
R <= Q/ell, that
  <2R>^sigma * ell^2 * sqrt(ell) * sqrt(2R)
   <= sqrt(2Q) * (1+(2Q)^2)^(sigma/2) * ell^(2-sigma).

Thus for 3/2<sigma<2 the COMPLETE quartic Riesz cutoff error
is genuinely small with positive order 2-sigma>0 in the
manuscript weighted Fredholm norm, not only pointwise.

No artificial rate for ell, no abstract source order, no local
cubic substitution, and no fixed annulus Kummer shortcut.
The three-domain Kummer/remote source cancellation remains necessary
for formal acceptance of the complete original prop 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The real scale geometry is the missing quantitative bridge:
physical support radius R<=Q/ell converts sigma-weight + sqrt(R)
into a positive source length power 2-sigma. -/
theorem actual_Hartree_weighted_cutoff_volume_ell_positive_order
    (ell R Q sigma : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hR : 0 < R) (hQ : 0 < Q)
    (hRmax : R ≤ Q / ell)
    (hsigma : 0 ≤ sigma) :
    (affineJapaneseWeight sigma (2 * R) *
       (ell ^ 2 * Real.sqrt ell)) * Real.sqrt (2 * R) ≤
      ((1 + (2 * Q) ^ 2) ^ (sigma / 2) *
        Real.sqrt (2 * Q)) * ell ^ (2 - sigma) := by
  have hScaledRadius : ell * R ≤ Q := by
    calc
      ell * R ≤ ell * (Q / ell) :=
        mul_le_mul_of_nonneg_left hRmax hell.le
      _ = Q := by field_simp [hell.ne']
  have hScaledTwo : ell * (2 * R) ≤ 2 * Q := by
    nlinarith [hScaledRadius]
  have hEllSq : ell ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr hellOne)]
  have hScaledSquare :
      (ell * (2 * R)) ^ 2 ≤ (2 * Q) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hScaledTwo 2
  have hBase :
      ell ^ 2 * (1 + (2 * R) ^ 2) ≤
        1 + (2 * Q) ^ 2 := by
    nlinarith [hScaledSquare, hEllSq]
  have hSigmaHalf : 0 ≤ sigma / 2 := by linarith
  have hBasePower :
      (ell ^ 2 * (1 + (2 * R) ^ 2)) ^ (sigma / 2) ≤
        (1 + (2 * Q) ^ 2) ^ (sigma / 2) :=
    Real.rpow_le_rpow (by positivity) hBase hSigmaHalf
  have hRealPow :
      (ell ^ 2) ^ (sigma / 2) = ell ^ sigma := by
    calc
      (ell ^ 2) ^ (sigma / 2) =
          (ell ^ (2 : ℝ)) ^ (sigma / 2) := by
            rfl
      _ = ell ^ ((2 : ℝ) * (sigma / 2)) :=
        (Real.rpow_mul hell.le 2 (sigma / 2)).symm
      _ = ell ^ sigma := by congr 1; ring
  have hWeight :
      ell ^ sigma * affineJapaneseWeight sigma (2 * R) ≤
        (1 + (2 * Q) ^ 2) ^ (sigma / 2) := by
    unfold affineJapaneseWeight
    calc
      ell ^ sigma * (1 + (2 * R) ^ 2) ^ (sigma / 2) =
          (ell ^ 2) ^ (sigma / 2) *
            (1 + (2 * R) ^ 2) ^ (sigma / 2) := by
              rw [hRealPow]
      _ = (ell ^ 2 * (1 + (2 * R) ^ 2)) ^ (sigma / 2) :=
        (Real.mul_rpow (sq_nonneg ell) (by positivity)).symm
      _ ≤ (1 + (2 * Q) ^ 2) ^ (sigma / 2) := hBasePower
  have hSqrt :
      Real.sqrt ell * Real.sqrt (2 * R) ≤ Real.sqrt (2 * Q) := by
    calc
      Real.sqrt ell * Real.sqrt (2 * R) =
          Real.sqrt (ell * (2 * R)) :=
        (Real.sqrt_mul hell.le _).symm
      _ ≤ Real.sqrt (2 * Q) := Real.sqrt_le_sqrt hScaledTwo
  have hCombined :
      (ell ^ sigma * affineJapaneseWeight sigma (2 * R)) *
          (Real.sqrt ell * Real.sqrt (2 * R)) ≤
        (1 + (2 * Q) ^ 2) ^ (sigma / 2) *
          Real.sqrt (2 * Q) :=
    mul_le_mul hWeight hSqrt (by positivity) (by positivity)
  have hPowTwo : ell ^ (2 - sigma) * ell ^ sigma = ell ^ 2 := by
    calc
      _ = ell ^ ((2 - sigma) + sigma) :=
        (Real.rpow_add hell (2 - sigma) sigma).symm
      _ = ell ^ (2 : ℝ) := by congr 1; ring
      _ = ell ^ 2 := Real.rpow_natCast ell 2
  calc
    (affineJapaneseWeight sigma (2 * R) *
       (ell ^ 2 * Real.sqrt ell)) * Real.sqrt (2 * R) =
        ell ^ (2 - sigma) *
          ((ell ^ sigma * affineJapaneseWeight sigma (2 * R)) *
            (Real.sqrt ell * Real.sqrt (2 * R))) := by
          rw [← hPowTwo]
          ring
    _ ≤ ell ^ (2 - sigma) *
        ((1 + (2 * Q) ^ 2) ^ (sigma / 2) * Real.sqrt (2 * Q)) :=
      mul_le_mul_of_nonneg_left hCombined (by positivity)
    _ = ((1 + (2 * Q) ^ 2) ^ (sigma / 2) *
        Real.sqrt (2 * Q)) * ell ^ (2 - sigma) := by ring

/-- TRUE nonlocal inverse-square Hartree Riesz source has uniformly
positive power 2-sigma in the original weighted Fredholm norm,
when the physical quartic moment is bounded below by m0>0. -/
theorem actual_Hartree_physical_nonlocal_Riesz_positive_Fredholm_gain
    (ell m m0 B D sigma : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hm0 : 0 < m0) (hm0m : m0 ≤ m)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hSigmaLo : 3 / 2 < sigma) (hSigmaHi : sigma < 2)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hzAmp : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hzQuartic : ∀ u : ℝ, 0 < u →
      ‖z u‖ ^ 4 ≤ D * bubble u ^ 2) :
    (eLpNorm
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualHartreeNonlocalCutoffError
          (actualHartreeMomentCutoffRadius ell m) ell z r‖)
        2 halfLineMeasure).toReal ≤
      ((2 * radialHartreeRowBoundConstant * D * B ^ 3) *
        ((1 + (2 * (4 / (hartreeKappa * m0))) ^ 2) ^ (sigma / 2) *
           Real.sqrt (2 * (4 / (hartreeKappa * m0))))) *
        ell ^ (2 - sigma) := by
  let R : ℝ := actualHartreeMomentCutoffRadius ell m
  let Q : ℝ := 4 / (hartreeKappa * m0)
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hm : 0 < m := hm0.trans_le hm0m
  have hR : 0 < R := by
    dsimp [R, actualHartreeMomentCutoffRadius]
    positivity
  have hRadius : R ≤ Q / ell :=
    actual_Hartree_positive_moment_upper_cutoff_radius
      ell m m0 hell hm0 hm0m
  have hSigma : 0 ≤ sigma := by linarith
  have hGeo :=
    actual_Hartree_weighted_cutoff_volume_ell_positive_order
      ell R Q sigma hell hellOne hR hQ hRadius hSigma
  have hSource := actual_Hartree_nonlocal_physical_weighted_L2_quantitative
    ell R B D sigma hell hR hB hD hSigmaLo hSigmaHi
      z hz hzAmp hzQuartic
  have hCoeff : 0 ≤ 2 * radialHartreeRowBoundConstant * D * B ^ 3 := by
    have hK := radialHartreeRowBoundConstant_pos
    positivity
  change (eLpNorm
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualHartreeNonlocalCutoffError R ell z r‖)
      2 halfLineMeasure).toReal ≤
      ((2 * radialHartreeRowBoundConstant * D * B ^ 3) *
        ((1 + (2 * Q) ^ 2) ^ (sigma / 2) *
          Real.sqrt (2 * Q))) * ell ^ (2 - sigma)
  calc
    _ ≤ (affineJapaneseWeight sigma (2 * R) *
          ((2 * radialHartreeRowBoundConstant * D * B ^ 3) *
            ell ^ 2 * Real.sqrt ell)) * Real.sqrt (2 * R) := hSource
    _ = (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
          ((affineJapaneseWeight sigma (2 * R) *
            (ell ^ 2 * Real.sqrt ell)) * Real.sqrt (2 * R)) := by ring
    _ ≤ (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
          (((1 + (2 * Q) ^ 2) ^ (sigma / 2) *
             Real.sqrt (2 * Q)) * ell ^ (2 - sigma)) :=
      mul_le_mul_of_nonneg_left hGeo hCoeff
    _ = ((2 * radialHartreeRowBoundConstant * D * B ^ 3) *
         ((1 + (2 * Q) ^ 2) ^ (sigma / 2) *
           Real.sqrt (2 * Q))) * ell ^ (2 - sigma) := by ring

/-- The source gain exponent is genuinely positive in precisely
the original Fredholm range 3/2 < sigma < 2. -/
theorem actual_Hartree_Fredholm_exponent_strictly_positive
    (sigma : ℝ) (_hLower : 3 / 2 < sigma) (hUpper : sigma < 2) :
    0 < 2 - sigma := by linarith

end HBL.TypeIIDynamicSelection
