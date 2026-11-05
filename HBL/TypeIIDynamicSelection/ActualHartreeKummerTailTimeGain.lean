import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import Mathlib.Tactic

/-!
# True Kummer regular-tail time gain

The compatibility/Kummer analysis already proves a genuine regular Green
tail factor L^(-3/8).  With the physical slow-inner radius
L=ell^(-1/16), this is exactly ell^(3/128).

Under the visible scale bootstrap ell(s) <= s^(-beta), this supplies the
strict positive time gain 3 beta / 128.  This is weaker than the old
structural Frobenius half-order, but it is an actual physical producer.
A finite recursion needs only a positive fixed gain, so this is the safe
replacement when physicalizing the old structural ledger.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualHartreeKummerTailTimeGain (beta : ℝ) : ℝ :=
  3 * beta / 128

theorem actual_Hartree_Kummer_tail_time_gain_positive
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < actualHartreeKummerTailTimeGain beta := by
  unfold actualHartreeKummerTailTimeGain
  positivity

theorem actual_Hartree_slow_inner_tail_factor_exact
    (ell : ℝ) (hell : 0 < ell) :
    actualHartreeSlowInnerRadius ell ^ (-(3 / 8 : ℝ)) =
      ell ^ (3 / 128 : ℝ) := by
  unfold actualHartreeSlowInnerRadius
  calc
    (ell ^ (-(1 / 16 : ℝ))) ^ (-(3 / 8 : ℝ)) =
        ell ^ ((-(1 / 16 : ℝ)) * (-(3 / 8 : ℝ))) :=
      (Real.rpow_mul hell.le (-(1 / 16 : ℝ)) (-(3 / 8 : ℝ))).symm
    _ = ell ^ (3 / 128 : ℝ) := by norm_num

/-- The actual Kummer regular-tail factor has a strict positive
renormalized-time order in the same bootstrap trap used elsewhere. -/
theorem actual_Hartree_trapped_Kummer_tail_time_gain
    (s ell beta : ℝ)
    (hs : 1 ≤ s) (hell : 0 < ell)
    (htrap : ell ≤ s ^ (-beta)) :
    actualHartreeSlowInnerRadius ell ^ (-(3 / 8 : ℝ)) ≤
      s ^ (-actualHartreeKummerTailTimeGain beta) := by
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hpow :
      ell ^ (3 / 128 : ℝ) ≤
        (s ^ (-beta)) ^ (3 / 128 : ℝ) :=
    Real.rpow_le_rpow hell.le htrap (by norm_num)
  have hsPow :
      (s ^ (-beta)) ^ (3 / 128 : ℝ) =
        s ^ (-actualHartreeKummerTailTimeGain beta) := by
    calc
      _ = s ^ ((-beta) * (3 / 128 : ℝ)) :=
        (Real.rpow_mul hs0 (-beta) (3 / 128 : ℝ)).symm
      _ = s ^ (-actualHartreeKummerTailTimeGain beta) := by
        congr 1
        unfold actualHartreeKummerTailTimeGain
        ring
  rw [actual_Hartree_slow_inner_tail_factor_exact ell hell]
  exact hpow.trans_eq hsPow

/-- Direct specialization of the already strict true-Hartree regular Green
tail estimate to the physical slow radius and then to its positive time
gain. No endpoint estimate or Kummer coefficient is assumed. -/
theorem actual_Hartree_scaled_Kummer_regular_Green_positive_time_gain
    {mu theta scale : ℝ} (K : HBL.Profile.Kummer.OriginKummerPair mu theta scale)
    (D G R a B A ell c s beta : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (ha : 0 < a)
    (hOrder : actualHartreeSlowInnerRadius ell / a ≤ R)
    (hRscale : R < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖HBL.Profile.Kummer.originFirstCoeff r‖ +
        ‖HBL.Profile.Kummer.originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (hs : 1 ≤ s) (htrap : ell ≤ s ^ (-beta)) :
    let F := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
    ‖HBL.Profile.Kummer.originGreenCoeffB K
        (actualHartreeSlowInnerRadius ell / a) F R‖ ≤
      (8 / 3 : ℝ) * G *
        (actualHartreePhysicalWeightedSourceConstant B A *
          ell ^ (1 / 8 : ℝ)) *
        s ^ (-actualHartreeKummerTailTimeGain beta) := by
  dsimp only
  have hLone : 1 ≤ actualHartreeSlowInnerRadius ell := by
    unfold actualHartreeSlowInnerRadius
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hell hellOne (by norm_num)
  have hraw :=
    actual_Hartree_scaled_Kummer_regular_Green_tail_gain
      K D G (actualHartreeSlowInnerRadius ell) R a B A ell c
      hD hG hLone ha hOrder hRscale hcoeff hbound
      hB hA hell hellOne hc z hz hSup hStrauss
  have htime :=
    actual_Hartree_trapped_Kummer_tail_time_gain
      s ell beta hs hell htrap
  have hcoef : 0 ≤
      (8 / 3 : ℝ) * G *
        (actualHartreePhysicalWeightedSourceConstant B A *
          ell ^ (1 / 8 : ℝ)) := by
    have hK :=
      actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
    positivity
  exact hraw.trans
    (mul_le_mul_of_nonneg_left htime hcoef)

end HBL.TypeIIDynamicSelection
