import HBL.TypeIIDynamicSelection.ActualHartreeMatchedRegularJetNoRadiusLoss
import HBL.KummerOriginBasis.AnnulusBound
import Mathlib.Tactic

/-!
# Exact physical Cramer matched weighted first profile, no singular-basis loss

Once the ORIGINAL two-real-component Hartree compatibility is zero, the
singular homogeneous coefficient of the actual Cramer-matched Kummer
profile is EXACTLY zero. The full profile is the original inhomogeneous
Green field plus the original regular homogeneous coefficient times x/r.

If the original Green field has already been bounded in the radius-weighted
norm (as established separately from the true quartic Hartree Riesz
source), its contribution is used unchanged. The regular Cramer term
has its genuine exact Wronskian cancellation with a uniform bound on the
regularized IVP modes. The possibly singular annulus OriginBasisOn
constant is derived here for the exact identity, and is NOT present
in the output estimate.

No independent forcing supremum or arbitrary homogeneous amplitude is
introduced. The main theorem must invoke this with its actual
source-selected Green and physical Fredholm Cauchy data.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_matched_from_weighted_original_Green_and_Cramer
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hG : 0 ≤ G)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ) (U DU : ℂ)
    (hCompatible : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (hWeightedGreen : ∀ r ∈ Icc a b,
      ‖(r : ℂ) * originGreenValue K a b F r‖ ≤ H)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b F U DU r‖ ≤
      H + G ^ 2 * (a * ‖DU‖ + (a + 1) * ‖U‖) := by
  let C : ℝ := G * (1 / a + 1 / a ^ 2) + b ^ 2 + 1
  have hK : OriginBasisOn K a b C :=
    origin_kummer_annulus_bound K a b G ha hb hG hbound
  have hSing : actualOriginMatchedSingularCoeff K a b F U DU = 0 :=
    (actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F U DU).trans
      hCompatible
  have hSmall : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.1, (hbound x hx).2.2.1⟩
  have hRegular :=
    actual_Hartree_matched_regular_part_weighted_no_radius_loss
      K a b G ha hab hb.le hG hSmall F U DU r hr
  have hSplit :
      (r : ℂ) * actualOriginMatchedKummerValue K a b F U DU r =
        (r : ℂ) * originGreenValue K a b F r +
          (r : ℂ) * (actualOriginMatchedRegularCoeff K a b F U DU *
            originPhysicalValue K.x r) := by
    unfold actualOriginMatchedKummerValue
    rw [hSing]
    ring
  rw [hSplit]
  exact (norm_add_le _ _).trans (add_le_add (hWeightedGreen r hr) hRegular)

end HBL.TypeIIDynamicSelection
