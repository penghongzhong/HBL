import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import HBL.TypeIIDynamicSelection.ActualHartreeExactGreenMomentsMovingSpectral
import Mathlib.Tactic

/-!
# Genuine original nonlocal Hartree Riesz source: whole Green field without basis-radius loss

The origin-normalized inverse-square quartic 3D Hartree source has TWO
true unswapped Wronskian Green coefficients, each strictly verified to
be O(G * Cphys * ell^(1/8) * L^(-3/8)), at EVERY normalized radius.
A separate exact moment identity multiplies the FULL Green field by
radius before taking norms, replacing the nonuniform physical
OriginBasisOn bound with globally controlled regularized origin modes.

The conclusion therefore controls the complete ORIGINAL nonlocal
source-driven Green field, not only the singular coefficient or one
endpoint, by (16/3) G^2 Cphys ell^(1/8) L^(-3/8).
There is NO matching-radius inverse power and no assumption that
the Green field is small. The real selected modulation-speed source,
matched Fredholm jet and full nonlinear four-region PDE are separate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The exact 3D critical Hartree Riesz source gives a genuine
radius-weighted bound on the WHOLE original Green field with no
shrinking-annulus OriginBasisOn constant, at EVERY r in [L/a,R]. -/
theorem actual_Hartree_original_source_full_Green_weighted_no_radius_loss
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G L R a B A ell c : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hL : 1 ≤ L) (ha : 0 < a)
    (hOrder : L / a ≤ R) (hRscale : R < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    (r : ℝ) (hr : r ∈ Icc (L / a) R) :
    let F0 : ℝ → ℂ :=
      fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
    let M : ℝ :=
      actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
    ‖(r : ℂ) * originGreenValue K (L / a) R F0 r‖ ≤
      G * (2 * (((8 / 3 : ℝ) * G * M) * L ^ (-(3 / 8 : ℝ)))) := by
  dsimp only
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let M : ℝ :=
    actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  let C0 : ℝ := ((8 / 3 : ℝ) * G * M) * L ^ (-(3 / 8 : ℝ))
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < L / a := div_pos hLp ha
  have hCoefficients :
      ‖originGreenCoeffA K R F0 r‖ ≤ C0 ∧
        ‖originGreenCoeffB K (L / a) F0 r‖ ≤ C0 := by
    simpa only [F0, C0, M] using
      (actual_Hartree_scaled_Kummer_both_Green_coefficients_uniform
        K D G L R a B A ell c hD hG hL ha hOrder hRscale
        hcoeff hbound hB hA hell hellOne hc z hz hSup hStrauss r hr)
  have hWeight :=
    actual_Hartree_origin_Green_weighted_exact_moments
      K (L / a) R G hr0 hOrder hRscale.le
      (fun x hx => ⟨(hbound x hx).1, (hbound x hx).2.2.1⟩)
      F0 r hr
  have hSum :
      ‖originGreenCoeffA K R F0 r‖ +
          ‖originGreenCoeffB K (L / a) F0 r‖ ≤ 2 * C0 := by
    linarith only [hCoefficients.1, hCoefficients.2]
  have hFull :
      ‖(r : ℂ) * originGreenValue K (L / a) R F0 r‖ ≤
        G * (2 * C0) :=
    hWeight.trans (mul_le_mul_of_nonneg_left hSum hG)
  simpa only [F0, C0, M] using hFull

end HBL.TypeIIDynamicSelection
