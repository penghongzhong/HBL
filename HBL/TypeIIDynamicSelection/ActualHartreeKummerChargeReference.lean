import HBL.TypeIIDynamicSelection.ActualKummerFullSourceTransfer
import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedInnerChargeGain
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInteractionMeasurable
import Mathlib.Tactic

/-!
Full physical Hartree source -> uniformly controlled forced-charge reference.
The spatial coordinate is explicit: r_physical=a*r_Kummer, with the exact
Laplacian source factor a². The three original Riesz potentials, ten terms,
measurability and both affine charges are obtained from the accepted code.
No source continuity, pointwise source gain or boundary-jet smallness is
postulated. This controls a genuine Cauchy reference transfer; it does NOT
identify it with the independently prescribed origin/outgoing solution.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- Explicit spatial pullback of the original physical nonlocal source.
The factor a² is kept, rather than conflating the two radial coordinates. -/
def actualHartreeLaplacianScaledKummerSource
    (a ell c : ℝ) (z : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((a ^ 2 : ℝ) : ℂ) * actualHartreePhysicalSliceInteraction ell c z (a*r)

private theorem physical_source_radius_square_bound
    (B A ell c r : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1) (hr : 0 < r)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    r ^ 2 * ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
      actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ) := by
  let Q := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  have hQ : 0 ≤ Q := mul_nonneg
    (actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA)
    (Real.rpow_nonneg hell.le _)
  have hd : 0 < 1+r := by linarith
  have hd1 : 1 ≤ 1+r := by linarith
  have hRad : r ^ 2 ≤ (1+r) ^ (19 / 8 : ℝ) := by
    calc
      r ^ 2 ≤ (1+r) ^ 2 := by nlinarith [hr.le]
      _ = (1+r) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ ≤ (1+r) ^ (19 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  have hTail : r ^ 2 * (1+r) ^ (-(19 / 8 : ℝ)) ≤ 1 := by
    calc
      _ ≤ (1+r) ^ (19 / 8 : ℝ) * (1+r) ^ (-(19 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_right hRad (Real.rpow_nonneg hd.le _)
      _ = 1 := by rw [← Real.rpow_add hd]; norm_num
  have hRaw := actual_Hartree_physical_source_unweighted_pointwise
    B A ell c r hB hA hell hellOne hc hr z hz hSup hStrauss
  calc
    _ ≤ r ^ 2 * (Q * (1+r) ^ (-(19 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_left hRaw (sq_nonneg r)
    _ = Q * (r ^ 2 * (1+r) ^ (-(19 / 8 : ℝ))) := by ring
    _ ≤ Q * 1 := mul_le_mul_of_nonneg_left hTail hQ
    _ = _ := mul_one _

/-- The true pulled-back source has a derived annular inverse-square bound,
uniform in the spatial rescaling a. It is not an external source hypothesis. -/
theorem actual_Hartree_scaled_Kummer_source_annulus_bound
    (B A ell c a r0 r : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (ha : 0 < a) (hr0 : 0 < r0) (hr : r0 ≤ r)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ‖actualHartreeLaplacianScaledKummerSource a ell c z r‖ ≤
      actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ) / r0 ^ 2 := by
  have hrp : 0 < r := hr0.trans_le hr
  have h := physical_source_radius_square_bound B A ell c (a*r)
    hB hA hell hellOne hc (mul_pos ha hrp) z hz hSup hStrauss
  have heq : r ^ 2 * ‖actualHartreeLaplacianScaledKummerSource a ell c z r‖ =
      (a*r) ^ 2 * ‖actualHartreePhysicalSliceInteraction ell c z (a*r)‖ := by
    rw [actualHartreeLaplacianScaledKummerSource, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    ring
  apply (le_div_iff₀ (pow_pos hr0 2)).2
  calc
    ‖actualHartreeLaplacianScaledKummerSource a ell c z r‖ * r0 ^ 2 ≤
        ‖actualHartreeLaplacianScaledKummerSource a ell c z r‖ * r ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hr 2) (norm_nonneg _)
    _ = r ^ 2 * ‖actualHartreeLaplacianScaledKummerSource a ell c z r‖ := by ring
    _ ≤ _ := by rw [heq]; exact h

/-- The entire original source contribution is controlled, without an
unestimated source-dependent reference. The shifted source integral exists
by its derived bound and measurability; no continuity premise is required. -/
theorem actual_Hartree_full_scaled_source_Kummer_transfer_bound
    (B A ell c a : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1) (ha : 0 < a)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    {mu theta center eps : ℝ} (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hRatio : center+d ≤ 2*(center-d)) (U DU : ℂ) :
    let F := actualHartreeLaplacianScaledKummerSource a ell c z
    max ‖(actualKummerPhysicalRightTransfer K d F U DU).1‖
      ((center+d) * ‖(actualKummerPhysicalRightTransfer K d F U DU).2‖) ≤
      actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) *
        (max ‖U‖ ((center-d)*‖DU‖) +
          2 * actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)) := by
  let F := actualHartreeLaplacianScaledKummerSource a ell c z
  let Q := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  let M := Q / (center-d)^2
  have hQ : 0 ≤ Q := mul_nonneg
    (actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA)
    (Real.rpow_nonneg hell.le _)
  have hr0 : 0 < center-d := by
    simpa only [sub_eq_add_neg] using K.radial_pos (-d)
      (show -d ∈ Icc (-eps) eps from ⟨by linarith, by linarith⟩)
  have hM : 0 ≤ M := div_nonneg hQ (sq_nonneg _)
  have hPoint (s : ℝ) (hs : s ∈ Icc (-d) d) : ‖F (center+s)‖ ≤ M :=
    actual_Hartree_scaled_Kummer_source_annulus_bound B A ell c a
      (center-d) (center+s) hB hA hell hellOne hc ha hr0
      (by linarith [hs.1]) z hz hSup hStrauss
  let V := monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z := rescalePhysicalRadiation ell z
  have hV : Measurable V := actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul (hz.comp (measurable_const.mul measurable_id))
  have hPhys : Measurable (actualHartreePhysicalSliceInteraction ell c z) :=
    actual_Hartree_physical_complete_interaction_measurable V Z hV hZ
  have hFm : Measurable F :=
    measurable_const.mul (hPhys.comp (measurable_const.mul measurable_id))
  have hFI : IntervalIntegrable (fun s => F (center+s)) volume (-d) d := by
    have hConst : IntervalIntegrable (fun _ : ℝ => M) volume (-d) d := intervalIntegrable_const
    apply hConst.mono_fun' (hFm.comp (measurable_const.add measurable_id)).aestronglyMeasurable.restrict
    rw [uIoc_of_le (by linarith : -d ≤ d)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hPoint s (Ioc_subset_Icc_self hs)
  have hBound := actual_Kummer_full_source_scaled_transfer_uniform K d M hd hde
    hRatio hM F hFI hPoint U DU
  have hCancel : 2*(center-d)^2*M = 2*Q := by
    dsimp [M]
    field_simp [hr0.ne']
  rw [hCancel] at hBound
  simpa only [Q, mul_assoc] using hBound

/-- The previously unestimated charge-reference transfer itself is now
uniformly small, for the actual two forced affine charges and the complete
original Hartree source. Constants do not depend on ell,c,a, or annulus radius.
This does not identify the reference with an independently fixed outgoing jet. -/
theorem actual_Hartree_forced_charge_reference_Kummer_uniform
    (B A ell c a : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1) (ha : 0 < a)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    {mu theta center eps : ℝ} (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hRatio : center+d ≤ 2*(center-d)) :
    let G := actualHartreeRadiallyConjugatedInnerSource
      (actualHartreeSlowInnerRadius ell) ell c z
    let alpha : ℂ := (actualPlusCharge (fun r => (G r).re) : ℂ) +
      Complex.I * (actualMinusCharge (fun r => (G r).im) : ℂ)
    let F := actualHartreeLaplacianScaledKummerSource a ell c z
    max ‖(actualKummerPhysicalRightTransfer K d F alpha 0).1‖
      ((center+d) * ‖(actualKummerPhysicalRightTransfer K d F alpha 0).2‖) ≤
      actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) *
        (actualHartreePhysicalWeightedSourceConstant B A *
          (6 * |actualHartreePhysicalChargeTailConstant| + 2)) * ell ^ (1 / 16 : ℝ) := by
  let G := actualHartreeRadiallyConjugatedInnerSource
    (actualHartreeSlowInnerRadius ell) ell c z
  let alpha : ℂ := (actualPlusCharge (fun r => (G r).re) : ℂ) +
    Complex.I * (actualMinusCharge (fun r => (G r).im) : ℂ)
  let Q := actualHartreePhysicalWeightedSourceConstant B A
  let T := |actualHartreePhysicalChargeTailConstant|
  let e := ell ^ (1 / 16 : ℝ)
  have hQ : 0 ≤ Q := actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA
  have he : 0 ≤ e := Real.rpow_nonneg hell.le _
  have hCharge := actual_Hartree_conjugated_inner_forced_charges_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hAlpha : ‖alpha‖ ≤ (6*Q*T)*e := by
    calc
      ‖alpha‖ ≤ ‖(actualPlusCharge (fun r => (G r).re) : ℂ)‖ +
          ‖Complex.I * (actualMinusCharge (fun r => (G r).im) : ℂ)‖ := norm_add_le _ _
      _ = |actualPlusCharge (fun r => (G r).re)| +
          |actualMinusCharge (fun r => (G r).im)| := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2*((2*Q)*e*actualHartreePhysicalChargeTailConstant) +
          (2*Q)*e*actualHartreePhysicalChargeTailConstant :=
        _root_.add_le_add hCharge.1 hCharge.2
      _ = (6*Q*e)*actualHartreePhysicalChargeTailConstant := by ring
      _ ≤ (6*Q*e)*T := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = (6*Q*T)*e := by ring
  have heOne : e ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow hell.le hellOne (show (0 : ℝ) ≤ 1/16 by norm_num)
  have hSmall : ell ^ (1 / 8 : ℝ) ≤ e := by
    have hSplit : ell ^ (1 / 8 : ℝ) = e * e := by
      dsimp [e]
      rw [← Real.rpow_add hell]
      norm_num
    rw [hSplit]
    nlinarith
  have hBound := actual_Hartree_full_scaled_source_Kummer_transfer_bound
    B A ell c a hB hA hell hellOne hc ha z hz hSup hStrauss K d hd hde hRatio alpha 0
  simp only [norm_zero, mul_zero, max_eq_left (norm_nonneg alpha)] at hBound
  have hInside : ‖alpha‖ + 2*Q*ell^(1/8:ℝ) ≤ (Q*(6*T+2))*e := by
    have H := _root_.add_le_add hAlpha
      (mul_le_mul_of_nonneg_left hSmall (show 0 ≤ 2*Q by positivity))
    exact H.trans_eq (by ring)
  have hC : 0 ≤ actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) := by
    unfold actualKummerUniformTransferConstant
    positivity
  exact (hBound.trans (mul_le_mul_of_nonneg_left hInside hC)).trans_eq (by ring)

end HBL.TypeIIDynamicSelection
