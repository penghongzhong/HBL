import HBL.TypeIIDynamicSelection.ActualHartreeSpectralCorrectedPhysicalOuterC1
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import Mathlib.Tactic

/-!
# Genuine spectral-corrected Fredholm/Green/repair/zero four-piece field

The spectral correction is constructed from the ORIGINAL Cramer-matched
Green response and the original zero-left-jet Cramer source integral.
Its left Cauchy coordinates are therefore identical to those of
the original Fredholm inner field. At the UPPER Kummer interface the
physical repair is rebuilt using the correction's ACTUAL value and
ACTUAL derivative, rather than obsolete uncorrected traces; at the
outer repair interface the actual field and derivative vanish.

Thus the literal physical four-piece field has all THREE C¹ joins.
This theorem neither postulates an independent selected speed nor
states a time-positive full nonlocal PDE residual. The source and inner
Fredholm fields must be provided by the actual Hartree orbit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel

/-- Literal true spectral-corrected Kummer continuation with its rebuilt
physical outer repair and the unchanged Fredholm physical inner field. -/
def actualHartreeInnerKummerSpectralFourPiece
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L a B : ℝ)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (d : ℂ) (y : ℝ) : ℂ :=
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let w := actualHartreeMatchedSpectralCorrectedValue
    K (L / a) B F J.1 J.2 d
  let v := fun y => w (y / a)
  let rep := actualKummerPhysicalInterfaceRepair a B (w B) (deriv w B)
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  if y ≤ L then u y else glued y

theorem actual_Hartree_spectral_inner_four_piece_three_C1_joins
    {mu theta scale B : ℝ} (K : OriginKummerPair mu theta scale)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hOrder : L / a ≤ B) (hB : B < scale)
    (hStrict : L < a * B)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (d : ℂ) :
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let w := actualHartreeMatchedSpectralCorrectedValue
      K (L / a) B F J.1 J.2 d
    let full := actualHartreeInnerKummerSpectralFourPiece
      K L a B Fp Fm hp hm F d
    HasDerivAt full (deriv u L) L ∧
      HasDerivAt full ((1 / a : ℝ) • deriv w B) (a * B) ∧
      HasDerivAt full (0 : ℂ) (2 * a * B) := by
  dsimp only
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let w0 := actualOriginMatchedKummerValue K (L / a) B F J.1 J.2
  let v0 := actualOriginMatchedKummerPullback K a (L / a) B F J.1 J.2
  let w := actualHartreeMatchedSpectralCorrectedValue
    K (L / a) B F J.1 J.2 d
  let v : ℝ → ℂ := fun y => w (y / a)
  let rep := actualKummerPhysicalInterfaceRepair a B (w B) (deriv w B)
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  let full : ℝ → ℂ := fun y => if y ≤ L then u y else glued y
  have hr0 : 0 < L / a := div_pos hL ha
  have hOld :=
    actual_Hartree_moment_locked_pullback_actual_inner_jet
      K L a hL ha hOrder hB Fp Fm hp hm F hF
  dsimp only at hOld
  have hOrigLeft :=
    actual_origin_matched_Kummer_actual_endpoint_jets
      K hr0 hOrder hB F hF J.1 J.2
  have hSelected :=
    actual_Hartree_matched_spectral_corrected_left_C1_and_exact_equation
      K (L / a) B hr0 hOrder hB F hF J.1 J.2 d
  dsimp only at hSelected
  have hOriginalV : HasDerivAt v0 ((1 / a : ℝ) • J.2) L := by
    have h := hOrigLeft.2.1.scomp L ((hasDerivAt_id L).div_const a)
    simpa only [v0, actualOriginMatchedKummerPullback,
      Function.comp_def, id_eq, one_div,
      Complex.real_smul, Complex.ofReal_inv] using h
  have hJetDerivative : ((1 / a : ℝ) • J.2) = deriv u L :=
    hOriginalV.unique hOld.2.1
  have hCorrectedV : HasDerivAt v (deriv u L) L := by
    have h := hSelected.2.1.scomp L
      ((hasDerivAt_id L).div_const a)
    have hV : HasDerivAt v ((1 / a : ℝ) • J.2) L := by
      simpa only [v, Function.comp_def, id_eq, one_div,
        Complex.real_smul, Complex.ofReal_inv] using h
    simpa only [hJetDerivative] using hV
  have hJvalue : J.1 = u L := by
    calc
      J.1 = w0 (L / a) := hOrigLeft.1.symm
      _ = v0 L := rfl
      _ = u L := hOld.1
  have hCorrectedValue : v L = u L := by
    calc
      v L = w (L / a) := rfl
      _ = J.1 := hSelected.1
      _ = u L := hJvalue
  have hInnerDerivative : HasDerivAt u (deriv u L) L := by
    have hD := (hOld.2.2.2.2.1).add hOld.2.1
    have hEq : (fun y => u y - v0 y) + v0 = u := by
      funext y
      simp
    rw [hEq] at hD
    simpa only [zero_add] using hD
  have hOuter :=
    actual_Hartree_spectral_corrected_physical_two_outer_C1_joins
      K a (L / a) B ha hr0 hOrder hB F hF J.1 J.2 d
  dsimp only at hOuter
  have hGnear : glued =ᶠ[𝓝 L] v := by
    filter_upwards [Iio_mem_nhds hStrict] with y hy
    change (if y ≤ a * B then v y else
      if y ≤ 2 * a * B then rep y else 0) = v y
    change y < a * B at hy
    simp [le_of_lt hy]
  have hGderiv : HasDerivAt glued (deriv u L) L :=
    hCorrectedV.congr_of_eventuallyEq hGnear
  have hGvalue : u L = glued L := by
    have hv : glued L = v L := by
      dsimp [glued, actualPhysicalMatchedKummerC1Splice]
      simp [hStrict.le]
    exact hCorrectedValue.symm.trans hv.symm
  have hBpos : 0 < B := hr0.trans_le hOrder
  have hAB : a * B < 2 * a * B := by
    have hp := mul_pos ha hBpos
    linarith
  have hFar : glued (2 * a * B) = 0 := by
    have hEnds :=
      actual_Kummer_physical_interface_repair_endpoint_jets
        a B ha hBpos (w B) (deriv w B)
    change (if 2 * a * B ≤ a * B then v (2 * a * B)
      else if 2 * a * B ≤ 2 * a * B then rep (2 * a * B)
      else 0) = 0
    have hr : rep (2 * a * B) = 0 := hEnds.2.2.1
    simp [not_le.mpr hAB, hr]
  have hGone (y : ℝ) (hy : 2 * a * B < y) : glued y = 0 := by
    dsimp [glued, actualPhysicalMatchedKummerC1Splice]
    have hnot1 : ¬ y ≤ a * B := not_le.mpr (hAB.trans hy)
    have hnot2 : ¬ y ≤ 2 * a * B := not_le.mpr hy
    simp [hnot1, hnot2]
  have hThree :=
    actual_physical_three_piece_C1_interfaces
      L (2 * a * B) (hStrict.trans hAB)
      u glued (deriv u L)
      hInnerDerivative hGderiv hGvalue hOuter.2 hFar
  dsimp only at hThree
  have hEq :
      (fun y : ℝ => if y ≤ L then u y
        else if y ≤ 2 * a * B then glued y else 0) = full := by
    funext y
    by_cases hleft : y ≤ L
    · simp [full, hleft]
    · by_cases hfar : y ≤ 2 * a * B
      · simp [full, hleft, hfar]
      · have hyfar : 2 * a * B < y := lt_of_not_ge hfar
        have hz : glued y = 0 := hGone y hyfar
        simp [full, hleft, hfar, hz]
  rw [hEq] at hThree
  have hFullNear : full =ᶠ[𝓝 (a * B)] glued := by
    filter_upwards [Ioi_mem_nhds hStrict] with y hy
    change (if y ≤ L then u y else glued y) = glued y
    change L < y at hy
    simp [not_le.mpr hy]
  have hAt : HasDerivAt full ((1 / a : ℝ) • deriv w B) (a * B) :=
    hOuter.1.congr_of_eventuallyEq hFullNear
  change HasDerivAt full (deriv u L) L ∧
    HasDerivAt full ((1 / a : ℝ) • deriv w B) (a * B) ∧
    HasDerivAt full (0 : ℂ) (2 * a * B)
  exact ⟨hThree.1, hAt, hThree.2⟩

end HBL.TypeIIDynamicSelection
