import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import Mathlib.Tactic

/-!
# True Fredholm inner, normalized Kummer Green, physical repair and zero: C1

The local Fredholm inner physical field and the same-source origin Kummer
continuation have exactly matching genuine value and physical derivative
at y=L. The actual same-sign physical repair matches the same Kummer
solution at y=aB and has zero value and slope at y=2aB.

Thus the literal four-region physical field is C1 at ALL THREE joins,
without any fictitious global affine tail, free monopole coefficient,
independently prescribed boundary datum or type-II rate. No full
nonlinear PDE residual bound or whole Hdot1 gluing is claimed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The inner Fredholm field is retained to y=L; the SAME forced physical
Kummer profile continues it to the replacement shell, where the genuine
jet-matched repair connects to zero. -/
def actualHartreeInnerKummerFourPiece
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L a B : ℝ)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let v := actualOriginMatchedKummerPullback K a (L / a) B F J.1 J.2
  let UB := actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 B
  let DUB := actualOriginMatchedKummerSlope K (L / a) B F J.1 J.2 B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  if y ≤ L then u y else glued y

/-- All three genuine physical interface derivatives of one selected
four-piece Hartree Kummer field; no interface derivative is assumed. -/
theorem actual_Hartree_inner_Kummer_four_piece_three_C1_joins
    {mu theta scale B : ℝ} (K : OriginKummerPair mu theta scale)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hLB : L / a ≤ B) (hB : B < scale)
    (hStrict : L < a * B)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r) :
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let DUB := actualOriginMatchedKummerSlope K (L / a) B F J.1 J.2 B
    let full := actualHartreeInnerKummerFourPiece K L a B Fp Fm hp hm F
    HasDerivAt full (deriv u L) L ∧
      HasDerivAt full ((1 / a : ℝ) • DUB) (a * B) ∧
      HasDerivAt full (0 : ℂ) (2 * a * B) := by
  dsimp only
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let v := actualOriginMatchedKummerPullback K a (L / a) B F J.1 J.2
  let UB := actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 B
  let DUB := actualOriginMatchedKummerSlope K (L / a) B F J.1 J.2 B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued := actualPhysicalMatchedKummerC1Splice a B v rep
  let full : ℝ → ℂ := fun y => if y ≤ L then u y else glued y
  have hInner :=
    actual_Hartree_moment_locked_pullback_actual_inner_jet
      K L a hL ha hLB hB Fp Fm hp hm F hF
  have hr0 : 0 < L / a := div_pos hL ha
  have hOuter :=
    actual_Hartree_matched_Kummer_repair_is_C1_at_both_physical_joins
      K a ha hr0 hLB hB F hF J.1 J.2
  dsimp only at hInner hOuter
  have hBpos : 0 < B := (div_pos hL ha).trans_le hLB
  have hAB : a * B < 2 * a * B := by
    have h := mul_pos ha hBpos
    linarith
  have hInnerDeriv :
      HasDerivAt u (deriv u L) L := by
    have hD := (hInner.2.2.2.2.1).add hInner.2.1
    have hEq : (fun y : ℝ => u y - v y) + v = u := by
      funext y
      simp
    rw [hEq] at hD
    simpa only [zero_add] using hD
  have hGNear : glued =ᶠ[𝓝 L] v := by
    filter_upwards [Iio_mem_nhds hStrict] with y hy
    change (if y ≤ a * B then v y else
      if y ≤ 2 * a * B then rep y else 0) = v y
    change y < a * B at hy
    simp [le_of_lt hy]
  have hGDeriv : HasDerivAt glued (deriv u L) L :=
    (hInner.2.1).congr_of_eventuallyEq hGNear
  have hGValue : u L = glued L := by
    have hglue : glued L = v L := by
      dsimp [glued, actualPhysicalMatchedKummerC1Splice]
      simp [hStrict.le]
    exact hInner.1.symm.trans hglue.symm
  have hGfar : glued (2 * a * B) = 0 := by
    have hends :=
      actual_Kummer_physical_interface_repair_endpoint_jets
        a B ha hBpos UB DUB
    change (if 2 * a * B ≤ a * B then v (2 * a * B)
      else if 2 * a * B ≤ 2 * a * B then rep (2 * a * B) else 0) = 0
    have hr : rep (2 * a * B) = 0 := hends.2.2.1
    simp [not_le.mpr hAB, hr]
  have hGzeroFar (y : ℝ) (hy : 2 * a * B < y) :
      glued y = 0 := by
    dsimp [glued, actualPhysicalMatchedKummerC1Splice]
    have hnot1 : ¬ y ≤ a * B := not_le.mpr (hAB.trans hy)
    have hnot2 : ¬ y ≤ 2 * a * B := not_le.mpr hy
    simp [hnot1, hnot2]
  have hThree :=
    actual_physical_three_piece_C1_interfaces
      L (2 * a * B) (hStrict.trans hAB)
      u glued (deriv u L)
      hInnerDeriv hGDeriv hGValue hOuter.2 hGfar
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
        have hz : glued y = 0 := hGzeroFar y hyfar
        simp [full, hleft, hfar, hz]
  rw [hEq] at hThree
  have hFullNear : full =ᶠ[𝓝 (a * B)] glued := by
    filter_upwards [Ioi_mem_nhds hStrict] with y hy
    change (if y ≤ L then u y else glued y) = glued y
    change L < y at hy
    simp [not_le.mpr hy]
  have hAt : HasDerivAt full ((1 / a : ℝ) • DUB) (a * B) :=
    hOuter.1.congr_of_eventuallyEq hFullNear
  change HasDerivAt full (deriv u L) L ∧
    HasDerivAt full ((1 / a : ℝ) • DUB) (a * B) ∧
    HasDerivAt full (0 : ℂ) (2 * a * B)
  exact ⟨hThree.1, hAt, hThree.2⟩

end HBL.TypeIIDynamicSelection
