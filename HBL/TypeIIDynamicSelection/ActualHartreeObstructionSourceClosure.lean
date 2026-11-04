import HBL.TypeIIDynamicSelection.ActualHartreeCompleteObstructionBound

/-!
# One physical source, one compatibility solve, and an original-data bound

This terminal synthesis removes the formerly unestimated obstruction Z
from the source-norm inequality. The SAME basis, interface, physical outer
source and fixed Fredholm inner jet are used by cancellation, its inverse
bound, and the new obstruction estimate. The real speed increment is
constructed and unique, not assumed. Source membership, |c| <= 1,
L |c| <= 1 and the interface inclusion are all derived.

The conclusion concerns the original core/radiation forcing at a frozen
time. It is not a complete nonlinear residual step for arbitrary iterates.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- Construct the unique compatible correction and bound its actual
adjusted sources using only original source norms and physical radiation
amplitudes. No obstruction-smallness or speed-inverse estimate is an input. -/
theorem actual_Hartree_same_source_compatible_correction_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ, 6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (B0 A0 ell c a : ℝ) (z : ℝ → ℂ) (hell : 0 < ell),
        0 ≤ B0 → 0 ≤ A0 → ell ≤ 1 →
        L0 ≤ actualHartreeSlowInnerRadius ell →
        actualHartreeSlowInnerRadius ell ^ 3 ≤ a → a * |c| ≤ epsilon →
        Measurable z → (∀ r : ℝ, 0 < r → ‖z r‖ ≤ B0) →
        (∀ r : ℝ, 1 ≤ r → r * ‖z r‖ ≤ A0) →
        Continuous (actualHartreeTransmissionPlusSource ell c z) →
        Continuous (actualHartreeTransmissionMinusSource ell c z) →
        let L := actualHartreeSlowInnerRadius ell
        let hLp : 0 < L := Real.rpow_pos_of_pos hell _
        let Fp := actualHartreeTransmissionPlusSource ell c z
        let Fm := actualHartreeTransmissionMinusSource ell c z
        let F := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
        let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
        ∃ (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
          (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (p : ℝ × ℝ),
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          innerWeightedNorm (7 / 4 : ℝ)
              (fun r => Fp r + p.2 * actualMomentLockedInnerPhaseSource L c r) +
            innerWeightedNorm (7 / 4 : ℝ)
              (fun r => Fm r + p.1 * actualMomentLockedInnerScaleSource L c r) ≤
            N0 + (1024 * C / B ^ 2) * L ^ (-(1 / 2 : ℝ)) *
              (actualMomentLockedObstructionTraceConstant D G B / a * N0 +
                (1 + (D + 1) * G * B ^ 2) * B *
                  actualHartreePhysicalWeightedSourceConstant B0 A0 * ell ^ (1 / 8 : ℝ)) := by
  obtain ⟨Lc, ec, _hLc, hec, hCancel⟩ :=
    actual_Hartree_moment_locked_coupled_unique_cancellation_region
      K D G hD hG hB hBR hcoeff hbound hsmallB
  obtain ⟨Li, ei, _hLi, hei, hInverse⟩ :=
    actual_Hartree_moment_locked_coupled_inverse_bound_region
      K D G hD hG hB hBR hcoeff hbound hsmallB
  obtain ⟨C, hC, hSharp⟩ := actual_Hartree_moment_locked_sharp_source_obstruction_gain
  let L0 : ℝ := max Lc (max Li (6 + 1 / B))
  let epsilon : ℝ := min ec (min ei 1)
  have hL0 : 6 ≤ L0 := by
    have hTail : 6 + 1 / B ≤ L0 := (le_max_right _ _).trans (le_max_right _ _)
    have hRecip : 0 ≤ 1 / B := by positivity
    linarith
  have hepsilon : 0 < epsilon := lt_min hec (lt_min hei (by norm_num))
  have hepsOne : epsilon ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨L0, epsilon, C, hL0, hepsilon, hepsOne, hC, ?_⟩
  intro B0 A0 ell c a z hell hB0 hA0 hellOne hLarge ha3 hSmall hz hSup hStrauss hcp hcm
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  let F : ℝ → ℂ := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
  have hLp : 0 < L := Real.rpow_pos_of_pos hell _
  have hLsix : 6 ≤ L := hL0.trans hLarge
  have hLtwo : 2 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hLargeC : Lc ≤ L := (le_max_left _ _).trans hLarge
  have hLargeI : Li ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hTail : 6 + 1 / B ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLarge)
  have hSmallC : a * |c| ≤ ec := hSmall.trans (min_le_left _ _)
  have hSmallI : a * |c| ≤ ei :=
    hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hLa : L ≤ a := by
    have hPow : L ≤ L ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLone)
        (show 0 ≤ L ^ 2 + L by positivity)]
    exact hPow.trans ha3
  have hLc : L * |c| ≤ 1 :=
    (mul_le_mul_of_nonneg_right hLa (abs_nonneg c)).trans (hSmall.trans hepsOne)
  have hc : |c| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hLone (abs_nonneg c)
    nlinarith only [h, hLc]
  have hLB : L / a ≤ B := by
    apply (div_le_iff₀ ha).2
    have hRecip : 1 / B ≤ L := by linarith only [hTail]
    have hBL : 1 ≤ L * B := (div_le_iff₀ hB).1 hRecip
    have hBL2 := mul_le_mul_of_nonneg_left hBL (sq_nonneg L)
    have hALB := mul_le_mul_of_nonneg_right ha3 hB.le
    have hLsq : L ≤ L ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLone) hLp.le]
    nlinarith only [hBL2, hALB, hLsq]
  obtain ⟨hp, hm, hObstruction⟩ := actual_Hartree_moment_locked_full_obstruction_bound
    K D G B hD hG hBR hcoeff hbound B0 A0 ell c a
    hB0 hA0 hell hellOne hc hLtwo ha3 hLB z hz hSup hStrauss hcp hcm
  dsimp only at hObstruction
  have hF : IntervalIntegrable F volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable B0 A0 ell c a (L / a) B
      hB0 hA0 hell hellOne hc ha (div_pos hLp ha) hLB z hz hSup hStrauss).neg
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let Z := actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2
  have hK := origin_kummer_annulus_bound K (L / a) B G (div_pos hLp ha) hBR hG hbound
  obtain ⟨p, hColumns, hUnique⟩ := hCancel L c a hLp hLargeC ha3 hc hSmallC Z
  have hAffine (q : ℝ × ℝ) := actual_Hartree_moment_locked_full_coupled_response
    K (div_pos hLp ha) hLB hK L c hLp a ha Fp Fm hp hm F hF q.1 q.2
  have hCompat : actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
      Fp Fm hp hm F p.1 p.2 = 0 := (hAffine p).trans hColumns
  have hSpeed := hInverse L c a hLp hLargeI ha3 hc hSmallI Fp Fm hp hm F hF
    p.1 p.2 hCompat
  have hAdjusted := hSharp L c a B hLone hLc ha3 hB Fp Fm hp hm p.1 p.2 Z hSpeed
  have hFactor : 0 ≤ (1024 * C / B ^ 2) * L ^ (-(1 / 2 : ℝ)) := by positivity
  refine ⟨hp, hm, p, hCompat, ?_, ?_⟩
  · intro q hq
    exact hUnique q ((hAffine q).symm.trans hq)
  · exact hAdjusted.trans (_root_.add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hObstruction.2 hFactor))

end HBL.TypeIIDynamicSelection
