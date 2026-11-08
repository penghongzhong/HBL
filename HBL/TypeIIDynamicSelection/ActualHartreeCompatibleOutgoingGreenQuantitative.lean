import HBL.TypeIIDynamicSelection.ActualHartreeKummerSingularGreenCompatibilityTransport
import HBL.TypeIIDynamicSelection.ActualHartreeFredholmOutgoingNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeKummerOutgoingLocalMomentGain
import Mathlib.Tactic

/-!
# One genuinely compatible Hartree source: moving-interface singular Green bound

This is an exact composition of three *actual* producers:
(1) the original two-channel weighted Fredholm inverse gives the left jet;
(2) the exact origin Wronskian makes its outgoing projection O(L/a);
(3) the real inverse-square quartic Hartree density makes the local Green
    source moment vanish at the left interface.

The ORIGINAL compatibility equation is kept visible; it is the same
condition that the unique Cramer speed must cancel. It is NOT silently
assumed to be satisfied by arbitrary unadjusted core-radiation data.
This theorem connects an actually compatible profile source (if supplied)
to a quantitative full-annulus outgoing coefficient. Deriving that exact
compatibility from the selected time-dependent source on a single orbit,
and the full 9/4-order three-region Hartree PDE, remain distinct obligations.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_compatible_outgoing_Green_quantitative_from_true_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G R L a B A ell c : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hR : 0 < R) (hROne : R ≤ 1) (hRscale : R < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hL : 2 < L) (ha : 0 < a)
    (hOrder : L / a ≤ R)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hStrauss : ∀ x : ℝ, 1 ≤ x → x * ‖z x‖ ≤ A)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (hzero : actualMomentLockedIntervalObstruction
      K (L / a) R
      (fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x)
      (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)).1
      (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)).2 = 0)
    (y : ℝ) (hy : y ∈ Icc (L / a) R) :
    let F := fun x : ℝ => -actualHartreeLaplacianScaledKummerSource a ell c z x
    let Creg := 1 + (D + 1) * G * (R ^ 2 + 2)
    let Csrc := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
    let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
    let M := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
    ‖originGreenCoeffA K R F y‖ ≤
      Creg * (L / a) * (Csrc * N) +
      G * M * (a * y - L) * L ^ (-(11 / 8 : ℝ)) := by
  dsimp only
  let r0 : ℝ := L / a
  let F : ℝ → ℂ := fun x =>
    -actualHartreeLaplacianScaledKummerSource a ell c z x
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
  let Creg : ℝ := 1 + (D + 1) * G * (R ^ 2 + 2)
  let Csrc : ℝ := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let M : ℝ := actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  have hLp : 0 < L := by linarith
  have hr0 : 0 < r0 := div_pos hLp ha
  have hSource : IntervalIntegrable F volume r0 R :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      B A ell c a r0 R hB hA hell hellOne hc ha hr0
      (by simpa only [r0] using hOrder) z hz hSup hStrauss).neg
  have hK : OriginBasisOn K r0 R G :=
    origin_kummer_annulus_bound K r0 R G hr0 hRscale hG hbound
  have hCompat :
      originGreenCoeffA K R F y =
        actualOriginOutgoingTrace K r0 J.1 J.2 -
          ∫ x in r0..y, originGreenSourceA K F x :=
    actual_Hartree_compatible_singular_Green_coefficient_local_transport
      K r0 R G hK hOrder F hSource J.1 J.2 hzero y hy
  have hTraceRaw :=
    actual_Hartree_original_Fredholm_outgoing_trace_source_radius_gain
      K D G R L a hD hG hR hROne hRscale hcoeff hbound
      hL ha hOrder Fp Fm hp hm hcp hcm
  have hTrace :
      ‖actualOriginOutgoingTrace K r0 J.1 J.2‖ ≤
        Creg * r0 * (Csrc * N) := by
    simpa only [r0, J, Creg, Csrc, N] using hTraceRaw
  have hMomentRaw :=
    actual_Hartree_Kummer_outgoing_local_source_moment_bound
      K G L R a B A ell c hG (by linarith : 1 ≤ L) ha hOrder
      hRscale hbound hB hA hell hellOne hc z hz hSup hStrauss y hy
  have hMoment :
      ‖∫ x in r0..y, originGreenSourceA K F x‖ ≤
        G * M * (a * y - L) * L ^ (-(11 / 8 : ℝ)) := by
    simpa only [originGreenCoeffA, r0, F, M] using hMomentRaw
  calc
    ‖originGreenCoeffA K R F y‖ =
        ‖actualOriginOutgoingTrace K r0 J.1 J.2 -
          ∫ x in r0..y, originGreenSourceA K F x‖ := by
      rw [hCompat]
    _ ≤ ‖actualOriginOutgoingTrace K r0 J.1 J.2‖ +
        ‖∫ x in r0..y, originGreenSourceA K F x‖ :=
      norm_sub_le _ _
    _ ≤ Creg * r0 * (Csrc * N) +
        G * M * (a * y - L) * L ^ (-(11 / 8 : ℝ)) :=
      add_le_add hTrace hMoment
    _ = Creg * (L / a) * (Csrc * N) +
        G * M * (a * y - L) * L ^ (-(11 / 8 : ℝ)) := rfl

end HBL.TypeIIDynamicSelection
