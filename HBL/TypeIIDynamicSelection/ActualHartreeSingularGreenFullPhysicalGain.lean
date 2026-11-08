import HBL.TypeIIDynamicSelection.ActualHartreeKummerSingularGreenCompatibilityTransport
import HBL.TypeIIDynamicSelection.ActualHartreeFredholmOutgoingNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeSingularGreenPhysicalSourceGain
import Mathlib.Tactic

/-!
# Actual compatible Hartree singular Green field has no moving-scale loss

The physical singular Green channel is Y(r) A(r), not the coefficient
A(r) by itself. The strict original compatibility equation transports A:
A(r) = J_-(r0) - integral_{r0}^r (X F / W).
The first component has a true Fredholm source norm and positive r0
factor by the exact origin Wronskian. The second component uses the
regular Frobenius bound |X(r)|=O(1), not the coarse |X(r)|<=G/r.
Multiplying by the physical singular solution Y(r) cancels r0/r in the
first component and the integration interval/r in the second.

The conclusion is an explicit uniform (in the moving scale a) bound
on the actual singular Green physical source field, with original
weighted Fredholm source and true inverse-square quartic Hartree source.

The compatibility condition is an explicit premise, NOT automatically
proved for the unadjusted core-radiation source. The unique selected
Cramer speed must produce it on the same PDE orbit in the final §2.13.
No complete PDE residual O(s^(-9/4)) is claimed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

theorem actual_Hartree_compatible_full_singular_Green_physical_source_gain
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
    let Cr := 1 + (D + 1) * G * (R ^ 2 + 2)
    let Cp := 1 + (D + 1) * G * R ^ 2
    let Cf := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
    let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
    let M := actualHartreePhysicalWeightedSourceConstant B A *
      ell ^ (1 / 8 : ℝ)
    ‖originPhysicalValue K.y y * originGreenCoeffA K R F y‖ ≤
      G * Cr * (Cf * N) + G * Cp * M := by
  dsimp only
  let F : ℝ → ℂ := fun x =>
    -actualHartreeLaplacianScaledKummerSource a ell c z x
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let r0 : ℝ := L / a
  let Cr : ℝ := 1 + (D + 1) * G * (R ^ 2 + 2)
  let Cp : ℝ := 1 + (D + 1) * G * R ^ 2
  let Cf : ℝ := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let M : ℝ := actualHartreePhysicalWeightedSourceConstant B A *
    ell ^ (1 / 8 : ℝ)
  have hLp : 0 < L := by linarith
  have hr0 : 0 < r0 := div_pos hLp ha
  have hypos : 0 < y := hr0.trans_le hy.1
  have hSource : IntervalIntegrable F volume r0 R :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      B A ell c a r0 R hB hA hell hellOne hc ha hr0
      (by simpa only [r0] using hOrder) z hz hSup hStrauss).neg
  have hBasis : OriginBasisOn K r0 R G :=
    origin_kummer_annulus_bound K r0 R G hr0 hRscale hG hbound
  have hCompat :
      originGreenCoeffA K R F y =
        actualOriginOutgoingTrace K r0 J.1 J.2 -
          originGreenCoeffA K y F r0 := by
    have h :=
      actual_Hartree_compatible_singular_Green_coefficient_local_transport
        K r0 R G hBasis hOrder F hSource J.1 J.2 hzero y hy
    simpa only [originGreenCoeffA] using h
  have hTraceRaw :=
    actual_Hartree_original_Fredholm_outgoing_trace_source_radius_gain
      K D G R L a hD hG hR hROne hRscale.le hcoeff hbound
      hL ha hOrder Fp Fm hp hm hcp hcm
  have hTrace :
      ‖actualOriginOutgoingTrace K r0 J.1 J.2‖ ≤
        Cr * r0 * (Cf * N) := by
    simpa only [r0, J, Cr, Cf, N] using hTraceRaw
  have hMomentRaw :=
    actual_Hartree_singular_Green_local_moment_full_product_gain
      K D G L R a B A ell c hD hG (by linarith : 1 ≤ L)
      ha hOrder hRscale hcoeff hbound hB hA hell hellOne hc
      z hz hSup hStrauss y hy
  have hMoment :
      ‖originPhysicalValue K.y y * originGreenCoeffA K y F r0‖ ≤
        G * Cp * M := by
    simpa only [r0, F, M, Cp] using hMomentRaw.2
  have hY : ‖originPhysicalValue K.y y‖ ≤ G / y := by
    have hBr := hbound y ⟨hypos.le, hy.2.trans hRscale.le⟩
    rw [originPhysicalValue, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hypos]
    exact div_le_div_of_nonneg_right hBr.1 hypos.le
  have hRadius : r0 / y ≤ 1 :=
    (div_le_iff₀ hypos).2 (by linarith [hy.1])
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCf : 0 ≤ Cf := by dsimp [Cf]; positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    exact add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hCoef : 0 ≤ G * Cr * (Cf * N) := by positivity
  have hTraceProduct :
      ‖originPhysicalValue K.y y *
        actualOriginOutgoingTrace K r0 J.1 J.2‖ ≤
        G * Cr * (Cf * N) := by
    calc
      _ = ‖originPhysicalValue K.y y‖ *
        ‖actualOriginOutgoingTrace K r0 J.1 J.2‖ := norm_mul _ _
      _ ≤ (G / y) * (Cr * r0 * (Cf * N)) :=
        mul_le_mul hY hTrace (norm_nonneg _) (div_nonneg hG hypos.le)
      _ = (G * Cr * (Cf * N)) * (r0 / y) := by
        field_simp [hypos.ne']
        ring
      _ ≤ (G * Cr * (Cf * N)) * 1 :=
        mul_le_mul_of_nonneg_left hRadius hCoef
      _ = G * Cr * (Cf * N) := by ring
  calc
    ‖originPhysicalValue K.y y * originGreenCoeffA K R F y‖ =
      ‖originPhysicalValue K.y y *
        actualOriginOutgoingTrace K r0 J.1 J.2 -
        originPhysicalValue K.y y *
          originGreenCoeffA K y F r0‖ := by
      rw [hCompat]
      ring
    _ ≤ ‖originPhysicalValue K.y y *
        actualOriginOutgoingTrace K r0 J.1 J.2‖ +
      ‖originPhysicalValue K.y y *
        originGreenCoeffA K y F r0‖ := norm_sub_le _ _
    _ ≤ G * Cr * (Cf * N) + G * Cp * M :=
      add_le_add hTraceProduct hMoment

end HBL.TypeIIDynamicSelection
