import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledInverseBound
import HBL.TypeIIDynamicSelection.ActualHartreeInnerShellEquation
import HBL.TypeIIDynamicSelection.ActualHartreeSharpSpeedSource

/-!
# Quantitative control of the complete actual compatibility obstruction

The original physical Kummer forcing is retained on the whole interval
[L/a,B]. Its inverse-square bound is combined pointwise with the exact
Wronskian, rather than first replacing it by a supremum at L/a.
The baseline trace is the SAME normalized Fredholm output used in the
coupled matrix. No unrelated existential inner solution is substituted.

The bounds concern a frozen physical source. They do not establish a
full iterated PDE residual, time regularity or an infinity condition.
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

private theorem obstruction_inverse_wronskian_norm
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r : ℝ) (hr : 0 < r) (hrs : r ≤ scale) :
    ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
  have hW : originGreenWronskian K r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K ⟨hr.le, hrs⟩ hr.ne'
  have hExp : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hExp, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp

/-- The complete negative physical RHS has a uniformly bounded Green
coefficient even when the lower matching endpoint tends to zero.
Both interval integrability and the estimate are derived from the actual
Hartree source. No small forcing or projection is assumed. -/
theorem actual_Hartree_full_interval_Green_coefficient_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B r0 : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (B0 A0 ell c a : ℝ) (hB0 : 0 ≤ B0) (hA0 : 0 ≤ A0)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1) (ha : 0 < a)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ r : ℝ, 0 < r → ‖z r‖ ≤ B0)
    (hStrauss : ∀ r : ℝ, 1 ≤ r → r * ‖z r‖ ≤ A0) :
    let F := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
    IntervalIntegrable (originGreenSourceA K F) volume r0 B ∧
      ‖originGreenCoeffA K B F r0‖ ≤
        (1 + (D + 1) * G * B ^ 2) * B *
          actualHartreePhysicalWeightedSourceConstant B0 A0 * ell ^ (1 / 8 : ℝ) := by
  dsimp only
  let F : ℝ → ℂ := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let C0 : ℝ := 1 + (D + 1) * G * B ^ 2
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant B0 A0 * ell ^ (1 / 8 : ℝ)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hQ : 0 ≤ Q := mul_nonneg
    (actualHartreePhysicalWeightedSourceConstant_nonneg B0 A0 hB0 hA0)
    (Real.rpow_nonneg hell.le _)
  have hK := origin_kummer_annulus_bound K r0 B G hr0 hBR hG hbound
  have hF : IntervalIntegrable F volume r0 B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable B0 A0 ell c a r0 B
      hB0 hA0 hell hellOne hc ha hr0 hOrder z hz hSup hStrauss).neg
  have hDensity (r : ℝ) (hr : r ∈ Icc r0 B) :
      ‖originGreenSourceA K F r‖ ≤ C0 * Q := by
    have hrp : 0 < r := hr0.trans_le hr.1
    have hreg := origin_kummer_regular_physical_bound K D G hD hG hBR.le
      hcoeff hbound r ⟨hrp, hr.2⟩
    have hInv := obstruction_inverse_wronskian_norm K r hrp (hr.2.trans hBR.le)
    have hs : ‖F r‖ ≤ Q / r ^ 2 := by
      simpa only [F, norm_neg] using
        actual_Hartree_scaled_Kummer_source_annulus_bound B0 A0 ell c a r r
          hB0 hA0 hell hellOne hc ha hrp le_rfl z hz hSup hStrauss
    rw [originGreenSourceA, div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      _ ≤ C0 * (Q / r ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hreg.1 hs (norm_nonneg _) hC0) (sq_nonneg r)
      _ = C0 * Q := by field_simp [hrp.ne']
  have hIntegral : ‖originGreenCoeffA K B F r0‖ ≤ (C0 * Q) * |B - r0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    rw [uIoc_of_le hOrder] at hr
    exact hDensity r ⟨hr.1.le, hr.2⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hOrder)] at hIntegral
  refine ⟨(actual_origin_Green_source_integrability K hK hOrder F hF).1, ?_⟩
  calc
    _ ≤ C0 * Q * (B - r0) := hIntegral
    _ ≤ C0 * Q * B := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hQ)
    _ = _ := by dsimp [C0, Q]; ring

/-- Fixed-basis constant; independent of the cutoff, spatial scale and source. -/
def actualMomentLockedObstructionTraceConstant (D G B : ℝ) : ℝ :=
  2 * ((D + 1) * G) * actualInnerShellValueConstant +
    (1 + (D + 1) * G * B ^ 2) * actualInnerShellDerivativeConstant

private theorem obstruction_real_pair_norm (u v : ℝ) :
    ‖(u : ℂ) + Complex.I * (v : ℂ)‖ ≤ |u| + |v| := by
  exact (norm_add_le _ _).trans_eq (by
    simp [Complex.norm_real, Real.norm_eq_abs])

/-- The baseline flux is controlled by the original input norm of the SAME
fixed normalized Fredholm inverse, with no extra trace or moment premise. -/
theorem actual_Hartree_canonical_baseline_outgoing_trace_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B L a : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hBR : B < scale) (hL : 2 < L) (ha3 : L ^ 3 ≤ a) (hLB : L / a ≤ B)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (hcp : Continuous Fp) (hcm : Continuous Fm) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
      actualMomentLockedObstructionTraceConstant D G B / a *
        (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) := by
  dsimp only
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let up := actualMomentLockedPhysicalPlus Fp hp
  let um := actualMomentLockedPhysicalMinus Fm hm
  let Np := innerWeightedNorm (7 / 4 : ℝ) Fp
  let Nm := innerWeightedNorm (7 / 4 : ℝ) Fm
  let N := Np + Nm
  let V := actualInnerShellValueConstant
  let T := actualInnerShellDerivativeConstant
  let H := (D + 1) * G
  let C0 := 1 + (D + 1) * G * B ^ 2
  have hLp : 0 < L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hV : 0 ≤ V := by dsimp [V, actualInnerShellValueConstant]; positivity
  have hT : 0 ≤ T := by dsimp [T, actualInnerShellDerivativeConstant]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hN : 0 ≤ N := add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hScale : a * (L / a) = L := by field_simp [ha.ne']
  have hpj := (actual_Hartree_normalized_inner_shell_equation_bound Fp hp hcp L L hL le_rfl).1
  have hmj := (actual_Hartree_normalized_inner_shell_equation_bound Fm hm hcm L L hL le_rfl).2
  have hpv : |up L| ≤ V * Np := hpj.1
  have hmv : |um L| ≤ V * Nm := hmj.1
  have hpFun : (fun x : ℝ =>
      normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fp hp x / x) = up := by
    funext x
    rfl
  have hmFun : (fun x : ℝ =>
      normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) Fm hm x / x) = um := by
    funext x
    rfl
  have hpdRaw : L ^ 2 * |deriv up L| ≤ T * Np := by
    have h := hpj.2.1
    dsimp only at h
    rw [hpFun] at h
    exact h
  have hmdRaw : L ^ 2 * |deriv um L| ≤ T * Nm := by
    have h := hmj.2.1
    dsimp only at h
    rw [hmFun] at h
    exact h
  have hpd : |deriv up L| ≤ T * Np / L ^ 2 :=
    (le_div_iff₀ (pow_pos hLp 2)).2 ((mul_comm _ _).trans_le hpdRaw)
  have hmd : |deriv um L| ≤ T * Nm / L ^ 2 :=
    (le_div_iff₀ (pow_pos hLp 2)).2 ((mul_comm _ _).trans_le hmdRaw)
  have hU : ‖J.1‖ ≤ V * N := by
    change ‖(up (a * (L / a)) : ℂ) + Complex.I * (um (a * (L / a)) : ℂ)‖ ≤ _
    rw [hScale]
    exact ((obstruction_real_pair_norm _ _).trans (add_le_add hpv hmv)).trans_eq (by ring)
  have hDU : ‖J.2‖ ≤ a * T * N / L ^ 2 := by
    change ‖(a : ℂ) * (((deriv up (a * (L / a)) : ℝ) : ℂ) +
      Complex.I * ((deriv um (a * (L / a)) : ℝ) : ℂ))‖ ≤ _
    rw [hScale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left
      ((obstruction_real_pair_norm _ _).trans (add_le_add hpd hmd)) ha.le).trans_eq (by ring)
  have hr0 : 0 < L / a := div_pos hLp ha
  have hreg := origin_kummer_regular_physical_bound K D G hD hG hBR.le
    hcoeff hbound (L / a) ⟨hr0, hLB⟩
  have hInv := obstruction_inverse_wronskian_norm K (L / a) hr0 (hLB.trans hBR.le)
  have hRaw : ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
      ((V * N) * (2 * H * (L / a)) + (a * T * N / L ^ 2) * C0) * (L / a) ^ 2 := by
    unfold actualOriginOutgoingTrace
    rw [div_eq_mul_inv, norm_mul, hInv]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg (L / a))
    exact ((norm_sub_le _ _).trans_eq (by simp only [norm_mul])).trans
      (add_le_add
        (mul_le_mul hU hreg.2 (norm_nonneg _) (mul_nonneg hV hN))
        (mul_le_mul hDU hreg.1 (norm_nonneg _) (by positivity)))
  have hLcube : 1 ≤ L ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ L - 1 by linarith)
      (show 0 ≤ L ^ 2 + L + 1 by positivity)]
  have haOne : 1 ≤ a := hLcube.trans ha3
  have hLa2 : L ^ 3 ≤ a ^ 2 := ha3.trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr haOne) ha.le])
  have hRatio : L ^ 3 / a ^ 3 ≤ 1 / a := by
    apply (div_le_div_iff₀ (pow_pos ha 3) ha).2
    nlinarith [mul_le_mul_of_nonneg_right hLa2 ha.le]
  have hTraceCoeff : 0 ≤ 2 * H * V := by positivity
  calc
    _ ≤ ((V * N) * (2 * H * (L / a)) + (a * T * N / L ^ 2) * C0) * (L / a) ^ 2 := hRaw
    _ = (2 * H * V * (L ^ 3 / a ^ 3) + C0 * T / a) * N := by
      field_simp [ha.ne', hLp.ne']
    _ ≤ (2 * H * V * (1 / a) + C0 * T / a) * N :=
      mul_le_mul_of_nonneg_right
        (_root_.add_le_add (mul_le_mul_of_nonneg_left hRatio hTraceCoeff) le_rfl) hN
    _ = _ := by dsimp [actualMomentLockedObstructionTraceConstant, H, C0, V, T, N, Np, Nm]; ring

/-- Both parts of the full obstruction are bounded for one and the same
physical Hartree slice. Weighted source membership is constructed, not
assumed; the baseline jet is the actual canonical fixed-inverse output. -/
theorem actual_Hartree_moment_locked_full_obstruction_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (B0 A0 ell c a : ℝ) (hB0 : 0 ≤ B0) (hA0 : 0 ≤ A0)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hL : 2 < actualHartreeSlowInnerRadius ell)
    (ha3 : actualHartreeSlowInnerRadius ell ^ 3 ≤ a)
    (hLB : actualHartreeSlowInnerRadius ell / a ≤ B)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ r : ℝ, 0 < r → ‖z r‖ ≤ B0)
    (hStrauss : ∀ r : ℝ, 1 ≤ r → r * ‖z r‖ ≤ A0)
    (hcp : Continuous (actualHartreeTransmissionPlusSource ell c z))
    (hcm : Continuous (actualHartreeTransmissionMinusSource ell c z)) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let F := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
    ∃ (hp : InWeightedL2 (7 / 4 : ℝ) Fp) (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
      let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
      IntervalIntegrable (originGreenSourceA K F) volume (L / a) B ∧
      ‖actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2‖ ≤
        actualMomentLockedObstructionTraceConstant D G B / a *
          (innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm) +
        (1 + (D + 1) * G * B ^ 2) * B *
          actualHartreePhysicalWeightedSourceConstant B0 A0 * ell ^ (1 / 8 : ℝ) := by
  dsimp only
  let L := actualHartreeSlowInnerRadius ell
  let Fp := actualHartreeTransmissionPlusSource ell c z
  let Fm := actualHartreeTransmissionMinusSource ell c z
  let F : ℝ → ℂ := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  have hLp : 0 < L := by dsimp [L]; linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hSource := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B0 A0 hell hellOne hc hB0 hA0 z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) _ hSource.1 hSource.2.1
  have hp : InWeightedL2 (7 / 4 : ℝ) Fp := hPair.1
  have hm : InWeightedL2 (7 / 4 : ℝ) Fm := hPair.2
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  have hTrace := actual_Hartree_canonical_baseline_outgoing_trace_bound K D G B L a
    hD hG hBR hL ha3 hLB hcoeff hbound Fp Fm hp hm hcp hcm
  have hOuter := actual_Hartree_full_interval_Green_coefficient_bound K D G B (L / a)
    hD hG (div_pos hLp ha) hLB hBR hcoeff hbound B0 A0 ell c a
    hB0 hA0 hell hellOne hc ha z hz hSup hStrauss
  refine ⟨hp, hm, hOuter.1, ?_⟩
  change ‖actualOriginOutgoingTrace K (L / a) J.1 J.2 - originGreenCoeffA K B F (L / a)‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hTrace hOuter.2)

end HBL.TypeIIDynamicSelection
