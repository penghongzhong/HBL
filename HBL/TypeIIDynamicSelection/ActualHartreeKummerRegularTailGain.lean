import HBL.TypeIIDynamicSelection.ActualHartreeOriginOutgoingGain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# True-tail gain for the regular origin-Green coefficient

The inverse-square envelope is too coarse for the regular Green channel near
the moving inner endpoint.  Here we keep the already proved true physical
Hartree tail
  |S(y)| <= Q ell^(1/8) (1+y)^(-19/8).
After the exact origin Wronskian cancels r^2, the regular-channel density is
controlled by a multiple of
  a (a r)^(-11/8).
The change y=a r therefore removes the spatial rescaling completely and
gives the genuine tail L^(-3/8).

This is the regular Green coefficient only.  It is not yet the full upper
Cauchy jet or remote-region construction.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

private theorem regular_tail_inverse_wronskian_norm
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r : ℝ) (hr : 0 < r) (hrs : r ≤ scale) :
    ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
  have hW : originGreenWronskian K r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K ⟨hr.le, hrs⟩ hr.ne'
  have hE : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hE, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp

private theorem regular_tail_rpow_integral
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    IntervalIntegrable (fun r : ℝ => r ^ (-(11 / 8 : ℝ))) volume x y ∧
    (∫ r in x..y, r ^ (-(11 / 8 : ℝ))) ≤
      (8 / 3 : ℝ) * x ^ (-(3 / 8 : ℝ)) := by
  have hzero : (0 : ℝ) ∉ uIcc x y := by
    rw [uIcc_of_le hxy]
    intro h
    linarith [h.1]
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (-(11 / 8 : ℝ))) volume x y :=
    intervalIntegral.intervalIntegrable_rpow
      (Or.inr hzero)
  refine ⟨hi, ?_⟩
  rw [integral_rpow (a := x) (b := y)
    (r := -(11 / 8 : ℝ)) (Or.inr ⟨by norm_num, hzero⟩)]
  have hy0 : 0 ≤ y := hx.le.trans hxy
  have hyPow : 0 ≤ y ^ (-(3 / 8 : ℝ)) :=
    Real.rpow_nonneg hy0 _
  have hxPow : 0 ≤ x ^ (-(3 / 8 : ℝ)) :=
    Real.rpow_nonneg hx.le _
  norm_num
  linarith

/-- The true scaled Hartree source has a regular-channel Green coefficient
with L^(-3/8) gain.  In particular there is no B/(L/a) amplification and
no residual positive power of a. -/
theorem actual_Hartree_scaled_Kummer_regular_Green_tail_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G L R a B A ell c : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hL : 1 ≤ L) (ha : 0 < a)
    (hOrder : L / a ≤ R) (hRscale : R < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    let F := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
    ‖originGreenCoeffB K (L / a) F R‖ ≤
      (8 / 3 : ℝ) * G *
        (actualHartreePhysicalWeightedSourceConstant B A *
          ell ^ (1 / 8 : ℝ)) *
        L ^ (-(3 / 8 : ℝ)) := by
  dsimp only
  let F : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let M : ℝ :=
    actualHartreePhysicalWeightedSourceConstant B A * ell ^ (1 / 8 : ℝ)
  let r0 : ℝ := L / a
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < r0 := div_pos hLp ha
  have hRpos : 0 < R := hr0.trans_le hOrder
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg B A hB hA)
      (Real.rpow_nonneg hell.le _)
  have hK := origin_kummer_annulus_bound K r0 R G hr0 hRscale hG hbound
  have hFI : IntervalIntegrable F volume r0 R :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      B A ell c a r0 R hB hA hell hellOne hc ha hr0 hOrder
      z hz hSup hStrauss).neg
  have hIB := (actual_origin_Green_source_integrability K hK hOrder F hFI).2
  have hDensity (r : ℝ) (hr : r ∈ Icc r0 R) :
      ‖originGreenSourceB K F r‖ ≤
        G * M * a * (a * r) ^ (-(11 / 8 : ℝ)) := by
    have hrp : 0 < r := hr0.trans_le hr.1
    have har : 0 < a * r := mul_pos ha hrp
    have hary : L ≤ a * r := by
      have hh := (div_le_iff₀ ha).1 hr.1
      simpa only [mul_comm] using hh
    have hphys := actual_Hartree_physical_source_unweighted_pointwise
      B A ell c (a * r) hB hA hell hellOne hc har z hz hSup hStrauss
    have hF :
        ‖F r‖ ≤ a ^ 2 * M * (1 + a * r) ^ (-(19 / 8 : ℝ)) := by
      dsimp [F, M]
      rw [norm_neg, actualHartreeLaplacianScaledKummerSource, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hphys (sq_nonneg a))
    have hy := hbound r ⟨hrp.le, hr.2.trans hRscale.le⟩
    have hyPhys : ‖originPhysicalValue K.y r‖ ≤ G / r := by
      rw [originPhysicalValue, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hrp]
      exact div_le_div_of_nonneg_right hy.1 hrp.le
    have hInv := regular_tail_inverse_wronskian_norm K r hrp
      (hr.2.trans hRscale.le)
    have hTail :
        (a * r) * (1 + a * r) ^ (-(19 / 8 : ℝ)) ≤
          (a * r) ^ (-(11 / 8 : ℝ)) := by
      have hp :
          (1 + a * r) ^ (-(19 / 8 : ℝ)) ≤
            (a * r) ^ (-(19 / 8 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos har (by linarith) (by norm_num)
      calc
        _ ≤ (a * r) * (a * r) ^ (-(19 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hp har.le
        _ = (a * r) ^ (1 : ℝ) * (a * r) ^ (-(19 / 8 : ℝ)) := by
          rw [Real.rpow_one]
        _ = (a * r) ^ ((1 : ℝ) + (-(19 / 8 : ℝ))) :=
          (Real.rpow_add har (1 : ℝ) (-(19 / 8 : ℝ))).symm
        _ = (a * r) ^ (-(11 / 8 : ℝ)) := by
          congr 1
          norm_num
    rw [originGreenSourceB, div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      _ ≤ (G / r) *
          (a ^ 2 * M * (1 + a * r) ^ (-(19 / 8 : ℝ))) * r ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hyPhys hF (norm_nonneg _) (by positivity))
          (sq_nonneg r)
      _ = G * M * a * ((a * r) *
          (1 + a * r) ^ (-(19 / 8 : ℝ))) := by
        field_simp [hrp.ne']
      _ ≤ G * M * a * (a * r) ^ (-(11 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hTail (by positivity)
  have hScale (r : ℝ) (hr : 0 < r) :
      a * (a * r) ^ (-(11 / 8 : ℝ)) =
        a ^ (-(3 / 8 : ℝ)) * r ^ (-(11 / 8 : ℝ)) := by
    rw [Real.mul_rpow ha.le hr.le]
    calc
      a * (a ^ (-(11 / 8 : ℝ)) * r ^ (-(11 / 8 : ℝ))) =
          (a * a ^ (-(11 / 8 : ℝ))) * r ^ (-(11 / 8 : ℝ)) := by ring
      _ = (a ^ (1 : ℝ) * a ^ (-(11 / 8 : ℝ))) *
          r ^ (-(11 / 8 : ℝ)) := by rw [Real.rpow_one]
      _ = a ^ ((1 : ℝ) + (-(11 / 8 : ℝ))) *
          r ^ (-(11 / 8 : ℝ)) := by
            rw [Real.rpow_add ha]
      _ = a ^ (-(3 / 8 : ℝ)) * r ^ (-(11 / 8 : ℝ)) := by
        congr 2
        norm_num
  let Ctail : ℝ := G * M * a ^ (-(3 / 8 : ℝ))
  have hCtail : 0 ≤ Ctail := by
    dsimp [Ctail]
    positivity
  have hTailInt := regular_tail_rpow_integral r0 R hr0 hOrder
  have hMajor : IntervalIntegrable
      (fun r : ℝ => Ctail * r ^ (-(11 / 8 : ℝ))) volume r0 R :=
    hTailInt.1.const_mul Ctail
  have hNorm :
      ‖originGreenCoeffB K r0 F R‖ ≤
        ∫ r in r0..R, Ctail * r ^ (-(11 / 8 : ℝ)) := by
    unfold originGreenCoeffB
    apply intervalIntegral.norm_integral_le_of_norm_le hOrder
    · filter_upwards with r
      intro hrI
      have hrmem : r ∈ Icc r0 R := ⟨hrI.1.le, hrI.2⟩
      have hd := hDensity r hrmem
      have hd' :
          ‖originGreenSourceB K F r‖ ≤
            G * M * (a * (a * r) ^ (-(11 / 8 : ℝ))) := by
        simpa only [mul_assoc] using hd
      rw [hScale r (hr0.trans_le hrmem.1)] at hd'
      simpa only [Ctail, mul_assoc] using hd'
    · exact hMajor
  have hInt :
      (∫ r in r0..R, Ctail * r ^ (-(11 / 8 : ℝ))) ≤
        Ctail * ((8 / 3 : ℝ) * r0 ^ (-(3 / 8 : ℝ))) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hTailInt.2 hCtail
  have haPow : a ^ (-(3 / 8 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha _)
  have hCancel :
      a ^ (-(3 / 8 : ℝ)) * r0 ^ (-(3 / 8 : ℝ)) =
        L ^ (-(3 / 8 : ℝ)) := by
    dsimp [r0]
    rw [Real.div_rpow hLp.le ha.le]
    field_simp [haPow]
  calc
    ‖originGreenCoeffB K r0 F R‖ ≤
        ∫ r in r0..R, Ctail * r ^ (-(11 / 8 : ℝ)) := hNorm
    _ ≤ Ctail * ((8 / 3 : ℝ) * r0 ^ (-(3 / 8 : ℝ))) := hInt
    _ = (8 / 3 : ℝ) * G * M * L ^ (-(3 / 8 : ℝ)) := by
      dsimp [Ctail]
      rw [← hCancel]
      ring
    _ = _ := by rfl

end HBL.TypeIIDynamicSelection
