import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeGeneralSourceCorrection
import Mathlib.Tactic

/-!
# True 1/r tails of the modulation-speed outer sources

The coarse corrected-source envelope was intentionally written in the
inverse-square source class. For the two actual speed directions this loses
one power of radius. Keeping the genuine moment-locked profile tails gives
  |a^2 P_b(a r)| + |a^2 P_omega(a r)| <= C a/r
on the same physical parameter region. In the regular origin-Green channel
the singular physical basis contributes 1/r while the exact Wronskian
inverse contributes r^2, so the density is uniformly O(a) and its integral
is O(a B), with no logarithm and no L/a endpoint loss.

No compatibility inverse is used here; this is a reusable source estimate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual scale/phase speed sources have the true inverse-radius envelope. -/
theorem actual_Hartree_scaled_speed_outer_inverse_radius :
    ∃ C : ℝ, 0 < C ∧ ∀ (L c a B : ℝ),
      1 ≤ L → 0 < a → B ≤ 1 → a * |c| ≤ 1 →
      ∀ r ∈ Icc (L / a) B,
        ‖actualMomentLockedScaledScaleSource a c r‖ ≤ C * a / r ∧
        ‖actualMomentLockedScaledPhaseSource a c r‖ ≤ C * a / r := by
  obtain ⟨M, hM, hClose⟩ :=
    actual_Hartree_moment_locked_speed_profiles_uniform_close
  refine ⟨M + 3, by linarith, ?_⟩
  intro L c a B hL ha hB hSmall r hr
  have hLp : 0 < L := by linarith
  have hrp : 0 < r := (div_pos hLp ha).trans_le hr.1
  have htL : L ≤ a * r := by
    have h := (div_le_iff₀ ha).1 hr.1
    simpa only [mul_comm] using h
  have ht : 0 < a * r := mul_pos ha hrp
  have htOne : 1 ≤ a * r := hL.trans htL
  have htc : (a * r) * |c| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hSmall hrp.le
    nlinarith only [h, hr.2, hB]
  have hTail := bubble_two_speed_tail 1 (a * r) (by norm_num) htOne
  norm_num only [one_pow, div_one] at hTail
  have hScaleRef : |(a * r) * dilationGenerator bubble (a * r)| ≤ 3 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hTail.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hPhaseRef : |(a * r) * bubble (a * r)| ≤ 3 := by
    rw [abs_of_nonneg (mul_nonneg ht.le (bubble_nonneg _))]
    exact (radius_mul_bubble_le_one ht.le).trans (by norm_num)
  have hProfile (P P0 : ℝ) (href : |(a * r) * P0| ≤ 3)
      (hclose : |P - P0| ≤ M * |c|) :
      |(a * r) * P| ≤ M + 3 := by
    calc
      _ = |(a * r) * (P - P0) + (a * r) * P0| := by congr 1; ring
      _ ≤ |(a * r) * (P - P0)| + |(a * r) * P0| := abs_add_le _ _
      _ ≤ (a * r) * (M * |c|) + 3 := by
        rw [abs_mul, abs_of_pos ht]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hclose ht.le) href
      _ ≤ M + 3 := by
        nlinarith only [mul_le_mul_of_nonneg_left htc hM.le]
  have hScaled (P : ℝ) (hP : |(a * r) * P| ≤ M + 3) :
      a ^ 2 * |P| ≤ (M + 3) * a / r := by
    apply (le_div_iff₀ hrp).2
    have hprod : (a * r) * |P| ≤ M + 3 := by
      simpa only [abs_mul, abs_of_pos ht] using hP
    calc
      a ^ 2 * |P| * r = a * ((a * r) * |P|) := by ring
      _ ≤ a * (M + 3) :=
        mul_le_mul_of_nonneg_left hprod ha.le
      _ = (M + 3) * a := by ring
  constructor
  · simpa only [actualMomentLockedScaledScaleSource,
      actualMomentLockedScaleSource, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg a)] using
      hScaled _ (hProfile _ _ hScaleRef (hClose c (a * r) ht).1)
  · simpa only [actualMomentLockedScaledPhaseSource,
      actualMomentLockedPhaseSource, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg a)] using
      hScaled _ (hProfile _ _ hPhaseRef (hClose c (a * r) ht).2)

private theorem speed_regular_inverse_wronskian_norm
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

/-- The regular Green coefficients of both genuine speed sources are O(a B),
not logarithmically amplified at the moving left endpoint. -/
theorem actual_Hartree_speed_regular_Green_coefficients :
    ∃ C : ℝ, 0 < C ∧
      ∀ {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
        (G L c a B : ℝ),
        0 ≤ G → 1 ≤ L → 0 < a → B ≤ 1 → B < scale →
        a * |c| ≤ 1 → L / a ≤ B →
        (∀ r ∈ Icc 0 scale,
          ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
          ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G) →
        ‖originGreenCoeffB K (L / a)
            (actualMomentLockedScaledScaleSource a c) B‖ ≤ C * G * a * B ∧
        ‖originGreenCoeffB K (L / a)
            (actualMomentLockedScaledPhaseSource a c) B‖ ≤ C * G * a * B := by
  obtain ⟨C, hC, hSpeed⟩ :=
    actual_Hartree_scaled_speed_outer_inverse_radius
  refine ⟨C, hC, ?_⟩
  intro mu theta scale K G L c a B hG hL ha hBOne hBR hSmall hOrder hbound
  have hLp : 0 < L := by linarith
  have hr0 : 0 < L / a := div_pos hLp ha
  have hB : 0 < B := hr0.trans_le hOrder
  have hK :=
    origin_kummer_annulus_bound K (L / a) B G hr0 hBR hG hbound
  have hSpeedInt :=
    actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c (L / a) B ha hr0 hOrder
  have hGreenInt :=
    actual_origin_Green_source_integrability K hK hOrder
  have hDensity (F : ℝ → ℂ)
      (hF : ∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ C * a / r)
      (r : ℝ) (hr : r ∈ Icc (L / a) B) :
      ‖originGreenSourceB K F r‖ ≤ G * C * a := by
    have hrp : 0 < r := hr0.trans_le hr.1
    have hy := hbound r ⟨hrp.le, hr.2.trans hBR.le⟩
    have hyPhys : ‖originPhysicalValue K.y r‖ ≤ G / r := by
      rw [originPhysicalValue, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hrp]
      exact div_le_div_of_nonneg_right hy.1 hrp.le
    have hInv :=
      speed_regular_inverse_wronskian_norm K r hrp
        (hr.2.trans hBR.le)
    rw [originGreenSourceB, div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      _ ≤ (G / r) * (C * a / r) * r ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hyPhys (hF r hr) (norm_nonneg _)
            (by positivity)) (sq_nonneg r)
      _ = G * C * a := by field_simp [hrp.ne']
  have hCoeff (F : ℝ → ℂ)
      (hFI : IntervalIntegrable F volume (L / a) B)
      (hF : ∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ C * a / r) :
      ‖originGreenCoeffB K (L / a) F B‖ ≤ C * G * a * B := by
    have _hBI := (hGreenInt F hFI).2
    unfold originGreenCoeffB
    have hRaw :
        ‖∫ r in (L / a)..B, originGreenSourceB K F r‖ ≤
          (G * C * a) * |B - L / a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      rw [uIoc_of_le hOrder] at hr
      exact hDensity F hF r ⟨hr.1.le, hr.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hOrder)] at hRaw
    calc
      _ ≤ (G * C * a) * (B - L / a) := hRaw
      _ ≤ (G * C * a) * B :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = C * G * a * B := by ring
  have hs := hSpeed L c a B hL ha hBOne hSmall
  exact ⟨hCoeff _ hSpeedInt.1 (fun r hr => (hs r hr).1),
    hCoeff _ hSpeedInt.2 (fun r hr => (hs r hr).2)⟩

/-- The lower-endpoint regular Green coefficient is linear in the source,
on the complete actual interval. -/
theorem actual_moment_locked_regular_source_coefficient_add_mul_on
    {mu theta scale r0 r1 C0 : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K r0 r1 C0) (horder : r0 ≤ r1)
    (F G : ℝ → ℂ)
    (hF : IntervalIntegrable F volume r0 r1)
    (hG : IntervalIntegrable G volume r0 r1) (beta : ℂ) :
    originGreenCoeffB K r0 (fun r => F r + beta * G r) r1 =
      originGreenCoeffB K r0 F r1 +
        beta * originGreenCoeffB K r0 G r1 := by
  have hFI := (actual_origin_Green_source_integrability K hK horder F hF).2
  have hGI := (actual_origin_Green_source_integrability K hK horder G hG).2
  have hDensity : originGreenSourceB K (fun r => F r + beta * G r) =
      (fun r => originGreenSourceB K F r +
        beta * originGreenSourceB K G r) := by
    funext r
    unfold originGreenSourceB
    ring
  unfold originGreenCoeffB
  rw [hDensity, intervalIntegral.integral_add hFI (hGI.const_mul beta),
    intervalIntegral.integral_const_mul]

end HBL.TypeIIDynamicSelection
