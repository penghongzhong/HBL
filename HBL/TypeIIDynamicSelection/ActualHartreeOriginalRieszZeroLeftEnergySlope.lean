import HBL.TypeIIDynamicSelection.ActualHartreeKummerRegularTailGain
import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterraSlope
import HBL.KummerOriginBasis.RegularDerivativeBound
import Mathlib.Tactic

/-!
# Physical Hartree Riesz source: no shrinking-left-radius loss in radial energy slope

The true physical scaled source F0(r)=-a² S_H(a r) has BOTH
|F0(r)| <= Q/r² and a separate original, scale-sharp regular Green
coefficient bound O(Q L^(-3/8)).  Neither can be replaced by an
independent inverse-linear envelope |F0(r)|<=M/r as a shrinks.

The exact zero-left Cramer cancellation and the *regular* origin
Kummer mode imply a short-interval A-moment bound O(Q(r-r0)).
The regular B-channel is instead bounded by the verified genuine
original quartic Riesz tail.  Consequently r|u'(r)| is uniformly
bounded, independent of the moving left interface r0=L/a.
This is the coordinate required by the 3D radial Hdot1 density
r²|u'|². It does NOT impose an unweighted pointwise |u'| bound.

All source-size and integrability data below are produced from the
original Hartree interaction and actual radiation Strauss envelopes.
The moment identity is derived by interval-integrability and the
original Green source-integrability theorem, WITHOUT assuming
extra continuity of the physical source.
This is an auxiliary Cramer/energy estimate, not a full four-region
nonlocal PDE time-gain or a prescribed Type-II blowup exponent.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- True quartic Riesz source gives an *energy-weighted* zero-left radial
Kummer slope with constants independent of the shrinking left interface.
The regular Green coefficient is obtained from the actual original source,
not postulated as an unrelated bound. -/
theorem actual_Hartree_original_Riesz_zero_left_energy_weighted_slope_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G L B a Bz Az ell c : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hL : 1 ≤ L) (ha : 0 < a)
    (hOrder : L / a ≤ B) (hBscale : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hBz : 0 ≤ Bz) (hAz : 0 ≤ Az)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz)
    (hStrauss : ∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az)
    (r : ℝ) (hr : r ∈ Icc (L / a) B) :
    let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
      ell ^ (1 / 8 : ℝ)
    let J : ℝ := 1 + (D + 1) * G * B ^ 2
    let T : ℝ := ((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ))
    let F : ℝ → ℂ :=
      fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
    ‖(r : ℂ) * actualOriginMatchedKummerSlope K (L / a) B F 0 0 r‖ ≤
      (B + 1) * G * J * Q + 2 * (D + 1) * G * B ^ 2 * T := by
  dsimp only
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let J : ℝ := 1 + (D + 1) * G * B ^ 2
  let T : ℝ := ((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ))
  let F : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let E : ℝ := (B + 1) * G * J * Q +
    2 * (D + 1) * G * B ^ 2 * T
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < L / a := div_pos hLp ha
  have hrp : 0 < r := hr0.trans_le hr.1
  have hBp : 0 ≤ B := (hr0.trans_le hOrder).le
  have hrscale : r ∈ Icc 0 scale := ⟨hrp.le, hr.2.trans hBscale.le⟩
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg Bz Az hBz hAz)
      (Real.rpow_nonneg hell.le _)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hJQ : 0 ≤ J * Q := mul_nonneg hJ hQ
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hYconst : 0 ≤ (B + 1) * G := by positivity
  have hXconst : 0 ≤ 2 * (D + 1) * G := by positivity
  have hXFull : 0 ≤ 2 * (D + 1) * G * T := by positivity
  let Cbasis : ℝ := G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1
  have hK : OriginBasisOn K (L / a) B Cbasis :=
    origin_kummer_annulus_bound K (L / a) B G
      hr0 hBscale hG hbound
  let q : ℝ → ℂ := originGreenSourceA K F
  have hFI : IntervalIntegrable F volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a (L / a) B hBz hAz hell hellOne hc
      ha hr0 hOrder z hz hSup hStrauss).neg
  have hIq : IntervalIntegrable q volume (L / a) B := by
    simpa only [q] using
      (actual_origin_Green_source_integrability K hK hOrder F hFI).1
  have hIar : IntervalIntegrable q volume (L / a) r :=
    hIq.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le hOrder]
      exact Icc_subset_Icc_right hr.2)
  have hIrb : IntervalIntegrable q volume r B :=
    hIq.mono_set (by
      rw [uIcc_of_le hr.2, uIcc_of_le hOrder]
      exact Icc_subset_Icc_left hr.1)
  have hAdd := intervalIntegral.integral_add_adjacent_intervals hIar hIrb
  have hDifference :
      originGreenCoeffA K B F r -
        originGreenCoeffA K B F (L / a) =
        -(∫ x in (L / a)..r, q x) := by
    change (∫ x in r..B, q x) -
      (∫ x in (L / a)..B, q x) =
        -(∫ x in (L / a)..r, q x)
    rw [← hAdd]
    abel
  have hEnvelope (x : ℝ) (hx : x ∈ Icc (L / a) B) :
      ‖F x‖ ≤ Q / x ^ 2 := by
    have hxpos : 0 < x := hr0.trans_le hx.1
    have hPhys := actual_Hartree_scaled_Kummer_source_annulus_bound
      Bz Az ell c a x x hBz hAz hell hellOne hc
      ha hxpos le_rfl z hz hSup hStrauss
    simpa only [F, Q, norm_neg] using hPhys
  have hDensity (x : ℝ) (hx : x ∈ Icc (L / a) r) :
      ‖q x‖ ≤ J * Q := by
    have hxB : x ∈ Icc (L / a) B := ⟨hx.1, hx.2.trans hr.2⟩
    have hxpos : 0 < x := hr0.trans_le hx.1
    have hxscale : x ∈ Icc 0 scale :=
      ⟨hxpos.le, hxB.2.trans hBscale.le⟩
    have hX : ‖originPhysicalValue K.x x‖ ≤ J := by
      simpa only [J] using
        (origin_kummer_regular_physical_bound K D G hD hG
          hBscale.le hcoeff hbound x ⟨hxpos, hxB.2⟩).1
    have hWr := originGreenWronskian_exact K hK hxB
    have hExp :
        ‖Complex.exp (-Complex.I * (x : ℂ) ^ 2 / 4)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im, pow_two]
    have hInv : ‖(originGreenWronskian K x)⁻¹‖ = x ^ 2 := by
      rw [hWr, norm_inv, norm_mul, norm_pow, norm_inv,
        hExp, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hxpos]
      simp
    have hFQ : ‖F x‖ * x ^ 2 ≤ Q := by
      calc
        _ ≤ (Q / x ^ 2) * x ^ 2 :=
          mul_le_mul_of_nonneg_right (hEnvelope x hxB) (sq_nonneg x)
        _ = Q := by field_simp [hxpos.ne']
    change ‖originPhysicalValue K.x x * F x /
      originGreenWronskian K x‖ ≤ J * Q
    rw [div_eq_mul_inv, norm_mul, norm_mul, hInv]
    calc
      ‖originPhysicalValue K.x x‖ * ‖F x‖ * x ^ 2 =
        ‖originPhysicalValue K.x x‖ * (‖F x‖ * x ^ 2) := by ring
      _ ≤ J * Q :=
        mul_le_mul hX hFQ
          (mul_nonneg (norm_nonneg _) (sq_nonneg x)) hJ
  have hAIntegral :
      ‖∫ x in (L / a)..r, q x‖ ≤ (J * Q) * |r - L / a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hr.1] at hx
    exact hDensity x ⟨hx.1.le, hx.2⟩
  have hA :
      ‖originGreenCoeffA K B F r -
        originGreenCoeffA K B F (L / a)‖ ≤
        (J * Q) * (r - L / a) := by
    rw [hDifference, norm_neg]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hr.1)] using hAIntegral
  have hA2 :
      ‖originGreenCoeffA K B F r -
        originGreenCoeffA K B F (L / a)‖ ≤
        (J * Q) * r := by
    have hdist : r - L / a ≤ r := by linarith
    exact hA.trans (mul_le_mul_of_nonneg_left hdist hJQ)
  have hCoeffs := actual_Hartree_scaled_Kummer_both_Green_coefficients_uniform
    K D G L B a Bz Az ell c hD hG hL ha hOrder hBscale
    hcoeff hbound hBz hAz hell hellOne hc z hz hSup hStrauss r hr
  have hB :
      ‖originGreenCoeffB K (L / a) F r‖ ≤ T := by
    simpa only [T, F, Q, mul_assoc] using hCoeffs.2
  have hModes := hbound r hrscale
  have hY :
      ‖(r : ℂ) * K.dy r - K.y r‖ ≤ (B + 1) * G := by
    calc
      _ ≤ ‖(r : ℂ) * K.dy r‖ + ‖K.y r‖ := norm_sub_le _ _
      _ = r * ‖K.dy r‖ + ‖K.y r‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      _ ≤ r * G + G :=
        add_le_add (mul_le_mul_of_nonneg_left hModes.2.1 hrp.le)
          hModes.1
      _ ≤ B * G + G := by
        have hMul : r * G ≤ B * G :=
          mul_le_mul_of_nonneg_right hr.2 hG
        linarith
      _ = (B + 1) * G := by ring
  have hJet :=
    origin_kummer_regular_jet_bound K D G hD hG hcoeff hbound r hrscale
  have hX :
      ‖(r : ℂ) * K.dx r - K.x r‖ ≤
        (2 * (D + 1) * G) * r ^ 3 := by
    have hEq :
        (r : ℂ) * K.dx r - K.x r =
          (r : ℂ) * (K.dx r - 1) - (K.x r - (r : ℂ)) := by ring
    rw [hEq]
    calc
      _ ≤ ‖(r : ℂ) * (K.dx r - 1)‖ +
          ‖K.x r - (r : ℂ)‖ := norm_sub_le _ _
      _ = r * ‖K.dx r - 1‖ + ‖K.x r - (r : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      _ ≤ r * ((D + 1) * G * r ^ 2) +
          (D + 1) * G * r ^ 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hJet.2 hrp.le) hJet.1
      _ = (2 * (D + 1) * G) * r ^ 3 := by ring
  have hrSq : r ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hrp.le hr.2 2
  have hr3 : r ^ 3 ≤ B ^ 2 * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrSq) hrp.le]
  have hId :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_slope_identity
      K (L / a) B Cbasis hr0 hOrder hK F r hr
  have hScaled :
      ‖(r : ℂ) ^ 2 *
        actualOriginMatchedKummerSlope K (L / a) B F 0 0 r‖ ≤
      E * r := by
    rw [hId]
    calc
      ‖((r : ℂ) * K.dy r - K.y r) *
          (originGreenCoeffA K B F r -
            originGreenCoeffA K B F (L / a)) +
        ((r : ℂ) * K.dx r - K.x r) *
          originGreenCoeffB K (L / a) F r‖ ≤
        ‖(r : ℂ) * K.dy r - K.y r‖ *
          ‖originGreenCoeffA K B F r -
            originGreenCoeffA K B F (L / a)‖ +
        ‖(r : ℂ) * K.dx r - K.x r‖ *
          ‖originGreenCoeffB K (L / a) F r‖ := by
          simpa only [norm_mul] using
            (norm_add_le
              (((r : ℂ) * K.dy r - K.y r) *
                (originGreenCoeffA K B F r -
                  originGreenCoeffA K B F (L / a)))
              (((r : ℂ) * K.dx r - K.x r) *
                originGreenCoeffB K (L / a) F r))
      _ ≤ ((B + 1) * G) * ((J * Q) * r) +
          ((2 * (D + 1) * G) * r ^ 3) * T := by
        exact add_le_add
          (mul_le_mul hY hA2 (norm_nonneg _) hYconst)
          (mul_le_mul hX hB (norm_nonneg _)
            (mul_nonneg hXconst (pow_nonneg hrp.le 3)))
      _ = ((B + 1) * G * J * Q) * r +
          (2 * (D + 1) * G * T) * r ^ 3 := by ring
      _ ≤ ((B + 1) * G * J * Q) * r +
          (2 * (D + 1) * G * T) * (B ^ 2 * r) :=
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hr3 hXFull)
      _ = E * r := by dsimp [E]; ring
  have hNorm :
      ‖(r : ℂ) ^ 2 * actualOriginMatchedKummerSlope K (L / a) B F 0 0 r‖ =
      r * ‖(r : ℂ) * actualOriginMatchedKummerSlope K (L / a) B F 0 0 r‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrp]
    ring
  rw [hNorm] at hScaled
  have hBudget :
      r * ‖(r : ℂ) * actualOriginMatchedKummerSlope K (L / a) B F 0 0 r‖ ≤
      r * E := by
    calc
      _ ≤ E * r := hScaled
      _ = r * E := by ring
  have hFinal :
      ‖(r : ℂ) * actualOriginMatchedKummerSlope K (L / a) B F 0 0 r‖ ≤
      E := (mul_le_mul_iff_of_pos_left hrp).mp hBudget
  simpa only [E, T, J, Q, F, mul_assoc] using hFinal

end HBL.TypeIIDynamicSelection
