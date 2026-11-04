import HBL.TypeIIDynamicSelection.ActualKummerImpulseKernel
import Mathlib.Tactic

/-!
Complete nonhomogeneous Kummer transfer. Interval integrability is sufficient;
no false C2 assertion for a merely measurable forcing is made. The SAME original
Green integrals are rewritten as actual Wronskian impulse integrals. Their
radius-uniform estimate uses the already verified homogeneous shear at each
source point. In particular the forced-charge reference is no longer hidden
inside an unestimated particular solution. Outgoing compatibility is distinct.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Exact Duhamel representation of the existing physical Kummer transfer
with zero left Cauchy data. Both actual Green coefficients are retained. -/
theorem actual_Kummer_zero_data_Duhamel_exact
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ)
    (hFI : IntervalIntegrable (fun s => F (z+s)) volume (-d) d) :
    (actualKummerPhysicalRightTransfer K d F 0 0).1 =
      ∫ s in (-d)..d, actualKummerImpulseValue K s d * F (z+s) ∧
    (actualKummerPhysicalRightTransfer K d F 0 0).2 =
      ∫ s in (-d)..d, actualKummerImpulseSlope K s d * F (z+s) := by
  let f : ℝ → ℂ := fun s => F (z+s)
  let IA : ℂ := localAnnulusCoeffA K d f (-d)
  let IB : ℂ := localAnnulusCoeffB K (-d) f d
  have ht : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hSub : Icc (-d) d ⊆ Icc (-eps) eps := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hCoeffCont :
      ContinuousOn (fun s => K.psi s / localAnnulusWronskian K s) [[-d,d]] ∧
      ContinuousOn (fun s => K.phi s / localAnnulusWronskian K s) [[-d,d]] := by
    rw [uIcc_of_le (by linarith : -d ≤ d)]
    constructor
    · intro s hs
      have H := hSub hs
      have hW := ((K.phi_hasDeriv s H).continuousAt.mul
        (K.dpsi_hasDeriv s H).continuousAt).sub
        ((K.dphi_hasDeriv s H).continuousAt.mul (K.psi_hasDeriv s H).continuousAt)
      exact ((K.psi_hasDeriv s H).continuousAt.div hW
        (K.wronskian_ne s H)).continuousWithinAt
    · intro s hs
      have H := hSub hs
      have hW := ((K.phi_hasDeriv s H).continuousAt.mul
        (K.dpsi_hasDeriv s H).continuousAt).sub
        ((K.dphi_hasDeriv s H).continuousAt.mul (K.psi_hasDeriv s H).continuousAt)
      exact ((K.phi_hasDeriv s H).continuousAt.div hW
        (K.wronskian_ne s H)).continuousWithinAt
  have hA : IntervalIntegrable (localAnnulusSourceA K f) volume (-d) d := by
    convert hFI.continuousOn_mul hCoeffCont.1 using 1
    funext s
    dsimp [localAnnulusSourceA, f]
    ring
  have hB : IntervalIntegrable (localAnnulusSourceB K f) volume (-d) d := by
    convert hFI.continuousOn_mul hCoeffCont.2 using 1
    funext s
    dsimp [localAnnulusSourceB, f]
    ring
  have hLeftV : physicalLocalKummerValue K d F (z-d) = K.phi (-d) * IA := by
    simp [physicalLocalKummerValue, localAnnulusValue,
      localAnnulusCoeffA, localAnnulusCoeffB, IA, f,
      show z-d-z = -d by ring]
  have hLeftD : physicalLocalKummerDeriv K d F (z-d) = K.dphi (-d) * IA := by
    simp [physicalLocalKummerDeriv, localAnnulusDeriv,
      localAnnulusCoeffA, localAnnulusCoeffB, IA, f,
      show z-d-z = -d by ring]
  have hRightV : physicalLocalKummerValue K d F (z+d) = K.psi d * IB := by
    simp [physicalLocalKummerValue, localAnnulusValue,
      localAnnulusCoeffA, localAnnulusCoeffB, IB, f,
      show z+d-z = d by ring]
  have hRightD : physicalLocalKummerDeriv K d F (z+d) = K.dpsi d * IB := by
    simp [physicalLocalKummerDeriv, localAnnulusDeriv,
      localAnnulusCoeffA, localAnnulusCoeffB, IB, f,
      show z+d-z = d by ring]
  have hUnique := actual_Kummer_Wronskian_Cauchy_coefficients_unique K (-d) ht
    (0 - physicalLocalKummerValue K d F (z-d))
    (0 - physicalLocalKummerDeriv K d F (z-d)) (-IA) 0
    (by rw [hLeftV]; ring) (by rw [hLeftD]; ring)
  have ha : actualKummerLeftMatchPhi K d F 0 0 = -IA := hUnique.1.symm
  have hc : actualKummerLeftMatchPsi K d F 0 0 = 0 := hUnique.2.symm
  have hV : (actualKummerPhysicalRightTransfer K d F 0 0).1 =
      K.psi d * IB - K.phi d * IA := by
    change physicalLocalKummerValue K d F (z+d) +
      actualKummerLeftMatchPhi K d F 0 0 * K.phi (z+d-z) +
      actualKummerLeftMatchPsi K d F 0 0 * K.psi (z+d-z) = _
    rw [ha, hc, hRightV, show z+d-z = d by ring]
    ring
  have hD : (actualKummerPhysicalRightTransfer K d F 0 0).2 =
      K.dpsi d * IB - K.dphi d * IA := by
    change physicalLocalKummerDeriv K d F (z+d) +
      actualKummerLeftMatchPhi K d F 0 0 * K.dphi (z+d-z) +
      actualKummerLeftMatchPsi K d F 0 0 * K.dpsi (z+d-z) = _
    rw [ha, hc, hRightD, show z+d-z = d by ring]
    ring
  have hVF : (fun s => actualKummerImpulseValue K s d * F (z+s)) =
      (fun s => K.psi d * localAnnulusSourceB K f s -
        K.phi d * localAnnulusSourceA K f s) := by
    funext s
    dsimp [actualKummerImpulseValue, actualKummerMatchPhi,
      actualKummerMatchPsi, localAnnulusSourceA, localAnnulusSourceB, f]
    ring
  have hDF : (fun s => actualKummerImpulseSlope K s d * F (z+s)) =
      (fun s => K.dpsi d * localAnnulusSourceB K f s -
        K.dphi d * localAnnulusSourceA K f s) := by
    funext s
    dsimp [actualKummerImpulseSlope, actualKummerMatchPhi,
      actualKummerMatchPsi, localAnnulusSourceA, localAnnulusSourceB, f]
    ring
  constructor
  · rw [hV, hVF, intervalIntegral.integral_sub (hB.const_mul (K.psi d))
      (hA.const_mul (K.phi d)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl
  · rw [hD, hDF, intervalIntegral.integral_sub (hB.const_mul (K.dpsi d))
      (hA.const_mul (K.dphi d)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl

/-- Uniform actual source-to-jet bound for the ZERO-DATA particular
solution on a dyadic annulus. Source integrability is visible, not assumed
C2 regularity. This controls the term canceled in a same-source comparison. -/
theorem actual_Kummer_zero_data_scaled_source_bound
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d M : ℝ) (hd : 0 < d) (hde : d < eps)
    (hRatio : z + d ≤ 2 * (z-d)) (hM : 0 ≤ M)
    (F : ℝ → ℂ)
    (hFI : IntervalIntegrable (fun s => F (z+s)) volume (-d) d)
    (hF : ∀ s ∈ Icc (-d) d, ‖F (z+s)‖ ≤ M) :
    max ‖(actualKummerPhysicalRightTransfer K d F 0 0).1‖
      ((z+d) * ‖(actualKummerPhysicalRightTransfer K d F 0 0).2‖) ≤
      actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) *
        (2 * (z-d)^2 * M) := by
  let C := actualKummerUniformTransferConstant (frozenZeroCoeff mu theta)
  have hC : 0 ≤ C := by dsimp [C, actualKummerUniformTransferConstant]; positivity
  have hr0 : 0 < z-d := by
    simpa only [sub_eq_add_neg] using K.radial_pos (-d)
      (show -d ∈ Icc (-eps) eps from ⟨by linarith, by linarith⟩)
  have hr1 : 0 < z+d := by linarith
  have hKernel (s : ℝ) (hs : s ∈ Icc (-d) d) :
      ‖actualKummerImpulseValue K s d‖ ≤ C * (z+d) ∧
      ‖actualKummerImpulseSlope K s d‖ ≤ C := by
    have h := actual_Kummer_impulse_scaled_uniform K d s hd hde hRatio hs
    have hUpper : C * (z+s) ≤ C * (z+d) :=
      mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC
    constructor
    · exact ((le_max_left _ _).trans h).trans hUpper
    · apply (mul_le_mul_left hr1).mp
      exact (((le_max_right _ _).trans h).trans hUpper).trans_eq (by ring)
  obtain ⟨hDV,hDD⟩ := actual_Kummer_zero_data_Duhamel_exact K d hd hde F hFI
  have hVal : ‖(actualKummerPhysicalRightTransfer K d F 0 0).1‖ ≤
      (C * (z+d) * M) * (2*d) := by
    rw [hDV]
    have hI : ‖∫ s in (-d)..d, actualKummerImpulseValue K s d * F (z+s)‖ ≤
        (C * (z+d) * M) * |d - (-d)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le (by linarith : -d ≤ d)] at hs
      have hs' : s ∈ Icc (-d) d := Ioc_subset_Icc_self hs
      rw [norm_mul]
      exact mul_le_mul (hKernel s hs').1 (hF s hs')
        (norm_nonneg _) (mul_nonneg hC hr1.le)
    exact hI.trans_eq (by rw [abs_of_pos (by linarith : 0 < d - (-d))]; ring)
  have hSlope : ‖(actualKummerPhysicalRightTransfer K d F 0 0).2‖ ≤
      (C * M) * (2*d) := by
    rw [hDD]
    have hI : ‖∫ s in (-d)..d, actualKummerImpulseSlope K s d * F (z+s)‖ ≤
        (C * M) * |d - (-d)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le (by linarith : -d ≤ d)] at hs
      have hs' : s ∈ Icc (-d) d := Ioc_subset_Icc_self hs
      rw [norm_mul]
      exact mul_le_mul (hKernel s hs').2 (hF s hs') (norm_nonneg _) hC
    exact hI.trans_eq (by rw [abs_of_pos (by linarith : 0 < d - (-d))]; ring)
  have hMax : max ‖(actualKummerPhysicalRightTransfer K d F 0 0).1‖
      ((z+d) * ‖(actualKummerPhysicalRightTransfer K d F 0 0).2‖) ≤
      (C * (z+d) * M) * (2*d) := by
    apply max_le hVal
    exact (mul_le_mul_of_nonneg_left hSlope hr1.le).trans_eq (by ring)
  have hWidth : 2*d ≤ z-d := by linarith
  have hProd : (z+d)*(2*d) ≤ (2*(z-d))*(z-d) :=
    mul_le_mul hRatio hWidth (by positivity) (by positivity)
  have hScaled := mul_le_mul_of_nonneg_left hProd (mul_nonneg hC hM)
  exact hMax.trans (by nlinarith [hScaled])

/-- The FULL actual physical Kummer transfer, including the inhomogeneous
source contribution. The estimate is independent of radius and basis
normalization; no boundary compatibility or blowup rate is inserted. -/
theorem actual_Kummer_full_source_scaled_transfer_uniform
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d M : ℝ) (hd : 0 < d) (hde : d < eps)
    (hRatio : z+d ≤ 2*(z-d)) (hM : 0 ≤ M)
    (F : ℝ → ℂ)
    (hFI : IntervalIntegrable (fun s => F (z+s)) volume (-d) d)
    (hF : ∀ s ∈ Icc (-d) d, ‖F (z+s)‖ ≤ M)
    (U DU : ℂ) :
    max ‖(actualKummerPhysicalRightTransfer K d F U DU).1‖
      ((z+d) * ‖(actualKummerPhysicalRightTransfer K d F U DU).2‖) ≤
      actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) *
        (max ‖U‖ ((z-d)*‖DU‖) + 2*(z-d)^2*M) := by
  let C := actualKummerUniformTransferConstant (frozenZeroCoeff mu theta)
  let T := actualKummerPhysicalRightTransfer K d F U DU
  let Z := actualKummerPhysicalRightTransfer K d F 0 0
  let H := max ‖U‖ ((z-d)*‖DU‖)
  have hr1 : 0 < z+d := K.radial_pos d
    (show d ∈ Icc (-eps) eps from ⟨by linarith, by linarith⟩)
  have hD : max ‖T.1-Z.1‖ ((z+d)*‖T.2-Z.2‖) ≤ C*H := by
    simpa only [sub_zero] using
      actual_Kummer_same_source_scaled_transfer_uniform K d hd hde hRatio F U DU 0 0
  have hZ := actual_Kummer_zero_data_scaled_source_bound K d M hd hde hRatio hM F hFI hF
  have hv : ‖T.1‖ ≤ C*H + C*(2*(z-d)^2*M) := by
    calc
      ‖T.1‖ = ‖(T.1-Z.1)+Z.1‖ := by congr 1; ring
      _ ≤ ‖T.1-Z.1‖+‖Z.1‖ := norm_add_le _ _
      _ ≤ C*H + C*(2*(z-d)^2*M) := _root_.add_le_add
        ((le_max_left _ _).trans hD) ((le_max_left _ _).trans hZ)
  have hdv : (z+d)*‖T.2‖ ≤ C*H + C*(2*(z-d)^2*M) := by
    have hn : ‖T.2‖ ≤ ‖T.2-Z.2‖+‖Z.2‖ := by
      calc
        ‖T.2‖ = ‖(T.2-Z.2)+Z.2‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    calc
      (z+d)*‖T.2‖ ≤ (z+d)*(‖T.2-Z.2‖+‖Z.2‖) :=
        mul_le_mul_of_nonneg_left hn hr1.le
      _ = (z+d)*‖T.2-Z.2‖+(z+d)*‖Z.2‖ := by ring
      _ ≤ C*H + C*(2*(z-d)^2*M) := _root_.add_le_add
        ((le_max_right _ _).trans hD) ((le_max_right _ _).trans hZ)
  exact (max_le hv hdv).trans_eq (by ring)

end HBL.TypeIIDynamicSelection
