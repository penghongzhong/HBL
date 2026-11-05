import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorGrowth
import HBL.HartreeTailLeakage

/-!
# Actual matched-annulus contribution to the core Hartree feedback

The outer field is the SAME matched Kummer formula whose left Cauchy
jet is produced by the normalized inner Fredholm inverse. Its growth is
derived from the source data, not supplied. The genuine Hartree kernel
is then integrated on the whole physical annulus [L,aB]. This is an
exact contribution to the global nonlocal term; it does NOT set the
field to zero past aB or assert an infinity radiation condition.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

private theorem exterior_pair_norm (u v : ℝ) :
    ‖(u : ℂ) + Complex.I * (v : ℂ)‖ ≤ |u| + |v| := by
  exact (norm_add_le _ _).trans_eq (by
    simp [Complex.norm_real, Real.norm_eq_abs])

/-- Source-norm control of the actual two-coordinate Cauchy input. -/
theorem actual_Hartree_canonical_inner_jet_size
    (L a : ℝ) (hL : 2 < L) (ha : 0 < a)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (hcp : Continuous Fp) (hcm : Continuous Fm) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    ‖J.1‖ + (L / a) * ‖J.2‖ ≤
      (actualInnerShellValueConstant + actualInnerShellDerivativeConstant) *
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
  have hLp : 0 < L := by linarith
  have hT : 0 ≤ T := by dsimp [T, actualInnerShellDerivativeConstant]; positivity
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
    rw [hpFun] at h
    exact h
  have hmdRaw : L ^ 2 * |deriv um L| ≤ T * Nm := by
    have h := hmj.2.1
    rw [hmFun] at h
    exact h
  have hpd : |deriv up L| ≤ T * Np / L ^ 2 :=
    (le_div_iff₀ (pow_pos hLp 2)).2 ((mul_comm _ _).trans_le hpdRaw)
  have hmd : |deriv um L| ≤ T * Nm / L ^ 2 :=
    (le_div_iff₀ (pow_pos hLp 2)).2 ((mul_comm _ _).trans_le hmdRaw)
  have hU : ‖J.1‖ ≤ V * N := by
    change ‖(up (a * (L / a)) : ℂ) + Complex.I * (um (a * (L / a)) : ℂ)‖ ≤ _
    rw [hScale]
    exact ((exterior_pair_norm _ _).trans (add_le_add hpv hmv)).trans_eq (by ring)
  have hDU : ‖J.2‖ ≤ a * T * N / L ^ 2 := by
    change ‖(a : ℂ) * (((deriv up (a * (L / a)) : ℝ) : ℂ) +
      Complex.I * ((deriv um (a * (L / a)) : ℝ) : ℂ))‖ ≤ _
    rw [hScale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left
      ((exterior_pair_norm _ _).trans (add_le_add hpd hmd)) ha.le).trans_eq (by ring)
  have hScaled : (L / a) * ‖J.2‖ ≤ T * N := by
    calc
      _ ≤ (L / a) * (a * T * N / L ^ 2) :=
        mul_le_mul_of_nonneg_left hDU (div_nonneg hLp.le ha.le)
      _ = T * N / L := by field_simp [hLp.ne', ha.ne']
      _ ≤ T * N := div_le_self (mul_nonneg hT hN) (by linarith)
  exact (add_le_add hU hScaled).trans_eq (by ring)

/-- This constant is independent of L,a and all input source functions. -/
def actualMatchedExteriorSourceConstant (D G B : ℝ) : ℝ :=
  actualMatchedExteriorGrowthConstant D G B *
    (1 + actualInnerShellValueConstant + actualInnerShellDerivativeConstant)

private theorem exterior_finite_quadratic_tail
    (L U r M : ℝ) (hL : 0 < L) (hOrder : L ≤ U) (hr : 0 < r)
    (hsep : 2 * r ≤ L) (hM : 0 ≤ M) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc L U))
    (hBound : ∀ y ∈ Icc L U, |q y| ≤ M * y ^ 2 / L) :
    IntervalIntegrable (fun y => hartreeKernel r y * q y) volume L U ∧
      |∫ y in L..U, hartreeKernel r y * q y| ≤
        32 * Real.pi * hartreeKappa * M * r * bubble r ^ 3 / L ^ 2 := by
  let A := 4 * |8 * Real.pi * hartreeKappa| * M * r * bubble r ^ 3 / L
  have hA : 0 ≤ A := by dsimp [A]; unfold bubble; positivity
  have hP : ContinuousOn (fun y : ℝ => y⁻¹ ^ 2) (Icc L U) := by
    intro y hy
    exact (((hasDerivAt_id y).inv (hL.trans_le hy.1).ne').continuousAt.pow 2).continuousWithinAt
  have hPI : IntervalIntegrable (fun y : ℝ => y⁻¹ ^ 2) volume L U :=
    hP.intervalIntegrable_of_Icc hOrder
  have hMajor : IntervalIntegrable (fun y : ℝ => A * y⁻¹ ^ 2) volume L U := hPI.const_mul A
  have hPoint (y : ℝ) (hy : y ∈ Icc L U) :
      |hartreeKernel r y * q y| ≤ A * y⁻¹ ^ 2 := by
    have hyp : 0 < y := hL.trans_le hy.1
    have hk := hartreeKernel_separated_ordered y r hyp hr (hsep.trans hy.1)
    rw [hartreeKernel_symm y r, ← bubble_pow_three_eq_bracket] at hk
    rw [abs_mul]
    calc
      _ ≤ ((4 * |8 * Real.pi * hartreeKappa|) * y⁻¹ ^ 4 * r * bubble r ^ 3) *
          (M * y ^ 2 / L) := mul_le_mul hk (hBound y hy) (abs_nonneg _)
            (by unfold bubble; positivity)
      _ = A * y⁻¹ ^ 2 := by
        dsimp [A]
        field_simp [hyp.ne', hL.ne']
  have hKMeas : Measurable (fun y => hartreeKernel r y) :=
    hartreeKernel_uncurry_measurable.comp (measurable_const.prodMk measurable_id)
  have hqMeas : AEStronglyMeasurable q (volume.restrict (uIoc L U)) := by
    rw [uIoc_of_le hOrder]
    exact (hq.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hInt : IntervalIntegrable (fun y => hartreeKernel r y * q y) volume L U := by
    apply hMajor.mono_fun' (hKMeas.aestronglyMeasurable.restrict.mul hqMeas)
    rw [uIoc_of_le hOrder]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa only [Real.norm_eq_abs] using hPoint y (Ioc_subset_Icc_self hy)
  have hDeriv (y : ℝ) (hy : y ∈ uIcc L U) :
      HasDerivAt (fun x : ℝ => -x⁻¹) (y⁻¹ ^ 2) y := by
    rw [uIcc_of_le hOrder] at hy
    convert ((hasDerivAt_id y).inv (hL.trans_le hy.1).ne').neg using 1 <;>
      simp [one_div, inv_pow]
  have hIntegral : (∫ y : ℝ in L..U, y⁻¹ ^ 2) = L⁻¹ - U⁻¹ := by
    simpa only [neg_sub_neg] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hPI
  refine ⟨hInt, ?_⟩
  calc
    |∫ y in L..U, hartreeKernel r y * q y| ≤
        ∫ y in L..U, |hartreeKernel r y * q y| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm hOrder
    _ ≤ ∫ y in L..U, A * y⁻¹ ^ 2 :=
      intervalIntegral.integral_mono_on hOrder hInt.abs hMajor hPoint
    _ = A * (L⁻¹ - U⁻¹) := by rw [intervalIntegral.integral_const_mul, hIntegral]
    _ ≤ A * L⁻¹ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (inv_nonneg.mpr (hL.le.trans hOrder))) hA
    _ = _ := by
      dsimp [A]
      rw [abs_of_nonneg (show 0 ≤ 8 * Real.pi * hartreeKappa by unfold hartreeKappa; positivity)]
      simp only [div_eq_mul_inv, inv_pow]
      ring

/-- The full finite matched-annulus tail acting on the separated core.
The source norm, initial jet and exterior field all refer to the same
fixed normalized inverse. No growth estimate for that field is assumed.
The annulus ends at aB: feedback from beyond aB is NOT discarded. -/
theorem actual_Hartree_matched_exterior_core_feedback
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B L a : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hL : 2 < L) (ha : 0 < a) (hLB : L / a ≤ B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧ ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (hcp : Continuous Fp) (hcm : Continuous Fm)
    (F : ℝ → ℂ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hFC : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (hEnvelope : ∀ x ∈ Icc (L / a) B, ‖F x‖ ≤ Q / x ^ 2)
    (r : ℝ) (hr : 0 < r) (hsep : 2 * r ≤ L) :
    let N := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let q := fun y => y * (actualOriginMatchedKummerValue K (L / a) B F J.1 J.2 (y / a)).re
    IntervalIntegrable (fun y => hartreeKernel r y * q y) volume L (a * B) ∧
      |∫ y in L..(a * B), hartreeKernel r y * q y| ≤
        32 * Real.pi * hartreeKappa * actualMatchedExteriorSourceConstant D G B *
          (N + Q) * r * bubble r ^ 3 / L ^ 2 := by
  dsimp only
  let N := innerWeightedNorm (7 / 4 : ℝ) Fp + innerWeightedNorm (7 / 4 : ℝ) Fm
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let w := actualOriginMatchedKummerValue K (L / a) B F J.1 J.2
  let q := fun y => y * (w (y / a)).re
  let H0 := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let C := actualMatchedExteriorSourceConstant D G B
  let M := C * (N + Q)
  have hLp : 0 < L := by linarith
  have hr0 : 0 < L / a := div_pos hLp ha
  have hOrder : L ≤ a * B := by
    have h := (div_le_iff₀ ha).1 hLB
    simpa only [mul_comm] using h
  have hN : 0 ≤ N := add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hH0 : 0 ≤ H0 := by
    dsimp [H0, actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hCG : 0 ≤ actualMatchedExteriorGrowthConstant D G B := by
    unfold actualMatchedExteriorGrowthConstant
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, actualMatchedExteriorSourceConstant]
    have : 0 ≤ 1 + actualInnerShellValueConstant + actualInnerShellDerivativeConstant := by
      change 0 ≤ 1 + H0
      positivity
    exact mul_nonneg hCG this
  have hM : 0 ≤ M := mul_nonneg hC (add_nonneg hN hQ)
  have hFI : IntervalIntegrable F volume (L / a) B :=
    (show ContinuousOn F (Icc (L / a) B) from fun x hx =>
      (hFC x ⟨hr0.trans_le hx.1, hx.2.trans_lt hBR⟩).continuousWithinAt).intervalIntegrable_of_Icc hLB
  have hJet : ‖J.1‖ + (L / a) * ‖J.2‖ ≤ H0 * N :=
    actual_Hartree_canonical_inner_jet_size L a hL ha Fp Fm hp hm hcp hcm
  have hBudget : ‖J.1‖ + (L / a) * ‖J.2‖ + Q ≤ (1 + H0) * (N + Q) := by
    nlinarith [mul_nonneg hH0 hQ]
  have hArg (y : ℝ) (hy : y ∈ Icc L (a * B)) : y / a ∈ Icc (L / a) B := by
    refine ⟨div_le_div_of_nonneg_right hy.1 ha.le, ?_⟩
    exact (div_le_iff₀ ha).2 (by simpa only [mul_comm] using hy.2)
  have hClass := actual_origin_matched_Kummer_classical_on_positive_interval K hr0 hLB hBR F hFC J.1 J.2
  have hqCont : ContinuousOn q (Icc L (a * B)) := by
    intro y hy
    have hx := hArg y hy
    have hc := ((hClass (y / a) ⟨hr0.trans_le hx.1, hx.2.trans_lt hBR⟩).1.continuousAt).comp
      (continuous_id.div_const a).continuousAt
    exact (continuousAt_id.mul (Complex.continuous_re.continuousAt.comp hc)).continuousWithinAt
  have hqBound (y : ℝ) (hy : y ∈ Icc L (a * B)) : |q y| ≤ M * y ^ 2 / L := by
    have hyp : 0 < y := hLp.trans_le hy.1
    have hGrowth := actual_matched_Kummer_outward_growth K D G B (L / a) hD hG hr0 hLB hBOne hBR
      hcoeff hbound F Q hQ hFI hEnvelope J.1 J.2 (y / a) (hArg y hy)
    have hScale : (y / a) / (L / a) = y / L := by field_simp [ha.ne', hLp.ne']
    rw [hScale] at hGrowth
    have hw : ‖w (y / a)‖ ≤ M * (y / L) := by
      exact hGrowth.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBudget hCG) (div_nonneg hyp.le hLp.le)).trans_eq (by
          dsimp [M, C, actualMatchedExteriorSourceConstant, H0]
          ring))
    dsimp [q]
    rw [abs_mul, abs_of_pos hyp]
    calc
      _ ≤ y * ‖w (y / a)‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hyp.le
      _ ≤ y * (M * (y / L)) := mul_le_mul_of_nonneg_left hw hyp.le
      _ = _ := by ring
  have hTail := exterior_finite_quadratic_tail L (a * B) r M hLp hOrder hr hsep hM q hqCont hqBound
  exact ⟨hTail.1, hTail.2.trans_eq (by dsimp [M]; ring)⟩

end HBL.TypeIIDynamicSelection
