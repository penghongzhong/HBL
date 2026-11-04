import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummer

/-!
The original matched Green formula is genuinely differentiable at BOTH
matching endpoints.  Its integral limits stay fixed at a,b, while the
actual origin basis is certified on a larger positive annulus around the
evaluation point.  Thus the FTC applies in a full neighborhood, including
when the evaluation point equals a or b.

The result identifies the named slope with the actual derivative and the
original Kummer equation with the actual second derivative.  No endpoint
derivative, artificial extension, or compatibility hypothesis is assumed.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

private theorem actual_origin_basis_on_positive_annulus
    {mu theta scale a b : ℝ} (K : OriginKummerPair mu theta scale)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale) :
    ∃ C : ℝ, OriginBasisOn K a b C := by
  have hscale : 0 < scale := (ha.trans_le hab).trans hb
  let D : ℝ := scale / 2 + ‖originZeroCoeff mu theta‖
  let G : ℝ := Real.exp ((D + 1) * scale)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D := by
    intro r hr
    have hFirst : ‖originFirstCoeff r‖ = r / 2 := by
      simp [originFirstCoeff, abs_of_nonneg hr.1]
    rw [hFirst]
    dsimp [D]
    linarith [hr.2]
  exact ⟨_, origin_kummer_annulus_bound K a b G ha hb (Real.exp_pos _).le
    (origin_kummer_pair_bound K D hD hcoeff)⟩

private theorem actual_origin_matched_Kummer_derivatives_in_larger_annulus
    {mu theta scale lo hi a b C r : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K lo hi C) (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi)
    (F : ℝ → ℂ) (hF : Continuous F) (U DU : ℂ) (hr : r ∈ Ioo lo hi) :
    HasDerivAt (actualOriginMatchedKummerValue K a b F U DU)
      (actualOriginMatchedKummerSlope K a b F U DU r) r ∧
    HasDerivAt (actualOriginMatchedKummerSlope K a b F U DU)
      (F r - frozenFirstCoeff r * actualOriginMatchedKummerSlope K a b F U DU r -
        frozenZeroCoeff mu theta * actualOriginMatchedKummerValue K a b F U DU r) r := by
  have hc := originGreen_sources_continuous K hK F hF
  have hr' : r ∈ Icc lo hi := ⟨hr.1.le, hr.2.le⟩
  have hmA := hc.2.1.stronglyMeasurableAtFilter_nhdsWithin
    (μ := volume) measurableSet_Icc r
  have hmB := hc.2.2.stronglyMeasurableAtFilter_nhdsWithin
    (μ := volume) measurableSet_Icc r
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hr.1 hr.2)] at hmA hmB
  have hA : HasDerivAt (originGreenCoeffA K b F) (-originGreenSourceA K F r) r :=
    intervalIntegral.integral_hasDerivAt_left
      (hc.2.1.mono (uIcc_subset_Icc hr' hb)).intervalIntegrable hmA (hc.1 r hr').1
  have hB : HasDerivAt (originGreenCoeffB K a F) (originGreenSourceB K F r) r :=
    intervalIntegral.integral_hasDerivAt_right
      (hc.2.2.mono (uIcc_subset_Icc ha hr')).intervalIntegrable hmB (hc.1 r hr').2
  rcases hK r hr' with ⟨hphi, hdphi, hpsi, hdpsi, _, hW, _, _, _, _, _⟩
  have hValue : HasDerivAt (originGreenValue K a b F)
      (originGreenSlope K a b F r) r := by
    convert (hphi.mul hA).add (hpsi.mul hB) using 1
    · rfl
    · unfold originGreenSlope originGreenSourceA originGreenSourceB
      ring
  have hSlope : HasDerivAt (originGreenSlope K a b F)
      (originGreenSecond K a b F r) r := by
    convert (hdphi.mul hA).add (hdpsi.mul hB) using 1
    · rfl
    · unfold originGreenSecond originGreenSourceA originGreenSourceB originGreenWronskian
      field_simp [hW]
      ring
  have hEq := originGreen_equation K a b F r
  refine ⟨(hValue.add (hphi.const_mul _)).add (hpsi.const_mul _), ?_⟩
  convert (hSlope.add (hdphi.const_mul (actualOriginMatchedSingularCoeff K a b F U DU))).add
    (hdpsi.const_mul (actualOriginMatchedRegularCoeff K a b F U DU)) using 1
  · rfl
  · dsimp only [actualOriginMatchedKummerValue, actualOriginMatchedKummerSlope]
    linear_combination -hEq

/-- The fixed-endpoint Green/Cramer formula satisfies the actual classical
Kummer equation throughout the positive domain of the constructed origin
basis. In particular a and b are ordinary interior differentiation points. -/
theorem actual_origin_matched_Kummer_classical_on_positive_interval
    {mu theta scale a b : ℝ} (K : OriginKummerPair mu theta scale)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (F : ℝ → ℂ) (hF : Continuous F) (U DU : ℂ) :
    ∀ r ∈ Ioo 0 scale,
      HasDerivAt (actualOriginMatchedKummerValue K a b F U DU)
        (actualOriginMatchedKummerSlope K a b F U DU r) r ∧
      HasDerivAt (deriv (actualOriginMatchedKummerValue K a b F U DU))
        (F r - frozenFirstCoeff r * actualOriginMatchedKummerSlope K a b F U DU r -
          frozenZeroCoeff mu theta * actualOriginMatchedKummerValue K a b F U DU r) r ∧
      deriv (deriv (actualOriginMatchedKummerValue K a b F U DU)) r +
          frozenFirstCoeff r * deriv (actualOriginMatchedKummerValue K a b F U DU) r +
          frozenZeroCoeff mu theta * actualOriginMatchedKummerValue K a b F U DU r = F r := by
  have hPair (r : ℝ) (hr : r ∈ Ioo 0 scale) :
      HasDerivAt (actualOriginMatchedKummerValue K a b F U DU)
        (actualOriginMatchedKummerSlope K a b F U DU r) r ∧
      HasDerivAt (actualOriginMatchedKummerSlope K a b F U DU)
        (F r - frozenFirstCoeff r * actualOriginMatchedKummerSlope K a b F U DU r -
          frozenZeroCoeff mu theta * actualOriginMatchedKummerValue K a b F U DU r) r := by
    let lo : ℝ := min a r / 2
    let hi : ℝ := (max b r + scale) / 2
    have hlo : 0 < lo := by dsimp [lo]; exact div_pos (lt_min ha hr.1) (by norm_num)
    have hla : lo < a := by dsimp [lo]; linarith [min_le_left a r]
    have hlr : lo < r := by dsimp [lo]; linarith [min_le_right a r, hr.1]
    have hbh : b < hi := by dsimp [hi]; linarith [le_max_left b r]
    have hrh : r < hi := by dsimp [hi]; linarith [le_max_right b r, hr.2]
    have hhi : hi < scale := by
      have hm : max b r < scale := max_lt_iff.mpr ⟨hb, hr.2⟩
      dsimp [hi]
      linarith
    obtain ⟨C, hK⟩ := actual_origin_basis_on_positive_annulus K hlo (hlr.trans hrh).le hhi
    exact actual_origin_matched_Kummer_derivatives_in_larger_annulus K hK
      ⟨hla.le, hab.trans hbh.le⟩ ⟨hla.le.trans hab, hbh.le⟩ F hF U DU ⟨hlr, hrh⟩
  intro r hr
  have h := hPair r hr
  have heq : deriv (actualOriginMatchedKummerValue K a b F U DU) =ᶠ[𝓝 r]
      actualOriginMatchedKummerSlope K a b F U DU := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact (hPair x hx).1.deriv
  have hSecond := h.2.congr_of_eventuallyEq heq
  refine ⟨h.1, hSecond, ?_⟩
  rw [hSecond.deriv, h.1.deriv]
  ring

/-- The actual left derivative equals the input slope, and the actual
second derivative obeys the original equation there. The right endpoint
also has an ordinary two-sided derivative equal to the explicit slope. -/
theorem actual_origin_matched_Kummer_actual_endpoint_jets
    {mu theta scale a b : ℝ} (K : OriginKummerPair mu theta scale)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (F : ℝ → ℂ) (hF : Continuous F) (U DU : ℂ) :
    actualOriginMatchedKummerValue K a b F U DU a = U ∧
    HasDerivAt (actualOriginMatchedKummerValue K a b F U DU) DU a ∧
    deriv (actualOriginMatchedKummerValue K a b F U DU) a = DU ∧
    HasDerivAt (deriv (actualOriginMatchedKummerValue K a b F U DU))
      (F a - frozenFirstCoeff a * DU - frozenZeroCoeff mu theta * U) a ∧
    HasDerivAt (actualOriginMatchedKummerValue K a b F U DU)
      (actualOriginMatchedKummerSlope K a b F U DU b) b := by
  obtain ⟨C, hK⟩ := actual_origin_basis_on_positive_annulus K ha hab hb
  have hLeft := actual_origin_matched_Kummer_left_jet_and_unique_coefficients K hK hab F U DU
  have hClass := actual_origin_matched_Kummer_classical_on_positive_interval K ha hab hb F hF U DU
  have hAtLeft := hClass a ⟨ha, hab.trans_lt hb⟩
  have hFirst : HasDerivAt (actualOriginMatchedKummerValue K a b F U DU) DU a := by
    simpa only [hLeft.2.1] using hAtLeft.1
  refine ⟨hLeft.1, hFirst, hFirst.deriv, ?_, (hClass b ⟨ha.trans_le hab, hb⟩).1⟩
  simpa only [hLeft.1, hLeft.2.1] using hAtLeft.2.1

/-- The finite upper compatibility condition is now expressed using the
ACTUAL derivative of the continued profile, with the complete original source. -/
theorem actual_origin_matched_Kummer_actual_upper_trace
    {mu theta scale a b : ℝ} (K : OriginKummerPair mu theta scale)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (F : ℝ → ℂ) (hF : Continuous F) (U DU : ℂ) :
    actualOriginOutgoingTrace K b (actualOriginMatchedKummerValue K a b F U DU b)
      (deriv (actualOriginMatchedKummerValue K a b F U DU) b) =
      actualMomentLockedIntervalObstruction K a b F U DU := by
  obtain ⟨C, hK⟩ := actual_origin_basis_on_positive_annulus K ha hab hb
  have h := actual_origin_matched_Kummer_classical_on_positive_interval
    K ha hab hb F hF U DU b ⟨ha.trans_le hab, hb⟩
  rw [h.1.deriv]
  exact actual_origin_matched_Kummer_upper_trace K hK hab F U DU

end HBL.TypeIIDynamicSelection
