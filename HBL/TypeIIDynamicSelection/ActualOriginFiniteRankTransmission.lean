import HBL.TypeIIDynamicSelection.ActualOriginProjectionCancellation

/-!
An actual finite-rank augmented inverse for the original Kummer transmission.
The correction direction is the complete frozen residual of the already
verified smooth endpoint lift applied to the ORIGINAL singular basis jet.
Its projection is proved equal to ONE by the exact Wronskian identity.
No inverse matching Jacobian, zero obstruction or new physical mode is assumed.

For every integrable F and every incoming pair, the unique correction
coefficient is the computed obstruction. The corrected source is explicit;
it is NOT claimed to be the unchanged source or an already identified
physical modulation tangent. Matching at infinity and nonlinear recursion
remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- A source-independent direction made from the actual smooth lift and
original singular basis. Both derivative and drift terms are retained. -/
def actualOriginCompatibilitySource
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) : ℝ → ℂ :=
  actualKummerInterfaceRepairResidual mu theta R
    (originPhysicalValue K.y R) (originPhysicalSlope K.y K.dy R)

/-- The direction is integrable and its original outgoing projection is 1.
The normalization follows from the actual nonzero Wronskian, not a premise. -/
theorem actual_origin_compatibility_source_unit_projection
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C) :
    IntervalIntegrable (actualOriginCompatibilitySource K R) volume R (2*R) ∧
    IntervalIntegrable (originGreenSourceA K (actualOriginCompatibilitySource K R))
      volume R (2*R) ∧
    originGreenCoeffA K (2*R) (actualOriginCompatibilitySource K R) R = 1 := by
  have hCont : ContinuousOn (actualOriginCompatibilitySource K R)
      (uIcc R (2*R)) := by
    rw [uIcc_of_le (by linarith : R ≤ 2*R)]
    exact actual_Kummer_interface_defect_continuousOn mu theta R hR
      (originPhysicalValue K.y R) (originPhysicalSlope K.y K.dy R)
  have hProj := actual_Kummer_interface_defect_projection_exact K hR hK
    (originPhysicalValue K.y R) (originPhysicalSlope K.y K.dy R)
  have hW := originGreenWronskian_ne K hK
    (show R ∈ Icc R (2*R) by constructor <;> linarith)
  have hTrace : actualOriginOutgoingTrace K R
      (originPhysicalValue K.y R) (originPhysicalSlope K.y K.dy R) = 1 := by
    change originGreenWronskian K R / originGreenWronskian K R = 1
    exact div_self hW
  exact ⟨hCont.intervalIntegrable, hProj.1, hProj.2.trans hTrace⟩

/-- Exact source linearity is used only for genuinely integrable densities. -/
theorem actual_origin_source_coefficient_add_mul
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F G : ℝ → ℂ)
    (hF : IntervalIntegrable F volume R (2*R))
    (hG : IntervalIntegrable G volume R (2*R)) (beta : ℂ) :
    originGreenCoeffA K (2*R) (fun r => F r + beta * G r) R =
      originGreenCoeffA K (2*R) F R + beta * originGreenCoeffA K (2*R) G R := by
  have hFI := (actual_origin_Green_source_integrability K hK (by linarith) F hF).1
  have hGI := (actual_origin_Green_source_integrability K hK (by linarith) G hG).1
  have hDensity : originGreenSourceA K (fun r => F r + beta * G r) =
      (fun r => originGreenSourceA K F r + beta * originGreenSourceA K G r) := by
    funext r
    unfold originGreenSourceA
    ring
  unfold originGreenCoeffA
  rw [hDensity, intervalIntegral.integral_add hFI (hGI.const_mul beta),
    intervalIntegral.integral_const_mul]

/-- Exact affine dependence on the added source amplitude. This is NOT
an assertion about the derivative with respect to physical mu/theta. -/
theorem actual_origin_compatibility_amplitude_exact
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume R (2*R))
    (U DU beta : ℂ) :
    actualOriginTransmissionObstruction K R
      (fun r => F r + beta * actualOriginCompatibilitySource K R r) U DU =
      actualOriginTransmissionObstruction K R F U DU - beta := by
  have hMode := actual_origin_compatibility_source_unit_projection K hR hK
  unfold actualOriginTransmissionObstruction
  rw [actual_origin_source_coefficient_add_mul K hR hK F
    (actualOriginCompatibilitySource K R) hF hMode.1 beta, hMode.2.2]
  ring

/-- The source amplitude is uniquely determined, rather than supplied as
an unproved solvability or nondegeneracy assumption. -/
theorem actual_origin_compatibility_unique_cancellation
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume R (2*R)) (U DU : ℂ) :
    ∃! beta : ℂ, actualOriginTransmissionObstruction K R
      (fun r => F r + beta * actualOriginCompatibilitySource K R r) U DU = 0 := by
  refine ⟨actualOriginTransmissionObstruction K R F U DU, ?_, ?_⟩
  · rw [actual_origin_compatibility_amplitude_exact K hR hK F hF U DU, sub_self]
  · intro beta hBeta
    rw [actual_origin_compatibility_amplitude_exact K hR hK F hF U DU] at hBeta
    exact (sub_eq_zero.mp hBeta).symm

/-- The explicit corrected source. Its difference from F is one complex
rank, i.e. two real source directions. It is never silently discarded. -/
def actualOriginFiniteRankSource
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  F r + actualOriginTransmissionObstruction K R F U DU *
    actualOriginCompatibilitySource K R r

/-- Actual finite-rank augmented transmission: arbitrary incoming jets,
exact right finite-annulus normalization and the full corrected equation.
No zero-obstruction hypothesis occurs. This does not claim the uncorrected
physical source has acquired a stronger order. -/
theorem actual_origin_finite_rank_exact_transmission
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume R (2*R)) (U DU : ℂ) :
    let Faug := actualOriginFiniteRankSource K R F U DU
    IntervalIntegrable Faug volume R (2*R) ∧
    actualOriginProjectedValue K R Faug U DU R = U ∧
    actualOriginProjectedSlope K R Faug U DU R = DU ∧
    (actualOriginProjectedValue K R Faug U DU (2*R) * originPhysicalSlope K.x K.dx (2*R) -
      actualOriginProjectedSlope K R Faug U DU (2*R) * originPhysicalValue K.x (2*R) = 0) ∧
    ContinuousOn (actualOriginProjectedValue K R Faug U DU) (Icc R (2*R)) ∧
    ContinuousOn (actualOriginProjectedSlope K R Faug U DU) (Icc R (2*R)) ∧
    (∀ᵐ r ∂volume, r ∈ Icc R (2*R) →
      HasDerivAt (actualOriginProjectedValue K R Faug U DU)
        (actualOriginProjectedSlope K R Faug U DU r) r ∧
      HasDerivAt (actualOriginProjectedSlope K R Faug U DU)
        (F r + actualOriginTransmissionObstruction K R F U DU *
          actualOriginCompatibilitySource K R r -
          frozenFirstCoeff r * actualOriginProjectedSlope K R Faug U DU r -
          frozenZeroCoeff mu theta * actualOriginProjectedValue K R Faug U DU r) r) := by
  let Faug := actualOriginFiniteRankSource K R F U DU
  have hMode := actual_origin_compatibility_source_unit_projection K hR hK
  have hAug : IntervalIntegrable Faug volume R (2*R) :=
    hF.add (hMode.1.const_mul (actualOriginTransmissionObstruction K R F U DU))
  have hZero : actualOriginTransmissionObstruction K R Faug U DU = 0 := by
    change actualOriginTransmissionObstruction K R
      (fun r => F r + actualOriginTransmissionObstruction K R F U DU *
        actualOriginCompatibilitySource K R r) U DU = 0
    rw [actual_origin_compatibility_amplitude_exact K hR hK F hF U DU, sub_self]
  have hMatch := (actual_origin_projected_matching_iff_zero_obstruction
    K hR hK Faug U DU).mpr hZero
  have hEquation := actual_origin_projected_transmission_same_equation
    K hR hK Faug hAug U DU
  exact ⟨hAug, hMatch.1, hMatch.2, hEquation⟩

/-- The concrete source direction has a fixed annular bound chosen before
any forcing, incoming pair, physical length or radiation field. -/
theorem actual_origin_compatibility_source_bounded
    {mu theta scale R : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 1 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc R (2*R), ‖actualOriginCompatibilitySource K R r‖ ≤ M := by
  obtain ⟨C1,C2,hC1,hC2,hBound⟩ := actual_Kummer_interface_repair_uniform_bound
  refine ⟨(9*C2+15*C1+3+‖frozenZeroCoeff mu theta‖) *
      (‖originPhysicalValue K.y R‖ + R*‖originPhysicalSlope K.y K.dy R‖),
    by positivity, ?_⟩
  intro r hr
  exact (hBound mu theta R r hR hr
    (originPhysicalValue K.y R) (originPhysicalSlope K.y K.dy R)).2.2.2

end HBL.TypeIIDynamicSelection
