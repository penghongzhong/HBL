import HBL.TypeIIDynamicSelection.ActualKummerTransmissionProjection

/-!
A shorter exact transmission route after the actual complex compatibility
projection has been cancelled. Add ONLY the original right-normalized
homogeneous mode to the original Green inverse. The forcing is unchanged.
Left matching is proved equivalent to vanishing of the computed projection;
vanishing for the physical parameter path is NOT assumed proved here.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginMatchingRegularCoefficient
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  (originPhysicalValue K.y R * (DU-originGreenSlope K R (2*R) F R) -
    originPhysicalSlope K.y K.dy R * (U-originGreenValue K R (2*R) F R)) /
    originGreenWronskian K R

def actualOriginProjectedValue
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  originGreenValue K R (2*R) F r +
    actualOriginMatchingRegularCoefficient K R F U DU * originPhysicalValue K.x r

def actualOriginProjectedSlope
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  originGreenSlope K R (2*R) F r +
    actualOriginMatchingRegularCoefficient K R F U DU * originPhysicalSlope K.x K.dx r

/-- The remaining left jet is exactly the ONE complex obstruction times
the original singular fundamental mode. No smallness estimate replaces it. -/
theorem actual_origin_projected_left_defect_exact
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (U DU : ℂ) :
    actualOriginProjectedValue K R F U DU R - U =
      -actualOriginTransmissionObstruction K R F U DU * originPhysicalValue K.y R ∧
    actualOriginProjectedSlope K R F U DU R - DU =
      -actualOriginTransmissionObstruction K R F U DU * originPhysicalSlope K.y K.dy R := by
  have hr : R ∈ Icc R (2*R) := ⟨le_refl _, by linarith⟩
  have hW := originGreenWronskian_ne K hK hr
  have hTrace := actual_origin_Green_outgoing_trace_coefficient K hK hr F
  have hB : actualOriginTransmissionObstruction K R F U DU =
      actualOriginOutgoingTrace K R (U-originGreenValue K R (2*R) F R)
        (DU-originGreenSlope K R (2*R) F R) := by
    unfold actualOriginTransmissionObstruction
    rw [← hTrace]
    unfold actualOriginOutgoingTrace
    ring
  rw [hB]
  constructor
  · unfold actualOriginProjectedValue actualOriginMatchingRegularCoefficient actualOriginOutgoingTrace
    field_simp [hW]
    unfold originGreenWronskian
    ring
  · unfold actualOriginProjectedSlope actualOriginMatchingRegularCoefficient actualOriginOutgoingTrace
    field_simp [hW]
    unfold originGreenWronskian
    ring

/-- Exact criterion, in both directions. The sole complex projection is
not replaced by an asserted boundary compatibility. -/
theorem actual_origin_projected_matching_iff_zero_obstruction
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (U DU : ℂ) :
    (actualOriginProjectedValue K R F U DU R = U ∧
      actualOriginProjectedSlope K R F U DU R = DU) ↔
      actualOriginTransmissionObstruction K R F U DU = 0 := by
  have hDef := actual_origin_projected_left_defect_exact K hR hK F U DU
  have hW := originGreenWronskian_ne K hK
    (show R ∈ Icc R (2*R) by constructor <;> linarith)
  constructor
  · intro hMatch
    rw [hMatch.1, sub_self] at hDef
    rw [hMatch.2, sub_self] at hDef
    have hv : actualOriginTransmissionObstruction K R F U DU *
        originPhysicalValue K.y R = 0 := by linear_combination hDef.1
    have hd : actualOriginTransmissionObstruction K R F U DU *
        originPhysicalSlope K.y K.dy R = 0 := by linear_combination hDef.2
    have hBW : actualOriginTransmissionObstruction K R F U DU *
        originGreenWronskian K R = 0 := by
      unfold originGreenWronskian
      linear_combination originPhysicalSlope K.x K.dx R * hv -
        originPhysicalValue K.x R * hd
    exact (mul_eq_zero.mp hBW).resolve_right hW
  · intro hZero
    rw [hZero, neg_zero, zero_mul, zero_mul] at hDef
    exact ⟨sub_eq_zero.mp hDef.1, sub_eq_zero.mp hDef.2⟩

/-- A homogeneous addition preserves the original right endpoint functional,
continuity and the actual a.e. equation with EXACTLY F, no repair forcing.
Left matching remains equivalent to the separately exposed projection. -/
theorem actual_origin_projected_transmission_same_equation
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume R (2*R)) (U DU : ℂ) :
    (actualOriginProjectedValue K R F U DU (2*R) * originPhysicalSlope K.x K.dx (2*R) -
      actualOriginProjectedSlope K R F U DU (2*R) * originPhysicalValue K.x (2*R) = 0) ∧
    ContinuousOn (actualOriginProjectedValue K R F U DU) (Icc R (2*R)) ∧
    ContinuousOn (actualOriginProjectedSlope K R F U DU) (Icc R (2*R)) ∧
    (∀ᵐ r ∂volume, r ∈ Icc R (2*R) →
      HasDerivAt (actualOriginProjectedValue K R F U DU)
        (actualOriginProjectedSlope K R F U DU r) r ∧
      HasDerivAt (actualOriginProjectedSlope K R F U DU)
        (F r - frozenFirstCoeff r * actualOriginProjectedSlope K R F U DU r -
          frozenZeroCoeff mu theta * actualOriginProjectedValue K R F U DU r) r) := by
  let beta := actualOriginMatchingRegularCoefficient K R F U DU
  have hCont := actual_origin_Green_integrable_continuous_pair K hK (by linarith) F hF
  have hPsi : ContinuousOn (originPhysicalValue K.x) (Icc R (2*R)) :=
    fun r hr => (hK r hr).2.2.1.continuousAt.continuousWithinAt
  have hDPsi : ContinuousOn (originPhysicalSlope K.x K.dx) (Icc R (2*R)) :=
    fun r hr => (hK r hr).2.2.2.1.continuousAt.continuousWithinAt
  refine ⟨?_, hCont.1.add (continuousOn_const.mul hPsi),
    hCont.2.add (continuousOn_const.mul hDPsi), ?_⟩
  · have hN := (originGreen_endpoint_normalization K R (2*R) F).2.2.1
    unfold actualOriginProjectedValue actualOriginProjectedSlope
    linear_combination hN
  · filter_upwards [actual_origin_Green_integrable_forcing_ae_equation
      K hK (by linarith) F hF] with r hr
    intro hmem
    obtain ⟨hU, hV, hEq⟩ := hr hmem
    have hpsi := (hK r hmem).2.2.1
    have hdpsi := (hK r hmem).2.2.2.1
    refine ⟨hU.add (hpsi.const_mul beta), ?_⟩
    convert hV.add (hdpsi.const_mul beta) using 1
    · rfl
    · dsimp [actualOriginProjectedValue, actualOriginProjectedSlope, beta]
      linear_combination -hEq

end HBL.TypeIIDynamicSelection
