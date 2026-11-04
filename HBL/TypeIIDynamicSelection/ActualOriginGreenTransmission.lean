import HBL.TypeIIDynamicSelection.ActualKummerInterfaceRepair
import HBL.TypeIIDynamicSelection.ActualHartreeOriginOutgoingGain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The original normalized Green solution is repaired using its ACTUAL left
mismatch. Both left coordinates match, both right coordinates are unchanged,
and the full extra forcing is included in the differential equation.
This removes a spurious exact-compatibility requirement from an approximate
parametrix; it does NOT remove the obligation to control and eliminate the
new forcing in the complete nonlinear Hartree residual.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualOriginTransmissionValue
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  originGreenValue K R (2*R) F r +
    actualKummerInterfaceRepair R
      (U-originGreenValue K R (2*R) F R)
      (DU-originGreenSlope K R (2*R) F R) r

def actualOriginTransmissionSlope
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  originGreenSlope K R (2*R) F r +
    actualKummerInterfaceRepairSlope R
      (U-originGreenValue K R (2*R) F R)
      (DU-originGreenSlope K R (2*R) F R) r

def actualOriginTransmissionDefect
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  actualKummerInterfaceRepairResidual mu theta R
    (U-originGreenValue K R (2*R) F R)
    (DU-originGreenSlope K R (2*R) F R) r

/-- The original integral-defined value/slope have continuous annular traces.
No continuity of F is assumed. -/
theorem actual_origin_Green_integrable_continuous_pair
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume a b) :
    ContinuousOn (originGreenValue K a b F) (Icc a b) ∧
    ContinuousOn (originGreenSlope K a b F) (Icc a b) := by
  obtain ⟨hIA,hIB⟩ := actual_origin_Green_source_integrability K hK hab F hF
  have hCA : ContinuousOn (originGreenCoeffA K b F) (Icc a b) := by
    have h := (intervalIntegral.continuousOn_primitive_interval' hIA right_mem_uIcc).neg
    rw [uIcc_of_le hab] at h
    convert h using 1
    funext r
    exact intervalIntegral.integral_symm b r
  have hCB : ContinuousOn (originGreenCoeffB K a F) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hIB left_mem_uIcc
    rw [uIcc_of_le hab] at h
    exact h
  have hp : ContinuousOn (originPhysicalValue K.y) (Icc a b) :=
    fun r hr => (hK r hr).1.continuousAt.continuousWithinAt
  have hdp : ContinuousOn (originPhysicalSlope K.y K.dy) (Icc a b) :=
    fun r hr => (hK r hr).2.1.continuousAt.continuousWithinAt
  have hq : ContinuousOn (originPhysicalValue K.x) (Icc a b) :=
    fun r hr => (hK r hr).2.2.1.continuousAt.continuousWithinAt
  have hdq : ContinuousOn (originPhysicalSlope K.x K.dx) (Icc a b) :=
    fun r hr => (hK r hr).2.2.2.1.continuousAt.continuousWithinAt
  exact ⟨(hp.mul hCA).add (hq.mul hCB), (hdp.mul hCA).add (hdq.mul hCB)⟩

/-- Exact controlled transmission of the ORIGINAL Green pair. Both endpoint
jets are identities, the slope is continuous on the closed annulus, and the
actual a.e. differential system retains the complete interface forcing. -/
theorem actual_origin_Green_repaired_transmission
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume R (2*R))
    (U DU : ℂ) :
    actualOriginTransmissionValue K R F U DU R = U ∧
    actualOriginTransmissionSlope K R F U DU R = DU ∧
    actualOriginTransmissionValue K R F U DU (2*R) = originGreenValue K R (2*R) F (2*R) ∧
    actualOriginTransmissionSlope K R F U DU (2*R) = originGreenSlope K R (2*R) F (2*R) ∧
    (actualOriginTransmissionValue K R F U DU (2*R) * originPhysicalSlope K.x K.dx (2*R) -
      actualOriginTransmissionSlope K R F U DU (2*R) * originPhysicalValue K.x (2*R) = 0) ∧
    ContinuousOn (actualOriginTransmissionValue K R F U DU) (Icc R (2*R)) ∧
    ContinuousOn (actualOriginTransmissionSlope K R F U DU) (Icc R (2*R)) ∧
    (∀ᵐ r ∂volume, r ∈ Icc R (2*R) →
      HasDerivAt (actualOriginTransmissionValue K R F U DU)
        (actualOriginTransmissionSlope K R F U DU r) r ∧
      HasDerivAt (actualOriginTransmissionSlope K R F U DU)
        (F r - frozenFirstCoeff r * actualOriginTransmissionSlope K R F U DU r -
          frozenZeroCoeff mu theta * actualOriginTransmissionValue K R F U DU r +
          actualOriginTransmissionDefect K R F U DU r) r) := by
  let p := U-originGreenValue K R (2*R) F R
  let q := DU-originGreenSlope K R (2*R) F R
  have hEnds := actual_Kummer_interface_repair_endpoint_jets R hR p q
  have hLeft : actualOriginTransmissionValue K R F U DU R = U := by
    change originGreenValue K R (2*R) F R + actualKummerInterfaceRepair R p q R = U
    rw [hEnds.1]
    dsimp [p]
    ring
  have hLeftD : actualOriginTransmissionSlope K R F U DU R = DU := by
    change originGreenSlope K R (2*R) F R + actualKummerInterfaceRepairSlope R p q R = DU
    rw [hEnds.2.1]
    dsimp [q]
    ring
  have hRight : actualOriginTransmissionValue K R F U DU (2*R) =
      originGreenValue K R (2*R) F (2*R) := by
    change originGreenValue K R (2*R) F (2*R) + actualKummerInterfaceRepair R p q (2*R) = _
    rw [hEnds.2.2.1, add_zero]
  have hRightD : actualOriginTransmissionSlope K R F U DU (2*R) =
      originGreenSlope K R (2*R) F (2*R) := by
    change originGreenSlope K R (2*R) F (2*R) + actualKummerInterfaceRepairSlope R p q (2*R) = _
    rw [hEnds.2.2.2, add_zero]
  have hCont := actual_origin_Green_integrable_continuous_pair K hK (by linarith) F hF
  have hLiftCont : Continuous (actualKummerInterfaceRepair R p q) :=
    continuous_iff_continuousAt.mpr (fun r =>
      (actual_Kummer_interface_repair_derivatives R r hR.ne' p q).1.continuousAt)
  have hSlopeCont : Continuous (actualKummerInterfaceRepairSlope R p q) :=
    continuous_iff_continuousAt.mpr (fun r =>
      (actual_Kummer_interface_repair_derivatives R r hR.ne' p q).2.continuousAt)
  refine ⟨hLeft,hLeftD,hRight,hRightD,?_,hCont.1.add hLiftCont.continuousOn,
    hCont.2.add hSlopeCont.continuousOn,?_⟩
  · rw [hRight,hRightD]
    exact (originGreen_endpoint_normalization K R (2*R) F).2.2.1
  · filter_upwards [actual_origin_Green_integrable_forcing_ae_equation
      K hK (by linarith) F hF] with r hr
    intro hmem
    obtain ⟨hU,hV,hEq⟩ := hr hmem
    have hLift := actual_Kummer_interface_repair_derivatives R r hR.ne' p q
    refine ⟨hU.add hLift.1, ?_⟩
    convert hV.add hLift.2 using 1
    · rfl
    · dsimp [actualOriginTransmissionValue, actualOriginTransmissionSlope,
        actualOriginTransmissionDefect, actualKummerInterfaceRepairResidual, p, q]
      linear_combination -hEq

/-- Residual control is inherited from the measured left mismatch. No
zero mismatch or extra positive order is inserted as a hypothesis. -/
theorem actual_origin_Green_transmission_defect_bound :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (mu theta scale R : ℝ) (K : OriginKummerPair mu theta scale),
      1 ≤ R → ∀ (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ), r ∈ Icc R (2*R) →
      ‖actualOriginTransmissionDefect K R F U DU r‖ ≤
        (9*C2+15*C1+3+‖frozenZeroCoeff mu theta‖) *
        (‖U-originGreenValue K R (2*R) F R‖ +
          R*‖DU-originGreenSlope K R (2*R) F R‖) := by
  obtain ⟨C1,C2,hC1,hC2,hBound⟩ := actual_Kummer_interface_repair_uniform_bound
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro mu theta scale R K hR F U DU r hr
  exact (hBound mu theta R r hR hr
    (U-originGreenValue K R (2*R) F R)
    (DU-originGreenSlope K R (2*R) F R)).2.2.2

end HBL.TypeIIDynamicSelection
