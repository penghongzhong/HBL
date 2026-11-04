import HBL.TypeIIDynamicSelection.ActualOriginGreenTransmission
import HBL.KummerLocalODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The retained transmission defect has a non-arbitrary resonant projection.
The flux identity is integrated using the actual smooth repair, the original
origin-gauge Wronskian and genuinely integrable densities. It identifies the
missing two-real-component compatibility quantity, rather than declaring
that a small defect has higher order or that boundary matching is automatic.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.Profile.Kummer

/-- Normalized outgoing finite-annulus Wronskian trace. -/
def actualOriginOutgoingTrace
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r : ℝ) (U DU : ℂ) : ℂ :=
  (U * originPhysicalSlope K.x K.dx r -
    DU * originPhysicalValue K.x r) / originGreenWronskian K r

/-- The actual compatibility quantity, including the complete source integral. -/
def actualOriginTransmissionObstruction
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  actualOriginOutgoingTrace K R U DU - originGreenCoeffA K (2*R) F R

/-- Exact Lagrange identity for the actual complex frozen operator. -/
theorem actual_origin_outgoing_flux_hasDerivAt
    {mu theta scale a b C r : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hr : r ∈ Icc a b)
    (w dw ddw : ℝ → ℂ)
    (hw : HasDerivAt w (dw r) r) (hdw : HasDerivAt dw (ddw r) r) :
    HasDerivAt (fun t => actualOriginOutgoingTrace K t (w t) (dw t))
      (-originGreenSourceA K
        (fun t => ddw t + frozenFirstCoeff t * dw t +
          frozenZeroCoeff mu theta * w t) r) r := by
  rcases hK r hr with ⟨hphi, hdphi, hpsi, hdpsi, _, hWne, _, _, _, _, _⟩
  have hW : HasDerivAt (originGreenWronskian K)
      (-frozenFirstCoeff r * originGreenWronskian K r) r := by
    convert (hphi.mul hdpsi).sub (hdphi.mul hpsi) using 1
    · rfl
    · unfold originGreenWronskian
      ring
  have h := ((hw.mul hdpsi).sub (hdw.mul hpsi)).div hW hWne
  convert h using 1
  · rfl
  · unfold originGreenSourceA
    field_simp [hWne]
    ring

/-- The repair's full forcing is continuous on a positive annulus, hence
its Wronskian densities are genuinely integrable. -/
theorem actual_Kummer_interface_defect_continuousOn
    (mu theta R : ℝ) (hR : 0 < R) (p q : ℂ) :
    ContinuousOn (actualKummerInterfaceRepairResidual mu theta R p q)
      (Icc R (2*R)) := by
  have hcut : ContDiff ℝ ∞ cutoff := cutoff_contDiff_infty
  have hw : ContDiff ℝ ∞ (actualKummerInterfaceRepair R p q) := by
    unfold actualKummerInterfaceRepair actualKummerRepairCutoff actualOneLayerInnerOverlapCutoff
    fun_prop
  have hOne : deriv (actualKummerInterfaceRepair R p q) =
      actualKummerInterfaceRepairSlope R p q :=
    funext (fun r => (actual_Kummer_interface_repair_derivatives R r hR.ne' p q).1.deriv)
  have hTwo : deriv (deriv (actualKummerInterfaceRepair R p q)) =
      actualKummerInterfaceRepairSecond R p q := by
    funext r
    rw [hOne]
    exact (actual_Kummer_interface_repair_derivatives R r hR.ne' p q).2.deriv
  have hdw : Continuous (actualKummerInterfaceRepairSlope R p q) := by
    rw [← hOne]
    exact (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hddw : Continuous (actualKummerInterfaceRepairSecond R p q) := by
    rw [← hTwo]
    exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hw).2).2.continuous
  intro r hr
  have hr0 : 0 < r := hR.trans_le hr.1
  exact ((hddw.continuousAt.add
    ((frozenFirstCoeff_contDiffAt r hr0.ne').continuousAt.mul hdw.continuousAt)).add
    (continuousAt_const.mul hw.continuous.continuousAt)).continuousWithinAt

/-- Integrated projection of the actual repair. Its value depends on the
endpoint mismatch, not on an artificially assigned source order. -/
theorem actual_Kummer_interface_defect_projection_exact
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C) (p q : ℂ) :
    IntervalIntegrable
      (originGreenSourceA K (actualKummerInterfaceRepairResidual mu theta R p q))
      volume R (2*R) ∧
    (∫ r in R..(2*R),
      originGreenSourceA K (actualKummerInterfaceRepairResidual mu theta R p q) r) =
      actualOriginOutgoingTrace K R p q := by
  let w := actualKummerInterfaceRepair R p q
  let dw := actualKummerInterfaceRepairSlope R p q
  let E := actualKummerInterfaceRepairResidual mu theta R p q
  have hEI : IntervalIntegrable E volume R (2*R) :=
    (actual_Kummer_interface_defect_continuousOn mu theta R hR p q).intervalIntegrable
  have hAI := (actual_origin_Green_source_integrability K hK (by linarith) E hEI).1
  have hFlux (r : ℝ) (hr : r ∈ Icc R (2*R)) :
      HasDerivAt (fun t => actualOriginOutgoingTrace K t (w t) (dw t))
        (-originGreenSourceA K E r) r := by
    have hder := actual_Kummer_interface_repair_derivatives R r hR.ne' p q
    exact actual_origin_outgoing_flux_hasDerivAt K hK hr w dw
      (actualKummerInterfaceRepairSecond R p q) hder.1 hder.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hFlux r (by simpa only [uIcc_of_le (by linarith : R ≤ 2*R)] using hr))
    hAI.neg
  have hEnds := actual_Kummer_interface_repair_endpoint_jets R hR p q
  have hLeft : actualOriginOutgoingTrace K R (w R) (dw R) =
      actualOriginOutgoingTrace K R p q := by
    change actualOriginOutgoingTrace K R
      (actualKummerInterfaceRepair R p q R)
      (actualKummerInterfaceRepairSlope R p q R) = _
    rw [hEnds.1, hEnds.2.1]
  have hRight : actualOriginOutgoingTrace K (2*R) (w (2*R)) (dw (2*R)) = 0 := by
    change actualOriginOutgoingTrace K (2*R)
      (actualKummerInterfaceRepair R p q (2*R))
      (actualKummerInterfaceRepairSlope R p q (2*R)) = 0
    rw [hEnds.2.2.1, hEnds.2.2.2]
    simp only [actualOriginOutgoingTrace, zero_mul, sub_self, zero_div]
  rw [intervalIntegral.integral_neg, hRight, hLeft, zero_sub] at hFTC
  exact ⟨hAI, neg_injective hFTC⟩

/-- The original Green integral is exactly its outgoing Wronskian trace. -/
theorem actual_origin_Green_outgoing_trace_coefficient
    {mu theta scale a b C r : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hr : r ∈ Icc a b) (F : ℝ → ℂ) :
    actualOriginOutgoingTrace K r (originGreenValue K a b F r)
      (originGreenSlope K a b F r) = originGreenCoeffA K b F r := by
  have hWne := originGreenWronskian_ne K hK hr
  have hNum : originGreenValue K a b F r * originPhysicalSlope K.x K.dx r -
      originGreenSlope K a b F r * originPhysicalValue K.x r =
      originGreenWronskian K r * originGreenCoeffA K b F r := by
    unfold originGreenValue originGreenSlope originGreenWronskian
    ring
  unfold actualOriginOutgoingTrace
  rw [hNum]
  field_simp

/-- Same-source exact balance: the retained defect is precisely the missing
finite-annulus compatibility projection. Full source and defect are both
included, with their integral existence certified. -/
theorem actual_origin_transmission_defect_projection_balance
    {mu theta scale R C : ℝ} (K : OriginKummerPair mu theta scale)
    (hR : 0 < R) (hK : OriginBasisOn K R (2*R) C)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume R (2*R)) (U DU : ℂ) :
    IntervalIntegrable
      (originGreenSourceA K (actualOriginTransmissionDefect K R F U DU))
      volume R (2*R) ∧
    (∫ r in R..(2*R), originGreenSourceA K
      (actualOriginTransmissionDefect K R F U DU) r) =
      actualOriginTransmissionObstruction K R F U DU ∧
    (∫ r in R..(2*R), originGreenSourceA K
      (fun t => F t + actualOriginTransmissionDefect K R F U DU t) r) =
      actualOriginOutgoingTrace K R U DU := by
  let p := U - originGreenValue K R (2*R) F R
  let q := DU - originGreenSlope K R (2*R) F R
  obtain ⟨hEI, hP⟩ := actual_Kummer_interface_defect_projection_exact K hR hK p q
  have hTrace := actual_origin_Green_outgoing_trace_coefficient K hK
    (show R ∈ Icc R (2*R) by constructor <;> linarith) F
  have hDiff : actualOriginOutgoingTrace K R p q =
      actualOriginTransmissionObstruction K R F U DU := by
    unfold actualOriginTransmissionObstruction
    rw [← hTrace]
    dsimp [actualOriginOutgoingTrace, p, q]
    ring
  have hProjection : (∫ r in R..(2*R), originGreenSourceA K
      (actualOriginTransmissionDefect K R F U DU) r) =
      actualOriginTransmissionObstruction K R F U DU := hP.trans hDiff
  have hFI := (actual_origin_Green_source_integrability K hK (by linarith) F hF).1
  refine ⟨hEI, hProjection, ?_⟩
  have hAdd : originGreenSourceA K
      (fun t => F t + actualOriginTransmissionDefect K R F U DU t) =
      (fun t => originGreenSourceA K F t +
        originGreenSourceA K (actualOriginTransmissionDefect K R F U DU) t) := by
    funext t
    unfold originGreenSourceA
    ring
  rw [hAdd, intervalIntegral.integral_add hFI hEI, hProjection]
  unfold actualOriginTransmissionObstruction originGreenCoeffA
  ring

end HBL.TypeIIDynamicSelection
