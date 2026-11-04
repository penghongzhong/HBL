import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledCancellation
import HBL.TypeIIDynamicSelection.ActualOriginGreenTransmission

/-!
Exact finite-interval continuation of the actual Fredholm jet in the SAME
origin-normalized Kummer gauge as the complete compatibility matrix.
Both homogeneous coefficients are fixed by the left jet and original source.
The singular coefficient is exactly the compatibility obstruction; it is
not an independently adjustable monopole.  The constructed real speed
increments cancel it, without introducing an interface repair forcing.

The upper condition is the origin-basis trace at a finite small radius B.
It does not identify the true outgoing branch at infinity.  No moving-time,
nonlinear shell, or uniform shrinking-interface inverse estimate is claimed.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Cramer's singular coefficient from the actual left mismatch. -/
def actualOriginMatchedSingularCoeff
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  ((U - originGreenValue K a b F a) * originPhysicalSlope K.x K.dx a -
    (DU - originGreenSlope K a b F a) * originPhysicalValue K.x a) /
    originGreenWronskian K a

/-- The regular coefficient is fixed by the same two-coordinate match. -/
def actualOriginMatchedRegularCoeff
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  (originPhysicalValue K.y a * (DU - originGreenSlope K a b F a) -
    originPhysicalSlope K.y K.dy a * (U - originGreenValue K a b F a)) /
    originGreenWronskian K a

def actualOriginMatchedKummerValue
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  originGreenValue K a b F r +
    actualOriginMatchedSingularCoeff K a b F U DU * originPhysicalValue K.y r +
    actualOriginMatchedRegularCoeff K a b F U DU * originPhysicalValue K.x r

def actualOriginMatchedKummerSlope
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (r : ℝ) : ℂ :=
  originGreenSlope K a b F r +
    actualOriginMatchedSingularCoeff K a b F U DU * originPhysicalSlope K.y K.dy r +
    actualOriginMatchedRegularCoeff K a b F U DU * originPhysicalSlope K.x K.dx r

/-- Both endpoint coordinates determine the two coefficients uniquely. -/
theorem actual_origin_matched_Kummer_left_jet_and_unique_coefficients
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (U DU : ℂ) :
    actualOriginMatchedKummerValue K a b F U DU a = U ∧
    actualOriginMatchedKummerSlope K a b F U DU a = DU ∧
    ∀ alpha beta : ℂ,
      originGreenValue K a b F a + alpha * originPhysicalValue K.y a +
        beta * originPhysicalValue K.x a = U →
      originGreenSlope K a b F a + alpha * originPhysicalSlope K.y K.dy a +
        beta * originPhysicalSlope K.x K.dx a = DU →
      alpha = actualOriginMatchedSingularCoeff K a b F U DU ∧
      beta = actualOriginMatchedRegularCoeff K a b F U DU := by
  have hW := originGreenWronskian_ne K hK (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
  refine ⟨?_, ?_, ?_⟩
  · unfold actualOriginMatchedKummerValue actualOriginMatchedSingularCoeff
      actualOriginMatchedRegularCoeff
    generalize hWr : originGreenWronskian K a = w at hW ⊢
    field_simp [hW]
    rw [← hWr]
    unfold originGreenWronskian
    ring
  · unfold actualOriginMatchedKummerSlope actualOriginMatchedSingularCoeff
      actualOriginMatchedRegularCoeff
    generalize hWr : originGreenWronskian K a = w at hW ⊢
    field_simp [hW]
    rw [← hWr]
    unfold originGreenWronskian
    ring
  · intro alpha beta hv hd
    constructor
    · unfold actualOriginMatchedSingularCoeff originGreenWronskian
      apply (eq_div_iff hW).2
      unfold originGreenWronskian
      linear_combination originPhysicalSlope K.x K.dx a * hv -
        originPhysicalValue K.x a * hd
    · unfold actualOriginMatchedRegularCoeff originGreenWronskian
      apply (eq_div_iff hW).2
      unfold originGreenWronskian
      linear_combination originPhysicalValue K.y a * hd -
        originPhysicalSlope K.y K.dy a * hv

/-- The constructed singular coefficient is the previously defined complete
interval obstruction, with the original source integral retained. -/
theorem actual_origin_matched_Kummer_singular_eq_obstruction
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (U DU : ℂ) :
    actualOriginMatchedSingularCoeff K a b F U DU =
      actualMomentLockedIntervalObstruction K a b F U DU := by
  have hG := actual_origin_Green_outgoing_trace_coefficient K hK
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) F
  calc
    _ = actualOriginOutgoingTrace K a U DU -
        actualOriginOutgoingTrace K a (originGreenValue K a b F a)
          (originGreenSlope K a b F a) := by
      unfold actualOriginMatchedSingularCoeff actualOriginOutgoingTrace
      ring
    _ = _ := by rw [hG]; rfl

/-- The original Green normalization removes its contribution to the
regular coefficient. This coefficient is fixed entirely by the left jet. -/
theorem actual_origin_matched_Kummer_regular_coefficient
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU : ℂ) :
    actualOriginMatchedRegularCoeff K a b F U DU =
      (originPhysicalValue K.y a * DU - originPhysicalSlope K.y K.dy a * U) /
        originGreenWronskian K a := by
  have hG := (originGreen_endpoint_normalization K a b F).2.2.2
  unfold actualOriginMatchedRegularCoeff
  apply congrArg (fun z : ℂ => z / originGreenWronskian K a)
  linear_combination -hG

/-- The finite upper origin trace equals the actual left/source obstruction.
This trace condition alone is not a radiation condition at infinity. -/
theorem actual_origin_matched_Kummer_upper_trace
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (U DU : ℂ) :
    actualOriginOutgoingTrace K b
      (actualOriginMatchedKummerValue K a b F U DU b)
      (actualOriginMatchedKummerSlope K a b F U DU b) =
      actualMomentLockedIntervalObstruction K a b F U DU := by
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hW := originGreenWronskian_ne K hK hb
  have hG := actual_origin_Green_outgoing_trace_coefficient K hK hb F
  have hA : originGreenCoeffA K b F b = 0 := by simp [originGreenCoeffA]
  calc
    _ = actualOriginOutgoingTrace K b (originGreenValue K a b F b)
          (originGreenSlope K a b F b) +
        actualOriginMatchedSingularCoeff K a b F U DU := by
      unfold actualOriginOutgoingTrace actualOriginMatchedKummerValue
        actualOriginMatchedKummerSlope
      generalize hWr : originGreenWronskian K b = w at hW ⊢
      field_simp [hW]
      rw [← hWr]
      unfold originGreenWronskian
      ring
    _ = actualOriginMatchedSingularCoeff K a b F U DU := by rw [hG, hA, zero_add]
    _ = _ := actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F U DU

/-- After genuine compatibility cancellation, the complete upper jet is
the regular origin jet times its FORCED coefficient. The full source integral
still contributes to that coefficient. -/
theorem actual_origin_matched_Kummer_upper_regular_jet
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0) :
    actualOriginMatchedKummerValue K a b F U DU b =
      originPhysicalValue K.x b *
        (actualOriginMatchedRegularCoeff K a b F U DU + originGreenCoeffB K a F b) ∧
    actualOriginMatchedKummerSlope K a b F U DU b =
      originPhysicalSlope K.x K.dx b *
        (actualOriginMatchedRegularCoeff K a b F U DU + originGreenCoeffB K a F b) := by
  have hs := (actual_origin_matched_Kummer_singular_eq_obstruction K hK hab F U DU).trans hzero
  have hA : originGreenCoeffA K b F b = 0 := by simp [originGreenCoeffA]
  constructor
  · unfold actualOriginMatchedKummerValue originGreenValue
    rw [hs, hA]
    ring
  · unfold actualOriginMatchedKummerSlope originGreenSlope
    rw [hs, hA]
    ring

/-- Explicit solution, continuous value/slope traces and the ORIGINAL forced
Kummer system. The only terminal boundary condition is the finite origin trace. -/
def ActualOriginMatchedKummerCertificate
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : Prop :=
  actualOriginMatchedKummerValue K a b F U DU a = U ∧
  actualOriginMatchedKummerSlope K a b F U DU a = DU ∧
  actualOriginOutgoingTrace K b
    (actualOriginMatchedKummerValue K a b F U DU b)
    (actualOriginMatchedKummerSlope K a b F U DU b) = 0 ∧
  ContinuousOn (actualOriginMatchedKummerValue K a b F U DU) (Icc a b) ∧
  ContinuousOn (actualOriginMatchedKummerSlope K a b F U DU) (Icc a b) ∧
  (∀ᵐ r ∂volume, r ∈ Icc a b →
    HasDerivAt (actualOriginMatchedKummerValue K a b F U DU)
      (actualOriginMatchedKummerSlope K a b F U DU r) r ∧
    HasDerivAt (actualOriginMatchedKummerSlope K a b F U DU)
      (F r - frozenFirstCoeff r * actualOriginMatchedKummerSlope K a b F U DU r -
        frozenZeroCoeff mu theta * actualOriginMatchedKummerValue K a b F U DU r) r)

/-- The complete finite-interval certificate is equivalent to its genuine
compatibility equation; no extra source or independently prescribed jet enters. -/
theorem actual_origin_matched_Kummer_certificate_iff
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume a b) (U DU : ℂ) :
    ActualOriginMatchedKummerCertificate K a b F U DU ↔
      actualMomentLockedIntervalObstruction K a b F U DU = 0 := by
  have ht := actual_origin_matched_Kummer_upper_trace K hK hab F U DU
  constructor
  · intro h
    exact ht.symm.trans h.2.2.1
  · intro hzero
    have hLeft := actual_origin_matched_Kummer_left_jet_and_unique_coefficients
      K hK hab F U DU
    have hCont := actual_origin_Green_integrable_continuous_pair K hK hab F hF
    have hp : ContinuousOn (originPhysicalValue K.y) (Icc a b) :=
      fun r hr => (hK r hr).1.continuousAt.continuousWithinAt
    have hdp : ContinuousOn (originPhysicalSlope K.y K.dy) (Icc a b) :=
      fun r hr => (hK r hr).2.1.continuousAt.continuousWithinAt
    have hq : ContinuousOn (originPhysicalValue K.x) (Icc a b) :=
      fun r hr => (hK r hr).2.2.1.continuousAt.continuousWithinAt
    have hdq : ContinuousOn (originPhysicalSlope K.x K.dx) (Icc a b) :=
      fun r hr => (hK r hr).2.2.2.1.continuousAt.continuousWithinAt
    refine ⟨hLeft.1, hLeft.2.1, ht.trans hzero,
      (hCont.1.add (hp.const_mul _)).add (hq.const_mul _),
      (hCont.2.add (hdp.const_mul _)).add (hdq.const_mul _), ?_⟩
    filter_upwards [actual_origin_Green_integrable_forcing_ae_equation
      K hK hab F hF] with r hr
    intro hmem
    obtain ⟨hU, hV, hEq⟩ := hr hmem
    rcases hK r hmem with ⟨hphi, hdphi, hpsi, hdpsi, _, _, _, _, _, _, _⟩
    refine ⟨(hU.add (hphi.const_mul _)).add (hpsi.const_mul _), ?_⟩
    convert (hV.add (hdphi.const_mul (actualOriginMatchedSingularCoeff K a b F U DU))).add
      (hdpsi.const_mul (actualOriginMatchedRegularCoeff K a b F U DU)) using 1
    · rfl
    · dsimp only [actualOriginMatchedKummerValue, actualOriginMatchedKummerSlope]
      linear_combination -hEq

/-- Continuous forcing upgrades the same explicit solution to the classical
forced equation at every interior point. Endpoint traces remain the actual
continuous value/slope pair in the certificate above. -/
theorem actual_origin_matched_Kummer_classical_equation
    {mu theta scale a b C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K a b C) (hab : a < b)
    (F : ℝ → ℂ) (hF : Continuous F) (U DU : ℂ) :
    ∀ r ∈ Ioo a b,
      HasDerivAt (actualOriginMatchedKummerValue K a b F U DU)
        (actualOriginMatchedKummerSlope K a b F U DU r) r ∧
      HasDerivAt (actualOriginMatchedKummerSlope K a b F U DU)
        (F r - frozenFirstCoeff r * actualOriginMatchedKummerSlope K a b F U DU r -
          frozenZeroCoeff mu theta * actualOriginMatchedKummerValue K a b F U DU r) r := by
  intro r hr
  have hU := originGreenValue_hasDerivAt K hK hab F hF hr
  have hV := originGreenSlope_hasDerivAt K hK hab F hF hr
  have hEq := originGreen_equation K a b F r
  rcases hK r ⟨hr.1.le, hr.2.le⟩ with ⟨hphi, hdphi, hpsi, hdpsi, _, _, _, _, _, _, _⟩
  refine ⟨(hU.add (hphi.const_mul _)).add (hpsi.const_mul _), ?_⟩
  convert (hV.add (hdphi.const_mul (actualOriginMatchedSingularCoeff K a b F U DU))).add
    (hdpsi.const_mul (actualOriginMatchedRegularCoeff K a b F U DU)) using 1
  · rfl
  · dsimp only [actualOriginMatchedKummerValue, actualOriginMatchedKummerSlope]
    linear_combination -hEq

/-- The exact adjusted Fredholm reconstruction and the entire adjusted outer
source are inserted together. Both use the same two real increments. -/
def ActualMomentLockedMatchedKummerCertificate
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L c : ℝ) (hL : 0 < L) (a r0 r1 : ℝ)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (F : ℝ → ℂ) (db dw : ℝ) : Prop :=
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
  let J := actualMomentLockedCanonicalInnerJet
    (fun t => Fp t + dw * Gp t) (fun t => Fm t + db * Gm t)
    (innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp dw)
    (innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm db) a r0
  ActualOriginMatchedKummerCertificate K r0 r1
    (fun r => F r - (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r) J.1 J.2

/-- Matching the actual adjusted jet is exactly the complete coupled
compatibility condition, including the response of the inner solver. -/
theorem actual_Hartree_moment_locked_matched_Kummer_iff_compatibility
    {mu theta scale r0 r1 C : ℝ} (K : OriginKummerPair mu theta scale)
    (hr0 : 0 < r0) (horder : r0 ≤ r1) (hK : OriginBasisOn K r0 r1 C)
    (L c : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 < a)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume r0 r1) (db dw : ℝ) :
    ActualMomentLockedMatchedKummerCertificate K L c hL a r0 r1 Fp Fm hp hm F db dw ↔
      actualMomentLockedCoupledCompatibility K L c hL a r0 r1 Fp Fm hp hm F db dw = 0 := by
  have hI := actual_Hartree_moment_locked_scaled_speed_integrable_on a c r0 r1 ha hr0 horder
  unfold ActualMomentLockedMatchedKummerCertificate actualMomentLockedCoupledCompatibility
  dsimp only
  exact actual_origin_matched_Kummer_certificate_iff K hK horder _
    ((hF.sub (hI.1.const_mul (db : ℂ))).sub (hI.2.const_mul (dw : ℂ))) _ _

/-- Construct the origin basis, the full nondegenerate physical region and
the unique real speed correction. Its explicit Kummer continuation matches
the ACTUAL adjusted Fredholm jet and solves the unchanged adjusted source
equation on the WHOLE interval [L/a,B]. No compatibility, determinant, basis,
or trace is assumed. The boundary condition is only the finite origin trace. -/
theorem actual_Hartree_moment_locked_constructed_matched_Kummer
    (mu theta : ℝ) :
    ∃ (K : OriginKummerPair mu theta 1) (B L0 epsilon : ℝ),
      0 < B ∧ B < 1 ∧ 3 ≤ L0 ∧ 0 < epsilon ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → |c| ≤ 1 → a * |c| ≤ epsilon →
        0 < L / a ∧ L / a < B ∧
        ∀ (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
          (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (F : ℝ → ℂ),
          IntervalIntegrable F volume (L / a) B →
          ∃! p : ℝ × ℝ,
            ActualMomentLockedMatchedKummerCertificate K L c hLp a (L / a) B
              Fp Fm hp hm F p.1 p.2 := by
  obtain ⟨K, B, Lold, epsilon, hB, hBOne, hLold, hepsilon, hCancel⟩ :=
    actual_Hartree_moment_locked_constructed_unique_cancellation mu theta
  let D : ℝ := 1 / 2 + ‖originZeroCoeff mu theta‖
  let G : ℝ := Real.exp ((D + 1) * 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hcoeff : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D := by
    intro r hr
    have hFirst : ‖originFirstCoeff r‖ = r / 2 := by
      simp [originFirstCoeff, abs_of_nonneg hr.1]
    rw [hFirst]
    dsimp [D]
    linarith [hr.2]
  have hbound : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G :=
    origin_kummer_pair_bound K D hD hcoeff
  refine ⟨K, B, max Lold (1 / B), epsilon, hB, hBOne,
    hLold.trans (le_max_left _ _), hepsilon, ?_⟩
  intro L c a hLp hLarge ha3 hc hSmall
  have hOld : Lold ≤ L := (le_max_left _ _).trans hLarge
  have hInv : 1 / B ≤ L := (le_max_right _ _).trans hLarge
  have hLthree : 3 ≤ L := hLold.trans hOld
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < L / a := div_pos hLp ha
  have hBL : 1 ≤ B * L := by
    simpa only [mul_comm] using (div_le_iff₀ hB).mp hInv
  have hCubic : L ^ 2 ≤ B * L ^ 3 := by
    calc
      _ = 1 * L ^ 2 := by ring
      _ ≤ (B * L) * L ^ 2 := mul_le_mul_of_nonneg_right hBL (sq_nonneg L)
      _ = _ := by ring
  have horder : L / a < B := by
    apply (div_lt_iff₀ ha).2
    calc
      L < L ^ 2 := by nlinarith
      _ ≤ B * L ^ 3 := hCubic
      _ ≤ B * a := mul_le_mul_of_nonneg_left ha3 hB.le
  have hK := origin_kummer_annulus_bound K (L / a) B G hr0 hBOne hG hbound
  refine ⟨hr0, horder, ?_⟩
  intro Fp Fm hp hm F hF
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let Z := actualMomentLockedIntervalObstruction K (L / a) B F J.1 J.2
  obtain ⟨p, hpCancel, hpUnique⟩ := hCancel L c a hLp hOld ha3 hc hSmall Z
  have hAff (db dw : ℝ) := actual_Hartree_moment_locked_full_coupled_response
    K hr0 horder.le hK L c hLp a ha Fp Fm hp hm F hF db dw
  have hIff (db dw : ℝ) := actual_Hartree_moment_locked_matched_Kummer_iff_compatibility
    K hr0 horder.le hK L c hLp a ha Fp Fm hp hm F hF db dw
  refine ⟨p, (hIff p.1 p.2).2 ?_, ?_⟩
  · exact (hAff p.1 p.2).trans hpCancel
  · intro q hq
    apply hpUnique q
    exact (hAff q.1 q.2).symm.trans ((hIff q.1 q.2).1 hq)

end HBL.TypeIIDynamicSelection
