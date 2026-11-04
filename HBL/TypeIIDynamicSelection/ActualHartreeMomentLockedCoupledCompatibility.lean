import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedInnerResponse
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedProjection
import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalTransmission
import HBL.InnerEstimates.OutputLinearity

/-!
The two physical speed directions change BOTH the Kummer source and the
canonical inner solution.  This file assembles their complete columns using
the same fixed Fredholm normalization and proves the exact affine response.
The incoming traces are derivatives of the actual reconstructed q/r profiles.

The left endpoint is the actual inner radius divided by the spatial scale.
The configuration, inner cutoff, interface, and Kummer basis are frozen in
each affine law; their movement along a physical trajectory is not treated.
No determinant nondegeneracy, moving-configuration Jacobian, uncovered-region
estimate, relative residual gain, or manuscript environment is claimed.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

def actualMomentLockedPhysicalPlus (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) (r : ℝ) : ℝ :=
  normalizedPlusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r / r

def actualMomentLockedPhysicalMinus (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) (r : ℝ) : ℝ :=
  normalizedMinusOutput (7 / 4 : ℝ) (by norm_num) (by norm_num) F hF r / r

private theorem physical_plus_differentiable (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) (r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (actualMomentLockedPhysicalPlus F hF) r :=
  ((normalizedPlusOutput_C1 F hF).1 r).div differentiableAt_id hr.ne'

private theorem physical_minus_differentiable (F : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F) (r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (actualMomentLockedPhysicalMinus F hF) r :=
  ((normalizedMinusOutput_C1 F hF).1 r).div differentiableAt_id hr.ne'

private theorem physical_plus_add_smul (F G : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (hG : InWeightedL2 (7 / 4 : ℝ) G) (d : ℝ)
    (hH : InWeightedL2 (7 / 4 : ℝ) (fun r => F r + d * G r)) :
    actualMomentLockedPhysicalPlus (fun r => F r + d * G r) hH =
      fun r => actualMomentLockedPhysicalPlus F hF r +
        d * actualMomentLockedPhysicalPlus G hG r := by
  funext r
  unfold actualMomentLockedPhysicalPlus
  rw [normalizedPlusOutput_add_smul (7 / 4 : ℝ) (by norm_num) (by norm_num)
    F G hF hG d hH]
  ring

private theorem physical_minus_add_smul (F G : ℝ → ℝ)
    (hF : InWeightedL2 (7 / 4 : ℝ) F)
    (hG : InWeightedL2 (7 / 4 : ℝ) G) (d : ℝ)
    (hH : InWeightedL2 (7 / 4 : ℝ) (fun r => F r + d * G r)) :
    actualMomentLockedPhysicalMinus (fun r => F r + d * G r) hH =
      fun r => actualMomentLockedPhysicalMinus F hF r +
        d * actualMomentLockedPhysicalMinus G hG r := by
  funext r
  unfold actualMomentLockedPhysicalMinus
  rw [normalizedMinusOutput_add_smul (7 / 4 : ℝ) (by norm_num) (by norm_num)
    F G hF hG d hH]
  ring

/-- The jet of the fixed, normalized two-channel Fredholm reconstruction. -/
def actualMomentLockedCanonicalInnerJet (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (a r : ℝ) : ℂ × ℂ :=
  let up := actualMomentLockedPhysicalPlus Fp hp
  let um := actualMomentLockedPhysicalMinus Fm hm
  ((up (a * r) : ℂ) + Complex.I * (um (a * r) : ℂ),
    (a : ℂ) * ((deriv up (a * r) : ℂ) + Complex.I * (deriv um (a * r) : ℂ)))

def actualMomentLockedScaleResponseJet (L c : ℝ) (hL : 0 < L)
    (a r : ℝ) : ℂ × ℂ :=
  let u := actualMomentLockedPhysicalMinus (actualMomentLockedInnerScaleSource L c)
    (actual_Hartree_moment_locked_inner_scale_source_weighted L c hL)
  (Complex.I * (u (a * r) : ℂ),
    (a : ℂ) * Complex.I * (deriv u (a * r) : ℂ))

def actualMomentLockedPhaseResponseJet (L c : ℝ) (hL : 0 < L)
    (a r : ℝ) : ℂ × ℂ :=
  let u := actualMomentLockedPhysicalPlus (actualMomentLockedInnerPhaseSource L c)
    (actual_Hartree_moment_locked_inner_phase_source_weighted L c hL)
  ((u (a * r) : ℂ), (a : ℂ) * (deriv u (a * r) : ℂ))

/-- Actual Fredholm superposition, including the derivative of q/r. -/
theorem actual_Hartree_moment_locked_inner_jet_affine
    (L c : ℝ) (hL : 0 < L) (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (db dw : ℝ) :
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
    let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r
    let Jb := actualMomentLockedScaleResponseJet L c hL a r
    let Jw := actualMomentLockedPhaseResponseJet L c hL a r
    actualMomentLockedCanonicalInnerJet
      (fun t => Fp t + dw * Gp t) (fun t => Fm t + db * Gm t)
      (innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp dw)
      (innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm db) a r =
      (J.1 + (db : ℂ) * Jb.1 + (dw : ℂ) * Jw.1,
       J.2 + (db : ℂ) * Jb.2 + (dw : ℂ) * Jw.2) := by
  dsimp only
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  have hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
  have hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
  have hpH := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp dw
  have hmH := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm db
  have hPeq := physical_plus_add_smul Fp Gp hp hgp dw hpH
  have hMeq := physical_minus_add_smul Fm Gm hm hgm db hmH
  have hPder : deriv (actualMomentLockedPhysicalPlus
      (fun t => Fp t + dw * Gp t) hpH) (a * r) =
      deriv (actualMomentLockedPhysicalPlus Fp hp) (a * r) +
        dw * deriv (actualMomentLockedPhysicalPlus Gp hgp) (a * r) := by
    rw [hPeq]
    exact ((physical_plus_differentiable Fp hp (a * r) (mul_pos ha hr)).hasDerivAt.add
      ((physical_plus_differentiable Gp hgp (a * r) (mul_pos ha hr)).hasDerivAt.const_mul dw)).deriv
  have hMder : deriv (actualMomentLockedPhysicalMinus
      (fun t => Fm t + db * Gm t) hmH) (a * r) =
      deriv (actualMomentLockedPhysicalMinus Fm hm) (a * r) +
        db * deriv (actualMomentLockedPhysicalMinus Gm hgm) (a * r) := by
    rw [hMeq]
    exact ((physical_minus_differentiable Fm hm (a * r) (mul_pos ha hr)).hasDerivAt.add
      ((physical_minus_differentiable Gm hgm (a * r) (mul_pos ha hr)).hasDerivAt.const_mul db)).deriv
  apply Prod.ext
  · change ((actualMomentLockedPhysicalPlus (fun t => Fp t + dw * Gp t) hpH (a * r) : ℂ) +
        Complex.I * (actualMomentLockedPhysicalMinus (fun t => Fm t + db * Gm t) hmH (a * r) : ℂ)) = _
    rw [congrFun hPeq (a * r), congrFun hMeq (a * r)]
    dsimp [actualMomentLockedCanonicalInnerJet, actualMomentLockedScaleResponseJet,
      actualMomentLockedPhaseResponseJet, Gp, Gm]
    push_cast
    ring
  · change (a : ℂ) * ((deriv (actualMomentLockedPhysicalPlus
        (fun t => Fp t + dw * Gp t) hpH) (a * r) : ℂ) +
        Complex.I * (deriv (actualMomentLockedPhysicalMinus
          (fun t => Fm t + db * Gm t) hmH) (a * r) : ℂ)) = _
    rw [hPder, hMder]
    dsimp [actualMomentLockedCanonicalInnerJet, actualMomentLockedScaleResponseJet,
      actualMomentLockedPhaseResponseJet, Gp, Gm]
    push_cast
    ring

/-- The outgoing obstruction on the actual interval, including a moving
left endpoint. The source on the whole interval is retained. -/
def actualMomentLockedIntervalObstruction
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 r1 : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  actualOriginOutgoingTrace K r0 U DU - originGreenCoeffA K r1 F r0

/-- Complete cancellation columns. H±=-Delta-potential, whereas the
Kummer operator has +Delta. An additive correction solving Hq=rP
therefore uses -a^2 P on the Kummer side: the two contributions ADD. -/
def actualMomentLockedCoupledColumns
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L c : ℝ) (hL : 0 < L) (a r0 r1 : ℝ) : ℂ × ℂ :=
  let Jb := actualMomentLockedScaleResponseJet L c hL a r0
  let Jw := actualMomentLockedPhaseResponseJet L c hL a r0
  (actualOriginOutgoingTrace K r0 Jb.1 Jb.2 +
     originGreenCoeffA K r1 (actualMomentLockedScaledScaleSource a c) r0,
   actualOriginOutgoingTrace K r0 Jw.1 Jw.2 +
     originGreenCoeffA K r1 (actualMomentLockedScaledPhaseSource a c) r0)

def actualMomentLockedCoupledDeterminant
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L c : ℝ) (hL : 0 < L) (a r0 r1 : ℝ) : ℝ :=
  let C := actualMomentLockedCoupledColumns K L c hL a r0 r1
  C.1.re * C.2.im - C.2.re * C.1.im

/-- F is the outer correction RHS, hence the negative of the residual
forcing in the physical specialization below. -/
def actualMomentLockedCoupledCompatibility
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L c : ℝ) (hL : 0 < L) (a r0 r1 : ℝ)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (F : ℝ → ℂ) (db dw : ℝ) : ℂ :=
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hL
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hL
  let J := actualMomentLockedCanonicalInnerJet
    (fun t => Fp t + dw * Gp t) (fun t => Fm t + db * Gm t)
    (innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp dw)
    (innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm db) a r0
  actualMomentLockedIntervalObstruction K r0 r1
    (fun r => F r - (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
      (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r) J.1 J.2

/-- The actual coupled affine law for a specified correction RHS. The
inner normalization, outer sign and entire interval are explicit. -/
theorem actual_Hartree_moment_locked_full_coupled_response
    {mu theta scale r0 r1 C : ℝ} (K : OriginKummerPair mu theta scale)
    (hr0 : 0 < r0) (horder : r0 ≤ r1) (hK : OriginBasisOn K r0 r1 C)
    (L c : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 < a)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume r0 r1) (db dw : ℝ) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
    let cols := actualMomentLockedCoupledColumns K L c hL a r0 r1
    actualMomentLockedCoupledCompatibility K L c hL a r0 r1 Fp Fm hp hm F db dw =
      actualMomentLockedIntervalObstruction K r0 r1 F J.1 J.2 +
        (db : ℂ) * cols.1 + (dw : ℂ) * cols.2 := by
  have hJet := actual_Hartree_moment_locked_inner_jet_affine
    L c hL a r0 ha hr0 Fp Fm hp hm db dw
  have hI := actual_Hartree_moment_locked_scaled_speed_integrable_on a c r0 r1 ha hr0 horder
  have hFirst := actual_moment_locked_source_coefficient_add_mul_on K hK horder F
    (actualMomentLockedScaledScaleSource a c) hF hI.1 (-(db : ℂ))
  have hSecond := actual_moment_locked_source_coefficient_add_mul_on K hK horder
    (fun r => F r + (-(db : ℂ)) * actualMomentLockedScaledScaleSource a c r)
    (actualMomentLockedScaledPhaseSource a c)
    (hF.add (hI.1.const_mul (-(db : ℂ)))) hI.2 (-(dw : ℂ))
  have hSource : originGreenCoeffA K r1
      (fun r => F r - (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r) r0 =
      originGreenCoeffA K r1 F r0 -
        (db : ℂ) * originGreenCoeffA K r1 (actualMomentLockedScaledScaleSource a c) r0 -
        (dw : ℂ) * originGreenCoeffA K r1 (actualMomentLockedScaledPhaseSource a c) r0 := by
    simp only [neg_mul, ← sub_eq_add_neg] at hFirst hSecond
    rw [hSecond, hFirst]
  dsimp only at hJet ⊢
  unfold actualMomentLockedCoupledCompatibility
  dsimp only
  rw [hJet]
  unfold actualMomentLockedIntervalObstruction
  rw [hSource]
  dsimp [actualMomentLockedCoupledColumns, actualOriginOutgoingTrace]
  ring

/-- The actual interface is L/a and the original forcing is retained from
L/a all the way to r1. Thus no interval between the inner cutoff and a
separate fixed annulus is silently omitted. Membership and integrability
come from the same actual nonlocal Hartree interaction. This is a frozen
linear correction law, not a nonlinear residual or uniform inverse estimate. -/
theorem actual_Hartree_physical_moment_locked_coupled_response
    (B A ell c a r1 : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (ha : 0 < a) (horder : actualHartreeSlowInnerRadius ell / a ≤ r1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A)
    {mu theta scale C : ℝ} (K : OriginKummerPair mu theta scale)
    (hK : OriginBasisOn K (actualHartreeSlowInnerRadius ell / a) r1 C) :
    ∃ (hp : InWeightedL2 (7 / 4 : ℝ) (actualHartreeTransmissionPlusSource ell c z))
      (hm : InWeightedL2 (7 / 4 : ℝ) (actualHartreeTransmissionMinusSource ell c z)),
    let L := actualHartreeSlowInnerRadius ell
    let hL : 0 < L := Real.rpow_pos_of_pos hell _
    let r0 := L / a
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let F := fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
    let cols := actualMomentLockedCoupledColumns K L c hL a r0 r1
    a * r0 = L ∧ ∀ db dw : ℝ,
      actualMomentLockedCoupledCompatibility K L c hL a r0 r1 Fp Fm hp hm F db dw =
        actualMomentLockedIntervalObstruction K r0 r1 F J.1 J.2 +
          (db : ℂ) * cols.1 + (dw : ℂ) * cols.2 := by
  have hL : 0 < actualHartreeSlowInnerRadius ell := Real.rpow_pos_of_pos hell _
  have hr0 : 0 < actualHartreeSlowInnerRadius ell / a := div_pos hL ha
  have hSource := actual_Hartree_conjugated_slow_inner_one_sixteenth
    ell c B A hell hellOne hc hB hA z hz hSup hStrauss
  have hPair := actual_Hartree_one_complex_weighted_source_two_channels
    (7 / 4 : ℝ) _ hSource.1 hSource.2.1
  have hF := actual_Hartree_scaled_Kummer_source_intervalIntegrable B A ell c a
    (actualHartreeSlowInnerRadius ell / a) r1 hB hA hell hellOne hc ha hr0 horder
    z hz hSup hStrauss
  refine ⟨hPair.1, hPair.2, ?_⟩
  dsimp only
  constructor
  · field_simp [ha.ne']
  · intro db dw
    exact actual_Hartree_moment_locked_full_coupled_response K hr0 horder hK
      (actualHartreeSlowInnerRadius ell) c hL a ha _ _ hPair.1 hPair.2 _ hF.neg db dw

end HBL.TypeIIDynamicSelection
