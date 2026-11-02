import HBL.TypeIIDynamicSelection.ActualOneLayerPhysicalClassicalInnerJets
import HBL.TypeIIDynamicSelection.ActualKummerTwoInterfaceObstruction
import HBL.TypeIIDynamicSelection.ActualHartreeDynamicPhaseCovariance
import Mathlib.Tactic

/-!
# Revised HBL 2.13: actual PDE-generated INNER Cauchy data in Kummer coordinates

For ONE genuine critically scaled, dynamically phased Hartree radiation,
the independently verified physical H+/H- classical Fredholm
reconstructions provide both inner C1 jets. Their correct Kummer
coordinate derivative contains the indispensable sqrt(q) factor.

Use that physical inner jet as the Cauchy datum for the genuine Kummer
inhomogeneous equation. The unique Wronskian-selected coefficients
then force two explicit OUTER transfer equations. This theorem proves
the inner PDE connection and the precise equivalence, NOT the outer
compatibility equations. In particular, the corrected Cauchy solution
is NOT claimed to retain the two original Green normalizations.
No Type-II rate, artificial source orders, new axiom, or sorry.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Profile.ActualInner
open HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.L2Kernel

/-- The same physical radiation used by the original Hartree residual. -/
def actualHartreePhasedScaledRadiation
    (z : ℝ → ℝ → ℂ) (ell time gamma : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun τ r =>
    actualHartreeUnitPhase (gamma τ) *
      rescalePhysicalRadiation (ell τ) (z (time τ)) r

/-- The genuine physical complex PDE source, evaluated at the correct
bubble radius sqrt(q)*r and continuously clamped outside the annulus. -/
def actualHartreePhysicalKummerClampedSource
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s k center d : ℝ) : ℝ → ℂ :=
  fun r =>
    actualOneLayerCommonPDEResidual V Z b omega s
      (k * min (max r (center - d)) (center + d))

/-- Complex combination of the actual classical physical H+ and H-
profiles after the necessary bubble-to-Kummer coordinate conversion. -/
def actualHartreeInnerKummerProfile
    (up um : ℝ → ℝ) (k : ℝ) : ℝ → ℂ :=
  fun r => (up (k * r) : ℂ) + Complex.I * (um (k * r) : ℂ)

/-- Kummer-coordinate slope of the same physical two-channel profile.
The factor k=sqrt(q) is an actual spatial chain rule, not a definition
of an independent abstract boundary jet. -/
def actualHartreeInnerKummerSlope
    (up um : ℝ → ℝ) (k r : ℝ) : ℂ :=
  ((k * deriv up (k * r) : ℝ) : ℂ) +
    Complex.I * ((k * deriv um (k * r) : ℝ) : ℂ)

/-- Both real Hartree channel derivatives give one complex Kummer
C1 jet, with precisely the physical sqrt(q) coordinate Jacobian. -/
theorem actual_Hartree_two_channel_inner_Kummer_chain_rule
    (up um : ℝ → ℝ) (k r : ℝ)
    (hup : DifferentiableAt ℝ up (k * r))
    (hum : DifferentiableAt ℝ um (k * r)) :
    HasDerivAt (actualHartreeInnerKummerProfile up um k)
      (actualHartreeInnerKummerSlope up um k r) r := by
  have hk : HasDerivAt (fun x : ℝ => k * x) k r :=
    hasDerivAt_const_mul k
  have hp : HasDerivAt (fun x : ℝ => (up (k * x) : ℂ))
      ((k * deriv up (k * r) : ℝ) : ℂ) r := by
    convert (hup.hasDerivAt.scomp r hk).ofReal_comp using 1 <;> ring
  have hm : HasDerivAt (fun x : ℝ => (um (k * x) : ℂ))
      ((k * deriv um (k * r) : ℝ) : ℂ) r := by
    convert (hum.hasDerivAt.scomp r hk).ofReal_comp using 1 <;> ring
  change HasDerivAt
    (fun x : ℝ => (up (k * x) : ℂ) + Complex.I * (um (k * x) : ℂ))
    (((k * deriv up (k * r) : ℝ) : ℂ) +
      Complex.I * ((k * deriv um (k * r) : ℝ) : ℂ)) r
  exact hp.add (hm.const_mul Complex.I)

/-- A true physical Hartree source produces the classical inner H+/H-
Cauchy data in Kummer coordinates. Their unique inhomogeneous
Kummer initial-value extension is constructed. For ANY proposed outer
physical C1 jet, simultaneous matching is EXACTLY equivalent to the
two outer transfer conditions; those conditions are NOT asserted.

The strict PDE-to-two-channel source certificate and the full weighted
complex source hypothesis are retained visibly. In particular, this
does not manufacture the remote profile, weighted gain, or global
normalized Kummer boundary matching. -/
theorem actual_Hartree_PDE_inner_Kummer_jet_and_outer_obstruction
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (ell time gamma b omega : ℝ → ℝ)
    (s q : ℝ) (hq : 0 < q)
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hInnerPositive : 0 < center - d)
    (hCont : Continuous (actualOneLayerCommonPDEResidual V
      (actualHartreePhasedScaledRadiation z ell time gamma)
      (b s) (omega s) s))
    (hWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V
          (actualHartreePhasedScaledRadiation z ell time gamma)
          (b s) (omega s) s r‖)
      2 halfLineMeasure) :
    let Z := actualHartreePhasedScaledRadiation z ell time gamma
    let k := Real.sqrt q
    let F := actualHartreePhysicalKummerClampedSource
      V Z (b s) (omega s) s k center d
    ∃ up um : ℝ → ℝ,
      InnerAffineProperties up
        (actualPlusCharge (actualOneLayerPlusPDE V Z (b s) (omega s) s)) ∧
      InnerAffineProperties um
        (actualMinusCharge (actualOneLayerMinusPDE V Z (b s) (omega s) s)) ∧
      (∀ r : ℝ, 0 < r →
        hPlusApply up r = actualOneLayerPlusPDE V Z (b s) (omega s) s r ∧
        hMinusApply um r = actualOneLayerMinusPDE V Z (b s) (omega s) s r) ∧
      HasDerivAt (actualHartreeInnerKummerProfile up um k)
        (actualHartreeInnerKummerSlope up um k (center - d)) (center - d) ∧
      (∃ a c : ℂ,
        actualKummerCauchyValue K d F a c (center - d) =
          actualHartreeInnerKummerProfile up um k (center - d) ∧
        actualKummerCauchyDeriv K d F a c (center - d) =
          actualHartreeInnerKummerSlope up um k (center - d)) ∧
      (∀ Uout DUout : ℂ,
        (∃ a c : ℂ,
          actualKummerCauchyValue K d F a c (center - d) =
            actualHartreeInnerKummerProfile up um k (center - d) ∧
          actualKummerCauchyDeriv K d F a c (center - d) =
            actualHartreeInnerKummerSlope up um k (center - d) ∧
          actualKummerCauchyValue K d F a c (center + d) = Uout ∧
          actualKummerCauchyDeriv K d F a c (center + d) = DUout) ↔
        actualKummerPhysicalRightTransfer K d F
          (actualHartreeInnerKummerProfile up um k (center - d))
          (actualHartreeInnerKummerSlope up um k (center - d)) =
          (Uout, DUout)) := by
  dsimp only
  let Z : ℝ → ℝ → ℂ :=
    actualHartreePhasedScaledRadiation z ell time gamma
  let k : ℝ := Real.sqrt q
  let F : ℝ → ℂ :=
    actualHartreePhysicalKummerClampedSource
      V Z (b s) (omega s) s k center d
  obtain ⟨up, um, hUp, hUm, hClassical⟩ :=
    actual_Hartree_one_PDE_source_has_classical_Hplus_Hminus_jets
      sigma hLower hUpper V Z (b s) (omega s) s hCont hWeighted
  have hkPos : 0 < k := Real.sqrt_pos.2 hq
  have hRadius : 0 < k * (center - d) :=
    mul_pos hkPos hInnerPositive
  obtain ⟨hUpDiff, _, hUmDiff, _, _, _⟩ :=
    hClassical (k * (center - d)) hRadius
  have hJet :
      HasDerivAt (actualHartreeInnerKummerProfile up um k)
        (actualHartreeInnerKummerSlope up um k (center - d))
          (center - d) :=
    actual_Hartree_two_channel_inner_Kummer_chain_rule
      up um k (center - d) hUpDiff hUmDiff
  have hFC : Continuous F := by
    have hClip : Continuous
        (fun r : ℝ => min (max r (center - d)) (center + d)) :=
      (continuous_id.max continuous_const).min continuous_const
    have hArg : Continuous
        (fun r : ℝ => k * min (max r (center - d)) (center + d)) :=
      continuous_const.mul hClip
    change Continuous
      ((actualOneLayerCommonPDEResidual V Z (b s) (omega s) s) ∘
        (fun r : ℝ =>
          k * min (max r (center - d)) (center + d)))
    exact hCont.comp hArg
  let U : ℂ := actualHartreeInnerKummerProfile up um k (center - d)
  let DU : ℂ := actualHartreeInnerKummerSlope up um k (center - d)
  obtain ⟨a, c, hValue, hSlope, _hEquation⟩ :=
    actual_Kummer_inner_interface_Cauchy_match
      K d hd hde F hFC U DU
  refine ⟨up, um, hUp, hUm, ?_, hJet, ⟨a, c, hValue, hSlope⟩, ?_⟩
  · intro r hr
    rcases hClassical r hr with ⟨_, _, _, _, hPlus, hMinus⟩
    exact ⟨hPlus, hMinus⟩
  · intro Uout DUout
    exact actual_Kummer_two_boundary_Cauchy_match_iff_transfer
      K d hd hde F U DU Uout DUout

end HBL.TypeIIDynamicSelection
