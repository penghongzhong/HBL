import HBL.TypeIIDynamicSelection.ActualKummerInnerCauchyMatch
import Mathlib.Tactic

/-!
# HBL 2.12: the EXACT obstruction to matching both Kummer interfaces

A second-order complex inhomogeneous Kummer ODE has exactly two
homogeneous complex constants. The physical Wronskian is nonzero, so
matching the INNER value and first derivative determines those constants
UNIQUELY. The OUTER value and first derivative are therefore NOT
arbitrarily adjustable: they must satisfy two exact, explicit transfer
compatibility equations.

This file proves that algebraic necessity and sufficiency, for the
ACTUAL Kummer fundamental pair (not an abstract regional solver),
with the genuine inhomogeneous Kummer Green source F. The source can
be specialized to the one real/imag Hartree PDE residual already used
by the inner H+ and H- classical affine corrections.

This prevents the invalid shortcut of declaring both inner and remote
C1 matching from local Kummer invertibility alone. Closing the
physically generated outer compatibility conditions is a genuine
remaining analytical obligation in original 2.12. No Type II rate
or unrelated source is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The two physical Kummer homogeneous coefficients are
uniquely fixed by BOTH boundary Cauchy data, as a direct consequence
of the original nonvanishing physical Wronskian. -/
theorem actual_Kummer_Wronskian_Cauchy_coefficients_unique
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (t : ℝ) (ht : t ∈ Icc (-eps) eps)
    (p q a c : ℂ)
    (hVal : a * K.phi t + c * K.psi t = p)
    (hDeriv : a * K.dphi t + c * K.dpsi t = q) :
    a = actualKummerMatchPhi K t p q ∧
    c = actualKummerMatchPsi K t p q := by
  have hW : localAnnulusWronskian K t ≠ 0 :=
    K.wronskian_ne t ht
  constructor
  · unfold actualKummerMatchPhi
    apply (eq_div_iff hW).2
    calc
      a * localAnnulusWronskian K t =
          (a * K.phi t + c * K.psi t) * K.dpsi t -
            (a * K.dphi t + c * K.dpsi t) * K.psi t := by
        unfold localAnnulusWronskian
        ring
      _ = p * K.dpsi t - q * K.psi t := by
        rw [hVal, hDeriv]
  · unfold actualKummerMatchPsi
    apply (eq_div_iff hW).2
    calc
      c * localAnnulusWronskian K t =
          K.phi t * (a * K.dphi t + c * K.dpsi t) -
            K.dphi t * (a * K.phi t + c * K.psi t) := by
        unfold localAnnulusWronskian
        ring
      _ = K.phi t * q - K.dphi t * p := by
        rw [hDeriv, hVal]

/-- The uniquely selected homogeneous coefficients for actual
NONHOMOGENEOUS Kummer Green solution with prescribed inner
value U and slope DU at the true left endpoint. -/
def actualKummerLeftMatchPhi
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  actualKummerMatchPhi K (-d)
    (U - physicalLocalKummerValue K d F (z-d))
    (DU - physicalLocalKummerDeriv K d F (z-d))

def actualKummerLeftMatchPsi
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ :=
  actualKummerMatchPsi K (-d)
    (U - physicalLocalKummerValue K d F (z-d))
    (DU - physicalLocalKummerDeriv K d F (z-d))

/-- The RIGHT value and slope obtained from the only possible
inhomogeneous Kummer solution that matches both INNER Cauchy traces.
Their compatibility with the actual remote trace is to be PROVED
from the physical PDE, not freely postulated. -/
def actualKummerPhysicalRightTransfer
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (U DU : ℂ) : ℂ × ℂ :=
  (actualKummerCauchyValue K d F
      (actualKummerLeftMatchPhi K d F U DU)
      (actualKummerLeftMatchPsi K d F U DU) (z+d),
   actualKummerCauchyDeriv K d F
      (actualKummerLeftMatchPhi K d F U DU)
      (actualKummerLeftMatchPsi K d F U DU) (z+d))

/-- NECESSARY AND SUFFICIENT condition for simultaneous C1 matching
of the inner and remote interfaces by one original Kummer solution.
The two outer equations are a genuine obstruction, not automatic
consequences of a right inverse or a source-level matching identity. -/
theorem actual_Kummer_two_boundary_Cauchy_match_iff_transfer
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (U DU Uout DUout : ℂ) :
    (∃ a c : ℂ,
      actualKummerCauchyValue K d F a c (z-d) = U ∧
      actualKummerCauchyDeriv K d F a c (z-d) = DU ∧
      actualKummerCauchyValue K d F a c (z+d) = Uout ∧
      actualKummerCauchyDeriv K d F a c (z+d) = DUout) ↔
    actualKummerPhysicalRightTransfer K d F U DU =
      (Uout, DUout) := by
  let p : ℂ := U - physicalLocalKummerValue K d F (z-d)
  let q : ℂ := DU - physicalLocalKummerDeriv K d F (z-d)
  have ht : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hshift : z - d - z = -d := by ring
  constructor
  · rintro ⟨a, c, hLeftValue, hLeftSlope, hRightValue, hRightSlope⟩
    have hleft1 : a * K.phi (-d) + c * K.psi (-d) = p := by
      dsimp [actualKummerCauchyValue] at hLeftValue
      rw [hshift] at hLeftValue
      dsimp [p]
      linear_combination hLeftValue
    have hleft2 : a * K.dphi (-d) + c * K.dpsi (-d) = q := by
      dsimp [actualKummerCauchyDeriv] at hLeftSlope
      rw [hshift] at hLeftSlope
      dsimp [q]
      linear_combination hLeftSlope
    obtain ⟨ha, hc⟩ :=
      actual_Kummer_Wronskian_Cauchy_coefficients_unique
        K (-d) ht p q a c hleft1 hleft2
    change a = actualKummerLeftMatchPhi K d F U DU at ha
    change c = actualKummerLeftMatchPsi K d F U DU at hc
    unfold actualKummerPhysicalRightTransfer
    rw [← ha, ← hc, hRightValue, hRightSlope]
  · intro hTransfer
    let a : ℂ := actualKummerLeftMatchPhi K d F U DU
    let c : ℂ := actualKummerLeftMatchPsi K d F U DU
    have hPair := actual_Kummer_Wronskian_two_Cauchy_jets_match
      K (-d) ht p q
    have hVal : actualKummerCauchyValue K d F a c (z-d) = U := by
      unfold actualKummerCauchyValue
      rw [hshift]
      have hp : a * K.phi (-d) + c * K.psi (-d) = p := hPair.1
      calc
        physicalLocalKummerValue K d F (z-d) +
            a * K.phi (-d) + c * K.psi (-d) =
          physicalLocalKummerValue K d F (z-d) +
            (a * K.phi (-d) + c * K.psi (-d)) := by ring
        _ = physicalLocalKummerValue K d F (z-d) + p := by rw [hp]
        _ = U := by dsimp [p]; ring
    have hDer : actualKummerCauchyDeriv K d F a c (z-d) = DU := by
      unfold actualKummerCauchyDeriv
      rw [hshift]
      have hq : a * K.dphi (-d) + c * K.dpsi (-d) = q := hPair.2
      calc
        physicalLocalKummerDeriv K d F (z-d) +
            a * K.dphi (-d) + c * K.dpsi (-d) =
          physicalLocalKummerDeriv K d F (z-d) +
            (a * K.dphi (-d) + c * K.dpsi (-d)) := by ring
        _ = physicalLocalKummerDeriv K d F (z-d) + q := by rw [hq]
        _ = DU := by dsimp [q]; ring
    refine ⟨a,c,hVal,hDer,?_,?_⟩
    · simpa only [actualKummerPhysicalRightTransfer, Prod.fst] using
        congrArg Prod.fst hTransfer
    · simpa only [actualKummerPhysicalRightTransfer, Prod.snd] using
        congrArg Prod.snd hTransfer

end HBL.TypeIIDynamicSelection
