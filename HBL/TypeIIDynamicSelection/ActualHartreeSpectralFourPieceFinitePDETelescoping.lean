import HBL.TypeIIDynamicSelection.ActualHartreeFullFourPieceFinitePDETelescoping
import HBL.TypeIIDynamicSelection.ActualHartreeSpectralCorrectedFourPieceThreeC1
import Mathlib.Tactic

/-!
# Exact NONLINEAR Hartree residual of finite spectral-corrected four-piece fields

The genuine corrected physical field consists of:
  (1) the original two-channel Fredholm inner solution,
  (2) the Cramer matched Kummer continuation, corrected by the actual
      zero-left-jet spectral Green solution,
  (3) an outer repair built from the NEW corrected right Cauchy jet,
  (4) the literal zero continuation.

At each physical time t the spectral displacement is an actual complex
function d(t), rather than a symbolic residual-order marker.
The entire renormalized original inverse-square quartic Hartree PDE residual
is evaluated on the SUM of these fields; consequently every nonlocal
cross interaction, moving endpoint contribution and time derivative is
retained inside the genuine differential operator.

The telescope below is an exact identity of these nonlinear residuals,
not an invalid linear superposition. It provides the correct FINITE
spectral-corrected target for the next source-norm estimates, but does not
by itself prove positive time order or dynamically selected blowup.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Genuine time-dependent spectral correction to the original Fredholm
four-region packet. The original PDE source F and all inner data are
inherited unchanged, with the additional time-dependent spectrum d. -/
structure ActualHartreeSpectralFourPieceMovingPacket where
  physical : ActualHartreeFullFourPieceMovingPacket
  delta : ℝ → ℂ

/-- This is the literal FOUR-piece spectral corrected PDE field, not
an artificial thin outer shell or a generic residual-order label. -/
def actualHartreeSpectralFullFourPieceMovingField
    (P : ActualHartreeSpectralFourPieceMovingPacket) (t y : ℝ) : ℂ :=
  actualHartreeInnerKummerSpectralFourPiece
    (P.physical.K t) (P.physical.L t) (P.physical.a t)
    P.physical.B (P.physical.Fp t) (P.physical.Fm t)
    (P.physical.hp t) (P.physical.hm t)
    (P.physical.F t) (P.delta t) y

def actualHartreeSpectralFiniteFourPieceField
    (packets : List ActualHartreeSpectralFourPieceMovingPacket)
    (t y : ℝ) : ℂ :=
  (packets.map (fun P =>
    actualHartreeSpectralFullFourPieceMovingField P t y)).sum

/-- The ORIGINAL nonlocal Hartree PDE residual gap, evaluated directly on
the genuinely spectral-corrected complete four-piece physical sum. -/
def actualHartreeSpectralFiniteFourPiecePDEGap
    (packets : List ActualHartreeSpectralFourPieceMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
      actualHartreeSpectralFiniteFourPieceField packets t y)
    b omega s r -
  complexRadialRenormalizedResidual
    (actualKummerFinitePhysicalBase ell c time z)
    b omega s r

/-- Increment of the complete original nonlinear Hartree PDE on the
ALREADY corrected finite background, including nonlocal cross terms. -/
def actualHartreeSpectralFiniteFourPiecePDEIncrements
    (packets : List ActualHartreeSpectralFourPieceMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  match packets with
  | [] => 0
  | P :: ps =>
      (complexRadialRenormalizedResidual
        (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
          actualHartreeSpectralFiniteFourPieceField ps t y +
          actualHartreeSpectralFullFourPieceMovingField P t y)
        b omega s r -
       complexRadialRenormalizedResidual
        (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
          actualHartreeSpectralFiniteFourPieceField ps t y)
        b omega s r) +
      actualHartreeSpectralFiniteFourPiecePDEIncrements
        ps ell c time z b omega s r

/-- Full quartic nonlocal Hartree residual telescopes for genuinely
spectral-corrected physical FOUR-piece packets. This is NOT linearity
of the Hartree operator and does NOT assign a time-gain exponent. -/
theorem actual_Hartree_finite_spectral_Fredholm_four_piece_full_PDE_telescopes
    (packets : List ActualHartreeSpectralFourPieceMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) :
    actualHartreeSpectralFiniteFourPiecePDEGap packets
       ell c time z b omega s r =
      actualHartreeSpectralFiniteFourPiecePDEIncrements packets
        ell c time z b omega s r := by
  induction packets with
  | nil =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualHartreeSpectralFiniteFourPieceField
              ([] : List ActualHartreeSpectralFourPieceMovingPacket) t y) =
          actualKummerFinitePhysicalBase ell c time z := by
        funext t y
        simp [actualHartreeSpectralFiniteFourPieceField]
      simp only [actualHartreeSpectralFiniteFourPiecePDEGap,
        actualHartreeSpectralFiniteFourPiecePDEIncrements, hEq, sub_self]
  | cons P ps ih =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualHartreeSpectralFiniteFourPieceField (P :: ps) t y) =
          (fun t y =>
            actualKummerFinitePhysicalBase ell c time z t y +
              actualHartreeSpectralFiniteFourPieceField ps t y +
                actualHartreeSpectralFullFourPieceMovingField P t y) := by
        funext t y
        change actualKummerFinitePhysicalBase ell c time z t y +
          (actualHartreeSpectralFullFourPieceMovingField P t y +
            actualHartreeSpectralFiniteFourPieceField ps t y) =
          actualKummerFinitePhysicalBase ell c time z t y +
            actualHartreeSpectralFiniteFourPieceField ps t y +
              actualHartreeSpectralFullFourPieceMovingField P t y
        abel
      have hSplit :
          actualHartreeSpectralFiniteFourPiecePDEGap (P :: ps)
              ell c time z b omega s r =
            (complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualHartreeSpectralFiniteFourPieceField ps t y +
                  actualHartreeSpectralFullFourPieceMovingField P t y)
              b omega s r -
             complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualHartreeSpectralFiniteFourPieceField ps t y)
              b omega s r) +
            actualHartreeSpectralFiniteFourPiecePDEGap ps
              ell c time z b omega s r := by
        unfold actualHartreeSpectralFiniteFourPiecePDEGap
        rw [hEq]
        ring
      rw [hSplit, ih]
      rfl

end HBL.TypeIIDynamicSelection
