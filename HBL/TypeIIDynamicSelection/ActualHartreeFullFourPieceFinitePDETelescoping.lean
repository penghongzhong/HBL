import HBL.TypeIIDynamicSelection.ActualHartreeInnerKummerRepairFourPieceC1
import HBL.TypeIIDynamicSelection.ActualKummerFinitePhysicalPDETelescoping
import Mathlib.Tactic

/-!
# True Fredholm-inner, Kummer-Green, repair, zero: finite nonlinear Hartree PDE

The actual moving field here is NOT just the outer interface tail and not
a Kummer Green continuation incorrectly applied down to the origin.
Each packet uses the proven radial two-channel Fredholm inner inverse
up to its physical L(t), the SAME real normalized origin Kummer Green
continuation, the genuine physical C1 interface repair on the dyadic
shell, and zero beyond. The same original complete 3D Hartree nonlocal
operator is used to form each full field's nonlinear PDE residual.

The finite telescope is an exact original-PDE difference, NOT linear
superposition and NOT a claimed full 9/4 bound. Real source estimates
for each of its corrected full four-piece terms, including all time
derivatives, are essential for the retained revised manuscript §2.13.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual time-dependent Hartree Fredholm and Kummer source data,
with the genuine weighted inverse membership at EVERY physical time. -/
structure ActualHartreeFullFourPieceMovingPacket where
  mu : ℝ → ℝ
  theta : ℝ → ℝ
  scale : ℝ → ℝ
  K : ∀ t : ℝ, OriginKummerPair (mu t) (theta t) (scale t)
  L : ℝ → ℝ
  a : ℝ → ℝ
  B : ℝ
  Fp : ℝ → ℝ → ℝ
  Fm : ℝ → ℝ → ℝ
  hp : ∀ t : ℝ, InWeightedL2 (7 / 4 : ℝ) (Fp t)
  hm : ∀ t : ℝ, InWeightedL2 (7 / 4 : ℝ) (Fm t)
  F : ℝ → ℝ → ℂ

/-- The original physical four-piece correction, not an artificial
indicator-supported outer Kummer perturbation. -/
def actualHartreeFullFourPieceMovingField
    (P : ActualHartreeFullFourPieceMovingPacket) (t y : ℝ) : ℂ :=
  actualHartreeInnerKummerFourPiece
    (P.K t) (P.L t) (P.a t) P.B
    (P.Fp t) (P.Fm t) (P.hp t) (P.hm t) (P.F t) y

/-- A genuine finite sum of full physical Fredholm-inner/Kummer four-piece corrections. -/
def actualHartreeFiniteFullFourPieceField
    (packets : List ActualHartreeFullFourPieceMovingPacket) (t y : ℝ) : ℂ :=
  (packets.map (fun P => actualHartreeFullFourPieceMovingField P t y)).sum

/-- The original complete inverse-square quartic Hartree PDE residual gap. -/
def actualHartreeFiniteFullFourPiecePDEGap
    (packets : List ActualHartreeFullFourPieceMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
      actualHartreeFiniteFullFourPieceField packets t y) b omega s r -
  complexRadialRenormalizedResidual
    (actualKummerFinitePhysicalBase ell c time z) b omega s r

/-- Each increment evaluates the WHOLE original nonlinear Hartree operator
against the full previously spliced field, retaining all nonlocal crosses. -/
def actualHartreeFiniteFullFourPiecePDEIncrements
    (packets : List ActualHartreeFullFourPieceMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  match packets with
  | [] => 0
  | P :: ps =>
    (complexRadialRenormalizedResidual
      (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
        actualHartreeFiniteFullFourPieceField ps t y +
        actualHartreeFullFourPieceMovingField P t y) b omega s r -
     complexRadialRenormalizedResidual
      (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
        actualHartreeFiniteFullFourPieceField ps t y) b omega s r) +
    actualHartreeFiniteFullFourPiecePDEIncrements ps ell c time z b omega s r

/-- Actual source-dependent global C1 Kummer fields satisfy exact full-Hartree
finite nonlinear PDE telescoping. This is an exact structural identity, NOT
an assertion of smallness or yet a revised §2.13 environment. -/
theorem actual_Hartree_finite_original_Fredholm_four_piece_PDE_telescopes
    (packets : List ActualHartreeFullFourPieceMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) :
    actualHartreeFiniteFullFourPiecePDEGap packets ell c time z b omega s r =
      actualHartreeFiniteFullFourPiecePDEIncrements packets
        ell c time z b omega s r := by
  induction packets with
  | nil =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualHartreeFiniteFullFourPieceField
              ([] : List ActualHartreeFullFourPieceMovingPacket) t y) =
          actualKummerFinitePhysicalBase ell c time z := by
        funext t y
        simp [actualHartreeFiniteFullFourPieceField]
      simp only [actualHartreeFiniteFullFourPiecePDEGap,
        actualHartreeFiniteFullFourPiecePDEIncrements, hEq, sub_self]
  | cons P ps ih =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualHartreeFiniteFullFourPieceField (P :: ps) t y) =
          (fun t y =>
            actualKummerFinitePhysicalBase ell c time z t y +
              actualHartreeFiniteFullFourPieceField ps t y +
              actualHartreeFullFourPieceMovingField P t y) := by
        funext t y
        change actualKummerFinitePhysicalBase ell c time z t y +
          (actualHartreeFullFourPieceMovingField P t y +
            actualHartreeFiniteFullFourPieceField ps t y) =
          actualKummerFinitePhysicalBase ell c time z t y +
            actualHartreeFiniteFullFourPieceField ps t y +
              actualHartreeFullFourPieceMovingField P t y
        abel
      have hSplit :
          actualHartreeFiniteFullFourPiecePDEGap (P :: ps)
              ell c time z b omega s r =
            (complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualHartreeFiniteFullFourPieceField ps t y +
                actualHartreeFullFourPieceMovingField P t y) b omega s r -
             complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualHartreeFiniteFullFourPieceField ps t y) b omega s r) +
            actualHartreeFiniteFullFourPiecePDEGap ps ell c time z b omega s r := by
        unfold actualHartreeFiniteFullFourPiecePDEGap
        rw [hEq]
        ring
      rw [hSplit, ih]
      rfl

end HBL.TypeIIDynamicSelection
