import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import HBL.TypeIIDynamicSelection.ActualKummerFinitePhysicalPDETelescoping
import Mathlib.Tactic

/-!
# Literal time-dependent C1 Kummer Green/repair finite fields and nonlinear Hartree telescoping

The previously accepted finite PDE telescope used indicator-supported outer
repair tails, which are not themselves global C1 Kummer profiles when their
inner value jet is nonzero. Here each finite packet carries the SAME genuine
origin-normalized Kummer source, its physical inner Green branch, its
matching physical interface repair, and zero beyond the outer join.

The Kummer coefficients and normalization may vary with physical time; the
full original nonlinear nonlocal Hartree residual is evaluated on this
literal globally spliced finite field. Its exact finite telescoping is
proved algebraically WITHOUT any false linear superposition principle.

This theorem has no 9/4 residual upper bound: the next task is to estimate
each complete spliced-field increment, including its inner Green response,
moving joins, remote interactions and parameter time derivatives.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A literal moving, source-forced, origin-normalized Kummer branch,
its exact physical C1 repair, and zero exterior continuation. -/
structure ActualKummerC1SplicedMovingPacket where
  mu : ℝ → ℝ
  theta : ℝ → ℝ
  scale : ℝ → ℝ
  K : ∀ t : ℝ, OriginKummerPair (mu t) (theta t) (scale t)
  a : ℝ → ℝ
  r0 : ℝ
  B : ℝ
  F : ℝ → ℝ → ℂ
  U : ℝ → ℂ
  DU : ℝ → ℂ

/-- The actual time-dependent three-piece Green--repair--zero field,
not a discontinuous indicator-supported outer shell. -/
def actualKummerC1SplicedMovingField
    (P : ActualKummerC1SplicedMovingPacket) (t y : ℝ) : ℂ :=
  let w := actualOriginMatchedKummerValue
    (P.K t) P.r0 P.B (P.F t) (P.U t) (P.DU t)
  let v := actualOriginMatchedKummerPullback
    (P.K t) (P.a t) P.r0 P.B (P.F t) (P.U t) (P.DU t)
  let rep := actualKummerPhysicalInterfaceRepair
    (P.a t) P.B (w P.B)
    (actualOriginMatchedKummerSlope
      (P.K t) P.r0 P.B (P.F t) (P.U t) (P.DU t) P.B)
  actualPhysicalMatchedKummerC1Splice (P.a t) P.B v rep y

/-- Every time slice is genuinely C1 at both moving physical joins once
the original Green forcing is locally continuous and the geometric scale
is positive. No independently assigned boundary values or derivatives. -/
theorem actual_Kummer_C1_spliced_moving_packet_true_junctions
    (P : ActualKummerC1SplicedMovingPacket) (t : ℝ)
    (ha : 0 < P.a t)
    (hr0 : 0 < P.r0) (horder : P.r0 ≤ P.B)
    (hB : P.B < P.scale t)
    (hF : ∀ r ∈ Ioo (0 : ℝ) (P.scale t), ContinuousAt (P.F t) r) :
    let DUB := actualOriginMatchedKummerSlope
      (P.K t) P.r0 P.B (P.F t) (P.U t) (P.DU t) P.B
    HasDerivAt (actualKummerC1SplicedMovingField P t)
      ((1 / P.a t : ℝ) • DUB) (P.a t * P.B) ∧
    HasDerivAt (actualKummerC1SplicedMovingField P t)
      (0 : ℂ) (2 * P.a t * P.B) := by
  have h :=
    actual_Hartree_matched_Kummer_repair_is_C1_at_both_physical_joins
      (P.K t) (P.a t) ha hr0 horder hB (P.F t) hF (P.U t) (P.DU t)
  dsimp only at h ⊢
  exact h

/-- A genuine finite sum of full physical spliced Kummer fields. -/
def actualKummerFiniteFullC1Field
    (packets : List ActualKummerC1SplicedMovingPacket) (t y : ℝ) : ℂ :=
  (packets.map (fun P => actualKummerC1SplicedMovingField P t y)).sum

/-- The original complete inverse-square quartic Hartree PDE residual gap. -/
def actualKummerFiniteFullC1PDEGap
    (packets : List ActualKummerC1SplicedMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
      actualKummerFiniteFullC1Field packets t y) b omega s r -
  complexRadialRenormalizedResidual
    (actualKummerFinitePhysicalBase ell c time z) b omega s r

/-- Each increment evaluates the WHOLE original nonlinear Hartree operator
against the full previously spliced field, retaining all nonlocal crosses. -/
def actualKummerFiniteFullC1PDEIncrements
    (packets : List ActualKummerC1SplicedMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) : ℂ :=
  match packets with
  | [] => 0
  | P :: ps =>
    (complexRadialRenormalizedResidual
      (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
        actualKummerFiniteFullC1Field ps t y +
        actualKummerC1SplicedMovingField P t y) b omega s r -
     complexRadialRenormalizedResidual
      (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
        actualKummerFiniteFullC1Field ps t y) b omega s r) +
    actualKummerFiniteFullC1PDEIncrements ps ell c time z b omega s r

/-- Actual source-dependent global C1 Kummer fields satisfy exact full-Hartree
finite nonlinear PDE telescoping. This is an exact structural identity, NOT
an assertion of smallness or yet a revised §2.13 environment. -/
theorem actual_Hartree_finite_full_C1_spliced_PDE_residual_telescopes
    (packets : List ActualKummerC1SplicedMovingPacket)
    (ell c time : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ) :
    actualKummerFiniteFullC1PDEGap packets ell c time z b omega s r =
      actualKummerFiniteFullC1PDEIncrements packets
        ell c time z b omega s r := by
  induction packets with
  | nil =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFiniteFullC1Field
              ([] : List ActualKummerC1SplicedMovingPacket) t y) =
          actualKummerFinitePhysicalBase ell c time z := by
        funext t y
        simp [actualKummerFiniteFullC1Field]
      simp only [actualKummerFiniteFullC1PDEGap,
        actualKummerFiniteFullC1PDEIncrements, hEq, sub_self]
  | cons P ps ih =>
      have hEq :
          (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFiniteFullC1Field (P :: ps) t y) =
          (fun t y =>
            actualKummerFinitePhysicalBase ell c time z t y +
              actualKummerFiniteFullC1Field ps t y +
              actualKummerC1SplicedMovingField P t y) := by
        funext t y
        change actualKummerFinitePhysicalBase ell c time z t y +
          (actualKummerC1SplicedMovingField P t y +
            actualKummerFiniteFullC1Field ps t y) =
          actualKummerFinitePhysicalBase ell c time z t y +
            actualKummerFiniteFullC1Field ps t y +
              actualKummerC1SplicedMovingField P t y
        abel
      have hSplit :
          actualKummerFiniteFullC1PDEGap (P :: ps)
              ell c time z b omega s r =
            (complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFiniteFullC1Field ps t y +
                actualKummerC1SplicedMovingField P t y) b omega s r -
             complexRadialRenormalizedResidual
              (fun t y => actualKummerFinitePhysicalBase ell c time z t y +
                actualKummerFiniteFullC1Field ps t y) b omega s r) +
            actualKummerFiniteFullC1PDEGap ps ell c time z b omega s r := by
        unfold actualKummerFiniteFullC1PDEGap
        rw [hEq]
        ring
      rw [hSplit, ih]
      rfl

end HBL.TypeIIDynamicSelection
