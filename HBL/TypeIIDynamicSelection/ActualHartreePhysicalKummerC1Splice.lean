import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerRepairTwoC1Jets
import Mathlib.Tactic

/-!
# Genuine C1 gluing of the matched physical Kummer interior and repair shell

The standalone indicator-supported Kummer replacement is NOT globally
continuous at its left endpoint when the selected value jet is nonzero.
The correct actual physical profile uses the already constructed origin
Kummer solution to the left, the same physical repair to the right, and
zero after the repair's second endpoint.

The two exact physical C1 jets were proved from the genuine same-source
origin Green solution and the selected compatibility matrix. Here we
turn those endpoint identities into true derivatives of the piecewise
field itself, not merely matching numbers. This is a genuine C1-interface
producer, not yet full inner/remote Hartree Hdot1 assembly.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

private def physicalTwoPiece (a : ℝ) (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  if y ≤ a then f y else g y

private theorem physicalTwoPiece_hasDerivAt_at_join
    (a : ℝ) (f g : ℝ → ℂ) (d : ℂ)
    (hf : HasDerivAt f d a)
    (hg : HasDerivAt g d a)
    (hv : f a = g a) :
    HasDerivAt (physicalTwoPiece a f g) d a := by
  have heqL : EqOn (physicalTwoPiece a f g) f (Iic a) := by
    intro y hy
    change (if y ≤ a then f y else g y) = f y
    simp [hy]
  have heqR : EqOn (physicalTwoPiece a f g) g (Ici a) := by
    intro y hy
    by_cases hya : y = a
    · subst y
      simp [physicalTwoPiece, hv]
    · have hay : a < y := lt_of_le_of_ne hy (Ne.symm hya)
      simp [physicalTwoPiece, not_le.mpr hay]
  have hleft :
      HasDerivWithinAt (physicalTwoPiece a f g) d (Iic a) a := by
    apply hf.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact heqL hy
    · exact le_refl a
  have hright :
      HasDerivWithinAt (physicalTwoPiece a f g) d (Ici a) a := by
    apply hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact heqR hy
    · exact le_refl a
  have hjoin := hleft.union hright
  have hUnion : (Iic a ∪ Ici a) = (Set.univ : Set ℝ) := by
    ext y
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total y a
  rw [hUnion] at hjoin
  exact hjoin.hasDerivAt (by simp)

/-- Correct physical 3-piece Kummer field. The actual forced Kummer
solution is retained to the left of aB. The same sign physical repair
is used on (aB,2aB], and the field vanishes farther out. -/
def actualPhysicalMatchedKummerC1Splice
    (a B : ℝ) (v rep : ℝ → ℂ) (y : ℝ) : ℂ :=
  if y ≤ a * B then v y else
    if y ≤ 2 * a * B then rep y else 0

/-- Any two genuine C1 endpoint identities produce an actual field
differentiable at both interfaces, not just matching value/slope pairs. -/
theorem actual_physical_three_piece_C1_interfaces
    (a b : ℝ) (hab : a < b)
    (f g : ℝ → ℂ) (d : ℂ)
    (hf : HasDerivAt f d a)
    (hga : HasDerivAt g d a)
    (hva : f a = g a)
    (hgb : HasDerivAt g (0 : ℂ) b)
    (hvb : g b = 0) :
    let splice : ℝ → ℂ := fun y =>
      if y ≤ a then f y else if y ≤ b then g y else 0
    HasDerivAt splice d a ∧ HasDerivAt splice 0 b := by
  dsimp only
  let splice : ℝ → ℂ := fun y =>
    if y ≤ a then f y else if y ≤ b then g y else 0
  let pieceL := physicalTwoPiece a f g
  let pieceR := physicalTwoPiece b g (fun _ => (0 : ℂ))
  have hLeft : HasDerivAt pieceL d a :=
    physicalTwoPiece_hasDerivAt_at_join a f g d hf hga hva
  have hRight : HasDerivAt pieceR 0 b :=
    physicalTwoPiece_hasDerivAt_at_join b g (fun _ => (0 : ℂ)) 0
      hgb (hasDerivAt_const b (0 : ℂ)) hvb
  have hNearL : splice =ᶠ[𝓝 a] pieceL := by
    filter_upwards [Iio_mem_nhds hab] with y hy
    by_cases hya : y ≤ a
    · simp [splice, pieceL, physicalTwoPiece, hya]
    · have hyb : y ≤ b := le_of_lt hy
      simp [splice, pieceL, physicalTwoPiece, hya, hyb]
  have hNearR : splice =ᶠ[𝓝 b] pieceR := by
    filter_upwards [Ioi_mem_nhds hab] with y hy
    have hya : ¬y ≤ a := not_le.mpr hy
    simp [splice, pieceR, physicalTwoPiece, hya]
  constructor
  · exact hLeft.congr_of_eventuallyEq hNearL
  · exact hRight.congr_of_eventuallyEq hNearR

/-- For the actual origin-normalized Green solution, *same-source*
boundary jet UB,DUB and its physical repair, the correctly spliced
field is differentiable at both physical junctions. The derivative
equals the genuine shared interface slope and zero at the far edge. -/
theorem actual_Hartree_matched_Kummer_repair_is_C1_at_both_physical_joins
    {mu theta scale r0 B : ℝ} (K : OriginKummerPair mu theta scale)
    (a : ℝ) (ha : 0 < a)
    (hr0 : 0 < r0) (horder : r0 ≤ B) (hB : B < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU : ℂ) :
    let w := actualOriginMatchedKummerValue K r0 B F U DU
    let v := actualOriginMatchedKummerPullback K a r0 B F U DU
    let UB := w B
    let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
    let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
    let glued := actualPhysicalMatchedKummerC1Splice a B v rep
    HasDerivAt glued ((1 / a : ℝ) • DUB) (a * B) ∧
      HasDerivAt glued 0 (2 * a * B) := by
  dsimp only
  let w := actualOriginMatchedKummerValue K r0 B F U DU
  let v := actualOriginMatchedKummerPullback K a r0 B F U DU
  let UB := w B
  let DUB := actualOriginMatchedKummerSlope K r0 B F U DU B
  let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
  have hBpos : 0 < B := hr0.trans_le horder
  have hScale : 0 < scale := hBpos.trans hB
  have hDomain : a * B ∈ Ioo (0 : ℝ) (a * scale) :=
    ⟨mul_pos ha hBpos, mul_lt_mul_of_pos_left hB ha⟩
  have hMatch :=
    actual_Hartree_matched_Kummer_physical_repair_two_C1_jets
      K a ha hr0 horder hB F hF U DU
  dsimp only at hMatch
  have hPullback :=
    actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hB F hF U DU (a * B) hDomain
  have hV : HasDerivAt v ((1 / a : ℝ) • DUB) (a * B) := by
    have hfrom : HasDerivAt v (deriv v (a * B)) (a * B) :=
      hPullback.1.differentiableAt.hasDerivAt
    have hD := hMatch.2.1
    have hK :
        deriv v (a * B) = (1 / a : ℝ) • DUB := by
      have hRepD :=
        (actual_Kummer_physical_interface_repair_derivatives
          a B (a * B) ha.ne' hBpos.ne' UB DUB).1.deriv
      rw [hD, hRepD]
      exact (actual_Kummer_physical_interface_repair_endpoint_jets
        a B ha hBpos UB DUB).2.1
    simpa only [hK] using hfrom
  have hRepLeft : HasDerivAt rep ((1 / a : ℝ) • DUB) (a * B) := by
    have ht := (actual_Kummer_physical_interface_repair_derivatives
      a B (a * B) ha.ne' hBpos.ne' UB DUB).1
    rw [(actual_Kummer_physical_interface_repair_endpoint_jets
      a B ha hBpos UB DUB).2.1] at ht
    exact ht
  have hRepRight : HasDerivAt rep 0 (2 * a * B) := by
    have ht := (actual_Kummer_physical_interface_repair_derivatives
      a B (2 * a * B) ha.ne' hBpos.ne' UB DUB).1
    rw [(actual_Kummer_physical_interface_repair_endpoint_jets
      a B ha hBpos UB DUB).2.2.2] at ht
    exact ht
  have hEnds := actual_Kummer_physical_interface_repair_endpoint_jets
    a B ha hBpos UB DUB
  have hValA : v (a * B) = rep (a * B) := hMatch.1
  have hValB : rep (2 * a * B) = 0 := hEnds.2.2.1
  have hAB : a * B < 2 * a * B := by
    have hp := mul_pos ha hBpos
    linarith
  exact actual_physical_three_piece_C1_interfaces
    (a * B) (2 * a * B) hAB v rep
      ((1 / a : ℝ) • DUB) hV hRepLeft hValA hRepRight hValB

end HBL.TypeIIDynamicSelection
