import HBL.TypeIIDynamicSelection.ActualHartreeSpectralCorrectedFourPieceThreeC1
import Mathlib.Tactic

/-!
# Actual Hartree-selected backward Fredholm/Kummer smooth overlap

This replacement for the unquantified C¹-only repair is made directly
from the genuine fixed Fredholm inner response and the same-source,
spectral-corrected original Kummer Cramer/Green field.

The inner transition is intentionally within [L/2,L], where actual
inner-Fredholm source estimates are available; the prior candidate
transition to the right of L was not justified by those source estimates.

The outer transition lies strictly before aB: no out-of-domain Kummer
extension or pointwise F(B) / w''(B) curvature trace is inserted.
This module proves literal support geometry and region identities,
NOT the full nonlinear PDE time residual, parameter estimates, or orbit.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeFlatInnerTransition (L y : ℝ) : ℝ :=
  cutoff ((y - L + 4 * (L / 8)) / (L / 8))

def actualHartreeFlatOuterTransition (L a B y : ℝ) : ℝ :=
  1 - cutoff ((y - a * B + 4 * ((a * B - L) / 8)) /
     ((a * B - L) / 8))

/-- Real original inner and matched spectral Cramer Green fields, without
a free interface curvature jet or a prescribed blow-up rate. -/
def actualHartreeSameSourceBackwardFlatOverlap
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L a B : ℝ)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (d : ℂ) (y : ℝ) : ℂ :=
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let w := actualHartreeMatchedSpectralCorrectedValue
    K (L / a) B F J.1 J.2 d
  let eta : ℂ := (actualHartreeFlatInnerTransition L y : ℂ)
  let chi : ℂ := (actualHartreeFlatOuterTransition L a B y : ℂ)
  (1 - eta) * u y + eta * chi * w (y / a)

/-- Exact (not asymptotic) inner support, plateau, and outer support of
the true backward-domain two-cutoff field. This is not a residual gain. -/
theorem actual_Hartree_same_source_backward_flat_overlap_regions
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (L a B : ℝ) (hL : 0 < L) (hGap : L < a * B)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (F : ℝ → ℂ) (d : ℂ) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let w := actualHartreeMatchedSpectralCorrectedValue
      K (L / a) B F J.1 J.2 d
    (∀ y : ℝ, y ≤ 5 * L / 8 →
      actualHartreeSameSourceBackwardFlatOverlap
        K L a B Fp Fm hp hm F d y = u y) ∧
    (∀ y : ℝ, 3 * L / 4 ≤ y →
      y ≤ L + 5 * ((a * B - L) / 8) →
      actualHartreeSameSourceBackwardFlatOverlap
        K L a B Fp Fm hp hm F d y = w (y / a)) ∧
    (∀ y : ℝ, L + 6 * ((a * B - L) / 8) ≤ y →
      actualHartreeSameSourceBackwardFlatOverlap
        K L a B Fp Fm hp hm F d y = 0) := by
  dsimp only
  have hIn : 0 < L / 8 := div_pos hL (by norm_num)
  have hOut : 0 < (a * B - L) / 8 :=
    div_pos (sub_pos.mpr hGap) (by norm_num)
  have hEta0 (y : ℝ) (hy : y ≤ 5 * L / 8) :
      actualHartreeFlatInnerTransition L y = 0 := by
    unfold actualHartreeFlatInnerTransition
    apply cutoff_zero_of_le_one
    apply (div_le_one hIn).2
    linarith
  have hEta1 (y : ℝ) (hy : 3 * L / 4 ≤ y) :
      actualHartreeFlatInnerTransition L y = 1 := by
    unfold actualHartreeFlatInnerTransition
    apply cutoff_one_of_two_le
    apply (le_div_iff₀ hIn).2
    linarith
  have hChi1 (y : ℝ)
      (hy : y ≤ L + 5 * ((a * B - L) / 8)) :
      actualHartreeFlatOuterTransition L a B y = 1 := by
    unfold actualHartreeFlatOuterTransition
    have hc : cutoff ((y - a * B + 4 * ((a * B - L) / 8)) /
       ((a * B - L) / 8)) = 0 := by
      apply cutoff_zero_of_le_one
      apply (div_le_one hOut).2
      linarith
    rw [hc]
    ring
  have hChi0 (y : ℝ)
      (hy : L + 6 * ((a * B - L) / 8) ≤ y) :
      actualHartreeFlatOuterTransition L a B y = 0 := by
    unfold actualHartreeFlatOuterTransition
    have hc : cutoff ((y - a * B + 4 * ((a * B - L) / 8)) /
       ((a * B - L) / 8)) = 1 := by
      apply cutoff_one_of_two_le
      apply (le_div_iff₀ hOut).2
      linarith
    rw [hc]
    ring
  have hOuterImpliesEta (y : ℝ)
      (hy : L + 6 * ((a * B - L) / 8) ≤ y) :
      3 * L / 4 ≤ y := by
    have hgapnonneg : 0 ≤ (a * B - L) / 8 := le_of_lt hOut
    linarith
  constructor
  · intro y hy
    unfold actualHartreeSameSourceBackwardFlatOverlap
    dsimp only
    rw [hEta0 y hy]
    norm_num
  constructor
  · intro y hy hyo
    unfold actualHartreeSameSourceBackwardFlatOverlap
    dsimp only
    rw [hEta1 y hy, hChi1 y hyo]
    norm_num
  · intro y hy
    unfold actualHartreeSameSourceBackwardFlatOverlap
    dsimp only
    rw [hEta1 y (hOuterImpliesEta y hy), hChi0 y hy]
    norm_num

end HBL.TypeIIDynamicSelection
