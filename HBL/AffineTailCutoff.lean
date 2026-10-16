import HBL.AffineTailCharge
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
Concrete smooth affine cutoff used in the manuscript's second numbered lemma.

We choose
  chi_aff(r) = smoothTransition(r - 1).
Thus chi_aff is C-infinity, vanishes on (-infinity,1], and equals one on
[2,infinity).  Consequently q_aff(r)=chi_aff(r) r is exactly the affine
function r in the far field.
-/

noncomputable section

open scoped Topology ContDiff

namespace HBL.Modulation.AffineTail

/-- A concrete manuscript-compatible affine cutoff. -/
def cutoff (r : ℝ) : ℝ :=
  Real.smoothTransition (r - 1)

/-- The affine tail model `chi_aff(r) r`. -/
def model (r : ℝ) : ℝ :=
  cutoff r * r

/-- The chosen cutoff is infinitely differentiable. -/
theorem cutoff_contDiff_infty :
    ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  exact Real.smoothTransition.contDiff.comp
    (contDiff_id.sub contDiff_const)

/-- It vanishes on the whole inner interval r <= 1. -/
theorem cutoff_zero_of_le_one (r : ℝ) (hr : r ≤ 1) :
    cutoff r = 0 := by
  unfold cutoff
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- It equals one throughout the far region r >= 2. -/
theorem cutoff_one_of_two_le (r : ℝ) (hr : 2 ≤ r) :
    cutoff r = 1 := by
  unfold cutoff
  exact Real.smoothTransition.one_of_one_le (by linarith)

/-- The affine model is itself C-infinity. -/
theorem model_contDiff_infty :
    ContDiff ℝ ∞ model := by
  unfold model
  exact cutoff_contDiff_infty.mul contDiff_id

/-- The affine model vanishes on the inner interval. -/
theorem model_zero_of_le_one (r : ℝ) (hr : r ≤ 1) :
    model r = 0 := by
  simp [model, cutoff_zero_of_le_one r hr]

/-- In the far field the affine model is exactly r. -/
theorem model_eq_id_of_two_le (r : ℝ) (hr : 2 ≤ r) :
    model r = r := by
  simp [model, cutoff_one_of_two_le r hr]

end HBL.Modulation.AffineTail
