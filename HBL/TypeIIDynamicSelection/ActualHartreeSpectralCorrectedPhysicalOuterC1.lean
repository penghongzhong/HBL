import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralLeftC1Exact
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import Mathlib.Tactic

/-!
# Actual first spectral-corrected Kummer field: both outer physical C¹ joins

For the literal Cramer matched solution u0 and its genuine zero-left
spectral correction u1, use the corrected profile u0-u1 through y=aB.
At y=aB the ORIGINAL physical repair is rebuilt from the corrected
value and derivative, not from the obsolete uncorrected upper jet.
At y=2aB both the repaired field and its slope vanish exactly.

Both new C¹ junction derivatives are constructed by actual HasDerivAt
proofs for the original matched Green fields, linearity, the physical
pullback and the original smooth repair. There is no artificial boundary
jet, outgoing-flux cancellation hypothesis, or prescribed Type-II rate.

The left Fredholm C¹ join and the true nonlinear Hartree full-residual
gain must be composed with these outer joins on the SAME selected orbit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_spectral_corrected_physical_two_outer_C1_joins
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a r0 B : ℝ)
    (ha : 0 < a) (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hB : B < scale)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r)
    (U DU d : ℂ) :
    let w := actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU d
    let v : ℝ → ℂ := fun y => w (y / a)
    let UB := w B
    let DUB := deriv w B
    let rep := actualKummerPhysicalInterfaceRepair a B UB DUB
    let glued := actualPhysicalMatchedKummerC1Splice a B v rep
    HasDerivAt glued ((1 / a : ℝ) • DUB) (a * B) ∧
      HasDerivAt glued (0 : ℂ) (2 * a * B) := by
  dsimp only
  let u0 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 B F U DU
  let q : ℝ → ℂ := fun x => d * u0 x
  let u1 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 B q 0 0
  let w : ℝ → ℂ := actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU d
  let v : ℝ → ℂ := fun y => w (y / a)
  let UB : ℂ := w B
  let DUB : ℂ := deriv w B
  let rep : ℝ → ℂ := actualKummerPhysicalInterfaceRepair a B UB DUB
  let glued : ℝ → ℂ := actualPhysicalMatchedKummerC1Splice a B v rep
  have hU := actual_origin_matched_Kummer_classical_on_positive_interval
    K hr0 hOrder hB F hF U DU
  have hQcont : ∀ x ∈ Ioo 0 scale, ContinuousAt q x := by
    intro x hx
    have hu : ContinuousAt u0 x := (hU x hx).1.continuousAt
    change ContinuousAt (fun z : ℝ => d * u0 z) x
    exact continuousAt_const.mul hu
  have hU1 := actual_origin_matched_Kummer_classical_on_positive_interval
    K hr0 hOrder hB q hQcont 0 0
  have hBDomain : B ∈ Ioo (0 : ℝ) scale :=
    ⟨hr0.trans_le hOrder, hB⟩
  have hW : HasDerivAt w (deriv w B) B := by
    have hD : DifferentiableAt ℝ (fun x => u0 x - u1 x) B :=
      (hU B hBDomain).1.differentiableAt.sub
        (hU1 B hBDomain).1.differentiableAt
    have hwEq : w = (fun x => u0 x - u1 x) := by funext x; rfl
    rw [hwEq]
    exact hD.hasDerivAt
  have hBpos : 0 < B := hr0.trans_le hOrder
  have hAt : a * B / a = B := by field_simp [ha.ne']
  have hV : HasDerivAt v ((1 / a : ℝ) • DUB) (a * B) := by
    have hPull := hW.scomp (a * B) ((hasDerivAt_id (a * B)).div_const a)
    simpa only [v, DUB, Function.comp_def, id_eq, hAt, one_div,
      Complex.real_smul, Complex.ofReal_inv] using hPull
  have hEnds := actual_Kummer_physical_interface_repair_endpoint_jets
    a B ha hBpos UB DUB
  have hRepL : HasDerivAt rep ((1 / a : ℝ) • DUB) (a * B) := by
    have hd := (actual_Kummer_physical_interface_repair_derivatives
      a B (a * B) ha.ne' hBpos.ne' UB DUB).1
    rw [hEnds.2.1] at hd
    exact hd
  have hRepR : HasDerivAt rep (0 : ℂ) (2 * a * B) := by
    have hd := (actual_Kummer_physical_interface_repair_derivatives
      a B (2 * a * B) ha.ne' hBpos.ne' UB DUB).1
    rw [hEnds.2.2.2] at hd
    exact hd
  have hValL : v (a * B) = rep (a * B) := by
    change w (a * B / a) = rep (a * B)
    rw [hAt, hEnds.1]
  have hValR : rep (2 * a * B) = 0 := hEnds.2.2.1
  have hAB : a * B < 2 * a * B := by
    have hp := mul_pos ha hBpos
    linarith
  exact actual_physical_three_piece_C1_interfaces
    (a * B) (2 * a * B) hAB v rep
    ((1 / a : ℝ) • DUB) hV hRepL hValL hRepR hValR

end HBL.TypeIIDynamicSelection
