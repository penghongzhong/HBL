import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSecondJetSplice
import Mathlib.Tactic

/-!
# Three physical C² interfaces from their actual source-dependent endpoint jets

The separately verified three-C¹ Hartree spectral field alone cannot
supply spatial derivative estimates for the full nonlinear residual:
the curvature jump may produce a delta distribution. This theorem
supplies the precise functional matching statement needed to eliminate
that artificial interface source, provided the three true second jets
have themselves been derived from the same physical Hartree profiles.

No time-order, independent curvature envelope, nonlocal PDE residual
gain, parameter Lipschitz or actual orbit is introduced here.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualHartreeSecondJetThreePiece
    (a b : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x ≤ a then f x else if x ≤ b then g x else 0

/-- True twice-differentiable three-piece field at both outer interfaces,
with curvature zero after the last interface. -/
theorem actual_Hartree_second_jet_three_piece_C2_interfaces
    (a b : ℝ) (hab : a < b)
    (f g : ℝ → ℂ) (d dd : ℂ)
    (hfa : HasDerivAt f d a)
    (hga : HasDerivAt g d a)
    (hva : f a = g a)
    (hf2a : HasDerivAt (deriv f) dd a)
    (hg2a : HasDerivAt (deriv g) dd a)
    (hgb : HasDerivAt g 0 b)
    (hvb : g b = 0)
    (hg2b : HasDerivAt (deriv g) 0 b) :
    let full := actualHartreeSecondJetThreePiece a b f g
    HasDerivAt full d a ∧
      HasDerivAt (deriv full) dd a ∧
      HasDerivAt full 0 b ∧
      HasDerivAt (deriv full) 0 b := by
  dsimp only
  let pieceA := actualHartreeSecondJetTwoPiece a f g
  let pieceB := actualHartreeSecondJetTwoPiece b g (fun _ => (0 : ℂ))
  let full := actualHartreeSecondJetThreePiece a b f g
  have hA := actual_Hartree_second_jet_two_piece_has_second_derivative
    a f g d dd hfa hga hva hf2a hg2a
  have hZero2 :
      HasDerivAt (deriv (fun _ : ℝ => (0 : ℂ))) 0 b := by
    have hz : deriv (fun _ : ℝ => (0 : ℂ)) = (fun _ => 0) := by
      funext y
      exact deriv_const y (0 : ℂ)
    rw [hz]
    exact hasDerivAt_const b (0 : ℂ)
  have hB := actual_Hartree_second_jet_two_piece_has_second_derivative
    b g (fun _ => (0 : ℂ)) 0 0 hgb
    (hasDerivAt_const b (0 : ℂ)) hvb hg2b hZero2
  have hNearA : full =ᶠ[𝓝 a] pieceA := by
    filter_upwards [Iio_mem_nhds hab] with y hy
    change y < b at hy
    by_cases hya : y ≤ a
    · simp [full, pieceA, actualHartreeSecondJetThreePiece,
        actualHartreeSecondJetTwoPiece, hya]
    · have hyb : y ≤ b := le_of_lt hy
      simp [full, pieceA, actualHartreeSecondJetThreePiece,
        actualHartreeSecondJetTwoPiece, hya, hyb]
  have hNearB : full =ᶠ[𝓝 b] pieceB := by
    filter_upwards [Ioi_mem_nhds hab] with y hy
    change a < y at hy
    have hya : ¬ y ≤ a := not_le.mpr hy
    simp [full, pieceB, actualHartreeSecondJetThreePiece,
      actualHartreeSecondJetTwoPiece, hya]
  have hDerNearA : deriv full =ᶠ[𝓝 a] deriv pieceA := by
    filter_upwards [Iio_mem_nhds hab] with x hx
    change x < b at hx
    have hLoc : full =ᶠ[𝓝 x] pieceA := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < b at hy
      by_cases hya : y ≤ a
      · simp [full, pieceA, actualHartreeSecondJetThreePiece,
          actualHartreeSecondJetTwoPiece, hya]
      · have hyb : y ≤ b := le_of_lt hy
        simp [full, pieceA, actualHartreeSecondJetThreePiece,
          actualHartreeSecondJetTwoPiece, hya, hyb]
    exact hLoc.deriv_eq
  have hDerNearB : deriv full =ᶠ[𝓝 b] deriv pieceB := by
    filter_upwards [Ioi_mem_nhds hab] with x hx
    change a < x at hx
    have hLoc : full =ᶠ[𝓝 x] pieceB := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change a < y at hy
      have hya : ¬ y ≤ a := not_le.mpr hy
      simp [full, pieceB, actualHartreeSecondJetThreePiece,
        actualHartreeSecondJetTwoPiece, hya]
    exact hLoc.deriv_eq
  exact ⟨hA.1.congr_of_eventuallyEq hNearA,
    hA.2.congr_of_eventuallyEq hDerNearA,
    hB.1.congr_of_eventuallyEq hNearB,
    hB.2.congr_of_eventuallyEq hDerNearB⟩

end HBL.TypeIIDynamicSelection
