import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerC1Splice
import Mathlib.Tactic

/-!
# Real second-jet matching rather than a formal C¹ boundary identity

The original physical spectral four-piece field is C¹ at its joins.
To apply any source norm that differentiates the full Hartree residual,
the actual joined function needs at least second-jet transmission.
This module supplies the nontrivial differentiability bridge: matching
both first and second jets of the *same two concrete branches* gives
a real twice-differentiable splice. No smallness or PDE orbit is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

def actualHartreeSecondJetTwoPiece
    (R : ℝ) (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  if y ≤ R then f y else g y

private theorem actual_Hartree_second_jet_two_piece_first
    (R : ℝ) (f g : ℝ → ℂ) (d : ℂ)
    (hf : HasDerivAt f d R)
    (hg : HasDerivAt g d R)
    (hv : f R = g R) :
    HasDerivAt (actualHartreeSecondJetTwoPiece R f g) d R := by
  have hleft :
      HasDerivWithinAt (actualHartreeSecondJetTwoPiece R f g)
        d (Iic R) R := by
    apply hf.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x ≤ R at hx
      simp [actualHartreeSecondJetTwoPiece, hx]
    · exact le_refl R
  have hright :
      HasDerivWithinAt (actualHartreeSecondJetTwoPiece R f g)
        d (Ici R) R := by
    apply hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change R ≤ x at hx
      by_cases hxr : x = R
      · subst x
        simp [actualHartreeSecondJetTwoPiece, hv]
      · have hrx : R < x := lt_of_le_of_ne hx (Ne.symm hxr)
        simp [actualHartreeSecondJetTwoPiece, not_le.mpr hrx]
    · exact le_refl R
  have hjoin := hleft.union hright
  have hunion : (Iic R ∪ Ici R) = (Set.univ : Set ℝ) := by
    ext y
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total y R
  rw [hunion] at hjoin
  exact hjoin.hasDerivAt (by simp)

/-- A genuinely twice differentiable splice, not just first-jet matching.
The assumptions are entirely the values and actual derivatives of f and
g at R; no second-derivative boundary data are independently prescribed. -/
theorem actual_Hartree_second_jet_two_piece_has_second_derivative
    (R : ℝ) (f g : ℝ → ℂ) (d dd : ℂ)
    (hf : HasDerivAt f d R)
    (hg : HasDerivAt g d R)
    (hv : f R = g R)
    (hf2 : HasDerivAt (deriv f) dd R)
    (hg2 : HasDerivAt (deriv g) dd R) :
    HasDerivAt (actualHartreeSecondJetTwoPiece R f g) d R ∧
    HasDerivAt (deriv (actualHartreeSecondJetTwoPiece R f g)) dd R := by
  have hfirst := actual_Hartree_second_jet_two_piece_first
    R f g d hf hg hv
  have hderiv : deriv (actualHartreeSecondJetTwoPiece R f g) =
      actualHartreeSecondJetTwoPiece R (deriv f) (deriv g) := by
    funext x
    rcases lt_trichotomy x R with hx | hx | hx
    · have hlocal :
          actualHartreeSecondJetTwoPiece R f g =ᶠ[𝓝 x] f := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        simp [actualHartreeSecondJetTwoPiece, le_of_lt hy]
      change deriv (actualHartreeSecondJetTwoPiece R f g) x =
        (if x ≤ R then deriv f x else deriv g x)
      rw [hlocal.deriv_eq]
      simp [le_of_lt hx]
    · subst x
      change deriv (actualHartreeSecondJetTwoPiece R f g) R =
        (if R ≤ R then deriv f R else deriv g R)
      rw [hfirst.deriv, hf.deriv]
      simp
    · have hlocal :
          actualHartreeSecondJetTwoPiece R f g =ᶠ[𝓝 x] g := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        simp [actualHartreeSecondJetTwoPiece, not_le.mpr hy]
      change deriv (actualHartreeSecondJetTwoPiece R f g) x =
        (if x ≤ R then deriv f x else deriv g x)
      rw [hlocal.deriv_eq]
      simp [not_le.mpr hx]
  constructor
  · exact hfirst
  · rw [hderiv]
    exact actual_Hartree_second_jet_two_piece_first
      R (deriv f) (deriv g) dd hf2 hg2
        (hf.deriv.trans hg.deriv.symm)

end HBL.TypeIIDynamicSelection
