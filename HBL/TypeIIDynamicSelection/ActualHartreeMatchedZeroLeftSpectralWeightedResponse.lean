import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterra
import HBL.KummerOriginBasis.AnnulusBound
import Mathlib.Tactic

/-!
# Genuine zero-left Kummer spectral correction in the regularized weighted norm

For any actual origin-normalized physical Kummer pair, the true
Wronskian cancels the inverse-linear source loss. The original matched
Green/Cramer solution with zero LEFT value and slope is the actual
Volterra response, not a newly postulated abstract right inverse.

Given a weighted profile r*|u(r)| <= H, set q(r)=d*u(r). Then
r*|G_left[q](r)| <= 2 G² (b-a) |d| H, for EVERY a<=r<=b,
where G is the true regularized IVP bound on y,x (not the singular
physical basis). The annular OriginBasisOn certificate is DERIVED
from the original IVP and used only for exact Cramer identities;
its a^-1 and a^-2 constants do not enter the final bound.

This is the stable one-step spectral-response estimate needed for
repeated physical matching. The true selected Hartree field must
supply the input weighted profile norm; it is not assumed by
the eventual II-type existence theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_matched_zero_left_spectral_weighted_response
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G H : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (u : ℝ → ℂ)
    (hWeighted : ∀ x ∈ Icc a b, ‖(x : ℂ) * u x‖ ≤ H)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) *
      actualOriginMatchedKummerValue K a b (fun x => d * u x) 0 0 r‖ ≤
        (2 * G ^ 2 * (b - a)) * (‖d‖ * H) := by
  let C : ℝ := G * (1 / a + 1 / a ^ 2) + b ^ 2 + 1
  let q : ℝ → ℂ := fun x => d * u x
  have hK : OriginBasisOn K a b C := by
    exact origin_kummer_annulus_bound K a b G ha hb hG hbound
  have hM : 0 ≤ ‖d‖ * H := mul_nonneg (norm_nonneg d) hH
  have hQ : ∀ x ∈ Icc a b, ‖q x‖ ≤ (‖d‖ * H) / x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    have hX : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    have hU : ‖u x‖ ≤ H / x := by
      apply (le_div_iff₀ hxpos).2
      have hw := hWeighted x hx
      rw [norm_mul, hX] at hw
      simpa only [mul_comm] using hw
    change ‖d * u x‖ ≤ (‖d‖ * H) / x
    rw [norm_mul]
    calc
      ‖d‖ * ‖u x‖ ≤ ‖d‖ * (H / x) :=
        mul_le_mul_of_nonneg_left hU (norm_nonneg d)
      _ = (‖d‖ * H) / x := by ring
  have hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hbound x hx).1, (hbound x hx).2.2.1⟩
  have hEstimate :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_value_bound
      K a b C G (‖d‖ * H) ha hab hb.le hG hM hK
      hModes q hQ r hr
  simpa only [q] using hEstimate

end HBL.TypeIIDynamicSelection
