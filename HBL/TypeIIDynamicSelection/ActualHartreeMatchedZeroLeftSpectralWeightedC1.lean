import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterraSlope
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedZeroLeftSpectralWeightedResponse
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummerClassical
import Mathlib.Tactic

/-!
# Source-faithful matched zero-left spectral Green: joint weighted C¹ norm

The earlier actual origin Volterra proof controls the corrected value r*u1,
but the full C¹ repair and physical radial H1 norm also require r²*u1'.
The original zero-left Green/Cramer slope is here controlled using the
new EXACT regularized first-derivative Wronskian cancellation.

The source q=d*u0 is literally the true first matched spectral forcing.
Its inverse-linear envelope is DERIVED from the weighted first-profile
bound ‖r u0(r)‖<=H, not independently prescribed for q. The resulting
constant 2(b+2)G²(b-a)|d|H has no inverse moving-left-radius powers.

A second theorem identifies the genuine classical derivative of u1,
provided the original matched profile is continuous at positive radii.
Neither theorem asserts an unproved time order of d or an arbitrary
whole-Hartree source envelope; the true selected Hartree producer must
supply H on the same physical orbit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Literal spectral source d*u, exact zero-left Cramer correction,
and BOTH radius-weighted physical C¹ coordinates. -/
theorem actual_Hartree_matched_zero_left_spectral_weighted_C1_response
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (u : ℝ → ℂ)
    (hWeighted : ∀ x ∈ Icc a b, ‖(x : ℂ) * u x‖ ≤ H)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) *
      actualOriginMatchedKummerValue K a b (fun x => d * u x) 0 0 r‖ +
    ‖(r : ℂ) ^ 2 *
      actualOriginMatchedKummerSlope K a b (fun x => d * u x) 0 0 r‖ ≤
      2 * (b + 2) * G ^ 2 * (b - a) * (‖d‖ * H) := by
  let C : ℝ := G * (1 / a + 1 / a ^ 2) + b ^ 2 + 1
  let q : ℝ → ℂ := fun x => d * u x
  have hK : OriginBasisOn K a b C :=
    origin_kummer_annulus_bound K a b G ha hb hG hbound
  have hM : 0 ≤ ‖d‖ * H :=
    mul_nonneg (norm_nonneg d) hH
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
  have hBoth :=
    actual_Hartree_zero_left_Kummer_regularized_Volterra_weighted_C1_bound
      K a b C G (‖d‖ * H) ha hab hb.le hG hM hK
      hbound q hQ r hr
  simpa only [q] using hBoth

/-- The slope above is the TRUE derivative of the same original matched
Green solution, not merely a label or a separately assumed Cauchy jet. -/
theorem actual_Hartree_matched_zero_left_spectral_weighted_C1_derivative
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (u : ℝ → ℂ)
    (hWeighted : ∀ x ∈ Icc a b, ‖(x : ℂ) * u x‖ ≤ H)
    (hCont : ∀ x ∈ Ioo 0 scale, ContinuousAt u x)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a b) :
    let q : ℝ → ℂ := fun x => d * u x
    let w1 : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
    ‖(r : ℂ) * w1 r‖ + ‖(r : ℂ) ^ 2 * deriv w1 r‖ ≤
      2 * (b + 2) * G ^ 2 * (b - a) * (‖d‖ * H) := by
  dsimp only
  let q : ℝ → ℂ := fun x => d * u x
  let w1 : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  have hQcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt q x := by
    intro x hx
    change ContinuousAt (fun y : ℝ => d * u y) x
    exact continuousAt_const.mul (hCont x hx)
  have hrPos : r ∈ Ioo (0 : ℝ) scale :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hDeriv :=
    (actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb q hQcont 0 0 r hrPos).1.deriv
  have hBoth :=
    actual_Hartree_matched_zero_left_spectral_weighted_C1_response
      K a b G H ha hab hb hG hH hbound u hWeighted d r hr
  change ‖(r : ℂ) * w1 r‖ +
    ‖(r : ℂ) ^ 2 * deriv w1 r‖ ≤ _
  rw [hDeriv]
  simpa only [q, w1] using hBoth

end HBL.TypeIIDynamicSelection
