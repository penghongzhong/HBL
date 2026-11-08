import HBL.TypeIIDynamicSelection.ActualHartreeMatchedZeroLeftSpectralWeightedResponse
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralLeftC1Exact
import Mathlib.Tactic

/-!
# Exact selected-source-compatible matched Kummer spectral quadratic residual

For a genuine origin-normalized Kummer matched field u0, its first
spectral-response source is q = d*u0. The exact zero-left-Cauchy-jet
Cramer/Green solve u1 has u1(a)=u1'(a)=0 and obeys L0 u1=q.
Hence the corrected matched field u=u0-u1 preserves both actual left
Fredholm coordinates, while L_d u-F=-d*u1.

The TRUE inverse-linear original Wronskian cancellation yields a
weighted quadratic residual with coefficient 2G²(b-a) and no
unweighted singular-basis constant depending on a.

The input weighted field bound r*|u0|<=H is visible here as an
INTERMEDIATE norm interface. The main Hartree theorem must derive H
from its actual selected source, Fredholm Cramer data and moving orbit,
rather than postulating any independent source decay or Type-II exponent.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_matched_spectral_left_C1_weighted_quadratic_residual
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b G H : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H)
    (r : ℝ) (hr : r ∈ Icc a b) :
    let v := actualHartreeMatchedSpectralCorrectedValue K a b F U DU d
    v a = U ∧
      HasDerivAt v DU a ∧
      ‖(r : ℂ) *
        (deriv (deriv v) r +
          frozenFirstCoeff r * deriv v r +
          (frozenZeroCoeff mu theta + d) * v r - F r)‖ ≤
          (2 * G ^ 2 * (b - a)) * (‖d‖ ^ 2 * H) := by
  dsimp only
  let u : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let q : ℝ → ℂ := fun x => d * u x
  let w1 : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  let v : ℝ → ℂ := actualHartreeMatchedSpectralCorrectedValue K a b F U DU d
  have hMatch :=
    actual_Hartree_matched_spectral_corrected_left_C1_and_exact_equation
      K a b ha hab hb F hF U DU d
  dsimp only at hMatch
  obtain ⟨hLeftValue, hLeftSlope, hEquation⟩ := hMatch
  have hSource :
      ‖(r : ℂ) * w1 r‖ ≤ (2 * G ^ 2 * (b - a)) * (‖d‖ * H) := by
    have hOrig : ∀ x ∈ Icc a b, ‖(x : ℂ) * u x‖ ≤ H := by
      intro x hx
      exact hProfile x hx
    exact actual_Hartree_matched_zero_left_spectral_weighted_response
      K a b G H ha hab hb hG hH hbound u hOrig d r hr
  have hrDomain : r ∈ Ioo (0 : ℝ) scale :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hExact :
      deriv (deriv v) r + frozenFirstCoeff r * deriv v r +
        (frozenZeroCoeff mu theta + d) * v r - F r =
          -(d * w1 r) := by
    have h := hEquation r hrDomain
    change deriv (deriv v) r + frozenFirstCoeff r * deriv v r +
      (frozenZeroCoeff mu theta + d) * v r = F r - d * w1 r at h
    rw [h]
    ring
  refine ⟨hLeftValue, hLeftSlope, ?_⟩
  change ‖(r : ℂ) *
      (deriv (deriv v) r + frozenFirstCoeff r * deriv v r +
        (frozenZeroCoeff mu theta + d) * v r - F r)‖ ≤ _
  rw [hExact]
  have hReorder :
      (r : ℂ) * (-(d * w1 r)) = -(d * ((r : ℂ) * w1 r)) := by ring
  rw [hReorder, norm_neg, norm_mul]
  calc
    ‖d‖ * ‖(r : ℂ) * w1 r‖ ≤
        ‖d‖ * ((2 * G ^ 2 * (b - a)) * (‖d‖ * H)) :=
      mul_le_mul_of_nonneg_left hSource (norm_nonneg d)
    _ = (2 * G ^ 2 * (b - a)) * (‖d‖ ^ 2 * H) := by ring

end HBL.TypeIIDynamicSelection
