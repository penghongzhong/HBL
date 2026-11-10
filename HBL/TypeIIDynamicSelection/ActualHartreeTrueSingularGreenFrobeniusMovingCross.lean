import HBL.TypeIIDynamicSelection.ActualHartreeSingularGreenFrobeniusQuadraticRadius
import HBL.TypeIIDynamicSelection.ActualHartreeOnePhysicalMovingSingularGreenFullDerivative
import HBL.TypeIIDynamicSelection.ActualOriginGreenMovingSingularChannel
import Mathlib.Tactic

/-!
# The true nonlocal Hartree source has a quadratic-radius smaller moving slit

The ORIGINAL singular outgoing Green source density is X/W times the
same genuinely nonlocal three-dimensional quartic Hartree forcing
selected by the unique real Cramer speeds.

The normalized Frobenius ODE shows |X/W| <= C*r². For the ACTUAL moving
interval between r0(s) and r0(t), this yields an O(R²) improvement
over the coarse radius-uniform time-Lipschitz constant, where R bounds
the two true matching radii. The exact two-variable Green difference
is integrated only over that genuine moving slit, without a synthetic
localized source or an assumed PDE decay gain.

The actual nonlocal source-time derivative majorant and original
three-Riesz integrability remain explicit analytic inputs.
This is NOT a full four-piece Hartree PDE positive-time remainder.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology Interval
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_true_moving_singular_Green_cross_Frobenius_radius_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s t B D G R E : ℝ)
    (htShort : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
      volume
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s))
    (htLong : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t))
      volume (actualHartreeSlowInnerRadius (ell s) / a s) B)
    (hsShort : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s))
    (hsLong : IntervalIntegrable
      (originGreenSourceA K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s))
      volume (actualHartreeSlowInnerRadius (ell s) / a s) B)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hBR : R ≤ scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
      ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hSliver : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      0 < x ∧ x ≤ R)
    (hSourceTime : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      ∀ τ ∈ Icc (min s t) (max s t),
        ∃ d : ℂ,
          HasDerivAt
            (fun u => actualHartreeTrueMovingAdjustedSource
              a ell c z b w Z u x) d τ ∧
          ‖d‖ ≤ E) :
    let F : ℝ → ℝ → ℂ :=
      fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ
    let r0 : ℝ → ℝ :=
      fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ
    ‖actualSingularGreenCoeff K (r0 t) (F t) B -
        actualSingularGreenCoeff K (r0 s) (F t) B -
        actualSingularGreenCoeff K (r0 t) (F s) B +
        actualSingularGreenCoeff K (r0 s) (F s) B‖ ≤
      (((1 + (D + 1) * G * R ^ 2) * R ^ 2 * E) * |t-s|) * |r0 s - r0 t| := by
  have hC : 0 ≤ 1 + (D + 1) * G * R ^ 2 := by positivity
  have hLip : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      ‖originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) x -
        originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) x‖ ≤
        (((1 + (D + 1) * G * R ^ 2) * R ^ 2 * E) * |t-s|) := by
    intro x hx
    obtain ⟨hxpos, hxR⟩ := hSliver x hx
    have hfrob :=
      actual_Hartree_original_singular_Green_density_Frobenius_quadratic_radius
        K D G R x hD hG hxpos hxR hBR hcoeff hbound
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      nlinarith [sq_nonneg (R - x)]
    have hRatio :
        ‖originPhysicalValue K.x x / originGreenWronskian K x‖ ≤
          (1 + (D + 1) * G * R ^ 2) * R ^ 2 :=
      hfrob.trans (mul_le_mul_of_nonneg_left hx2 hC)
    exact actual_Hartree_true_selected_singular_Green_density_time_MVT
      K a ell c z b w Z s t x
        ((1 + (D + 1) * G * R ^ 2) * R ^ 2) E
      hRatio (hSourceTime x hx)
  exact actual_Hartree_true_selected_moving_SingularGreen_mixed_difference
    K a ell c z b w Z s t B
      ((1 + (D + 1) * G * R ^ 2) * R ^ 2 * E)
    htShort htLong hsShort hsLong hLip

end HBL.TypeIIDynamicSelection
