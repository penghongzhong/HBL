import HBL.TypeIIDynamicSelection.ActualHartreeTrueSingularGreenFrobeniusMovingCross
import Mathlib.Tactic

/-!
# Physical Hartree moving singular Green cross from inverse-radius source time

The original true nonlocal quartic Hartree source is NOT replaced.
The actual outgoing Green density has the exact Frobenius O(r^2)
multiplier; for a source differentiated at one inverse radius, the
source-density derivative retains a FULL O(r) positive power.

This explicitly removes the possible hidden loss from the moving
lower endpoint and isolates the primitive weighted source condition
r * norm(d_t F_adj) <= E, which must be derived from the genuine
Cramer and physical Riesz source derivative budgets. It is not an
assumed positive TIME-order and is not the complete PDE residual.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology Interval
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- True original moving Hartree Green cross gains one power of the
moving radius if the differentiated ORIGINAL selected source loses
at most one inverse radius, rather than two. The only source function
is the real-Cramer-selected physical quartic Hartree forcing. -/
theorem actual_Hartree_true_moving_singular_Green_cross_Frobenius_one_inverse_radius
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
    (hSourceTimeWeighted : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      ∀ τ ∈ Icc (min s t) (max s t),
        ∃ d : ℂ,
          HasDerivAt
            (fun u => actualHartreeTrueMovingAdjustedSource
              a ell c z b w Z u x) d τ ∧
          x * ‖d‖ ≤ E) :
    let F : ℝ → ℝ → ℂ :=
      fun τ => actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ
    let r0 : ℝ → ℝ :=
      fun τ => actualHartreeSlowInnerRadius (ell τ) / a τ
    ‖actualSingularGreenCoeff K (r0 t) (F t) B -
        actualSingularGreenCoeff K (r0 s) (F t) B -
        actualSingularGreenCoeff K (r0 t) (F s) B +
        actualSingularGreenCoeff K (r0 s) (F s) B‖ ≤
      (((1 + (D + 1) * G * R ^ 2) * R * E) * |t-s|) * |r0 s - r0 t| := by
  have hC : 0 ≤ 1 + (D + 1) * G * R ^ 2 := by positivity
  have hLip : ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
      ‖originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) x -
        originGreenSourceA K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) x‖ ≤
        (((1 + (D + 1) * G * R ^ 2) * R * E) * |t-s|) := by
    intro x hx
    obtain ⟨hxpos, hxR⟩ := hSliver x hx
    have hfrob :=
      actual_Hartree_original_singular_Green_density_Frobenius_quadratic_radius
        K D G R x hD hG hxpos hxR hBR hcoeff hbound
    have hTimeS : s ∈ Icc (min s t) (max s t) :=
      ⟨min_le_left _ _, le_max_left _ _⟩
    obtain ⟨ds, _, hds⟩ := hSourceTimeWeighted x hx s hTimeS
    have hE : 0 ≤ E :=
      (mul_nonneg hxpos.le (norm_nonneg ds)).trans hds
    have hSourceTime : ∀ τ ∈ Icc (min s t) (max s t),
        ∃ d : ℂ,
          HasDerivAt
            (fun u => actualHartreeTrueMovingAdjustedSource a ell c z b w Z u x)
            d τ ∧ ‖d‖ ≤ E / x := by
      intro τ hτ
      obtain ⟨d, hd, hxd⟩ := hSourceTimeWeighted x hx τ hτ
      refine ⟨d, hd, ?_⟩
      exact (le_div_iff₀ hxpos).2 (by simpa only [mul_comm] using hxd)
    have hMVT :=
      actual_Hartree_true_selected_singular_Green_density_time_MVT
        K a ell c z b w Z s t x
        ((1 + (D + 1) * G * R ^ 2) * x ^ 2) (E / x)
        hfrob hSourceTime
    have hCancel :
        ((1 + (D + 1) * G * R ^ 2) * x ^ 2) * (E / x) =
          (1 + (D + 1) * G * R ^ 2) * x * E := by
      field_simp [hxpos.ne']
      ring
    have hXProd :
        ((1 + (D + 1) * G * R ^ 2) * x ^ 2) * (E / x) ≤
          (1 + (D + 1) * G * R ^ 2) * R * E := by
      rw [hCancel]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxR hC) hE
    calc
      _ ≤
        (((1 + (D + 1) * G * R ^ 2) * x ^ 2) * (E / x)) *
          |t-s| := hMVT
      _ ≤
        (((1 + (D + 1) * G * R ^ 2) * R * E) * |t-s|) :=
        mul_le_mul_of_nonneg_right hXProd (abs_nonneg _)
  exact actual_Hartree_true_selected_moving_SingularGreen_mixed_difference
    K a ell c z b w Z s t B
      ((1 + (D + 1) * G * R ^ 2) * R * E)
    htShort htLong hsShort hsLong hLip

end HBL.TypeIIDynamicSelection
