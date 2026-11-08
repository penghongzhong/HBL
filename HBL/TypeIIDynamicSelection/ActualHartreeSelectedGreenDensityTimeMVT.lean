import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingAdjustedSourceDerivative
import HBL.KummerOriginGreen.GreenBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# One genuine Hartree source: a physical Green-density time Lipschitz theorem

The exact moving-Green source/endpoint cross estimate only needs the
original Wronskian density to be locally Lipschitz in time.
That is NOT inserted here as a consequence of measurability.

For one physical radius r and the actual Cramer-selected full quartic
Hartree Riesz source F(t,r), the original Green density equals
  (Y_K(r)/W_K(r)) * F(t,r).
The Wronskian multiplier is independent of time when K is frozen.
The real mean-value theorem therefore produces the required temporal
Lipschitz bound from a quantitative full source derivative along the
same physical time segment and a quantitative original Green basis
multiplier bound. This is a real reduction of the joint-time regularity
obligation to PDE source derivative estimates, not a new axiom.

The time derivative bound and basis multiplier are visible inputs; a
global original Hartree PDE producer must still supply them on the
actual moving intervals, including nonlocal Riesz cross interactions.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_true_selected_Green_density_time_MVT
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a ell c : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (b w Z : ℝ → ℂ) (s t r C D : ℝ)
    (hRatio : ‖originPhysicalValue K.y r /
      originGreenWronskian K r‖ ≤ C)
    (hFullDerivative : ∀ τ ∈ Icc (min s t) (max s t),
      ∃ d : ℂ,
        HasDerivAt
          (fun u => actualHartreeTrueMovingAdjustedSource
            a ell c z b w Z u r) d τ ∧
        ‖d‖ ≤ D) :
    ‖originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z t) r -
      originGreenSourceB K
        (actualHartreeTrueMovingAdjustedSource a ell c z b w Z s) r‖ ≤
      (C * D) * |t-s| := by
  let F : ℝ → ℂ := fun τ =>
    actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ r
  let q : ℂ := originPhysicalValue K.y r / originGreenWronskian K r
  let H : ℝ → ℂ := fun τ => F τ * q
  have hHValue (τ : ℝ) :
      originGreenSourceB K
          (actualHartreeTrueMovingAdjustedSource a ell c z b w Z τ) r =
        H τ := by
    dsimp [H, F, q, originGreenSourceB]
    ring
  have hDiff : ∀ τ ∈ Icc (min s t) (max s t),
      ∃ d : ℂ, HasDerivAt H d τ ∧ ‖d‖ ≤ C * D := by
    intro τ hτ
    obtain ⟨d, hd, hD⟩ := hFullDerivative τ hτ
    have hdH : HasDerivAt H (d * q) τ := by
      exact hd.mul_const q
    have hDpos : 0 ≤ D := (norm_nonneg d).trans hD
    have hNorm : ‖d * q‖ ≤ C * D := by
      calc
        ‖d * q‖ = ‖d‖ * ‖q‖ := norm_mul _ _
        _ ≤ D * C := by
          have hq : ‖q‖ ≤ C := hRatio
          exact mul_le_mul hD hq (norm_nonneg _) hDpos
        _ = C * D := by ring
    exact ⟨d * q, hdH, hNorm⟩
  have hHdiff : ∀ τ ∈ Icc (min s t) (max s t),
      DifferentiableAt ℝ H τ := by
    intro τ hτ
    obtain ⟨d, hd, _⟩ := hDiff τ hτ
    exact hd.differentiableAt
  have hHbound : ∀ τ ∈ Icc (min s t) (max s t),
      ‖deriv H τ‖ ≤ C * D := by
    intro τ hτ
    obtain ⟨d, hd, hdBound⟩ := hDiff τ hτ
    simpa only [hd.deriv] using hdBound
  have hs : s ∈ Icc (min s t) (max s t) :=
    ⟨min_le_left _ _, le_max_left _ _⟩
  have ht : t ∈ Icc (min s t) (max s t) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  have hMVT :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hHdiff hHbound (convex_Icc _ _) hs ht
  rw [hHValue t, hHValue s]
  simpa only [Real.norm_eq_abs] using hMVT

end HBL.TypeIIDynamicSelection
