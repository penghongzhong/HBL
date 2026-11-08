import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import Mathlib.Tactic

/-!
# The actual real-speed regular Kummer Green moment at every radius

The source modes for the *original* two real modulation speeds have
‖P_j(r)‖ ≤ C a/r, not the coarse inverse-square envelope.
The already verified original Wronskian theorem bounds both lower
Green source moments on an interval ending at B by C G a B.
Applying that SAME theorem with its upper endpoint set to each
intermediate radius r proves the bound simultaneously for every
r in [L/a,B], with the SAME C and no shrinking-left-radius loss.

The result is a real source estimate, not an assumed regular-channel
bound. The unique Cramer-selected p_j, its original Hartree source
and the four-region PDE recursion are separate steps still to be joined.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Uniform-in-radius actual scale and phase source regular Green moments,
using the existing strict original Wronskian endpoint theorem with a
variable upper endpoint. A single source constant works on the whole
moving Kummer annulus. -/
theorem actual_Hartree_speed_regular_Green_coefficients_all_radii :
    ∃ C : ℝ, 0 < C ∧
      ∀ {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
        (G L c a B : ℝ),
        0 ≤ G → 1 ≤ L → 0 < a → B ≤ 1 → B < scale →
        a * |c| ≤ 1 →
        (∀ x ∈ Icc 0 scale,
          ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
          ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G) →
        ∀ r ∈ Icc (L / a) B,
          ‖originGreenCoeffB K (L / a)
              (actualMomentLockedScaledScaleSource a c) r‖ ≤
            C * G * a * B ∧
          ‖originGreenCoeffB K (L / a)
              (actualMomentLockedScaledPhaseSource a c) r‖ ≤
            C * G * a * B := by
  obtain ⟨C, hC, hOriginal⟩ :=
    actual_Hartree_speed_regular_Green_coefficients
  refine ⟨C, hC, ?_⟩
  intro mu theta scale K G L c a B hG hL ha hB hBR hc hbound
  intro r hr
  have hrOne : r ≤ 1 := hr.2.trans hB
  have hrScale : r < scale := hr.2.trans_lt hBR
  have hAtR :=
    hOriginal K G L c a r hG hL ha hrOne hrScale hc hr.1 hbound
  have hNonneg : 0 ≤ C * G * a := by positivity
  have hInterval :
      C * G * a * r ≤ C * G * a * B :=
    mul_le_mul_of_nonneg_left hr.2 hNonneg
  exact ⟨hAtR.1.trans hInterval, hAtR.2.trans hInterval⟩

end HBL.TypeIIDynamicSelection
