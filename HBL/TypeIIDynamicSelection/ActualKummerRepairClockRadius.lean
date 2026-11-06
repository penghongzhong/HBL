import HBL.KinematicPathBounds
import Mathlib.Tactic

/-!
# Coarse linear physical radius bound for the Kummer replacement shell

Only the exact relation a^2=q and a linear upper bound q(s)=O(s) are used.
The latter is already available from the trapped slice clock.  This is much
weaker than the final Type-II asymptotic rate and does not prescribe any
limiting modulation exponent.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

/-- If the physical Kummer scale satisfies a^2=q and the clock has a linear
upper bound, then every fixed normalized radius B<=1 pulls back to O(s). -/
theorem actual_Kummer_repair_radius_linear_from_clock
    (a B q s Cq : ℝ)
    (ha : 0 ≤ a) (hB : B ≤ 1) (hs : 1 ≤ s)
    (haq : a ^ 2 = q) (hq : q ≤ Cq * s) :
    a * B ≤ (Cq + 1) * s := by
  have hAB : a * B ≤ a := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hB)]
  have haSq : a ≤ a ^ 2 + 1 := by
    nlinarith [sq_nonneg (a - 1 / 2)]
  calc
    a * B ≤ a := hAB
    _ ≤ a ^ 2 + 1 := haSq
    _ = q + 1 := by rw [haq]
    _ ≤ Cq * s + s := by linarith
    _ = (Cq + 1) * s := by ring

/-- Specialization to the already verified trapped slice clock.  No final
rate or mu-limit occurs: only the coarse clock inequality q(s)<=2As. -/
theorem actual_Kummer_repair_radius_linear_from_slice_clock
    {A s0 kappa delta H s a B : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs0 : 0 < s0)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, s0 ≤ t → |h t| ≤ H * t ^ (-delta))
    (hsmall : (4 * H / (1 - delta)) * s0 ^ (-delta) ≤ A / 4)
    (hkappa : |kappa| ≤ A * s0 / 4)
    (hs : s0 ≤ s) (hs1 : 1 ≤ s)
    (ha : 0 ≤ a) (hB : B ≤ 1)
    (haq : a ^ 2 = HBL.Kinematic.sliceClock A s0 kappa h s) :
    a * B ≤ (2 * A + 1) * s := by
  have hq :=
    (HBL.Kinematic.sliceClock_linear_bounds h hA hs0 hdelta hdelta1
      hH hbound hsmall hkappa hs).2
  exact actual_Kummer_repair_radius_linear_from_clock
    a B (HBL.Kinematic.sliceClock A s0 kappa h s) s (2 * A)
    ha hB hs1 haq hq

end HBL.TypeIIDynamicSelection
