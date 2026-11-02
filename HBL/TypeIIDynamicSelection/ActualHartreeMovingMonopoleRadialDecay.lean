import HBL.TypeIIDynamicSelection.ActualOneOrbitMovingMonopoleMixed
import HBL.MonopoleMovingCutoffDerivative
import HBL.MonopoleRadialBound
import Mathlib.Tactic

/-!
# Revised 2.13: genuine moving monopole obeys a global radial 1/r bound

The actual physical profile is
  V_c(r) = W(r) + c(1 - chi(|c|r/4)) Phi_mon(r).
The cutoff becomes exactly one when |c|r/4 >= 2, so
the monopole correction vanishes whenever |c|r >= 8.
On the remaining region, r|c| <= 8 and the strictly constructed
Fredholm monopole profile is uniformly bounded.

Thus sup_{r>0} r|V_c(r)| <= 1 + 8 C_mon,
UNIFORMLY in the actual time-dependent coefficient c, including c=0.
This important physical spatial decay estimate is NOT an assumed
radiation scattering rate or an abstract generated-term weight.
It is an ingredient for the missing complete mixed-quartic weighted
Fredholm source bound, not a certificate for revised 2.13 itself.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The exact physical moving-cutoff monopole satisfies a uniform
radial 1/r envelope, for ANY real moment-selected amplitude c.
The amplitude c may depend on the actual Hartree PDE time and scale. -/
theorem actual_Hartree_moving_monopole_global_radial_decay
    (c r : ℝ) (hr : 0 < r) :
    r * |monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c r| ≤
        1 + 8 * monopoleRadialBoundConstant := by
  let chi : ℝ := cutoff (|c| * r / 4)
  have hchi0 : 0 ≤ chi := by
    dsimp [chi, cutoff]
    exact Real.smoothTransition.nonneg _
  have hchi1 : chi ≤ 1 := by
    dsimp [chi, cutoff]
    exact Real.smoothTransition.le_one _
  have hphi : |monopoleRadialProfile r| ≤ monopoleRadialBoundConstant :=
    monopoleRadialProfile_abs_le hr
  have hbubble0 : 0 ≤ bubble r := by
    unfold bubble
    positivity
  have hbubble : bubble r ≤ 1 / r :=
    actual_one_orbit_bubble_le_inverse_radius r hr
  have hrbubble : r * |bubble r| ≤ 1 := by
    rw [abs_of_nonneg hbubble0]
    calc
      r * bubble r ≤ r * (1 / r) :=
        mul_le_mul_of_nonneg_left hbubble hr.le
      _ = 1 := by field_simp [hr.ne']
  have hcutoff : r * |c| * |1 - chi| ≤ 8 := by
    by_cases hcap : |c| * r ≤ 8
    · have hnonneg : 0 ≤ r * |c| := mul_nonneg hr.le (abs_nonneg c)
      have hbound : r * |c| ≤ 8 := by
        simpa only [mul_comm] using hcap
      rw [abs_of_nonneg (sub_nonneg.mpr hchi1)]
      calc
        r * |c| * (1 - chi) ≤ (r * |c|) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hchi0]) hnonneg
        _ = r * |c| := by ring
        _ ≤ 8 := hbound
    · have hlarge : 8 < |c| * r := lt_of_not_ge hcap
      have htwo : 2 ≤ |c| * r / 4 := by linarith
      have heq : chi = 1 := by
        dsimp [chi]
        exact cutoff_one_of_two_le _ htwo
      rw [heq]
      norm_num
  rw [monopoleMovingCutoffProfile_eq]
  change r * |bubble r + c * (1 - chi) * monopoleRadialProfile r| ≤ _
  calc
    _ ≤ r * (|bubble r| + |c * (1 - chi) * monopoleRadialProfile r|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hr.le
    _ = r * |bubble r| +
          (r * |c| * |1 - chi|) * |monopoleRadialProfile r| := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ 1 + 8 * monopoleRadialBoundConstant :=
      add_le_add hrbubble
        (mul_le_mul hcutoff hphi (abs_nonneg _) (by norm_num))

/-- Direct 1/r form of the previous physically constructed envelope.
It applies uniformly to c(t,ell)=kappa_H*ell*m[z(t)]. -/
theorem actual_Hartree_moving_monopole_abs_le_inverse_radius
    (c r : ℝ) (hr : 0 < r) :
    |monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c r| ≤
        (1 + 8 * monopoleRadialBoundConstant) / r := by
  apply (le_div_iff₀ hr).2
  calc
    |monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c r| * r =
      r * |monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c r| := by ring
    _ ≤ 1 + 8 * monopoleRadialBoundConstant :=
      actual_Hartree_moving_monopole_global_radial_decay c r hr

end HBL.TypeIIDynamicSelection
