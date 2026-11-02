import HBL.KummerLocalInverse.Definitions
import Mathlib.Tactic

/-!
# Genuine Kummer normalization uses ALL homogeneous degrees of freedom

The manuscript's Kummer Green inverse uses TWO exact Wronskian boundary
normalizations. The genuine complex second-order Kummer equation has two
homogeneous modes with coefficients a,c. These normalizations force a=0
and c=0 for ANY homogeneous correction to the normalized Green solution.

Thus the independent "correct both Cauchy jets at the inner interface"
construction is valid as a local INHOMOGENEOUS IVP, but generally
breaks the original Kummer *normalized inverse*. It cannot alone
close manuscript original 2.12. The remaining overlap matching must
be achieved by actual source/parameter modulation and cutoff
commutator estimates, not by freely changing normalized Kummer
homogeneous coefficients or assuming outer Cauchy matching.

This is an exact result in the original physical normalized Kummer
basis with its nonvanishing Wronskian, and requires no substitute
regional solver, imposed gain, or blowup rate.
-/

noncomputable section
set_option autoImplicit false
open Set

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The two ACTUAL Kummer endpoint normalizations eliminate every
homogeneous complex degree of freedom of the normalized right inverse. -/
theorem actual_Kummer_both_normalized_endpoints_force_zero_homogeneous
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (a c : ℂ)
    (hRight :
      (a * K.phi d + c * K.psi d) * K.dpsi d -
        (a * K.dphi d + c * K.dpsi d) * K.psi d = 0)
    (hLeft :
      K.phi (-d) * (a * K.dphi (-d) + c * K.dpsi (-d)) -
        K.dphi (-d) * (a * K.phi (-d) + c * K.psi (-d)) = 0) :
    a = 0 ∧ c = 0 := by
  have hdmem : d ∈ Icc (-eps) eps := by
    constructor <;> linarith
  have hmdmem : -d ∈ Icc (-eps) eps := by
    constructor <;> linarith
  have hwR : localAnnulusWronskian K d ≠ 0 :=
    K.wronskian_ne d hdmem
  have hwL : localAnnulusWronskian K (-d) ≠ 0 :=
    K.wronskian_ne (-d) hmdmem
  have hA : a * localAnnulusWronskian K d = 0 := by
    calc
      a * localAnnulusWronskian K d =
          (a * K.phi d + c * K.psi d) * K.dpsi d -
            (a * K.dphi d + c * K.dpsi d) * K.psi d := by
        unfold localAnnulusWronskian
        ring
      _ = 0 := hRight
  have hC : c * localAnnulusWronskian K (-d) = 0 := by
    calc
      c * localAnnulusWronskian K (-d) =
          K.phi (-d) * (a * K.dphi (-d) + c * K.dpsi (-d)) -
            K.dphi (-d) * (a * K.phi (-d) + c * K.psi (-d)) := by
        unfold localAnnulusWronskian
        ring
      _ = 0 := hLeft
  exact ⟨(mul_eq_zero.mp hA).resolve_right hwR,
    (mul_eq_zero.mp hC).resolve_right hwL⟩

end HBL.TypeIIDynamicSelection
