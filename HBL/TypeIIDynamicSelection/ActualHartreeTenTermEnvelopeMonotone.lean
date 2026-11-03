import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInteractionTenTermNorm
import Mathlib.Tactic

/-!
# Revised HBL 2.13 — exact ten-term interaction envelope is monotone

This is the missing algebraic link from the *actual* physical potential
magnitudes and field amplitudes to the three rigorously derived
radial/scale envelopes. Every term is positive, and all four Hartree
source products are retained.

No Type-II rate, new axiom, or artificial source order.
-/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Full ten-monomial core/mixed/radiation interaction is monotone
in all three nonlocal Riesz potential magnitudes and both field
magnitudes. This permits direct use of genuine measured source bounds. -/
theorem actual_Hartree_complete_ten_term_polynomial_mono
    (pm pz pc v z Pm Pz Pc V Z : ℝ)
    (hpm0 : 0 ≤ pm) (hpz0 : 0 ≤ pz) (hpc0 : 0 ≤ pc)
    (hv0 : 0 ≤ v) (hz0 : 0 ≤ z)
    (hpm : pm ≤ Pm) (hpz : pz ≤ Pz) (hpc : pc ≤ Pc)
    (hv : v ≤ V) (hz : z ≤ Z) :
    pm * (v ^ 3 + (2 * v + z) ^ 2 * z) +
      pz * ((v + 2 * z) ^ 2 * v) +
      pc * ((2 * v + z) ^ 2 * z) ≤
    Pm * (V ^ 3 + (2 * V + Z) ^ 2 * Z) +
      Pz * ((V + 2 * Z) ^ 2 * V) +
      Pc * ((2 * V + Z) ^ 2 * Z) := by
  have hV0 : 0 ≤ V := hv0.trans hv
  have hZ0 : 0 ≤ Z := hz0.trans hz
  have hPm0 : 0 ≤ Pm := hpm0.trans hpm
  have hPz0 : 0 ≤ Pz := hpz0.trans hpz
  have hPc0 : 0 ≤ Pc := hpc0.trans hpc
  have hv3 : v ^ 3 ≤ V ^ 3 :=
    pow_le_pow_left₀ hv0 hv 3
  have hCore : 2 * v + z ≤ 2 * V + Z := by
    linarith
  have hRad : v + 2 * z ≤ V + 2 * Z := by
    linarith
  have hCore0 : 0 ≤ 2 * v + z := by positivity
  have hRad0 : 0 ≤ v + 2 * z := by positivity
  have hCoreSq :
      (2 * v + z) ^ 2 ≤ (2 * V + Z) ^ 2 :=
    pow_le_pow_left₀ hCore0 hCore 2
  have hRadSq :
      (v + 2 * z) ^ 2 ≤ (V + 2 * Z) ^ 2 :=
    pow_le_pow_left₀ hRad0 hRad 2
  have hCoreDiff :
      (2 * v + z) ^ 2 * z ≤ (2 * V + Z) ^ 2 * Z :=
    mul_le_mul hCoreSq hz hz0 (by positivity)
  have hRadDiff :
      (v + 2 * z) ^ 2 * v ≤ (V + 2 * Z) ^ 2 * V :=
    mul_le_mul hRadSq hv hv0 (by positivity)
  have hMix :
      v ^ 3 + (2 * v + z) ^ 2 * z ≤
      V ^ 3 + (2 * V + Z) ^ 2 * Z :=
    add_le_add hv3 hCoreDiff
  have hMix0 :
      0 ≤ v ^ 3 + (2 * v + z) ^ 2 * z := by positivity
  have hRadMult0 :
      0 ≤ (v + 2 * z) ^ 2 * v := by positivity
  have hCoreMult0 :
      0 ≤ (2 * v + z) ^ 2 * z := by positivity
  have hM :
      pm * (v ^ 3 + (2 * v + z) ^ 2 * z) ≤
        Pm * (V ^ 3 + (2 * V + Z) ^ 2 * Z) :=
    mul_le_mul hpm hMix hMix0 hPm0
  have hR :
      pz * ((v + 2 * z) ^ 2 * v) ≤
        Pz * ((V + 2 * Z) ^ 2 * V) :=
    mul_le_mul hpz hRadDiff hRadMult0 hPz0
  have hC :
      pc * ((2 * v + z) ^ 2 * z) ≤
        Pc * ((2 * V + Z) ^ 2 * Z) :=
    mul_le_mul hpc hCoreDiff hCoreMult0 hPc0
  exact add_le_add (add_le_add hM hR) hC

end HBL.TypeIIDynamicSelection
