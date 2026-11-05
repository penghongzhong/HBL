import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCorrectionResidual
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalOneLayerGain
import Mathlib.Tactic

/-!
# The actual speed-cross terms gain one physical layer

The exact moment-locked correction residual contains
  I*delta_b*Lambda H + delta_omega*H.
If the selected speed and the correction field/dilation are both of current
order s^(-rho), this genuine PDE term is quadratic and therefore has order
s^(-2 rho).  Once rho is at least the physical profile gain, it belongs to
the next residual layer.

No generated-order label proves the estimate.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

theorem actual_Hartree_speed_cross_quadratic_time_order
    (H : ℝ → ℝ → ℂ)
    (db domega s r rho Cspeed CHd CH : ℝ)
    (hs : 1 ≤ s) (_hrho : 0 ≤ rho)
    (hCs : 0 ≤ Cspeed) (_hCHd : 0 ≤ CHd) (_hCH : 0 ≤ CH)
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hH : ‖H s r‖ ≤ CH * s ^ (-rho)) :
    ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
        (domega : ℂ) * H s r‖ ≤
      (Cspeed * (CHd + CH)) * s ^ (-2 * rho) := by
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hp0 : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  have hdb : |db| ≤ Cspeed * s ^ (-rho) :=
    le_trans (le_add_of_nonneg_right (abs_nonneg domega)) hSpeed
  have hdw : |domega| ≤ Cspeed * s ^ (-rho) :=
    le_trans (le_add_of_nonneg_left (abs_nonneg db)) hSpeed
  have hfirst :
      ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r‖ ≤
        (Cspeed * CHd) * (s ^ (-rho)) ^ 2 := by
    simp only [norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      |db| * ‖complexRadialDilation (H s) r‖ ≤
          (Cspeed * s ^ (-rho)) * (CHd * s ^ (-rho)) :=
        mul_le_mul hdb hDilation (norm_nonneg _) (mul_nonneg hCs hp0)
      _ = (Cspeed * CHd) * (s ^ (-rho)) ^ 2 := by ring
  have hsecond :
      ‖(domega : ℂ) * H s r‖ ≤
        (Cspeed * CH) * (s ^ (-rho)) ^ 2 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |domega| * ‖H s r‖ ≤
          (Cspeed * s ^ (-rho)) * (CH * s ^ (-rho)) :=
        mul_le_mul hdw hH (norm_nonneg _) (mul_nonneg hCs hp0)
      _ = (Cspeed * CH) * (s ^ (-rho)) ^ 2 := by ring
  have hp :
      (s ^ (-rho)) ^ 2 = s ^ (-2 * rho) := by
    rw [← Real.rpow_mul_natCast hs0 (-rho) 2]
    congr 1
    ring
  calc
    _ ≤ ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r‖ +
        ‖(domega : ℂ) * H s r‖ := norm_add_le _ _
    _ ≤ (Cspeed * CHd) * (s ^ (-rho)) ^ 2 +
        (Cspeed * CH) * (s ^ (-rho)) ^ 2 :=
      add_le_add hfirst hsecond
    _ = (Cspeed * (CHd + CH)) * s ^ (-2 * rho) := by
      rw [hp]
      ring

theorem actual_Hartree_speed_cross_next_physical_layer
    (H : ℝ → ℝ → ℂ)
    (db domega s r beta rhoStar rho Cspeed CHd CH : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hH : ‖H s r‖ ≤ CH * s ^ (-rho)) :
    ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
        (domega : ℂ) * H s r‖ ≤
      (Cspeed * (CHd + CH)) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
  have hkpos := actual_Hartree_physical_kappa_positive
    beta rhoStar hbeta hrhoStar hflat
  have hrho0 : 0 ≤ rho := le_trans hkpos.le hrho
  have hraw := actual_Hartree_speed_cross_quadratic_time_order
    H db domega s r rho Cspeed CHd CH hs hrho0
      hCs hCHd hCH hSpeed hDilation hH
  have hexp : -2 * rho ≤
      -(rho + actualHartreePhysicalKappa beta rhoStar) := by
    linarith
  have hp :
      s ^ (-2 * rho) ≤
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) :=
    Real.rpow_le_rpow_of_exponent_le hs hexp
  have hc : 0 ≤ Cspeed * (CHd + CH) := by positivity
  exact hraw.trans (mul_le_mul_of_nonneg_left hp hc)

end HBL.TypeIIDynamicSelection
