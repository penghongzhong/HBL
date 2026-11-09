import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import Mathlib.Tactic

/-!
# Universal true Hartree radiation half-radial decay without ell losses

The real 3D critical scaling Z_ell(r)=sqrt(ell)*z(ell*r) does NOT
obey a uniformly weighted full-bubble bound. It DOES satisfy a
uniform half-power squared bound, exactly because 0<ell<=1:
   ell*(1+r) <= (1+ell*r)^2.
This gives the decay needed for the quartic-density Riesz remainder
times the local cubic factor in weighted Fredholm L2 spaces.
No time order, bootstrap persistence or Type-II rate is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Scalar inequality for every physical Hartree scale and radial point. -/
theorem actual_Hartree_scaled_radiation_halfpower_scalar
    (ell r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hr : 0 ≤ r) :
    (1 + r) * (Real.sqrt ell / (1 + ell * r)) ^ 2 ≤ 1 := by
  have hden : 0 < 1 + ell * r := by
    have hprod := mul_nonneg hell.le hr
    linarith
  have hq : ell * (1 + r) ≤ (1 + ell * r) ^ 2 := by
    have h0 : 0 ≤ 1 - ell := by linarith
    have h1 : 0 ≤ ell * r := mul_nonneg hell.le hr
    have h2 : 0 ≤ (ell * r) ^ 2 := sq_nonneg _
    nlinarith [h0, h1, h2]
  calc
    (1 + r) * (Real.sqrt ell / (1 + ell * r)) ^ 2 =
        ell * (1 + r) / (1 + ell * r) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hell.le]
          ring
    _ ≤ 1 := (div_le_iff₀ (pow_pos hden 2)).2 (by simpa using hq)

/-- Original critical rescaling and radial Strauss data imply
uniform half-power decay, with no full-bubble source hypothesis. -/
theorem actual_Hartree_scaled_radiation_halfpower_squared
    (ell r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hStrauss : ∀ x : ℝ, 1 ≤ x → x * ‖z x‖ ≤ A) :
    (1 + r) * ‖rescalePhysicalRadiation ell z r‖ ^ 2 ≤
      (2 * (B + A)) ^ 2 := by
  let E : ℝ := 2 * (B + A)
  have hden : 0 < 1 + ell * r := by
    have hp := mul_pos hell hr
    linarith
  have hZ :=
    actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
  have hZbound :
      ‖rescalePhysicalRadiation ell z r‖ ≤
        E * (Real.sqrt ell / (1 + ell * r)) := by
    have hd : ‖rescalePhysicalRadiation ell z r‖ ≤
        (E * Real.sqrt ell) / (1 + ell * r) := by
      apply (le_div_iff₀ hden).2
      dsimp [E]
      nlinarith [hZ]
    calc
      _ ≤ (E * Real.sqrt ell) / (1 + ell * r) := hd
      _ = E * (Real.sqrt ell / (1 + ell * r)) := by ring
  have hZ2 :
      ‖rescalePhysicalRadiation ell z r‖ ^ 2 ≤
        E ^ 2 * (Real.sqrt ell / (1 + ell * r)) ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hZbound 2
    simpa only [mul_pow] using h
  have hfactor :=
    actual_Hartree_scaled_radiation_halfpower_scalar
      ell r hell hellOne hr.le
  calc
    (1 + r) * ‖rescalePhysicalRadiation ell z r‖ ^ 2 ≤
       (1 + r) * (E ^ 2 * (Real.sqrt ell / (1 + ell * r)) ^ 2) :=
      mul_le_mul_of_nonneg_left hZ2 (by linarith)
    _ = E ^ 2 * ((1 + r) *
       (Real.sqrt ell / (1 + ell * r)) ^ 2) := by ring
    _ ≤ E ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hfactor (sq_nonneg E)
    _ = (2 * (B + A)) ^ 2 := by dsimp [E]; ring

end HBL.TypeIIDynamicSelection
