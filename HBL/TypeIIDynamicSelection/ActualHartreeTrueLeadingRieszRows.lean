import HBL.TypeIIDynamicSelection.ActualHartreeHalfRadialOriginalRieszLinear
import HBL.TypeIIDynamicSelection.ActualHartreeTrueQuadraticRieszCubicFiveWeight
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import Mathlib.Tactic

/-!
# Physical original 3D Hartree leading and linear-density Riesz rows

The original physical profile U(r)=Vc(r)+sqrt(ell)*z(ell*r) supplies
the full two-scale half-radial bound K and L-infinity amplitude M.
It therefore generates the TWO original inverse-square Riesz potentials:
P0=I[|U|^4], P1=I[4|U|^2 Re(conj(U)H)],
with exact 1/(1+r) decay. No independent source envelope,
Kummer speed, time rate or background single-bubble bound is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_true_monopole_radiation_leading_two_Riesz_rows
    (ell c B A e : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) (hA : 0 ≤ A) (he : 0 ≤ e)
    (z H : ℝ → ℂ)
    (hz : Measurable z) (hHmeas : Measurable H)
    (hSup : ∀ x : ℝ, 0 < x → ‖z x‖ ≤ B)
    (hStrauss : ∀ x : ℝ, 1 ≤ x → x*‖z x‖ ≤ A)
    (hH : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e*bubble x)
    (r : ℝ) (hr : 0 < r) :
    let U : ℝ → ℂ := fun x =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c x : ℂ)+
        rescalePhysicalRadiation ell z x
    let M : ℝ := 1+monopoleRadialBoundConstant+B
    let D : ℝ := 2+9*monopoleRadialBoundConstant
    let E : ℝ := 2*(B+A)
    let K : ℝ := 2*(D^2+E^2)
    (IntegrableOn (fun x => x*hartreeRadialLog r x*‖U x‖^4)
      (Ioi (0:ℝ)) ∧
     |radialHartreePotential (fun x => ‖U x‖^4) r| ≤
       K^2*actualHartreeBubbleSquaredRieszDecayConstant/(1+r)) ∧
    (IntegrableOn (fun x => x*hartreeRadialLog r x*
       actualHartreeComplexDensityLinear (U x) (H x))
      (Ioi (0:ℝ)) ∧
     |radialHartreePotential
       (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r| ≤
       (8*M*K*e)*actualHartreeBubbleSquaredRieszDecayConstant/(1+r)) := by
  dsimp only
  let U : ℝ → ℂ := fun x =>
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c x : ℂ)+
        rescalePhysicalRadiation ell z x
  let M : ℝ := 1+monopoleRadialBoundConstant+B
  let D : ℝ := 2+9*monopoleRadialBoundConstant
  let E : ℝ := 2*(B+A)
  let K : ℝ := 2*(D^2+E^2)
  have hM : 0 ≤ M := by
    dsimp [M]
    have := monopoleRadialBoundConstant_pos
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hVmeas := actual_Hartree_moving_monopole_measurable c
  have hUmeas : Measurable U := by
    dsimp [U,rescalePhysicalRadiation]
    fun_prop
  have hSqrt : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg ell
  have hSqrtOne : Real.sqrt ell ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hUbound (x : ℝ) (hx : 0 < x) : ‖U x‖ ≤ M := by
    have hVbound :
       ‖(monopolePerturbedRadialProfile
           (monopoleQuadraticRadius c) c x : ℂ)‖ ≤
         1+monopoleRadialBoundConstant := by
       simpa only [Complex.norm_real,Real.norm_eq_abs] using
         (monopolePerturbedRadialProfile_abs_le
           (R := monopoleQuadraticRadius c) hx hc)
    have hZbound : ‖rescalePhysicalRadiation ell z x‖ ≤ B := by
      have hnorm :
          ‖rescalePhysicalRadiation ell z x‖ =
            Real.sqrt ell*‖z (ell*x)‖ := by
        unfold rescalePhysicalRadiation
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg hSqrt]
      calc
        _ = Real.sqrt ell*‖z (ell*x)‖ := hnorm
        _ ≤ Real.sqrt ell*B :=
          mul_le_mul_of_nonneg_left
            (hSup (ell*x) (mul_pos hell hx)) hSqrt
        _ ≤ 1*B := mul_le_mul_of_nonneg_right hSqrtOne hB
        _ = B := one_mul B
    calc
      ‖U x‖ ≤
        ‖(monopolePerturbedRadialProfile
            (monopoleQuadraticRadius c) c x : ℂ)‖+
        ‖rescalePhysicalRadiation ell z x‖ := norm_add_le _ _
      _ ≤ (1+monopoleRadialBoundConstant)+B :=
        add_le_add hVbound hZbound
      _ = M := rfl
  have hHalf (x : ℝ) (hx : 0 < x) :
      (1+x)*‖U x‖^2 ≤ K := by
    simpa only [K,D,E,U] using
      actual_Hartree_true_two_scale_background_half_radial_square
        ell c x B A hell hellOne hx hc hB hA z hSup hStrauss
  have hRows :=
    actual_Hartree_half_radial_background_and_linear_Riesz_decay
      U H hUmeas hHmeas M K e hM hK he
      hUbound hHalf hH r hr
  simpa only [U,M,D,E,K] using hRows

end HBL.TypeIIDynamicSelection
