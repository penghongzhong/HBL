import HBL.TypeIIDynamicSelection.ActualRadiationCenter
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Physical slow monopole cubic from the WHOLE radial radiation

This compares the first monopole effective source to the actual quartic
self-potential of the entire complex regular radiation. Unlike
the remote-support exploratory bridge, it matches the c_g definition
used in the original Hartree manuscript without a spatial support
assumption or a prescribed asymptotic rate.

The identity covers the pure radiation self-density contribution to
the physical Hartree source, NOT all mixed bubble-radiation cross
terms or an exact nonlinear PDE trajectory. Those additional terms
must be included in the full original one-layer proposition 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual physical quartic self-radiation potential, not a local
ad hoc cubic, in the complex renormalized Hartree source. -/
def actualWholeRadiationSelfCubicIncrement
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
    (fun t x => (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c t)) (c t) x : ℂ))
    (b s) (omega s) s r +
  (radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r : ℂ) *
    (monopolePerturbedRadialProfile
      (monopoleQuadraticRadius (c s)) (c s) r : ℂ) ^ 3 -
  complexRadialRenormalizedResidual
    (fun _ x => (bubble x : ℂ)) (b s) (omega s) s r

/-- The formerly inserted effective c(s)*V^3 is exactly the genuine
radiation self-potential at radius r, plus the displayed scalar
physical center discrepancy; no unsupported exterior-mass equation. -/
theorem actual_whole_radiation_self_cubic_exact
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (s r : ℝ) :
    monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      actualWholeRadiationSelfCubicIncrement c b omega Z s r =
    ((c s - radialHartreePotential
      (fun rho => ‖Z s rho‖ ^ 4) r : ℝ) : ℂ) *
      (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s) r : ℂ) ^ 3 := by
  unfold monopoleComplexEffectiveIncrement
    actualWholeRadiationSelfCubicIncrement
  ring

/-- For the ACTUAL slow coefficient c_g supplied by whole radiation,
the physical source correction is O(r^2) in the bubble core. It holds
without an exterior-support condition, including zero amplitude. -/
theorem actual_whole_radiation_self_cubic_core_bound
    (c b omega : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r M D : ℝ}
    (hZ : Measurable (Z s)) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z s rho‖ ≤ M)
    (hmass : IntegrableOn (fun rho => rho ^ 2 * ‖Z s rho‖ ^ 2) (Ioi 0))
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 →
      ‖Z s rho - Z s 0‖ ≤ D * rho ^ 2)
    (hcenter : c s = actualRadiationCenter (Z s))
    (hc : |c s| ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖monopoleComplexEffectiveIncrement c (b s) (omega s) s r -
      actualWholeRadiationSelfCubicIncrement c b omega Z s r‖ ≤
    (radialHartreeCenterBoundConstant
      (fun rho => ‖Z s rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2) *
        (1 + monopoleRadialBoundConstant) ^ 3 := by
  rw [actual_whole_radiation_self_cubic_exact]
  have hp := actual_radiation_center_quadratic_bound
    (Z s) hZ hM hD hbound hmass hflat hr hr1
  have hpe : |c s - radialHartreePotential
        (fun rho => ‖Z s rho‖ ^ 4) r| ≤
      radialHartreeCenterBoundConstant
        (fun rho => ‖Z s rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2 := by
    rw [hcenter, abs_sub_comm]
    exact hp
  have hv := monopolePerturbedRadialProfile_abs_le
    (R := monopoleQuadraticRadius (c s)) hr hc
  have hpow :
      |monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c s)) (c s) r| ^ 3 ≤
          (1 + monopoleRadialBoundConstant) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hv 3
  have hC : 0 ≤ radialHartreeCenterBoundConstant
      (fun rho => ‖Z s rho‖ ^ 4) (4 * M ^ 3 * D) * r ^ 2 :=
    (abs_nonneg _).trans hpe
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul hpe hpow (by positivity) hC

end HBL.TypeIIDynamicSelection
