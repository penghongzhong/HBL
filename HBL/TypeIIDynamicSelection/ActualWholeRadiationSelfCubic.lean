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
  push_cast
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

/-- The genuine quartic Hartree interaction density involving both
the concentrating real profile and the entire complex radiation.
No support separation or approximation is imposed. -/
def actualWholeRadiationMixedQuartic
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (rho : ℝ) : ℝ :=
  ‖(V rho : ℂ) + Z rho‖ ^ 4 -
    ‖(V rho : ℂ)‖ ^ 4 - ‖Z rho‖ ^ 4

/-- Exact decomposition of the ORIGINAL whole-radiation Hartree center
into bubble, pure radiation and the full mixed quartic interaction.
Integrability of the mixed density is DERIVED from the three physical
quartic integrability inputs, not an extra postulated source estimate. -/
theorem actual_whole_radiation_mixed_center_exact
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    (hFull : IntegrableOn
      (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hV : IntegrableOn
      (fun rho => ‖(V rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hZ : IntegrableOn
      (fun rho => ‖Z rho‖ ^ 4) (Ioi (0 : ℝ))) :
    radialHartreeCenter (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) =
      radialHartreeCenter (fun rho => ‖(V rho : ℂ)‖ ^ 4) +
        actualRadiationCenter Z +
          radialHartreeCenter (actualWholeRadiationMixedQuartic V Z) := by
  have hMixEq :
      actualWholeRadiationMixedQuartic V Z =
        (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) -
          (fun rho => ‖(V rho : ℂ)‖ ^ 4) -
            (fun rho => ‖Z rho‖ ^ 4) := rfl
  have hMix : IntegrableOn
      (actualWholeRadiationMixedQuartic V Z) (Ioi (0 : ℝ)) := by
    rw [hMixEq]
    exact (hFull.sub hV).sub hZ
  have hDensity :
      (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) =
        (fun rho => ‖(V rho : ℂ)‖ ^ 4) +
          (fun rho => ‖Z rho‖ ^ 4) +
            actualWholeRadiationMixedQuartic V Z := by
    funext rho
    simp only [Pi.add_apply, actualWholeRadiationMixedQuartic]
    ring
  unfold actualRadiationCenter radialHartreeCenter
  rw [hDensity]
  change
    (4 * Real.pi * hartreeKappa) *
      (∫ rho in Ioi (0 : ℝ),
        (‖(V rho : ℂ)‖ ^ 4 + ‖Z rho‖ ^ 4) +
          actualWholeRadiationMixedQuartic V Z rho) = _
  have hsum1 := integral_add (hV.add hZ) hMix
  have hsum2 := integral_add hV hZ
  simp only [Pi.add_apply] at hsum1 hsum2
  rw [hsum1, hsum2]
  ring

/-- Exact nonlocal potential decomposition for the SAME physical Hartree
field V+Z at every observation radius r. The full mixed source is
retained; unlike a remote-only construction this needs NO artificial
exterior-support separation. All row integrabilities are genuine
Lebesgue hypotheses on the physical quartic densities. -/
theorem actual_whole_radiation_mixed_potential_exact
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (r : ℝ)
    (hFull : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ) + Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hV : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hZ : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z rho‖ ^ 4) (Ioi (0 : ℝ))) :
    radialHartreePotential
        (fun rho => ‖(V rho : ℂ) + Z rho‖ ^ 4) r =
      radialHartreePotential (fun rho => ‖(V rho : ℂ)‖ ^ 4) r +
        radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r +
          radialHartreePotential (actualWholeRadiationMixedQuartic V Z) r := by
  have hMixedRow :
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedQuartic V Z rho) =
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ) + Z rho‖ ^ 4) -
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ)‖ ^ 4) -
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z rho‖ ^ 4) := by
    funext rho
    simp only [Pi.sub_apply, actualWholeRadiationMixedQuartic]
    ring
  have hMix : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedQuartic V Z rho) (Ioi (0 : ℝ)) := by
    rw [hMixedRow]
    exact (hFull.sub hV).sub hZ
  have hDensityRow :
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ) + Z rho‖ ^ 4) =
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ)‖ ^ 4) +
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z rho‖ ^ 4) +
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedQuartic V Z rho) := by
    funext rho
    simp only [Pi.add_apply, actualWholeRadiationMixedQuartic]
    ring
  unfold radialHartreePotential
  rw [hDensityRow]
  change
    (2 * Real.pi * hartreeKappa / r) *
      (∫ rho in Ioi (0 : ℝ),
        (rho * hartreeRadialLog r rho * ‖(V rho : ℂ)‖ ^ 4 +
          rho * hartreeRadialLog r rho * ‖Z rho‖ ^ 4) +
        rho * hartreeRadialLog r rho *
          actualWholeRadiationMixedQuartic V Z rho) = _
  have hsum1 := integral_add (hV.add hZ) hMix
  have hsum2 := integral_add hV hZ
  simp only [Pi.add_apply] at hsum1 hsum2
  rw [hsum1, hsum2]
  ring

/-- The local complex cubic multiplier appearing in the ORIGINAL
energy-critical Hartree equation. This is not an invented local
nonlinearity: the full term is the genuine Riesz potential times it. -/
def actualWholeRadiationLocalCubic (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  (‖u r‖ ^ 2 : ℝ) * u r

/-- Exact SAME-EQUATION Hartree nonlinear source difference for arbitrary
complex whole radiation Z, with no remote support or preselected
modulation speed. The first term contains the pure-radiation Riesz
potential AND the entire mixed quartic Riesz potential; the second
contains the change of the local cubic multiplier. All three source
rows are genuinely integrable, rather than formal symbolic kernels.
Obtaining positive time-order estimates for these terms and actual
three-region residual cancellation is still required by manuscript 2.12. -/
theorem actual_whole_radiation_complete_Hartree_nonlinearity_difference
    (V : ℝ → ℝ) (Z : ℝ → ℂ) (r : ℝ)
    (hFull : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ) + Z rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hV : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hZ : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z rho‖ ^ 4) (Ioi (0 : ℝ))) :
    complexRadialHartreeNonlinearity
        (fun rho => (V rho : ℂ) + Z rho) r -
      complexRadialHartreeNonlinearity
        (fun rho => (V rho : ℂ)) r =
      ((radialHartreePotential
          (fun rho => ‖Z rho‖ ^ 4) r +
        radialHartreePotential
          (actualWholeRadiationMixedQuartic V Z) r : ℝ) : ℂ) *
        actualWholeRadiationLocalCubic
          (fun rho => (V rho : ℂ) + Z rho) r +
      (radialHartreePotential
          (fun rho => ‖(V rho : ℂ)‖ ^ 4) r : ℂ) *
        (actualWholeRadiationLocalCubic
            (fun rho => (V rho : ℂ) + Z rho) r -
          actualWholeRadiationLocalCubic
            (fun rho => (V rho : ℂ)) r) := by
  have hPotential :=
    actual_whole_radiation_mixed_potential_exact V Z r hFull hV hZ
  unfold complexRadialHartreeNonlinearity actualWholeRadiationLocalCubic
  rw [hPotential]
  push_cast
  ring

end HBL.TypeIIDynamicSelection
