import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import HBL.MonopoleComplexResidual
import Mathlib.Tactic

/-!
# Original manuscript 2.12: actual whole-radiation renormalized PDE residual

No abstract RegionalSolver, ThresholdSolver or assigned source orders appear.
For a genuine time-dependent real radial background V(s,r) and a complex
whole radiation Z(s,r), identify EVERY term of the ORIGINAL renormalized
Hartree residual, including time derivatives, both spatial derivatives,
scaling, phase, and all the true nonlocal quartic interactions.

This removes the purely formal 'tangent=tangent' shortcut from the
PHYSICAL SOURCE IDENTIFICATION. The regional Fredholm/Kummer/remote
corrections, their moving cutoffs, parameter-tangent projection and
positive-order generated terms still have to be constructed to close
the FULL original 2.12. This theorem does not prove that final claim.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The complete true Hartree PDE residual split for a time-dependent
real core and entire complex radiation, without remote-support
assumptions or prescribed scaling dynamics. The only analytic inputs
are the genuine local differentiability and Riesz-row integrability. -/
theorem actual_one_layer_full_renormalized_Hartree_PDE_source
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hVTime : DifferentiableAt ℝ (fun t : ℝ => (V t r : ℂ)) s)
    (hZTime : DifferentiableAt ℝ (fun t : ℝ => Z t r) s)
    (hVSpace : ∀ x : ℝ,
      DifferentiableAt ℝ (fun y : ℝ => (V s y : ℂ)) x)
    (hZSpace : ∀ x : ℝ, DifferentiableAt ℝ (Z s) x)
    (hVSecond : DifferentiableAt ℝ
      (deriv (fun y : ℝ => (V s y : ℂ))) r)
    (hZSecond : DifferentiableAt ℝ (deriv (Z s)) r)
    (hFullRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ) + Z s rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hCoreRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖(V s rho : ℂ)‖ ^ 4) (Ioi (0 : ℝ)))
    (hRadiationRow : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        ‖Z s rho‖ ^ 4) (Ioi (0 : ℝ))) :
    complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ) + Z t x) b omega s r -
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ)) b omega s r =
      Complex.I * deriv (fun t : ℝ => Z t r) s +
        complexRadialLaplacian (Z s) r +
        Complex.I * (b : ℂ) * complexRadialDilation (Z s) r +
        (omega : ℂ) * Z s r +
        ((radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r +
          radialHartreePotential
            (actualWholeRadiationMixedQuartic (V s) (Z s)) r : ℝ) : ℂ) *
          actualWholeRadiationLocalCubic
            (fun rho => (V s rho : ℂ) + Z s rho) r +
        (radialHartreePotential
          (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r : ℂ) *
          (actualWholeRadiationLocalCubic
              (fun rho => (V s rho : ℂ) + Z s rho) r -
            actualWholeRadiationLocalCubic
              (fun rho => (V s rho : ℂ)) r) := by
  let v : ℝ → ℂ := fun x => (V s x : ℂ)
  let z : ℝ → ℂ := Z s
  have hTime :
      deriv (fun t : ℝ => (V t r : ℂ) + Z t r) s =
        deriv (fun t : ℝ => (V t r : ℂ)) s +
          deriv (fun t : ℝ => Z t r) s :=
    (hVTime.hasDerivAt.add hZTime.hasDerivAt).deriv
  have hFirst : ∀ x : ℝ,
      deriv (fun y : ℝ => v y + z y) x =
        deriv v x + deriv z x := by
    intro x
    exact ((hVSpace x).hasDerivAt.add (hZSpace x).hasDerivAt).deriv
  have hFirstEq :
      deriv (fun y : ℝ => v y + z y) =
        fun x => deriv v x + deriv z x := funext hFirst
  have hSecond :
      deriv (deriv (fun y : ℝ => v y + z y)) r =
        deriv (deriv v) r + deriv (deriv z) r := by
    rw [hFirstEq]
    exact (hVSecond.hasDerivAt.add hZSecond.hasDerivAt).deriv
  have hLap :
      complexRadialLaplacian (fun x => v x + z x) r =
        complexRadialLaplacian v r +
          complexRadialLaplacian z r := by
    unfold complexRadialLaplacian
    rw [hSecond, hFirst r]
    ring
  have hScale :
      complexRadialDilation (fun x => v x + z x) r =
        complexRadialDilation v r +
          complexRadialDilation z r := by
    unfold complexRadialDilation
    rw [hFirst r]
    ring
  have hNL :=
    actual_whole_radiation_complete_Hartree_nonlinearity_difference
      (V s) (Z s) r hFullRow hCoreRow hRadiationRow
  change
    Complex.I * deriv (fun t : ℝ => (V t r : ℂ) + Z t r) s +
        complexRadialLaplacian (fun x => v x + z x) r +
        complexRadialHartreeNonlinearity (fun x => v x + z x) r +
        Complex.I * (b : ℂ) *
          complexRadialDilation (fun x => v x + z x) r +
        (omega : ℂ) * (v r + z r) -
      (Complex.I * deriv (fun t : ℝ => (V t r : ℂ)) s +
        complexRadialLaplacian v r +
        complexRadialHartreeNonlinearity v r +
        Complex.I * (b : ℂ) * complexRadialDilation v r +
        (omega : ℂ) * v r) = _
  rw [hTime, hLap, hScale]
  have hNL' :
      complexRadialHartreeNonlinearity (fun x => v x + z x) r -
        complexRadialHartreeNonlinearity v r =
          ((radialHartreePotential (fun rho => ‖Z s rho‖ ^ 4) r +
            radialHartreePotential
              (actualWholeRadiationMixedQuartic (V s) (Z s)) r : ℝ) : ℂ) *
              actualWholeRadiationLocalCubic
                (fun rho => (V s rho : ℂ) + Z s rho) r +
            (radialHartreePotential
              (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r : ℂ) *
              (actualWholeRadiationLocalCubic
                  (fun rho => (V s rho : ℂ) + Z s rho) r -
                actualWholeRadiationLocalCubic
                  (fun rho => (V s rho : ℂ)) r) := by
    simpa only [v,z] using hNL
  calc
    _ = Complex.I * deriv (fun t : ℝ => Z t r) s +
          complexRadialLaplacian (Z s) r +
          Complex.I * (b : ℂ) * complexRadialDilation (Z s) r +
          (omega : ℂ) * Z s r +
          (complexRadialHartreeNonlinearity (fun x => v x + z x) r -
            complexRadialHartreeNonlinearity v r) := by
        dsimp [z]
        ring
    _ = _ := by rw [hNL']

end HBL.TypeIIDynamicSelection
