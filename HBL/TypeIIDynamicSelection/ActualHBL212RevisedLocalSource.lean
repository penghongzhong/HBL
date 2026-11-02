import HBL.TypeIIDynamicSelection.ActualOneOrbitPhysicalKummerSourceBridge
import HBL.TypeIIDynamicSelection.ActualHartreeKummerClockIdentity
import Mathlib.Tactic

/-!
# Revised original lemma 2.12: one physical Hartree source, actual local
# normalized Kummer Green equation, BOTH Fredholm channel projections.

This is a precisely LIMITED revised manuscript target. It does not
claim the old, stronger 2.12 minimum-weight cluster, global C1
inner/Kummer/outer boundary matching, or all positive generated orders.
Those genuinely open tasks are retained without deletion in the revised
finite-profile proposition 2.13. The true PDE-derived Type-II
concentration exponent remains an output of the final main theorem.

For one genuine Hartree regular orbit with explicit primitive PDE jets
and dominated quartic moment, the true physical clock time(s) -> T
from below and the EXACT q(s)=(T-time(s))/ell(s)^2 show that
the original Kummer-coordinate moving cutoff radius eventually
covers the prescribed positive local annulus. The same full complex
Hartree PDE residual is pulled back through R=sqrt(q)*z and used as
the normalized Kummer Green forcing; its real/imaginary projections
equal the actual Hplus/Hminus source. No abstract regional solver.

Rate selection, physical high-regularity source realization and
global nonlinear three-domain matching must not be inferred from
this local result.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

/-- The complete *revised local* original HBL 2.12 terminal:
same physical nonlocal Hartree PDE source and quartic moment,
exact physical-to-Kummer coordinate change, two-Wronskian-normalized
Green source identity on every point of its fixed positive annulus,
and the exact two true Fredholm projections, EVENTUALLY in the
original physical terminal time. Does not imply original global
one-weight atom elimination (moved to and still open in 2.13). -/
theorem revised_2_12_same_Hartree_orbit_normalized_Kummer_source_closed
    (z zt : ℝ → ℝ → ℂ) (T : ℝ)
    (hTerminal : z T = actualOneOrbitTerminalRadiation)
    (I : Set ℝ) (hI : I ∈ 𝓝 T)
    (hZmeas : ∀ᶠ t in 𝓝 T,
      AEStronglyMeasurable (fun rho => ‖z t rho‖ ^ 4)
        (volume.restrict (Ioi (0 : ℝ))))
    (hZint : IntegrableOn
      (fun rho => ‖z T rho‖ ^ 4) (Ioi (0 : ℝ)))
    (hVelMeas : AEStronglyMeasurable
      (fun rho => actualRadialQuarticMomentVelocity (z T rho) (zt T rho))
      (volume.restrict (Ioi (0 : ℝ))))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioi (0 : ℝ)))
    (hBound : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      |actualRadialQuarticMomentVelocity (z t rho) (zt t rho)| ≤ B rho)
    (hRe : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).re) (zt t rho).re t)
    (hIm : ∀ rho : ℝ, 0 < rho → ∀ t ∈ I,
      HasDerivAt (fun x => (z x rho).im) (zt t rho).im t)
    (hPDEall : ∀ t ∈ I, ∀ rho : ℝ, 0 < rho →
      zt t rho = Complex.I *
        (complexRadialLaplacian (z t) rho +
          complexRadialHartreeNonlinearity (z t) rho))
    (ell q time gamma b omega : ℝ → ℝ)
    (V : ℝ → ℝ → ℝ)
    (hTime : Tendsto time atTop (𝓝 T))
    (hBefore : ∀ᶠ s in atTop, time s < T)
    (hEll : ∀ᶠ s in atTop, 0 < ell s)
    (hClock : ∀ᶠ s in atTop,
      q s = (T - time s) / (ell s) ^ 2)
    (hFcont : ∀ s : ℝ,
      Continuous (actualOneLayerCommonPDEResidual V
        (fun τ x => actualHartreeUnitPhase (gamma τ) *
          rescalePhysicalRadiation (ell τ) (z (time τ)) x)
        (b s) (omega s) s))
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hcenter : 0 < center + d) :
    ∀ᶠ s in atTop,
      ∀ r ∈ Ioo (center - d) (center + d),
        let Z : ℝ → ℝ → ℂ :=
          fun τ x => actualHartreeUnitPhase (gamma τ) *
            rescalePhysicalRadiation (ell τ) (z (time τ)) x
        let F : ℝ → ℂ :=
          fun u => actualOneLayerCommonPDEResidual V Z
            (b s) (omega s) s (Real.sqrt (q s) * u)
        let Rz := actualHartreeKummerCoordinateCutoffRadius (ell s) (q s)
          (radialPhysicalQuarticMoment (z (time s)))
        actualHartreeFrozenKummerRadialApply mu theta
          (fun x => actualOneLayerInnerOverlapCutoff Rz x *
            actualKummerCauchyValue K d F 0 0 x) r = F r ∧
        actualOneLayerPlusPDE V Z (b s) (omega s) s
          (Real.sqrt (q s) * r) = (F r).re ∧
        actualOneLayerMinusPDE V Z (b s) (omega s) s
          (Real.sqrt (q s) * r) = (F r).im := by
  have hTmem : T ∈ I := mem_of_mem_nhds hI
  have hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho) :=
    hPDEall T hTmem
  obtain ⟨deltaT, ellMax, hDeltaT, hEllMax, hLocal⟩ :=
    actual_one_orbit_Hartree_same_PDE_normalized_Kummer_core
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE ell q time gamma b omega V
      hFcont K d hd hde hcenter
  have hCloseTime : ∀ᶠ s in atTop, |time s - T| < deltaT := by
    have hBall : ∀ᶠ s in atTop, time s ∈ Metric.ball T deltaT :=
      hTime.eventually (Metric.ball_mem_nhds hDeltaT)
    filter_upwards [hBall] with s hs
    simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hTau : Tendsto (fun s : ℝ => T - time s)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub hTime)
  have hSmallTau : ∀ᶠ s in atTop, T - time s < ellMax ^ 2 :=
    hTau.eventually (Iio_mem_nhds (sq_pos_of_pos hEllMax))
  filter_upwards [hCloseTime, hBefore, hEll, hClock, hSmallTau] with
      s hNear hBeforeS hEllS hClockS hTauSmall
  have hRemaining : 0 < T - time s := sub_pos.mpr hBeforeS
  have hQPos : 0 < q s := by
    rw [hClockS]
    positivity
  have hSqrt : Real.sqrt (T - time s) ≤ ellMax := by
    have hsquare : (Real.sqrt (T - time s)) ^ 2 < ellMax ^ 2 := by
      rw [Real.sq_sqrt hRemaining.le]
      exact hTauSmall
    nlinarith [Real.sqrt_nonneg (T - time s)]
  have hEllQ : ell s * Real.sqrt (q s) ≤ ellMax := by
    calc
      ell s * Real.sqrt (q s) =
          Real.sqrt (T - time s) := by
        rw [hClockS]
        exact actual_Hartree_Kummer_clock_sqrt_scale_exact
          (ell s) (T - time s) hEllS hRemaining
      _ ≤ ellMax := hSqrt
  intro r hr
  exact hLocal s hNear hEllS hQPos hEllQ r hr

end HBL.TypeIIDynamicSelection
