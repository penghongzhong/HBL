import HBL.TypeIIDynamicSelection.ActualOneOrbitPhysicalKummerSourceBridge
import HBL.TypeIIDynamicSelection.ActualHartreeKummerClockIdentity
import Mathlib.Tactic

/-!
# Revised manuscript 2.12: one physical Hartree source, two channels, canonical local Kummer inverse

The genuine radial energy-critical 3D Hartree flow z(t,r) (with the true
inverse-square quartic Riesz interaction) supplies its own terminal
quartic moment, the two real Fredholm source channels, and a single
canonical normalized inhomogeneous Kummer Green solution.

The EXACT physical clock q(s)=(T-time(s))/ell(s)^2 and the positive,
continuous moment m[z(t)] together imply eventual inclusion of any
fixed prescribed Kummer annulus in the original physical moving cutoff:
ell(s)*sqrt(q(s))=sqrt(T-time(s)). No Type-II rate is assumed.

This theorem concludes equality of the Kummer FROZEN LOCAL differential
equation to the SAME original complex Hartree residual, plus its real/imag
H+/H- projection identities, all eventually in renormalized time.
It does NOT assert simultaneous global Fredholm/Kummer/remote C1 matches
or the entire nonlinear minimal-weight cluster and generated positive
source hierarchy. These stronger tasks belong to revised 2.13 and
remain mathematical obligations, not inputs to this theorem.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Revision of old one-layer stage3: canonical local Hartree-Kummer
source elimination from one actual physical PDE orbit, with no
postulated concentration rate or arbitrary homogeneous matching
coefficients. Its conclusion is strictly local and is NOT the old
global minimum-weight cancellation claim. -/
theorem revised_one_layer_physical_local_source_certified
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
    (hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho))
    (ell q time gamma b omega : ℝ → ℝ)
    (hTime : Tendsto time atTop (𝓝 T))
    (hBefore : ∀ᶠ s in atTop, time s < T)
    (hEll : ∀ᶠ s in atTop, 0 < ell s)
    (hClock : ∀ᶠ s in atTop,
      q s = (T - time s) / (ell s) ^ 2)
    (V : ℝ → ℝ → ℝ)
    (hFcont : ∀ s : ℝ,
      Continuous (actualOneLayerCommonPDEResidual V
        (fun τ x => actualHartreeUnitPhase (gamma τ) *
          rescalePhysicalRadiation (ell τ) (z (time τ)) x)
        (b s) (omega s) s))
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hcenter : 0 < center + d) :
    ∀ᶠ s in atTop, ∀ r ∈ Ioo (center - d) (center + d),
      let Z : ℝ → ℝ → ℂ :=
        fun τ x => actualHartreeUnitPhase (gamma τ) *
          rescalePhysicalRadiation (ell τ) (z (time τ)) x
      let F : ℝ → ℂ :=
        actualOneLayerCommonPDEResidual V Z (b s) (omega s) s
      let Rz : ℝ := actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s) (radialPhysicalQuarticMoment (z (time s)))
      let U : ℝ → ℂ := actualKummerCauchyValue K d F 0 0
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff Rz x * U x) r = F r ∧
      actualOneLayerPlusPDE V Z (b s) (omega s) s r = (F r).re ∧
      actualOneLayerMinusPDE V Z (b s) (omega s) s r = (F r).im := by
  obtain ⟨deltaT, ellMax, hDeltaT, hEllMax, hBridge⟩ :=
    actual_one_orbit_Hartree_same_PDE_normalized_Kummer_core
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE
      ell q time gamma b omega V hFcont K d hd hde hcenter
  have hTau : Tendsto (fun s : ℝ => T - time s)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub hTime)
  have hNear : ∀ᶠ s in atTop, |time s - T| < deltaT := by
    filter_upwards [hTime.eventually (Metric.ball_mem_nhds hDeltaT)]
      with s hs
    simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hClose : ∀ᶠ s in atTop, T - time s < ellMax ^ 2 :=
    hTau.eventually (Iio_mem_nhds (sq_pos_of_pos hEllMax))
  filter_upwards [hNear, hClose, hBefore, hEll, hClock]
    with s hNearS hCloseS hBeforeS hEllS hClockS
  have hTauPos : 0 < T - time s := sub_pos.mpr hBeforeS
  have hQPos : 0 < q s := by
    rw [hClockS]
    exact div_pos hTauPos (sq_pos_of_pos hEllS)
  have hScale :
      ell s * Real.sqrt (q s) = Real.sqrt (T - time s) := by
    rw [hClockS]
    exact actual_Hartree_Kummer_clock_sqrt_scale_exact
      (ell s) (T - time s) hEllS hTauPos
  have hSqrtSmall : Real.sqrt (T - time s) ≤ ellMax := by
    have hSq :
        (Real.sqrt (T - time s)) ^ 2 < ellMax ^ 2 := by
      rw [Real.sq_sqrt hTauPos.le]
      exact hCloseS
    nlinarith [Real.sqrt_nonneg (T - time s)]
  have hSmall : ell s * Real.sqrt (q s) ≤ ellMax :=
    hScale.le.trans hSqrtSmall
  intro r hr
  have hExact := hBridge s hNearS hEllS hQPos hSmall r hr
  dsimp only at hExact ⊢
  refine ⟨hExact, ?_, ?_⟩
  · rfl
  · rfl

end HBL.TypeIIDynamicSelection
