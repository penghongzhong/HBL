import HBL.TypeIIDynamicSelection.ActualHartreeKummerTerminalCoverage
import HBL.TypeIIDynamicSelection.ActualOneOrbitTwoSidedMomentWindow
import HBL.TypeIIDynamicSelection.ActualOneLayerTwoChannelPDE
import HBL.TypeIIDynamicSelection.ActualHartreeDynamicPhaseCovariance
import Mathlib.Tactic

/-!
# Revised HBL manuscript 2.12: actual physical source in correct Kummer coordinates

Only local positive-annulus continuity of the original physical source
is used. Its global totalized 2/r radial Laplacian need NOT be continuous
at the origin: a concrete continuous extension is constructed using
the standard clamp to the fixed positive Kummer annulus.

The physical Hartree PDE is an explicit assumption for all real physical times in the local regularity interval, NOT merely at T. The actual 3D energy-critical inverse-square Hartree orbit has a strictly
positive continuous terminal quartic moment. In the TRUE Kummer coordinate
r=R_bubble/sqrt(q), a physical source F_phys(R_bubble) becomes the
genuine coordinate-pullback F_K(z)=F_phys(sqrt(q)*z).

The physical clock q(s)=(T-time(s))/ell(s)^2 removes the *unknown*
Type-II concentration rate from the cutoff geometry:
ell(s)*sqrt(q(s))=sqrt(T-time(s)).
Therefore a prescribed finite Kummer annulus is eventually wholly
inside the original physical Hartree moment-generated smooth cutoff.
The fixed Wronskian-normalized inhomogeneous Green inverse solves the
local frozen Kummer equation for F_K without a differential cutoff error.
The two genuine H+/H- physical PDE channels at sqrt(q)*z are its
real and imaginary parts. No independent surrogate source is used.

IMPORTANT SCOPE: This local frozen-ODE inverse theorem does NOT claim
the *full* physical PDE residual is equal to the frozen ODE operator
without the still-missing conjugation/parameter-tangent identities.
Global remote Riesz, interface transfer and generated positive-order
residual estimates remain in the revised manuscript 2.13, which must
construct the actual global Hartree finite profile. Do not count this
as the old unmodified global one-layer elimination.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- A single genuine physical Hartree trajectory produces both real
H+/H- source components and the fixed-annulus, rate-free
Wronskian-normalized Kummer Green inverse of their CORRECT
physical-coordinate pullback. This is the revised LOCAL lemma 2.12,
not the old full four-region minimal-weight cancellation. -/
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
    (hPDEall : ∀ t ∈ I, ∀ rho : ℝ, 0 < rho →
      zt t rho = Complex.I *
        (complexRadialLaplacian (z t) rho +
          complexRadialHartreeNonlinearity (z t) rho))
    (ell q time gamma b omega : ℝ → ℝ)
    (hTime : Tendsto time atTop (𝓝 T))
    (hBefore : ∀ᶠ s in atTop, time s < T)
    (hEll : ∀ᶠ s in atTop, 0 < ell s)
    (hClock : ∀ᶠ s in atTop,
      q s = (T - time s) / (ell s) ^ 2)
    (V : ℝ → ℝ → ℝ)
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hcenter : 0 < center + d)
    (hFcontOn : ∀ s : ℝ, 0 < q s →
      ContinuousOn
        (fun r : ℝ =>
          actualOneLayerCommonPDEResidual V
            (fun τ x => actualHartreeUnitPhase (gamma τ) *
              rescalePhysicalRadiation (ell τ) (z (time τ)) x)
            (b s) (omega s) s (Real.sqrt (q s) * r))
        (Icc (center - d) (center + d))) :
    ∀ᶠ s in atTop, ∀ r ∈ Ioo (center - d) (center + d),
      let Z : ℝ → ℝ → ℂ :=
        fun τ x => actualHartreeUnitPhase (gamma τ) *
          rescalePhysicalRadiation (ell τ) (z (time τ)) x
      let Fphys : ℝ → ℂ :=
        actualOneLayerCommonPDEResidual V Z (b s) (omega s) s
      let FK : ℝ → ℂ := fun x =>
        Fphys (Real.sqrt (q s) *
          min (max x (center - d)) (center + d))
      let Rz : ℝ := actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s) (radialPhysicalQuarticMoment (z (time s)))
      let U : ℝ → ℂ := actualKummerCauchyValue K d FK 0 0
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualOneLayerInnerOverlapCutoff Rz x * U x) r = FK r ∧
      actualOneLayerPlusPDE V Z (b s) (omega s) s
        (Real.sqrt (q s) * r) =
          (Fphys (Real.sqrt (q s) * r)).re ∧
      actualOneLayerMinusPDE V Z (b s) (omega s) s
        (Real.sqrt (q s) * r) =
          (Fphys (Real.sqrt (q s) * r)).im := by
  have hTmem : T ∈ I := mem_of_mem_nhds hI
  have hPDE : ∀ rho : ℝ, 0 < rho →
      zt T rho = Complex.I *
        (complexRadialLaplacian (z T) rho +
          complexRadialHartreeNonlinearity (z T) rho) :=
    hPDEall T hTmem
  obtain ⟨deltaT, hDelta, hWindow⟩ :=
    actual_one_orbit_Hartree_terminal_two_sided_moment_window
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE
  let mT : ℝ :=
    radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation
  have hmT : 0 < mT := by
    have h := actual_one_orbit_terminal_radiation_positive_moment
    simpa only [mT, actual_physical_inverse_square_radial_reduction] using h
  let M : ℝ := 2 * mT
  have hM : 0 < M := by dsimp [M]; positivity
  have hNear : ∀ᶠ s in atTop, |time s - T| < deltaT := by
    filter_upwards [hTime.eventually (Metric.ball_mem_nhds hDelta)]
      with s hs
    simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hMoment : ∀ᶠ s in atTop,
      0 < radialPhysicalQuarticMoment (z (time s)) ∧
      radialPhysicalQuarticMoment (z (time s)) ≤ M := by
    filter_upwards [hNear] with s hs
    obtain ⟨hLower, hUpper⟩ := hWindow (time s) hs
    have hmLower : mT / 2 <
        radialPhysicalQuarticMoment (z (time s)) := by
      simpa only [mT, actual_physical_inverse_square_radial_reduction]
        using hLower
    have hmUpper :
        radialPhysicalQuarticMoment (z (time s)) < M := by
      simpa only [M, mT, actual_physical_inverse_square_radial_reduction]
        using hUpper
    exact ⟨by linarith [hmT], hmUpper.le⟩
  have hCover : ∀ᶠ s in atTop,
      center + d ≤ actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s)
          (radialPhysicalQuarticMoment (z (time s))) :=
    actual_Hartree_eventual_original_Kummer_coordinate_covered
      ell q (fun s => radialPhysicalQuarticMoment (z (time s)))
      time T M center d hM hcenter hTime hBefore hEll hClock hMoment
  filter_upwards [hCover, hBefore, hEll, hClock, hMoment]
    with s hCovered hBeforeS hEllS hClockS hMomentS
  have htau : 0 < T - time s := sub_pos.mpr hBeforeS
  have hq : 0 < q s := by
    rw [hClockS]
    exact div_pos htau (sq_pos_of_pos hEllS)
  have hsqrt : 0 < Real.sqrt (q s) := Real.sqrt_pos.2 hq
  have hmPos :
      0 < radialPhysicalQuarticMoment (z (time s)) := hMomentS.1
  have hR :
      0 < actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s)
          (radialPhysicalQuarticMoment (z (time s))) := by
    dsimp [actualHartreeKummerCoordinateCutoffRadius,
      actualHartreeMomentCutoffRadius]
    have hk : 0 < hartreeKappa := by
      unfold hartreeKappa
      positivity
    positivity
  let Z : ℝ → ℝ → ℂ :=
    fun τ x => actualHartreeUnitPhase (gamma τ) *
      rescalePhysicalRadiation (ell τ) (z (time τ)) x
  let Fphys : ℝ → ℂ :=
    actualOneLayerCommonPDEResidual V Z (b s) (omega s) s
  let clamp : ℝ → ℝ :=
    fun x => min (max x (center - d)) (center + d)
  let FK : ℝ → ℂ :=
    fun x => Fphys (Real.sqrt (q s) * clamp x)
  have hInterval : center - d ≤ center + d := by linarith [hd]
  have hClampContinuous : Continuous clamp := by
    exact (continuous_id.max continuous_const).min continuous_const
  have hClampMem (x : ℝ) :
      clamp x ∈ Icc (center - d) (center + d) := by
    dsimp [clamp]
    exact ⟨le_min (le_max_right _ _) hInterval, min_le_right _ _⟩
  have hFK : Continuous FK := by
    change Continuous ((fun r : ℝ =>
      Fphys (Real.sqrt (q s) * r)) ∘ clamp)
    exact (hFcontOn s hq).comp_continuous
      hClampContinuous hClampMem
  have hFK_id (r : ℝ) (hr : r ∈ Ioo (center - d) (center + d)) :
      FK r = Fphys (Real.sqrt (q s) * r) := by
    dsimp [FK, clamp]
    rw [max_eq_left hr.1.le, min_eq_left hr.2.le]
  have hExact (r : ℝ) (hr : r ∈ Ioo (center - d) (center + d)) :
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x =>
          actualOneLayerInnerOverlapCutoff
            (actualHartreeKummerCoordinateCutoffRadius
              (ell s) (q s)
              (radialPhysicalQuarticMoment (z (time s)))) x *
            actualKummerCauchyValue K d FK 0 0 x) r =
          FK r :=
    (actual_Hartree_normalized_Kummer_inside_physical_cutoff_exact
      K d hd hde FK hFK
      (actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s) (radialPhysicalQuarticMoment (z (time s))))
      hR hCovered r hr).2.2.2
  intro r hr
  dsimp only
  have hSource := hExact r hr
  rw [hFK_id r hr] at hSource
  refine ⟨hSource, ?_, ?_⟩
  · rfl
  · rfl

end HBL.TypeIIDynamicSelection
