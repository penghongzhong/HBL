import HBL.TypeIIDynamicSelection.ActualHartreeKummerCoordinateBridge
import HBL.TypeIIDynamicSelection.ActualOneOrbitTwoSidedMomentWindow
import HBL.TypeIIDynamicSelection.ActualOneLayerTwoChannelPDE
import HBL.TypeIIDynamicSelection.ActualHartreeDynamicPhaseCovariance
import Mathlib.Tactic

/-!
# Original HBL 2.12: the SAME actual Hartree orbit, source and Kummer radius

One genuine physical 3D generalized-Hartree radial regular solution z(t)
enters BOTH the actual physical inverse-square quartic moment
m(t)=4*pi*integral |z(t,r)|^4 and the dynamically rephased,
critically rescaled radiation Z(s,r).

From the actual Hartree PDE/dominated quartic moment, the moment lies
between m(T)/2 and 2*m(T) on one terminal neighborhood.
Consequently, when ell(s)*sqrt(q(s)) is small, the KUMMER-COORDINATE
cutoff R_z(s)=4/(kappa_H ell(s)*sqrt(q(s))*m(t(s))) contains any
given FIXED prescribed normalized Kummer annulus. The physical
coordinate is R_bubble=sqrt(q)*z, never identified with z.

The same complex actual full-Hartree-minus-core PDE source is PULLED
BACK from the bubble radius R=sqrt(q)*z to the Kummer radius z.
Its real and imaginary parts feed the actual H+/H- Fredholm channels,
is solved EXACTLY on this fixed annulus by the already constructed
two-Wronskian-normalized Kummer Green solution, even after applying
the original moving cutoff. The cutoff is identically one there,
so the *differential* Kummer commutator vanishes.

Only source continuity on the corresponding CLOSED POSITIVE annulus
is a visible high-regularity input. Endpoint clipping gives the
canonical global continuous extension, with no origin regularity.
The source's local continuity is an analytic not a postulated positive-order remainder. This is NOT a
proof of large-radius Kummer/Frobenius asymptotics or remote
boundary-jet compatibility, the mixed whole-radiation weighted
source hierarchy, or the full original 2.12.
No prescribed Type-II rate or new axiom.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer


/-- Exact endpoint-clipped extension of a complex physical Hartree source
continuous only on a prescribed CLOSED positive annulus. -/
private theorem actual_Hartree_scaled_clamped_source_continuous
    (G : ℝ → ℂ) (k a b : ℝ) (hk : 0 ≤ k) (hab : a ≤ b)
    (hG : ContinuousOn G (Icc (k * a) (k * b))) :
    Continuous (fun x : ℝ => G (k * min (max x a) b)) ∧
    (∀ x ∈ Icc a b, G (k * min (max x a) b) = G (k * x)) := by
  have hClip : Continuous (fun x : ℝ => min (max x a) b) :=
    (continuous_id.max continuous_const).min continuous_const
  have hArg : Continuous (fun x : ℝ => k * min (max x a) b) :=
    continuous_const.mul hClip
  have hRange (x : ℝ) :
      k * min (max x a) b ∈ Icc (k * a) (k * b) := by
    have hlo : a ≤ min (max x a) b :=
      le_min (le_max_right _ _) hab
    have hhi : min (max x a) b ≤ b := min_le_right _ _
    exact ⟨mul_le_mul_of_nonneg_left hlo hk,
      mul_le_mul_of_nonneg_left hhi hk⟩
  refine ⟨hG.comp_continuous hArg hRange, ?_⟩
  intro x hx
  have hClipEq : min (max x a) b = x := by
    rw [max_eq_left hx.1, min_eq_left hx.2]
  rw [hClipEq]

/-- Same physical PDE orbit supplies the moment-selected cutoff radius
and the genuine complex Hartree source in the normalized Kummer equation.
Exact local equation, not an abstract RegionalSolver hypothesis. -/
theorem actual_one_orbit_Hartree_same_PDE_normalized_Kummer_core
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
    (V : ℝ → ℝ → ℝ)
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hcenter : 0 < center + d)
    (hFcont : ∀ s : ℝ,
      ContinuousOn (actualOneLayerCommonPDEResidual V
        (fun τ x => actualHartreeUnitPhase (gamma τ) *
          rescalePhysicalRadiation (ell τ) (z (time τ)) x)
        (b s) (omega s) s)
        (Icc (Real.sqrt (q s) * (center - d))
          (Real.sqrt (q s) * (center + d)))) :
    ∃ deltaT ellMax : ℝ, 0 < deltaT ∧ 0 < ellMax ∧
      ∀ s : ℝ, |time s - T| < deltaT →
        0 < ell s → 0 < q s →
        ell s * Real.sqrt (q s) ≤ ellMax →
        ∀ r ∈ Ioo (center - d) (center + d),
          let Z : ℝ → ℝ → ℂ :=
            fun τ x => actualHartreeUnitPhase (gamma τ) *
              rescalePhysicalRadiation (ell τ) (z (time τ)) x
          let F : ℝ → ℂ :=
            fun u => actualOneLayerCommonPDEResidual V Z
              (b s) (omega s) s
              (Real.sqrt (q s) * min (max u (center - d)) (center + d))
          let Rz := actualHartreeKummerCoordinateCutoffRadius (ell s) (q s)
            (radialPhysicalQuarticMoment (z (time s)))
          F r = actualOneLayerCommonPDEResidual V Z
              (b s) (omega s) s (Real.sqrt (q s) * r) ∧
          actualHartreeFrozenKummerRadialApply mu theta
            (fun x => actualOneLayerInnerOverlapCutoff Rz x *
              actualKummerCauchyValue K d F 0 0 x) r = F r ∧
          actualOneLayerPlusPDE V Z (b s) (omega s) s
              (Real.sqrt (q s) * r) = (F r).re ∧
          actualOneLayerMinusPDE V Z (b s) (omega s) s
              (Real.sqrt (q s) * r) = (F r).im := by
  obtain ⟨deltaT,hDeltaT,hWindow⟩ :=
    actual_one_orbit_Hartree_terminal_two_sided_moment_window
      z zt T hTerminal I hI hZmeas hZint hVelMeas
      B hB hBound hRe hIm hPDE
  let mT : ℝ :=
    radialPhysicalQuarticMoment actualOneOrbitTerminalRadiation
  have hmT : 0 < mT := by
    have h := actual_one_orbit_terminal_radiation_positive_moment
    simpa only [mT, actual_physical_inverse_square_radial_reduction] using h
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  let ellMax : ℝ := 4 / (hartreeKappa * (2 * mT) * (center + d))
  have hEllMax : 0 < ellMax := by
    dsimp [ellMax]
    positivity
  refine ⟨deltaT,ellMax,hDeltaT,hEllMax,?_⟩
  intro s hTimeSmall hEllPos hqPos hEllSmall r hr
  obtain ⟨hMomentLo,hMomentHi⟩ := hWindow (time s) hTimeSmall
  have hmLo :
      mT / 2 < radialPhysicalQuarticMoment (z (time s)) := by
    simpa only [mT, actual_physical_inverse_square_radial_reduction]
      using hMomentLo
  have hmPos : 0 < radialPhysicalQuarticMoment (z (time s)) := by
    linarith [hmT]
  have hmHi :
      radialPhysicalQuarticMoment (z (time s)) ≤ 2 * mT := by
    have h := hMomentHi.le
    simpa only [mT, actual_physical_inverse_square_radial_reduction]
      using h
  have hLength : ell s * Real.sqrt (q s) ≤
      4 / (hartreeKappa * (2 * mT) * (center + d)) := by
    simpa only [ellMax] using hEllSmall
  let Z : ℝ → ℝ → ℂ :=
    fun τ x => actualHartreeUnitPhase (gamma τ) *
      rescalePhysicalRadiation (ell τ) (z (time τ)) x
  let F : ℝ → ℂ :=
    fun u => actualOneLayerCommonPDEResidual V Z
      (b s) (omega s) s
      (Real.sqrt (q s) * min (max u (center - d)) (center + d))
  have hClosed : center - d ≤ center + d := by linarith [hd]
  obtain ⟨hFc, hFinside⟩ :=
    actual_Hartree_scaled_clamped_source_continuous
      (actualOneLayerCommonPDEResidual V Z (b s) (omega s) s)
      (Real.sqrt (q s)) (center - d) (center + d)
      (Real.sqrt_nonneg _) hClosed (hFcont s)
  have hPoint : F r =
      actualOneLayerCommonPDEResidual V Z
        (b s) (omega s) s (Real.sqrt (q s) * r) :=
    hFinside r (Ioo_subset_Icc_self hr)
  dsimp only
  refine ⟨hPoint, ?_, ?_, ?_⟩
  · exact actual_Hartree_Kummer_coordinate_original_source_exact
      K d hd hde F hFc (ell s) (q s)
      (radialPhysicalQuarticMoment (z (time s))) (2 * mT)
      hEllPos hqPos hmPos hmHi hcenter hLength r hr
  · exact congrArg Complex.re hPoint.symm
  · exact congrArg Complex.im hPoint.symm

end HBL.TypeIIDynamicSelection
