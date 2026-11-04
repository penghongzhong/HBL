import HBL.TypeIIDynamicSelection.ActualHartreeComplexCorrectionResidual
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedSpeed
import Mathlib.Tactic

/-!
# Moment-locked time jets in the actual correction residual

Changing the scale speed while fixing the instantaneous core also changes
the derivative of its radiation-moment amplitude.  The two time jets obey
c_s = -b*c + m and c_s = -(b+db)*c + m.  Their difference supplies the
missing -db*c*partial_c V_c term in the scale source.

The physical terminal constructs the second scale jet explicitly from
the first scale path, the same physical clock, and the same genuine 3D
radiation moment.  It is an instantaneous residual identity, not the
construction of a second dynamical orbit.  The correction's full time
derivative, both speed cross terms, and the nonlocal Taylor remainder
remain present.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The complete first variation with the scale source selected by the
same radiation moment, including speed increments acting on the correction. -/
def actualHartreeMomentLockedCorrectionLinearPart
    (c : ℝ) (H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ) : ℂ :=
  Complex.I * deriv (fun t => H t r) s +
    complexRadialLaplacian (H s) r +
    actualHartreeComplexLinearization
      (fun x => (actualMomentLockedCore c x : ℂ)) (H s) r +
    Complex.I * (b : ℂ) * complexRadialDilation (H s) r +
    (omega : ℂ) * H s r +
    (db : ℂ) * actualMomentLockedScaleSource c r +
    (domega : ℂ) * actualMomentLockedPhaseSource c r +
    Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
    (domega : ℂ) * H s r

/-- The actual profile chain rule supplies the time-jet correction to
the scale source, including c=0 and the moving cutoff transition. -/
theorem actual_Hartree_moment_locked_core_time_jet_difference
    (c0 c1 : ℝ → ℝ) (b db m s r : ℝ)
    (hsame : c1 s = c0 s)
    (hc0 : HasDerivAt c0 (-(b * c0 s) + m) s)
    (hc1 : HasDerivAt c1 (-((b + db) * c1 s) + m) s) :
    deriv (fun t => actualMomentLockedCore (c1 t) r) s -
      deriv (fun t => actualMomentLockedCore (c0 t) r) s =
      -(db * c0 s) * actualMomentLockedAmplitudeTangent (c0 s) r := by
  have hd0 : deriv (fun t => actualMomentLockedCore (c0 t) r) s =
      (-(b * c0 s) + m) * actualMomentLockedAmplitudeTangent (c0 s) r := by
    simpa only [actualMomentLockedCore, actualMomentLockedAmplitudeTangent, mul_assoc]
      using (monopoleMovingCutoffTime_hasDerivAt hc0 r).deriv
  have hd1 : deriv (fun t => actualMomentLockedCore (c1 t) r) s =
      (-((b + db) * c1 s) + m) *
        actualMomentLockedAmplitudeTangent (c1 s) r := by
    simpa only [actualMomentLockedCore, actualMomentLockedAmplitudeTangent, mul_assoc]
      using (monopoleMovingCutoffTime_hasDerivAt hc1 r).deriv
  rw [hd1, hd0, hsame]
  ring

/-- Full original PDE correction identity for two moment-locked time
jets with the same instantaneous core.  No projection cancellation or
residual smallness is assumed. -/
theorem actual_Hartree_moment_locked_correction_residual_exact
    (c0 c1 : ℝ → ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega m s r : ℝ) (hr : 0 < r)
    (hsame : c1 s = c0 s)
    (hc0 : HasDerivAt c0 (-(b * c0 s) + m) s)
    (hc1 : HasDerivAt c1 (-((b + db) * c1 s) + m) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r) :
    complexRadialRenormalizedResidual
        (fun t x => (actualMomentLockedCore (c1 t) x : ℂ) + H t x)
        (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual
        (fun t x => (actualMomentLockedCore (c0 t) x : ℂ)) b omega s r =
      actualHartreeMomentLockedCorrectionLinearPart
        (c0 s) H b omega db domega s r +
      actualHartreeComplexTaylorRemainder
        (fun x => (actualMomentLockedCore (c0 s) x : ℂ)) (H s) r := by
  let U : ℝ → ℝ → ℂ := fun t x => (actualMomentLockedCore (c1 t) x : ℂ)
  have hUtime : DifferentiableAt ℝ (fun t => U t r) s :=
    (monopoleMovingCutoffTime_hasDerivAt hc1 r).ofReal_comp.differentiableAt
  have hRealSpace : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (actualMomentLockedCore (c1 s)) x := by
    intro x hx
    exact monopolePerturbedRadialProfile_differentiableAt hx
  have hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x := by
    intro x hx
    exact (hRealSpace x hx).hasDerivAt.ofReal_comp.differentiableAt
  have hfirst : deriv (U s) =ᶠ[𝓝 r]
      (fun x => ((deriv (actualMomentLockedCore (c1 s)) x : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hRealSpace x hx).hasDerivAt.ofReal_comp.deriv
  have hRealSecond :
      DifferentiableAt ℝ (deriv (actualMomentLockedCore (c1 s))) r :=
    monopolePerturbedRadialProfile_deriv_differentiableAt hr
  have hUsecond : DifferentiableAt ℝ (deriv (U s)) r :=
    (hRealSecond.hasDerivAt.ofReal_comp.congr_of_eventuallyEq hfirst).differentiableAt
  have hadd := actual_Hartree_complex_correction_residual_exact
    U H (b + db) (omega + domega) 0 0 s r hr hUtime hHtime
      hUspace hHspace hUsecond hHsecond
  simp only [add_zero] at hadd
  have hbase :
      complexRadialRenormalizedResidual U (b + db) (omega + domega) s r -
        complexRadialRenormalizedResidual
          (fun t x => (actualMomentLockedCore (c0 t) x : ℂ)) b omega s r =
        (db : ℂ) * actualMomentLockedScaleSource (c0 s) r +
          (domega : ℂ) * actualMomentLockedPhaseSource (c0 s) r := by
    dsimp only [U]
    rw [actual_Hartree_core_residual_moment_locked_speed_split
      c1 (b + db) (omega + domega) m s r hr hc1,
      actual_Hartree_core_residual_moment_locked_speed_split
        c0 b omega m s r hr hc0, hsame]
    push_cast
    ring
  change complexRadialRenormalizedResidual (fun t x => U t x + H t x)
      (b + db) (omega + domega) s r -
    complexRadialRenormalizedResidual
      (fun t x => (actualMomentLockedCore (c0 t) x : ℂ)) b omega s r = _
  calc
    _ = (complexRadialRenormalizedResidual (fun t x => U t x + H t x)
          (b + db) (omega + domega) s r -
        complexRadialRenormalizedResidual U (b + db) (omega + domega) s r) +
      (complexRadialRenormalizedResidual U (b + db) (omega + domega) s r -
        complexRadialRenormalizedResidual
          (fun t x => (actualMomentLockedCore (c0 t) x : ℂ)) b omega s r) := by ring
    _ = (actualHartreeComplexCorrectionLinearPart
          U H (b + db) (omega + domega) 0 0 s r +
        actualHartreeComplexTaylorRemainder (U s) (H s) r) +
      ((db : ℂ) * actualMomentLockedScaleSource (c0 s) r +
        (domega : ℂ) * actualMomentLockedPhaseSource (c0 s) r) := by
          rw [hadd, hbase]
    _ = _ := by
      unfold actualHartreeComplexCorrectionLinearPart
        actualHartreeMomentLockedCorrectionLinearPart
      simp only [U, hsame, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
      push_cast
      ring

/-- A concrete change of the scale time jet, fixing its value at s.
Only the instantaneous clock law is used in the physical terminal. -/
def actualMomentLockedScaleJetPerturbation
    (ell : ℝ → ℝ) (db s t : ℝ) : ℝ :=
  ell t * Real.exp (-db * (t - s))

private theorem actual_scale_jet_value (ell : ℝ → ℝ) (db s : ℝ) :
    actualMomentLockedScaleJetPerturbation ell db s s = ell s := by
  simp [actualMomentLockedScaleJetPerturbation]

set_option backward.isDefEq.respectTransparency false in
private theorem actual_scale_jet_hasDerivAt
    (ell : ℝ → ℝ) (b db s : ℝ)
    (hEll : HasDerivAt ell (-(b * ell s)) s) :
    HasDerivAt (actualMomentLockedScaleJetPerturbation ell db s)
      (-((b + db) * actualMomentLockedScaleJetPerturbation ell db s s)) s := by
  have hlin : HasDerivAt (fun t : ℝ => -db * (t - s)) (-db) s := by
    simpa using ((hasDerivAt_id s).sub_const s).const_mul (-db)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-db * (t - s))) (-db) s := by
    simpa only [sub_self, mul_zero, Real.exp_zero, one_mul, mul_one] using hlin.exp
  have hcoef : -((b + db) * actualMomentLockedScaleJetPerturbation ell db s s) =
      -(b * ell s) + ell s * -db := by
    rw [actual_scale_jet_value]
    ring
  rw [hcoef]
  have hprod := hEll.mul hexp
  have hfun : (ell * fun t : ℝ => Real.exp (-db * (t - s))) =
      actualMomentLockedScaleJetPerturbation ell db s := by
    funext t
    rfl
  rw [hfun] at hprod
  simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using hprod

/-- Physical specialization: one scale path, one physical clock and one
genuine 3D radiation moment construct both time jets. The second moment
amplitude and its derivative are derived, not freely prescribed. -/
theorem actual_Hartree_physical_moment_locked_correction_residual_exact
    (ell : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (H : ℝ → ℝ → ℂ) (b omega db domega s dm r : ℝ) (hr : 0 < r)
    (hEll : HasDerivAt ell (-(b * ell s)) s)
    (hEllPos : 0 < ell s)
    (hTime : HasDerivAt time ((ell s) ^ 2) s)
    (hMoment : HasDerivAt
      (fun t => actualPhysicalInverseSquareMoment (z t)) dm (time s))
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r) :
    complexRadialRenormalizedResidual
        (fun t x =>
          (actualMomentMonopoleProfile
            (actualMomentLockedScaleJetPerturbation ell db s) z time t x : ℂ) +
              H t x) (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual
        (fun t x => (actualMomentMonopoleProfile ell z time t x : ℂ)) b omega s r =
      actualHartreeMomentLockedCorrectionLinearPart
        (actualPhysicalRadiationMonopole ell z time s) H b omega db domega s r +
      actualHartreeComplexTaylorRemainder
        (fun x => (actualMomentMonopoleProfile ell z time s x : ℂ)) (H s) r := by
  let ell1 : ℝ → ℝ := actualMomentLockedScaleJetPerturbation ell db s
  let c0 : ℝ → ℝ := actualPhysicalRadiationMonopole ell z time
  let c1 : ℝ → ℝ := actualPhysicalRadiationMonopole ell1 z time
  let m : ℝ := hartreeKappa * (ell s) ^ 3 * dm
  have hell : ell1 s = ell s := actual_scale_jet_value ell db s
  have hell1 : HasDerivAt ell1 (-((b + db) * ell1 s)) s :=
    actual_scale_jet_hasDerivAt ell b db s hEll
  have hell1pos : 0 < ell1 s := by rw [hell]; exact hEllPos
  have htime1 : HasDerivAt time ((ell1 s) ^ 2) s := by
    rw [hell]
    exact hTime
  have hc0 : HasDerivAt c0 (-(b * c0 s) + m) s :=
    actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
      ell (fun _ => b) z time hEll hEllPos hTime hMoment
  have hc1 : HasDerivAt c1 (-((b + db) * c1 s) + m) s := by
    have h := actual_physical_threeD_radiation_slow_coefficient_hasDerivAt
      ell1 (fun _ => b + db) z time hell1 hell1pos htime1 hMoment
    simpa only [hell, c1, m] using h
  have hsame : c1 s = c0 s := by
    dsimp only [c0, c1, actualPhysicalRadiationMonopole]
    rw [hell]
  exact actual_Hartree_moment_locked_correction_residual_exact
    c0 c1 H b omega db domega m s r hr hsame hc0 hc1
      hHtime hHspace hHsecond

end HBL.TypeIIDynamicSelection
