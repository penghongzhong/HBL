import HBL.TypeIIDynamicSelection.PhysicalResidualMatch

/-!
# Moving Hartree remote cutoff: local-in-time physical residual identity

The earlier exact radial Hartree source identity required remote radiation
Z(t,rho) to vanish below ONE fixed radius R for ALL times t. Actual
three-region blowup profiles have a moving cutoff R(t), so that global
assumption was too strong.

This module proves that CONTINUITY of the physical moving cutoff R at
the test time s and actual exterior support rho <= R(t) imply the local
time derivative cancellation. This makes the identity compatible with
moving regions, without postulating the renormalized residual equality.
It does not construct the remote radiation or the full PDE orbit.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation HBL.Modulation.AffineTail

/-- For a continuously moving exterior cutoff, an interior observation
radius remains exterior-radiation-free on a real time neighborhood. -/
theorem moving_remote_cutoff_eventually_zero
    (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ) {s r : ℝ}
    (hR : ContinuousAt R s) (hr : r < R s)
    (hZ : ∀ t rho, rho ≤ R t → Z t rho = 0) :
    (fun t => Z t r) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℂ)) := by
  have hnear : ∀ᶠ t in 𝓝 s, r < R t :=
    hR.tendsto.eventually (Ioi_mem_nhds hr)
  filter_upwards [hnear] with t ht
  exact hZ t r ht.le

/-- The *full* actual renormalized Hartree PDE residual, not merely a
scalar effective source, changes in the interior ONLY by the genuine
nonlocal Hartree density contribution of moving exterior radiation.
No frozen spatial or time cutoff is assumed. -/
theorem actual_full_radial_residual_moving_remote_eq_nonlin
    (c b omega R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r : ℝ} (hR : ContinuousAt R s) (hr : r < R s)
    (hZ : ∀ t rho, rho ≤ R t → Z t rho = 0) :
    complexRadialRenormalizedResidual
      (monopoleWithRemoteRadiation c Z) (b s) (omega s) s r -
      complexRadialRenormalizedResidual
        (monopoleInnerComplexProfile c) (b s) (omega s) s r =
    complexRadialHartreeNonlinearity
      (monopoleWithRemoteRadiation c Z s) r -
      complexRadialHartreeNonlinearity
        (monopoleInnerComplexProfile c s) r := by
  have htimeEq : (fun t => monopoleWithRemoteRadiation c Z t r) =ᶠ[𝓝 s]
      (fun t => monopoleInnerComplexProfile c t r) := by
    filter_upwards [moving_remote_cutoff_eventually_zero R Z hR hr hZ]
      with t hz
    simp only [monopoleWithRemoteRadiation, hz, add_zero]
  have ht : deriv (fun t => monopoleWithRemoteRadiation c Z t r) s =
      deriv (fun t => monopoleInnerComplexProfile c t r) s :=
    htimeEq.deriv_eq
  have hsp : monopoleWithRemoteRadiation c Z s =ᶠ[𝓝 r]
      monopoleInnerComplexProfile c s := by
    filter_upwards [Iio_mem_nhds hr] with x hx
    simp only [monopoleWithRemoteRadiation, hZ s x hx.le, add_zero]
  have hL : complexRadialLaplacian
      (monopoleWithRemoteRadiation c Z s) r =
      complexRadialLaplacian (monopoleInnerComplexProfile c s) r := by
    unfold complexRadialLaplacian
    rw [hsp.deriv.deriv_eq, hsp.deriv_eq]
  have hD : complexRadialDilation
      (monopoleWithRemoteRadiation c Z s) r =
      complexRadialDilation (monopoleInnerComplexProfile c s) r := by
    unfold complexRadialDilation
    rw [hsp.eq_of_nhds, hsp.deriv_eq]
  unfold complexRadialRenormalizedResidual
  rw [ht, hL, hD, hsp.eq_of_nhds]
  ring

end HBL.TypeIIDynamicSelection
