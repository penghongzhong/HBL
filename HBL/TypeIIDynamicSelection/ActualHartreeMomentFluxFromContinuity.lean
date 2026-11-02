import HBL.TypeIIDynamicSelection.ActualMomentTransportGain
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# HBL original 2.12: selected Hartree radiation's RELATIVE moment flux

The previous genuine PDE cutoff estimate contains a relative physical
moment-velocity factor |m_0'(t)|/m_0(t).  It must not be assigned a
small time order without proof.

For ONE fixed selected genuine regular Hartree trajectory, positivity
of its terminal quartic moment and continuity of the moment and its
actual Hartree-PDE radial Laplacian flux imply a UNIFORM positive
moment lower bound and a UNIFORM upper bound for the relative flux
on a real physical-time neighborhood of T.

When the true physical clock t(s) tends to T, the SAME bounds hold
eventually for all large renormalized times.  The proof uses genuine
continuity/terminal positivity, not an assumed relative-moment
source bound, a fixed Type-II exponent, or a fictitious cutoff support.
The separate genuine high-regularity Hartree flow must supply the
continuity premises.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole

/-- Positivity and continuity of the actual physical quartic moment,
plus continuity of its genuine Hartree PDE Laplacian flux, yield
the missing relative moment derivative bound automatically near T.
No upper or lower Type-II blowup rate is assumed. -/
theorem actual_Hartree_positive_terminal_moment_bounds_relative_PDE_flux
    (z : ℝ → ℝ → ℂ) (T : ℝ)
    (hm : ContinuousAt (fun t : ℝ => radialPhysicalQuarticMoment (z t)) T)
    (hflux : ContinuousAt (fun t : ℝ => actualMomentLaplacianFlux (z t)) T)
    (hmT : 0 < radialPhysicalQuarticMoment (z T)) :
    ∃ J : ℝ, 0 < J ∧
      ∀ᶠ t in 𝓝 T,
        0 < radialPhysicalQuarticMoment (z t) ∧
        |actualMomentLaplacianFlux (z t)| ≤
          J * radialPhysicalQuarticMoment (z t) := by
  let m : ℝ → ℝ := fun t => radialPhysicalQuarticMoment (z t)
  let flux : ℝ → ℝ := fun t => actualMomentLaplacianFlux (z t)
  change ContinuousAt m T at hm
  change ContinuousAt flux T at hflux
  change 0 < m T at hmT
  let M : ℝ := |flux T| + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  let J : ℝ := 2 * M / m T
  have hJ : 0 < J := div_pos (by dsimp [M]; positivity) hmT
  have hhalf : m T / 2 < m T := by linarith
  have hhi : flux T < M := by
    dsimp [M]
    linarith [le_abs_self (flux T)]
  have hlo : -M < flux T := by
    dsimp [M]
    linarith [neg_le_abs (flux T)]
  have heventM : ∀ᶠ t in 𝓝 T, m T / 2 < m t :=
    hm.tendsto.eventually (Ioi_mem_nhds hhalf)
  have heventHi : ∀ᶠ t in 𝓝 T, flux t < M :=
    hflux.tendsto.eventually (Iio_mem_nhds hhi)
  have heventLo : ∀ᶠ t in 𝓝 T, -M < flux t :=
    hflux.tendsto.eventually (Ioi_mem_nhds hlo)
  refine ⟨J,hJ,?_⟩
  filter_upwards [heventM, heventHi, heventLo] with t hp hthi htlo
  have hMbound : M < J * m t := by
    have hsmall : 2 * M * (m T / 2) < 2 * M * m t :=
      mul_lt_mul_of_pos_left hp (by positivity)
    have hmul : M * m T < (2 * M) * m t := by
      nlinarith [hsmall]
    have hdiv : M < (2 * M * m t) / m T :=
      (lt_div_iff₀ hmT).2 hmul
    calc
      M < (2 * M * m t) / m T := hdiv
      _ = J * m t := by dsimp [J]; ring
  have habs : |flux t| ≤ M :=
    abs_le.mpr ⟨le_of_lt htlo, le_of_lt hthi⟩
  exact ⟨by linarith, habs.trans hMbound.le⟩

/-- The same actual Hartree relative moment flux estimate holds
eventually along any REAL physical clock converging to T, including
the clock prescribed by ell_s=-b ell, time_s=ell². -/
theorem actual_Hartree_terminal_flux_bounded_on_physical_clock
    (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ) (T : ℝ)
    (hm : ContinuousAt (fun t : ℝ => radialPhysicalQuarticMoment (z t)) T)
    (hflux : ContinuousAt (fun t : ℝ => actualMomentLaplacianFlux (z t)) T)
    (hmT : 0 < radialPhysicalQuarticMoment (z T))
    (hTime : Tendsto time atTop (𝓝 T)) :
    ∃ J : ℝ, 0 < J ∧
      ∀ᶠ s in atTop,
        0 < radialPhysicalQuarticMoment (z (time s)) ∧
        |actualMomentLaplacianFlux (z (time s))| ≤
          J * radialPhysicalQuarticMoment (z (time s)) := by
  obtain ⟨J,hJ,hEvent⟩ :=
    actual_Hartree_positive_terminal_moment_bounds_relative_PDE_flux
      z T hm hflux hmT
  exact ⟨J,hJ,hTime.eventually hEvent⟩

end HBL.TypeIIDynamicSelection
