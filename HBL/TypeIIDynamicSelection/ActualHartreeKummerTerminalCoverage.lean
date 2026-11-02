import HBL.TypeIIDynamicSelection.ActualHartreeKummerClockIdentity
import Mathlib.Tactic

/-!
# Original HBL 2.12: eventual physical Kummer annulus coverage without an assumed rate

The original 3D Hartree physical clock satisfies time(s) -> T and time(s)<T,
while q(s)=(T-time(s))/ell(s)^2 and ell(s)>0. If the positive true
physical radiation quartic moment is eventually bounded above, then
the ORIGINAL Kummer cutoff radius Rz = 4/(kappa_H*m(s)*sqrt(T-time(s)))
eventually exceeds ANY fixed prescribed Kummer annulus.

This is a genuine quantified atTop result, not a guessed asymptotic
Type-II concentration exponent. The eventual moment input is derived
separately from the physical PDE by the strictly audited one-orbit
terminal-moment theorem. No axiom and no invocation of a global Kummer
C1 match are present.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Terminal physical-time convergence and an eventual positive bounded
actual moment force all fixed Kummer annuli inside the cutoff when
expressed using the EXACT physical clock tau=T-time(s). -/
theorem actual_Hartree_eventual_fixed_Kummer_annulus_covered
    (m time : ℝ → ℝ) (T M center d : ℝ)
    (hM : 0 < M) (hcenter : 0 < center + d)
    (hTime : Tendsto time atTop (𝓝 T))
    (hBefore : ∀ᶠ s in atTop, time s < T)
    (hMoment : ∀ᶠ s in atTop, 0 < m s ∧ m s ≤ M) :
    ∀ᶠ s in atTop,
      center + d ≤ actualHartreeMomentCutoffRadius
        (Real.sqrt (T - time s)) (m s) := by
  have hk : 0 < hartreeKappa := by
    unfold hartreeKappa
    positivity
  let delta : ℝ := 4 / (hartreeKappa * M * (center + d))
  have hDelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hTau : Tendsto (fun s : ℝ => T - time s) atTop (𝓝 (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℝ => T) atTop (𝓝 T) :=
      tendsto_const_nhds
    simpa only [sub_self] using hConst.sub hTime
  have hClose : ∀ᶠ s in atTop, T - time s < delta ^ 2 :=
    hTau.eventually (Iio_mem_nhds (sq_pos_of_pos hDelta))
  filter_upwards [hClose, hBefore, hMoment] with s hs hpre hm
  have htau : 0 < T - time s := sub_pos.mpr hpre
  have hSqrt : Real.sqrt (T - time s) ≤ delta := by
    have hSquare :
        (Real.sqrt (T - time s)) ^ 2 < delta ^ 2 := by
      rw [Real.sq_sqrt htau.le]
      exact hs
    nlinarith [Real.sqrt_nonneg (T - time s)]
  exact actual_Hartree_moment_cutoff_covers_Kummer_annulus
    (Real.sqrt (T - time s)) (m s) M center d
    (Real.sqrt_pos.mpr htau) hm.1 hm.2 hcenter hSqrt

/-- The eventual coverage applies to the ACTUAL Kummer radius
in the self-similar z coordinate, without assuming a Type-II rate:
the physical clock identity eliminates the unknown ell(s). -/
theorem actual_Hartree_eventual_original_Kummer_coordinate_covered
    (ell q m time : ℝ → ℝ) (T M center d : ℝ)
    (hM : 0 < M) (hcenter : 0 < center + d)
    (hTime : Tendsto time atTop (𝓝 T))
    (hBefore : ∀ᶠ s in atTop, time s < T)
    (hEll : ∀ᶠ s in atTop, 0 < ell s)
    (hClock : ∀ᶠ s in atTop,
      q s = (T - time s) / (ell s) ^ 2)
    (hMoment : ∀ᶠ s in atTop, 0 < m s ∧ m s ≤ M) :
    ∀ᶠ s in atTop,
      center + d ≤ actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s) (m s) := by
  have hCover :=
    actual_Hartree_eventual_fixed_Kummer_annulus_covered
      m time T M center d hM hcenter hTime hBefore hMoment
  filter_upwards [hCover, hBefore, hEll, hClock, hMoment] with s hcov hpre hell hclock hm
  have htau : 0 < T - time s := sub_pos.mpr hpre
  have hEq := actual_Hartree_Kummer_cutoff_true_physical_clock
    (ell s) (T - time s) (m s) hell htau hm.1
  have hRad :
      actualHartreeMomentCutoffRadius
        (Real.sqrt (T - time s)) (m s) =
        4 / (hartreeKappa * m s * Real.sqrt (T - time s)) := by
    unfold actualHartreeMomentCutoffRadius
    congr 1
    ring
  calc
    center + d ≤ actualHartreeMomentCutoffRadius
        (Real.sqrt (T - time s)) (m s) := hcov
    _ = 4 / (hartreeKappa * m s * Real.sqrt (T - time s)) := hRad
    _ = actualHartreeKummerCoordinateCutoffRadius
        (ell s) (q s) (m s) := by
      rw [hclock]
      exact hEq.symm

end HBL.TypeIIDynamicSelection
