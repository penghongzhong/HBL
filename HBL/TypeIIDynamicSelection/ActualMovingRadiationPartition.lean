import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import HBL.TypeIIDynamicSelection.ActualMovingRemoteResidual
import Mathlib.Tactic

/-!
# One physical off-terminal Hartree radiation, with its TRUE moving split

Unlike a terminal bump, the actual Schrödinger/Hartree radiation does
not retain compact support at earlier times. Apply the manuscript's
genuine moving radial overlap cutoff to the WHOLE solution instead:

  Z_inner(s,r) = chi_inner(R(s),r) Z(s,r)
  Z_remote(s,r) = Z(s,r) - Z_inner(s,r).

This partition is exact for each s, and Z_remote vanishes identically
on r<=R(s), even though Z itself need not. Continuity of R(s) alone
then proves local time/spatial derivative cancellation in the core.
Consequently the FULL nonlocal Hartree renormalized residual of
V+Z differs from that of V+Z_inner by exactly its true nonlinear
Hartree interaction, with no unphysical persistence-of-support
assumption and no inserted source order or blowup exponent.

It is not the final three-domain correction or the Kummer/remote
overlap matching in original manuscript environment 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Inner part of the ACTUAL complex regular Hartree radiation,
with the same variable radius and overlap cutoff as original 2.12. -/
def actualOneLayerInnerRadiation
    (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  actualOneLayerInnerOverlapCutoff (R t) r * Z t r

/-- Exterior part of the SAME physical radiation, not a separately
chosen compact-support solution of the nonlinear Schrödinger flow. -/
def actualOneLayerRemoteRadiation
    (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  Z t r - actualOneLayerInnerRadiation R Z t r

/-- The interior complex profile and the original uncut profile. -/
def actualOneLayerWithInnerRadiation
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ)
    (Z : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  (V t r : ℂ) + actualOneLayerInnerRadiation R Z t r

def actualOneLayerWithWholeRadiation
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (t r : ℝ) : ℂ :=
  (V t r : ℂ) + Z t r

/-- No change to the physical radiation: the split is an EXACT sum
at all times and radii, with the SAME nonlocal Hartree field. -/
theorem actual_one_layer_true_radiation_partition_exact
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ)
    (Z : ℝ → ℝ → ℂ) (t r : ℝ) :
    actualOneLayerWithWholeRadiation V Z t r =
      actualOneLayerWithInnerRadiation V R Z t r +
        actualOneLayerRemoteRadiation R Z t r := by
  unfold actualOneLayerWithWholeRadiation actualOneLayerWithInnerRadiation
    actualOneLayerRemoteRadiation
  ring

/-- The actual smooth exterior cutoff gives a moving support condition
for the constructed Z_remote. NO support condition is imposed on
the Hartree flow Z itself, at the terminal or any earlier time. -/
theorem actual_one_layer_true_remote_radiation_zero_on_moving_core
    (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (hR : ∀ t : ℝ, 0 < R t) :
    ∀ t rho : ℝ, rho ≤ R t →
      actualOneLayerRemoteRadiation R Z t rho = 0 := by
  intro t rho hr
  have hquot : rho / R t ≤ 1 := (div_le_one (hR t)).2 hr
  have hcut : cutoff (rho / R t) = 0 :=
    cutoff_zero_of_le_one (rho / R t) hquot
  have hchi : actualOneLayerInnerOverlapCutoff (R t) rho = 1 := by
    simp [actualOneLayerInnerOverlapCutoff, hcut]
  simp [actualOneLayerRemoteRadiation, actualOneLayerInnerRadiation, hchi]

/-- Local-in-time equality of the TRUE WHOLE Hartree profile and
its interior-only profile at a point strictly inside the moving
transition: it uses the exterior support of the CONSTRUCTED cutoff
piece and continuity of R, rather than support persistence for Z. -/
theorem actual_one_layer_whole_inner_eventually_eq
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    {s r : ℝ} (hRc : ContinuousAt R s)
    (hr : r < R s) (hR : ∀ t : ℝ, 0 < R t) :
    (fun t => actualOneLayerWithWholeRadiation V Z t r) =ᶠ[𝓝 s]
      (fun t => actualOneLayerWithInnerRadiation V R Z t r) := by
  have hSupport :=
    actual_one_layer_true_remote_radiation_zero_on_moving_core R Z hR
  filter_upwards [moving_remote_cutoff_eventually_zero
    R (actualOneLayerRemoteRadiation R Z) hRc hr hSupport] with t ht
  rw [actual_one_layer_true_radiation_partition_exact V R Z t r, ht, add_zero]

/-- Original SAME-equation remote-region identity, now for the
physical complex-core-plus-radiation instead of an abstract real
cutoff monopole. The moving cutoff's time derivative cancels EXACTLY
in the core. Only the genuine NONLOCAL Hartree interaction survives. -/
theorem actual_one_layer_true_moving_remote_residual_is_nonlinear
    (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s r : ℝ)
    (hRc : ContinuousAt R s)
    (hR : ∀ t : ℝ, 0 < R t)
    (hr : 0 < r) (hsep : 2 * r ≤ R s) :
    complexRadialRenormalizedResidual
        (actualOneLayerWithWholeRadiation V Z) b omega s r -
      complexRadialRenormalizedResidual
        (actualOneLayerWithInnerRadiation V R Z) b omega s r =
      complexRadialHartreeNonlinearity
        (actualOneLayerWithWholeRadiation V Z s) r -
      complexRadialHartreeNonlinearity
        (actualOneLayerWithInnerRadiation V R Z s) r := by
  have hrR : r < R s := by linarith
  have htLocal := actual_one_layer_whole_inner_eventually_eq
    V R Z hRc hrR hR
  have ht :
      deriv (fun t => actualOneLayerWithWholeRadiation V Z t r) s =
        deriv (fun t => actualOneLayerWithInnerRadiation V R Z t r) s :=
    htLocal.deriv_eq
  have hSp :
      actualOneLayerWithWholeRadiation V Z s =ᶠ[𝓝 r]
        actualOneLayerWithInnerRadiation V R Z s := by
    have hSupport :=
      actual_one_layer_true_remote_radiation_zero_on_moving_core R Z hR
    filter_upwards [Iio_mem_nhds hrR] with x hx
    rw [actual_one_layer_true_radiation_partition_exact V R Z s x,
      hSupport s x hx.le, add_zero]
  have hLap :
      complexRadialLaplacian (actualOneLayerWithWholeRadiation V Z s) r =
        complexRadialLaplacian
          (actualOneLayerWithInnerRadiation V R Z s) r := by
    unfold complexRadialLaplacian
    rw [hSp.deriv.deriv_eq, hSp.deriv_eq]
  have hDil :
      complexRadialDilation (actualOneLayerWithWholeRadiation V Z s) r =
        complexRadialDilation
          (actualOneLayerWithInnerRadiation V R Z s) r := by
    unfold complexRadialDilation
    rw [hSp.eq_of_nhds, hSp.deriv_eq]
  unfold complexRadialRenormalizedResidual
  rw [ht, hLap, hDil, hSp.eq_of_nhds]
  ring

end HBL.TypeIIDynamicSelection
