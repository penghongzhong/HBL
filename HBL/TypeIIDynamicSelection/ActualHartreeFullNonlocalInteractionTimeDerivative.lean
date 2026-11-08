import HBL.TypeIIDynamicSelection.ActualHartreeMixedRieszTimeDerivative
import HBL.TypeIIDynamicSelection.ActualHartreeLocalCubicTimeDerivative
import HBL.TypeIIDynamicSelection.ActualOneLayerRadiationPDECancellation
import Mathlib.Tactic

/-!
# FULL original quartic Hartree interaction: exact three-potential time derivative

The one nonlocal physical PDE source is exactly
  P_mix C(V+z) + P_z [C(V+z)-C(z)] + P_V [C(V+z)-C(V)]
where P are the original radial inverse-square logarithmic Riesz potentials
and C(u)=|u|^2 u is the original local cubic multiplier.

This file composes the genuine time derivatives of ALL THREE physical
Riesz components and the three actual complex cubic multipliers.
No cross term is dropped, and no HasDerivAt of the complete nonlinear
interaction is assumed. The three potential time derivatives are explicit
inputs that can be furnished by the proved original Riesz differentiation
lemmas from the physical V_s and z_s with original kernel integrability
and domination.

This is the full fixed-observer nonlinear time-product formula. It is
not a proof that a rough energy-class Hartree orbit automatically
satisfies the required dominated original potential derivatives, nor
does it include moving spatial observation coordinates or Kummer basis.
The full O(s^(-9/4)) weighted four-piece residual remains open.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeFullInteractionTimeVelocity
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (pMixDot pZDot pVDot : ℝ)
    (s r : ℝ) : ℂ :=
  let total : ℂ := (V s r : ℂ) + z s r
  let dTotal : ℂ := (dV s r : ℂ) + dz s r
  let v : ℂ := (V s r : ℂ)
  let dv : ℂ := (dV s r : ℂ)
  let qMix : ℝ :=
    radialHartreePotential (actualWholeRadiationMixedQuartic (V s) (z s)) r
  let qZ : ℝ := radialHartreePotential (fun rho => ‖z s rho‖ ^ 4) r
  let qV : ℝ := radialHartreePotential (fun rho => ‖(V s rho : ℂ)‖ ^ 4) r
  let Ctotal : ℂ := actualWholeRadiationLocalCubic
    (fun rho => (V s rho : ℂ) + z s rho) r
  let Cz : ℂ := actualWholeRadiationLocalCubic (z s) r
  let Cv : ℂ := actualWholeRadiationLocalCubic
    (fun rho => (V s rho : ℂ)) r
  ((pMixDot : ℂ) * Ctotal +
    (qMix : ℂ) * actualHartreeLocalCubicTimeVelocity total dTotal) +
  ((pZDot : ℂ) * (Ctotal - Cz) +
    (qZ : ℂ) *
      (actualHartreeLocalCubicTimeVelocity total dTotal -
        actualHartreeLocalCubicTimeVelocity (z s r) (dz s r))) +
  ((pVDot : ℂ) * (Ctotal - Cv) +
    (qV : ℂ) *
      (actualHartreeLocalCubicTimeVelocity total dTotal -
        actualHartreeLocalCubicTimeVelocity v dv))

/-- Exact one-source derivative: the THREE original physical Riesz
potential derivatives and the two primitive physical field velocities
are sufficient; no derivative of the full interaction is postulated. -/
theorem actual_Hartree_full_nonlocal_interaction_time_derivative
    (V dV : ℝ → ℝ → ℝ) (z dz : ℝ → ℝ → ℂ)
    (s r pMixDot pZDot pVDot : ℝ)
    (hV : HasDerivAt (fun t => V t r) (dV s r) s)
    (hZ : HasDerivAt (fun t => z t r) (dz s r) s)
    (hMix : HasDerivAt
      (fun t => radialHartreePotential
        (actualWholeRadiationMixedQuartic (V t) (z t)) r)
      pMixDot s)
    (hPure : HasDerivAt
      (fun t => radialHartreePotential
        (fun rho => ‖z t rho‖ ^ 4) r)
      pZDot s)
    (hCore : HasDerivAt
      (fun t => radialHartreePotential
        (fun rho => ‖(V t rho : ℂ)‖ ^ 4) r)
      pVDot s) :
    HasDerivAt
      (fun t => actualOneLayerInteractionOnly V z t r)
      (actualHartreeFullInteractionTimeVelocity
        V dV z dz pMixDot pZDot pVDot s r) s := by
  let total : ℝ → ℝ → ℂ :=
    fun t rho => (V t rho : ℂ) + z t rho
  let core : ℝ → ℝ → ℂ :=
    fun t rho => (V t rho : ℂ)
  have hvC : HasDerivAt (fun t => core t r) (dV s r : ℂ) s := by
    simpa only [core] using hV.ofReal_comp
  have htC : HasDerivAt (fun t => total t r)
      ((dV s r : ℂ) + dz s r) s := by
    convert hvC.add hZ using 1
  have hCt :=
    actual_Hartree_local_cubic_multiplier_time_derivative
      total s r ((dV s r : ℂ) + dz s r) htC
  have hCz :=
    actual_Hartree_local_cubic_multiplier_time_derivative
      z s r (dz s r) hZ
  have hCv :=
    actual_Hartree_local_cubic_multiplier_time_derivative
      core s r (dV s r : ℂ) hvC
  have hPM : HasDerivAt
      (fun t => (radialHartreePotential
        (actualWholeRadiationMixedQuartic (V t) (z t)) r : ℂ))
        (pMixDot : ℂ) s := hMix.ofReal_comp
  have hPZ : HasDerivAt
      (fun t => (radialHartreePotential
        (fun rho => ‖z t rho‖ ^ 4) r : ℂ))
        (pZDot : ℂ) s := hPure.ofReal_comp
  have hPV : HasDerivAt
      (fun t => (radialHartreePotential
        (fun rho => ‖(V t rho : ℂ)‖ ^ 4) r : ℂ))
        (pVDot : ℂ) s := hCore.ofReal_comp
  have hFull :=
    ((hPM.mul hCt).add (hPZ.mul (hCt.sub hCz))).add
      (hPV.mul (hCt.sub hCv))
  convert hFull using 1
  · funext t
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
      actualOneLayerInteractionOnly, core, total]
  · unfold actualHartreeFullInteractionTimeVelocity
    dsimp [core, total]
    ring

end HBL.TypeIIDynamicSelection
