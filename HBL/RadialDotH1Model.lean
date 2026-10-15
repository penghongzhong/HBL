import HBL.FullBubbleRadialEnergy
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
Radial homogeneous H1 in the half-line energy-coordinate realization.

For radial three-dimensional profiles the conjugation U f(r)=r f(r)
identifies the reduced homogeneous gradient energy with the half-line L2
coordinate q=(U f)'.  Accordingly we use FullRadialEnergyL2 as the precise
coordinate model of real radial dot-H1, and a product of two copies for
complex-valued radial data.

This module proves that every smooth profile with finite full radial energy
maps into this model, that restriction agrees with the already verified
finite-radius coordinate, and that the full transported dual acts exactly as
the manuscript's transported scalar threshold integral on that smooth core.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Real radial homogeneous H1, represented by q=(r f)' in L2(0,infinity).
The omitted angular factor 4*pi is a fixed positive norm factor and does not
change the energy topology. -/
abbrev RadialDotH1 : Type := FullRadialEnergyL2

/-- Complex radial homogeneous H1 as real and imaginary energy coordinates. -/
abbrev ComplexRadialDotH1 : Type := RadialDotH1 × RadialDotH1

/-- Full radial energy coordinate of a smooth profile known to have finite
half-line L2 energy. -/
def smoothToRadialDotH1
    (f : ℝ → ℝ)
    (hmem : MemLp (deriv (radialU f)) 2
      (volume.restrict (Ioi (0 : ℝ)))) :
    RadialDotH1 :=
  hmem.toLp (deriv (radialU f))

/-- The full smooth energy coordinate agrees a.e. with the classical
derivative of U f. -/
theorem smoothToRadialDotH1_ae
    (f : ℝ → ℝ)
    (hmem : MemLp (deriv (radialU f)) 2
      (volume.restrict (Ioi (0 : ℝ)))) :
    (smoothToRadialDotH1 f hmem : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] deriv (radialU f) := by
  unfold smoothToRadialDotH1
  exact hmem.coeFn_toLp

/-- Restricting a smooth full radial energy coordinate to (0,R) gives
exactly the finite-radius energy vector used in the modulation proof. -/
theorem smoothToRadialDotH1_restrict
    (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hmem : MemLp (deriv (radialU f)) 2
      (volume.restrict (Ioi (0 : ℝ)))) :
    fullToFiniteRadialEnergy R (smoothToRadialDotH1 f hmem) =
      radialUDerivativeL2 R hR f hf := by
  apply Lp.ext
  let μR : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  let μFull : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hμ : μR ≤ μFull := by
    simpa [μR, μFull] using finiteRadialMeasure_le_full R
  have hac : μR ≪ μFull :=
    Measure.absolutelyContinuous_of_le hμ
  have hfull :
      (smoothToRadialDotH1 f hmem : ℝ → ℝ) =ᵐ[μFull]
        deriv (radialU f) := by
    simpa [μFull] using smoothToRadialDotH1_ae f hmem
  have hfullR :
      (smoothToRadialDotH1 f hmem : ℝ → ℝ) =ᵐ[μR]
        deriv (radialU f) :=
    hac.ae_eq hfull
  have hrestrict :=
    fullToFiniteRadialEnergy_ae R (smoothToRadialDotH1 f hmem)
  have hfinite :=
    radialUDerivativeL2_ae R hR f hf
  filter_upwards [hrestrict, hfullR, hfinite] with r hr hfr hfin
  rw [hr, hfr, hfin]

/-- On the smooth finite-energy radial core, the full Hilbert dual is
exactly the transported scalar threshold integral used to represent
ell(T_{lambda,0} f). -/
theorem fullTransportedEnergyThresholdDual_on_smoothCore
    (R : ℝ) (hR : 0 ≤ R)
    (zeta f : ℝ → ℝ)
    (hzeta : ContDiff ℝ 1 zeta)
    (hf : ContDiff ℝ 1 f)
    (hmem : MemLp (deriv (radialU f)) 2
      (volume.restrict (Ioi (0 : ℝ))))
    (a : ℝ) :
    fullTransportedEnergyThresholdDual R hR zeta hzeta a
        (smoothToRadialDotH1 f hmem) =
      transportedRadialTestIntegral R zeta f a := by
  rw [fullTransportedEnergyThresholdDual_apply]
  rw [smoothToRadialDotH1_restrict R hR f hf hmem]
  exact transportedEnergyThresholdDual_on_radialCore
    R hR zeta f hzeta hf a

/-- The explicit stationary bubble in the dot-H1 coordinate model is the
same vector previously constructed analytically. -/
theorem smoothBubbleToRadialDotH1_eq :
    smoothToRadialDotH1 bubble
      (by
        simpa [radialU_bubble_deriv_closed] using
          bubbleRadialEnergyDerivative_memLp) =
      fullBubbleRadialEnergyL2 := by
  apply Lp.ext
  filter_upwards [
    smoothToRadialDotH1_ae bubble
      (by
        simpa [radialU_bubble_deriv_closed] using
          bubbleRadialEnergyDerivative_memLp),
    bubbleRadialEnergyDerivative_memLp.coeFn_toLp
  ] with r h1 h2
  rw [h1, h2, radialU_bubble_deriv_closed]

end HBL.Modulation
