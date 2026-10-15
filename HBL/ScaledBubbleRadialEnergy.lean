import HBL.TransportedEnergyRecenter
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
The stationary bubble at an arbitrary logarithmic scale in the concrete
radial dot-H1 model.

For a0 = log lambda0 define
  W[a0](r) = exp(a0/2) W(exp(a0) r).
Then T_{exp(a0),0} W[a0] = W.  In the energy coordinate q=(r f)',
  q[a0](r) = exp(a0/2) q_W(exp(a0) r),
which has the same L2 scaling and therefore lies in the full half-line
radial energy space.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Stationary bubble at logarithmic scale a0. -/
def bubbleAtLogScale (a₀ r : ℝ) : ℝ :=
  Real.exp (a₀ / 2) * bubble (Real.exp a₀ * r)

/-- The scaled bubble remains C1. -/
theorem bubbleAtLogScale_contDiff (a₀ : ℝ) :
    ContDiff ℝ 1 (bubbleAtLogScale a₀) := by
  change ContDiff ℝ 1 (fun r : ℝ =>
    Real.exp (a₀ / 2) * bubble (Real.exp a₀ * r))
  fun_prop

/-- Applying the manuscript scale pullback with the base scale returns W. -/
theorem scalePullback_bubbleAtLogScale_self
    (a₀ r : ℝ) :
    scalePullback (bubbleAtLogScale a₀) a₀ r = bubble r := by
  unfold scalePullback bubbleAtLogScale
  have harg :
      Real.exp a₀ * (Real.exp (-a₀) * r) = r := by
    calc
      Real.exp a₀ * (Real.exp (-a₀) * r) =
          (Real.exp a₀ * Real.exp (-a₀)) * r := by ring
      _ = r := by
        rw [← Real.exp_add]
        simp
  rw [harg]
  have hcoef :
      Real.exp (-a₀ / 2) * Real.exp (a₀ / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcoef, one_mul]

/-- Closed energy-coordinate derivative of the scaled bubble. -/
def scaledBubbleRadialEnergyDerivative (a₀ r : ℝ) : ℝ :=
  Real.exp (a₀ / 2) *
    bubbleRadialEnergyDerivative (Real.exp a₀ * r)

/-- Exact derivative formula for U W[a0]. -/
theorem radialU_bubbleAtLogScale_hasDerivAt
    (a₀ r : ℝ) :
    HasDerivAt (radialU (bubbleAtLogScale a₀))
      (scaledBubbleRadialEnergyDerivative a₀ r) r := by
  have harg :
      HasDerivAt (fun x : ℝ => Real.exp a₀ * x)
        (Real.exp a₀) r := by
    simpa using (hasDerivAt_id r).const_mul (Real.exp a₀)
  have hcore :
      HasDerivAt
        (fun x : ℝ => radialU bubble (Real.exp a₀ * x))
        (bubbleRadialEnergyDerivative (Real.exp a₀ * r) *
          Real.exp a₀) r :=
    (radialU_bubble_hasDerivAt_closed (Real.exp a₀ * r)).comp r harg
  have hmul :=
    hcore.const_mul (Real.exp (-a₀ / 2))
  have heq :
      (fun x : ℝ =>
        Real.exp (-a₀ / 2) *
          radialU bubble (Real.exp a₀ * x)) =
      radialU (bubbleAtLogScale a₀) := by
    funext x
    unfold radialU bubbleAtLogScale
    have hc :
        Real.exp (-a₀ / 2) * Real.exp a₀ =
          Real.exp (a₀ / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hc]
    ring
  rw [heq] at hmul
  convert hmul using 1
  unfold scaledBubbleRadialEnergyDerivative
  have hc :
      Real.exp (-a₀ / 2) * Real.exp a₀ =
        Real.exp (a₀ / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hc]
  ring

theorem radialU_bubbleAtLogScale_deriv
    (a₀ r : ℝ) :
    deriv (radialU (bubbleAtLogScale a₀)) r =
      scaledBubbleRadialEnergyDerivative a₀ r :=
  (radialU_bubbleAtLogScale_hasDerivAt a₀ r).deriv

/-- The scaled energy derivative is continuous. -/
theorem scaledBubbleRadialEnergyDerivative_continuous
    (a₀ : ℝ) :
    Continuous (scaledBubbleRadialEnergyDerivative a₀) := by
  unfold scaledBubbleRadialEnergyDerivative
  fun_prop

/-- Its square is integrable on the full real line. -/
theorem scaledBubbleRadialEnergyDerivative_sq_integrable
    (a₀ : ℝ) :
    Integrable
      (fun r : ℝ => scaledBubbleRadialEnergyDerivative a₀ r ^ 2)
      volume := by
  have hcomp :
      Integrable
        (fun r : ℝ =>
          bubbleRadialEnergyDerivative (Real.exp a₀ * r) ^ 2)
        volume :=
    bubbleRadialEnergyDerivative_sq_integrable.comp_mul_left'
      (Real.exp_ne_zero a₀)
  have hmul :=
    hcomp.const_mul (Real.exp a₀)
  convert hmul using 1
  funext r
  unfold scaledBubbleRadialEnergyDerivative
  have hs :
      Real.exp (a₀ / 2) ^ 2 = Real.exp a₀ := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hs]

/-- Hence the scaled bubble gives a genuine full radial dot-H1 vector. -/
theorem radialU_bubbleAtLogScale_deriv_memLp
    (a₀ : ℝ) :
    MemLp (deriv (radialU (bubbleAtLogScale a₀))) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hclosed :
      (deriv (radialU (bubbleAtLogScale a₀))) =
        scaledBubbleRadialEnergyDerivative a₀ := by
    funext r
    exact radialU_bubbleAtLogScale_deriv a₀ r
  rw [hclosed]
  have hmeas :
      AEStronglyMeasurable
        (scaledBubbleRadialEnergyDerivative a₀)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (scaledBubbleRadialEnergyDerivative_continuous a₀).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  exact (scaledBubbleRadialEnergyDerivative_sq_integrable a₀).integrableOn

/-- The arbitrary-scale stationary bubble as a vector of RadialDotH1. -/
def bubbleAtLogScaleRadialDotH1 (a₀ : ℝ) : RadialDotH1 :=
  smoothToRadialDotH1 (bubbleAtLogScale a₀)
    (radialU_bubbleAtLogScale_deriv_memLp a₀)

/-- At scale zero this is exactly the standard bubble vector. -/
theorem bubbleAtLogScaleRadialDotH1_zero :
    bubbleAtLogScaleRadialDotH1 0 =
      fullBubbleRadialEnergyL2 := by
  unfold bubbleAtLogScaleRadialDotH1
  have hfun : bubbleAtLogScale 0 = bubble := by
    funext r
    simp [bubbleAtLogScale]
  subst hfun
  exact smoothBubbleToRadialDotH1_eq

end HBL.Modulation
