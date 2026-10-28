import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exceptional remote block k = -1

For the manuscript's exceptional remote phase the scalar equation is

  r g'(r) + a g(r) = F(r),

with Re(a)>1.  Its normalized solution is the integrating-factor formula

  g(r) = r^(-a) ∫_0^r rho^(a-1) F(rho) d rho.

The proof below is the actual complex-power formula, not an abstract right-inverse package.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped Interval

namespace HBL.Profile.Remote

def exceptionalIntegrand (a : ℂ) (F : ℝ → ℂ) (rho : ℝ) : ℂ :=
  (rho : ℂ) ^ (a - 1) * F rho

def exceptionalPrimitive (a : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ rho in (0 : ℝ)..r, exceptionalIntegrand a F rho

def exceptionalInverse (a : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (-a) * exceptionalPrimitive a F r

def exceptionalInverseDeriv (a : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  (-a) * (r : ℂ) ^ (-a - 1) * exceptionalPrimitive a F r +
    (r : ℂ) ^ (-a) * exceptionalIntegrand a F r

theorem exceptionalIntegrand_continuous
    (a : ℂ) (F : ℝ → ℂ) (ha : 1 < a.re) (hF : Continuous F) :
    Continuous (exceptionalIntegrand a F) := by
  have hp : 0 < (a - 1).re := by
    simpa using sub_pos.mpr ha
  exact (Complex.continuous_ofReal_cpow_const hp).mul hF

theorem exceptionalPrimitive_hasDerivAt
    (a : ℂ) (F : ℝ → ℂ) (ha : 1 < a.re) (hF : Continuous F) (r : ℝ) :
    HasDerivAt (exceptionalPrimitive a F) (exceptionalIntegrand a F r) r := by
  have hc : Continuous (exceptionalIntegrand a F) :=
    exceptionalIntegrand_continuous a F ha hF
  unfold exceptionalPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt

theorem exceptionalInverse_hasDerivAt
    (a : ℂ) (F : ℝ → ℂ) (ha : 1 < a.re) (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (exceptionalInverse a F) (exceptionalInverseDeriv a F r) r := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hp :
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-a))
        ((-a) * (r : ℂ) ^ (-a - 1)) r := by
    exact hasDerivAt_ofReal_cpow_const hr.ne'
      (neg_ne_zero.mpr ha0)
  have hI := exceptionalPrimitive_hasDerivAt a F ha hF r
  convert hp.mul hI using 1 <;>
    simp [exceptionalInverse, exceptionalInverseDeriv] <;> ring

theorem exceptionalInverse_solves
    (a : ℂ) (F : ℝ → ℂ) (ha : 1 < a.re) (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) :
    (r : ℂ) * exceptionalInverseDeriv a F r +
        a * exceptionalInverse a F r = F r := by
  have hx : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hshift :
      (r : ℂ) ^ (-a) = (r : ℂ) ^ (-a - 1) * (r : ℂ) := by
    calc
      (r : ℂ) ^ (-a) = (r : ℂ) ^ ((-a - 1) + 1) := by congr 1 <;> ring
      _ = (r : ℂ) ^ (-a - 1) * (r : ℂ) ^ (1 : ℂ) :=
        Complex.cpow_add _ _ hx
      _ = (r : ℂ) ^ (-a - 1) * (r : ℂ) := by rw [Complex.cpow_one]
  have hsource :
      (r : ℂ) * ((r : ℂ) ^ (-a) * ((r : ℂ) ^ (a - 1) * F r)) = F r := by
    have hp :
        (r : ℂ) ^ (-a) * (r : ℂ) ^ (a - 1) = (r : ℂ) ^ (-1 : ℂ) := by
      rw [← Complex.cpow_add _ _ hx]
      congr 1
      ring
    calc
      (r : ℂ) * ((r : ℂ) ^ (-a) * ((r : ℂ) ^ (a - 1) * F r)) =
          ((r : ℂ) ^ (-a) * (r : ℂ) ^ (a - 1)) * (r : ℂ) * F r := by
            ring
      _ = (r : ℂ) ^ (-1 : ℂ) * (r : ℂ) * F r := by rw [hp]
      _ = F r := by
        rw [Complex.cpow_neg_one]
        field_simp [hx]
  unfold exceptionalInverseDeriv exceptionalInverse exceptionalIntegrand
  rw [mul_add]
  rw [hsource]
  rw [hshift]
  ring

theorem exceptionalRemoteBlock_certified
    (a : ℂ) (F : ℝ → ℂ) (ha : 1 < a.re) (hF : Continuous F) :
    ∀ r : ℝ, 0 < r →
      HasDerivAt (exceptionalInverse a F) (exceptionalInverseDeriv a F r) r ∧
      (r : ℂ) * exceptionalInverseDeriv a F r +
        a * exceptionalInverse a F r = F r := by
  intro r hr
  exact ⟨exceptionalInverse_hasDerivAt a F ha hF hr,
    exceptionalInverse_solves a F ha hF hr⟩

#print axioms exceptionalIntegrand_continuous
#print axioms exceptionalPrimitive_hasDerivAt
#print axioms exceptionalInverse_hasDerivAt
#print axioms exceptionalInverse_solves
#print axioms exceptionalRemoteBlock_certified

end HBL.Profile.Remote
