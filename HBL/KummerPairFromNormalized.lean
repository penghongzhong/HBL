import HBL.KummerVariationOfParameters
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Construct a genuine Kummer fundamental pair from normalized ODE solutions

Unlike `FundamentalPair`, the candidate structure below does not assume a
nonvanishing Wronskian.  Abel's identity and an integrating factor propagate
a single nonzero normalization value to every point.  The resulting object
is then promoted to the existing `FundamentalPair` used by the annulus
variation-of-parameters inverse.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HBL.Profile.Kummer

structure CandidatePair where
  a : ℝ → ℂ
  b : ℝ → ℂ
  phi : ℝ → ℂ
  psi : ℝ → ℂ
  dphi : ℝ → ℂ
  dpsi : ℝ → ℂ
  ddphi : ℝ → ℂ
  ddpsi : ℝ → ℂ
  a_continuous : Continuous a
  phi_hasDeriv : ∀ z, HasDerivAt phi (dphi z) z
  psi_hasDeriv : ∀ z, HasDerivAt psi (dpsi z) z
  dphi_hasDeriv : ∀ z, HasDerivAt dphi (ddphi z) z
  dpsi_hasDeriv : ∀ z, HasDerivAt dpsi (ddpsi z) z
  phi_homogeneous : ∀ z, ddphi z + a z * dphi z + b z * phi z = 0
  psi_homogeneous : ∀ z, ddpsi z + a z * dpsi z + b z * psi z = 0

def candidateWronskian (K : CandidatePair) (z : ℝ) : ℂ :=
  K.phi z * K.dpsi z - K.dphi z * K.psi z

theorem candidateWronskian_hasDerivAt
    (K : CandidatePair) (z : ℝ) :
    HasDerivAt (candidateWronskian K)
      (-(K.a z) * candidateWronskian K z) z := by
  have hprod1 :=
    (K.phi_hasDeriv z).mul (K.dpsi_hasDeriv z)
  have hprod2 :=
    (K.dphi_hasDeriv z).mul (K.psi_hasDeriv z)
  have h := hprod1.sub hprod2
  convert h using 1
  · rfl
  · unfold candidateWronskian
    have hphi := K.phi_homogeneous z
    have hpsi := K.psi_homogeneous z
    have hddphi :
        K.ddphi z =
          -(K.a z * K.dphi z + K.b z * K.phi z) := by
      linear_combination hphi
    have hddpsi :
        K.ddpsi z =
          -(K.a z * K.dpsi z + K.b z * K.psi z) := by
      linear_combination hpsi
    rw [hddphi, hddpsi]
    ring

def candidateAbelPrimitive
    (K : CandidatePair) (z0 z : ℝ) : ℂ :=
  ∫ t in z0..z, K.a t

def candidateAbelFactor
    (K : CandidatePair) (z0 z : ℝ) : ℂ :=
  Complex.exp (candidateAbelPrimitive K z0 z)

def candidateAbelInvariant
    (K : CandidatePair) (z0 z : ℝ) : ℂ :=
  candidateAbelFactor K z0 z * candidateWronskian K z

theorem candidateAbelPrimitive_hasDerivAt
    (K : CandidatePair) (z0 z : ℝ) :
    HasDerivAt (candidateAbelPrimitive K z0) (K.a z) z := by
  unfold candidateAbelPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (K.a_continuous.intervalIntegrable z0 z)
    K.a_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    K.a_continuous.continuousAt

theorem candidateAbelFactor_hasDerivAt
    (K : CandidatePair) (z0 z : ℝ) :
    HasDerivAt (candidateAbelFactor K z0)
      (candidateAbelFactor K z0 z * K.a z) z := by
  have h := (candidateAbelPrimitive_hasDerivAt K z0 z).cexp
  simpa only [candidateAbelFactor] using h

theorem candidateAbelInvariant_hasDerivAt_zero
    (K : CandidatePair) (z0 z : ℝ) :
    HasDerivAt (candidateAbelInvariant K z0) 0 z := by
  have h :=
    (candidateAbelFactor_hasDerivAt K z0 z).mul
      (candidateWronskian_hasDerivAt K z)
  convert h using 1
  · rfl
  · unfold candidateAbelInvariant
    ring

theorem candidateAbelInvariant_eq
    (K : CandidatePair) (z0 x y : ℝ) :
    candidateAbelInvariant K z0 y =
      candidateAbelInvariant K z0 x := by
  have hftc :
      (∫ _t in x..y, (0 : ℂ)) =
        candidateAbelInvariant K z0 y -
          candidateAbelInvariant K z0 x := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _hz => candidateAbelInvariant_hasDerivAt_zero K z0 z)
      intervalIntegrable_zero
  exact sub_eq_zero.mp (by simpa using hftc.symm)

theorem candidateAbelFactor_ne_zero
    (K : CandidatePair) (z0 z : ℝ) :
    candidateAbelFactor K z0 z ≠ 0 := by
  unfold candidateAbelFactor
  exact Complex.exp_ne_zero _

theorem candidateWronskian_ne_of_normalized
    (K : CandidatePair) (z0 : ℝ)
    (hW0 : candidateWronskian K z0 ≠ 0) :
    ∀ z : ℝ, candidateWronskian K z ≠ 0 := by
  intro z hW
  have hconst := candidateAbelInvariant_eq K z0 z0 z
  unfold candidateAbelInvariant at hconst
  rw [hW, mul_zero] at hconst
  have hfac0 : candidateAbelFactor K z0 z0 ≠ 0 :=
    candidateAbelFactor_ne_zero K z0 z0
  exact (mul_ne_zero hfac0 hW0) hconst.symm

def CandidatePair.toFundamentalPair
    (K : CandidatePair) (z0 : ℝ)
    (hW0 : candidateWronskian K z0 ≠ 0) :
    FundamentalPair where
  a := K.a
  b := K.b
  phi := K.phi
  psi := K.psi
  dphi := K.dphi
  dpsi := K.dpsi
  ddphi := K.ddphi
  ddpsi := K.ddpsi
  phi_hasDeriv := K.phi_hasDeriv
  psi_hasDeriv := K.psi_hasDeriv
  dphi_hasDeriv := K.dphi_hasDeriv
  dpsi_hasDeriv := K.dpsi_hasDeriv
  phi_homogeneous := K.phi_homogeneous
  psi_homogeneous := K.psi_homogeneous
  wronskian_ne := candidateWronskian_ne_of_normalized K z0 hW0

theorem toFundamentalPair_wronskian
    (K : CandidatePair) (z0 : ℝ)
    (hW0 : candidateWronskian K z0 ≠ 0) (z : ℝ) :
    wronskian (K.toFundamentalPair z0 hW0) z =
      candidateWronskian K z := rfl

#print axioms candidateWronskian_hasDerivAt
#print axioms candidateAbelInvariant_eq
#print axioms candidateWronskian_ne_of_normalized
#print axioms CandidatePair.toFundamentalPair
#print axioms toFundamentalPair_wronskian

end HBL.Profile.Kummer
