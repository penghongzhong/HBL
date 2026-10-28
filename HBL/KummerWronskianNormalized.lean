import HBL.KummerWronskianAbel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Integrated Abel invariant for the Kummer Wronskian

For a C2 fundamental pair and continuous first-derivative coefficient a,
the integrating factor exp(∫a) times the Wronskian is constant.  Hence
nonvanishing at one normalization point propagates to every point.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HBL.Profile.Kummer

def abelPrimitive
    (K : FundamentalPair) (z0 z : ℝ) : ℂ :=
  ∫ t in z0..z, K.a t

def abelFactor
    (K : FundamentalPair) (z0 z : ℝ) : ℂ :=
  Complex.exp (abelPrimitive K z0 z)

def abelInvariant
    (K : FundamentalPair) (z0 z : ℝ) : ℂ :=
  abelFactor K z0 z * wronskian K z

theorem abelPrimitive_hasDerivAt
    (K : FundamentalPair) (ha : Continuous K.a)
    (z0 z : ℝ) :
    HasDerivAt (abelPrimitive K z0) (K.a z) z := by
  unfold abelPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (ha.intervalIntegrable z0 z)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter
    ha.continuousAt

theorem abelFactor_hasDerivAt
    (K : FundamentalPair) (ha : Continuous K.a)
    (z0 z : ℝ) :
    HasDerivAt (abelFactor K z0)
      (abelFactor K z0 z * K.a z) z := by
  have h := (abelPrimitive_hasDerivAt K ha z0 z).cexp
  simpa only [abelFactor] using! h

theorem abelInvariant_hasDerivAt_zero
    (K : FundamentalPair) (ha : Continuous K.a)
    (z0 z : ℝ) :
    HasDerivAt (abelInvariant K z0) 0 z := by
  have h :=
    (abelFactor_hasDerivAt K ha z0 z).mul
      (wronskian_hasDerivAt K z)
  convert h using 1
  · rfl
  · ring

theorem abelInvariant_eq
    (K : FundamentalPair) (ha : Continuous K.a)
    (z0 x y : ℝ) :
    abelInvariant K z0 y = abelInvariant K z0 x := by
  have hftc :
      (∫ _t in x..y, (0 : ℂ)) =
        abelInvariant K z0 y - abelInvariant K z0 x := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _hz => abelInvariant_hasDerivAt_zero K ha z0 z)
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ))).intervalIntegrable x y
  simpa using (sub_eq_zero.mp (by simpa using hftc.symm))

theorem abelFactor_ne_zero
    (K : FundamentalPair) (z0 z : ℝ) :
    abelFactor K z0 z ≠ 0 := by
  unfold abelFactor
  exact Complex.exp_ne_zero _

theorem wronskian_ne_of_normalized
    (K : FundamentalPair) (ha : Continuous K.a)
    (z0 : ℝ) (hW0 : wronskian K z0 ≠ 0) :
    ∀ z : ℝ, wronskian K z ≠ 0 := by
  intro z hW
  have hconst := abelInvariant_eq K ha z0 z0 z
  unfold abelInvariant at hconst
  rw [hW, mul_zero] at hconst
  have hfac0 : abelFactor K z0 z0 ≠ 0 :=
    abelFactor_ne_zero K z0 z0
  exact hW0 (mul_eq_zero.mp hconst.symm |>.resolve_left hfac0)

#print axioms abelPrimitive_hasDerivAt
#print axioms abelFactor_hasDerivAt
#print axioms abelInvariant_hasDerivAt_zero
#print axioms abelInvariant_eq
#print axioms wronskian_ne_of_normalized

end HBL.Profile.Kummer
