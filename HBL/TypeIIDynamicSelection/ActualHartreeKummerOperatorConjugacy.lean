import HBL.TypeIIDynamicSelection.ActualHartreeKummerLocalizedCommutator
import HBL.TypeIIDynamicSelection.ActualHartreeCriticalRadialLaplacianScaling
import Mathlib.Tactic

/-!
# Revised HBL 2.13: true radial Kummer operator under the physical self-similar coordinate

The manuscript uses the *physical* bubble radius R and the Kummer
radius z with R = sqrt(q) * z, q > 0.

For an actual smooth complex radial profile f(R) and its pulled-back
profile u(z)=f(sqrt(q)*z), this file proves the exact chain-rule
identity for the FULL frozen linear Kummer radial operator, including:
  * both physical radial derivatives and the THREE-DIMENSIONAL 2/R term;
  * the imaginary drift i*R/2;
  * the two real spectral parameters (mu,theta).

Explicitly, with a=sqrt(q),
  L_K(u)(z)=q Delta_rad f(a*z)
          +(i*(a*z)/2)*f'(a*z)+b(mu,theta)*f(a*z).

This is a physically necessary analytic step towards the missing
Kummer/Frobenius section of original/revised finite-profile 2.13.
It does NOT assert the remaining identity between this FROZEN LINEAR
operator and the entire time-dependent renormalized Hartree PDE,
nor does it provide the far-zone nonlocal Riesz or C1 interface
matching. No assumed Type-II blowup law or new axiom is used.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole

/-- Physical radial coordinate pullback, with no extra amplitude
or phase convention hidden in the definition. -/
def actualHartreeKummerSpatialPullback
    (q : ℝ) (f : ℝ → ℂ) (z : ℝ) : ℂ :=
  f (Real.sqrt q * z)

/-- The actual bubble-coordinate form of the original FROZEN linear
Kummer operator, retaining the whole 3D radial Laplacian and i R/2 drift. -/
def actualHartreeBubbleKummerLinearApply
    (q mu theta : ℝ) (f : ℝ → ℂ) (R : ℝ) : ℂ :=
  (q : ℂ) * complexRadialLaplacian f R +
    (Complex.I * (R : ℂ) / 2) * deriv f R +
    frozenZeroCoeff mu theta * f R

/-- Exact pointwise CONJUGACY on the physical positive half-line.
All derivative identities are proved by the real-to-complex chain
rule; they are NOT assumed as symbolic radial jet inputs. -/
theorem actual_Hartree_Kummer_frozen_operator_physical_conjugacy
    (q mu theta z : ℝ) (hq : 0 < q) (hz : 0 < z)
    (f : ℝ → ℂ)
    (hf : ∀ x : ℝ,
      DifferentiableAt ℝ f (Real.sqrt q * x))
    (hf2 : DifferentiableAt ℝ (deriv f) (Real.sqrt q * z)) :
    actualHartreeFrozenKummerRadialApply mu theta
        (actualHartreeKummerSpatialPullback q f) z =
      actualHartreeBubbleKummerLinearApply
        q mu theta f (Real.sqrt q * z) := by
  let a : ℝ := Real.sqrt q
  have ha : 0 < a := Real.sqrt_pos.mpr hq
  have hScale (x : ℝ) :
      HasDerivAt (fun y : ℝ => a * y) a x :=
    hasDerivAt_const_mul a
  have hFirst (x : ℝ) :
      deriv (actualHartreeKummerSpatialPullback q f) x =
        (a : ℂ) * deriv f (a * x) := by
    have h := (hf x).hasDerivAt.scomp x (hScale x)
    change deriv (fun y : ℝ => f (a * y)) x = _
    convert h.deriv using 1
  have hFirstFun :
      deriv (actualHartreeKummerSpatialPullback q f) =
        (fun x : ℝ => (a : ℂ) * deriv f (a * x)) :=
    funext hFirst
  have hSecond :
      deriv (deriv (actualHartreeKummerSpatialPullback q f)) z =
        (a : ℂ) * ((a : ℂ) * deriv (deriv f) (a * z)) := by
    rw [hFirstFun]
    have h := ((hf2.hasDerivAt.scomp z (hScale z)).const_mul
      (a : ℂ)).deriv
    simpa only [mul_assoc] using h
  have hAsq : (a : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have haC : (a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ha.ne'
  have hzC : (z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hz.ne'
  change
    deriv (deriv (actualHartreeKummerSpatialPullback q f)) z +
      frozenFirstCoeff z *
        deriv (actualHartreeKummerSpatialPullback q f) z +
      frozenZeroCoeff mu theta * f (a * z) =
    (q : ℂ) *
        (deriv (deriv f) (a * z) +
          (2 / ((a * z : ℝ) : ℂ)) * deriv f (a * z)) +
      (Complex.I * ((a * z : ℝ) : ℂ) / 2) *
        deriv f (a * z) +
      frozenZeroCoeff mu theta * f (a * z)
  rw [hSecond, hFirst z]
  unfold frozenFirstCoeff
  rw [← hAsq]
  push_cast
  field_simp [haC, hzC]
  ring

/-- The normalized Kummer ODE can be transported back to the
actual bubble coordinate with an EXACT prescribed source. This
does not identify that source with the still-open complete Hartree
nonlinear residual. -/
theorem actual_Hartree_Kummer_frozen_source_equation_iff_physical
    (q mu theta z : ℝ) (hq : 0 < q) (hz : 0 < z)
    (f F : ℝ → ℂ)
    (hf : ∀ x : ℝ,
      DifferentiableAt ℝ f (Real.sqrt q * x))
    (hf2 : DifferentiableAt ℝ (deriv f) (Real.sqrt q * z)) :
    actualHartreeFrozenKummerRadialApply mu theta
        (actualHartreeKummerSpatialPullback q f) z = F (Real.sqrt q * z) ↔
      actualHartreeBubbleKummerLinearApply
        q mu theta f (Real.sqrt q * z) = F (Real.sqrt q * z) := by
  rw [actual_Hartree_Kummer_frozen_operator_physical_conjugacy
    q mu theta z hq hz f hf hf2]

end HBL.TypeIIDynamicSelection
