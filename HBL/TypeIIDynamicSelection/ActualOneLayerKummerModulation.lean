import HBL.TypeIIDynamicSelection.ActualOneLayerPDEResidual
import HBL.KummerSourceTangents.TangentDerivative
import HBL.KummerParameterInverse.OperatorDerivative
import HBL.KummerParameterInverse.PhysicalParameterDerivatives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Real two-dimensional modulation speed in the ACTUAL Kummer inverse

The original one-layer Hartree analysis has two actual slow parameters
(mu,theta). The frozen annular operator has coefficient
  theta + I*(1/4 - mu).
Its derivative is theta_s - I*mu_s, not a formal unspecified tangent.

The locally invertible parameter-dependent Kummer solver is the
previously constructed actual annulusParameterInverse, not an arbitrary
RegionalSolver package. Its speed derivative is obtained by composing
the strictly verified Neumann resolvent derivative with the genuine
two-dimensional physical coefficient path.

This identifies a Kummer-region parameter-tangent operator entering
original manuscript prop:one-layer-stage3. The full physical source
projection, matching with the plus/minus Fredholm and remote solvers, and
positive-order remainder remain open.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact coefficient velocity of the *physical* frozen Kummer ODE,
with real parameters mu and theta. No bound or terminal exponent is
inserted into the parameter path. -/
theorem actual_Kummer_frozen_coefficient_two_speed
    (mu theta : ℝ → ℝ) (mu0 theta0 : ℝ)
    {s mus ths : ℝ}
    (hmu : HasDerivAt mu mus s)
    (htheta : HasDerivAt theta ths s) :
    HasDerivAt
      (fun t : ℝ =>
        frozenZeroCoeff (mu t) (theta t) -
          frozenZeroCoeff mu0 theta0)
      ((ths : ℂ) - Complex.I * (mus : ℂ)) s := by
  have hm : HasDerivAt
      (fun t : ℝ => (mu t : ℂ)) (mus : ℂ) s :=
    hmu.ofReal_comp
  have ht : HasDerivAt
      (fun t : ℝ => (theta t : ℂ)) (ths : ℂ) s :=
    htheta.ofReal_comp
  have hmuDiff : HasDerivAt
      (fun t : ℝ => (1 / 4 : ℂ) - (mu t : ℂ))
      (-(mus : ℂ)) s := by
    convert ((hasDerivAt_const s (1 / 4 : ℂ)).sub hm) using 1;
      simp only [zero_sub]
  have hcoeff := (ht.add (hmuDiff.const_mul Complex.I)).sub_const
    (frozenZeroCoeff mu0 theta0)
  convert hcoeff using 1
  · funext t
    unfold frozenZeroCoeff
    simp only [Pi.add_apply]
  · ring

/-- The true Kummer inverse has an EXACT two-parameter time tangent.
The only operator input is its physically required smallness
‖delta‖ ‖T‖ ≤ 1/2 for the verified annular resolvent.
It is not the arbitrary right-inverse package of the older structural
one-layer statement. -/
theorem actual_Kummer_inverse_two_parameter_speed
    {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d)
    (mu theta : ℝ → ℝ) (mu0 theta0 : ℝ)
    {s mus ths : ℝ}
    (hmu : HasDerivAt mu mus s)
    (htheta : HasDerivAt theta ths s)
    (hsmall :
      ‖frozenZeroCoeff (mu s) (theta s) -
        frozenZeroCoeff mu0 theta0‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    HasDerivAt
      (fun t : ℝ =>
        annulusParameterInverse T
          (frozenZeroCoeff (mu t) (theta t) -
            frozenZeroCoeff mu0 theta0))
      (((ths : ℂ) - Complex.I * (mus : ℂ)) •
        (-((annulusParameterInverse T
            (frozenZeroCoeff (mu s) (theta s) -
              frozenZeroCoeff mu0 theta0)).comp
          (annulusValueOperator
            (annulusParameterInverse T
              (frozenZeroCoeff (mu s) (theta s) -
                frozenZeroCoeff mu0 theta0)))))) s := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hcoef := actual_Kummer_frozen_coefficient_two_speed
    mu theta mu0 theta0 hmu htheta
  have hInv := annulusParameterInverse_hasDerivAt
    T (frozenZeroCoeff (mu s) (theta s) -
      frozenZeroCoeff mu0 theta0) hsmall
  simpa only [Function.comp_def] using!
    hInv.scomp (𝕜 := ℝ) (𝕜' := ℂ)
      (F := AnnulusSource z d →L[ℂ] AnnulusJet z d) s hcoef


/-- The ACTUAL whole-radiation Hartree PDE residual increment, restricted to a Kummer annulus.
Continuity of this physical source on the annulus is a classical
regularity input, not a claim of Hartree error cancellation. -/
def actualHartreePDEResidualAnnulusSource
    {z d : ℝ}
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ) (s : ℝ)
    (hcontinuous : Continuous (fun r : PhysicalAnnulus z d =>
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ) + Z t x) (b s) (omega s) s r.val -
      complexRadialRenormalizedResidual
        (fun t x => (V t x : ℂ)) (b s) (omega s) s r.val)) :
    AnnulusSource z d :=
  ⟨_, hcontinuous⟩

/-- Genuine coupled physical Hartree-source / two-speed Kummer tangent.
The source is the EXACT whole-radiation increment of the full Hartree residual, rather
than a freely specified layer source. Its Banach-valued time derivative
is explicitly retained as a regularity assumption. The formula is
  U_s = G_s (F_s - (theta_s - i*mu_s) P U).
No asymptotic speed, regional matching, or source cancellation is assumed.
This is an ingredient, not the full original one-layer stage 3. -/
theorem actual_Kummer_inverse_physical_Hartree_source_two_speed
    {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d)
    (mu theta : ℝ → ℝ) (mu0 theta0 : ℝ)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega : ℝ → ℝ)
    (hcontinuous : ∀ t : ℝ,
      Continuous (fun r : PhysicalAnnulus z d =>
        complexRadialRenormalizedResidual
          (fun τ x => (V τ x : ℂ) + Z τ x)
          (b t) (omega t) t r.val -
        complexRadialRenormalizedResidual
          (fun τ x => (V τ x : ℂ))
          (b t) (omega t) t r.val))
    {s mus ths : ℝ} (G : AnnulusSource z d)
    (hmu : HasDerivAt mu mus s)
    (htheta : HasDerivAt theta ths s)
    (hF : HasDerivAt
      (fun t => actualHartreePDEResidualAnnulusSource V Z b omega t
        (hcontinuous t)) G s)
    (hsmall :
      ‖frozenZeroCoeff (mu s) (theta s) -
        frozenZeroCoeff mu0 theta0‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    HasDerivAt
      (fun t =>
        annulusParameterInverse T
          (frozenZeroCoeff (mu t) (theta t) -
            frozenZeroCoeff mu0 theta0)
          (actualHartreePDEResidualAnnulusSource V Z b omega t
            (hcontinuous t)))
      (annulusSourceTangent
        (annulusParameterInverse T
          (frozenZeroCoeff (mu s) (theta s) -
            frozenZeroCoeff mu0 theta0))
        (-((ths : ℂ) - Complex.I * (mus : ℂ)))
        (actualHartreePDEResidualAnnulusSource V Z b omega s
          (hcontinuous s)) G) s := by
  have hS := actual_Kummer_inverse_two_parameter_speed
    T mu theta mu0 theta0 hmu htheta hsmall
  have hS' : HasDerivAt
      (fun t =>
        annulusParameterInverse T
          (frozenZeroCoeff (mu t) (theta t) -
            frozenZeroCoeff mu0 theta0))
      ((-((ths : ℂ) - Complex.I * (mus : ℂ))) •
        ((annulusParameterInverse T
          (frozenZeroCoeff (mu s) (theta s) -
            frozenZeroCoeff mu0 theta0)).comp
          (annulusValueOperator
            (annulusParameterInverse T
              (frozenZeroCoeff (mu s) (theta s) -
                frozenZeroCoeff mu0 theta0))))) s := by
    convert hS using 1
    ext F x <;> simp [ContinuousLinearMap.comp_apply, smul_neg, neg_smul]
  exact annulusSourceTangent_hasDerivAt
    (fun t =>
      annulusParameterInverse T
        (frozenZeroCoeff (mu t) (theta t) -
          frozenZeroCoeff mu0 theta0))
    (fun t =>
      actualHartreePDEResidualAnnulusSource V Z b omega t
        (hcontinuous t))
    s (-((ths : ℂ) - Complex.I * (mus : ℂ))) G hS' hF


end HBL.TypeIIDynamicSelection
