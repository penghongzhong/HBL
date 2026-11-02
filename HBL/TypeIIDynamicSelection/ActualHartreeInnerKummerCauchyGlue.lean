import HBL.TypeIIDynamicSelection.ActualKummerInnerCauchyMatch
import HBL.TypeIIDynamicSelection.ActualOneLayerPhysicalClassicalInnerJets
import HBL.KummerPrescribedAnnulus.ActualInverse
import Mathlib.Tactic

/-!
# Original 2.12: C1 inner/Kummer jet gluing for ONE genuine Hartree PDE source

Take the SAME actual nonterminal inverse-square Hartree residual F(r) in
the real H+ and imaginary H- physical Fredholm problems.
When the one common complex source is continuous and in the *original*
weighted L2 class, previous strict theorems construct true C2
classical inner solutions (up,um) with uniquely FORCED affine charges.

At any prescribed strictly positive Kummer annulus [z-d,z+d],
the published native Lean theorem constructs the actual normalized
Kummer fundamental pair K and local Green right inverse. The
physical Wronskian is nonzero. Correct the inhomogeneous Kummer Green
solution by two *actual* homogeneous modes to match:

   u_K(z-d)  = up(z-d) + i*um(z-d),
   u_K'(z-d) = up'(z-d)+ i*um'(z-d).

The same exact full complex Hartree PDE source drives both sides;
the Kummer field still solves its original nonhomogeneous ODE.
Neither a chosen regional inverse, unspecified inner boundary jet,
nor a postulated Kummer matching condition is an input.

This establishes the first inner--Kummer C1 interface *conditional on
the visible one-complex-weighted-L2 source*. Global outer boundary
matching, the actual source norm from the orbit and the generated
positive-weight ledger are still open before ORIGINAL 2.12 acceptance.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection

open HBL.Profile.Kummer HBL.Profile.ActualInner
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.L2Kernel

/-- For one physical Hartree PDE residual, the genuinely constructed
classical real/phase affine inner correction has exactly matching C1
data with a classically solved physical Kummer annulus equation. -/
theorem actual_Hartree_same_PDE_inner_Kummer_Cauchy_glued
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ) (b omega s : ℝ)
    (hCont : Continuous (actualOneLayerCommonPDEResidual V Z b omega s))
    (hWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V Z b omega s r‖)
      2 halfLineMeasure)
    (mu theta z d : ℝ) (hd : 0 < d) (hz : d < z) :
    ∃ eps C : ℝ, d < eps ∧ eps < z ∧ 0 < C ∧
      ∃ K : LocalKummerPair mu theta z eps,
      ∃ up um : ℝ → ℝ,
        InnerAffineProperties up
          (actualPlusCharge (actualOneLayerPlusPDE V Z b omega s)) ∧
        InnerAffineProperties um
          (actualMinusCharge (actualOneLayerMinusPDE V Z b omega s)) ∧
        (∀ r : ℝ, 0 < r →
          DifferentiableAt ℝ up r ∧
          DifferentiableAt ℝ (deriv up) r ∧
          DifferentiableAt ℝ um r ∧
          DifferentiableAt ℝ (deriv um) r ∧
          hPlusApply up r = actualOneLayerPlusPDE V Z b omega s r ∧
          hMinusApply um r = actualOneLayerMinusPDE V Z b omega s r) ∧
        ∃ a c : ℂ,
          actualKummerCauchyValue K d
              (actualOneLayerCommonPDEResidual V Z b omega s)
              a c (z - d) =
                (up (z - d) : ℂ) + Complex.I * (um (z - d) : ℂ) ∧
          deriv (actualKummerCauchyValue K d
              (actualOneLayerCommonPDEResidual V Z b omega s) a c)
                (z - d) =
                (deriv up (z - d) : ℂ) +
                  Complex.I * (deriv um (z - d) : ℂ) ∧
          (∀ r ∈ Icc (z - d) (z + d),
            HasDerivAt
              (actualKummerCauchyValue K d
                (actualOneLayerCommonPDEResidual V Z b omega s) a c)
              (actualKummerCauchyDeriv K d
                (actualOneLayerCommonPDEResidual V Z b omega s) a c r) r ∧
            HasDerivAt (deriv
              (actualKummerCauchyValue K d
                (actualOneLayerCommonPDEResidual V Z b omega s) a c))
              (actualKummerCauchySecond K d
                (actualOneLayerCommonPDEResidual V Z b omega s) a c r) r ∧
            deriv (deriv (actualKummerCauchyValue K d
                (actualOneLayerCommonPDEResidual V Z b omega s) a c)) r +
              frozenFirstCoeff r *
                deriv (actualKummerCauchyValue K d
                  (actualOneLayerCommonPDEResidual V Z b omega s) a c) r +
              frozenZeroCoeff mu theta *
                actualKummerCauchyValue K d
                  (actualOneLayerCommonPDEResidual V Z b omega s) a c r =
              actualOneLayerCommonPDEResidual V Z b omega s r) := by
  obtain ⟨eps,C,hde,hez,hC,K,T,_hBound,_hRight,_hSolution,
      _hUnique,_hStable,_hResidual⟩ :=
    exists_actual_kummer_prescribed_annulus_inverse mu theta z d hd hz
  obtain ⟨up,um,hup,hum,hInner⟩ :=
    actual_Hartree_one_PDE_source_has_classical_Hplus_Hminus_jets
      sigma hLower hUpper V Z b omega s hCont hWeighted
  obtain ⟨a,c,hValue,hSlope,hKummer⟩ :=
    actual_Kummer_inner_interface_Cauchy_match
      K d hd hde
      (actualOneLayerCommonPDEResidual V Z b omega s) hCont
      ((up (z - d) : ℂ) + Complex.I * (um (z - d) : ℂ))
      ((deriv up (z - d) : ℂ) +
        Complex.I * (deriv um (z - d) : ℂ))
  have hrStart : z - d ∈ Icc (z - d) (z + d) :=
    ⟨le_rfl, by linarith [hd]⟩
  have hDerivative := (hKummer (z - d) hrStart).1.deriv
  refine ⟨eps,C,hde,hez,hC,K,up,um,hup,hum,hInner,a,c,
    hValue,?_,hKummer⟩
  exact hDerivative.trans hSlope

end HBL.TypeIIDynamicSelection
