import HBL.TypeIIDynamicSelection.ActualHartreePhysicalKummerSecondJet
import HBL.TypeIIDynamicSelection.ActualKummerInnerCauchyMatch
import Mathlib.Tactic

/-!
# Revised HBL 2.13: genuine C2 Hartree/Kummer defect equation

The actual H+/H- classical Fredholm inner profile is not automatically
a solution of the Kummer equation. The *same* complex Hartree source
feeds the normalized Green solution, and the difference of the two
actual profiles solves the inhomogeneous Kummer equation with exactly
the physically generated operator defect D = L_K U - F.

This is the appropriate input for a later variation-of-constants
transfer estimate; it neither assumes two-interface C1 matching
nor creates freely adjustable homogeneous solutions. It DOES NOT
prove smallness or vanishing of D, full remote Hartree matching, a
finite nonlinear profile, or the dynamical Type-II concentration rate.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.L2Kernel

/-- The TRUE frozen physical complex Kummer differential operator
is additive on two C2 functions on an actual open positive annulus;
global differentiability is not demanded. -/
theorem actual_Hartree_frozen_Kummer_difference_C2
    (mu theta a b : ℝ) (u v : ℝ → ℂ) (r : ℝ)
    (hr : r ∈ Ioo a b)
    (hu : ∀ x ∈ Ioo a b, DifferentiableAt ℝ u x)
    (hv : ∀ x ∈ Ioo a b, DifferentiableAt ℝ v x)
    (hu2 : DifferentiableAt ℝ (deriv u) r)
    (hv2 : DifferentiableAt ℝ (deriv v) r) :
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => u x - v x) r =
      actualHartreeFrozenKummerRadialApply mu theta u r -
        actualHartreeFrozenKummerRadialApply mu theta v r := by
  have hFirst (x : ℝ) (hx : x ∈ Ioo a b) :
      deriv (fun y => u y - v y) x = deriv u x - deriv v x :=
    ((hu x hx).hasDerivAt.sub (hv x hx).hasDerivAt).deriv
  have hFirstEventually :
      deriv (fun x => u x - v x) =ᶠ[𝓝 r]
        (fun x => deriv u x - deriv v x) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact hFirst x hx
  have hSecond :
      deriv (deriv (fun x => u x - v x)) r =
        deriv (deriv u) r - deriv (deriv v) r := by
    have h :=
      ((hu2.hasDerivAt.sub hv2.hasDerivAt).congr_of_eventuallyEq
        hFirstEventually)
    exact h.deriv
  unfold actualHartreeFrozenKummerRadialApply
  rw [hFirst r hr, hSecond]
  ring

/-- Exact physical defect equation, not an assumed Kummer matching:
the H+/H- inner profile minus the ORIGINAL a=c=0 normalized Kummer
Green profile is forced by its *actual* Kummer-vs-Hartree operator
defect at every interior point of the fixed physical annulus. -/
theorem actual_Hartree_inner_minus_normalized_Kummer_green_defect_equation
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (k : ℝ) (hLeftPositive : 0 < center - d)
    (F : ℝ → ℂ) (hF : Continuous F)
    (up um : ℝ → ℝ)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : ∀ x ∈ Ioo (center - d) (center + d),
      DifferentiableAt ℝ (deriv up) (k * x))
    (hum2 : ∀ x ∈ Ioo (center - d) (center + d),
      DifferentiableAt ℝ (deriv um) (k * x)) :
    ∀ r ∈ Ioo (center - d) (center + d),
      actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualHartreeInnerKummerProfile up um k x -
          actualKummerCauchyValue K d F 0 0 x) r =
      actualHartreeInnerKummerSourceDefect mu theta up um k r F := by
  intro r hr
  have hrPos : 0 < r := lt_trans hLeftPositive hr.1
  have hProfileDiff (x : ℝ) (hx : x ∈ Ioo (center - d) (center + d)) :
      DifferentiableAt ℝ (actualHartreeInnerKummerProfile up um k) x := by
    have hxpos : 0 < x := lt_trans hLeftPositive hx.1
    exact (actual_Hartree_two_channel_inner_Kummer_chain_rule
      up um k x (hup x hxpos) (hum x hxpos)).differentiableAt
  have hGreenDiff (x : ℝ) (hx : x ∈ Ioo (center - d) (center + d)) :
      DifferentiableAt ℝ (actualKummerCauchyValue K d F 0 0) x :=
    (actual_Kummer_Cauchy_corrected_classical_equation K d hd hde
      F hF 0 0 x (Ioo_subset_Icc_self hx)).1.differentiableAt
  have hProfile2 :
      DifferentiableAt ℝ
        (deriv (actualHartreeInnerKummerProfile up um k)) r :=
    (actual_Hartree_two_channel_Kummer_C2_chain_rule
      up um k r hrPos hup hum (hup2 r hr) (hum2 r hr)).differentiableAt
  have hGreenClassical :=
    actual_Kummer_Cauchy_corrected_classical_equation
      K d hd hde F hF 0 0 r (Ioo_subset_Icc_self hr)
  have hGreen2 :
      DifferentiableAt ℝ (deriv (actualKummerCauchyValue K d F 0 0)) r :=
    hGreenClassical.2.1.differentiableAt
  have hDiff :=
    actual_Hartree_frozen_Kummer_difference_C2
      mu theta (center - d) (center + d)
      (actualHartreeInnerKummerProfile up um k)
      (actualKummerCauchyValue K d F 0 0) r hr
      hProfileDiff hGreenDiff hProfile2 hGreen2
  have hPhysical :=
    actual_Hartree_two_channel_Kummer_operator_exact
      mu theta up um k r hrPos hup hum (hup2 r hr) (hum2 r hr)
  have hGreen :
      actualHartreeFrozenKummerRadialApply mu theta
        (actualKummerCauchyValue K d F 0 0) r = F r :=
    hGreenClassical.2.2
  calc
    actualHartreeFrozenKummerRadialApply mu theta
        (fun x => actualHartreeInnerKummerProfile up um k x -
          actualKummerCauchyValue K d F 0 0 x) r =
      actualHartreeFrozenKummerRadialApply mu theta
          (actualHartreeInnerKummerProfile up um k) r -
        actualHartreeFrozenKummerRadialApply mu theta
          (actualKummerCauchyValue K d F 0 0) r := hDiff
    _ = actualHartreeInnerKummerSourceDefect mu theta up um k r F := by
      rw [hPhysical, hGreen]
      rfl

/-- The source in the forced equation is taken from the same real
Hartree full-minus-core residual feeding the two classical H+/H-
Fredholm channels; no independent Kummer source is introduced.
The full-line continuity and weighted-L2 source memberships remain
visible hypotheses and are NOT silently deduced from 2.12. -/
theorem actual_Hartree_PDE_inner_minus_normalized_Kummer_defect
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s q : ℝ) (hq : 0 < q)
    {mu theta center eps : ℝ}
    (K : LocalKummerPair mu theta center eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (hLeftPositive : 0 < center - d)
    (hCont : Continuous (actualOneLayerCommonPDEResidual V Z b omega s))
    (hWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V Z b omega s r‖)
      2 halfLineMeasure) :
    let k : ℝ := Real.sqrt q
    let F : ℝ → ℂ :=
      actualHartreePhysicalKummerClampedSource V Z b omega s k center d
    ∃ up um : ℝ → ℝ,
      InnerAffineProperties up
        (actualPlusCharge (actualOneLayerPlusPDE V Z b omega s)) ∧
      InnerAffineProperties um
        (actualMinusCharge (actualOneLayerMinusPDE V Z b omega s)) ∧
      ∀ r ∈ Ioo (center - d) (center + d),
        actualHartreeFrozenKummerRadialApply mu theta
          (fun x => actualHartreeInnerKummerProfile up um k x -
            actualKummerCauchyValue K d F 0 0 x) r =
          actualHartreeInnerKummerSourceDefect mu theta up um k r F := by
  dsimp only
  let k : ℝ := Real.sqrt q
  let F : ℝ → ℂ :=
    actualHartreePhysicalKummerClampedSource V Z b omega s k center d
  have hk : 0 < k := Real.sqrt_pos.2 hq
  have hF : Continuous F := by
    have hClip : Continuous
        (fun x : ℝ => min (max x (center - d)) (center + d)) :=
      (continuous_id.max continuous_const).min continuous_const
    have hArg : Continuous
        (fun x : ℝ => k * min (max x (center - d)) (center + d)) :=
      continuous_const.mul hClip
    change Continuous
      ((actualOneLayerCommonPDEResidual V Z b omega s) ∘
        (fun x : ℝ =>
          k * min (max x (center - d)) (center + d)))
    exact hCont.comp hArg
  obtain ⟨up, um, hUp, hUm, hClassical⟩ :=
    actual_Hartree_one_PDE_source_has_classical_Hplus_Hminus_jets
      sigma hLower hUpper V Z b omega s hCont hWeighted
  refine ⟨up, um, hUp, hUm, ?_⟩
  have hup (x : ℝ) (hx : 0 < x) :
      DifferentiableAt ℝ up (k * x) :=
    (hClassical (k * x) (mul_pos hk hx)).1
  have hum (x : ℝ) (hx : 0 < x) :
      DifferentiableAt ℝ um (k * x) :=
    (hClassical (k * x) (mul_pos hk hx)).2.2.1
  have hup2 (x : ℝ) (hx : x ∈ Ioo (center - d) (center + d)) :
      DifferentiableAt ℝ (deriv up) (k * x) :=
    (hClassical (k * x)
      (mul_pos hk (lt_trans hLeftPositive hx.1))).2.1
  have hum2 (x : ℝ) (hx : x ∈ Ioo (center - d) (center + d)) :
      DifferentiableAt ℝ (deriv um) (k * x) :=
    (hClassical (k * x)
      (mul_pos hk (lt_trans hLeftPositive hx.1))).2.2.2.1
  exact actual_Hartree_inner_minus_normalized_Kummer_green_defect_equation
    K d hd hde k hLeftPositive F hF up um hup hum hup2 hum2

end HBL.TypeIIDynamicSelection
