import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeFullCutoffSupport
import HBL.KummerParameterInverse.ActualPhysicalFamily
import Mathlib.Tactic

/-!
# Actual inverse-square Hartree Riesz cutoff source -> normalized Kummer Green jet

The EXACT physical moving-cutoff nonlinear Riesz source
 E_{ell,R}(r)=N(chi_R sqrt(ell) z(ell r))
                 -chi_R(r) N(sqrt(ell) z(ell r))
has a genuine, previously strict-verified O(ell^2 sqrt(ell))
pointwise gain from the full quartic Riesz integral.
The Strauss radial-H1 plus Linfty estimate DERIVES the required
quartic bubble envelope, rather than postulating it.

A constructed two-Wronskian-normalized Kummer right inverse
T_{mu,theta}: C(annulus)->C(annulus,C^2) has uniform operator norm
<=2B_K on a positive physical annulus. Its actual source-to-jet
bound is therefore O(ell^2 sqrt(ell)) on the SAME Hartree source.

The genuine physical Riesz source's continuity on the compact
annulus is the visible high-regularity Hartree analytic interface.
The statement does NOT assume a forced Kummer source order,
invent a regional solver, or add homogeneous correction freedom.
The final physical inner/remote overlap mismatches and
mixed Vc+Z effects remain unproved in original 2.12.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.Kummer

/-- The original constructed Kummer Green inverse solves the REAL
nonlocal Hartree cutoff commutator with an explicit strictly positive
ell^(5/2) source-to-jet gain for the same profile and both channels. -/
theorem actual_Hartree_nonlocal_Riesz_source_to_normalized_Kummer_jet
    (mu0 theta0 zCenter : ℝ) (hzCenter : 0 < zCenter) :
    ∃ eps BK rho : ℝ,
      0 < eps ∧ 0 < BK ∧ 0 < rho ∧
      ∃ K : LocalKummerPair mu0 theta0 zCenter eps,
      ∃ T : ℝ → ℝ →
        (AnnulusSource zCenter (eps / 2) →L[ℂ]
          AnnulusJet zCenter (eps / 2)),
      0 < zCenter - eps / 2 ∧
      ∀ mu theta : ℝ,
        |mu - mu0| + |theta - theta0| ≤ rho →
        IsKummerInverseAtCoefficient K (eps / 2)
          (frozenZeroCoeff mu theta) (T mu theta) ∧
        ∀ ell R B A : ℝ,
          0 < ell → 0 < R → 0 ≤ B → 0 ≤ A →
          ∀ (zPhys : ℝ → ℂ), Measurable zPhys →
          (∀ u : ℝ, 0 < u → ‖zPhys u‖ ≤ B) →
          (∀ u : ℝ, 1 ≤ u → u * ‖zPhys u‖ ≤ A) →
          ∀ (hCont : Continuous
            (fun x : PhysicalAnnulus zCenter (eps / 2) =>
              actualHartreeNonlocalCutoffError R ell zPhys x.val)),
            ‖T mu theta
                (⟨fun x : PhysicalAnnulus zCenter (eps / 2) =>
                   actualHartreeNonlocalCutoffError R ell zPhys x.val,
                   hCont⟩ : AnnulusSource zCenter (eps / 2))‖ ≤
            (2 * BK) *
              ((2 * radialHartreeRowBoundConstant *
                (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
                  ell ^ 2 * Real.sqrt ell) := by
  obtain ⟨eps,BK,rho,heps,hBK,hrho,K,T,hpositive,hFamily,_hLip⟩ :=
    exists_actual_localKummer_uniform_physical_family
      mu0 theta0 zCenter hzCenter
  refine ⟨eps,BK,rho,heps,hBK,hrho,K,T,hpositive,?_⟩
  intro mu theta hnear
  obtain ⟨hInverse,hTOp,_hMu,_hTheta,_hStability⟩ :=
    hFamily mu theta hnear
  refine ⟨hInverse,?_⟩
  intro ell R B A hell hR hB hA zPhys hz hSup hStrauss hCont
  let F : AnnulusSource zCenter (eps / 2) :=
    ⟨fun x => actualHartreeNonlocalCutoffError R ell zPhys x.val,hCont⟩
  let D : ℝ := 2 * (B ^ 4 + A ^ 4)
  let C : ℝ :=
    (2 * radialHartreeRowBoundConstant * D * B ^ 3) *
      ell ^ 2 * Real.sqrt ell
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hk := radialHartreeRowBoundConstant_pos
    positivity
  have hFC (x : PhysicalAnnulus zCenter (eps / 2)) : ‖F x‖ ≤ C := by
    have hx : 0 < x.val := hpositive.trans_le x.property.1
    have hPoint := actual_Hartree_physical_nonlocal_sharp_from_Strauss
      ell R x.val B A hell hR hx hB hA
      zPhys hz hSup hStrauss
    simpa only [F,C,D] using hPoint
  have hF : ‖F‖ ≤ C :=
    (ContinuousMap.norm_le F hC).2 hFC
  have hOp : ‖T mu theta F‖ ≤
      ‖T mu theta‖ * ‖F‖ :=
    ContinuousLinearMap.le_opNorm (T mu theta) F
  calc
    ‖T mu theta
        (⟨fun x : PhysicalAnnulus zCenter (eps / 2) =>
          actualHartreeNonlocalCutoffError R ell zPhys x.val,
          hCont⟩ : AnnulusSource zCenter (eps / 2))‖ =
      ‖T mu theta F‖ := rfl
    _ ≤ ‖T mu theta‖ * ‖F‖ := hOp
    _ ≤ (2 * BK) * C :=
      mul_le_mul hTOp hF (norm_nonneg F) (by positivity)
    _ = (2 * BK) *
          ((2 * radialHartreeRowBoundConstant *
            (2 * (B ^ 4 + A ^ 4)) * B ^ 3) *
              ell ^ 2 * Real.sqrt ell) := by rfl

end HBL.TypeIIDynamicSelection
