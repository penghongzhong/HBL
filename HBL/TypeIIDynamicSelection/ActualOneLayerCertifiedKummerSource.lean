import HBL.TypeIIDynamicSelection.ActualOneLayerKummerModulation
import HBL.TypeIIDynamicSelection.ActualOneLayerTwoChannelPDE
import HBL.KummerParameterInverse.ActualPhysicalFamily
import Mathlib.Tactic

/-!
# Original one-layer 2.12: an ACTUALLY constructed normalized Kummer inverse

The earlier same-Hartree-source Kummer formula accepted a general
annulus inverse T. Here T is constructed from the genuine
origin-normalized Kummer ODE local pair and Green right-inverse,
uniformly over the two real parameters (mu,theta). On ANY actual
real-core/complex-radiation Hartree PDE residual continuous on the
prescribed physical annulus, this *concrete* inverse produces the
classical ODE jet, both Wronskian boundary conditions, and an operator
norm estimate. The forcing is exactly the source whose real and
imaginary projections enter the physical H+/H- Fredholm systems.

This is a local annulus inverse, not yet the required inner-to-outer
boundary matching, global remote solve, or positive order gain for all
generated residual atoms. It does not choose a Type II rate.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The actual source-dependent Kummer inverse and normalized ODE
boundary jet, with no arbitrarily supplied regional solver. -/
theorem actual_Hartree_common_PDE_has_constructed_Kummer_certificate
    (mu0 theta0 z : ℝ) (hz : 0 < z) :
    ∃ eps B rho : ℝ, 0 < eps ∧ 0 < B ∧ 0 < rho ∧
      ∃ K : LocalKummerPair mu0 theta0 z eps,
      ∃ T : ℝ → ℝ →
        (AnnulusSource z (eps / 2) →L[ℂ] AnnulusJet z (eps / 2)),
      0 < z - eps / 2 ∧
      ∀ mu theta : ℝ, |mu - mu0| + |theta - theta0| ≤ rho →
        ∀ (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
          (b omega : ℝ → ℝ) (s : ℝ)
          (hcontinuous : Continuous (fun r : PhysicalAnnulus z (eps / 2) =>
            complexRadialRenormalizedResidual
              (fun t x => (V t x : ℂ) + Z t x)
              (b s) (omega s) s r.val -
            complexRadialRenormalizedResidual
              (fun t x => (V t x : ℂ))
              (b s) (omega s) s r.val)),
        ∃ u v w : ℝ → ℂ,
          (∀ r : PhysicalAnnulus z (eps / 2),
            T mu theta (actualHartreePDEResidualAnnulusSource
              V Z b omega s hcontinuous) r = (u r, v r)) ∧
          (∀ (r : ℝ) (hr : r ∈ PhysicalAnnulus z (eps / 2)),
            HasDerivAt u (v r) r ∧
            HasDerivAt (deriv u) (w r) r ∧
            deriv (deriv u) r + frozenFirstCoeff r * deriv u r +
              frozenZeroCoeff mu theta * u r =
                (actualHartreePDEResidualAnnulusSource
                  V Z b omega s hcontinuous) ⟨r,hr⟩) ∧
          (u (z + eps / 2) * K.dpsi (eps / 2) -
            v (z + eps / 2) * K.psi (eps / 2) = 0) ∧
          (K.phi (-(eps / 2)) * v (z - eps / 2) -
            K.dphi (-(eps / 2)) * u (z - eps / 2) = 0) ∧
          ‖T mu theta (actualHartreePDEResidualAnnulusSource
              V Z b omega s hcontinuous)‖ ≤
            (2 * B) * ‖actualHartreePDEResidualAnnulusSource
              V Z b omega s hcontinuous‖ := by
  obtain ⟨eps,B,rho,heps,hB,hrho,K,T,hpositive,hFamily,_hLip⟩ :=
    exists_actual_localKummer_uniform_physical_family mu0 theta0 z hz
  refine ⟨eps,B,rho,heps,hB,hrho,K,T,hpositive,?_⟩
  intro mu theta hnear V Z b omega s hcontinuous
  let F : AnnulusSource z (eps / 2) :=
    actualHartreePDEResidualAnnulusSource V Z b omega s hcontinuous
  obtain ⟨hK, hBound, _hMu, _hTheta, _hStability⟩ :=
    hFamily mu theta hnear
  obtain ⟨u,v,w,hJet,hEquation,hPlus,hMinus⟩ := hK F
  refine ⟨u,v,w,hJet,hEquation,hPlus,hMinus,?_⟩
  calc
    ‖T mu theta F‖ ≤ ‖T mu theta‖ * ‖F‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * B) * ‖F‖ :=
      mul_le_mul_of_nonneg_right hBound (norm_nonneg F)

end HBL.TypeIIDynamicSelection
