import HBL.TypeIIDynamicSelection.ActualHBL212ThreeRegionSamePDESource
import HBL.TypeIIDynamicSelection.ActualOneLayerCertifiedKummerSource
import Mathlib.Tactic

/-!
# HBL original 2.12: actual normalized Kummer Green solution uses the WHOLE Hartree PDE source

Combine two already certified components:
(1) the origin-normalized parameter-dependent Kummer inverse, with its
    ACTUAL two Wronskian endpoint normalizations and uniform source norm;
(2) the moving-core 3-region same-Hartree-PDE exact source identity,
    including the true remote inverse-square Riesz interaction.

Thus the physical annulus ODE equation is solved with precisely
  F_K = (R_H(V+Z_inner)-R_H(V)) +
        Riesz_ext(|V+Z|^4-|V+Z_inner|^4) |V+Z_inner|^2(V+Z_inner)
and its real and imaginary parts coincide with the actual
H_plus/H_minus Fredholm data.

No prescribed abstract Kummer RHS is used; no false freedom of
homogeneous coefficients is introduced.

IMPORTANT: exact matching of the normalized Kummer endpoint jets to
the classical inner H+/H- and remote boundary jets, the full
moving-weight residual gain, and the eventual Type II rate are NOT
proved by this theorem. Original manuscript 2.12 remains open.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The ACTUAL constructed two-Wronskian-normalized physical Kummer
inverse, with source equal to the full three-region Hartree PDE
including exact remote nonlinear Riesz potential, and a uniform norm. -/
theorem actual_Hartree_2_12_true_remote_Kummer_solution_certificate
    (mu0 theta0 z : ℝ) (hz : 0 < z) :
    ∃ eps B rho : ℝ, 0 < eps ∧ 0 < B ∧ 0 < rho ∧
      ∃ K : LocalKummerPair mu0 theta0 z eps,
      ∃ T : ℝ → ℝ →
        (AnnulusSource z (eps / 2) →L[ℂ] AnnulusJet z (eps / 2)),
      0 < z - eps / 2 ∧
      ∀ mu theta : ℝ, |mu - mu0| + |theta - theta0| ≤ rho →
        ∀ (V : ℝ → ℝ → ℝ) (R : ℝ → ℝ)
          (Z : ℝ → ℝ → ℂ) (b omega : ℝ → ℝ) (s : ℝ),
        ContinuousAt R s → (∀ t, 0 < R t) →
        ∀ (hcontinuous : Continuous (fun x : PhysicalAnnulus z (eps / 2) =>
          complexRadialRenormalizedResidual
            (fun t y => (V t y : ℂ) + Z t y) (b s) (omega s) s x.val -
          complexRadialRenormalizedResidual
            (fun t y => (V t y : ℂ)) (b s) (omega s) s x.val)),
        (∀ x : PhysicalAnnulus z (eps / 2),
          0 < x.val ∧ 2 * x.val ≤ R s) →
        Measurable (actualOneLayerWithInnerRadiation V R Z s) →
        Measurable (actualOneLayerRemoteRadiation R Z s) →
        IntegrableOn (actualMovingHartreeRemoteDensity V R Z s)
          (Ioi (R s)) →
        (∀ x : PhysicalAnnulus z (eps / 2),
          IntegrableOn (fun ρ =>
            ρ * hartreeRadialLog x.val ρ *
              ‖actualOneLayerWithInnerRadiation V R Z s ρ‖ ^ 4)
            (Ioi (0 : ℝ))) →
        ∃ u v w : ℝ → ℂ,
          (∀ x : PhysicalAnnulus z (eps / 2),
             T mu theta (actualHartreePDEResidualAnnulusSource
               V Z b omega s hcontinuous) x = (u x, v x)) ∧
          (∀ (r : ℝ) (_hr : r ∈ PhysicalAnnulus z (eps / 2)),
             HasDerivAt u (v r) r ∧
             HasDerivAt (deriv u) (w r) r ∧
             deriv (deriv u) r +
               frozenFirstCoeff r * deriv u r +
               frozenZeroCoeff mu theta * u r =
                actualOneLayerInnerCoreResidual V R Z
                  (b s) (omega s) s r +
                (radialHartreeExteriorPotential
                  (actualMovingHartreeRemoteDensity V R Z s)
                  (R s) r : ℂ) *
                    actualWholeRadiationLocalCubic
                      (actualOneLayerWithInnerRadiation V R Z s) r) ∧
          (u (z + eps / 2) * K.dpsi (eps / 2) -
            v (z + eps / 2) * K.psi (eps / 2) = 0) ∧
          (K.phi (-(eps / 2)) * v (z - eps / 2) -
            K.dphi (-(eps / 2)) * u (z - eps / 2) = 0) ∧
          ‖T mu theta (actualHartreePDEResidualAnnulusSource
             V Z b omega s hcontinuous)‖ ≤
               (2 * B) *
                 ‖actualHartreePDEResidualAnnulusSource
                   V Z b omega s hcontinuous‖ := by
  obtain ⟨eps,B,rho,heps,hB,hrho,K,T,hpositive,hKummer⟩ :=
    actual_Hartree_common_PDE_has_constructed_Kummer_certificate
      mu0 theta0 z hz
  refine ⟨eps,B,rho,heps,hB,hrho,K,T,hpositive,?_⟩
  intro mu theta hnear V R Z b omega s hRc hR hcontinuous
    hAnnulus hUmeas hQmeas hF hUrow
  obtain ⟨u,v,w,hJet,hEquation,hPlus,hMinus,hNorm⟩ :=
    hKummer mu theta hnear V Z b omega s hcontinuous
  have hSource :=
    actual_Hartree_three_region_common_PDE_Kummer_source_exact
      V R Z b omega s hRc hR hcontinuous
      hAnnulus hUmeas hQmeas hF hUrow
  refine ⟨u,v,w,hJet,?_,hPlus,hMinus,hNorm⟩
  intro r hr
  obtain ⟨hFirst,hSecond,hODE⟩ := hEquation r hr
  refine ⟨hFirst,hSecond,?_⟩
  rw [hSource ⟨r,hr⟩] at hODE
  exact hODE

end HBL.TypeIIDynamicSelection
