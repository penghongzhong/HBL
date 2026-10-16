import HBL.AffineTailPlusAsymptotics

/-!
The symmetric kernel pairing for the *actual* three-dimensional Hartree
radial operator. The absolute product-integrability assumption is explicit;
this module does not assert that the weighted kernel estimate is already
proved. It cannot be omitted in Fubini's theorem.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Full half-line Hartree pairing, provided the exact bilinear density
is integrable on the product measure. No finite-radius cancellation is used. -/
theorem hartree_nonlocal_pairing_of_integrable
    (psi q : ℝ → ℝ)
    (hint : Integrable
      (Function.uncurry (fun r rho =>
        psi r * hartreeKernel r rho * q rho))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ))))) :
    (∫ r in Ioi (0 : ℝ), psi r * nonlocalApply q r) =
      ∫ r in Ioi (0 : ℝ), q r * nonlocalApply psi r := by
  exact symmetricKernel_pairing
    (volume.restrict (Ioi (0 : ℝ)))
    hartreeKernel psi q hartreeKernel_symm hint

/-- The nonlocal cancellation required by the manuscript's real-channel
affine charge, with the weighted integrability obligation visible. -/
theorem hartree_scale_affine_pairing_of_integrable
    (hint : Integrable
      (Function.uncurry (fun r rho =>
        resonancePlus r * hartreeKernel r rho * model rho))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ))))) :
    (∫ r in Ioi (0 : ℝ),
      resonancePlus r * nonlocalApply model r) =
      ∫ r in Ioi (0 : ℝ),
        model r * nonlocalApply resonancePlus r :=
  hartree_nonlocal_pairing_of_integrable resonancePlus model hint

end HBL.Modulation.AffineTail
