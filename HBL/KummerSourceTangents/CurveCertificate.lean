import HBL.KummerSourceTangents.TangentDerivative
import HBL.KummerSourceTangents.TangentBound
import HBL.KummerSourceTangents.PointwiseDerivative
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_source_tangent_certificate {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (c : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (S : ℝ → (AnnulusSource z d →L[ℂ] AnnulusJet z d))
    (F : ℝ → AnnulusSource z d) (t : ℝ) (q : ℂ) (G : AnnulusSource z d)
    (hS : HasDerivAt S (q • ((S t).comp (annulusValueOperator (S t)))) t)
    (hF : HasDerivAt F G t)
    (hc : IsKummerInverseAtCoefficient K d c (S t)) (hn : ‖S t‖ ≤ C)
    (hu : ∀ H V, IsKummerBoundarySolution K d c H V ↔ V = S t H) :
    KummerSourceTangentAt K c C S F t q G := by
  have hD := annulusSourceTangent_hasDerivAt S F t q G hS hF
  exact ⟨hD,annulusJet_parameter_derivative_pointwise _ _ t hD,
    hc (G + q • annulusValueProjection z d (S t (F t))),
    hu (G + q • annulusValueProjection z d (S t (F t))),
    annulusSourceTangent_norm_le (S t) C hC hn q (F t) G⟩
end HBL.Profile.Kummer
