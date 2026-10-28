import HBL.KummerLocalInverse.CertificateDefinitions
import HBL.KummerLocalInverse.PhysicalClassical
import HBL.KummerLocalInverse.PhysicalEndpoints
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localKummerJetOperator_rightInverse
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d C : ℝ)
    (hd : 0 < d) (hde : d < eps) (hC : 0 ≤ C) (hK : LocalKummerBound K C) :
    IsLocalKummerRightInverse K d (localKummerJetOperator K d C hd hde hC hK) := by
  intro F
  let f := annulusSourceExtension z d hd.le F
  have hf := (annulusSourceExtension_properties z d hd.le F).1
  refine ⟨physicalLocalKummerValue K d f, physicalLocalKummerDeriv K d f,
    physicalLocalKummerSecond K d f, ?_, ?_, ?_, ?_⟩
  · intro r
    rfl
  · intro r hr
    have hD := physicalLocalKummer_hasDerivAt K d hd hde f hf hr
    have hc := physicalLocalKummer_classical K d hd hde f hf hr
    have hE := hc.2
    have he : f r = F ⟨r, hr⟩ := (annulusSourceExtension_properties z d hd.le F).2.2 r hr
    rw [he] at hE
    exact ⟨hD.1, hc.1, hE⟩
  · exact (physicalLocalKummer_endpoint_normalization K d f).1
  · exact (physicalLocalKummer_endpoint_normalization K d f).2
end HBL.Profile.Kummer
