import HBL.KummerLocalInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_endpoint_normalization
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (a b : ℝ) (F : ℝ → ℂ) :
    localAnnulusCoeffA K b F b = 0 ∧ localAnnulusCoeffB K a F a = 0 ∧
    localAnnulusValue K a b F b * K.dpsi b - localAnnulusDeriv K a b F b * K.psi b = 0 ∧
    K.phi a * localAnnulusDeriv K a b F a - K.dphi a * localAnnulusValue K a b F a = 0 := by
  have hA : localAnnulusCoeffA K b F b = 0 := by simp [localAnnulusCoeffA]
  have hB : localAnnulusCoeffB K a F a = 0 := by simp [localAnnulusCoeffB]
  refine ⟨hA, hB, ?_, ?_⟩
  · unfold localAnnulusValue localAnnulusDeriv
    rw [hA]
    ring
  · unfold localAnnulusValue localAnnulusDeriv
    rw [hB]
    ring
end HBL.Profile.Kummer
