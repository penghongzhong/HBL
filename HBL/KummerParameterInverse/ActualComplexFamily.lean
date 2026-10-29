import HBL.KummerParameterInverse.ClassicalCertificate
import HBL.KummerParameterInverse.OperatorLipschitz
import HBL.KummerParameterInverse.SourceStability
import HBL.KummerParameterInverse.DerivativeBound
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem exists_actual_localKummer_complex_parameter_family (mu theta z : ℝ) (hz : 0 < z) :
    ∃ eps B ρ : ℝ, 0 < eps ∧ 0 < B ∧ 0 < ρ ∧
      ∃ K : LocalKummerPair mu theta z eps,
      ∃ S : ℂ → (AnnulusSource z (eps / 2) →L[ℂ] AnnulusJet z (eps / 2)),
        0 < z - eps / 2 ∧
        (∀ δ : ℂ, ‖δ‖ ≤ ρ →
          IsKummerInverseAtCoefficient K (eps / 2) (frozenZeroCoeff mu theta + δ) (S δ) ∧
          ‖S δ‖ ≤ 2 * B ∧
          HasDerivAt S (-((S δ).comp (annulusValueOperator (S δ)))) δ ∧
          ‖deriv S δ‖ ≤ 4 * B ^ 2 ∧
          ∀ F G : AnnulusSource z (eps / 2), ‖S δ F - S δ G‖ ≤ (2 * B) * ‖F - G‖) ∧
        (∀ δ η : ℂ, ‖δ‖ ≤ ρ → ‖η‖ ≤ ρ → ‖S δ - S η‖ ≤ (4 * B ^ 2) * ‖δ - η‖) := by
  obtain ⟨eps,C,heps,hC,K,T,hpos,hT,hcert,_⟩ := exists_actual_localKummer_bounded_rightInverse mu theta z hz
  let B : ℝ := 2 * eps * C ^ 3
  have hB : 0 < B := by dsimp [B]; positivity
  let ρ : ℝ := 1 / (2 * B)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hTB : ‖T‖ ≤ B := hT
  have hsmall : ∀ δ : ℂ, ‖δ‖ ≤ ρ → ‖δ‖ * B ≤ (1 / 2 : ℝ) := by
    intro δ hδ
    calc
      ‖δ‖ * B ≤ ρ * B := mul_le_mul_of_nonneg_right hδ hB.le
      _ = 1 / 2 := by dsimp [ρ]; field_simp
  refine ⟨eps,B,ρ,heps,hB,hρ,K,annulusParameterInverse T,hpos,?_,?_⟩
  · intro δ hδ
    have hs := hsmall δ hδ
    have hsT := (mul_le_mul_of_nonneg_left hTB (norm_nonneg δ)).trans hs
    exact ⟨annulusParameterInverse_classical K T hcert δ hsT,
      annulusParameterInverse_norm_le T B hB.le hTB δ hs,
      annulusParameterInverse_hasDerivAt T δ hsT,
      annulusParameterInverse_deriv_norm_le T B hB.le hTB δ hs,
      annulusParameterInverse_source_stability T B hB.le hTB δ hs⟩
  · intro δ η hδ hη
    exact annulusParameterInverse_lipschitz T B hB.le hTB δ η (hsmall δ hδ) (hsmall η hη)
end HBL.Profile.Kummer
