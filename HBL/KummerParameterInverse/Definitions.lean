import HBL.KummerLocalInverse.ActualRightInverse
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Analysis.Calculus.Deriv.Mul
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

abbrev AnnulusSource (z d : ℝ) := C(PhysicalAnnulus z d, ℂ)
abbrev AnnulusJet (z d : ℝ) := C(PhysicalAnnulus z d, ℂ × ℂ)

instance annulusJetOperator_continuousSMul_real (z d : ℝ) :
    ContinuousSMul ℝ (AnnulusSource z d →L[ℂ] AnnulusJet z d) := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  exact IsScalarTower.continuousSMul ℂ

def annulusValueLinear (z d : ℝ) : AnnulusJet z d →ₗ[ℂ] AnnulusSource z d where
  toFun f := ⟨fun r => (f r).1, f.continuous.fst⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def annulusValueProjection (z d : ℝ) : AnnulusJet z d →L[ℂ] AnnulusSource z d :=
  (annulusValueLinear z d).mkContinuous 1 (by
    intro f
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro r
    exact (le_max_left ‖(f r).1‖ ‖(f r).2‖).trans (f.norm_coe_le_norm r))

def annulusValueOperator {z d : ℝ} (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) :
    AnnulusSource z d →L[ℂ] AnnulusSource z d := (annulusValueProjection z d).comp T

def annulusParameterBlock {z d : ℝ} (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ) :
    AnnulusSource z d →L[ℂ] AnnulusSource z d := 1 + δ • annulusValueOperator T

def annulusParameterResolvent {z d : ℝ} (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ) :
    AnnulusSource z d →L[ℂ] AnnulusSource z d := Ring.inverse (annulusParameterBlock T δ)

def annulusParameterInverse {z d : ℝ} (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ) :
    AnnulusSource z d →L[ℂ] AnnulusJet z d := T.comp (annulusParameterResolvent T δ)

/-- The endpoint conditions use one fixed base pair for the entire parameter neighborhood. -/
def IsKummerInverseAtCoefficient {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps) (d : ℝ) (c : ℂ)
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) : Prop :=
  ∀ F : AnnulusSource z d, ∃ u v w : ℝ → ℂ,
    (∀ r : PhysicalAnnulus z d, T F r = (u r, v r)) ∧
    (∀ (r : ℝ) (hr : r ∈ PhysicalAnnulus z d),
      HasDerivAt u (v r) r ∧ HasDerivAt (deriv u) (w r) r ∧
      deriv (deriv u) r + frozenFirstCoeff r * deriv u r + c * u r = F ⟨r, hr⟩) ∧
    (u (z + d) * K.dpsi d - v (z + d) * K.psi d = 0) ∧
    (K.phi (-d) * v (z - d) - K.dphi (-d) * u (z - d) = 0)
end HBL.Profile.Kummer
