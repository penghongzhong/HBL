import HBL.KummerBoundaryUnique.Definitions
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

def annulusSourceTangent {z d : ℝ}
    (S : AnnulusSource z d →L[ℂ] AnnulusJet z d) (q : ℂ)
    (F G : AnnulusSource z d) : AnnulusJet z d :=
  S (G + q • annulusValueProjection z d (S F))

/-- The pointwise classical certificate, including second derivatives at the endpoints. -/
def IsClassicalKummerBoundaryJet {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps) (d : ℝ) (c : ℂ)
    (F : AnnulusSource z d) (U : AnnulusJet z d) : Prop :=
  ∃ u v w : ℝ → ℂ,
    (∀ r : PhysicalAnnulus z d, U r = (u r, v r)) ∧
    (∀ (r : ℝ) (hr : r ∈ PhysicalAnnulus z d),
      HasDerivAt u (v r) r ∧ HasDerivAt (deriv u) (w r) r ∧
      deriv (deriv u) r + frozenFirstCoeff r * deriv u r + c * u r = F ⟨r,hr⟩) ∧
    (u (z+d) * K.dpsi d - v (z+d) * K.psi d = 0) ∧
    (K.phi (-d) * v (z-d) - K.dphi (-d) * u (z-d) = 0)

/-- Actual source-dependent derivative, its unique classical equation and its norm bound. -/
def KummerSourceTangentAt {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (c : ℂ) (C : ℝ)
    (S : ℝ → (AnnulusSource z d →L[ℂ] AnnulusJet z d))
    (F : ℝ → AnnulusSource z d) (t : ℝ) (q : ℂ) (G : AnnulusSource z d) : Prop :=
  HasDerivAt (fun s => S s (F s)) (annulusSourceTangent (S t) q (F t) G) t ∧
  (∀ r : PhysicalAnnulus z d,
    HasDerivAt (fun s => (S s (F s) r).1) (annulusSourceTangent (S t) q (F t) G r).1 t ∧
    HasDerivAt (fun s => (S s (F s) r).2) (annulusSourceTangent (S t) q (F t) G r).2 t) ∧
  IsClassicalKummerBoundaryJet K d c (G + q • annulusValueProjection z d (S t (F t)))
    (annulusSourceTangent (S t) q (F t) G) ∧
  (∀ V, IsKummerBoundarySolution K d c (G + q • annulusValueProjection z d (S t (F t))) V ↔
    V = annulusSourceTangent (S t) q (F t) G) ∧
  ‖annulusSourceTangent (S t) q (F t) G‖ ≤ C * ‖G‖ + ‖q‖ * C^2 * ‖F t‖
end HBL.Profile.Kummer
