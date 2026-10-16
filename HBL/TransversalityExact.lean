import HBL.AffineTailLogIntegralReduction
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
Manuscript lemma thm:transversality (main-parameter transversality).

The manuscript records the first Laurent coefficient
  c1(mu,theta) = -theta/2 + i*(mu+1/4)/2
and defines the normalized jet coordinates
  Theta0 = (2 Im c1 - 1/4, -2 Re c1).
The two conclusions of the numbered lemma, namely Theta0=id and its
complete real Frechet Jacobian being I_2, are verified below.

This lemma is algebraically independent of the affine-charge lemma.
The hypergeometric Laurent-expansion derivation of c1 belongs to the
 preceding unnumbered manuscript computation, not this assertion.
-/

noncomputable section

open scoped Topology

namespace HBL.Modulation.Transversality

/-- The coefficient c_1 displayed in the manuscript's first Kummer jet. -/
def firstKummerCoefficient (mu theta : ℝ) : ℂ :=
  ⟨-theta / 2, (mu + 1 / 4) / 2⟩

/-- The real two-component jet normalization of the first coefficient. -/
def mainJet (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * (firstKummerCoefficient p.1 p.2).im - 1 / 4,
    -2 * (firstKummerCoefficient p.1 p.2).re)

/-- Exact first coordinate of the normalized Kummer jet. -/
theorem mainJet_first (p : ℝ × ℝ) : (mainJet p).1 = p.1 := by
  dsimp [mainJet, firstKummerCoefficient]
  ring

/-- Exact second coordinate of the normalized Kummer jet. -/
theorem mainJet_second (p : ℝ × ℝ) : (mainJet p).2 = p.2 := by
  dsimp [mainJet, firstKummerCoefficient]
  ring

/-- The first assertion of the manuscript's numbered transversality lemma. -/
theorem mainJet_eq (p : ℝ × ℝ) : mainJet p = p := by
  apply Prod.ext
  · exact mainJet_first p
  · exact mainJet_second p

theorem mainJet_eq_id : mainJet = (id : ℝ × ℝ → ℝ × ℝ) := by
  funext p
  exact mainJet_eq p

/-- The full real Frechet Jacobian is the two-dimensional identity map. -/
theorem mainJet_fderiv (p : ℝ × ℝ) :
    fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [mainJet_eq_id]
  exact fderiv_id

/-- The normalized first jet recovers the two parameters uniquely. -/
theorem mainJet_unique (y : ℝ × ℝ) :
    ∃! p : ℝ × ℝ, mainJet p = y := by
  refine ⟨y, mainJet_eq y, ?_⟩
  intro p hp
  rw [mainJet_eq p] at hp
  exact hp

/-- The complete pair of claims in manuscript lemma thm:transversality. -/
theorem manuscript_transversality_environment_closed :
    (∀ p : ℝ × ℝ, mainJet p = p) ∧
      (∀ p : ℝ × ℝ,
        fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ)) := by
  exact ⟨mainJet_eq, mainJet_fderiv⟩

end HBL.Modulation.Transversality
