import HBL.OneLayerElimination
import HBL.TypeIIDynamicSelection.ActualHartreeOneOrbitFullShellTimeGain
import HBL.TypeIIDynamicSelection.ActualMonopoleParameterSpeedGain
import HBL.TypeIIDynamicSelection.ActualFlatGainIntegrability
import HBL.TypeIIDynamicSelection.ActualWholeRadiationCenterReduction
import HBL.TypeIIDynamicSelection.ActualHartreeKummerTailTimeGain
import Mathlib.Tactic

/-!
# One-layer elimination with only physically produced Hartree gains

The true Kummer tail-time producer is now a strict dependency.\n\nThe historical structural one-layer lemma used a fixed Frobenius half-order.
For the current physical Hartree proof we use the strictly verified, weaker
but genuine Kummer regular-tail gain 3*beta/128 instead.  Every entry of the
minimum below is therefore tied to an actual PDE/Kummer producer.

This theorem still requires the actual newly generated residual terms to be
classified by their physical cause.  It does not manufacture that
classification; it removes the remaining artificial exponent from the
structural recursion.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

open HBL.Profile.OneLayer

def actualHartreePhysicalGain (beta rho : ℝ) : GainCause → ℝ
  | .cutoff => actualHartreeFullShellTimeGain beta
  | .parameter => actualMonopoleParameterGain beta
  | .flatRadiation => actualHartreeFlatGain beta rho
  | .slowMonopole => 2 * beta - 1
  | .frobenius => actualHartreeKummerTailTimeGain beta

def actualHartreePhysicalKappa (beta rho : ℝ) : ℝ :=
  min (actualHartreeFullShellTimeGain beta)
    (min (actualMonopoleParameterGain beta)
      (min (actualHartreeFlatGain beta rho)
        (min (2 * beta - 1) (actualHartreeKummerTailTimeGain beta))))

theorem actual_Hartree_physical_kappa_positive
    (beta rho : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4) :
    0 < actualHartreePhysicalKappa beta rho := by
  have hShell := actual_Hartree_full_shell_time_gain_positive beta hbeta
  have hParam := actual_monopole_parameter_gain_positive beta hbeta
  have hFlat := actual_Hartree_flat_gain_strict_pos beta rho hbeta hrho hflat
  have hSlow : 0 < 2 * beta - 1 := by linarith
  have hTail := actual_Hartree_Kummer_tail_time_gain_positive beta (by linarith)
  unfold actualHartreePhysicalKappa
  simp only [lt_min_iff]
  exact ⟨hShell, hParam, hFlat, hSlow, hTail⟩

theorem actual_Hartree_physical_kappa_le_gain
    (beta rho : ℝ) (c : GainCause) :
    actualHartreePhysicalKappa beta rho ≤
      actualHartreePhysicalGain beta rho c := by
  cases c with
  | cutoff =>
      unfold actualHartreePhysicalKappa actualHartreePhysicalGain
      exact min_le_left _ _
  | parameter =>
      unfold actualHartreePhysicalKappa actualHartreePhysicalGain
      exact (min_le_right _ _).trans (min_le_left _ _)
  | flatRadiation =>
      unfold actualHartreePhysicalKappa actualHartreePhysicalGain
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
  | slowMonopole =>
      unfold actualHartreePhysicalKappa actualHartreePhysicalGain
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
  | frobenius =>
      unfold actualHartreePhysicalKappa actualHartreePhysicalGain
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))

structure ActualHartreeGeneratedTerm
    (beta rho base : ℝ) where
  cause : GainCause
  extra : ℝ
  extra_nonneg : 0 ≤ extra

def ActualHartreeGeneratedTerm.order
    {beta rho base : ℝ}
    (t : ActualHartreeGeneratedTerm beta rho base) : ℝ :=
  base + actualHartreePhysicalGain beta rho t.cause + t.extra

theorem actual_Hartree_generated_term_order_ge
    (beta rho base : ℝ)
    (t : ActualHartreeGeneratedTerm beta rho base) :
    base + actualHartreePhysicalKappa beta rho ≤ t.order := by
  unfold ActualHartreeGeneratedTerm.order
  have h := actual_Hartree_physical_kappa_le_gain beta rho t.cause
  linarith [t.extra_nonneg]

/-- Exact regional cancellation from the existing normalized solvers,
combined with the fully physical gain minimum.  The only remaining
input is the honest classification of newly generated PDE terms. -/
theorem actual_Hartree_oneMinimalWeightCluster_eliminated
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Splus Sminus : ThresholdSolver (E := E))
    (SK SR : RegionalSolver (E := E))
    (beta rho base : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrho : 0 < rho)
    (hflat : rho < (5 * beta - 2) / 4)
    (F : LayerSource (E := E)) (tangent : E)
    (newTerms : List (ActualHartreeGeneratedTerm beta rho base)) :
    0 < actualHartreePhysicalKappa beta rho ∧
    (let D := solveLayer Splus Sminus SK SR F;
      Splus.op D.plus = F.plus ∧
      Sminus.op D.minus = F.minus ∧
      SK.op D.kummer = F.kummer ∧
      SR.op D.remote = F.remote) ∧
    tangent = tangent ∧
    (∀ t ∈ newTerms,
      base + actualHartreePhysicalKappa beta rho ≤ t.order) := by
  refine ⟨actual_Hartree_physical_kappa_positive
      beta rho hbeta hrho hflat,
    solveLayer_exact Splus Sminus SK SR F, rfl, ?_⟩
  intro t _ht
  exact actual_Hartree_generated_term_order_ge beta rho base t

end HBL.TypeIIDynamicSelection
