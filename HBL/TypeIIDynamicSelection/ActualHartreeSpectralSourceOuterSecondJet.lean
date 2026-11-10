import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralOriginalPDEMismatch
import HBL.TypeIIDynamicSelection.ActualHartreeC2SourceJetRepair
import Mathlib.Tactic

/-!
# Actual original Hartree/Kummer source fixes the outer C² repair curvature

No second-jet datum is introduced independently.  The curvature equals
the actual spectrally corrected origin-Green solution's second derivative
and, by the unshifted original Kummer equation, equals an explicit
expression in the very same physical source F, the Cramer solution u0,
and the true matched value and slope.  The existing concrete smooth
cutoff then yields all six outer endpoint jets of the same-source
quadratic repair.

This proves actual source-to-C² *endpoint data*, NOT a C² global
four-region physical PDE field, residual derivative/time gain, or
a blowup orbit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual unshifted physical Kummer source determines the unique
spectral-corrected curvature at the outer matching point. -/
theorem actual_Hartree_spectral_second_jet_from_same_original_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 B : ℝ) (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hB : B < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (U DU delta : ℂ) :
    let u0 := actualOriginMatchedKummerValue K r0 B F U DU
    let w := actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU delta
    deriv (deriv w) B =
      F B - delta * u0 B -
        frozenFirstCoeff B * deriv w B -
        frozenZeroCoeff mu theta * w B := by
  dsimp only
  let u0 := actualOriginMatchedKummerValue K r0 B F U DU
  let w := actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU delta
  have hBDomain : B ∈ Ioo (0 : ℝ) scale :=
    ⟨hr0.trans_le hOrder, hB⟩
  have hSource :=
    actual_Hartree_matched_spectral_original_unshifted_source
      K r0 B hr0 hOrder hB F hF U DU delta B hBDomain
  dsimp only at hSource
  calc
    deriv (deriv w) B =
        (deriv (deriv w) B +
           frozenFirstCoeff B * deriv w B +
           frozenZeroCoeff mu theta * w B) -
           frozenFirstCoeff B * deriv w B -
           frozenZeroCoeff mu theta * w B := by ring
    _ = F B - delta * u0 B -
          frozenFirstCoeff B * deriv w B -
          frozenZeroCoeff mu theta * w B := by rw [hSource]

/-- All six endpoint jets are produced using ONE original source,
without postulating independent C² matching curvature. -/
theorem actual_Hartree_spectral_source_locked_outer_C2_repair_jets
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 B : ℝ) (hr0 : 0 < r0) (hOrder : r0 ≤ B) (hB : B < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (U DU delta : ℂ) :
    let u0 := actualOriginMatchedKummerValue K r0 B F U DU
    let w := actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU delta
    let j := F B - delta * u0 B -
      frozenFirstCoeff B * deriv w B -
      frozenZeroCoeff mu theta * w B
    let rep := actualHartreeC2SourceJetRepair B (w B) (deriv w B) j
    rep B = w B ∧
      deriv rep B = deriv w B ∧
      deriv (deriv rep) B = deriv (deriv w) B ∧
      rep (2 * B) = 0 ∧
      deriv rep (2 * B) = 0 ∧
      deriv (deriv rep) (2 * B) = 0 := by
  dsimp only
  let u0 := actualOriginMatchedKummerValue K r0 B F U DU
  let w := actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU delta
  let j := F B - delta * u0 B -
      frozenFirstCoeff B * deriv w B -
      frozenZeroCoeff mu theta * w B
  let rep := actualHartreeC2SourceJetRepair B (w B) (deriv w B) j
  have hJ :
      deriv (deriv w) B = j :=
    actual_Hartree_spectral_second_jet_from_same_original_source
      K r0 B hr0 hOrder hB F hF U DU delta
  have hEnds := actual_Hartree_C2_source_jet_repair_endpoint_jets
    B (hr0.trans_le hOrder) (w B) (deriv w B) j
  rcases hEnds with ⟨hV, hD, hDD, hZV, hZD, hZDD⟩
  change rep B = w B ∧
    deriv rep B = deriv w B ∧
    deriv (deriv rep) B = deriv (deriv w) B ∧
    rep (2 * B) = 0 ∧
    deriv rep (2 * B) = 0 ∧
    deriv (deriv rep) (2 * B) = 0
  exact ⟨hV, hD, hDD.trans hJ.symm, hZV, hZD, hZDD⟩

end HBL.TypeIIDynamicSelection
