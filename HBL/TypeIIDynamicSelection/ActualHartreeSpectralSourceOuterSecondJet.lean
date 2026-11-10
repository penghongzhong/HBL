import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralOriginalPDEMismatch
import HBL.TypeIIDynamicSelection.ActualHartreeC2SourceJetRepair
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSecondJetThreePiece
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


/-- The ACTUAL source-selected spectral Green solution and its *original*
curvature (not a free interpolation datum) now form a genuinely twice
differentiable normalized outer Green/repair/zero field at both endpoints.
The Fredholm left join and full physical nonlinear residual remain open. -/
theorem actual_Hartree_spectral_same_source_outer_splice_C2
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
    let full := actualHartreeSecondJetThreePiece B (2 * B) w rep
    HasDerivAt full (deriv w B) B ∧
    HasDerivAt (deriv full) (deriv (deriv w) B) B ∧
    HasDerivAt full 0 (2 * B) ∧
    HasDerivAt (deriv full) 0 (2 * B) := by
  dsimp only
  let u0 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 B F U DU
  let q : ℝ → ℂ :=
    actualHartreeMatchedSpectralFirstSource K r0 B F U DU delta
  let w1 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 B q 0 0
  let w : ℝ → ℂ :=
    actualHartreeMatchedSpectralCorrectedValue K r0 B F U DU delta
  let j : ℂ := F B - delta * u0 B -
      frozenFirstCoeff B * deriv w B -
      frozenZeroCoeff mu theta * w B
  let rep : ℝ → ℂ := actualHartreeC2SourceJetRepair B (w B) (deriv w B) j
  let full : ℝ → ℂ := actualHartreeSecondJetThreePiece B (2 * B) w rep
  have hBpos : 0 < B := hr0.trans_le hOrder
  have hBdomain : B ∈ Ioo (0 : ℝ) scale := ⟨hBpos, hB⟩
  have hU :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K hr0 hOrder hB F hF U DU
  have hqCont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt q x := by
    intro x hx
    change ContinuousAt (fun t : ℝ => delta * u0 t) x
    exact continuousAt_const.mul (hU x hx).1.continuousAt
  have hV :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K hr0 hOrder hB q hqCont 0 0
  have hW : HasDerivAt w (deriv w B) B := by
    change HasDerivAt (fun x => u0 x - w1 x) (deriv w B) B
    exact ((hU B hBdomain).1.sub (hV B hBdomain).1).differentiableAt.hasDerivAt
  have hNearDeriv :
      deriv w =ᶠ[𝓝 B] (fun x => deriv u0 x - deriv w1 x) := by
    filter_upwards [Ioo_mem_nhds hBdomain.1 hBdomain.2] with x hx
    change deriv (fun y => u0 y - w1 y) x =
      deriv u0 x - deriv w1 x
    exact ((hU x hx).1.sub (hV x hx).1).deriv
  have hW2 : HasDerivAt (deriv w) (deriv (deriv w) B) B := by
    have hdiff := (hU B hBdomain).2.1.sub (hV B hBdomain).2.1
    have h := hdiff.congr_of_eventuallyEq hNearDeriv
    exact h.differentiableAt.hasDerivAt
  have hJ : deriv (deriv w) B = j :=
    actual_Hartree_spectral_second_jet_from_same_original_source
      K r0 B hr0 hOrder hB F hF U DU delta
  have hEnds :=
    actual_Hartree_spectral_source_locked_outer_C2_repair_jets
      K r0 B hr0 hOrder hB F hF U DU delta
  dsimp only at hEnds
  rcases hEnds with ⟨hVal, _, _, hFar, _, _⟩
  have hLeftBound : B < B + B / 3 := by linarith
  have hRightBound : B + 2 * (B / 3) < 2 * B := by linarith
  have hRepNearLeft :
      rep =ᶠ[𝓝 B] actualHartreeC2RepairPolynomial B (w B) (deriv w B) j := by
    filter_upwards [Iio_mem_nhds hLeftBound] with x hx
    change actualKummerRepairCutoff B x *
        actualHartreeC2RepairPolynomial B (w B) (deriv w B) j x =
      actualHartreeC2RepairPolynomial B (w B) (deriv w B) j x
    have hc : cutoff ((x - B) / (B / 3)) = 0 :=
      cutoff_zero_of_le_one _
        ((div_le_one (by positivity)).2 (by linarith))
    simp [actualKummerRepairCutoff, actualOneLayerInnerOverlapCutoff, hc]
  have hRepNearRight : rep =ᶠ[𝓝 (2 * B)] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hRightBound] with x hx
    change actualKummerRepairCutoff B x *
        actualHartreeC2RepairPolynomial B (w B) (deriv w B) j x = 0
    have hc : cutoff ((x - B) / (B / 3)) = 1 :=
      cutoff_one_of_two_le _
        ((le_div_iff₀ (by positivity)).2 (by linarith))
    simp [actualKummerRepairCutoff, actualOneLayerInnerOverlapCutoff, hc]
  have hDerNearLeft :
      deriv rep =ᶠ[𝓝 B]
        deriv (actualHartreeC2RepairPolynomial B (w B) (deriv w B) j) := by
    filter_upwards [Iio_mem_nhds hLeftBound] with x hx
    have hlocal :
        rep =ᶠ[𝓝 x] actualHartreeC2RepairPolynomial B (w B) (deriv w B) j := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change actualKummerRepairCutoff B y *
          actualHartreeC2RepairPolynomial B (w B) (deriv w B) j y =
        actualHartreeC2RepairPolynomial B (w B) (deriv w B) j y
      have hc : cutoff ((y - B) / (B / 3)) = 0 :=
        cutoff_zero_of_le_one _
          ((div_le_one (by positivity)).2 (by linarith))
      simp [actualKummerRepairCutoff, actualOneLayerInnerOverlapCutoff, hc]
    exact hlocal.deriv_eq
  have hDerNearRight :
      deriv rep =ᶠ[𝓝 (2 * B)] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hRightBound] with x hx
    have hlocal : rep =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change actualKummerRepairCutoff B y *
          actualHartreeC2RepairPolynomial B (w B) (deriv w B) j y = 0
      have hc : cutoff ((y - B) / (B / 3)) = 1 :=
        cutoff_one_of_two_le _
          ((le_div_iff₀ (by positivity)).2 (by linarith))
      simp [actualKummerRepairCutoff, actualOneLayerInnerOverlapCutoff, hc]
    rw [hlocal.deriv_eq]
    exact deriv_const x (0 : ℂ)
  have hRep1 : HasDerivAt rep (deriv w B) B := by
    have h := actual_Hartree_C2_repair_polynomial_hasDerivAt
      B B (w B) (deriv w B) j
    have heq : deriv w B + ((B - B : ℝ) : ℂ) * j = deriv w B := by simp
    rw [heq] at h
    exact h.congr_of_eventuallyEq hRepNearLeft
  have hRep2 : HasDerivAt (deriv rep) (deriv (deriv w) B) B := by
    have h := (actual_Hartree_C2_repair_polynomial_second_hasDerivAt
      B B (w B) (deriv w B) j).congr_of_eventuallyEq hDerNearLeft
    rw [hJ]
    exact h
  have hFar1 : HasDerivAt rep 0 (2 * B) :=
    (hasDerivAt_const (2 * B) (0 : ℂ)).congr_of_eventuallyEq hRepNearRight
  have hFar2 : HasDerivAt (deriv rep) 0 (2 * B) :=
    (hasDerivAt_const (2 * B) (0 : ℂ)).congr_of_eventuallyEq hDerNearRight
  have hAB : B < 2 * B := by linarith
  have hThree := actual_Hartree_second_jet_three_piece_C2_interfaces
    B (2 * B) hAB w rep (deriv w B) (deriv (deriv w) B)
    hW hRep1 hVal hW2 hRep2 hFar1 hFar hFar2
  simpa only [full, actualHartreeSecondJetThreePiece] using hThree


end HBL.TypeIIDynamicSelection
