import HBL.TypeIIDynamicSelection.ActualHartreeOriginOutgoingTraceNoRadiusLoss
import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalJetBound
import Mathlib.Tactic

/-!
# Same actual Fredholm source controls the origin Kummer singular trace

The matched left Cauchy jet is not independent Kummer data: the original
two-channel weighted Hartree Fredholm inverse produces both coordinates.
Its source norm bounds |U|+(L/a)|DU| uniformly in the moving physical
scale. The regular origin Kummer mode and exact Wronskian then provide
another factor L/a for the genuine outgoing Wronskian trace.

This is the exact source-to-shrinking-interface estimate required by the
compatibility-cancelled physical Green branch. It has neither a guessed
homogeneous amplitude nor a fixed Type-II rate. The full spatial/time
Hartree residual O(s^(-9/4)) is not proved here.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

theorem actual_Hartree_original_Fredholm_outgoing_trace_source_radius_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B L a : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBScale : B ≤ scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧
        ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hL : 2 < L) (ha : 0 < a) (hLB : L / a ≤ B)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
    let Csrc := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
    let Cbasis := 1 + (D + 1) * G * (B ^ 2 + 2)
    ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
      Cbasis * (L / a) * (Csrc * N) := by
  dsimp only
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let N := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let Csrc := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let Cbasis := 1 + (D + 1) * G * (B ^ 2 + 2)
  have hLp : 0 < L := by linarith
  have hr0 : 0 ≤ L / a := (div_pos hLp ha).le
  have hCr : 0 ≤ Cbasis := by dsimp [Cbasis]; positivity
  have hRadius : L / a ∈ Ioc (0 : ℝ) B :=
    ⟨div_pos hLp ha, hLB⟩
  have hJet :=
    actual_Hartree_canonical_inner_jet_source_norm_bound
      Fp Fm hp hm hcp hcm L a hL ha
  have hTrace :=
    actual_Hartree_origin_outgoing_trace_without_inverse_radius_loss
      K D G B (L / a) hD hG hB hBOne hBScale
      hcoeff hbound hRadius J.1 J.2
  dsimp only at hJet hTrace
  have hFactor : 0 ≤ Cbasis * (L / a) :=
    mul_nonneg hCr hr0
  calc
    ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
      Cbasis * (L / a) * (‖J.1‖ + (L / a) * ‖J.2‖) := by
        simpa only [Cbasis] using hTrace
    _ ≤ Cbasis * (L / a) * (Csrc * N) :=
      mul_le_mul_of_nonneg_left (by simpa only [J, Csrc, N] using hJet)
        hFactor

end HBL.TypeIIDynamicSelection
