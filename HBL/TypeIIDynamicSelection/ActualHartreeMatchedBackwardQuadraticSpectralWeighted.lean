import HBL.TypeIIDynamicSelection.ActualHartreeMatchedBackwardQuadraticSpectralSource
import HBL.TypeIIDynamicSelection.ActualHartreeShellWeightedNorm
import Mathlib.Tactic

/-!
# Original Hartree matched backward QUADRATIC spectral source: actual L²_{7/4} bound

This theorem composes the actual same-source Fredholm two-channel matched
Kummer field, the genuine inverse-linear zero-Cauchy Volterra correction
BELOW its matching anchor, and the ORIGINAL radial-conjugated 7/4-weighted
source norm. It never treats the source as a radius-independent atom.

In particular the quadratic field is not an independently assumed bound:
it is the exact u1=G_K0[delta*u0;0,0] on [L/(2a),L/a].
The geometric radius factor R^(13/4) remains visible, as does the physical
a^(-2) scale. The true Hartree inner plateau is a separate, strictly
proved producer of the same-source equation; the time-dependent global
four-zone nonlinear residual, its parameter Lipschitz estimate, and
actual finite recursion are NOT conclusions here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The original radial-conjugated spatial norm of the true quadratic
selected spectral correction on the genuine backward physical shell. -/
theorem actual_Hartree_matched_backward_quadratic_spectral_source_weighted
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a R B C G : ℝ)
    (ha : 0 < a) (hR : 2 < R)
    (hOrder : 2 * R / a ≤ B) (hB : B < scale)
    (hG : 0 ≤ G)
    (hK : OriginBasisOn K (2 * R / a) B C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (hSmall : 16 * R ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (hSame : ∀ y ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a
        (actualOriginMatchedKummerPullback K a (2 * R / a) B
          F
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2) y =
        -actualHartreeTwoChannelPhysicalSource Fp Fm y)
    (delta : ℂ)
    (hInt : ∀ x ∈ Icc ((2 * R / a) / 2) (2 * R / a),
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (2 * R / a) B F
            (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
            (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2 t))
        volume x (2 * R / a))
    (hIntR : IntervalIntegrable
      (originGreenSourceA K
        (fun t => delta * actualOriginMatchedKummerValue K
          (2 * R / a) B F
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2 t))
      volume (2 * R / a) B)
    (hMeas : ∀ U DU : ℂ,
      Measurable (fun y : ℝ =>
        (((a ^ 2)⁻¹ : ℝ) : ℂ) *
          (delta * actualOriginMatchedKummerValue K (2 * R / a) B
            (fun x => delta *
              actualOriginMatchedKummerValue K (2 * R / a) B F U DU x)
            0 0 (y / a)))) :
    let r0 := 2 * R / a
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
    let u0 := actualOriginMatchedKummerValue K r0 B F J.1 J.2
    let u1 := actualOriginMatchedKummerValue K r0 B
      (fun x => delta * u0 x) 0 0
    let E : ℝ → ℂ := fun y =>
      (((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))
    let D := actualInnerShellValueConstant *
      (innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm) +
      8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
    let A := ((a ^ 2)⁻¹ * ‖delta‖) *
      (2 * G ^ 2 * (r0 * ‖delta‖ * D))
    InWeightedL2 (7 / 4 : ℝ) (actualConjugatedShellMagnitude R E) ∧
      innerWeightedNorm (7 / 4 : ℝ)
        (actualConjugatedShellMagnitude R E) ≤
        20 * R ^ (13 / 4 : ℝ) * A := by
  dsimp only
  let r0 : ℝ := 2 * R / a
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
  let u0 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 B F J.1 J.2
  let u1 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 B
    (fun x => delta * u0 x) 0 0
  let E : ℝ → ℂ := fun y =>
    (((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))
  let D : ℝ := actualInnerShellValueConstant *
      (innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm) +
      8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
  let A : ℝ := ((a ^ 2)⁻¹ * ‖delta‖) *
    (2 * G ^ 2 * (r0 * ‖delta‖ * D))
  have hPt (y : ℝ) (hy : y ∈ Icc R (2 * R)) : ‖E y‖ ≤ A := by
    have h := actual_Hartree_matched_backward_quadratic_spectral_source
      K a R B C G ha hR hOrder hB hG hK hModes hSmall
      Fp Fm hp hm hcp hcm F hF hSame delta hInt hIntR y hy
    change ‖E y‖ ≤ A at h
    exact h
  have hRone : 1 ≤ R := by linarith
  have hRin : R ∈ Icc R (2 * R) := ⟨le_rfl, by linarith⟩
  have hA : 0 ≤ A := (norm_nonneg (E R)).trans (hPt R hRin)
  have hEMeas : Measurable E := by
    dsimp only [E, u1, u0, J, r0]
    exact hMeas
      (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
      (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2
  exact actual_conjugated_shell_weighted_power_bound
    R A hRone hA E hEMeas hPt

end HBL.TypeIIDynamicSelection
