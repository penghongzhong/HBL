import HBL.TypeIIDynamicSelection.ActualHartreeFixedKummerBasisMovingSpectrum
import HBL.KummerOriginGreen.UniformBound
import Mathlib.Tactic

/-!
# Original normalized Kummer Green: ONE GENUINE positive relative spectral step

Let K0 be the same origin-normalized Wronskian pair for the frozen
spectral parameters (mu0,theta0). Let G0 denote its ACTUAL Green integral
and let d=b(mu(s),theta(s))-b(mu0,theta0), a complex scalar independent
of the spatial radius.

For the real original Hartree source F, the first Green field u0=G0[F]
has spectral defect d*u0. Do NOT merely label that source "higher order":
construct the actual correcting Green field u1=G0[d*u0] with its genuine
Wronskian source. Then the original variable-spectral physical operator
obeys the EXACT cancellation
  L_s (u0-u1) = F - d*u1.
The first-order defect d*u0 has disappeared; the remaining source
is quadratic in the actual physical spectral displacement d.

A second genuine original Green estimate gives directly
  ||L_s(u0-u1)-F|| <= ||d||^2*(2*C^3*(B-a))^2*M,
when F has norm <=M on [a,B] and the fixed original pair has the
actual OriginBasisOn constant C. NO abstract residual order field,
arbitrary right inverse, rate assumption or extra axiom is inserted.

This is a nontrivial physical Kummer-region relative spectral step.
All other original 3D nonlocal Hartree, moving cutoff, far-field and
finite recursion residuals remain separate and essential.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual first spectral correction SOURCE is exactly the
physical displacement d times the original normalized Green field. -/
def actualHartreeOriginalSpectralFirstSource
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a B : ℝ) (F : ℝ → ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  d * originGreenValue K a B F r

/-- The literal first corrected normalized Green field u0-G0[d*u0]. -/
def actualHartreeOriginalSpectralFirstCorrectedField
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a B : ℝ) (F : ℝ → ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  originGreenValue K a B F r -
    originGreenValue K a B
      (actualHartreeOriginalSpectralFirstSource K a B F d) r

/-- The complete variable-spectral physical SECOND-ORDER Kummer jet of
the literal first corrected Green field. Every value, first slope and
second derivative is produced from its original Green functionals. -/
def actualHartreeOriginalSpectralCorrectedJetResidual
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a B : ℝ) (F : ℝ → ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  let Q := actualHartreeOriginalSpectralFirstSource K a B F d
  (originGreenSecond K a B F r - originGreenSecond K a B Q r) +
    frozenFirstCoeff r *
      (originGreenSlope K a B F r - originGreenSlope K a B Q r) +
    (frozenZeroCoeff mu0 theta0 + d) *
      actualHartreeOriginalSpectralFirstCorrectedField K a B F d r

/-- Exact ORIGINAL operator cancellation. There is no hidden
approximation or assigned symbolic generated-order number. -/
theorem actual_Hartree_original_Kummer_first_spectral_correction_exact
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a B : ℝ) (F : ℝ → ℂ) (d : ℂ) (r : ℝ) :
    actualHartreeOriginalSpectralCorrectedJetResidual K a B F d r =
      F r - d * originGreenValue K a B
        (actualHartreeOriginalSpectralFirstSource K a B F d) r := by
  let Q := actualHartreeOriginalSpectralFirstSource K a B F d
  have h0 := originGreen_equation K a B F r
  have h1 := originGreen_equation K a B Q r
  unfold actualHartreeOriginalSpectralCorrectedJetResidual
    actualHartreeOriginalSpectralFirstCorrectedField
  dsimp only
  calc
    _ =
      (originGreenSecond K a B F r +
        frozenFirstCoeff r * originGreenSlope K a B F r +
        frozenZeroCoeff mu0 theta0 * originGreenValue K a B F r) -
      (originGreenSecond K a B Q r +
        frozenFirstCoeff r * originGreenSlope K a B Q r +
        frozenZeroCoeff mu0 theta0 * originGreenValue K a B Q r) +
      d * originGreenValue K a B F r -
      d * originGreenValue K a B Q r := by ring
    _ = F r - Q r + d * originGreenValue K a B F r -
          d * originGreenValue K a B Q r := by rw [h0, h1]
    _ = F r - d * originGreenValue K a B Q r := by
      dsimp [Q, actualHartreeOriginalSpectralFirstSource]
      ring

/-- A real positive relative gain in the SAME original Green source norm:
the actual first-order spectral defect is eliminated and the remaining
source is QUADRATIC in the original spectral difference. -/
theorem actual_Hartree_original_Kummer_first_spectral_correction_quadratic_bound
    {mu0 theta0 scale : ℝ} (K : OriginKummerPair mu0 theta0 scale)
    (a B C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hab : a ≤ B) (hK : OriginBasisOn K a B C)
    (F : ℝ → ℂ) (hF : ∀ x ∈ Icc a B, ‖F x‖ ≤ M)
    (d : ℂ) (r : ℝ) (hr : r ∈ Icc a B) :
    ‖actualHartreeOriginalSpectralCorrectedJetResidual
        K a B F d r - F r‖ ≤
      ‖d‖ ^ 2 * (2 * C ^ 3 * (B-a)) ^ 2 * M := by
  let E : ℝ := 2 * C ^ 3 * (B-a)
  let Q : ℝ → ℂ := actualHartreeOriginalSpectralFirstSource K a B F d
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hField (x : ℝ) (hx : x ∈ Icc a B) :
      ‖originGreenValue K a B F x‖ ≤ E*M := by
    have hFull := originGreen_value_slope_norm_le
      K a B C M hC hM hK F hF hx
    have hn := norm_nonneg (originGreenSlope K a B F x)
    dsimp [E]
    linarith only [hFull, hn]
  have hQ (x : ℝ) (hx : x ∈ Icc a B) :
      ‖Q x‖ ≤ ‖d‖ * (E*M) := by
    dsimp [Q, actualHartreeOriginalSpectralFirstSource]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hField x hx) (norm_nonneg d)
  have hQM : 0 ≤ ‖d‖ * (E*M) := by positivity
  have hNext := originGreen_value_slope_norm_le
    K a B C (‖d‖ * (E*M)) hC hQM hK Q hQ hr
  have hNextValue : ‖originGreenValue K a B Q r‖ ≤
      E * (‖d‖ * (E*M)) := by
    have hn := norm_nonneg (originGreenSlope K a B Q r)
    dsimp [E]
    linarith only [hNext, hn]
  have hExact := actual_Hartree_original_Kummer_first_spectral_correction_exact
    K a B F d r
  have hDifference :
      actualHartreeOriginalSpectralCorrectedJetResidual K a B F d r -
        F r = -(d * originGreenValue K a B Q r) := by
    rw [hExact]
    dsimp only [Q]
    ring
  rw [hDifference, norm_neg, norm_mul]
  calc
    ‖d‖ * ‖originGreenValue K a B Q r‖ ≤
        ‖d‖ * (E * (‖d‖ * (E*M))) :=
      mul_le_mul_of_nonneg_left hNextValue (norm_nonneg d)
    _ = ‖d‖ ^ 2 * E ^ 2 * M := by ring
    _ = _ := by rfl

end HBL.TypeIIDynamicSelection
