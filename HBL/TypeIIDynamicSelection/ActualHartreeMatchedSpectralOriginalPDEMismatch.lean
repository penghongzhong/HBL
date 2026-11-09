import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralLeftC1Exact
import Mathlib.Tactic

/-!
# Original (unshifted) Hartree/Kummer PDE source after spectral correction

The spectral correction w_delta = u0 - w1 preserves the original Fredholm
Cauchy jet, but w1 solves L0 w1 = delta u0. Therefore the ORIGINAL
unshifted operator has source F - delta u0, not a quadratic
delta^2 w1 source. The quadratic shifted-operator residual must never
be substituted for this original physical PDE source.

Both the normalized equation and its exact y/a physical pullback
are derived from genuine Cramer/Volterra solutions, without assuming
a new original-source envelope, spatial time gain or blowup rate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Exact ORIGINAL normalized operator, not the shifted quadratic one.
The first-order spectral source -delta*u0 is retained explicitly. -/
theorem actual_Hartree_matched_spectral_original_unshifted_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (r0 r1 : ℝ) (hr0 : 0 < r0) (horder : r0 ≤ r1) (hr1 : r1 < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (U DU delta : ℂ) :
    let u0 := actualOriginMatchedKummerValue K r0 r1 F U DU
    let w := actualHartreeMatchedSpectralCorrectedValue K r0 r1 F U DU delta
    ∀ r ∈ Ioo (0 : ℝ) scale,
      deriv (deriv w) r + frozenFirstCoeff r * deriv w r +
        frozenZeroCoeff mu theta * w r = F r - delta * u0 r := by
  dsimp only
  let u0 := actualOriginMatchedKummerValue K r0 r1 F U DU
  let q := actualHartreeMatchedSpectralFirstSource K r0 r1 F U DU delta
  let w1 := actualOriginMatchedKummerValue K r0 r1 q 0 0
  let w := actualHartreeMatchedSpectralCorrectedValue K r0 r1 F U DU delta
  have hOriginal :=
    actual_Hartree_matched_spectral_corrected_left_C1_and_exact_equation
      K r0 r1 hr0 horder hr1 F hF U DU delta
  dsimp only at hOriginal
  intro r hr
  have hShift :
      deriv (deriv w) r + frozenFirstCoeff r * deriv w r +
        (frozenZeroCoeff mu theta + delta) * w r =
          F r - delta * w1 r := hOriginal.2.2 r hr
  have hw : w r = u0 r - w1 r := rfl
  calc
    deriv (deriv w) r + frozenFirstCoeff r * deriv w r +
        frozenZeroCoeff mu theta * w r =
        (deriv (deriv w) r + frozenFirstCoeff r * deriv w r +
          (frozenZeroCoeff mu theta + delta) * w r) -
            delta * w r := by ring
    _ = (F r - delta * w1 r) - delta * w r := by rw [hShift]
    _ = F r - delta * u0 r := by rw [hw]; ring

/-- Literal physical spectral four-piece Kummer-region continuation. -/
def actualHartreeMatchedSpectralPhysicalValue
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a r0 r1 : ℝ) (F : ℝ → ℂ) (U DU delta : ℂ)
    (y : ℝ) : ℂ :=
  actualHartreeMatchedSpectralCorrectedValue K r0 r1 F U DU delta (y / a)

/-- Linear subtraction for the ORIGINAL scaled Kummer operator, justified
by actual first- and second-derivative regularity on an open region. -/
private theorem actual_spectral_scaled_Kummer_sub_on_open
    (mu theta a : ℝ) (u v : ℝ → ℂ) (D : Set ℝ)
    (hD : IsOpen D)
    (hu : ∀ x ∈ D, DifferentiableAt ℝ u x)
    (hv : ∀ x ∈ D, DifferentiableAt ℝ v x)
    (r : ℝ) (hr : r ∈ D)
    (hu2 : DifferentiableAt ℝ (deriv u) r)
    (hv2 : DifferentiableAt ℝ (deriv v) r) :
    actualMatchedScaledKummerApply mu theta a (fun x => u x - v x) r =
      actualMatchedScaledKummerApply mu theta a u r -
        actualMatchedScaledKummerApply mu theta a v r := by
  have hfirst (x : ℝ) (hx : x ∈ D) :
      HasDerivAt (fun y => u y - v y) (deriv u x - deriv v x) x :=
    (hu x hx).hasDerivAt.sub (hv x hx).hasDerivAt
  have hnear : deriv (fun x => u x - v x) =ᶠ[𝓝 r]
      (fun x => deriv u x - deriv v x) := by
    filter_upwards [hD.mem_nhds hr] with x hx
    exact (hfirst x hx).deriv
  have hsecond :=
    (hu2.hasDerivAt.sub hv2.hasDerivAt).congr_of_eventuallyEq hnear
  unfold actualMatchedScaledKummerApply complexRadialLaplacian
  rw [hsecond.deriv, (hfirst r hr).deriv]
  simp only [Complex.real_smul]
  ring

/-- The EXACT physical unshifted Kummer equation for the spectral
correction at a moving physical radius y=a*r. In particular, the source
contains the original first-order -delta*u0, not merely the shifted
quadratic defect -delta*w1. -/
theorem actual_Hartree_matched_spectral_original_physical_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a r0 r1 : ℝ) (ha : 0 < a)
    (hr0 : 0 < r0) (horder : r0 ≤ r1) (hr1 : r1 < scale)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (U DU delta : ℂ) :
    ∀ y ∈ Ioo (0 : ℝ) (a * scale),
      actualMatchedScaledKummerApply mu theta a
        (actualHartreeMatchedSpectralPhysicalValue
          K a r0 r1 F U DU delta) y =
      ((a ^ 2)⁻¹ : ℝ) •
        (F (y / a) -
          delta * actualOriginMatchedKummerValue K r0 r1 F U DU (y / a)) := by
  let u0 : ℝ → ℂ := actualOriginMatchedKummerValue K r0 r1 F U DU
  let q : ℝ → ℂ :=
    actualHartreeMatchedSpectralFirstSource K r0 r1 F U DU delta
  let v0 := actualOriginMatchedKummerPullback K a r0 r1 F U DU
  let v1 := actualOriginMatchedKummerPullback K a r0 r1 q 0 0
  have hClassic :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K hr0 horder hr1 F hF U DU
  have hqCont : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt q r := by
    intro r hr
    change ContinuousAt (fun x : ℝ => delta * u0 x) r
    exact continuousAt_const.mul (hClassic r hr).1.continuousAt
  have hP0 :=
    actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hr1 F hF U DU
  have hP1 :=
    actual_Hartree_matched_Kummer_pullback_classical
      K a ha hr0 horder hr1 q hqCont 0 0
  let D : Set ℝ := Ioo (0 : ℝ) (a * scale)
  have hD : IsOpen D := isOpen_Ioo
  have hV0 (y : ℝ) (hy : y ∈ D) : DifferentiableAt ℝ v0 y :=
    (hP0 y hy).1.differentiableAt
  have hV1 (y : ℝ) (hy : y ∈ D) : DifferentiableAt ℝ v1 y :=
    (hP1 y hy).1.differentiableAt
  intro y hy
  have hSub :=
    actual_spectral_scaled_Kummer_sub_on_open
      mu theta a v0 v1 D hD hV0 hV1 y hy
      (hP0 y hy).2.1 (hP1 y hy).2.1
  change actualMatchedScaledKummerApply mu theta a
      (fun x => v0 x - v1 x) y =
        ((a ^ 2)⁻¹ : ℝ) • (F (y / a) - delta * u0 (y / a))
  calc
    actualMatchedScaledKummerApply mu theta a
        (fun x => v0 x - v1 x) y =
      actualMatchedScaledKummerApply mu theta a v0 y -
        actualMatchedScaledKummerApply mu theta a v1 y := hSub
    _ = ((a ^ 2)⁻¹ : ℝ) • F (y / a) -
        ((a ^ 2)⁻¹ : ℝ) • q (y / a) := by
      rw [(hP0 y hy).2.2, (hP1 y hy).2.2]
    _ = ((a ^ 2)⁻¹ : ℝ) • (F (y / a) - delta * u0 (y / a)) := by
      dsimp only [q, actualHartreeMatchedSpectralFirstSource]
      simp only [Complex.real_smul]
      ring

end HBL.TypeIIDynamicSelection
