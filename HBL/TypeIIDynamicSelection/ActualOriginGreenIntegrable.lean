import HBL.KummerOriginGreen.UniformBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
The manuscript's ORIGINAL origin-normalized Green inverse for integrable
forcing. The two source integrals are proved integrable before differentiation;
the actual first-order differential system then holds almost everywhere.
No continuity of the nonlocal Hartree forcing, new normalized pair, or
independently imposed outer Cauchy trace is used.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Both original Wronskian densities are genuinely interval integrable. -/
theorem actual_origin_Green_source_integrability
    {mu theta R a b C : ℝ} (K : OriginKummerPair mu theta R)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume a b) :
    IntervalIntegrable (originGreenSourceA K F) volume a b ∧
    IntervalIntegrable (originGreenSourceB K F) volume a b := by
  have hCont :
      ContinuousOn (fun r => originPhysicalValue K.x r / originGreenWronskian K r)
        (uIcc a b) ∧
      ContinuousOn (fun r => originPhysicalValue K.y r / originGreenWronskian K r)
        (uIcc a b) := by
    rw [uIcc_of_le hab]
    constructor
    · intro r hr
      rcases hK r hr with ⟨hphi, hdphi, hpsi, hdpsi, _, hW, _, _, _, _, _⟩
      have hw : ContinuousAt (originGreenWronskian K) r :=
        (hphi.continuousAt.mul hdpsi.continuousAt).sub
          (hdphi.continuousAt.mul hpsi.continuousAt)
      exact (hpsi.continuousAt.div hw hW).continuousWithinAt
    · intro r hr
      rcases hK r hr with ⟨hphi, hdphi, hpsi, hdpsi, _, hW, _, _, _, _, _⟩
      have hw : ContinuousAt (originGreenWronskian K) r :=
        (hphi.continuousAt.mul hdpsi.continuousAt).sub
          (hdphi.continuousAt.mul hpsi.continuousAt)
      exact (hphi.continuousAt.div hw hW).continuousWithinAt
  constructor
  · convert hF.continuousOn_mul hCont.1 using 1
    funext r
    simp only [originGreenSourceA, div_eq_mul_inv]
    ring
  · convert hF.continuousOn_mul hCont.2 using 1
    funext r
    simp only [originGreenSourceB, div_eq_mul_inv]
    ring

/-- The ORIGINAL Green value and slope satisfy the actual forced Kummer
system almost everywhere for merely interval-integrable forcing. The
second component is a genuine derivative, not an algebraically named proxy. -/
theorem actual_origin_Green_integrable_forcing_ae_equation
    {mu theta R a b C : ℝ} (K : OriginKummerPair mu theta R)
    (hK : OriginBasisOn K a b C) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume a b) :
    ∀ᵐ r ∂volume, r ∈ Icc a b →
      HasDerivAt (originGreenValue K a b F) (originGreenSlope K a b F r) r ∧
      HasDerivAt (originGreenSlope K a b F) (originGreenSecond K a b F r) r ∧
      originGreenSecond K a b F r +
        frozenFirstCoeff r * originGreenSlope K a b F r +
        frozenZeroCoeff mu theta * originGreenValue K a b F r = F r := by
  obtain ⟨hIA, hIB⟩ := actual_origin_Green_source_integrability K hK hab F hF
  have hA := hIA.ae_hasDerivAt_integral
  have hB := hIB.ae_hasDerivAt_integral
  rw [uIcc_of_le hab] at hA hB
  filter_upwards [hA, hB] with r hAr hBr
  intro hr
  have ha : a ∈ Icc a b := ⟨le_refl _, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_refl _⟩
  have hCA : HasDerivAt (originGreenCoeffA K b F) (-originGreenSourceA K F r) r := by
    have hfun : originGreenCoeffA K b F =
        (fun t => -(∫ s in b..t, originGreenSourceA K F s)) := by
      funext t
      exact intervalIntegral.integral_symm b t
    rw [hfun]
    exact (hAr hr b hb).neg
  have hCB : HasDerivAt (originGreenCoeffB K a F) (originGreenSourceB K F r) r :=
    hBr hr a ha
  rcases hK r hr with ⟨hphi, hdphi, hpsi, hdpsi, _, hW, _, _, _, _, _⟩
  have hValue : HasDerivAt (originGreenValue K a b F)
      (originGreenSlope K a b F r) r := by
    have h := (hphi.mul hCA).add (hpsi.mul hCB)
    convert h using 1
    · rfl
    · unfold originGreenSlope originGreenSourceA originGreenSourceB
      ring
  have hSlope : HasDerivAt (originGreenSlope K a b F)
      (originGreenSecond K a b F r) r := by
    have h := (hdphi.mul hCA).add (hdpsi.mul hCB)
    convert h using 1
    · rfl
    · unfold originGreenSecond originGreenSourceA originGreenSourceB originGreenWronskian
      field_simp [hW]
      ring
  exact ⟨hValue, hSlope, originGreen_equation K a b F r⟩

end HBL.TypeIIDynamicSelection
