import HBL.KummerOriginBasis.CompactBasis
import HBL.KummerLocalInverse.CoefficientDerivatives

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Profile.Kummer

/-- The determinant of the ACTUAL origin-normalized physical fundamental pair.
It is not the center-normalized determinant from LocalKummerPair. -/
def originGreenWronskian {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (r : ℝ) : ℂ :=
  originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
    originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r

/-- The manuscript outgoing coefficient on the upper endpoint. -/
def originGreenSourceA {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalValue K.x r * F r / originGreenWronskian K r

/-- The manuscript outgoing coefficient on the lower endpoint. -/
def originGreenSourceB {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalValue K.y r * F r / originGreenWronskian K r

def originGreenCoeffA {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (b : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in r..b, originGreenSourceA K F s

def originGreenCoeffB {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a : ℝ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in a..r, originGreenSourceB K F s

/-- The exact two-endpoint Green formula in the manuscript's origin gauge. -/
def originGreenValue {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ)
    (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalValue K.y r * originGreenCoeffA K b F r +
    originPhysicalValue K.x r * originGreenCoeffB K a F r

def originGreenSlope {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ)
    (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalSlope K.y K.dy r * originGreenCoeffA K b F r +
    originPhysicalSlope K.x K.dx r * originGreenCoeffB K a F r

def originGreenSecond {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ)
    (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(frozenFirstCoeff r * originPhysicalSlope K.y K.dy r +
      frozenZeroCoeff mu theta * originPhysicalValue K.y r) *
      originGreenCoeffA K b F r +
    -(frozenFirstCoeff r * originPhysicalSlope K.x K.dx r +
      frozenZeroCoeff mu theta * originPhysicalValue K.x r) *
      originGreenCoeffB K a F r + F r

/-- An already-certified origin fundamental pair has the EXACT Wronskian. -/
theorem originGreenWronskian_exact {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C r : ℝ}
    (hK : OriginBasisOn K a b C) (hr : r ∈ Icc a b) :
    originGreenWronskian K r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) := by
  rcases hK r hr with ⟨_, _, _, _, hW, _, _, _, _, _, _⟩
  exact hW

theorem originGreenWronskian_ne {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C r : ℝ}
    (hK : OriginBasisOn K a b C) (hr : r ∈ Icc a b) :
    originGreenWronskian K r ≠ 0 := by
  rcases hK r hr with ⟨_, _, _, _, _, hW, _, _, _, _, _⟩
  exact hW

/-- The integral densities are continuous throughout the prescribed annulus. -/
theorem originGreen_sources_continuous {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ r ∈ Icc a b,
      ContinuousAt (originGreenSourceA K F) r ∧
      ContinuousAt (originGreenSourceB K F) r) ∧
    ContinuousOn (originGreenSourceA K F) (Icc a b) ∧
    ContinuousOn (originGreenSourceB K F) (Icc a b) := by
  have hc (r : ℝ) (hr : r ∈ Icc a b) :
      ContinuousAt (originGreenSourceA K F) r ∧
      ContinuousAt (originGreenSourceB K F) r := by
    rcases hK r hr with ⟨hphi, hdphi, hpsi, hdpsi, _, hW, _, _, _, _, _⟩
    have hw : ContinuousAt (originGreenWronskian K) r := by
      dsimp [originGreenWronskian]
      exact (hphi.continuousAt.mul hdpsi.continuousAt).sub
        (hdphi.continuousAt.mul hpsi.continuousAt)
    exact ⟨(hpsi.continuousAt.mul hF.continuousAt).div hw hW,
      (hphi.continuousAt.mul hF.continuousAt).div hw hW⟩
  exact ⟨hc, fun r hr => (hc r hr).1.continuousWithinAt,
    fun r hr => (hc r hr).2.continuousWithinAt⟩

/-- The two integral coefficients have the actual endpoint derivatives. -/
theorem originGreen_coefficients_hasDerivAt {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a < b)
    (F : ℝ → ℂ) (hF : Continuous F) {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (originGreenCoeffA K b F) (-originGreenSourceA K F r) r ∧
    HasDerivAt (originGreenCoeffB K a F) (originGreenSourceB K F r) r := by
  have hc := originGreen_sources_continuous K hK F hF
  have ha : a ∈ Icc a b := ⟨le_refl _, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_refl _⟩
  have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
  have hmA := hc.2.1.stronglyMeasurableAtFilter_nhdsWithin
    (μ := volume) measurableSet_Icc r
  have hmB := hc.2.2.stronglyMeasurableAtFilter_nhdsWithin
    (μ := volume) measurableSet_Icc r
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hr.1 hr.2)] at hmA hmB
  exact ⟨intervalIntegral.integral_hasDerivAt_left
    (hc.2.1.mono (uIcc_subset_Icc hr' hb)).intervalIntegrable hmA (hc.1 r hr').1,
    intervalIntegral.integral_hasDerivAt_right
    (hc.2.2.mono (uIcc_subset_Icc ha hr')).intervalIntegrable hmB (hc.1 r hr').2⟩

/-- First derivative: cancellation of variation-of-constants cross terms. -/
theorem originGreenValue_hasDerivAt {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a < b)
    (F : ℝ → ℂ) (hF : Continuous F) {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (originGreenValue K a b F) (originGreenSlope K a b F r) r := by
  have hc := originGreen_coefficients_hasDerivAt K hK hab F hF hr
  have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
  rcases hK r hr' with ⟨hphi, _, hpsi, _, _, _, _, _, _, _, _⟩
  have h := (hphi.mul hc.1).add (hpsi.mul hc.2)
  convert h using 1
  · rfl
  · unfold originGreenSlope originGreenSourceA originGreenSourceB
    ring

/-- Second derivative: the physical Wronskian supplies exactly F. -/
theorem originGreenSlope_hasDerivAt {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a < b)
    (F : ℝ → ℂ) (hF : Continuous F) {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (originGreenSlope K a b F) (originGreenSecond K a b F r) r := by
  have hc := originGreen_coefficients_hasDerivAt K hK hab F hF hr
  have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
  rcases hK r hr' with ⟨_, hdphi, _, hdpsi, _, hW, _, _, _, _, _⟩
  have h := (hdphi.mul hc.1).add (hdpsi.mul hc.2)
  convert h using 1
  · rfl
  · unfold originGreenSecond originGreenSourceA originGreenSourceB originGreenWronskian
    field_simp [hW]
    ring

/-- The actual frozen Kummer equation, NOT an abstract right-inverse hypothesis. -/
theorem originGreen_equation {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ)
    (F : ℝ → ℂ) (r : ℝ) :
    originGreenSecond K a b F r +
      frozenFirstCoeff r * originGreenSlope K a b F r +
      frozenZeroCoeff mu theta * originGreenValue K a b F r = F r := by
  unfold originGreenSecond originGreenSlope originGreenValue
  ring

/-- Both manuscript outgoing endpoint functionals vanish identically. -/
theorem originGreen_endpoint_normalization {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b : ℝ) (F : ℝ → ℂ) :
    originGreenCoeffA K b F b = 0 ∧
    originGreenCoeffB K a F a = 0 ∧
    (originGreenValue K a b F b * originPhysicalSlope K.x K.dx b -
      originGreenSlope K a b F b * originPhysicalValue K.x b = 0) ∧
    (originPhysicalValue K.y a * originGreenSlope K a b F a -
      originPhysicalSlope K.y K.dy a * originGreenValue K a b F a = 0) := by
  have hA : originGreenCoeffA K b F b = 0 := by
    simp [originGreenCoeffA]
  have hB : originGreenCoeffB K a F a = 0 := by
    simp [originGreenCoeffB]
  refine ⟨hA, hB, ?_, ?_⟩
  · unfold originGreenValue originGreenSlope
    rw [hA]
    ring
  · unfold originGreenValue originGreenSlope
    rw [hB]
    ring

/-- The source-independent, physically normalized Green construction solves the
actual ODE on the open prescribed annulus and both endpoint conditions. -/
theorem originGreen_classical_outgoing {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a < b)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∀ r ∈ Ioo a b,
      HasDerivAt (originGreenValue K a b F) (originGreenSlope K a b F r) r ∧
      HasDerivAt (originGreenSlope K a b F) (originGreenSecond K a b F r) r ∧
      originGreenSecond K a b F r +
        frozenFirstCoeff r * originGreenSlope K a b F r +
        frozenZeroCoeff mu theta * originGreenValue K a b F r = F r) ∧
    (originGreenValue K a b F b * originPhysicalSlope K.x K.dx b -
      originGreenSlope K a b F b * originPhysicalValue K.x b = 0) ∧
    (originPhysicalValue K.y a * originGreenSlope K a b F a -
      originPhysicalSlope K.y K.dy a * originGreenValue K a b F a = 0) := by
  refine ⟨?_, (originGreen_endpoint_normalization K a b F).2.2.1,
    (originGreen_endpoint_normalization K a b F).2.2.2⟩
  intro r hr
  exact ⟨originGreenValue_hasDerivAt K hK hab F hF hr,
    originGreenSlope_hasDerivAt K hK hab F hF hr,
    originGreen_equation K a b F r⟩

end HBL.Profile.Kummer
