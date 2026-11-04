import HBL.TypeIIDynamicSelection.ActualOriginProjectionCancellation
import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalTransmission

/-!
The same physical inner solution, original scaled Hartree source and retained
interface error now share one exact compatibility projection. Its vanishing
is exactly the condition for a homogeneous, source-preserving transmission.
No vanishing, modulation nondegeneracy or relative residual gain is postulated
as a physical conclusion. The actual two-channel equations remain explicit.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- The compatibility map of the actual normalized inner solution and the
same complete nonlocal source. Its two real components are the quantities
to be controlled by the physical parameter equations. -/
def actualHartreeCanonicalCompatibility
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (R a ell c : ℝ) (z : ℝ → ℂ) (x : InnerCorrections) : ℂ :=
  let J := actualHartreeTransmissionInnerJet ell c z x a R
  actualOriginTransmissionObstruction K R
    (actualHartreeLaplacianScaledKummerSource a ell c z) J.1 J.2

/-- Canonical physical realization, without assumed boundary compatibility:
the actual error has a certified integral equal to the explicit projection,
and cancelling that projection is equivalent to exact left matching by a
right-normalized homogeneous addition that solves the UNCHANGED source.
The existing scale-small error bound and both Fredholm equations are retained. -/
theorem actual_Hartree_canonical_projection_and_exact_matching
    (B A mu theta scale R C : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (K : OriginKummerPair mu theta scale) (hK : OriginBasisOn K R (2*R) C) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (ell c a : ℝ), 0 < ell → ell ≤ 1 → |c| ≤ 1 → 0 < a → 2 < a*R →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ u : ℝ, 0 < u → ‖z u‖ ≤ B) →
        (∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) →
      ∃ (hp : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionPlusSource ell c z))
        (hm : InWeightedL2 (7/4 : ℝ) (actualHartreeTransmissionMinusSource ell c z))
        (x : InnerCorrections),
        ActualHartreeTransmissionInnerSolve ell c z hp hm x ∧
        (let J := actualHartreeTransmissionInnerJet ell c z x a R
         let F := actualHartreeLaplacianScaledKummerSource a ell c z
         let E := actualOriginTransmissionDefect K R F J.1 J.2
         (∀ r ∈ Icc R (2*R), ‖E r‖ ≤ D*ell^(1/16 : ℝ)) ∧
         IntervalIntegrable (originGreenSourceA K E) volume R (2*R) ∧
         (∫ r in R..(2*R), originGreenSourceA K E r) =
           actualHartreeCanonicalCompatibility K R a ell c z x ∧
         ((actualOriginProjectedValue K R F J.1 J.2 R = J.1 ∧
           actualOriginProjectedSlope K R F J.1 J.2 R = J.2) ↔
           actualHartreeCanonicalCompatibility K R a ell c z x = 0) ∧
         (actualOriginProjectedValue K R F J.1 J.2 (2*R) * originPhysicalSlope K.x K.dx (2*R) -
           actualOriginProjectedSlope K R F J.1 J.2 (2*R) * originPhysicalValue K.x (2*R) = 0) ∧
         (∀ᵐ r ∂volume, r ∈ Icc R (2*R) →
           HasDerivAt (actualOriginProjectedValue K R F J.1 J.2)
             (actualOriginProjectedSlope K R F J.1 J.2 r) r ∧
           HasDerivAt (actualOriginProjectedSlope K R F J.1 J.2)
             (F r - frozenFirstCoeff r * actualOriginProjectedSlope K R F J.1 J.2 r -
               frozenZeroCoeff mu theta * actualOriginProjectedValue K R F J.1 J.2 r) r)) := by
  obtain ⟨D,hD,hExisting⟩ := actual_Hartree_canonical_origin_transmission_small_defect
    B A mu theta scale R C hB hA hR hC K hK
  refine ⟨D,hD,?_⟩
  intro ell c a hell hellOne hc ha hAR z hz hSup hStrauss
  obtain ⟨hp,hm,x,hSolve,hCertificate⟩ :=
    hExisting ell c a hell hellOne hc ha hAR z hz hSup hStrauss
  let J := actualHartreeTransmissionInnerJet ell c z x a R
  let F := actualHartreeLaplacianScaledKummerSource a ell c z
  have hR0 : 0 < R := by linarith
  have hFI : IntervalIntegrable F volume R (2*R) :=
    actual_Hartree_scaled_Kummer_source_intervalIntegrable B A ell c a R (2*R)
      hB hA hell hellOne hc ha hR0 (by linarith) z hz hSup hStrauss
  have hProjection := actual_origin_transmission_defect_projection_balance K hR0 hK F hFI J.1 J.2
  have hMatching := actual_origin_projected_matching_iff_zero_obstruction K hR0 hK F J.1 J.2
  have hEquation := actual_origin_projected_transmission_same_equation K hR0 hK F hFI J.1 J.2
  refine ⟨hp,hm,x,hSolve,?_,hProjection.1,hProjection.2.1,hMatching,hEquation.1,hEquation.2.2.2⟩
  exact hCertificate.2.2.2.2.2

end HBL.TypeIIDynamicSelection
