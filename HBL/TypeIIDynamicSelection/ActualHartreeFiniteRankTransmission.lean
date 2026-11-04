import HBL.TypeIIDynamicSelection.ActualOriginFiniteRankTransmission
import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalProjection

/-!
Same canonical physical Hartree solution -> exact finite-rank transmission.
The interface compatibility is solved by an EXPLICIT source correction,
not by assuming its value zero. Its coefficient and source norm are derived
from the already proved physical residual estimates. Both original inner
Fredholm equations and all physical coordinate factors are retained.

This theorem does not identify the constructed two real source directions
with the actual time-modulation tangents, and does not complete the nonlinear
higher-profile residual. That identification cannot be replaced by the
unit projection proved here. No Type-II rate is assumed or claimed.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel HBL.Profile.Kummer

/-- Actual physical data, an actual normalized inner solve, derived small
compatibility amplitude, and an exactly matched augmented annular inverse.
The corrected source F+beta*S is explicit in the equation. The constants
are chosen BEFORE ell,c,a,z, for the prescribed basis and annulus. -/
theorem actual_Hartree_canonical_finite_rank_transmission
    (B A mu theta scale R C : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (K : OriginKummerPair mu theta scale) (hK : OriginBasisOn K R (2*R) C) :
    ∃ Db Ds : ℝ, 0 ≤ Db ∧ 0 ≤ Ds ∧
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
         let beta := actualHartreeCanonicalCompatibility K R a ell c z x
         let Faug := actualOriginFiniteRankSource K R F J.1 J.2
         ‖beta‖ ≤ Db*ell^(1/16 : ℝ) ∧
         (∀ r ∈ Icc R (2*R), ‖Faug r-F r‖ ≤ Ds*ell^(1/16 : ℝ)) ∧
         IntervalIntegrable Faug volume R (2*R) ∧
         actualOriginProjectedValue K R Faug J.1 J.2 R = J.1 ∧
         actualOriginProjectedSlope K R Faug J.1 J.2 R = J.2 ∧
         (actualOriginProjectedValue K R Faug J.1 J.2 (2*R) * originPhysicalSlope K.x K.dx (2*R) -
           actualOriginProjectedSlope K R Faug J.1 J.2 (2*R) * originPhysicalValue K.x (2*R) = 0) ∧
         ContinuousOn (actualOriginProjectedValue K R Faug J.1 J.2) (Icc R (2*R)) ∧
         ContinuousOn (actualOriginProjectedSlope K R Faug J.1 J.2) (Icc R (2*R)) ∧
         (∀ᵐ r ∂volume, r ∈ Icc R (2*R) →
           HasDerivAt (actualOriginProjectedValue K R Faug J.1 J.2)
             (actualOriginProjectedSlope K R Faug J.1 J.2 r) r ∧
           HasDerivAt (actualOriginProjectedSlope K R Faug J.1 J.2)
             (F r + beta * actualOriginCompatibilitySource K R r -
               frozenFirstCoeff r * actualOriginProjectedSlope K R Faug J.1 J.2 r -
               frozenZeroCoeff mu theta * actualOriginProjectedValue K R Faug J.1 J.2 r) r)) := by
  obtain ⟨D0,hD0,hExisting⟩ := actual_Hartree_canonical_projection_and_exact_matching
    B A mu theta scale R C hB hA hR hC K hK
  obtain ⟨M,hM,hModeBound⟩ := actual_origin_compatibility_source_bounded K hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let Db : ℝ := C^2*D0*R
  let Ds : ℝ := Db*M
  have hDb : 0 ≤ Db := by dsimp [Db]; positivity
  have hDs : 0 ≤ Ds := mul_nonneg hDb hM
  refine ⟨Db,Ds,hDb,hDs,?_⟩
  intro ell c a hell hellOne hc ha hAR z hz hSup hStrauss
  obtain ⟨hp,hm,x,hSolve,hCertificate⟩ :=
    hExisting ell c a hell hellOne hc ha hAR z hz hSup hStrauss
  let J := actualHartreeTransmissionInnerJet ell c z x a R
  let F := actualHartreeLaplacianScaledKummerSource a ell c z
  let E := actualOriginTransmissionDefect K R F J.1 J.2
  let beta := actualHartreeCanonicalCompatibility K R a ell c z x
  let e : ℝ := ell^(1/16 : ℝ)
  have he : 0 ≤ e := Real.rpow_nonneg hell.le _
  have hE : ∀ r ∈ Icc R (2*R), ‖E r‖ ≤ D0*e := hCertificate.1
  have hProjection : originGreenCoeffA K (2*R) E R = beta := hCertificate.2.2.1
  have hBeta : ‖beta‖ ≤ Db*e := by
    have h := (originGreen_coefficients_norm_le K R (2*R) C (D0*e)
      hC (mul_nonneg hD0 he) hK E hE
      (show R ∈ Icc R (2*R) by constructor <;> linarith)).1
    rw [hProjection] at h
    exact h.trans_eq (by dsimp [Db]; ring)
  have hCorrection : ∀ r ∈ Icc R (2*R),
      ‖actualOriginFiniteRankSource K R F J.1 J.2 r-F r‖ ≤ Ds*e := by
    intro r hr
    change ‖F r+beta*actualOriginCompatibilitySource K R r-F r‖ ≤ Ds*e
    rw [add_sub_cancel_left, norm_mul]
    exact (mul_le_mul hBeta (hModeBound r hr) (norm_nonneg _)
      (mul_nonneg hDb he)).trans_eq (by dsimp [Ds]; ring)
  have hFI : IntervalIntegrable F volume R (2*R) :=
    actual_Hartree_scaled_Kummer_source_intervalIntegrable B A ell c a R (2*R)
      hB hA hell hellOne hc ha hR0 (by linarith) z hz hSup hStrauss
  have hExact := actual_origin_finite_rank_exact_transmission K hR0 hK F hFI J.1 J.2
  exact ⟨hp,hm,x,hSolve,hBeta,hCorrection,hExact⟩

end HBL.TypeIIDynamicSelection
