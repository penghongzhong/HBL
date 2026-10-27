import HBL.FiniteProfile
import HBL.PhysicalVectorGradient
import HBL.MonopoleGlobalEnergy
import Mathlib.Tactic

/-!
# Three-region energy ledger and global radial H1 matching

This file targets the existing manuscript environment
`prop:global-H1-profile-v3`; it introduces no new numbered R-environment.

The finite profile recursion is already certified in `FiniteProfile.lean`.
After the standard finite Kummer large-argument extraction of the zero
physical-time algebraic branch, only three decaying regional pieces remain.
The local estimates on those pieces are precisely the explicit estimates
displayed in the manuscript.  The work below verifies the nontrivial global
bookkeeping: the three cutoff exponents can be chosen simultaneously with a
uniform positive energy margin, the regional bounds sum to a global radial
energy estimate, the perturbative error adds with its stated power, and the
radial energy coordinate has the already verified physical three-dimensional
gradient norm.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.Profile.GlobalH1

open HBL.Profile.FiniteProfile
open HBL.Modulation.Monopole

/-- Exact three-region decomposition after the finite terminal algebraic
Kummer branch has been removed.  This is only a bookkeeping package: it
contains no norm bound or decay conclusion. -/
structure ThreeRegionEnergyData (E : Type*) [NormedAddCommGroup E] where
  profile : E
  inner : E
  kummer : E
  remote : E
  split : profile = inner + kummer + remote

/-- Positive baseline energy orders admit simultaneously positive cutoff
exponents and one common positive margin.  This is the precise finite-list
"choose the regional powers sufficiently small" step used in the paper. -/
theorem choose_three_region_scales
    (bIn bK bRem gIn gK gRem : ℝ)
    (hbIn : 0 < bIn) (hbK : 0 < bK) (hbRem : 0 < bRem) :
    ∃ rhoIn rhoK rhoRem nuE : ℝ,
      0 < rhoIn ∧ 0 < rhoK ∧ 0 < rhoRem ∧ 0 < nuE ∧
      nuE ≤ bIn - gIn * rhoIn ∧
      nuE ≤ bK - gK * rhoK ∧
      nuE ≤ bRem - gRem * rhoRem := by
  obtain ⟨rhoIn, hrhoIn, hIn⟩ := exists_pos_mul_lt hbIn gIn
  obtain ⟨rhoK, hrhoK, hK⟩ := exists_pos_mul_lt hbK gK
  obtain ⟨rhoRem, hrhoRem, hRem⟩ := exists_pos_mul_lt hbRem gRem
  let mIn := bIn - gIn * rhoIn
  let mK := bK - gK * rhoK
  let mRem := bRem - gRem * rhoRem
  let m := min mIn (min mK mRem)
  have hmIn : 0 < mIn := by
    dsimp [mIn]
    linarith
  have hmK : 0 < mK := by
    dsimp [mK]
    linarith
  have hmRem : 0 < mRem := by
    dsimp [mRem]
    linarith
  have hm : 0 < m := by
    dsimp [m]
    simpa only [lt_min_iff] using And.intro hmIn (And.intro hmK hmRem)
  refine ⟨rhoIn, rhoK, rhoRem, m / 2,
    hrhoIn, hrhoK, hrhoRem, by linarith, ?_, ?_, ?_⟩
  · have hle : m ≤ mIn := by
      dsimp [m]
      exact min_le_left _ _
    dsimp [mIn]
    linarith
  · have hle : m ≤ mK := by
      dsimp [m]
      exact (min_le_right _ _).trans (min_le_left _ _)
    dsimp [mK]
    linarith
  · have hle : m ≤ mRem := by
      dsimp [m]
      exact (min_le_right _ _).trans (min_le_right _ _)
    dsimp [mRem]
    linarith

/-- Three local radial-energy estimates with exponents above one common
positive margin give the global radial-energy estimate. -/
theorem three_region_energy_bound
    {E : Type*} [NormedAddCommGroup E]
    (D : ThreeRegionEnergyData E)
    (s nuE mIn mK mRem CIn CK CRem : ℝ)
    (hs : 1 ≤ s)
    (hnuIn : nuE ≤ mIn) (hnuK : nuE ≤ mK) (hnuRem : nuE ≤ mRem)
    (hCIn : 0 ≤ CIn) (hCK : 0 ≤ CK) (hCRem : 0 ≤ CRem)
    (hIn : ‖D.inner‖ ≤ CIn * s ^ (-mIn))
    (hK : ‖D.kummer‖ ≤ CK * s ^ (-mK))
    (hRem : ‖D.remote‖ ≤ CRem * s ^ (-mRem)) :
    ‖D.profile‖ ≤ (CIn + CK + CRem) * s ^ (-nuE) := by
  have hpIn : s ^ (-mIn) ≤ s ^ (-nuE) :=
    Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg hnuIn)
  have hpK : s ^ (-mK) ≤ s ^ (-nuE) :=
    Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg hnuK)
  have hpRem : s ^ (-mRem) ≤ s ^ (-nuE) :=
    Real.rpow_le_rpow_of_exponent_le hs (neg_le_neg hnuRem)
  have hIn' : ‖D.inner‖ ≤ CIn * s ^ (-nuE) :=
    hIn.trans (mul_le_mul_of_nonneg_left hpIn hCIn)
  have hK' : ‖D.kummer‖ ≤ CK * s ^ (-nuE) :=
    hK.trans (mul_le_mul_of_nonneg_left hpK hCK)
  have hRem' : ‖D.remote‖ ≤ CRem * s ^ (-nuE) :=
    hRem.trans (mul_le_mul_of_nonneg_left hpRem hCRem)
  calc
    ‖D.profile‖ = ‖D.inner + D.kummer + D.remote‖ := by rw [D.split]
    _ ≤ ‖D.inner + D.kummer‖ + ‖D.remote‖ := norm_add_le _ _
    _ ≤ (‖D.inner‖ + ‖D.kummer‖) + ‖D.remote‖ := by
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ (CIn * s ^ (-nuE) + CK * s ^ (-nuE)) +
          CRem * s ^ (-nuE) := by
      exact add_le_add (add_le_add hIn' hK') hRem'
    _ = (CIn + CK + CRem) * s ^ (-nuE) := by ring

/-- Adding the shooting/remainder correction preserves the exact two-term
bound appearing in the manuscript. -/
theorem three_region_with_error_bound
    {E : Type*} [NormedAddCommGroup E]
    (D : ThreeRegionEnergyData E) (err : E)
    (s nuE mIn mK mRem M CIn CK CRem CErr : ℝ)
    (hs : 1 ≤ s)
    (hnuIn : nuE ≤ mIn) (hnuK : nuE ≤ mK) (hnuRem : nuE ≤ mRem)
    (hCIn : 0 ≤ CIn) (hCK : 0 ≤ CK) (hCRem : 0 ≤ CRem)
    (hIn : ‖D.inner‖ ≤ CIn * s ^ (-mIn))
    (hK : ‖D.kummer‖ ≤ CK * s ^ (-mK))
    (hRem : ‖D.remote‖ ≤ CRem * s ^ (-mRem))
    (hErr : ‖err‖ ≤ CErr * s ^ (-M)) :
    ‖D.profile + err‖ ≤
      (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) := by
  calc
    ‖D.profile + err‖ ≤ ‖D.profile‖ + ‖err‖ := norm_add_le _ _
    _ ≤ (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) :=
      add_le_add
        (three_region_energy_bound D s nuE mIn mK mRem CIn CK CRem
          hs hnuIn hnuK hnuRem hCIn hCK hCRem hIn hK hRem)
        hErr

/-- The already constructed physical three-dimensional weak gradient has
exactly the radial energy norm required by the manuscript. -/
theorem physical_gradient_energy_of_radial_coordinate
    (q : FullRadialEnergyL2) :
    ‖physicalGradientRealization (physicalEnergyEquiv.symm q)‖ ^ 2 =
      (4 * Real.pi) * ‖q‖ ^ 2 := by
  exact physicalVectorGradient_certified.2.2.2.1 q

/-- Structural terminal matching the manuscript's global H1 ledger after the
standard finite Kummer terminal-algebraic extraction.  No global decay bound
is assumed: it is assembled from the three local regional estimates. -/
theorem globalH1Matching_certified
    (D : ThreeRegionEnergyData FullRadialEnergyL2)
    (err : FullRadialEnergyL2)
    (bIn bK bRem gIn gK gRem : ℝ)
    (hbIn : 0 < bIn) (hbK : 0 < bK) (hbRem : 0 < bRem)
    (s rhoIn rhoK rhoRem nuE M CIn CK CRem CErr : ℝ)
    (hs : 1 ≤ s)
    (hnu : 0 < nuE)
    (hnuIn : nuE ≤ bIn - gIn * rhoIn)
    (hnuK : nuE ≤ bK - gK * rhoK)
    (hnuRem : nuE ≤ bRem - gRem * rhoRem)
    (hCIn : 0 ≤ CIn) (hCK : 0 ≤ CK) (hCRem : 0 ≤ CRem)
    (hIn : ‖D.inner‖ ≤ CIn * s ^ (-(bIn - gIn * rhoIn)))
    (hK : ‖D.kummer‖ ≤ CK * s ^ (-(bK - gK * rhoK)))
    (hRem : ‖D.remote‖ ≤ CRem * s ^ (-(bRem - gRem * rhoRem)))
    (hErr : ‖err‖ ≤ CErr * s ^ (-M)) :
    (∃ rIn rK rRem nu : ℝ,
      0 < rIn ∧ 0 < rK ∧ 0 < rRem ∧ 0 < nu ∧
      nu ≤ bIn - gIn * rIn ∧
      nu ≤ bK - gK * rK ∧
      nu ≤ bRem - gRem * rRem) ∧
    0 < nuE ∧
    ‖D.profile + err‖ ≤
      (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) ∧
    ‖physicalGradientRealization (physicalEnergyEquiv.symm D.profile)‖ ^ 2 =
      (4 * Real.pi) * ‖D.profile‖ ^ 2 ∧
    Tendsto monopoleMovingCutoffGradientSeminorm (𝓝 (0 : ℝ)) (𝓝 0) := by
  refine ⟨choose_three_region_scales bIn bK bRem gIn gK gRem hbIn hbK hbRem,
    hnu, ?_, physical_gradient_energy_of_radial_coordinate D.profile,
    monopoleMovingCutoffGradientSeminorm_tendsto_zero⟩
  exact three_region_with_error_bound D err s nuE
    (bIn - gIn * rhoIn) (bK - gK * rhoK) (bRem - gRem * rhoRem)
    M CIn CK CRem CErr hs hnuIn hnuK hnuRem hCIn hCK hCRem
    hIn hK hRem hErr

#print axioms choose_three_region_scales
#print axioms three_region_energy_bound
#print axioms three_region_with_error_bound
#print axioms physical_gradient_energy_of_radial_coordinate
#print axioms globalH1Matching_certified

end HBL.Profile.GlobalH1
