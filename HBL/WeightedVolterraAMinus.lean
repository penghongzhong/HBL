import HBL.WeightedVolterraProfileCoercivity
import HBL.WeightedVolterraSineModes

/-!
The real phase-channel form A₋ = I - 3 V* V for the concrete weighted
Volterra operator.  The actual radial profile integral and quantitative
phase-channel gap are proved without requiring completeness of the
transferred input modes.  This is the reduced energy realization, not yet
the three-dimensional physical Hessian identification or full theorem 3.1.
-/

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel HBL.Modulation.AffineTail

/-- Real phase-channel representative on the existing Hilbert energy space. -/
def weightedVolterraAMinus :
    RealL2 halfLineMeasure →L[ℝ] RealL2 halfLineMeasure :=
  ContinuousLinearMap.id ℝ (RealL2 halfLineMeasure) -
    (3 : ℝ) • (ContinuousLinearMap.adjoint weightedVolterraOperator ∘L
      weightedVolterraOperator)

/-- The genuine phase-channel operator is symmetric on the real Hilbert space. -/
theorem weightedVolterraAMinus_selfAdjoint :
    IsSelfAdjoint weightedVolterraAMinus := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (x - (3 : ℝ) •
      ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedVolterraOperator x)) y =
    inner ℝ x (y - (3 : ℝ) •
      ContinuousLinearMap.adjoint weightedVolterraOperator
        (weightedVolterraOperator y))
  rw [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- Actual singular modes diagonalize the phase channel, with no added
completeness hypothesis. -/
theorem weightedVolterraAMinus_sineMode (n : ℕ) :
    weightedVolterraAMinus (weightedVolterraSineMode n) =
      (1 - 3 / (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)) •
        weightedVolterraSineMode n := by
  change weightedVolterraSineMode n -
    (3 : ℝ) • (ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedVolterraOperator (weightedVolterraSineMode n))) = _
  rw [weightedVolterraGram_sineMode]
  module

/-- The first transferred Volterra mode is an exact phase zero mode. -/
theorem weightedVolterraAMinus_zero_sineMode :
    weightedVolterraAMinus (weightedVolterraSineMode 0) = 0 := by
  rw [weightedVolterraAMinus_sineMode]
  norm_num

/-- The second transferred mode has phase energy multiplier exactly 4/5. -/
theorem weightedVolterraAMinus_second_sineMode :
    weightedVolterraAMinus (weightedVolterraSineMode 1) =
      (4 / 5 : ℝ) • weightedVolterraSineMode 1 := by
  rw [weightedVolterraAMinus_sineMode]
  norm_num

/-- The quadratic form is the squared energy minus three times the
actual weighted Volterra output norm. -/
theorem weightedVolterraAMinus_quadratic (x : RealL2 halfLineMeasure) :
    inner ℝ (weightedVolterraAMinus x) x =
      ‖x‖ ^ 2 - 3 * ‖weightedVolterraOperator x‖ ^ 2 := by
  change inner ℝ (x - (3 : ℝ) •
    (ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedVolterraOperator x))) x = _
  rw [inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

/-- The actual phase-channel form on classical full-energy profiles is
the derivative-coordinate pairing minus the genuine local W⁴ potential.
The three-dimensional angular factor has not been inserted here. -/
theorem weightedVolterraAMinus_radial_profile_pairing
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hgmem : MemLp (deriv (radialU g)) 2 halfLineMeasure) :
    inner ℝ (weightedVolterraAMinus (smoothToRadialDotH1 f hfmem))
      (smoothToRadialDotH1 g hgmem) =
      (∫ r : ℝ, deriv (radialU f) r * deriv (radialU g) r
        ∂halfLineMeasure) -
      3 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU f r * radialU g r
        ∂halfLineMeasure) := by
  change inner ℝ (smoothToRadialDotH1 f hfmem -
    (3 : ℝ) • (ContinuousLinearMap.adjoint weightedVolterraOperator
      (weightedVolterraOperator (smoothToRadialDotH1 f hfmem))))
    (smoothToRadialDotH1 g hgmem) = _
  rw [inner_sub_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left,
    smoothRadialEnergy_coordinate_pairing f g hfmem hgmem,
    weightedVolterraOperator_smoothToRadialDotH1_eq f hf hfmem,
    weightedVolterraOperator_smoothToRadialDotH1_eq g hg hgmem,
    weightedProfile_inner (radialU f) (radialU g)
      (weightedRadialU_memLp f hf hfmem)
      (weightedRadialU_memLp g hg hgmem)]

/-- Exact spectral sum for the genuine Volterra output norm.
Output completeness has already been proved from the Green operator. -/
theorem weightedVolterraGram_hasSum (x : RealL2 halfLineMeasure) :
    HasSum (fun n : ℕ => (weightedVolterraSineScale n)⁻¹ ^ 2 *
      (inner ℝ (weightedVolterraSineMode n) x) ^ 2)
      (inner ℝ (weightedVolterraOperator x) (weightedVolterraOperator x)) := by
  convert weightedHartreeSineHilbertBasis.hasSum_inner_mul_inner
    (weightedVolterraOperator x) (weightedVolterraOperator x) using 1
  funext n
  simp only [weightedHartreeSineHilbertBasis_apply]
  have hcoeff :
      inner ℝ (weightedVolterraOperator x)
          (weightedHartreeOrthonormalSineMode n) =
        (weightedVolterraSineScale n)⁻¹ *
          inner ℝ (weightedVolterraSineMode n) x := by
    rw [real_inner_comm]
    exact weightedVolterraSineMode_inner n x
  simp only [hcoeff, weightedVolterraSineMode_inner]
  ring

/-- Outside the true phase zero mode, the squared Volterra norm is bounded
by 1/15 of the input energy, using Bessel rather than an assumed basis. -/
theorem weightedVolterraGram_tail_le (x : RealL2 halfLineMeasure)
    (hzero : inner ℝ (weightedVolterraSineMode 0) x = 0) :
    ‖weightedVolterraOperator x‖ ^ 2 ≤ (1 / 15 : ℝ) * ‖x‖ ^ 2 := by
  obtain ⟨hsummable, hbessel⟩ := weightedVolterraSineMode_bessel x
  have hcoeff (n : ℕ) (hn : 1 ≤ n) :
      (weightedVolterraSineScale n)⁻¹ ^ 2 ≤ (1 / 15 : ℝ) := by
    have hnr : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hn
    have hprod : (0 : ℝ) ≤
        (((n + 1 : ℕ) : ℝ) - 2) * (((n + 1 : ℕ) : ℝ) + 2) :=
      mul_nonneg (by linarith) (by linarith)
    have hden : (15 : ℝ) ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by
      nlinarith
    have hsq : weightedVolterraSineScale n ^ 2 =
        4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by
      unfold weightedVolterraSineScale
      exact Real.sq_sqrt (by linarith)
    calc
      (weightedVolterraSineScale n)⁻¹ ^ 2 =
          1 / (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1) := by
            rw [inv_pow, hsq]
            ring
      _ ≤ (1 / 15 : ℝ) := by
            apply (div_le_iff₀ (by linarith :
              (0 : ℝ) < 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)).2
            nlinarith
  have hspectral :
      inner ℝ (weightedVolterraOperator x) (weightedVolterraOperator x) ≤
        (1 / 15 : ℝ) *
          (∑' n : ℕ, (inner ℝ (weightedVolterraSineMode n) x) ^ 2) := by
    refine hasSum_le ?_ (weightedVolterraGram_hasSum x)
      (hsummable.hasSum.mul_left (1 / 15 : ℝ))
    intro n
    by_cases hn0 : n = 0
    · subst n
      rw [hzero]
      norm_num
    have hn : 1 ≤ n := by omega
    exact mul_le_mul_of_nonneg_right (hcoeff n hn) (sq_nonneg _)
  rw [real_inner_self_eq_norm_sq] at hspectral
  exact hspectral.trans
    (mul_le_mul_of_nonneg_left hbessel (by norm_num :
      (0 : ℝ) ≤ 1 / 15))

/-- A sharp 4/5 phase gap for the genuine half-line operator on the
orthogonal complement of its single exact phase zero mode. -/
theorem weightedVolterraAMinus_tail_coercive (x : RealL2 halfLineMeasure)
    (hzero : inner ℝ (weightedVolterraSineMode 0) x = 0) :
    (4 / 5 : ℝ) * ‖x‖ ^ 2 ≤ inner ℝ (weightedVolterraAMinus x) x := by
  have hnorm := weightedVolterraGram_tail_le x hzero
  rw [weightedVolterraAMinus_quadratic]
  nlinarith

/-- Direct phase-channel gap in the actual radial-profile local potential
integral, without imposing ordinary L² membership of r f. -/
theorem weightedVolterraAMinus_radial_profile_coercive
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfmem : MemLp (deriv (radialU f)) 2 halfLineMeasure)
    (hzero : inner ℝ (weightedVolterraSineMode 0)
      (smoothToRadialDotH1 f hfmem) = 0) :
    (4 / 5 : ℝ) *
      (∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) ≤
      (∫ r : ℝ, (deriv (radialU f) r) ^ 2 ∂halfLineMeasure) -
      3 * (∫ r : ℝ, weightedGreenDecay r ^ 2 * radialU f r * radialU f r
        ∂halfLineMeasure) := by
  have hgap := weightedVolterraAMinus_tail_coercive
    (smoothToRadialDotH1 f hfmem) hzero
  rw [weightedVolterraAMinus_radial_profile_pairing f f hf hf hfmem hfmem,
    smoothRadialEnergy_coordinate_norm_sq f hfmem] at hgap
  simpa only [pow_two] using hgap

end HBL.Modulation.Monopole
