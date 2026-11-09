import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralUnweightedDerivative
import Mathlib.Tactic

/-!
# True finite radial Hdot1 energy of the original matched spectral correction

The actual first spectral forcing is q=d*u₀, with u₀ the same
Cramer-matched source profile. The strictly verified uniform derivative
estimate is integrated against the original 3D radial measure r² dr.
The derivative is the *actual* classical derivative of the Green field;
the density is genuinely integrable, so the resulting energy estimate
does not exploit a vacuous nonintegrable integral.

The annular estimate is independent of inverse powers of the moving
left endpoint. Its physical coordinate rescaling still carries the
genuine, non-negligible outer scale factor and is NOT asserted here.
No time decay, matched four-region PDE gain, or blowup rate is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- An actual (non-vacuous) 3D radial gradient-energy bound for the first
spectral correction to the original Cramer-matched Hartree Green profile.
The source q=d*u₀ is not replaced by an independent forcing envelope. -/
theorem actual_Hartree_original_matched_spectral_radial_H1_energy_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b D G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ)
    (hF : ∀ x ∈ Ioo 0 scale, ContinuousAt F x)
    (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H) :
    let q := actualHartreeMatchedSpectralFirstSource K a b F U DU d
    let w₁ := actualOriginMatchedKummerValue K a b q 0 0
    let E : ℝ :=
      (b + 1) * G * (1 + (D + 1) * G * b ^ 2) * (‖d‖ * H) +
      2 * (D + 1) * G ^ 2 * (‖d‖ * H) * b ^ 2
    IntegrableOn (fun r : ℝ => r ^ 2 * ‖deriv w₁ r‖ ^ 2)
      (Icc a b) volume ∧
    (∫ r in Icc a b, r ^ 2 * ‖deriv w₁ r‖ ^ 2) ≤
      (b - a) * b ^ 2 * E ^ 2 := by
  let u : ℝ → ℂ := actualOriginMatchedKummerValue K a b F U DU
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let w₁ : ℝ → ℂ := actualOriginMatchedKummerValue K a b q 0 0
  let E : ℝ :=
    (b + 1) * G * (1 + (D + 1) * G * b ^ 2) * (‖d‖ * H) +
    2 * (D + 1) * G ^ 2 * (‖d‖ * H) * b ^ 2
  let g : ℝ → ℝ := fun r => r ^ 2 * ‖deriv w₁ r‖ ^ 2
  change IntegrableOn g (Icc a b) volume ∧
    (∫ r in Icc a b, g r) ≤ (b - a) * b ^ 2 * E ^ 2
  have hb0 : 0 ≤ b := (ha.trans_le hab).le
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hU :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb F hF U DU
  have hQcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt q x := by
    intro x hx
    change ContinuousAt (fun y : ℝ => d * u y) x
    exact continuousAt_const.mul ((hU x hx).1.continuousAt)
  have hClass :=
    actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb q hQcont 0 0
  have hDerivCont : ContinuousOn (deriv w₁) (Icc a b) := by
    intro r hr
    have hrPos : r ∈ Ioo (0 : ℝ) scale :=
      ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
    exact ((hClass r hrPos).2.1.continuousAt).continuousWithinAt
  have hGCont : ContinuousOn g (Icc a b) := by
    dsimp [g]
    exact ((continuous_id.pow 2).continuousOn).mul ((hDerivCont.norm).pow 2)
  have hGIntegrable : IntegrableOn g (Icc a b) volume :=
    hGCont.integrableOn_Icc
  have hFirst (r : ℝ) (hr : r ∈ Icc a b) :
      ‖deriv w₁ r‖ ≤ E := by
    simpa only [E, w₁, q] using
      (actual_Hartree_original_matched_spectral_unweighted_C1_no_left_radius
        K a b D G H ha hab hb hD hG hH hcoeff hbound
        F hF U DU d hProfile r hr)
  have hPoint (r : ℝ) (hr : r ∈ Icc a b) :
      g r ≤ b ^ 2 * E ^ 2 := by
    have hr0 : 0 ≤ r := (ha.trans_le hr.1).le
    have hR : r ^ 2 ≤ b ^ 2 :=
      pow_le_pow_left₀ hr0 hr.2 2
    have hS : ‖deriv w₁ r‖ ^ 2 ≤ E ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hFirst r hr) 2
    dsimp [g]
    exact mul_le_mul hR hS (sq_nonneg _) (sq_nonneg _)
  have hFinite : (volume : Measure ℝ) (Icc a b) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hAE : ∀ᵐ r : ℝ ∂volume, r ∈ Icc a b →
      ‖g r‖ ≤ b ^ 2 * E ^ 2 :=
    Filter.Eventually.of_forall (by
      intro r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
      exact hPoint r hr)
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc a b) (f := g) (C := b ^ 2 * E ^ 2)
    hFinite hAE
  have hIntegral :
      ‖∫ r in Icc a b, g r‖ ≤ (b ^ 2 * E ^ 2) * (b - a) := by
    simpa only [Real.volume_real_Icc_of_le hab] using hNorm
  refine ⟨hGIntegrable, ?_⟩
  calc
    (∫ r in Icc a b, g r) ≤ ‖∫ r in Icc a b, g r‖ :=
      (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ (b ^ 2 * E ^ 2) * (b - a) := hIntegral
    _ = (b - a) * b ^ 2 * E ^ 2 := by ring

end HBL.TypeIIDynamicSelection
