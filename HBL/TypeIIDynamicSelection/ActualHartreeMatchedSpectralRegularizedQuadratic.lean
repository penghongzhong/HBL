import HBL.TypeIIDynamicSelection.ActualHartreeZeroLeftRegularizedVolterra
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSpectralLeftC1Exact
import Mathlib.Tactic

/-!
# The true zero-left matched spectral response: weighted quadratic error

The matched spectral correction is not the isolated Green field. Its source
is q=d*u, where u is the same original Cramer-matched Kummer profile.
The zero-left value and derivative eliminate an arbitrary homogeneous mode.
The original normalized Wronskian and bounded regularized Kummer IVP pair
then give a uniform r-weighted response with NO factor a⁻¹ or a⁻².

The weighted premise controls the FIRST matched profile, not an unrelated
source or a free speed. It must ultimately be produced by the original
nonlinear physical Hartree orbit before the full §2.13 can be accepted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The first spectral source of the genuine matched field belongs to
the inverse-linear source class whenever that same field is r-weighted. -/
theorem actual_Hartree_matched_spectral_first_source_inverse_linear
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b H : ℝ) (ha : 0 < a) (hH : 0 ≤ H)
    (F : ℝ → ℂ) (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H)
    (x : ℝ) (hx : x ∈ Icc a b) :
    ‖actualHartreeMatchedSpectralFirstSource K a b F U DU d x‖ ≤
      (‖d‖ * H) / x := by
  have hxpos : 0 < x := ha.trans_le hx.1
  have hnormx : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
  have hu : x * ‖actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H := by
    simpa only [norm_mul, hnormx] using hProfile x hx
  have hu' : ‖actualOriginMatchedKummerValue K a b F U DU x‖ * x ≤ H := by
    simpa only [mul_comm] using hu
  change ‖d * actualOriginMatchedKummerValue K a b F U DU x‖ ≤
    (‖d‖ * H) / x
  rw [norm_mul]
  apply (le_div_iff₀ hxpos).2
  calc
    ‖d‖ * ‖actualOriginMatchedKummerValue K a b F U DU x‖ * x =
        ‖d‖ * (‖actualOriginMatchedKummerValue K a b F U DU x‖ * x) := by
          ring
    _ ≤ ‖d‖ * H :=
      mul_le_mul_of_nonneg_left hu' (norm_nonneg d)

/-- The exact Cramer zero-left-jet spectral correction, without an
unweighted singular-basis constant or inverse moving matching radius. -/
theorem actual_Hartree_matched_spectral_zero_left_uniform_weighted
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
        ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖(r : ℂ) * actualOriginMatchedKummerValue K a b
      (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r‖ ≤
        2 * G ^ 2 * (b - a) * (‖d‖ * H) := by
  let q : ℝ → ℂ := actualHartreeMatchedSpectralFirstSource K a b F U DU d
  let M : ℝ := ‖d‖ * H
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) hH
  have hq : ∀ x ∈ Icc a b, ‖q x‖ ≤ M / x := by
    intro x hx
    exact actual_Hartree_matched_spectral_first_source_inverse_linear
      K a b H ha hH F U DU d hProfile x hx
  exact actual_Hartree_zero_left_Kummer_regularized_Volterra_value_bound
    K a b C G M ha hab hb hG hM hK hbound q hq r hr

/-- The first matched spectral PDE error is quadratic in d in the
regularized weighted norm, provided the genuine first profile has that
weighted norm. No physical time gain is claimed here. -/
theorem actual_Hartree_matched_spectral_quadratic_defect_weighted
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hK : OriginBasisOn K a b C)
    (hbound : ∀ x ∈ Icc 0 scale,
        ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (U DU d : ℂ)
    (hProfile : ∀ x ∈ Icc a b,
      ‖(x : ℂ) * actualOriginMatchedKummerValue K a b F U DU x‖ ≤ H)
    (r : ℝ) (hr : r ∈ Icc a b) :
    ‖d * actualOriginMatchedKummerValue K a b
      (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r‖ ≤
      (2 * G ^ 2 * (b - a)) * (‖d‖ ^ 2 * H) / r := by
  have hrpos : 0 < r := ha.trans_le hr.1
  have hnormr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hW := actual_Hartree_matched_spectral_zero_left_uniform_weighted
      K a b C G H ha hab hb hG hH hK hbound F U DU d hProfile r hr
  apply (le_div_iff₀ hrpos).2
  calc
    ‖d * actualOriginMatchedKummerValue K a b
        (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r‖ * r =
        ‖d‖ * ‖(r : ℂ) * actualOriginMatchedKummerValue K a b
          (actualHartreeMatchedSpectralFirstSource K a b F U DU d) 0 0 r‖ := by
            rw [norm_mul, norm_mul, hnormr]
            ring
    _ ≤ ‖d‖ * (2 * G ^ 2 * (b - a) * (‖d‖ * H)) :=
      mul_le_mul_of_nonneg_left hW (norm_nonneg _)
    _ = (2 * G ^ 2 * (b - a)) * (‖d‖ ^ 2 * H) := by ring

end HBL.TypeIIDynamicSelection
