import HBL.KummerOriginBasis.CompactBasis
import Mathlib.Tactic

/-!
# Genuine origin-normalized Green integrands

The coefficients here are the actual manuscript singular/regular Kummer
basis, and the exact physical Wronskian. No global fundamental pair and no
abstract right inverse are assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.Profile.Kummer

def originAnnulusWronskian {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (r : ℝ) : ℂ :=
  originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
    originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r

def originAnnulusSourceA {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalValue K.x r * F r / originAnnulusWronskian K r

def originAnnulusSourceB {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  originPhysicalValue K.y r * F r / originAnnulusWronskian K r

theorem originAnnulus_source_norm_le {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (a b C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ) {r : ℝ} (hr : r ∈ Icc a b) (hF : ‖F r‖ ≤ M) :
    ‖originAnnulusSourceA K F r‖ ≤ C ^ 2 * M ∧
    ‖originAnnulusSourceB K F r‖ ≤ C ^ 2 * M := by
  obtain ⟨_, _, _, _, _, _, hphi, _, hpsi, _, hWinv⟩ := hK r hr
  have hbound (p : ℂ) (hp : ‖p‖ ≤ C) :
      ‖p * F r / originAnnulusWronskian K r‖ ≤ C ^ 2 * M := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      _ ≤ C * M * C :=
        mul_le_mul (mul_le_mul hp hF (norm_nonneg _) hC)
          hWinv (by positivity) (mul_nonneg hC hM)
      _ = _ := by ring
  exact ⟨hbound _ hpsi, hbound _ hphi⟩

end HBL.Profile.Kummer
