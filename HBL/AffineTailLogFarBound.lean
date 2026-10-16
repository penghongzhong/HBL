import HBL.AffineTailPrimitiveGapFactor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
A quantitative far-field estimate for the logarithmic radial Hartree
kernel. For rho>r>0 the logarithm is nonnegative and is controlled
by 2r/(rho-r); for rho>=2r this improves to 4r/rho.
These estimates will be used to prove absolute integrability at infinity.
-/

noncomputable section

namespace HBL.Modulation.AffineTail

theorem radialLog_far_nonneg_le (r rho : ℝ)
    (hr : 0 < r) (hρ : r < rho) :
    0 ≤ Real.log ((r + rho) / |r - rho|) ∧
      Real.log ((r + rho) / |r - rho|) ≤
        2 * r / (rho - r) := by
  have hpos : 0 < rho - r := by linarith
  have habs : |r - rho| = rho - r := by
    rw [abs_of_neg (by linarith : r - rho < 0)]
    ring
  rw [habs]
  have hge : (1 : ℝ) ≤ (r + rho) / (rho - r) := by
    apply (le_div_iff₀ hpos).2
    linarith
  have hzr : 0 < (r + rho) / (rho - r) :=
    lt_of_lt_of_le zero_lt_one hge
  have hlog := Real.log_le_sub_one_of_pos hzr
  have hdiff :
      (r + rho) / (rho - r) - 1 =
        2 * r / (rho - r) := by
    field_simp [ne_of_gt hpos] <;> ring
  exact ⟨Real.log_nonneg hge, by simpa only [hdiff] using hlog⟩

theorem radialLog_far_inv_bound (r rho : ℝ)
    (hr : 0 < r) (hρ : 2 * r ≤ rho) :
    0 ≤ Real.log ((r + rho) / |r - rho|) ∧
      Real.log ((r + rho) / |r - rho|) ≤
        4 * r / rho := by
  have hrr : r < rho := by linarith
  rcases radialLog_far_nonneg_le r rho hr hrr with ⟨h0, hbound⟩
  have hden : 0 < rho - r := by linarith
  have hpos : 0 < rho := by linarith
  have hbound' : (2 * r) / (rho - r) ≤ (4 * r) / rho := by
    apply (div_le_div_iff₀ hden hpos).2
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hρ)]
  exact ⟨h0, hbound.trans hbound'⟩

end HBL.Modulation.AffineTail
