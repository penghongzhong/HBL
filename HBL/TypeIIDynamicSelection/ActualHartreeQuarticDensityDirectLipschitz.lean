import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import Mathlib.Tactic

/-!
# Direct two-point Lipschitz estimate for the actual quartic Hartree density

The original real-linear Taylor density remainder, not a synthetic source,
is quadratic in the correction. Its DIRECT difference is bounded by
the size of BOTH corrections times their difference. No Frechet
parameter derivative or assumed positive new-residual order is used.

This scalar source lemma is the input for a true logarithmic-radial
Riesz Lipschitz bound on the one-orbit two-threshold family.
-/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_Hartree_quartic_density_remainder_direct_Lipschitz
    (u h k : ℂ) (M e d : ℝ)
    (hM : 0 ≤ M) (he : 0 ≤ e) (hd : 0 ≤ d)
    (hu : ‖u‖ ≤ M) (hh : ‖h‖ ≤ e)
    (hk : ‖k‖ ≤ e) (hdelta : ‖h-k‖ ≤ d) :
    |actualHartreeComplexDensityRemainder u h -
      actualHartreeComplexDensityRemainder u k| ≤
      (12*M^2*e + 12*M*e^2 + 4*e^3)*d := by
  let p : ℂ → ℝ := fun z => actualHartreeComplexRealPair u z
  let a : ℝ := 2*p h + ‖h‖^2
  let b : ℝ := 2*p k + ‖k‖^2
  have hU2 : ‖u‖^2 ≤ M^2 :=
    pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hH2 : ‖h‖^2 ≤ e^2 :=
    pow_le_pow_left₀ (norm_nonneg h) hh 2
  have hK2 : ‖k‖^2 ≤ e^2 :=
    pow_le_pow_left₀ (norm_nonneg k) hk 2
  have hPairH : |p h| ≤ M*e := by
    calc
      _ ≤ ‖u‖*‖h‖ :=
        actual_Hartree_complex_real_pair_bound u h
      _ ≤ M*e := mul_le_mul hu hh (norm_nonneg h) hM
  have hPairK : |p k| ≤ M*e := by
    calc
      _ ≤ ‖u‖*‖k‖ :=
        actual_Hartree_complex_real_pair_bound u k
      _ ≤ M*e := mul_le_mul hu hk (norm_nonneg k) hM
  have hPdiff : |p h-p k| ≤ M*d := by
    have hid : p h-p k = actualHartreeComplexRealPair u (h-k) := by
      dsimp [p, actualHartreeComplexRealPair]
      ring
    rw [hid]
    calc
      _ ≤ ‖u‖*‖h-k‖ :=
        actual_Hartree_complex_real_pair_bound u (h-k)
      _ ≤ M*d := mul_le_mul hu hdelta (norm_nonneg (h-k)) hM
  have hSum : ‖h‖+‖k‖ ≤ 2*e := by linarith
  have hNormSqDiff :
      |‖h‖^2-‖k‖^2| ≤ 2*e*d := by
    calc
      _ = (‖h‖+‖k‖)*|‖h‖-‖k‖| := by
        rw [show ‖h‖^2-‖k‖^2 =
          (‖h‖+‖k‖)*(‖h‖-‖k‖) by ring,
          abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg h) (norm_nonneg k))]
      _ ≤ (‖h‖+‖k‖)*‖h-k‖ :=
        mul_le_mul_of_nonneg_left
          (abs_norm_sub_norm_le h k)
          (add_nonneg (norm_nonneg h) (norm_nonneg k))
      _ ≤ (2*e)*d :=
        mul_le_mul hSum hdelta (norm_nonneg _) (by positivity)
      _ = 2*e*d := by ring
  have hAbsA : |a| ≤ 2*M*e+e^2 := by
    change |2*p h+‖h‖^2| ≤ _
    calc
      _ ≤ |2*p h| + |‖h‖^2| := abs_add_le _ _
      _ = 2*|p h|+‖h‖^2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg (sq_nonneg (‖h‖))]
      _ ≤ 2*(M*e)+e^2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hPairH (by norm_num)) hH2
      _ = _ := by ring
  have hAbsB : |b| ≤ 2*M*e+e^2 := by
    change |2*p k+‖k‖^2| ≤ _
    calc
      _ ≤ |2*p k| + |‖k‖^2| := abs_add_le _ _
      _ = 2*|p k|+‖k‖^2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg (sq_nonneg (‖k‖))]
      _ ≤ 2*(M*e)+e^2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hPairK (by norm_num)) hK2
      _ = _ := by ring
  have hSumAB : |a+b| ≤ 4*M*e+2*e^2 := by
    exact (abs_add_le a b).trans (by linarith [hAbsA, hAbsB])
  have hDiffAB : |a-b| ≤ (2*M+2*e)*d := by
    have hi : a-b =
        2*(p h-p k)+(‖h‖^2-‖k‖^2) := by
      dsimp [a,b]
      ring
    rw [hi]
    calc
      _ ≤ |2*(p h-p k)| + |‖h‖^2-‖k‖^2| :=
        abs_add_le _ _
      _ = 2*|p h-p k| + |‖h‖^2-‖k‖^2| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ 2*(M*d)+2*e*d :=
        add_le_add
          (mul_le_mul_of_nonneg_left hPdiff (by norm_num))
          hNormSqDiff
      _ = (2*M+2*e)*d := by ring
  have hSqDiff :
      |a^2-b^2| ≤ ((2*M+2*e)*d)*(4*M*e+2*e^2) := by
    calc
      _ = |a-b| * |a+b| := by
        rw [show a^2-b^2=(a-b)*(a+b) by ring, abs_mul]
      _ ≤ ((2*M+2*e)*d)*(4*M*e+2*e^2) :=
        mul_le_mul hDiffAB hSumAB (abs_nonneg _) (by positivity)
  have hFirst :
      (2*‖u‖^2)*|‖h‖^2-‖k‖^2| ≤
        (2*M^2)*(2*e*d) := by
    have hco : 2*‖u‖^2 ≤ 2*M^2 := by nlinarith [hU2]
    exact mul_le_mul hco hNormSqDiff (abs_nonneg _) (by positivity)
  have hIdentity :
      actualHartreeComplexDensityRemainder u h -
        actualHartreeComplexDensityRemainder u k =
      (2*‖u‖^2)*(‖h‖^2-‖k‖^2) + (a^2-b^2) := by
    dsimp [actualHartreeComplexDensityRemainder,a,b,p]
    ring
  calc
    _ = |(2*‖u‖^2)*(‖h‖^2-‖k‖^2)+(a^2-b^2)| :=
      congrArg abs hIdentity
    _ ≤ |(2*‖u‖^2)*(‖h‖^2-‖k‖^2)| + |a^2-b^2| :=
      abs_add_le _ _
    _ = (2*‖u‖^2)*|‖h‖^2-‖k‖^2| + |a^2-b^2| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*‖u‖^2)]
    _ ≤ (2*M^2)*(2*e*d)+
          ((2*M+2*e)*d)*(4*M*e+2*e^2) :=
      add_le_add hFirst hSqDiff
    _ = (12*M^2*e+12*M*e^2+4*e^3)*d := by ring

end HBL.TypeIIDynamicSelection
