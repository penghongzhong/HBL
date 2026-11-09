import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import Mathlib.Tactic

/-!
# Original Hartree local cubic quadratic Taylor remainder: direct Lipschitz

Unlike universal Lipschitz for |u|^2u, this controls the difference
of the SECOND-ORDER cubic Taylor remainders, with a coefficient
vanishing as the correction radius e tends to zero:
  ||C_R(u,h)-C_R(u,k)|| <= (6 M e + 3 e^2) d.
This genuine original cubic factor and the true quartic-density
Riesz difference are the two halves of the complete nonlocal
two-threshold parameter-Lipschitz theorem.
-/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace HBL.TypeIIDynamicSelection

theorem actual_Hartree_original_cubic_Taylor_remainder_direct_Lipschitz
    (u h k : ℂ) (M e d : ℝ)
    (hM : 0 ≤ M) (he : 0 ≤ e) (hd : 0 ≤ d)
    (hu : ‖u‖ ≤ M) (hh : ‖h‖ ≤ e)
    (hk : ‖k‖ ≤ e) (hdelta : ‖h-k‖ ≤ d) :
    ‖actualHartreeComplexCubicRemainder u h -
      actualHartreeComplexCubicRemainder u k‖ ≤
      (6*M*e+3*e^2)*d := by
  let p : ℂ → ℝ := fun z => actualHartreeComplexRealPair u z
  let q : ℝ := ‖h‖^2-‖k‖^2
  let A : ℂ := (2*p h : ℝ)* (h-k)
  let B : ℂ := (2*(p h-p k) : ℝ)* k
  let C : ℂ := (q : ℂ)*u
  let D : ℂ := (‖h‖^2 : ℝ)* (h-k)
  let E : ℂ := (q : ℂ)*k
  have hPair : |p h| ≤ M*e := by
    calc
      _ ≤ ‖u‖*‖h‖ :=
        actual_Hartree_complex_real_pair_bound u h
      _ ≤ M*e := mul_le_mul hu hh (norm_nonneg h) hM
  have hPairDiff : |p h-p k| ≤ M*d := by
    have hid : p h-p k = actualHartreeComplexRealPair u (h-k) := by
      dsimp [p, actualHartreeComplexRealPair]
      ring
    rw [hid]
    calc
      _ ≤ ‖u‖*‖h-k‖ :=
        actual_Hartree_complex_real_pair_bound u (h-k)
      _ ≤ M*d :=
        mul_le_mul hu hdelta (norm_nonneg _) hM
  have hSum : ‖h‖+‖k‖ ≤ 2*e := by linarith
  have hDiffSq : |q| ≤ 2*e*d := by
    dsimp [q]
    calc
      |‖h‖^2-‖k‖^2| =
          (‖h‖+‖k‖)*|‖h‖-‖k‖| := by
        rw [show ‖h‖^2-‖k‖^2 =
          (‖h‖+‖k‖)*(‖h‖-‖k‖) by ring,
          abs_mul,abs_of_nonneg
            (add_nonneg (norm_nonneg h) (norm_nonneg k))]
      _ ≤ (‖h‖+‖k‖)*‖h-k‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le h k)
          (add_nonneg (norm_nonneg h) (norm_nonneg k))
      _ ≤ (2*e)*d :=
        mul_le_mul hSum hdelta (norm_nonneg _) (by positivity)
      _ = 2*e*d := by ring
  have hDecomp :
      actualHartreeComplexCubicRemainder u h -
          actualHartreeComplexCubicRemainder u k =
        A+(B+(C+(D+E))) := by
    dsimp [A,B,C,D,E,q,p,actualHartreeComplexCubicRemainder]
    push_cast
    ring
  have hA : ‖A‖ ≤ 2*M*e*d := by
    have htwo : |2*p h|=2 * |p h| := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    dsimp [A]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,htwo]
    calc
      2 * |p h|*‖h-k‖ ≤ (2*(M*e))*d := by
        have hp : 2 * |p h| ≤ 2*(M*e) :=
          mul_le_mul_of_nonneg_left hPair (by norm_num)
        exact mul_le_mul hp hdelta (norm_nonneg _) (by positivity)
      _ = 2*M*e*d := by ring
  have hB : ‖B‖ ≤ 2*M*d*e := by
    have htwo : |2*(p h-p k)|=2 * |p h-p k| := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    dsimp [B]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,htwo]
    calc
      2 * |p h-p k|*‖k‖ ≤ (2*(M*d))*e := by
        have hp : 2 * |p h-p k| ≤ 2*(M*d) :=
          mul_le_mul_of_nonneg_left hPairDiff (by norm_num)
        exact mul_le_mul hp hk (norm_nonneg _) (by positivity)
      _ = 2*M*d*e := by ring
  have hC : ‖C‖ ≤ 2*e*d*M := by
    dsimp [C]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul hDiffSq hu (norm_nonneg _) (by positivity)
  have hD : ‖D‖ ≤ e^2*d := by
    dsimp [D]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    have hp : ‖h‖^2 ≤ e^2 :=
      pow_le_pow_left₀ (norm_nonneg h) hh 2
    exact mul_le_mul hp hdelta (norm_nonneg _) (by positivity)
  have hE : ‖E‖ ≤ 2*e*d*e := by
    dsimp [E]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul hDiffSq hk (norm_nonneg _) (by positivity)
  rw [hDecomp]
  have hNorm :
      ‖A+(B+(C+(D+E)))‖ ≤
        ‖A‖+‖B‖+‖C‖+‖D‖+‖E‖ := by
    have h1 := norm_add_le A (B+(C+(D+E)))
    have h2 := norm_add_le B (C+(D+E))
    have h3 := norm_add_le C (D+E)
    have h4 := norm_add_le D E
    linarith
  calc
    _ ≤ ‖A‖+‖B‖+‖C‖+‖D‖+‖E‖ := hNorm
    _ ≤ 2*M*e*d+2*M*d*e+2*e*d*M+e^2*d+2*e*d*e := by
      linarith [hA,hB,hC,hD,hE]
    _ = (6*M*e+3*e^2)*d := by ring

end HBL.TypeIIDynamicSelection
