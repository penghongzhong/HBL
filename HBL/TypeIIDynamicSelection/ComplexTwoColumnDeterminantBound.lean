import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

namespace HBL.TypeIIDynamicSelection

private def realColumnDet (v w : ℂ) : ℝ := v.re * w.im - w.re * v.im

private theorem realColumnDet_abs_le (v w : ℂ) :
    |realColumnDet v w| ≤ ‖v‖ * ‖w‖ := by
  have hs : (realColumnDet v w) ^ 2 ≤ (‖v‖ * ‖w‖) ^ 2 := by
    simp only [realColumnDet, mul_pow, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (v.re * w.re + v.im * w.im)]
  have hn : 0 ≤ ‖v‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs (realColumnDet v w), abs_nonneg (realColumnDet v w)]

/-- Quantitative two-real-column stability at the actual reference pair
`(-I*A/2,A)`. This algebraic estimate is used only after both full physical
column errors and the reference integral lower bound have been proved. -/
theorem complex_two_column_determinant_lower_bound
    (A b w : ℂ) (E : ℝ)
    (hb : ‖b + Complex.I * A / 2‖ ≤ E)
    (hw : ‖w - A‖ ≤ E) (hsmall : E ≤ ‖A‖ / 4) :
    ‖A‖ ^ 2 / 16 ≤ b.re * w.im - w.re * b.im := by
  let v : ℂ := -(Complex.I * A / 2)
  let e : ℂ := b - v
  let f : ℂ := w - A
  have hE : 0 ≤ E := (norm_nonneg _).trans hb
  have he : ‖e‖ ≤ E := by simpa [e, v] using hb
  have hf : ‖f‖ ≤ E := hw
  have hv : ‖v‖ = ‖A‖ / 2 := by
    dsimp [v]
    norm_num [norm_div, norm_mul]
  have hvpair : v = ⟨A.im / 2, -A.re / 2⟩ := by
    apply Complex.ext <;> simp [v, Complex.div_re, Complex.div_im] <;> ring
  have hbase : realColumnDet v A = ‖A‖ ^ 2 / 2 := by
    rw [hvpair]
    simp only [realColumnDet, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hdecomp : realColumnDet b w =
      realColumnDet v A + realColumnDet v f + realColumnDet e A +
        realColumnDet e f := by
    dsimp [realColumnDet, e, f]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have h1 : |realColumnDet v f| ≤ (‖A‖ / 2) * E := by
    calc
      _ ≤ ‖v‖ * ‖f‖ := realColumnDet_abs_le v f
      _ ≤ ‖v‖ * E := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
      _ = _ := by rw [hv]
  have h2 : |realColumnDet e A| ≤ E * ‖A‖ :=
    (realColumnDet_abs_le e A).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have h3 : |realColumnDet e f| ≤ E ^ 2 := by
    calc
      _ ≤ ‖e‖ * ‖f‖ := realColumnDet_abs_le e f
      _ ≤ E * E := mul_le_mul he hf (norm_nonneg _) hE
      _ = E ^ 2 := by ring
  have hNE : ‖A‖ * E ≤ ‖A‖ ^ 2 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hsmall (norm_nonneg A)]
  have hE2 : E ^ 2 ≤ ‖A‖ ^ 2 / 16 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall)
      (show 0 ≤ ‖A‖ / 4 + E by positivity)]
  change ‖A‖ ^ 2 / 16 ≤ realColumnDet b w
  rw [hdecomp, hbase]
  linarith [(abs_le.mp h1).1, (abs_le.mp h2).1, (abs_le.mp h3).1]

end HBL.TypeIIDynamicSelection
