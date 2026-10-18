import Mathlib.Analysis.Fourier.AddCircle

/-!
The cross-term form of Parseval's identity on an interval.

Mathlib already provides the norm-square form for `fourierCoeffOn`.  The
polarized form below is the one needed for the product of two logarithmic
Hartree kernels.
-/

noncomputable section

open MeasureTheory Complex
open scoped Interval ComplexConjugate

namespace HBL

variable {T : ℝ} [hT : Fact (0 < T)]

theorem hasSum_prod_fourierCoeff
    (f g : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    HasSum
      (fun i : ℤ =>
        conj (fourierCoeff (f : AddCircle T → ℂ) i) *
          fourierCoeff (g : AddCircle T → ℂ) i)
      (∫ t : AddCircle T, conj (f t) * g t
        ∂(@AddCircle.haarAddCircle T hT)) := by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun
    ((@fourierBasis T hT).hasSum_inner_mul_inner f g) (fun n => ?_)
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply,
    inner_conj_symm, mul_comm (inner ℂ f _)]

theorem hasSum_prod_fourierCoeffOn
    {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    HasSum
      (fun i : ℤ =>
        conj (fourierCoeffOn hab f i) * fourierCoeffOn hab g i)
      ((b - a)⁻¹ • ∫ x in a..b, conj (f x) * g x) := by
  letI : Fact (0 < b - a) := Fact.mk (by linarith)
  rw [← add_sub_cancel a b] at hf hg
  have hflift := hf.memLp_liftIoc.haarAddCircle
  have hglift := hg.memLp_liftIoc.haarAddCircle
  have hfcoeff (i : ℤ) :
      fourierCoeff
          (hflift.toLp : AddCircle (b - a) → ℂ) i =
        fourierCoeffOn hab f i := by
    simpa [fourierCoeff_liftIoc_eq] using
      congrFun (fourierCoeff_congr_ae hflift.coeFn_toLp) i
  have hgcoeff (i : ℤ) :
      fourierCoeff
          (hglift.toLp : AddCircle (b - a) → ℂ) i =
        fourierCoeffOn hab g i := by
    simpa [fourierCoeff_liftIoc_eq] using
      congrFun (fourierCoeff_congr_ae hglift.coeFn_toLp) i
  have htarget :
      (∫ t : AddCircle (b - a),
          conj ((hflift.toLp :
            Lp ℂ 2 (@AddCircle.haarAddCircle (b - a) this)) t) *
          ((hglift.toLp :
            Lp ℂ 2 (@AddCircle.haarAddCircle (b - a) this)) t)
          ∂(@AddCircle.haarAddCircle (b - a) this)) =
        (b - a)⁻¹ • ∫ x in a..b, conj (f x) * g x := by
    symm
    nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral,
      ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [hflift.coeFn_toLp, hglift.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
    rfl
  rw [← htarget]
  exact (hasSum_prod_fourierCoeff hflift.toLp hglift.toLp).congr_fun
    (fun i => by rw [hfcoeff i, hgcoeff i])

end HBL
