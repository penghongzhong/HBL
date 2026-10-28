import HBL.HartreeDensityRemainderGradient
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Graph-space L1 control of the differentiated Hartree density remainder

This removes the perturbation L2 and gradient Linfinity assumptions from the
L1 part of the noncompact source estimate.  The background factors are kept
instead of being replaced by global constants.  Consequently the estimate
uses precisely the homogeneous-energy exponents
  w,h in L6, Dw,Dh in L2.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
namespace HBL.RegularRadiation.PhysicalExpansion

/-- Pointwise major obtained from the exact differentiated density formula,
with the spatial decay factors retained. -/
def graphDensityGradientMajor
    (w : Space → ℝ) (h : Space → ℂ) (x : Space) : ℝ :=
  4 * ‖fderiv ℝ w x‖ * (3 * |w x| + ‖h x‖) * ‖h x‖ ^ 2 +
  4 * (|w x| ^ 2 + (2 * |w x| + ‖h x‖) * (|w x| + ‖h x‖)) *
    ‖h x‖ * ‖fderiv ℝ h x‖

theorem densityRemainder_fderiv_norm_le_graphMajor
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (x : Space) :
    ‖fderiv ℝ (densityRemainder w h) x‖ ≤
      graphDensityGradientMajor w h x := by
  simpa [graphDensityGradientMajor] using
    densityRemainder_fderiv_norm_le w h
      (hw.differentiable (by norm_num) x)
      (hh.differentiable (by norm_num) x)
      (abs_nonneg (w x)) (norm_nonneg (fderiv ℝ w x)) (norm_nonneg (h x))
      le_rfl le_rfl le_rfl

private theorem norm_w_memLp_six
    (w : Space → ℝ) (hw6 : MemLp w 6) :
    MemLp (fun x => |w x|) 6 := by
  simpa [Real.norm_eq_abs] using hw6.norm

/-- The retained-factor major is integrable using only the homogeneous
energy exponents L6 for values and L2 for first derivatives. -/
theorem graphDensityGradientMajor_integrable
    (w : Space → ℝ) (h : Space → ℂ)
    (hw6 : MemLp w 6) (hDw2 : MemLp (fderiv ℝ w) 2)
    (hh6 : MemLp h 6) (hDh2 : MemLp (fderiv ℝ h) 2) :
    Integrable (graphDensityGradientMajor w h) := by
  let W : Space → ℝ := fun x => |w x|
  let H : Space → ℝ := fun x => ‖h x‖
  let DW : Space → ℝ := fun x => ‖fderiv ℝ w x‖
  let DH : Space → ℝ := fun x => ‖fderiv ℝ h x‖
  have hW6 : MemLp W 6 := by
    simpa [W] using norm_w_memLp_six w hw6
  have hH6 : MemLp H 6 := by
    simpa [H] using hh6.norm
  have hDW2 : MemLp DW 2 := by
    simpa [DW] using hDw2.norm
  have hDH2 : MemLp DH 2 := by
    simpa [DH] using hDh2.norm

  have hH2_3 : MemLp (fun x => H x * H x) 3 := by
    simpa only [Pi.mul_apply] using
      (hH6.mul hH6 : MemLp (H * H) 3)
  have hW2_3 : MemLp (fun x => W x * W x) 3 := by
    simpa only [Pi.mul_apply] using
      (hW6.mul hW6 : MemLp (W * W) 3)

  have hWH2_2 : MemLp (fun x => W x * (H x * H x)) 2 := by
    simpa only [Pi.mul_apply] using
      (hW6.mul hH2_3 : MemLp (W * fun x => H x * H x) 2)
  have hH3_2 : MemLp (fun x => (H x * H x) * H x) 2 := by
    simpa only [Pi.mul_apply] using
      (hH2_3.mul hH6 : MemLp ((fun x => H x * H x) * H) 2)
  have hW2H_2 : MemLp (fun x => (W x * W x) * H x) 2 := by
    simpa only [Pi.mul_apply] using
      (hW2_3.mul hH6 : MemLp ((fun x => W x * W x) * H) 2)
  have hWH_3 : MemLp (fun x => W x * H x) 3 := by
    simpa only [Pi.mul_apply] using
      (hW6.mul hH6 : MemLp (W * H) 3)
  have hWH2_alt_2 : MemLp (fun x => (W x * H x) * H x) 2 := by
    simpa only [Pi.mul_apply] using
      (hWH_3.mul hH6 : MemLp ((fun x => W x * H x) * H) 2)

  have hT1 : Integrable (fun x => (W x * (H x * H x)) * DW x) :=
    memLp_one_iff_integrable.mp <| by
      simpa only [Pi.mul_apply] using
        (hWH2_2.mul hDW2 :
          MemLp ((fun x => W x * (H x * H x)) * DW) 1)
  have hT2 : Integrable (fun x => ((H x * H x) * H x) * DW x) :=
    memLp_one_iff_integrable.mp <| by
      simpa only [Pi.mul_apply] using
        (hH3_2.mul hDW2 :
          MemLp ((fun x => (H x * H x) * H x) * DW) 1)
  have hT3 : Integrable (fun x => ((W x * W x) * H x) * DH x) :=
    memLp_one_iff_integrable.mp <| by
      simpa only [Pi.mul_apply] using
        (hW2H_2.mul hDH2 :
          MemLp ((fun x => (W x * W x) * H x) * DH) 1)
  have hT4 : Integrable (fun x => ((W x * H x) * H x) * DH x) :=
    memLp_one_iff_integrable.mp <| by
      simpa only [Pi.mul_apply] using
        (hWH2_alt_2.mul hDH2 :
          MemLp ((fun x => (W x * H x) * H x) * DH) 1)
  have hT5 : Integrable (fun x => ((H x * H x) * H x) * DH x) :=
    memLp_one_iff_integrable.mp <| by
      simpa only [Pi.mul_apply] using
        (hH3_2.mul hDH2 :
          MemLp ((fun x => (H x * H x) * H x) * DH) 1)

  have hsum :
      Integrable (fun x =>
        12 * ((W x * (H x * H x)) * DW x) +
        4 * (((H x * H x) * H x) * DW x) +
        12 * (((W x * W x) * H x) * DH x) +
        12 * (((W x * H x) * H x) * DH x) +
        4 * (((H x * H x) * H x) * DH x)) :=
    ((((hT1.const_mul 12).add (hT2.const_mul 4)).add
      (hT3.const_mul 12)).add (hT4.const_mul 12)).add (hT5.const_mul 4)

  convert hsum using 1
  funext x
  dsimp [graphDensityGradientMajor, W, H, DW, DH]
  ring

/-- L1 graph-source closure for the exact differentiated physical density.
No L2 assumption on h and no Linfinity assumption on Dh occurs. -/
theorem densityRemainder_gradient_integrable_graph
    (w : Space → ℝ) (h : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h)
    (hw6 : MemLp w 6) (hDw2 : MemLp (fderiv ℝ w) 2)
    (hh6 : MemLp h 6) (hDh2 : MemLp (fderiv ℝ h) 2) :
    Integrable (fderiv ℝ (densityRemainder w h)) := by
  apply (graphDensityGradientMajor_integrable w h hw6 hDw2 hh6 hDh2).mono'
    ((densityRemainder_contDiff w h hw hh).continuous_fderiv
      (by norm_num)).aestronglyMeasurable
  filter_upwards with x
  have hmajor := densityRemainder_fderiv_norm_le_graphMajor w h hw hh x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by
      unfold graphDensityGradientMajor
      positivity)]
  exact hmajor

#print axioms densityRemainder_fderiv_norm_le_graphMajor
#print axioms graphDensityGradientMajor_integrable
#print axioms densityRemainder_gradient_integrable_graph

end HBL.RegularRadiation.PhysicalExpansion
