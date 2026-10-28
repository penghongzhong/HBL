import HBL.HartreeRemainderFirstOrderLipschitz
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The complete physical remainder in the classical three-dimensional H1 norm

The target norm uses the sum of the three Cartesian derivative squares.
The perturbation norm is the maximum of the L2 and Linfty norms of the
field and of its real Frechet differential. All finiteness and weak
derivative obligations are supplied by the actual field estimates.
This mixed norm is not the manuscript's homogeneous fractional graph norm;
no embedding of that graph space into this stronger space is asserted.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

namespace HBL.RegularRadiation.RemainderH1
open PhysicalExpansion RemainderFirstOrderLipschitz

/-- The mixed first-order norm on C1 fields with finite displayed norms. -/
def mixedFirstOrderNorm (f : Space → ℂ) : ℝ :=
  max (max (Real.sqrt (∫ x : Space, ‖f x‖ ^ 2))
    (Real.sqrt (∫ x : Space, ‖fderiv ℝ f x‖ ^ 2)))
    (max (lpNorm f ∞ volume) (lpNorm (fderiv ℝ f) ∞ volume))

/-- The classical inhomogeneous H1 norm, using the actual Cartesian derivatives. -/
def physicalH1Norm (f : Space → ℂ) : ℝ :=
  Real.sqrt ((∫ x : Space, ‖f x‖ ^ 2) +
    ∑ i : Fin 3, ∫ x : Space, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2)

private theorem physicalH1Norm_bound (f : Space → ℂ)
    (hDf : MemLp (fderiv ℝ f) 2) {S : ℝ}
    (hS : (∫ x : Space, ‖f x‖ ^ 2) +
      (∫ x : Space, ‖fderiv ℝ f x‖ ^ 2) ≤ S) :
    physicalH1Norm f ≤ Real.sqrt (3 * S) := by
  have hcoord (i : Fin 3) :
      (∫ x : Space, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) ≤
        ∫ x : Space, ‖fderiv ℝ f x‖ ^ 2 := by
    have hm := hDf.continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1))
    apply integral_mono_ae hm.norm.integrable_sq hDf.norm.integrable_sq
    filter_upwards with x
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa using (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i 1)
  have hsum : (∑ i : Fin 3, ∫ x : Space,
        ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) ≤
      3 * (∫ x : Space, ‖fderiv ℝ f x‖ ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin 3, ∫ x : Space, ‖fderiv ℝ f x‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hcoord i)
      _ = _ := by simp
  have hval : 0 ≤ ∫ x : Space, ‖f x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  unfold physicalH1Norm
  apply Real.sqrt_le_sqrt
  linarith

private theorem firstOrderBall_at_mixedNorm (f : Space → ℂ)
    (hf : MemLp f 2) (hDf : MemLp (fderiv ℝ f) 2)
    (hfTop : MemLp f ∞) (hDfTop : MemLp (fderiv ℝ f) ∞) :
    FirstOrderBall f (mixedFirstOrderNorm f) := by
  have h0 : Real.sqrt (∫ x : Space, ‖f x‖ ^ 2) ≤ mixedFirstOrderNorm f :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h1 : Real.sqrt (∫ x : Space, ‖fderiv ℝ f x‖ ^ 2) ≤ mixedFirstOrderNorm f :=
    (le_max_right _ _).trans (le_max_left _ _)
  have h2 : lpNorm f ∞ volume ≤ mixedFirstOrderNorm f :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h3 : lpNorm (fderiv ℝ f) ∞ volume ≤ mixedFirstOrderNorm f :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hf, hDf, ?_, ?_, ?_, ?_⟩
  · exact (ae_le_lpNorm_exponent_top hfTop).mono (fun _ hx => hx.trans h2)
  · exact (ae_le_lpNorm_exponent_top hDfTop).mono (fun _ hx => hx.trans h3)
  · have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) h0 2
    rwa [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hp
  · have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hp

/-- The requested local Lipschitz inequality for the complete physical
remainder, with the actual mixed first-order norm of h-k. The target is the
classical Cartesian H1 norm; all three weak partial derivatives are in L2.
The constant depends only on the four background bounds and kappa. -/
theorem physical_remainder_h1_lipschitz
    (κ : ℝ) (w : Space → ℝ) (h k : Space → ℂ)
    (hw : ContDiff ℝ 1 w) (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    (hw4 : Integrable (fun x : Space => |w x| ^ 4))
    (hDw : MemLp (fderiv ℝ w) 2)
    {M L J E r : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hJ0 : 0 ≤ J) (hE0 : 0 ≤ E)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hDwb : ∀ᵐ x, ‖fderiv ℝ w x‖ ≤ L)
    (hJ : (∫ x : Space, |w x| ^ 4) ≤ J)
    (hE : (∫ x : Space, ‖fderiv ℝ w x‖ ^ 2) ≤ E)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hball : FirstOrderBall h r) (kball : FirstOrderBall k r) :
    let R := fun x => remainder κ w h x - remainder κ w k x
    Differentiable ℝ R ∧ MemLp R 2 ∧ MemLp (fderiv ℝ R) 2 ∧
    (∀ i : Fin 3, MemLp (fun x => fderiv ℝ R x (EuclideanSpace.single i 1)) 2) ∧
    physicalH1Norm R ≤
      Real.sqrt (3 * remainderFirstOrderLipschitzConstant κ M L J E) *
        r * mixedFirstOrderNorm (fun x => h x - k x) ∧
    ∀ φ : Space → ℂ, HasCompactSupport φ → ContDiff ℝ 1 φ → ∀ v : Space,
      Integrable (fun x : Space => R x * fderiv ℝ φ x v) ∧
      Integrable (fun x : Space => fderiv ℝ R x v * φ x) ∧
      (∫ x : Space, R x * fderiv ℝ φ x v) =
        -(∫ x : Space, fderiv ℝ R x v * φ x) := by
  let δ : Space → ℂ := fun x => h x - k x
  let d := mixedFirstOrderNorm δ
  let C := remainderFirstOrderLipschitzConstant κ M L J E
  have hDδ : fderiv ℝ δ = fun x => fderiv ℝ h x - fderiv ℝ k x := by
    funext x
    exact ((hh.differentiable (by norm_num) x).hasFDerivAt.sub
      (hk.differentiable (by norm_num) x).hasFDerivAt).fderiv
  have hδ2 : MemLp δ 2 := hball.value_memLp.sub kball.value_memLp
  have hDδ2 : MemLp (fderiv ℝ δ) 2 := by
    rw [hDδ]
    exact hball.derivative_memLp.sub kball.derivative_memLp
  have hδTop : MemLp δ ∞ :=
    (memLp_top_of_bound hball.value_memLp.aestronglyMeasurable r hball.value_bound).sub
      (memLp_top_of_bound kball.value_memLp.aestronglyMeasurable r kball.value_bound)
  have hDδTop : MemLp (fderiv ℝ δ) ∞ := by
    rw [hDδ]
    exact (memLp_top_of_bound hball.derivative_memLp.aestronglyMeasurable r
      hball.derivative_bound).sub
      (memLp_top_of_bound kball.derivative_memLp.aestronglyMeasurable r
        kball.derivative_bound)
  have hd : 0 ≤ d := (Real.sqrt_nonneg _).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hb := firstOrderBall_at_mixedNorm δ hδ2 hDδ2 hδTop hDδTop
  have ht := physical_remainder_first_order_lipschitz κ w h k hw hh hk hw4 hDw
    hM hL hJ0 hE0 hwb hDwb hJ hE hr hr1 hd hball kball hb
  dsimp only at ht ⊢
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, ?_, ht.2.2.2.2⟩
  · intro i
    exact ht.2.2.1.continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1))
  · have hC : 0 ≤ 3 * C := by
      dsimp [C, remainderFirstOrderLipschitzConstant]
      positivity
    have hfactor : 3 * (C * r ^ 2 * d ^ 2) =
        (Real.sqrt (3 * C) * r * d) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC]
      ring
    calc
      _ ≤ Real.sqrt (3 * (C * r ^ 2 * d ^ 2)) :=
        physicalH1Norm_bound _ ht.2.2.1 ht.2.2.2.1
      _ = Real.sqrt (3 * C) * r * d := by
        rw [hfactor, Real.sqrt_sq (by positivity)]

#print axioms mixedFirstOrderNorm
#print axioms physicalH1Norm
#print axioms physical_remainder_h1_lipschitz

end HBL.RegularRadiation.RemainderH1
