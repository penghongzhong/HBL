import HBL.TypeIIDynamicSelection.ActualHartreePhysicalFullWeightedSource
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInteractionMeasurable
import HBL.WeightedPhaseAffineSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Full physical Hartree interaction in the original weighted L2 space

For the SAME moving monopole and scaled physical radiation, derive
measurability, the ten-term bound, and its half-line integral. The
conclusion has constant K(B,A), independent of c,ell and radius.
No pointwise source bound or Riesz estimate is assumed in this theorem:
the proof obtains them from the original-kernel results.

Only the specified physical measurability, amplitude and Strauss inputs
are retained. This is a spatial nonlinear interaction estimate, not the
three-region matched finite-profile theorem or a blowup-rate hypothesis.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Full ORIGINAL Hartree interaction is in L^{2,7/4}(dr), with squared
weighted norm at most K(B,A)^2 ell^(1/4) times a fixed finite integral.
The positive-order physical scale is an output, not a source assumption. -/
theorem actual_Hartree_physical_full_interaction_weighted_L2
    (B A ell c : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    MemLp
      (fun r : ℝ => affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreePhysicalSliceInteraction ell c z r‖)
      2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ),
      (affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreePhysicalSliceInteraction ell c z r‖) ^ 2) ≤
    (actualHartreePhysicalWeightedSourceConstant B A) ^ 2 *
      ell ^ (1 / 4 : ℝ) *
      (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let K : ℝ := actualHartreePhysicalWeightedSourceConstant B A
  let S : ℝ → ℝ := fun r => affineJapaneseWeight (7 / 4 : ℝ) r *
    ‖actualHartreePhysicalSliceInteraction ell c z r‖
  have hV : Measurable V := actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z, rescalePhysicalRadiation]
    exact measurable_const.mul (hz.comp (measurable_const.mul measurable_id))
  have hF : Measurable (actualHartreePhysicalSliceInteraction ell c z) :=
    actual_Hartree_physical_complete_interaction_measurable V Z hV hZ
  have hSm : Measurable S :=
    (affineJapaneseWeight_continuous (7 / 4 : ℝ)).measurable.mul hF.norm
  have hS0 (r : ℝ) : 0 ≤ S r := by
    dsimp [S, affineJapaneseWeight]
    positivity
  have hPoint (r : ℝ) (hr : 0 < r) :
      S r ≤ K * ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ)) :=
    actual_Hartree_physical_full_interaction_Japanese_pointwise
      ell c r B A hell hellOne hc hr hB hA z hz hSup hStrauss
  have hTailInt : IntegrableOn
      (fun r : ℝ => (1 + r) ^ (-(5 / 4 : ℝ))) (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt
        (show -(5 / 4 : ℝ) < -1 by norm_num)
        (show -(1 : ℝ) < 0 by norm_num))
  have hMajorInt : IntegrableOn
      (fun r : ℝ => (K * ell ^ (1 / 8 : ℝ)) ^ 2 *
        (1 + r) ^ (-(5 / 4 : ℝ))) (Ioi (0 : ℝ)) :=
    hTailInt.const_mul ((K * ell ^ (1 / 8 : ℝ)) ^ 2)
  have hSq (r : ℝ) (hr : 0 < r) :
      S r ^ 2 ≤ (K * ell ^ (1 / 8 : ℝ)) ^ 2 *
        (1 + r) ^ (-(5 / 4 : ℝ)) := by
    have hp := pow_le_pow_left₀ (hS0 r) (hPoint r hr) 2
    have hd : 0 ≤ (1 : ℝ) + r := by linarith
    have hPower : ((1 + r) ^ (-(5 / 8 : ℝ))) ^ 2 =
        (1 + r) ^ (-(5 / 4 : ℝ)) := by
      calc
        _ = ((1 + r) ^ (-(5 / 8 : ℝ))) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (1 + r) ^ (-(5 / 8 : ℝ) * 2) :=
          (Real.rpow_mul hd (-(5 / 8 : ℝ)) 2).symm
        _ = _ := by norm_num
    simpa only [mul_pow, hPower] using hp
  have hInt : IntegrableOn (fun r : ℝ => S r ^ 2) (Ioi (0 : ℝ)) := by
    apply hMajorInt.mono' (hSm.pow_const 2).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S r))]
    exact hSq r hr
  have hLp : MemLp S 2 halfLineMeasure :=
    (memLp_two_iff_integrable_sq hSm.aestronglyMeasurable.restrict).2 hInt
  have hEllPower : (ell ^ (1 / 8 : ℝ)) ^ 2 = ell ^ (1 / 4 : ℝ) := by
    calc
      _ = (ell ^ (1 / 8 : ℝ)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = ell ^ ((1 / 8 : ℝ) * 2) :=
        (Real.rpow_mul hell.le (1 / 8 : ℝ) 2).symm
      _ = _ := by norm_num
  change MemLp S 2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
      K ^ 2 * ell ^ (1 / 4 : ℝ) *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ)))
  refine ⟨hLp, ?_⟩
  calc
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        ∫ r in Ioi (0 : ℝ), (K * ell ^ (1 / 8 : ℝ)) ^ 2 *
          (1 + r) ^ (-(5 / 4 : ℝ)) := by
      apply integral_mono_ae hInt hMajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hSq r hr
    _ = (K * ell ^ (1 / 8 : ℝ)) ^ 2 *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
      rw [integral_const_mul]
    _ = K ^ 2 * ell ^ (1 / 4 : ℝ) *
        (∫ r in Ioi (0 : ℝ), (1 + r) ^ (-(5 / 4 : ℝ))) := by
      rw [mul_pow, hEllPower]

end HBL.TypeIIDynamicSelection
