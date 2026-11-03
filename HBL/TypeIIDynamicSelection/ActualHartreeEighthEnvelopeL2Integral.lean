import HBL.TypeIIDynamicSelection.ActualHartreeThreeFredholmEnvelopes
import HBL.AffineTailRationalIntegrability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Revised HBL 2.13 — true positive L2 membership from the critical 1/8 envelope

This proves the ANALYTIC step left after the strict three scalar
radial/scale Hartree source estimates. The half-line envelope
(1+r)^(-5/8) is in the original L² half-line space. Any measurable
weighted source dominated by C*ell^(1/8)*(1+r)^(-5/8) has
squared-L² norm O(ell^(1/4)).

The lemma has no asserted PDE source bounds, rate, or generated-term
order. It must be specialized to the single true four-product
Hartree PDE source in a later statement; that obligation is OPEN.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.AffineTail

/-- The real square of the radial profile has integrable decay on
the original positive half-line; no unsupported formal integration. -/
theorem actual_Hartree_eighth_weighted_envelope_square_integrable :
    IntegrableOn
      (fun r : ℝ => ((1 + r) ^ (-(5 / 8 : ℝ))) ^ 2)
      (Ioi (0 : ℝ)) := by
  have hBase :
      IntegrableOn (fun r : ℝ => (r + 1) ^ (-(5 / 4 : ℝ)))
        (Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt
      (show -(5 / 4 : ℝ) < -1 by norm_num)
      (show -(1 : ℝ) < 0 by norm_num)
  have hEq :
      (fun r : ℝ => ((1 + r) ^ (-(5 / 8 : ℝ))) ^ 2) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
        (fun r : ℝ => (r + 1) ^ (-(5 / 4 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hd : 0 ≤ (1 : ℝ) + r := by linarith
    calc
      ((1 + r) ^ (-(5 / 8 : ℝ))) ^ 2 =
          ((1 + r) ^ (-(5 / 8 : ℝ))) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (1 + r) ^ (-(5 / 8 : ℝ) * 2) :=
        (Real.rpow_mul hd (-(5 / 8 : ℝ)) 2).symm
      _ = (r + 1) ^ (-(5 / 4 : ℝ)) := by
        norm_num
        rw [add_comm]
  exact hBase.congr hEq.symm

/-- Quantitative squared L2 source estimate from the exact
epsilon=1/8 radial Hartree source majorant, on the manuscript's
genuine positive half-line. The integral constant is finite and
determined by the original Lebesgue measure, not assumed. -/
theorem actual_Hartree_eighth_weighted_source_L2_of_pointwise
    (S : ℝ → ℝ) (ell C : ℝ)
    (hell : 0 < ell) (hC : 0 ≤ C)
    (hSmeas : Measurable S)
    (hSnonneg : ∀ r : ℝ, 0 < r → 0 ≤ S r)
    (hPoint : ∀ r : ℝ, 0 < r →
      S r ≤ C * ell ^ (1 / 8 : ℝ) * (1 + r) ^ (-(5 / 8 : ℝ))) :
    MemLp S 2 halfLineMeasure ∧
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
      (C * ell ^ (1 / 8 : ℝ)) ^ 2 *
        (∫ r in Ioi (0 : ℝ),
          (1 + r) ^ (-(5 / 4 : ℝ))) := by
  have hTailInt :
      IntegrableOn (fun r : ℝ => (1 + r) ^ (-(5 / 4 : ℝ)))
        (Ioi (0 : ℝ)) := by
    simpa only [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt
        (show -(5 / 4 : ℝ) < -1 by norm_num)
        (show -(1 : ℝ) < 0 by norm_num))
  have hMajorInt :
      IntegrableOn
        (fun r : ℝ =>
          (C * ell ^ (1 / 8 : ℝ)) ^ 2 *
          (1 + r) ^ (-(5 / 4 : ℝ)))
        (Ioi (0 : ℝ)) :=
    hTailInt.const_mul ((C * ell ^ (1 / 8 : ℝ)) ^ 2)
  have hSqMeas :
      AEStronglyMeasurable (fun r : ℝ => S r ^ 2)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (hSmeas.pow_const 2).aestronglyMeasurable.restrict
  have hBound (r : ℝ) (hr : 0 < r) :
      S r ^ 2 ≤
        (C * ell ^ (1 / 8 : ℝ)) ^ 2 *
          (1 + r) ^ (-(5 / 4 : ℝ)) := by
    have hSq :=
      pow_le_pow_left₀ (hSnonneg r hr) (hPoint r hr) 2
    have hd : 0 ≤ (1 : ℝ) + r := by linarith
    have hPow :
        ((1 + r) ^ (-(5 / 8 : ℝ))) ^ 2 =
          (1 + r) ^ (-(5 / 4 : ℝ)) := by
      calc
        _ = ((1 + r) ^ (-(5 / 8 : ℝ))) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (1 + r) ^ (-(5 / 8 : ℝ) * 2) :=
          (Real.rpow_mul hd (-(5 / 8 : ℝ)) 2).symm
        _ = _ := by norm_num
    simpa only [mul_pow, hPow] using hSq
  have hSqInt :
      IntegrableOn (fun r : ℝ => S r ^ 2)
        (Ioi (0 : ℝ)) := by
    apply hMajorInt.mono' hSqMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (S r))]
    exact hBound r hr
  have hL2 : MemLp S 2 halfLineMeasure := by
    apply (memLp_two_iff_integrable_sq
      (hSmeas.aestronglyMeasurable.restrict)).2
    exact hSqInt
  refine ⟨hL2,?_⟩
  calc
    (∫ r in Ioi (0 : ℝ), S r ^ 2) ≤
        ∫ r in Ioi (0 : ℝ),
          (C * ell ^ (1 / 8 : ℝ)) ^ 2 *
          (1 + r) ^ (-(5 / 4 : ℝ)) := by
      apply integral_mono_ae hSqInt hMajorInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hBound r hr
    _ = (C * ell ^ (1 / 8 : ℝ)) ^ 2 *
        (∫ r in Ioi (0 : ℝ),
          (1 + r) ^ (-(5 / 4 : ℝ))) := by
      rw [integral_const_mul]

end HBL.TypeIIDynamicSelection
