import HBL.FullRadialEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
The explicit stationary bubble as a vector of the full radial energy space.

For W(r) = (1+r^2)^(-1/2),
  U W(r) = r W(r),
and a direct derivative calculation gives
  (U W)'(r) = 1 / (sqrt(1+r^2))^3.
Its square is dominated by (1+r^2)^(-1), an integrable Cauchy weight.
Hence (U W)' belongs to L2 on (0,∞).  This closes the remaining
object-level premise in the full-half-line modulation theorem.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace HBL.Modulation

/-- Closed form of the radial-energy derivative of the stationary bubble. -/
def bubbleRadialEnergyDerivative (r : ℝ) : ℝ :=
  (Real.sqrt (1 + r ^ 2) ^ 3)⁻¹

/-- Direct differentiation of U W = r / sqrt(1+r^2). -/
theorem radialU_bubble_hasDerivAt_closed (r : ℝ) :
    HasDerivAt (radialU bubble)
      (bubbleRadialEnergyDerivative r) r := by
  have hq :
      HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    convert ((hasDerivAt_id r).pow 2).const_add 1 using 1 <;> ring
  have hqpos : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hs :
      HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
        ((2 * r) / (2 * Real.sqrt (1 + r ^ 2))) r :=
    hq.sqrt (ne_of_gt hqpos)
  have hspos : 0 < Real.sqrt (1 + r ^ 2) :=
    Real.sqrt_pos.2 hqpos
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 :=
    ne_of_gt hspos
  have hs2 :
      Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt hqpos.le
  have hdiv :=
    (hasDerivAt_id r).div hs hsne
  have hder :
      ((1 : ℝ) * Real.sqrt (1 + r ^ 2) -
          r * ((2 * r) / (2 * Real.sqrt (1 + r ^ 2)))) /
          Real.sqrt (1 + r ^ 2) ^ 2 =
        bubbleRadialEnergyDerivative r := by
    unfold bubbleRadialEnergyDerivative
    field_simp [hsne]
    nlinarith [hs2]
  rw [hder] at hdiv
  simpa [radialU, bubble, div_eq_mul_inv, id_eq] using hdiv

/-- The classical derivative equals the closed energy-density formula. -/
theorem radialU_bubble_deriv_closed (r : ℝ) :
    deriv (radialU bubble) r = bubbleRadialEnergyDerivative r :=
  (radialU_bubble_hasDerivAt_closed r).deriv

/-- The explicit energy derivative is continuous. -/
theorem bubbleRadialEnergyDerivative_continuous :
    Continuous bubbleRadialEnergyDerivative := by
  unfold bubbleRadialEnergyDerivative
  fun_prop (discharger := intro; positivity)

/-- Square of the bubble energy derivative is dominated by the standard
integrable Cauchy weight. -/
theorem bubbleRadialEnergyDerivative_sq_le (r : ℝ) :
    ‖bubbleRadialEnergyDerivative r ^ 2‖ ≤ (1 + r ^ 2)⁻¹ := by
  let s : ℝ := Real.sqrt (1 + r ^ 2)
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hs1 : 1 ≤ s := by
    dsimp [s]
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg r]
  have hs2 : s ^ 2 = 1 + r ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have hs4 : 1 ≤ s ^ 4 := by
    exact one_le_pow₀ hs1
  have hs26 : s ^ 2 ≤ s ^ 6 := by
    calc
      s ^ 2 = s ^ 2 * 1 := by ring
      _ ≤ s ^ 2 * s ^ 4 :=
        mul_le_mul_of_nonneg_left hs4 (sq_nonneg s)
      _ = s ^ 6 := by ring
  have hinv : (s ^ 6)⁻¹ ≤ (s ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hs26
  have hleft :
      ‖bubbleRadialEnergyDerivative r ^ 2‖ = (s ^ 6)⁻¹ := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    unfold bubbleRadialEnergyDerivative
    dsimp [s]
    field_simp [ne_of_gt hspos]
    ring
  have hright : (1 + r ^ 2)⁻¹ = (s ^ 2)⁻¹ := by
    rw [hs2]
  rw [hleft, hright]
  exact hinv

/-- The bubble energy derivative is square integrable on the full line,
hence in particular on the positive half-line. -/
theorem bubbleRadialEnergyDerivative_sq_integrable :
    Integrable (fun r : ℝ => bubbleRadialEnergyDerivative r ^ 2) volume := by
  have hmeas :
      AEStronglyMeasurable
        (fun r : ℝ => bubbleRadialEnergyDerivative r ^ 2) volume :=
    (bubbleRadialEnergyDerivative_continuous.pow 2).aestronglyMeasurable
  exact integrable_inv_one_add_sq.mono'
    hmeas (Filter.Eventually.of_forall
      bubbleRadialEnergyDerivative_sq_le)

/-- The explicit stationary bubble defines a genuine vector of the full
radial homogeneous-energy Hilbert coordinate. -/
theorem bubbleRadialEnergyDerivative_memLp :
    MemLp bubbleRadialEnergyDerivative 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas :
      AEStronglyMeasurable bubbleRadialEnergyDerivative
        (volume.restrict (Ioi (0 : ℝ))) :=
    bubbleRadialEnergyDerivative_continuous.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  exact bubbleRadialEnergyDerivative_sq_integrable.integrableOn

/-- Full-half-line radial energy vector of the stationary bubble. -/
def fullBubbleRadialEnergyL2 : FullRadialEnergyL2 :=
  bubbleRadialEnergyDerivative_memLp.toLp bubbleRadialEnergyDerivative

/-- The full bubble vector restricts exactly to the finite-radius bubble
coordinate used in the already verified local modulation theorem. -/
theorem fullBubbleRadialEnergyL2_restrict
    (R : ℝ) (hR : 0 ≤ R) :
    fullToFiniteRadialEnergy R fullBubbleRadialEnergyL2 =
      bubbleRadialEnergyL2 R hR := by
  apply Lp.ext
  let μR : Measure ℝ := volume.restrict (Ioc (0 : ℝ) R)
  let μ∞ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hμ : μR ≤ μ∞ := by
    simpa [μR, μ∞] using finiteRadialMeasure_le_full R
  have hac : μR ≪ μ∞ := Measure.absolutelyContinuous_of_le hμ
  have hfull :
      (fullBubbleRadialEnergyL2 : ℝ → ℝ) =ᵐ[μ∞]
        bubbleRadialEnergyDerivative := by
    unfold fullBubbleRadialEnergyL2
    exact bubbleRadialEnergyDerivative_memLp.coeFn_toLp
  have hfullR :
      (fullBubbleRadialEnergyL2 : ℝ → ℝ) =ᵐ[μR]
        bubbleRadialEnergyDerivative :=
    hac.ae_eq hfull
  have hrestrict :=
    fullToFiniteRadialEnergy_ae R fullBubbleRadialEnergyL2
  have hfinite :=
    radialUDerivativeL2_ae R hR bubble bubble_contDiff
  filter_upwards [hrestrict, hfullR, hfinite] with r hr hbr hfin
  rw [hr, hbr, hfin]
  exact (radialU_bubble_deriv_closed r).symm

/-- The concrete full-half-line version of the first modulation theorem:
the base point is now the actual explicit stationary-bubble energy vector,
not an abstract vector with a restriction hypothesis. -/
theorem fullRadialEnergy_local_modulation
    (R : ℝ) (hR : 0 ≤ R)
    (zPlus zMinus : ℝ → ℝ)
    (hzPlus : ContDiff ℝ 1 zPlus)
    (hzMinus : ContDiff ℝ 1 zMinus)
    (hzPlusR : zPlus R = 0)
    (hPlusNorm :
      (∫ r in (0 : ℝ)..R,
        zPlus r * radialResonancePlus r) = 1)
    (hMinusNorm :
      (∫ r in (0 : ℝ)..R,
        zMinus r * radialResonanceMinus r) = 1) :
    ∃ Phi : (FullRadialEnergyL2 × FullRadialEnergyL2) → Param,
      Phi (fullBubbleRadialEnergyL2, (0 : FullRadialEnergyL2)) = (1, 0) ∧
      ContDiffAt ℝ 1 Phi
        (fullBubbleRadialEnergyL2, (0 : FullRadialEnergyL2)) ∧
      (∀ u, 0 < (Phi u).1) ∧
      (∀ᶠ u in 𝓝
        (fullBubbleRadialEnergyL2, (0 : FullRadialEnergyL2)),
        scalePhaseResidual
          (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
          (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
          fullBubbleRadialEnergyL2
          (u, (Real.log (Phi u).1, (Phi u).2)) = 0) ∧
      (∀ᶠ v in 𝓝
        ((fullBubbleRadialEnergyL2, (0 : FullRadialEnergyL2)),
          (0 : Param)),
        (scalePhaseResidual
          (fullTransportedEnergyThresholdDual R hR zPlus hzPlus)
          (fullTransportedEnergyThresholdDual R hR zMinus hzMinus)
          fullBubbleRadialEnergyL2 v = 0 ↔
          (Real.log (Phi v.1).1, (Phi v.1).2) = v.2)) := by
  exact fullRadialEnergy_local_modulation_of_restrict_bubble
    R hR zPlus zMinus hzPlus hzMinus hzPlusR
    hPlusNorm hMinusNorm fullBubbleRadialEnergyL2
    (fullBubbleRadialEnergyL2_restrict R hR)

end HBL.Modulation
