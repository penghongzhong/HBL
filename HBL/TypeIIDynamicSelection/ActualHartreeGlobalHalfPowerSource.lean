import HBL.TypeIIDynamicSelection.ActualHartreeSlowInnerHalfPowerSource
import HBL.InnerEstimates.WeightedNormIdentity

/-!
A uniform square-root-length bound for the COMPLETE original spatial
Hartree interaction, on the whole half-line. All three physical Riesz
potentials and both fields are the actual existing source definitions.
This strengthens the old ell^(1/8) global source envelope and, together
with the improved conjugated inner source, removes an avoidable loss
from both inputs to the original Cramer selection estimates.
It does not prove time differentiation, full PDE residual or an orbit.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

def actualHartreeGlobalHalfPowerConstant (B A : ℝ) : ℝ :=
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let CW : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  let Cm := (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 + 4 * D * E ^ 3) * CW
  let Cz := 2 * (B ^ 4 + A ^ 4) * CW
  let C4 := 6 * D ^ 4
  Cm * (D ^ 3 + (2 * D + E) ^ 2 * E) +
    Cz * (D + 2 * E) ^ 2 * D + C4 * (2 * D + E) ^ 2 * E

private theorem ten_term_half_radius_bound
    (w s D E Cm Cz C4 pm pz pc v z : ℝ)
    (hw : 1 ≤ w) (hs : 0 ≤ s) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hCm : 0 ≤ Cm) (hCz : 0 ≤ Cz) (hC4 : 0 ≤ C4)
    (hpm0 : 0 ≤ pm) (hpz0 : 0 ≤ pz) (hpc0 : 0 ≤ pc)
    (hv0 : 0 ≤ v) (hz0 : 0 ≤ z)
    (hpm : w ^ 2 * pm ≤ Cm * s) (hpz : w * pz ≤ Cz * s)
    (hpc : w ^ 4 * pc ≤ C4) (hv : w ^ 2 * v ≤ D)
    (hz : w * z ≤ E) (hzs : z ≤ E * s) :
    w ^ 5 * (pm * (v ^ 3 + (2 * v + z) ^ 2 * z) +
      pz * ((v + 2 * z) ^ 2 * v) + pc * ((2 * v + z) ^ 2 * z)) ≤
      (Cm * (D ^ 3 + (2 * D + E) ^ 2 * E) +
        Cz * (D + 2 * E) ^ 2 * D + C4 * (2 * D + E) ^ 2 * E) * s := by
  have hw0 : 0 ≤ w := by linarith
  have hwv : w * v ≤ D := by
    have hww : w ≤ w ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hww hv0).trans hv
  have hm : (w ^ 2 * pm) * ((w * v) ^ 3 + (2 * (w * v) + w * z) ^ 2 * (w * z)) ≤
      (Cm * s) * (D ^ 3 + (2 * D + E) ^ 2 * E) := by gcongr
  have hr : (w * pz) * ((w * v) + 2 * (w * z)) ^ 2 * (w ^ 2 * v) ≤
      (Cz * s) * (D + 2 * E) ^ 2 * D := by gcongr
  have hc6 : w ^ 6 * (pc * ((2 * v + z) ^ 2 * z)) ≤
      C4 * (2 * D + E) ^ 2 * (E * s) := by
    calc
      _ = (w ^ 4 * pc) * (2 * (w * v) + w * z) ^ 2 * z := by ring
      _ ≤ _ := by gcongr
  have hc : w ^ 5 * (pc * ((2 * v + z) ^ 2 * z)) ≤
      C4 * (2 * D + E) ^ 2 * (E * s) := by
    apply le_trans _ hc6
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      w ^ 5 = w ^ 5 * 1 := by ring
      _ ≤ w ^ 5 * w := mul_le_mul_of_nonneg_left hw (pow_nonneg hw0 _)
      _ = w ^ 6 := by ring
  calc
    _ = (w ^ 2 * pm) * ((w * v) ^ 3 + (2 * (w * v) + w * z) ^ 2 * (w * z)) +
        (w * pz) * ((w * v) + 2 * (w * z)) ^ 2 * (w ^ 2 * v) +
        w ^ 5 * (pc * ((2 * v + z) ^ 2 * z)) := by ring
    _ ≤ (Cm * s) * (D ^ 3 + (2 * D + E) ^ 2 * E) +
        (Cz * s) * (D + 2 * E) ^ 2 * D +
        C4 * (2 * D + E) ^ 2 * (E * s) := add_le_add (add_le_add hm hr) hc
    _ = _ := by ring

/-- Whole-half-line physical interaction: no independent potential
or weighted-source bounds occur among the hypotheses. -/
theorem actual_Hartree_global_physical_half_power
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hr : 0 < r) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    (Real.sqrt (1 + r)) ^ 5 * ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
      actualHartreeGlobalHalfPowerConstant B A * Real.sqrt ell := by
  let V : ℝ → ℝ := monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let CW : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  let Cm : ℝ := (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 + 4 * D * E ^ 3) * CW
  let Cz : ℝ := 2 * (B ^ 4 + A ^ 4) * CW
  let C4 : ℝ := 6 * D ^ 4
  let pm := radialHartreePotential (actualWholeRadiationMixedQuartic V Z) r
  let pz := radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r
  let pc := radialHartreePotential (fun rho => ‖(V rho : ℂ)‖ ^ 4) r
  let w := Real.sqrt (1 + r)
  let s := Real.sqrt ell
  let q := 1 + ell * r
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ell := Real.sq_sqrt hell.le
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 1 + r := Real.sq_sqrt (by linarith)
  have hw : 1 ≤ w := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + r by linarith)
    simpa only [Real.sqrt_one] using h
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by dsimp [q]; nlinarith [mul_pos hell hr]
  have hsw : s * w ≤ q := by
    have hp : (s * w) ^ 2 ≤ q := by rw [mul_pow, hs2, hw2]; dsimp [q]; nlinarith
    nlinarith [mul_nonneg hs hw0]
  have hfrac : s * w / q ≤ 1 := (div_le_one hq).2 hsw
  have hD : 0 ≤ D := by dsimp [D]; have h := monopoleRadialBoundConstant_pos; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCW : 0 ≤ CW := actualHartreeBubbleSquaredRieszDecayConstant_pos.le
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have hCz : 0 ≤ Cz := by dsimp [Cz]; positivity
  have hC4 : 0 ≤ C4 := by dsimp [C4]; positivity
  have hd : 0 < 1 + r := by linarith
  have hPmRaw : |pm| ≤ Cm * s / (1 + r) :=
    actual_Hartree_full_mixed_Riesz_spatial_decay
      ell c r B A hell hellOne hr hc hB hA z hz hSup hStrauss
  have hPm : w ^ 2 * |pm| ≤ Cm * s := by
    rw [hw2]
    simpa only [mul_comm] using (le_div_iff₀ hd).1 hPmRaw
  have hPzRaw : |pz| ≤ Cz * ell / q :=
    actual_Hartree_pure_radiation_Riesz_global_scaled_decay
      ell r B A hell hr hB hA z hz hSup hStrauss
  have hPz : w * |pz| ≤ Cz * s := by
    calc
      _ ≤ w * (Cz * ell / q) := mul_le_mul_of_nonneg_left hPzRaw hw0
      _ = (Cz * s) * (s * w / q) := by rw [← hs2]; ring
      _ ≤ (Cz * s) * 1 := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hCz hs)
      _ = _ := mul_one _
  have hRealQuartic : (fun rho : ℝ => ‖(V rho : ℂ)‖ ^ 4) = (fun rho => V rho ^ 4) := by
    funext rho
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |V rho| ^ 4 = (|V rho| ^ 2) ^ 2 := by ring
      _ = (V rho ^ 2) ^ 2 := by rw [sq_abs]
      _ = V rho ^ 4 := by ring
  have hPcRaw : |pc| ≤ C4 / (1 + r) ^ 2 := by
    dsimp only [pc]
    rw [hRealQuartic]
    exact actual_Hartree_moving_core_Riesz_inverse_square c r hc hr
  have hPc : w ^ 4 * |pc| ≤ C4 := by
    have hw4 : w ^ 4 = (1 + r) ^ 2 := by
      calc
        w ^ 4 = (w ^ 2) ^ 2 := by ring
        _ = _ := by rw [hw2]
    rw [hw4]
    simpa only [mul_comm] using (le_div_iff₀ (pow_pos hd 2)).1 hPcRaw
  have hV : w ^ 2 * ‖(V r : ℂ)‖ ≤ D := by
    rw [hw2, Complex.norm_real, Real.norm_eq_abs]
    exact actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hZRaw : ‖Z r‖ ≤ E * s / q := by
    apply (le_div_iff₀ hq).2
    simpa only [mul_comm] using actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
  have hZ : w * ‖Z r‖ ≤ E := by
    calc
      _ ≤ w * (E * s / q) := mul_le_mul_of_nonneg_left hZRaw hw0
      _ = E * (s * w / q) := by ring
      _ ≤ E * 1 := mul_le_mul_of_nonneg_left hfrac hE
      _ = _ := mul_one _
  have hZs : ‖Z r‖ ≤ E * s := hZRaw.trans (div_le_self (mul_nonneg hE hs) hq1)
  have hScalar := ten_term_half_radius_bound w s D E Cm Cz C4 |pm| |pz| |pc| ‖(V r : ℂ)‖ ‖Z r‖
    hw hs hD hE hCm hCz hC4 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hPm hPz hPc hV hZ hZs
  have hNorm := actual_Hartree_physical_interaction_complete_ten_term_norm_le
    (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r
  exact (mul_le_mul_of_nonneg_left hNorm (pow_nonneg hw0 5)).trans hScalar

end HBL.TypeIIDynamicSelection
