import HBL.TypeIIDynamicSelection.ActualHartreeBubbleSquaredDominatedRieszSpatialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylor
import Mathlib.Tactic

/-!
# Full physical two-scale background quartic and first-order Riesz sources

The true scaled Hartree field only satisfies the half-radial condition
 (1+r) * ||U(r)||^2 <= K,
not the false uniform one-bubble ||U|| <= M W.

For any actual original quartic U and correction H <= e W,
both I_2[|U|^4] and I_2[4|U|^2 Re(conj(U) H)] have
an honestly derived O(1/(1+r)) potential via the true inverse-square
logarithmic kernel. These are TWO of the three exact rows entering the
six-product nonlocal Taylor remainder. The quadratic row was previously
certified; no synthetic source or time order is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

private theorem actual_Hartree_one_plus_radius_bubble_le_two
    (r : ℝ) (hr : 0 < r) :
    (1+r)*bubble r ≤ 2 := by
  have hb : bubble r ≤ 1 := bubble_le_one r
  have hd := actual_one_orbit_bubble_le_inverse_radius r hr
  have hR : r*bubble r ≤ 1 := by
    calc
      r*bubble r ≤ r*(1/r) :=
        mul_le_mul_of_nonneg_left hd hr.le
      _ = 1 := by field_simp [hr.ne']
  calc
    (1+r)*bubble r = bubble r+r*bubble r := by ring
    _ ≤ 1+1 := add_le_add hb hR
    _ = 2 := by norm_num

private theorem actual_Hartree_one_le_radius_sq_bubble_sq
    (r : ℝ) (hr : 0 < r) :
    1 ≤ (1+r)^2*bubble r^2 := by
  have hDen : 0 < 1+r^2 := by positivity
  have ht2 : 1+r^2 ≤ (1+r)^2 := by
    nlinarith [hr.le]
  have hFrac : 1 ≤ (1+r)^2/(1+r^2) := by
    apply (le_div_iff₀ hDen).2
    simpa using ht2
  rw [bubble_sq]
  simpa only [div_eq_mul_inv] using hFrac

/-- Same original nonlocal Hartree kernel: the *background density*
and the *real-linear density* gain inverse-radius spatial decay under
a physical HALF-radial field bound and bubble-small correction. -/
theorem actual_Hartree_half_radial_background_and_linear_Riesz_decay
    (U H : ℝ → ℂ)
    (hUmeas : Measurable U) (hHmeas : Measurable H)
    (M K e : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hU : ∀ x : ℝ, 0 < x → ‖U x‖ ≤ M)
    (hHalf : ∀ x : ℝ, 0 < x → (1+x)*‖U x‖^2 ≤ K)
    (hH : ∀ x : ℝ, 0 < x → ‖H x‖ ≤ e*bubble x)
    (r : ℝ) (hr : 0 < r) :
    (IntegrableOn
      (fun x => x*hartreeRadialLog r x*‖U x‖^4)
      (Ioi (0:ℝ)) ∧
     |radialHartreePotential (fun x => ‖U x‖^4) r| ≤
       K^2*actualHartreeBubbleSquaredRieszDecayConstant/(1+r)) ∧
    (IntegrableOn
      (fun x => x*hartreeRadialLog r x*
        actualHartreeComplexDensityLinear (U x) (H x))
      (Ioi (0:ℝ)) ∧
     |radialHartreePotential
       (fun x => actualHartreeComplexDensityLinear (U x) (H x)) r| ≤
       (8*M*K*e)*actualHartreeBubbleSquaredRieszDecayConstant/(1+r)) := by
  have hF0meas : Measurable (fun x => ‖U x‖^4) :=
    hUmeas.norm.pow_const 4
  have hF1meas : Measurable (fun x =>
      actualHartreeComplexDensityLinear (U x) (H x)) := by
    unfold actualHartreeComplexDensityLinear actualHartreeComplexRealPair
    fun_prop
  have hF0 (x : ℝ) (hx : 0 < x) :
      |‖U x‖^4| ≤ K^2*bubble x^2 := by
    let t : ℝ := 1+x
    have ht : 0 < t := by dsimp [t]; linarith
    have hw := actual_Hartree_one_le_radius_sq_bubble_sq x hx
    have hK2 : (t*‖U x‖^2)^2 ≤ K^2 :=
      pow_le_pow_left₀ (mul_nonneg ht.le (sq_nonneg _))
        (hHalf x hx) 2
    have hRaw : t^2*‖U x‖^4 ≤ K^2 := by
      calc
        _ = (t*‖U x‖^2)^2 := by ring
        _ ≤ K^2 := hK2
    have hPos : 0 ≤ ‖U x‖^4 := by positivity
    rw [abs_of_nonneg hPos]
    calc
      ‖U x‖^4 = 1*‖U x‖^4 := by ring
      _ ≤ ((1+x)^2*bubble x^2)*‖U x‖^4 :=
        mul_le_mul_of_nonneg_right hw hPos
      _ = (t^2*‖U x‖^4)*bubble x^2 := by
        dsimp [t]
        ring
      _ ≤ K^2*bubble x^2 :=
        mul_le_mul_of_nonneg_right hRaw (sq_nonneg _)
  have hF1 (x : ℝ) (hx : 0 < x) :
      |actualHartreeComplexDensityLinear (U x) (H x)| ≤
         (8*M*K*e)*bubble x^2 := by
    let t : ℝ := 1+x
    have ht : 0 < t := by dsimp [t]; linarith
    have hTwo := actual_Hartree_one_plus_radius_bubble_le_two x hx
    have hw := actual_Hartree_one_le_radius_sq_bubble_sq x hx
    have hPair :=
      actual_Hartree_complex_real_pair_bound (U x) (H x)
    have hPairRaw :
        |actualHartreeComplexDensityLinear (U x) (H x)| ≤
           (4*‖U x‖^2*‖U x‖)*‖H x‖ := by
      unfold actualHartreeComplexDensityLinear
      calc
        _ = (4*‖U x‖^2)*
            |actualHartreeComplexRealPair (U x) (H x)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4*‖U x‖^2)]
        _ ≤ (4*‖U x‖^2)*(‖U x‖*‖H x‖) :=
          mul_le_mul_of_nonneg_left hPair (by positivity)
        _ = (4*‖U x‖^2*‖U x‖)*‖H x‖ := by ring
    have hA : (t*‖U x‖^2)*‖U x‖ ≤ K*M :=
      mul_le_mul (hHalf x hx) (hU x hx)
        (norm_nonneg _) hK
    have hB : t*‖H x‖ ≤ 2*e := by
      calc
        _ ≤ t*(e*bubble x) :=
          mul_le_mul_of_nonneg_left (hH x hx) ht.le
        _ = e*(t*bubble x) := by ring
        _ ≤ e*2 :=
          mul_le_mul_of_nonneg_left hTwo he
        _ = 2*e := by ring
    have hAB :
        ((t*‖U x‖^2)*‖U x‖)*(t*‖H x‖) ≤
            (K*M)*(2*e) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    have hFourAB :
        4*(((t*‖U x‖^2)*‖U x‖)*(t*‖H x‖)) ≤
          4*((K*M)*(2*e)) :=
      mul_le_mul_of_nonneg_left hAB
        (show (0:ℝ) ≤ 4 by norm_num)
    have hRaw : t^2*
        |actualHartreeComplexDensityLinear (U x) (H x)| ≤
          8*M*K*e := by
      calc
        _ ≤ t^2*((4*‖U x‖^2*‖U x‖)*‖H x‖) :=
          mul_le_mul_of_nonneg_left hPairRaw (sq_nonneg _)
        _ = 4*((t*‖U x‖^2)*‖U x‖)*(t*‖H x‖) := by ring
        _ = 4*(((t*‖U x‖^2)*‖U x‖)*(t*‖H x‖)) := by ring
        _ ≤ 4*((K*M)*(2*e)) := hFourAB
        _ = 8*M*K*e := by ring
    calc
      |actualHartreeComplexDensityLinear (U x) (H x)| =
           1*|actualHartreeComplexDensityLinear (U x) (H x)| := by ring
      _ ≤ ((1+x)^2*bubble x^2)*
           |actualHartreeComplexDensityLinear (U x) (H x)| :=
         mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ = (t^2*|actualHartreeComplexDensityLinear (U x) (H x)|)*
           bubble x^2 := by dsimp [t]; ring
      _ ≤ (8*M*K*e)*bubble x^2 :=
        mul_le_mul_of_nonneg_right hRaw (sq_nonneg _)
  have hC0 : 0 ≤ K^2 := sq_nonneg _
  have hC1 : 0 ≤ 8*M*K*e := by positivity
  have hP0 := actual_Hartree_true_Riesz_bubble_squared_dominated_spatial_decay
    (fun x => ‖U x‖^4) hF0meas (K^2) hC0 hF0 r hr
  have hP1 := actual_Hartree_true_Riesz_bubble_squared_dominated_spatial_decay
    (fun x => actualHartreeComplexDensityLinear (U x) (H x))
    hF1meas (8*M*K*e) hC1 hF1 r hr
  exact ⟨hP0,hP1⟩

end HBL.TypeIIDynamicSelection
