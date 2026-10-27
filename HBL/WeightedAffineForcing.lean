import HBL.WeightedCenterFeedbackMap
import HBL.WeightedThresholdMap
import Mathlib.Tactic

/-!
# Weighted affine forcing paths

The fixed high-order profile residual and the threshold/profile forcing are
converted into the two affine paths used by the nonlinear backward fixed
point.  Their smallness at late time is proved from their explicit decay.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

def weightedThresholdForcingTail
    (F : ℝ → ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  -(∫ t in Ioi s, F t)

def weightedThresholdForcingValue
    (F : ℝ → ℝ × ℝ) (p : ℝ) (s : ℝ) : ℝ × ℝ :=
  (s ^ (p-1)) • weightedThresholdForcingTail F s

theorem weightedThresholdForcing_bound
    (F : ℝ → ℝ × ℝ) (s0 p CF s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hCF : 0 ≤ CF)
    (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF * t ^ (-p-1))
    (hs : s0 ≤ s) :
    ‖weightedThresholdForcingValue F p s‖ ≤
      (CF / p) * s0⁻¹ := by
  have hsp : 0 < s := hs0.trans_le hs
  have hi : IntegrableOn F (Ioi s) := by
    have hmajor : IntegrableOn (fun t : ℝ => CF * t ^ (-p-1)) (Ioi s) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hsp).const_mul CF
    apply hmajor.mono' hFcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hF t (hs.trans ht.le)
  have hmajor : IntegrableOn (fun t : ℝ => CF * t ^ (-p-1)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hsp).const_mul CF
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s), ‖F t‖ ≤ CF*t^(-p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hF t (hs.trans ht.le)
  have hI : (∫ t in Ioi s, t^(-p-1)) = s^(-p)/p := by
    have h1 : -1-p = -p-1 := by ring
    simpa only [h1] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀:=s) (δ:=p) hsp (by linarith))
  have htail : ‖weightedThresholdForcingTail F s‖ ≤
      (CF/p)*s^(-p) := by
    unfold weightedThresholdForcingTail
    rw [norm_neg]
    calc
      ‖∫ t in Ioi s, F t‖ ≤ ∫ t in Ioi s, CF*t^(-p-1) :=
        norm_integral_le_of_norm_le hmajor hpoint
      _ = CF*(s^(-p)/p) := by rw [integral_const_mul,hI]
      _ = (CF/p)*s^(-p) := by ring
  unfold weightedThresholdForcingValue
  rw [norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hsp _)]
  have hpw : s^(p-1)*s^(-p)=s⁻¹ := by
    rw [← Real.rpow_add hsp, show p-1 + -p = -(1:ℝ) by ring,
      Real.rpow_neg_one]
  have hmono : s⁻¹ ≤ s0⁻¹ := inv_anti₀ hs0 hs
  have hc : 0 ≤ CF/p := by positivity
  calc
    s^(p-1)*‖weightedThresholdForcingTail F s‖
        ≤ s^(p-1)*((CF/p)*s^(-p)) :=
          mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hsp.le _)
    _ = (CF/p)*s⁻¹ := by rw [← hpw]; ring
    _ ≤ (CF/p)*s0⁻¹ := mul_le_mul_of_nonneg_left hmono hc

theorem weightedThresholdForcing_continuousOn
    (F : ℝ → ℝ × ℝ) (s0 : ℝ)
    (hFcont : Continuous F)
    (hInt : IntegrableOn F (Ioi s0)) :
    ContinuousOn (weightedThresholdForcingTail F) (Ici s0) := by
  have hc : Continuous
      (fun s => -(∫ t in Ioi s0, F t) + ∫ t in s0..s, F t) :=
    continuous_const.add
      (intervalIntegral.differentiable_integral_of_continuous hFcont).continuous
  apply hc.continuousOn.congr
  intro s hs
  have h := intervalIntegral.integral_interval_add_Ioi hInt
    (hInt.mono_set (Ioi_subset_Ioi hs))
  unfold weightedThresholdForcingTail
  rw [← h]
  abel

def weightedThresholdForcingPath
    (F : ℝ → ℝ × ℝ) (s0 p CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hCF : 0 ≤ CF)
    (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF * t ^ (-p-1)) :
    ThresholdWeightedPath s0 p := by
  have hInt : IntegrableOn F (Ioi s0) := by
    have hmajor : IntegrableOn (fun t : ℝ => CF*t^(-p-1)) (Ioi s0) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hs0).const_mul CF
    apply hmajor.mono' hFcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hF t ht.le
  let v : LateTime s0 → ℝ × ℝ :=
    fun s => weightedThresholdForcingValue F p s
  have hv : Continuous v := by
    have ht := (weightedThresholdForcing_continuousOn F s0 hFcont hInt).domRestrict
    apply continuous_iff_continuousAt.2
    intro s
    have hspos : 0 < (s:ℝ) := hs0.trans_le s.2
    have hpcont : ContinuousAt (fun x : LateTime s0 => (x:ℝ)^(p-1)) s :=
      (Real.continuousAt_rpow_const (s:ℝ) (p-1) (Or.inl hspos.ne')).comp s
        continuousAt_subtype_val
    exact hpcont.smul ht.continuousAt
  exact BoundedContinuousFunction.ofNormedAddCommGroup v hv
    ((CF/p)*s0⁻¹)
    (fun s => weightedThresholdForcing_bound F s0 p CF s hs0 hp hCF hFcont hF s.2)

def weightedCenterForcingTail
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace) (s : ℝ) : ConstrainedCenterSpace :=
  -(∫ t in Ioi s, CE.U s t (F t))

theorem weightedCenterForcing_bound
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace)
    (p N CF s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hN : p+1 < N)
    (hCF : 0 ≤ CF) (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF*t^(-N))
    (hs : s0 ≤ s) :
    ‖(s^p) • weightedCenterForcingTail CE F s‖ ≤
      (CE.boundConst*CF)/(N-1) * s0^(p+1-N) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hmajor : IntegrableOn
      (fun t : ℝ => (CE.boundConst*CF)*t^(-N)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hsp).const_mul _
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖CE.U s t (F t)‖ ≤ (CE.boundConst*CF)*t^(-N) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      ‖CE.U s t (F t)‖ ≤ ‖CE.U s t‖*‖F t‖ := (CE.U s t).le_opNorm _
      _ ≤ CE.boundConst*(CF*t^(-N)) := by
        exact mul_le_mul (CE.bound s t hs ht.le) (hF t (hs.trans ht.le))
          (norm_nonneg _) CE.bound_nonneg
      _ = _ := by ring
  have hI : (∫ t in Ioi s, t^(-N)) = s^(1-N)/(N-1) := by
    have h1 : -1-(N-1)=-N := by ring
    have h2 : -(N-1)=1-N := by ring
    simpa only [h1,h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀:=s) (δ:=N-1) hsp (by linarith))
  have ht : ‖weightedCenterForcingTail CE F s‖ ≤
      (CE.boundConst*CF)/(N-1)*s^(1-N) := by
    unfold weightedCenterForcingTail
    rw [norm_neg]
    calc
      ‖∫ t in Ioi s, CE.U s t (F t)‖
          ≤ ∫ t in Ioi s, (CE.boundConst*CF)*t^(-N) :=
            norm_integral_le_of_norm_le hmajor hpoint
      _ = (CE.boundConst*CF)*(s^(1-N)/(N-1)) := by
        rw [integral_const_mul,hI]
      _ = (CE.boundConst*CF)/(N-1)*s^(1-N) := by ring
  rw [norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hsp _)]
  have hpw : s^p*s^(1-N)=s^(p+1-N) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  have hmono : s^(p+1-N) ≤ s0^(p+1-N) :=
    Real.rpow_le_rpow_of_nonpos hs0 hs (by linarith)
  have hc : 0 ≤ (CE.boundConst*CF)/(N-1) := by positivity
  calc
    s^p*‖weightedCenterForcingTail CE F s‖
        ≤ s^p*((CE.boundConst*CF)/(N-1)*s^(1-N)) :=
          mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hsp.le _)
    _ = (CE.boundConst*CF)/(N-1)*s^(p+1-N) := by rw [← hpw]; ring
    _ ≤ (CE.boundConst*CF)/(N-1)*s0^(p+1-N) :=
      mul_le_mul_of_nonneg_left hmono hc

def weightedCenterForcingPath
    {s0 : ℝ} (CE : StandardConstrainedCenterPropagator s0)
    (F : ℝ → ConstrainedCenterSpace)
    (p N CF : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hN : p+1 < N)
    (hCF : 0 ≤ CF) (hFcont : Continuous F)
    (hF : ∀ t, s0 ≤ t → ‖F t‖ ≤ CF*t^(-N)) :
    CenterWeightedPath s0 p := by
  have hInt : ∀ s, s0 ≤ s →
      IntegrableOn (fun t => CE.U s t (F t)) (Ioi s) := by
    intro s hs
    have hsp : 0 < s := hs0.trans_le hs
    have hmajor : IntegrableOn
        (fun t : ℝ => (CE.boundConst*CF)*t^(-N)) (Ioi s) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hsp).const_mul _
    have hmeas :=
      (CE.orbit_continuous s F hFcont).aestronglyMeasurable.restrict
    apply hmajor.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      ‖CE.U s t (F t)‖ ≤ ‖CE.U s t‖*‖F t‖ := (CE.U s t).le_opNorm _
      _ ≤ CE.boundConst*(CF*t^(-N)) := by
        exact mul_le_mul (CE.bound s t hs ht.le) (hF t (hs.trans ht.le))
          (norm_nonneg _) CE.bound_nonneg
      _ = _ := by ring
  have htail := CE.duhamel_continuous F hFcont hInt
  let v : LateTime s0 → ConstrainedCenterSpace :=
    fun s => ((s:ℝ)^p) • weightedCenterForcingTail CE F s
  have hv : Continuous v := by
    have ht : Continuous
        (fun s : LateTime s0 => weightedCenterForcingTail CE F s) :=
      htail.domRestrict
    apply continuous_iff_continuousAt.2
    intro s
    have hspos : 0 < (s:ℝ) := hs0.trans_le s.2
    have hpcont : ContinuousAt (fun x : LateTime s0 => (x:ℝ)^p) s :=
      (Real.continuousAt_rpow_const (s:ℝ) p (Or.inl hspos.ne')).comp s
        continuousAt_subtype_val
    exact hpcont.smul ht.continuousAt
  exact BoundedContinuousFunction.ofNormedAddCommGroup v hv
    ((CE.boundConst*CF)/(N-1)*s0^(p+1-N))
    (fun s => weightedCenterForcing_bound CE F p N CF s hs0 hp hN hCF hFcont hF s.2)

#print axioms weightedThresholdForcing_bound
#print axioms weightedCenterForcing_bound

end HBL.MainBackward
