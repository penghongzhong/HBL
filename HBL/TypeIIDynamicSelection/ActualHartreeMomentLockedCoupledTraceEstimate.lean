import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedResponseTraceBound
import HBL.KummerOriginBasis.RegularDerivativeBound

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualMomentLockedResponseMomentSum (L c : ℝ) (hL : 0 < L) : ℝ :=
  actualMomentLockedInnerScaleMoment L c hL +
    actualMomentLockedInnerPhaseMoment L c hL

def actualMomentLockedResponseChargeSum (L c : ℝ) : ℝ :=
  |actualMomentLockedInnerScaleCharge L c| +
    |actualMomentLockedInnerPhaseCharge L c|

def actualMomentLockedCoupledTraceBudget
    (L c : ℝ) (hL : 0 < L) (a H C0 : ℝ) : ℝ :=
  C0 * actualMomentLockedResponseMomentSum L c hL / a ^ 2 +
    2 * H * (L ^ 3 * actualMomentLockedResponseChargeSum L c +
      L ^ 2 * actualMomentLockedResponseMomentSum L c hL) / a ^ 4

private theorem origin_outgoing_norm_bound
    {mu theta R : ℝ} (K : OriginKummerPair mu theta R)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) (U DU : ℂ) :
    ‖actualOriginOutgoingTrace K r U DU‖ ≤
      (‖U‖ * ‖originPhysicalSlope K.x K.dx r‖ +
        ‖DU‖ * ‖originPhysicalValue K.x r‖) * r ^ 2 := by
  have hW : originGreenWronskian K r =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4) :=
    origin_physical_wronskian_exact K ⟨hr.le, hrR⟩ hr.ne'
  have hN : ‖Complex.exp (-Complex.I * (r : ℂ) ^ 2 / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hInv : ‖(originGreenWronskian K r)⁻¹‖ = r ^ 2 := by
    rw [hW, norm_inv, norm_mul, norm_pow, norm_inv, hN, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simp
  unfold actualOriginOutgoingTrace
  rw [div_eq_mul_inv, norm_mul, hInv]
  exact mul_le_mul_of_nonneg_right
    ((norm_sub_le _ _).trans_eq (by simp only [norm_mul])) (sq_nonneg r)

private theorem outgoing_scaled_trace_budget
    {mu theta R : ℝ} (K : OriginKummerPair mu theta R)
    (L a H C0 M Q : ℝ) (hL : 0 < L) (ha : 0 < a)
    (_hH : 0 ≤ H) (_hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hrR : L / a ≤ R) (U DU : ℂ)
    (hU : ‖U‖ ≤ Q + M / L) (hDU : ‖DU‖ ≤ a * M / L ^ 2)
    (hk : ‖originPhysicalValue K.x (L / a)‖ ≤ C0)
    (hdk : ‖originPhysicalSlope K.x K.dx (L / a)‖ ≤ 2 * H * (L / a)) :
    ‖actualOriginOutgoingTrace K (L / a) U DU / (a : ℂ)‖ ≤
      C0 * M / a ^ 2 + 2 * H * (L ^ 3 * Q + L ^ 2 * M) / a ^ 4 := by
  have hN := origin_outgoing_norm_bound K (L / a) (div_pos hL ha) hrR U DU
  have h1 := mul_le_mul hU hdk (norm_nonneg _)
    (show 0 ≤ Q + M / L by positivity)
  have h2 := mul_le_mul hDU hk (norm_nonneg _)
    (show 0 ≤ a * M / L ^ 2 by positivity)
  have hFull := hN.trans
    (mul_le_mul_of_nonneg_right (add_le_add h1 h2) (sq_nonneg (L / a)))
  calc
    _ = ‖actualOriginOutgoingTrace K (L / a) U DU‖ / a := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    _ ≤ ((Q + M / L) * (2 * H * (L / a)) +
        (a * M / L ^ 2) * C0) * (L / a) ^ 2 / a :=
      div_le_div_of_nonneg_right hFull ha.le
    _ = _ := by field_simp [hL.ne', ha.ne']; ring

/-- The actual two Fredholm response jets are small in the outgoing flux
after normalization by a. All affine charges and both reconstructed-source
moments remain in the explicit bound; no boundary data are supplied. -/
theorem actual_Hartree_moment_locked_outgoing_trace_bounds
    {mu theta R B : ℝ} (K : OriginKummerPair mu theta R)
    (D G : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hBR : B ≤ R)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (L c a : ℝ) (hL : 2 < L) (ha : 0 < a) (hLB : L / a ≤ B) :
    let hLp : 0 < L := lt_trans (by norm_num : (0 : ℝ) < 2) hL
    let Jb := actualMomentLockedScaleResponseJet L c hLp a (L / a)
    let Jw := actualMomentLockedPhaseResponseJet L c hLp a (L / a)
    let H := (D + 1) * G
    let C0 := 1 + H * B ^ 2
    ‖actualOriginOutgoingTrace K (L / a) Jb.1 Jb.2 / (a : ℂ)‖ ≤
      actualMomentLockedCoupledTraceBudget L c hLp a H C0 ∧
    ‖actualOriginOutgoingTrace K (L / a) Jw.1 Jw.2 / (a : ℂ)‖ ≤
      actualMomentLockedCoupledTraceBudget L c hLp a H C0 := by
  dsimp only
  have hLp : 0 < L := by linarith
  let M := actualMomentLockedResponseMomentSum L c hLp
  let Q := actualMomentLockedResponseChargeSum L c
  let ub := actualMomentLockedPhysicalMinus (actualMomentLockedInnerScaleSource L c)
    (actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp)
  let uw := actualMomentLockedPhysicalPlus (actualMomentLockedInnerPhaseSource L c)
    (actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp)
  have hMom := actual_Hartree_moment_locked_response_moments_nonneg L c hLp
  have hM : 0 ≤ M := add_nonneg hMom.1 hMom.2
  have hQ : 0 ≤ Q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hMb : actualMomentLockedInnerScaleMoment L c hLp ≤ M := by
    dsimp [M, actualMomentLockedResponseMomentSum]; linarith [hMom.2]
  have hMw : actualMomentLockedInnerPhaseMoment L c hLp ≤ M := by
    dsimp [M, actualMomentLockedResponseMomentSum]; linarith [hMom.1]
  have hQb : |actualMomentLockedInnerScaleCharge L c| ≤ Q := by
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hQw : |actualMomentLockedInnerPhaseCharge L c| ≤ Q := by
    exact le_add_of_nonneg_left (abs_nonneg _)
  have ht := actual_Hartree_moment_locked_response_trace_bounds L c hLp L hL
  dsimp only at ht
  have abs_value (u alpha m : ℝ) (hu : |u - alpha| ≤ m / L)
      (hm : m ≤ M) (halpha : |alpha| ≤ Q) : |u| ≤ Q + M / L := by
    have htriangle := abs_add_le (u - alpha) alpha
    rw [sub_add_cancel] at htriangle
    have hmL := div_le_div_of_nonneg_right hm hLp.le
    linarith
  have hub : |ub L| ≤ Q + M / L := abs_value _ _ _ ht.1 hMb hQb
  have huw : |uw L| ≤ Q + M / L := abs_value _ _ _ ht.2.2.1 hMw hQw
  have hdb : |deriv ub L| ≤ M / L ^ 2 :=
    ht.2.1.trans (div_le_div_of_nonneg_right hMb (sq_nonneg L))
  have hdw : |deriv uw L| ≤ M / L ^ 2 :=
    ht.2.2.2.trans (div_le_div_of_nonneg_right hMw (sq_nonneg L))
  have hScale : a * (L / a) = L := by field_simp [ha.ne']
  have hreg := origin_kummer_regular_physical_bound K D G hD hG hBR hcoeff hbound
    (L / a) ⟨div_pos hLp ha, hLB⟩
  have hH : 0 ≤ (D + 1) * G := by positivity
  have hC0 : 0 ≤ 1 + (D + 1) * G * B ^ 2 := by positivity
  have hbU : ‖(actualMomentLockedScaleResponseJet L c hLp a (L / a)).1‖ ≤
      Q + M / L := by
    change ‖Complex.I * (ub (a * (L / a)) : ℂ)‖ ≤ _
    simpa only [hScale, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul] using hub
  have hbDU : ‖(actualMomentLockedScaleResponseJet L c hLp a (L / a)).2‖ ≤
      a * M / L ^ 2 := by
    change ‖(a : ℂ) * Complex.I * ((deriv ub (a * (L / a)) : ℝ) : ℂ)‖ ≤ _
    simp only [hScale, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha, mul_one]
    exact (mul_le_mul_of_nonneg_left hdb ha.le).trans_eq (by ring)
  have hwU : ‖(actualMomentLockedPhaseResponseJet L c hLp a (L / a)).1‖ ≤
      Q + M / L := by
    change ‖(uw (a * (L / a)) : ℂ)‖ ≤ _
    simpa only [hScale, Complex.norm_real, Real.norm_eq_abs] using huw
  have hwDU : ‖(actualMomentLockedPhaseResponseJet L c hLp a (L / a)).2‖ ≤
      a * M / L ^ 2 := by
    change ‖(a : ℂ) * ((deriv uw (a * (L / a)) : ℝ) : ℂ)‖ ≤ _
    simp only [hScale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hdw ha.le).trans_eq (by ring)
  constructor
  · exact outgoing_scaled_trace_budget K L a ((D + 1) * G)
      (1 + (D + 1) * G * B ^ 2) M Q hLp ha hH hC0 hM hQ
      (hLB.trans hBR) _ _ hbU hbDU hreg.1 hreg.2
  · exact outgoing_scaled_trace_budget K L a ((D + 1) * G)
      (1 + (D + 1) * G * B ^ 2) M Q hLp ha hH hC0 hM hQ
      (hLB.trans hBR) _ _ hwU hwDU hreg.1 hreg.2

end HBL.TypeIIDynamicSelection
