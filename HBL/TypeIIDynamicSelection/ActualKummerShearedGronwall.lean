import HBL.TypeIIDynamicSelection.ActualKummerSameSourceJetTransfer
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
The large imaginary radial drift is removed BEFORE any norm estimate.
The bound below depends only on the frozen zero-order coefficient b,
not on the radius or on norms of an arbitrarily normalized basis.
The only differential assumptions are the actual homogeneous Kummer ODE.
A separate file specializes the theorem to the already proved same-source
physical transfer difference. No remote compatibility or Type-II law is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology
namespace HBL.TypeIIDynamicSelection

 def actualKummerShearCoefficient (b : ℂ) : ℂ := 2 * Complex.I * b
 def actualKummerShearPhase (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (r : ℂ) ^ 2 / 4)
 def actualKummerShearedState (b : ℂ) (h dh : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  (h r, actualKummerShearPhase r *
    ((r : ℂ) * dh r - actualKummerShearCoefficient b * h r))
 def actualKummerShearedDerivative (b : ℂ) (h dh : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  (dh r, (-(1 + actualKummerShearCoefficient b) *
      (actualKummerShearedState b h dh r).2 -
    actualKummerShearCoefficient b * (1 + actualKummerShearCoefficient b) *
      actualKummerShearPhase r * h r) / (r : ℂ))
 def actualKummerScaledJet (h dh : ℝ → ℂ) (r : ℝ) : ℝ :=
  max ‖h r‖ (r * ‖dh r‖)
 def actualKummerUniformTransferConstant (b : ℂ) : ℝ :=
  (1 + ‖actualKummerShearCoefficient b‖) ^ 2 *
    Real.exp ((1 + ‖actualKummerShearCoefficient b‖) ^ 2)

 theorem actual_Kummer_shear_phase_norm (r : ℝ) :
    ‖actualKummerShearPhase r‖ = 1 := by
  rw [actualKummerShearPhase, Complex.norm_exp]
  have he : (Complex.I * (r : ℂ) ^ 2 / 4).re = 0 := by
    simp [Complex.div_re, Complex.mul_re]
  rw [he, Real.exp_zero]

 theorem actual_Kummer_shear_phase_hasDerivAt (r : ℝ) :
    HasDerivAt actualKummerShearPhase
      (Complex.I * (r : ℂ) / 2 * actualKummerShearPhase r) r := by
  have hi : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r := by
    simpa only [Complex.ofReal_one] using (hasDerivAt_id r).ofReal_comp
  have he := (((hi.pow 2).const_mul Complex.I).div_const 4).cexp
  convert he using 1
  dsimp [actualKummerShearPhase]
  ring

/-- Exact differentiation: the O(r) imaginary coefficient cancels. -/
 theorem actual_Kummer_sheared_system_hasDerivAt
    (b : ℂ) (h dh : ℝ → ℂ) (r : ℝ) (hr : 0 < r)
    (hh : HasDerivAt h (dh r) r)
    (hdh : HasDerivAt dh
      (-((2 / (r : ℂ) + Complex.I * (r : ℂ) / 2) * dh r + b * h r)) r) :
    HasDerivAt (actualKummerShearedState b h dh)
      (actualKummerShearedDerivative b h dh r) r := by
  have hi : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r := by
    simpa only [Complex.ofReal_one] using (hasDerivAt_id r).ofReal_comp
  have hw := (hi.mul hdh).sub (hh.const_mul (actualKummerShearCoefficient b))
  have hv := (actual_Kummer_shear_phase_hasDerivAt r).mul hw
  have heq :
      (Complex.I * (r : ℂ) / 2 * actualKummerShearPhase r) *
          ((r : ℂ) * dh r - actualKummerShearCoefficient b * h r) +
        actualKummerShearPhase r *
          (1 * dh r + (r : ℂ) *
            (-((2 / (r : ℂ) + Complex.I * (r : ℂ) / 2) * dh r + b * h r)) -
            actualKummerShearCoefficient b * dh r) =
      (actualKummerShearedDerivative b h dh r).2 := by
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    dsimp [actualKummerShearedDerivative, actualKummerShearedState,
      actualKummerShearCoefficient]
    field_simp [hn]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hv' := hv.congr_deriv heq
  exact hh.prodMk hv'

private theorem shear_norm_comparison
    (a P u du : ℂ) (r : ℝ) (hr : 0 ≤ r) (hP : ‖P‖ = 1) :
    ‖(u, P * ((r : ℂ) * du - a * u))‖ ≤
        (1 + ‖a‖) * max ‖u‖ (r * ‖du‖) ∧
    max ‖u‖ (r * ‖du‖) ≤
        (1 + ‖a‖) * ‖(u, P * ((r : ℂ) * du - a * u))‖ := by
  let w : ℂ := (r : ℂ) * du - a * u
  have hw : ‖P * w‖ = ‖w‖ := by rw [norm_mul, hP, one_mul]
  have hR : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  let H : ℝ := max ‖u‖ (r * ‖du‖)
  let N : ℝ := max ‖u‖ ‖w‖
  have huH : ‖u‖ ≤ H := le_max_left _ _
  have hdH : r * ‖du‖ ≤ H := le_max_right _ _
  have huN : ‖u‖ ≤ N := le_max_left _ _
  have hwN : ‖w‖ ≤ N := le_max_right _ _
  have hH : 0 ≤ H := (norm_nonneg u).trans huH
  have hN : 0 ≤ N := (norm_nonneg u).trans huN
  have hHN : N ≤ (1 + ‖a‖) * H := by
    apply max_le
    · nlinarith [mul_nonneg (norm_nonneg a) hH]
    · calc
        ‖w‖ ≤ ‖(r : ℂ) * du‖ + ‖a * u‖ := norm_sub_le _ _
        _ = r * ‖du‖ + ‖a‖ * ‖u‖ := by rw [norm_mul, norm_mul, hR]
        _ ≤ H + ‖a‖ * H := _root_.add_le_add hdH
          (mul_le_mul_of_nonneg_left huH (norm_nonneg _))
        _ = _ := by ring
  have hNH : H ≤ (1 + ‖a‖) * N := by
    apply max_le
    · nlinarith [mul_nonneg (norm_nonneg a) hN]
    · have hid : (r : ℂ) * du = a * u + w := by dsimp [w]; ring
      calc
        r * ‖du‖ = ‖(r : ℂ) * du‖ := by rw [norm_mul, hR]
        _ ≤ ‖a * u‖ + ‖w‖ := by rw [hid]; exact norm_add_le _ _
        _ = ‖a‖ * ‖u‖ + ‖w‖ := by rw [norm_mul]
        _ ≤ ‖a‖ * N + N := _root_.add_le_add
          (mul_le_mul_of_nonneg_left huN (norm_nonneg _)) hwN
        _ = _ := by ring
  simpa only [Prod.norm_def, hw, H, N, w] using And.intro hHN hNH

/-- The sheared system has O(1/r) norm, with no hidden annulus constant. -/
 theorem actual_Kummer_sheared_derivative_norm_le
    (b : ℂ) (h dh : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    ‖actualKummerShearedDerivative b h dh r‖ ≤
      ((1 + ‖actualKummerShearCoefficient b‖) ^ 2 / r) *
        ‖actualKummerShearedState b h dh r‖ := by
  let a := actualKummerShearCoefficient b
  let P := actualKummerShearPhase r
  let w : ℂ := (r : ℂ) * dh r - a * h r
  let v : ℂ := P * w
  let N : ℝ := ‖actualKummerShearedState b h dh r‖
  let L : ℝ := 1 + ‖a‖
  have hP : ‖P‖ = 1 := actual_Kummer_shear_phase_norm r
  have hR : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hv : ‖v‖ = ‖w‖ := by dsimp [v]; rw [norm_mul, hP, one_mul]
  have huN : ‖h r‖ ≤ N := le_max_left _ _
  have hvN : ‖v‖ ≤ N := le_max_right _ _
  have hwN : ‖w‖ ≤ N := by rwa [hv] at hvN
  have hN : 0 ≤ N := norm_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hL2 : L ≤ L ^ 2 := by dsimp [L]; nlinarith [norm_nonneg a, sq_nonneg ‖a‖]
  have ha1 : ‖(1 : ℂ) + a‖ ≤ L := by
    simpa only [norm_one, L] using norm_add_le (1 : ℂ) a
  have hdBound : r * ‖dh r‖ ≤ L * N := by
    have hid : (r : ℂ) * dh r = a * h r + w := by dsimp [w]; ring
    calc
      r * ‖dh r‖ = ‖(r : ℂ) * dh r‖ := by rw [norm_mul, hR]
      _ ≤ ‖a * h r‖ + ‖w‖ := by rw [hid]; exact norm_add_le _ _
      _ = ‖a‖ * ‖h r‖ + ‖w‖ := by rw [norm_mul]
      _ ≤ ‖a‖ * N + N := _root_.add_le_add
        (mul_le_mul_of_nonneg_left huN (norm_nonneg _)) hwN
      _ = L * N := by dsimp [L]; ring
  have hFirst : ‖dh r‖ ≤ (L ^ 2 / r) * N := by
    have h1 : ‖dh r‖ ≤ (L * N) / r :=
      (le_div_iff₀ hr).2 (by simpa only [mul_comm] using hdBound)
    calc
      _ ≤ (L * N) / r := h1
      _ ≤ (L ^ 2 * N) / r := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL2 hN) hr.le
      _ = _ := by ring
  have hNumer : ‖-(1 + a) * v - a * (1 + a) * P * h r‖ ≤ L ^ 2 * N := by
    calc
      _ ≤ ‖-(1 + a) * v‖ + ‖a * (1 + a) * P * h r‖ := norm_sub_le _ _
      _ = ‖1 + a‖ * ‖v‖ + ‖a‖ * ‖1 + a‖ * ‖h r‖ := by
        simp only [norm_mul, norm_neg, hP, mul_one]
      _ ≤ L * N + ‖a‖ * L * N := by
        gcongr
      _ = L ^ 2 * N := by dsimp [L]; ring
  change max ‖dh r‖
    ‖(-(1 + a) * v - a * (1 + a) * P * h r) / (r : ℂ)‖ ≤ (L ^ 2 / r) * N
  apply max_le hFirst
  rw [norm_div, hR]
  exact (div_le_div_of_nonneg_right hNumer hr.le).trans_eq (by ring)

/-- Radius-uniform propagation of the actual homogeneous Kummer equation
on a dyadic positive annulus. The coefficient is explicit and independent
of r0,r1. No uniform fundamental-pair bound is assumed. -/
 theorem actual_Kummer_homogeneous_dyadic_uniform_bound
    (b : ℂ) (h dh : ℝ → ℂ) (r0 r1 : ℝ)
    (hr0 : 0 < r0) (h01 : r0 ≤ r1) (hRatio : r1 ≤ 2 * r0)
    (hh : ∀ r ∈ Icc r0 r1, HasDerivAt h (dh r) r)
    (hdh : ∀ r ∈ Icc r0 r1, HasDerivAt dh
      (-((2 / (r : ℂ) + Complex.I * (r : ℂ) / 2) * dh r + b * h r)) r) :
    actualKummerScaledJet h dh r1 ≤
      actualKummerUniformTransferConstant b * actualKummerScaledJet h dh r0 := by
  let X := actualKummerShearedState b h dh
  let DX := actualKummerShearedDerivative b h dh
  let L : ℝ := 1 + ‖actualKummerShearCoefficient b‖
  let K : ℝ := L ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := sq_nonneg _
  have hDer (r : ℝ) (hr : r ∈ Icc r0 r1) : HasDerivAt X (DX r) r :=
    actual_Kummer_sheared_system_hasDerivAt b h dh r (hr0.trans_le hr.1)
      (hh r hr) (hdh r hr)
  have hCont : ContinuousOn X (Icc r0 r1) :=
    fun r hr => (hDer r hr).continuousAt.continuousWithinAt
  have hBound (r : ℝ) (hr : r ∈ Ico r0 r1) :
      ‖DX r‖ ≤ (K / r0) * ‖X r‖ + 0 := by
    have hpos : 0 < r := hr0.trans_le hr.1
    have hsmall : K / r ≤ K / r0 := by gcongr
    have h := actual_Kummer_sheared_derivative_norm_le b h dh r hpos
    exact (h.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))).trans_eq
      (by rw [add_zero])
  have hGrowth := norm_le_gronwallBound_of_norm_deriv_right_le hCont
    (fun r hr => (hDer r (Ico_subset_Icc_self hr)).hasDerivWithinAt)
    (le_refl ‖X r0‖) hBound r1 (show r1 ∈ Icc r0 r1 from ⟨h01, le_rfl⟩)
  rw [gronwallBound_ε0] at hGrowth
  have hExponent : (K / r0) * (r1 - r0) ≤ K := by
    have hfrac : (r1 - r0) / r0 ≤ 1 := (div_le_iff₀ hr0).2 (by linarith)
    calc
      (K / r0) * (r1 - r0) = K * ((r1 - r0) / r0) := by ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hfrac hK
      _ = K := mul_one _
  have hN : ‖X r1‖ ≤ Real.exp K * ‖X r0‖ := by
    exact (hGrowth.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hExponent) (norm_nonneg _))).trans_eq (by ring)
  have hC0 := shear_norm_comparison (actualKummerShearCoefficient b)
    (actualKummerShearPhase r0) (h r0) (dh r0) r0 hr0.le
    (actual_Kummer_shear_phase_norm r0)
  have hC1 := shear_norm_comparison (actualKummerShearCoefficient b)
    (actualKummerShearPhase r1) (h r1) (dh r1) r1 (hr0.le.trans h01)
    (actual_Kummer_shear_phase_norm r1)
  calc
    actualKummerScaledJet h dh r1 ≤ L * ‖X r1‖ := hC1.2
    _ ≤ L * (Real.exp K * ‖X r0‖) := mul_le_mul_of_nonneg_left hN hL
    _ ≤ L * (Real.exp K * (L * actualKummerScaledJet h dh r0)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hC0.1 (Real.exp_pos K).le) hL
    _ = actualKummerUniformTransferConstant b * actualKummerScaledJet h dh r0 := by
      dsimp [actualKummerUniformTransferConstant, K, L]
      ring

end HBL.TypeIIDynamicSelection
