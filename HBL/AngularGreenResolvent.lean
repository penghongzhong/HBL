import HBL.AngularHartreeComposition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
The elementary resolvent identity between the Dirichlet Green kernels of
`-∂²` and `-∂² - 1` on `(0, π / 2)`.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace HBL.Modulation.Monopole

theorem hasDerivAt_sin_sub_mul_cos (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin t - t * Real.cos t)
      (x * Real.sin x) x := by
  convert (Real.hasDerivAt_sin x).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1
  · funext t
    rfl
  · simp only [id_eq]
    ring

theorem integral_mul_sin (a b : ℝ) :
    (∫ x : ℝ in a..b, x * Real.sin x) =
      (Real.sin b - b * Real.cos b) -
        (Real.sin a - a * Real.cos a) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_sin_sub_mul_cos x)
    ((continuous_id.mul Real.continuous_sin).intervalIntegrable a b)

theorem hasDerivAt_mul_sin_add_cos (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.sin t + Real.cos t)
      (x * Real.cos x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).add
    (Real.hasDerivAt_cos x) using 1
  · funext t
    rfl
  · simp only [id_eq]
    ring

theorem integral_mul_cos (a b : ℝ) :
    (∫ x : ℝ in a..b, x * Real.cos x) =
      (b * Real.sin b + Real.cos b) -
        (a * Real.sin a + Real.cos a) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mul_sin_add_cos x)
    ((continuous_id.mul Real.continuous_cos).intervalIntegrable a b)

theorem hasDerivAt_sub_mul_sin_primitive (ell x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (t - ell) * Real.cos t - Real.sin t)
      ((ell - x) * Real.sin x) x := by
  convert (((hasDerivAt_id x).sub_const ell).mul
    (Real.hasDerivAt_cos x)).sub (Real.hasDerivAt_sin x) using 1
  · funext t
    rfl
  · simp only [id_eq]
    ring

theorem integral_sub_mul_sin (ell a b : ℝ) :
    (∫ x : ℝ in a..b, (ell - x) * Real.sin x) =
      ((b - ell) * Real.cos b - Real.sin b) -
        ((a - ell) * Real.cos a - Real.sin a) := by
  have hcont : Continuous (fun x : ℝ => (ell - x) * Real.sin x) := by
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_sub_mul_sin_primitive ell x)
    (hcont.intervalIntegrable a b)

theorem hasDerivAt_sub_mul_cos_primitive (ell x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (ell - t) * Real.sin t - Real.cos t)
      ((ell - x) * Real.cos x) x := by
  convert (((hasDerivAt_const x ell).sub (hasDerivAt_id x)).mul
    (Real.hasDerivAt_sin x)).sub (Real.hasDerivAt_cos x) using 1
  · funext t
    rfl
  · simp only [Pi.sub_apply, id_eq]
    ring

theorem integral_sub_mul_cos (ell a b : ℝ) :
    (∫ x : ℝ in a..b, (ell - x) * Real.cos x) =
      ((ell - b) * Real.sin b - Real.cos b) -
        ((ell - a) * Real.sin a - Real.cos a) := by
  have hcont : Continuous (fun x : ℝ => (ell - x) * Real.cos x) := by
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_sub_mul_cos_primitive ell x)
    (hcont.intervalIntegrable a b)

theorem angularZeroGreen_symm (theta phi : ℝ) :
    angularZeroGreen theta phi = angularZeroGreen phi theta := by
  unfold angularZeroGreen
  rw [min_comm theta phi, max_comm theta phi]

theorem angularFreeGreen_symm (theta phi : ℝ) :
    angularFreeGreen theta phi = angularFreeGreen phi theta := by
  unfold angularFreeGreen
  rw [min_comm theta phi, max_comm theta phi]

theorem angularGreen_resolvent_of_le
    {theta phi : ℝ}
    (htheta0 : 0 ≤ theta) (hthetaPhi : theta ≤ phi)
    (hphi : phi ≤ Real.pi / 2) :
    angularZeroGreen theta phi +
        (∫ s : ℝ in 0..Real.pi / 2,
          angularZeroGreen theta s * angularFreeGreen s phi) =
      angularFreeGreen theta phi := by
  let ell : ℝ := Real.pi / 2
  let p : ℝ → ℝ := fun s =>
    angularZeroGreen theta s * angularFreeGreen s phi
  have hthetaEll : theta ≤ ell := hthetaPhi.trans hphi
  have hzeroTheta : 0 ≤ theta := htheta0
  have hphiEll : phi ≤ ell := hphi
  have hpCont : Continuous p := by
    dsimp only [p, angularZeroGreen, angularFreeGreen, ell]
    fun_prop
  have hp0theta : IntervalIntegrable p volume 0 theta :=
    hpCont.intervalIntegrable 0 theta
  have hpthetaPhi : IntervalIntegrable p volume theta phi :=
    hpCont.intervalIntegrable theta phi
  have hp0phi : IntervalIntegrable p volume 0 phi :=
    hpCont.intervalIntegrable 0 phi
  have hpphiEll : IntervalIntegrable p volume phi ell :=
    hpCont.intervalIntegrable phi ell
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    hp0theta hpthetaPhi
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    hp0phi hpphiEll
  have hpiece1 :
      (∫ s : ℝ in 0..theta, p s) =
        ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
          (Real.sin theta - theta * Real.cos theta) := by
    calc
      (∫ s : ℝ in 0..theta, p s) =
          ∫ s : ℝ in 0..theta,
            ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
              (s * Real.sin s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hzeroTheta] at hs
        have hsTheta : s ≤ theta := hs.2
        have hsPhi : s ≤ phi := hsTheta.trans hthetaPhi
        dsimp only [p, angularZeroGreen, angularFreeGreen]
        rw [min_eq_right hsTheta, max_eq_left hsTheta,
          min_eq_left hsPhi, max_eq_right hsPhi]
        dsimp only [ell]
        ring
      _ = ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
          (∫ s : ℝ in 0..theta, s * Real.sin s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
          (Real.sin theta - theta * Real.cos theta) := by
        rw [integral_mul_sin]
        simp
  have hpiece2 :
      (∫ s : ℝ in theta..phi, p s) =
        ((2 / Real.pi) * theta * Real.cos phi) *
          (((phi - ell) * Real.cos phi - Real.sin phi) -
            ((theta - ell) * Real.cos theta - Real.sin theta)) := by
    calc
      (∫ s : ℝ in theta..phi, p s) =
          ∫ s : ℝ in theta..phi,
            ((2 / Real.pi) * theta * Real.cos phi) *
              ((ell - s) * Real.sin s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hthetaPhi] at hs
        have hthetaS : theta ≤ s := hs.1
        have hsPhi : s ≤ phi := hs.2
        dsimp only [p, angularZeroGreen, angularFreeGreen]
        rw [min_eq_left hthetaS, max_eq_right hthetaS,
          min_eq_left hsPhi, max_eq_right hsPhi]
        dsimp only [ell]
        ring
      _ = ((2 / Real.pi) * theta * Real.cos phi) *
          (∫ s : ℝ in theta..phi, (ell - s) * Real.sin s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_sub_mul_sin]
  have hpiece3 :
      (∫ s : ℝ in phi..ell, p s) =
        ((2 / Real.pi) * theta * Real.sin phi) *
          (Real.cos phi - (ell - phi) * Real.sin phi) := by
    calc
      (∫ s : ℝ in phi..ell, p s) =
          ∫ s : ℝ in phi..ell,
            ((2 / Real.pi) * theta * Real.sin phi) *
              ((ell - s) * Real.cos s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hphiEll] at hs
        have hphiS : phi ≤ s := hs.1
        have hthetaS : theta ≤ s := hthetaPhi.trans hphiS
        dsimp only [p, angularZeroGreen, angularFreeGreen]
        rw [min_eq_left hthetaS, max_eq_right hthetaS,
          min_eq_right hphiS, max_eq_left hphiS]
        dsimp only [ell]
        ring
      _ = ((2 / Real.pi) * theta * Real.sin phi) *
          (∫ s : ℝ in phi..ell, (ell - s) * Real.cos s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ((2 / Real.pi) * theta * Real.sin phi) *
          (Real.cos phi - (ell - phi) * Real.sin phi) := by
        rw [integral_sub_mul_cos]
        dsimp only [ell]
        rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have hsum :
      (∫ s : ℝ in 0..ell, p s) =
        (∫ s : ℝ in 0..theta, p s) +
          (∫ s : ℝ in theta..phi, p s) +
            (∫ s : ℝ in phi..ell, p s) := by
    linarith
  dsimp only [p] at hsum
  rw [hpiece1, hpiece2, hpiece3] at hsum
  dsimp only [ell] at hsum ⊢
  rw [hsum]
  unfold angularZeroGreen angularFreeGreen
  rw [min_eq_left hthetaPhi, max_eq_right hthetaPhi]
  field_simp [Real.pi_ne_zero]
  have htrig : Real.cos phi ^ 2 = 1 - Real.sin phi ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq phi]
  ring_nf
  rw [htrig]
  ring

theorem angularGreen_resolvent_of_ge
    {theta phi : ℝ}
    (hphi0 : 0 ≤ phi) (hphiTheta : phi ≤ theta)
    (htheta : theta ≤ Real.pi / 2) :
    angularZeroGreen theta phi +
        (∫ s : ℝ in 0..Real.pi / 2,
          angularZeroGreen theta s * angularFreeGreen s phi) =
      angularFreeGreen theta phi := by
  let ell : ℝ := Real.pi / 2
  let p : ℝ → ℝ := fun s =>
    angularZeroGreen theta s * angularFreeGreen s phi
  have hphiEll : phi ≤ ell := hphiTheta.trans htheta
  have hzeroPhi : 0 ≤ phi := hphi0
  have hthetaEll : theta ≤ ell := htheta
  have hpCont : Continuous p := by
    dsimp only [p, angularZeroGreen, angularFreeGreen, ell]
    fun_prop
  have hp0phi : IntervalIntegrable p volume 0 phi :=
    hpCont.intervalIntegrable 0 phi
  have hpphiTheta : IntervalIntegrable p volume phi theta :=
    hpCont.intervalIntegrable phi theta
  have hp0theta : IntervalIntegrable p volume 0 theta :=
    hpCont.intervalIntegrable 0 theta
  have hpthetaEll : IntervalIntegrable p volume theta ell :=
    hpCont.intervalIntegrable theta ell
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    hp0phi hpphiTheta
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    hp0theta hpthetaEll
  have hpiece1 :
      (∫ s : ℝ in 0..phi, p s) =
        ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
          (Real.sin phi - phi * Real.cos phi) := by
    calc
      (∫ s : ℝ in 0..phi, p s) =
          ∫ s : ℝ in 0..phi,
            ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
              (s * Real.sin s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hzeroPhi] at hs
        have hsPhi : s ≤ phi := hs.2
        have hsTheta : s ≤ theta := hsPhi.trans hphiTheta
        dsimp only [p, angularZeroGreen, angularFreeGreen]
        rw [min_eq_right hsTheta, max_eq_left hsTheta,
          min_eq_left hsPhi, max_eq_right hsPhi]
        dsimp only [ell]
        ring
      _ = ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
          (∫ s : ℝ in 0..phi, s * Real.sin s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ((2 / Real.pi) * (ell - theta) * Real.cos phi) *
          (Real.sin phi - phi * Real.cos phi) := by
        rw [integral_mul_sin]
        simp
  have hpiece2 :
      (∫ s : ℝ in phi..theta, p s) =
        ((2 / Real.pi) * (ell - theta) * Real.sin phi) *
          ((theta * Real.sin theta + Real.cos theta) -
            (phi * Real.sin phi + Real.cos phi)) := by
    calc
      (∫ s : ℝ in phi..theta, p s) =
          ∫ s : ℝ in phi..theta,
            ((2 / Real.pi) * (ell - theta) * Real.sin phi) *
              (s * Real.cos s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hphiTheta] at hs
        have hphiS : phi ≤ s := hs.1
        have hsTheta : s ≤ theta := hs.2
        dsimp only [p, angularZeroGreen, angularFreeGreen]
        rw [min_eq_right hsTheta, max_eq_left hsTheta,
          min_eq_right hphiS, max_eq_left hphiS]
        dsimp only [ell]
        ring
      _ = ((2 / Real.pi) * (ell - theta) * Real.sin phi) *
          (∫ s : ℝ in phi..theta, s * Real.cos s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_mul_cos]
  have hpiece3 :
      (∫ s : ℝ in theta..ell, p s) =
        ((2 / Real.pi) * theta * Real.sin phi) *
          (Real.cos theta - (ell - theta) * Real.sin theta) := by
    calc
      (∫ s : ℝ in theta..ell, p s) =
          ∫ s : ℝ in theta..ell,
            ((2 / Real.pi) * theta * Real.sin phi) *
              ((ell - s) * Real.cos s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hthetaEll] at hs
        have hthetaS : theta ≤ s := hs.1
        have hphiS : phi ≤ s := hphiTheta.trans hthetaS
        dsimp only [p, angularZeroGreen, angularFreeGreen]
        rw [min_eq_left hthetaS, max_eq_right hthetaS,
          min_eq_right hphiS, max_eq_left hphiS]
        dsimp only [ell]
        ring
      _ = ((2 / Real.pi) * theta * Real.sin phi) *
          (∫ s : ℝ in theta..ell, (ell - s) * Real.cos s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ((2 / Real.pi) * theta * Real.sin phi) *
          (Real.cos theta - (ell - theta) * Real.sin theta) := by
        rw [integral_sub_mul_cos]
        dsimp only [ell]
        rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
        ring
  have hsum :
      (∫ s : ℝ in 0..ell, p s) =
        (∫ s : ℝ in 0..phi, p s) +
          (∫ s : ℝ in phi..theta, p s) +
            (∫ s : ℝ in theta..ell, p s) := by
    linarith
  dsimp only [p] at hsum
  rw [hpiece1, hpiece2, hpiece3] at hsum
  dsimp only [ell] at hsum ⊢
  rw [hsum]
  unfold angularZeroGreen angularFreeGreen
  rw [min_eq_right hphiTheta, max_eq_left hphiTheta]
  field_simp [Real.pi_ne_zero]
  have htrig : Real.cos phi ^ 2 = 1 - Real.sin phi ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq phi]
  ring_nf
  rw [htrig]
  ring

theorem angularGreen_resolvent
    {theta phi : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta ≤ Real.pi / 2)
    (hphi0 : 0 ≤ phi) (hphi : phi ≤ Real.pi / 2) :
    angularZeroGreen theta phi +
        (∫ s : ℝ in 0..Real.pi / 2,
          angularZeroGreen theta s * angularFreeGreen s phi) =
      angularFreeGreen theta phi := by
  rcases le_total theta phi with hthetaPhi | hphiTheta
  · exact angularGreen_resolvent_of_le htheta0 hthetaPhi hphi
  · exact angularGreen_resolvent_of_ge hphi0 hphiTheta htheta

theorem weightedZeroGreen_free_resolvent_integral
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    weightedZeroGreen r rho +
        (∫ s in Ioi (0 : ℝ),
          weightedZeroGreen r s * weightedFreeGreen s rho) =
      weightedFreeGreen r rho := by
  have htheta0 : 0 ≤ Real.arctan r := (Real.arctan_pos.mpr hr).le
  have htheta : Real.arctan r ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two r).le
  have hphi0 : 0 ≤ Real.arctan rho := (Real.arctan_pos.mpr hrho).le
  have hphi : Real.arctan rho ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two rho).le
  let c : ℝ := bubble r * bubble rho
  let g : ℝ → ℝ := fun sigma =>
    angularZeroGreen (Real.arctan r) sigma *
      angularFreeGreen sigma (Real.arctan rho)
  have hradial :
      (∫ s in Ioi (0 : ℝ),
          weightedZeroGreen r s * weightedFreeGreen s rho) =
        c * ∫ sigma : ℝ in 0..Real.pi / 2, g sigma := by
    calc
      (∫ s in Ioi (0 : ℝ),
          weightedZeroGreen r s * weightedFreeGreen s rho) =
          ∫ s in Ioi (0 : ℝ),
            c * (bubble s ^ 2 * g (Real.arctan s)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s _
        change weightedZeroGreen r s * weightedFreeGreen s rho =
          c * (bubble s ^ 2 * g (Real.arctan s))
        rw [weightedFreeGreen_eq_angular]
        dsimp only [weightedZeroGreen, c, g]
        ring
      _ = c * ∫ s in Ioi (0 : ℝ),
          bubble s ^ 2 * g (Real.arctan s) := by
        rw [MeasureTheory.integral_const_mul]
      _ = c * ∫ sigma : ℝ in 0..Real.pi / 2, g sigma := by
        rw [intervalIntegral_eq_integral_Ioi_arctan]
  rw [hradial, weightedFreeGreen_eq_angular]
  have hangular := angularGreen_resolvent htheta0 htheta hphi0 hphi
  dsimp only [weightedZeroGreen, c, g]
  calc
    bubble r * bubble rho *
          angularZeroGreen (Real.arctan r) (Real.arctan rho) +
        bubble r * bubble rho *
          (∫ sigma : ℝ in 0..Real.pi / 2,
            angularZeroGreen (Real.arctan r) sigma *
              angularFreeGreen sigma (Real.arctan rho)) =
        bubble r * bubble rho *
          (angularZeroGreen (Real.arctan r) (Real.arctan rho) +
            ∫ sigma : ℝ in 0..Real.pi / 2,
              angularZeroGreen (Real.arctan r) sigma *
                angularFreeGreen sigma (Real.arctan rho)) := by ring
    _ = bubble r * bubble rho *
        angularFreeGreen (Real.arctan r) (Real.arctan rho) := by
      rw [hangular]

end HBL.Modulation.Monopole
