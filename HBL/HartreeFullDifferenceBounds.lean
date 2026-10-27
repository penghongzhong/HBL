import HBL.HartreeDensityDifferenceBounds

/-!
# Full physical Hartree remainder differences

Native two-perturbation estimates for the actual seventh-order remainder.
Both local factors and all nonlocal density potentials are retained.
Background L4/L-infinity suffices; background L2 is not assumed.
These order-zero estimates do not construct the constrained PDE evolution.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HBL.RegularRadiation.PhysicalExpansion

def cubicDifferenceConstant (M r : ℝ) : ℝ :=
  3 * M ^ 2 + (6 * M + 3 * r) * r

def fullDifferenceFirstConstant (M r J : ℝ) : ℝ :=
  (nearMass * M ^ 4 + J) * (6 * M + 3 * r) +
    (linearPotentialConstant M J + quadraticPotentialConstant M r * r) *
      cubicDifferenceConstant M r

def fullDifferenceSecondConstant (M r J : ℝ) : ℝ :=
  (linearPotentialConstant M J + densityPotentialDifferenceConstant M r * r) *
    cubicDifferenceConstant M r

private theorem diff_constants_nonneg {M r J : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hJ : 0 ≤ J) :
    0 ≤ fullDifferenceFirstConstant M r J ∧
    0 ≤ fullDifferenceSecondConstant M r J ∧
    0 ≤ densityPotentialDifferenceConstant M r := by
  have hn := regularRadiationKernel_checks.2.1
  unfold fullDifferenceFirstConstant fullDifferenceSecondConstant
    cubicDifferenceConstant linearPotentialConstant quadraticPotentialConstant
    densityPotentialDifferenceConstant densityDifferenceConstant densityQuadraticConstant
  exact ⟨by positivity, by positivity, by positivity⟩

private theorem product_difference (x y u v : ℂ) :
    ‖x * y - u * v‖ ≤ ‖x‖ * ‖y - v‖ + ‖x - u‖ * ‖v‖ := by
  calc
    _ = ‖x * (y - v) + (x - u) * v‖ := by congr 1; ring
    _ ≤ ‖x * (y - v)‖ + ‖(x - u) * v‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul]

private theorem square_norm_difference (z v : ℂ) :
    |‖z‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖z‖ + ‖v‖) * ‖z - v‖ := by
  rw [show ‖z‖ ^ 2 - ‖v‖ ^ 2 = (‖z‖ - ‖v‖) * (‖z‖ + ‖v‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg v))]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (abs_norm_sub_norm_le z v) (add_nonneg (norm_nonneg z) (norm_nonneg v))

private theorem cubic_differences (a : ℝ) (z v : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (ha : |a| ≤ M)
    (hz : ‖z‖ ≤ r) (hv : ‖v‖ ≤ r) :
    ‖cubicLinear a z - cubicLinear a v‖ ≤ 3 * M ^ 2 * ‖z - v‖ ∧
    ‖cubicRemainder a z - cubicRemainder a v‖ ≤
      (6 * M + 3 * r) * r * ‖z - v‖ := by
  have hre : ‖(z.re : ℂ) - (v.re : ℂ)‖ ≤ ‖z - v‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - v)
  have hcoef : ‖(2 : ℂ) * (a : ℂ)‖ ≤ 2 * M := by
    have he : ‖(2 : ℂ) * (a : ℂ)‖ = 2 * |a| := by norm_num [norm_mul]
    rw [he]; linarith
  have hzr : ‖(z.re : ℂ)‖ ≤ r := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (Complex.abs_re_le_norm z).trans hz
  have hc : ‖2 * (a : ℂ) * (z.re : ℂ)‖ ≤ 2 * M * r := by
    rw [norm_mul]
    exact mul_le_mul hcoef hzr (norm_nonneg _) (by positivity)
  have hcd : ‖2 * (a : ℂ) * (z.re : ℂ) - 2 * (a : ℂ) * (v.re : ℂ)‖ ≤
      2 * M * ‖z - v‖ := by
    rw [show 2 * (a : ℂ) * (z.re : ℂ) - 2 * (a : ℂ) * (v.re : ℂ) =
      (2 * (a : ℂ)) * ((z.re : ℂ) - (v.re : ℂ)) by ring, norm_mul]
    exact mul_le_mul hcoef hre (norm_nonneg _) (by positivity)
  have hfirst : ‖(2 * (a : ℂ) * (z.re : ℂ)) * z -
      (2 * (a : ℂ) * (v.re : ℂ)) * v‖ ≤ 4 * M * r * ‖z - v‖ := by
    calc
      _ ≤ ‖2 * (a : ℂ) * (z.re : ℂ)‖ * ‖z - v‖ +
          ‖2 * (a : ℂ) * (z.re : ℂ) - 2 * (a : ℂ) * (v.re : ℂ)‖ * ‖v‖ :=
        product_difference _ _ _ _
      _ ≤ (2 * M * r) * ‖z - v‖ + (2 * M * ‖z - v‖) * r :=
        add_le_add (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
          (mul_le_mul hcd hv (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hs : ‖((‖z‖ ^ 2 : ℝ) : ℂ)‖ ≤ r ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖z‖)] using
      pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hsd : ‖((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖v‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (2 * r) * ‖z - v‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (square_norm_difference z v).trans
      (mul_le_mul_of_nonneg_right (by linarith : ‖z‖ + ‖v‖ ≤ 2 * r) (norm_nonneg _))
  have hav : ‖(a : ℂ) + v‖ ≤ M + r := by
    have ht := norm_add_le (a : ℂ) v
    have hab : ‖(a : ℂ)‖ ≤ M := by simpa using ha
    exact ht.trans (add_le_add hab hv)
  have hsecond : ‖((‖z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z) -
      ((‖v‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + v)‖ ≤
      (2 * M + 3 * r) * r * ‖z - v‖ := by
    have hd : ((a : ℂ) + z) - ((a : ℂ) + v) = z - v := by ring
    calc
      _ ≤ ‖((‖z‖ ^ 2 : ℝ) : ℂ)‖ * ‖((a : ℂ) + z) - ((a : ℂ) + v)‖ +
          ‖((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖v‖ ^ 2 : ℝ) : ℂ)‖ * ‖(a : ℂ) + v‖ :=
        product_difference _ _ _ _
      _ = ‖((‖z‖ ^ 2 : ℝ) : ℂ)‖ * ‖z - v‖ +
          ‖((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖v‖ ^ 2 : ℝ) : ℂ)‖ * ‖(a : ℂ) + v‖ := by rw [hd]
      _ ≤ r ^ 2 * ‖z - v‖ + ((2 * r) * ‖z - v‖) * (M + r) :=
        add_le_add (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
          (mul_le_mul hsd hav (norm_nonneg _) (by positivity))
      _ = _ := by ring
  constructor
  · have hi : cubicLinear a z - cubicLinear a v =
        (a : ℂ) ^ 2 * (2 * ((z.re : ℂ) - (v.re : ℂ)) + (z - v)) := by
      unfold cubicLinear; ring
    have hb : ‖2 * ((z.re : ℂ) - (v.re : ℂ)) + (z - v)‖ ≤ 3 * ‖z - v‖ := by
      have ht := norm_add_le (2 * ((z.re : ℂ) - (v.re : ℂ))) (z - v)
      have hp : ‖2 * ((z.re : ℂ) - (v.re : ℂ))‖ ≤ 2 * ‖z - v‖ := by
        simpa only [norm_mul, Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hre (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    rw [hi, norm_mul, norm_pow]
    have ha2 : ‖(a : ℂ)‖ ^ 2 ≤ M ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg a) ha 2
    calc
      _ ≤ M ^ 2 * (3 * ‖z - v‖) := mul_le_mul ha2 hb (norm_nonneg _) (sq_nonneg M)
      _ = _ := by ring
  · have hi : cubicRemainder a z - cubicRemainder a v =
        ((2 * (a : ℂ) * (z.re : ℂ)) * z - (2 * (a : ℂ) * (v.re : ℂ)) * v) +
        (((‖z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z) - ((‖v‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + v)) := by
      unfold cubicRemainder; ring
    rw [hi]
    calc
      _ ≤ ‖(2 * (a : ℂ) * (z.re : ℂ)) * z - (2 * (a : ℂ) * (v.re : ℂ)) * v‖ +
          ‖((‖z‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + z) - ((‖v‖ ^ 2 : ℝ) : ℂ) * ((a : ℂ) + v)‖ := norm_add_le _ _
      _ ≤ 4 * M * r * ‖z - v‖ + (2 * M + 3 * r) * r * ‖z - v‖ := add_le_add hfirst hsecond
      _ = _ := by ring

private theorem cubic_sum_difference (a : ℝ) (z v : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (ha : |a| ≤ M)
    (hz : ‖z‖ ≤ r) (hv : ‖v‖ ≤ r) :
    ‖(cubicLinear a z + cubicRemainder a z) -
      (cubicLinear a v + cubicRemainder a v)‖ ≤
      cubicDifferenceConstant M r * ‖z - v‖ := by
  have hc := cubic_differences a z v hM hr ha hz hv
  have he : (cubicLinear a z + cubicRemainder a z) -
      (cubicLinear a v + cubicRemainder a v) =
      (cubicLinear a z - cubicLinear a v) + (cubicRemainder a z - cubicRemainder a v) := by ring
  rw [he]
  have ht := (norm_add_le _ _).trans (add_le_add hc.1 hc.2)
  calc
    _ ≤ 3 * M ^ 2 * ‖z - v‖ + (6 * M + 3 * r) * r * ‖z - v‖ := ht
    _ = _ := by unfold cubicDifferenceConstant; ring

private theorem background_bound (w : Space → ℝ)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4))
    {M : ℝ} (hwb : ∀ᵐ y, |w y| ≤ M) (x : Space) :
    ‖potential (quarticDensity (fun y => (w y : ℂ))) x‖ ≤
      nearMass * M ^ 4 + ∫ y : Space, |w y| ^ 4 := by
  have hc : Integrable (fun y : Space => ((|w y| ^ 4 : ℝ) : ℂ)) := hw4.ofReal
  have hi : Integrable (quarticDensity (fun y => (w y : ℂ))) := by
    change Integrable (fun y : Space => ((‖(w y : ℂ)‖ ^ 4 : ℝ) : ℂ))
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc
  have hb : ∀ᵐ y, ‖quarticDensity (fun v => (w v : ℂ)) y‖ ≤ M ^ 4 := by
    filter_upwards [hwb] with y hy
    simpa only [quarticDensity, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w y)) 4)] using pow_le_pow_left₀ (abs_nonneg _) hy 4
  have hp := (potential_bound _ hi (M ^ 4) (by positivity) hb x).2
  have he : (∫ y : Space, ‖quarticDensity (fun v => (w v : ℂ)) y‖) =
      ∫ y : Space, |w y| ^ 4 := by
    apply integral_congr_ae
    filter_upwards with y
    simp only [quarticDensity, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w y)) 4)]
  rwa [he] at hp

private theorem four_products (a b c d e f g h : ℂ)
    {A B C D E F G H : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D)
    (he : ‖e‖ ≤ E) (hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ G) (hh : ‖h‖ ≤ H) :
    ‖a*b + c*d + e*f + g*h‖ ≤ A*B + C*D + E*F + G*H := by
  calc
    _ ≤ (‖a*b + c*d + e*f‖ + ‖g*h‖) := norm_add_le _ _
    _ ≤ (‖a*b + c*d‖ + ‖e*f‖) + ‖g*h‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖a*b‖ + ‖c*d‖) + ‖e*f‖) + ‖g*h‖ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = ((‖a‖*‖b‖ + ‖c‖*‖d‖) + ‖e‖*‖f‖) + ‖g‖*‖h‖ := by simp only [norm_mul]
    _ ≤ _ := add_le_add (add_le_add (add_le_add
      (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))
      (mul_le_mul hc hd (norm_nonneg _) ((norm_nonneg _).trans hc)))
      (mul_le_mul he hf (norm_nonneg _) ((norm_nonneg _).trans he)))
      (mul_le_mul hg hh (norm_nonneg _) ((norm_nonneg _).trans hg))

/-- Complete physical remainder difference, including the nonlocal W^3 term. -/
theorem fullRemainder_pointwise_difference
    (κ : ℝ) (w : Space → ℝ) (h k : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4))
    (hh : MemLp h 2) (hk : MemLp k 2) {M r d : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hkb : ∀ᵐ y, ‖k y‖ ≤ r) (hdb : ∀ᵐ y, ‖h y - k y‖ ≤ d)
    (hEh : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2)
    (hEk : (∫ y : Space, ‖k y‖ ^ 2) ≤ r ^ 2)
    (hEd : (∫ y : Space, ‖h y - k y‖ ^ 2) ≤ d ^ 2) :
    ∀ᵐ x, ‖remainder κ w h x - remainder κ w k x‖ ≤ |κ| *
      (r * fullDifferenceFirstConstant M r (∫ y : Space, |w y| ^ 4) * ‖h x - k x‖ +
        d * fullDifferenceSecondConstant M r (∫ y : Space, |w y| ^ 4) * ‖k x‖ +
        r * d * densityPotentialDifferenceConstant M r * |w x| ^ 3) := by
  filter_upwards [hwb, hhb, hkb] with x hx hhx hkx
  let P0 := potential (quarticDensity (fun y => (w y : ℂ))) x
  let P1h := potential (densityLinear w h) x
  let P1k := potential (densityLinear w k) x
  let PRh := potential (densityRemainder w h) x
  let PRk := potential (densityRemainder w k) x
  let Ch := cubicLinear (w x) (h x) + cubicRemainder (w x) (h x)
  let Ck := cubicLinear (w x) (k x) + cubicRemainder (w x) (k x)
  let C0 := cubicZero (w x)
  have hp0 := background_bound w hw4 hwb x
  have hp1 := densityLinear_potential_small w h hw hw4 hh hM hr hwb hhb hEh x
  have hpR := densityRemainder_small_ball_bound w h hw hh hM hr.le hwb hhb hEh x
  have hp1d := densityLinear_potential_difference w h k hw hw4 hh hk hM hr hd hwb hhb hkb hdb hEd x
  have hpRd := densityRemainder_potential_difference w h k hw hh hk hM hr hd hwb hhb hkb hdb hEh hEk hEd x
  have hcr := (cubic_differences (w x) (h x) (k x) hM hr.le hx hhx hkx).2
  have hCd := cubic_sum_difference (w x) (h x) (k x) hM hr.le hx hhx hkx
  have hCk : ‖Ck‖ ≤ cubicDifferenceConstant M r * ‖k x‖ := by
    simpa only [cubicLinear, cubicRemainder, Complex.zero_re, Complex.ofReal_zero,
      norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, sub_zero] using
      cubic_sum_difference (w x) (k x) 0 hM hr.le hx hkx (by simpa using hr.le)
  have hC0 : ‖C0‖ = |w x| ^ 3 := by simp [C0, cubicZero, norm_pow]
  have hsum : ‖C0 + Ck‖ ≤ |w x| ^ 3 + cubicDifferenceConstant M r * ‖k x‖ := by
    exact (norm_add_le _ _).trans (add_le_add hC0.le hCk)
  have hPs : ‖P1h + PRh‖ ≤
      linearPotentialConstant M (∫ y : Space, |w y| ^ 4) * r + quadraticPotentialConstant M r * r ^ 2 := by
    exact (norm_add_le _ _).trans (add_le_add hp1 hpR)
  have he : remainder κ w h x - remainder κ w k x = (κ : ℂ) *
      (P0 * (cubicRemainder (w x) (h x) - cubicRemainder (w x) (k x)) +
        (P1h + PRh) * (Ch - Ck) + (P1h - P1k) * Ck + (PRh - PRk) * (C0 + Ck)) := by
    dsimp [P0, P1h, P1k, PRh, PRk, Ch, Ck, C0, remainder]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb := four_products P0 (cubicRemainder (w x) (h x) - cubicRemainder (w x) (k x))
    (P1h + PRh) (Ch - Ck) (P1h - P1k) Ck (PRh - PRk) (C0 + Ck)
    hp0 hcr hPs hCd hp1d hCk hpRd hsum
  have ht := mul_le_mul_of_nonneg_left hb (abs_nonneg κ)
  calc
    _ ≤ |κ| *
        ((nearMass * M ^ 4 + ∫ y : Space, |w y| ^ 4) * ((6 * M + 3 * r) * r * ‖h x - k x‖) +
        (linearPotentialConstant M (∫ y : Space, |w y| ^ 4) * r + quadraticPotentialConstant M r * r ^ 2) *
          (cubicDifferenceConstant M r * ‖h x - k x‖) +
        (linearPotentialConstant M (∫ y : Space, |w y| ^ 4) * d) * (cubicDifferenceConstant M r * ‖k x‖) +
        (densityPotentialDifferenceConstant M r * r * d) * (|w x| ^ 3 + cubicDifferenceConstant M r * ‖k x‖)) := ht
    _ = _ := by unfold fullDifferenceFirstConstant fullDifferenceSecondConstant; ring

/-- L2 contraction-scale estimate for the complete physical remainder difference. -/
theorem fullRemainder_L2_difference
    (κ : ℝ) (w : Space → ℝ) (h k : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4))
    (hh : MemLp h 2) (hk : MemLp k 2) {M r d : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hkb : ∀ᵐ y, ‖k y‖ ≤ r) (hdb : ∀ᵐ y, ‖h y - k y‖ ≤ d)
    (hEh : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2)
    (hEk : (∫ y : Space, ‖k y‖ ^ 2) ≤ r ^ 2)
    (hEd : (∫ y : Space, ‖h y - k y‖ ^ 2) ≤ d ^ 2) :
    let J := ∫ y : Space, |w y| ^ 4
    let A := fullDifferenceFirstConstant M r J
    let B := fullDifferenceSecondConstant M r J
    let D := densityPotentialDifferenceConstant M r
    MemLp (fun x => remainder κ w h x - remainder κ w k x) 2 ∧
      (∫ x : Space, ‖remainder κ w h x - remainder κ w k x‖ ^ 2) ≤
        3 * |κ| ^ 2 * (A ^ 2 + B ^ 2 + D ^ 2 * M ^ 2 * J) * r ^ 2 * d ^ 2 := by
  let J := ∫ y : Space, |w y| ^ 4
  let A := fullDifferenceFirstConstant M r J
  let B := fullDifferenceSecondConstant M r J
  let D := densityPotentialDifferenceConstant M r
  have hm := (fullRemainder_L2_bound κ w h hw hw4 hh hM hr hwb hhb hEh).1.sub
    (fullRemainder_L2_bound κ w k hw hw4 hk hM hr hwb hkb hEk).1
  refine ⟨hm, ?_⟩
  have hw6le : ∀ᵐ x, |w x| ^ 6 ≤ M ^ 2 * |w x| ^ 4 := by
    filter_upwards [hwb] with x hx
    calc
      _ = |w x| ^ 2 * |w x| ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx 2) (by positivity)
  have hw6 : Integrable (fun x : Space => |w x| ^ 6) := by
    apply (hw4.const_mul (M ^ 2)).mono' (hw.norm.pow 6)
    filter_upwards [hw6le] with x hx
    simpa only [Pi.pow_apply, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg (w x)) 6)] using hx
  have hW6 := integral_mono_ae hw6 (hw4.const_mul (M ^ 2)) hw6le
  rw [integral_const_mul] at hW6
  have hp := fullRemainder_pointwise_difference κ w h k hw hw4 hh hk hM hr hd hwb hhb hkb hdb hEh hEk hEd
  have hs : ∀ᵐ x, ‖remainder κ w h x - remainder κ w k x‖ ^ 2 ≤
      3 * |κ| ^ 2 * (((r * A) ^ 2 * ‖h x - k x‖ ^ 2 +
        (d * B) ^ 2 * ‖k x‖ ^ 2) + (r * d * D) ^ 2 * |w x| ^ 6) := by
    filter_upwards [hp] with x hx
    have ht := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hthree : (r*A*‖h x-k x‖ + d*B*‖k x‖ + r*d*D*|w x|^3)^2 ≤
        3*((r*A*‖h x-k x‖)^2+(d*B*‖k x‖)^2+(r*d*D*|w x|^3)^2) := by
      nlinarith only [sq_nonneg (r*A*‖h x-k x‖ - d*B*‖k x‖),
        sq_nonneg (r*A*‖h x-k x‖ - r*d*D*|w x|^3),
        sq_nonneg (d*B*‖k x‖ - r*d*D*|w x|^3)]
    calc
      _ ≤ |κ|^2 * (r*A*‖h x-k x‖ + d*B*‖k x‖ + r*d*D*|w x|^3)^2 := by simpa only [mul_pow] using ht
      _ ≤ |κ|^2 * (3*((r*A*‖h x-k x‖)^2+(d*B*‖k x‖)^2+(r*d*D*|w x|^3)^2)) :=
        mul_le_mul_of_nonneg_left hthree (sq_nonneg _)
      _ = _ := by ring
  have i1 := (hh.sub hk).norm.integrable_sq.const_mul ((r*A)^2)
  have i2 := hk.norm.integrable_sq.const_mul ((d*B)^2)
  have i3 := hw6.const_mul ((r*d*D)^2)
  have hI := integral_mono_ae hm.norm.integrable_sq (((i1.add i2).add i3).const_mul (3*|κ|^2)) hs
  simp only [Pi.add_apply, Pi.sub_apply] at hI
  rw [integral_const_mul, integral_add (i1.add i2) i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul] at hI
  calc
    _ ≤ 3*|κ|^2 * (((r*A)^2 * (∫ x : Space, ‖h x-k x‖^2) +
        (d*B)^2 * (∫ x : Space, ‖k x‖^2)) + (r*d*D)^2 * (∫ x : Space, |w x|^6)) := hI
    _ ≤ 3*|κ|^2 * (((r*A)^2*d^2+(d*B)^2*r^2)+(r*d*D)^2*(M^2*J)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hEd (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hEk (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left hW6 (sq_nonneg _))) (by positivity)
    _ = _ := by ring

/-- Essential-supremum contraction-scale estimate for the same full difference. -/
theorem fullRemainder_Linfty_difference
    (κ : ℝ) (w : Space → ℝ) (h k : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4))
    (hh : MemLp h 2) (hk : MemLp k 2) {M r d : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hkb : ∀ᵐ y, ‖k y‖ ≤ r) (hdb : ∀ᵐ y, ‖h y - k y‖ ≤ d)
    (hEh : (∫ y : Space, ‖h y‖ ^ 2) ≤ r ^ 2)
    (hEk : (∫ y : Space, ‖k y‖ ^ 2) ≤ r ^ 2)
    (hEd : (∫ y : Space, ‖h y - k y‖ ^ 2) ≤ d ^ 2) :
    ∀ᵐ x, ‖remainder κ w h x - remainder κ w k x‖ ≤ |κ| *
      (fullDifferenceFirstConstant M r (∫ y : Space, |w y| ^ 4) +
        fullDifferenceSecondConstant M r (∫ y : Space, |w y| ^ 4) +
        densityPotentialDifferenceConstant M r * M ^ 3) * r * d := by
  have hJ : 0 ≤ ∫ y : Space, |w y| ^ 4 := integral_nonneg (fun _ => by positivity)
  have hc := diff_constants_nonneg hM hr.le hJ
  have hp := fullRemainder_pointwise_difference κ w h k hw hw4 hh hk hM hr hd hwb hhb hkb hdb hEh hEk hEd
  filter_upwards [hp, hwb, hkb, hdb] with x hx hwx hkx hdx
  calc
    _ ≤ |κ| * (r*fullDifferenceFirstConstant M r (∫ y : Space, |w y|^4)*‖h x-k x‖ +
        d*fullDifferenceSecondConstant M r (∫ y : Space, |w y|^4)*‖k x‖ +
        r*d*densityPotentialDifferenceConstant M r*|w x|^3) := hx
    _ ≤ |κ| * (r*fullDifferenceFirstConstant M r (∫ y : Space, |w y|^4)*d +
        d*fullDifferenceSecondConstant M r (∫ y : Space, |w y|^4)*r +
        r*d*densityPotentialDifferenceConstant M r*M^3) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg κ)
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hdx (mul_nonneg hr.le hc.1))
        (mul_le_mul_of_nonneg_left hkx (mul_nonneg hd.le hc.2.1)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hwx 3)
          (mul_nonneg (mul_nonneg hr.le hd.le) hc.2.2))
    _ = _ := by ring

end HBL.RegularRadiation.PhysicalExpansion
