import HBL.HartreeFullRemainderBounds

/-!
# Difference estimates for the actual Hartree density potentials

Native estimates for two physical complex perturbations. No background L2
condition is imposed. The quadratic density difference retains one small
radius factor and one difference factor, including the nonlocal potential.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HBL.RegularRadiation.PhysicalExpansion

def densityDifferenceConstant (M r : ℝ) : ℝ :=
  2 * M ^ 2 + (2 * M + r) * (2 * M + 2 * r)

def densityPotentialDifferenceConstant (M r : ℝ) : ℝ :=
  densityDifferenceConstant M r * (2 * nearMass + 4)

private theorem norm_sq_difference (z v : ℂ) :
    |‖z‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖z‖ + ‖v‖) * ‖z - v‖ := by
  rw [show ‖z‖ ^ 2 - ‖v‖ ^ 2 = (‖z‖ - ‖v‖) * (‖z‖ + ‖v‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg v))]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (abs_norm_sub_norm_le z v) (add_nonneg (norm_nonneg z) (norm_nonneg v))

private theorem density_increment_bound (a : ℝ) (z : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (ha : |a| ≤ M) (hz : ‖z‖ ≤ r) :
    |2 * a * z.re + ‖z‖ ^ 2| ≤ (2 * M + r) * ‖z‖ := by
  calc
    _ ≤ |2 * a * z.re| + |‖z‖ ^ 2| := abs_add_le _ _
    _ = 2 * |a| * |z.re| + ‖z‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg ‖z‖)]
    _ ≤ 2 * M * ‖z‖ + r * ‖z‖ := by
      apply add_le_add
      · exact mul_le_mul (by linarith : 2 * |a| ≤ 2 * M)
          (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity)
      · nlinarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg z)]
    _ = _ := by ring

private theorem density_scalar_difference (a : ℝ) (z v : ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (ha : |a| ≤ M)
    (hz : ‖z‖ ≤ r) (hv : ‖v‖ ≤ r) :
    |(2 * a ^ 2 * ‖z‖ ^ 2 + (2 * a * z.re + ‖z‖ ^ 2) ^ 2) -
      (2 * a ^ 2 * ‖v‖ ^ 2 + (2 * a * v.re + ‖v‖ ^ 2) ^ 2)| ≤
      densityDifferenceConstant M r * (‖z‖ + ‖v‖) * ‖z - v‖ := by
  let u := 2 * a * z.re + ‖z‖ ^ 2
  let t := 2 * a * v.re + ‖v‖ ^ 2
  have hu := density_increment_bound a z hM hr ha hz
  have ht := density_increment_bound a v hM hr ha hv
  have hreal : |z.re - v.re| ≤ ‖z - v‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - v)
  have hd : |u - t| ≤ (2 * M + 2 * r) * ‖z - v‖ := by
    calc
      _ = |2 * a * (z.re - v.re) + (‖z‖ ^ 2 - ‖v‖ ^ 2)| := by dsimp [u, t]; congr 1; ring
      _ ≤ |2 * a * (z.re - v.re)| + |‖z‖ ^ 2 - ‖v‖ ^ 2| := abs_add_le _ _
      _ = 2 * |a| * |z.re - v.re| + |‖z‖ ^ 2 - ‖v‖ ^ 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * M * ‖z - v‖ + (‖z‖ + ‖v‖) * ‖z - v‖ :=
        add_le_add (mul_le_mul (by linarith : 2 * |a| ≤ 2 * M)
          hreal (abs_nonneg _) (by positivity)) (norm_sq_difference z v)
      _ ≤ 2 * M * ‖z - v‖ + (2 * r) * ‖z - v‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      _ = _ := by ring
  have hs : |u + t| ≤ (2 * M + r) * (‖z‖ + ‖v‖) := by
    have hh := (abs_add_le u t).trans (add_le_add hu ht)
    nlinarith only [hh]
  have hsq : |u ^ 2 - t ^ 2| ≤
      ((2 * M + 2 * r) * ‖z - v‖) * ((2 * M + r) * (‖z‖ + ‖v‖)) := by
    rw [show u ^ 2 - t ^ 2 = (u - t) * (u + t) by ring, abs_mul]
    exact mul_le_mul hd hs (abs_nonneg _) (by positivity)
  have ha2 : a ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  calc
    _ = |2 * a ^ 2 * (‖z‖ ^ 2 - ‖v‖ ^ 2) + (u ^ 2 - t ^ 2)| := by
      dsimp [u, t]; congr 1; ring
    _ ≤ |2 * a ^ 2 * (‖z‖ ^ 2 - ‖v‖ ^ 2)| + |u ^ 2 - t ^ 2| := abs_add_le _ _
    _ = (2 * a ^ 2) * |‖z‖ ^ 2 - ‖v‖ ^ 2| + |u ^ 2 - t ^ 2| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * a ^ 2)]
    _ ≤ (2 * M ^ 2) * ((‖z‖ + ‖v‖) * ‖z - v‖) +
        ((2 * M + 2 * r) * ‖z - v‖) * ((2 * M + r) * (‖z‖ + ‖v‖)) :=
      add_le_add (mul_le_mul (by linarith : 2 * a ^ 2 ≤ 2 * M ^ 2)
        (norm_sq_difference z v) (abs_nonneg _) (by positivity)) hsq
    _ = _ := by unfold densityDifferenceConstant; ring

/-- Pointwise difference of the actual quadratic quartic-density remainder. -/
theorem densityRemainder_pointwise_difference
    (w : Space → ℝ) (h k : Space → ℂ) {M r : ℝ}
    (hM : 0 ≤ M) (hr : 0 ≤ r) (x : Space)
    (hw : |w x| ≤ M) (hh : ‖h x‖ ≤ r) (hk : ‖k x‖ ≤ r) :
    ‖densityRemainder w h x - densityRemainder w k x‖ ≤
      densityDifferenceConstant M r * (‖h x‖ + ‖k x‖) * ‖h x - k x‖ := by
  simpa only [densityRemainder, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using density_scalar_difference (w x) (h x) (k x) hM hr hw hh hk

private theorem mixed_product_integral (f g : Space → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hfa : (∫ x : Space, ‖f x‖ ^ 2) ≤ a ^ 2)
    (hgb : (∫ x : Space, ‖g x‖ ^ 2) ≤ b ^ 2) :
    Integrable (fun x : Space => ‖f x‖ * ‖g x‖) ∧
      (∫ x : Space, ‖f x‖ * ‖g x‖) ≤ 2 * a * b := by
  have hp (x : Space) : ‖f x‖ * ‖g x‖ ≤
      (b / a) * ‖f x‖ ^ 2 + (a / b) * ‖g x‖ ^ 2 := by
    have he : (b / a) * ‖f x‖ ^ 2 + (a / b) * ‖g x‖ ^ 2 =
        (b ^ 2 * ‖f x‖ ^ 2 + a ^ 2 * ‖g x‖ ^ 2) / (a * b) := by
      field_simp
    rw [he]
    apply (le_div_iff₀ (mul_pos ha hb)).2
    nlinarith only [sq_nonneg (b * ‖f x‖ - a * ‖g x‖),
      mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hd := (hf.norm.integrable_sq.const_mul (b / a)).add
    (hg.norm.integrable_sq.const_mul (a / b))
  have hi : Integrable (fun x : Space => ‖f x‖ * ‖g x‖) := by
    apply hd.mono' (hf.aestronglyMeasurable.norm.mul hg.aestronglyMeasurable.norm)
    filter_upwards with x
    simpa only [Pi.add_apply, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hp x
  refine ⟨hi, ?_⟩
  have hI := integral_mono_ae hi hd (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at hI
  rw [integral_add (hf.norm.integrable_sq.const_mul (b / a))
    (hg.norm.integrable_sq.const_mul (a / b)), integral_const_mul, integral_const_mul] at hI
  calc
    _ ≤ (b / a) * (∫ x : Space, ‖f x‖ ^ 2) + (a / b) * (∫ x : Space, ‖g x‖ ^ 2) := hI
    _ ≤ (b / a) * a ^ 2 + (a / b) * b ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfa (by positivity))
        (mul_le_mul_of_nonneg_left hgb (by positivity))
    _ = _ := by field_simp; <;> ring

/-- Difference estimate for the nonlocal quadratic density potential. -/
theorem densityRemainder_potential_difference
    (w : Space → ℝ) (h k : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hh : MemLp h 2) (hk : MemLp k 2) {M r d : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ x, |w x| ≤ M) (hhb : ∀ᵐ x, ‖h x‖ ≤ r)
    (hkb : ∀ᵐ x, ‖k x‖ ≤ r) (hdb : ∀ᵐ x, ‖h x - k x‖ ≤ d)
    (hEh : (∫ x : Space, ‖h x‖ ^ 2) ≤ r ^ 2)
    (hEk : (∫ x : Space, ‖k x‖ ^ 2) ≤ r ^ 2)
    (hEd : (∫ x : Space, ‖h x - k x‖ ^ 2) ≤ d ^ 2) (x : Space) :
    ‖potential (densityRemainder w h) x - potential (densityRemainder w k) x‖ ≤
      densityPotentialDifferenceConstant M r * r * d := by
  let D := densityDifferenceConstant M r
  have hD : 0 ≤ D := by dsimp [D, densityDifferenceConstant]; positivity
  have ih := (densityRemainder_source_bound w h hw hh hM hr.le hwb hhb).1
  have ik := (densityRemainder_source_bound w k hw hk hM hr.le hwb hkb).1
  have hpt : ∀ᵐ y, ‖densityRemainder w h y - densityRemainder w k y‖ ≤
      D * (‖h y‖ + ‖k y‖) * ‖h y - k y‖ := by
    filter_upwards [hwb, hhb, hkb] with y hy hhy hky
    exact densityRemainder_pointwise_difference w h k hM hr.le y hy hhy hky
  have hb : ∀ᵐ y, ‖densityRemainder w h y - densityRemainder w k y‖ ≤ D * (2 * r) * d := by
    filter_upwards [hpt, hhb, hkb, hdb] with y hy hhy hky hdy
    exact hy.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith : ‖h y‖ + ‖k y‖ ≤ 2 * r) hD)
      hdy (norm_nonneg _) (by positivity))
  have bh : ∀ᵐ y, ‖densityRemainder w h y‖ ≤ D * r ^ 2 := by
    filter_upwards [hwb, hhb] with y hy hhy
    have ht := densityRemainder_pointwise_difference w h (fun _ => 0) hM hr.le y hy hhy (by simpa using hr.le)
    simp only [densityRemainder, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      Complex.ofReal_zero, sub_zero] at ht
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhy 2) hD
    dsimp [D] at hs
    nlinarith only [ht, hs]
  have bk : ∀ᵐ y, ‖densityRemainder w k y‖ ≤ D * r ^ 2 := by
    filter_upwards [hwb, hkb] with y hy hky
    have ht := densityRemainder_pointwise_difference w k (fun _ => 0) hM hr.le y hy hky (by simpa using hr.le)
    simp only [densityRemainder, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      Complex.ofReal_zero, sub_zero] at ht
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hky 2) hD
    dsimp [D] at hs
    nlinarith only [ht, hs]
  have ph := mixed_product_integral h (fun y => h y - k y) hh (hh.sub hk) hr hd hEh hEd
  have pk := mixed_product_integral k (fun y => h y - k y) hk (hh.sub hk) hr hd hEk hEd
  have hmajor := (ph.1.add pk.1).const_mul D
  have hI : (∫ y : Space, ‖densityRemainder w h y - densityRemainder w k y‖) ≤
      D * (4 * r * d) := by
    have hi := integral_mono_ae (ih.sub ik).norm hmajor (hpt.mono fun y hy => by
      simpa only [Pi.add_apply, mul_add, add_mul, mul_assoc] using hy)
    simp only [Pi.add_apply] at hi
    rw [integral_const_mul, integral_add ph.1 pk.1] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith [ph.2, pk.2]) hD)
  have hP := potential_sub_bound (densityRemainder w h) (densityRemainder w k)
    ih ik (D * r ^ 2) (D * r ^ 2) (D * (2 * r) * d)
    (by positivity) (by positivity) (by positivity) bh bk hb x
  calc
    _ ≤ nearMass * (D * (2 * r) * d) + D * (4 * r * d) :=
      hP.trans (add_le_add le_rfl hI)
    _ = _ := by unfold densityPotentialDifferenceConstant; dsimp [D]; ring

/-- The actual linear density potential respects subtraction and has a
first-order bound in the mixed norm of the difference. -/
theorem densityLinear_potential_difference
    (w : Space → ℝ) (h k : Space → ℂ) (hw : AEStronglyMeasurable w)
    (hw4 : Integrable (fun y : Space => |w y| ^ 4))
    (hh : MemLp h 2) (hk : MemLp k 2) {M r d : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hd : 0 < d)
    (hwb : ∀ᵐ y, |w y| ≤ M) (hhb : ∀ᵐ y, ‖h y‖ ≤ r)
    (hkb : ∀ᵐ y, ‖k y‖ ≤ r) (hdb : ∀ᵐ y, ‖h y - k y‖ ≤ d)
    (hEd : (∫ y : Space, ‖h y - k y‖ ^ 2) ≤ d ^ 2) (x : Space) :
    ‖potential (densityLinear w h) x - potential (densityLinear w k) x‖ ≤
      linearPotentialConstant M (∫ y : Space, |w y| ^ 4) * d := by
  have ih := (densityLinear_source_integrable w h hw hw4 hh hM hr.le hwb hhb).2 x
  have ik := (densityLinear_source_integrable w k hw hw4 hk hM hr.le hwb hkb).2 x
  have he : potential (densityLinear w (fun y => h y - k y)) x =
      potential (densityLinear w h) x - potential (densityLinear w k) x := by
    unfold potential
    rw [← integral_sub ih ik]
    apply integral_congr_ae
    filter_upwards with y
    simp only [densityLinear, Complex.sub_re]
    push_cast
    ring
  rw [← he]
  exact densityLinear_potential_small w (fun y => h y - k y) hw hw4
    (hh.sub hk) hM hd hwb hdb hEd x

end HBL.RegularRadiation.PhysicalExpansion
