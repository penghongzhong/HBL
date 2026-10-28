import HBL.HartreeGradientDifference

/-!
# Complete first-order differences of the physical Hartree source

Combine the two actual potential difference estimates with the full local
cubic differential. Neither background is required to be L2; only their
difference is L2. The final statement gives explicit squared L2 Lipschitz
bounds for the entire seventh-order source and its entire spatial differential.
The weak derivative identity is proved for the source difference as well.

This closes a first-order source estimate, not the Taylor remainder's extra
small-ball factor, higher Sobolev estimates, or the constrained evolution.
No additional manuscript environment or main theorem acceptance is asserted.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Topology
namespace HBL.RegularRadiation.FullFirstOrderDifference
open SpatialCompletion QuarticGradient LocalCutoff FirstOrderSource GradientDifference

private def c (a : ℂ) : ℂ := ((‖a‖ ^ 2 : ℝ) : ℂ) * a
private def dc (a h : ℂ) : ℂ :=
  ((‖a‖ ^ 2 : ℝ) : ℂ) * h + ((2 * inner ℝ a h : ℝ) : ℂ) * a

private theorem c_norm (a : ℂ) : ‖c a‖ = ‖a‖ ^ 3 := by
  rw [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  ring

private theorem inner_factor (a h : ℂ) :
    ‖((2 * inner ℝ a h : ℝ) : ℂ)‖ ≤ 2 * ‖a‖ * ‖h‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hi : |inner ℝ a h| ≤ ‖a‖ * ‖h‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) a h
  exact (mul_le_mul_of_nonneg_left hi (by norm_num)).trans_eq (by ring)

private theorem dc_norm (a h : ℂ) : ‖dc a h‖ ≤ 3 * ‖a‖ ^ 2 * ‖h‖ := by
  unfold dc
  calc
    _ ≤ ‖((‖a‖ ^ 2 : ℝ) : ℂ) * h‖ + ‖((2 * inner ℝ a h : ℝ) : ℂ) * a‖ :=
      norm_add_le _ _
    _ = ‖a‖ ^ 2 * ‖h‖ + ‖((2 * inner ℝ a h : ℝ) : ℂ)‖ * ‖a‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ ‖a‖ ^ 2 * ‖h‖ + (2 * ‖a‖ * ‖h‖) * ‖a‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (inner_factor a h) (norm_nonneg _))
    _ = _ := by ring

private theorem square_difference (a b : ℂ) {M : ℝ}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * M * ‖a - b‖ := by
  rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b) (by positivity)
    _ ≤ ‖a - b‖ * (2 * M) := by gcongr; linarith
    _ = _ := by ring

private theorem c_difference (a b : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖c a - c b‖ ≤ 3 * M ^ 2 * ‖a - b‖ := by
  have he : c a - c b = ((‖a‖ ^ 2 : ℝ) : ℂ) * (a - b) +
      ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * b := by
    unfold c
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖((‖a‖ ^ 2 : ℝ) : ℂ) * (a - b)‖ +
        ‖((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * b‖ := norm_add_le _ _
    _ = ‖a‖ ^ 2 * ‖a - b‖ + |‖a‖ ^ 2 - ‖b‖ ^ 2| * ‖b‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    _ ≤ M ^ 2 * ‖a - b‖ + (2 * M * ‖a - b‖) * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ha 2) (norm_nonneg _))
        (mul_le_mul (square_difference a b ha hb) hb (norm_nonneg _) (by positivity))
    _ = _ := by ring

private theorem dc_difference (a b h k : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖dc a h - dc b k‖ ≤ 3 * M ^ 2 * ‖h - k‖ + 6 * M * ‖a - b‖ * ‖k‖ := by
  have he : dc a h - dc b k =
      ((dc a (h - k) + ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * k) +
        ((2 * inner ℝ (a - b) k : ℝ) : ℂ) * a) +
        ((2 * inner ℝ b k : ℝ) : ℂ) * (a - b) := by
    unfold dc
    simp only [inner_sub_right, inner_sub_left]
    push_cast
    ring
  have h1 : ‖dc a (h - k)‖ ≤ 3 * M ^ 2 * ‖h - k‖ := by
    apply (dc_norm a (h - k)).trans
    gcongr
  have h2 : ‖((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * k‖ ≤
      2 * M * ‖a - b‖ * ‖k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (square_difference a b ha hb) (norm_nonneg _)
  have h3 : ‖((2 * inner ℝ (a - b) k : ℝ) : ℂ) * a‖ ≤
      2 * M * ‖a - b‖ * ‖k‖ := by
    rw [norm_mul]
    exact (mul_le_mul (inner_factor (a - b) k) ha (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h4 : ‖((2 * inner ℝ b k : ℝ) : ℂ) * (a - b)‖ ≤
      2 * M * ‖a - b‖ * ‖k‖ := by
    rw [norm_mul]
    calc
      _ ≤ (2 * ‖b‖ * ‖k‖) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (inner_factor b k) (norm_nonneg _)
      _ ≤ (2 * M * ‖k‖) * ‖a - b‖ := by gcongr
      _ = _ := by ring
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans
    ((add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring))

private theorem four_square (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Complete source and complete spatial differential differences, with weak
identification and explicit uniform-on-bounded-sets squared L2 bounds.
Only the increment, not either background field, is required to be L2. -/
theorem hartree_first_order_difference_noncompact
    (κ : ℝ) (f g : Space → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf4 : Integrable (fun x : Space => ‖f x‖ ^ 4))
    (hg4 : Integrable (fun x : Space => ‖g x‖ ^ 4))
    (hDf : MemLp (fderiv ℝ f) 2) (hDg : MemLp (fderiv ℝ g) 2)
    (hfg : MemLp (fun x => f x - g x) 2)
    {M L j Q d : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hj : 0 < j) (hQ : 0 < Q) (hd : 0 < d)
    (hfb : ∀ᵐ x, ‖f x‖ ≤ M) (hgb : ∀ᵐ x, ‖g x‖ ≤ M)
    (hDfb : ∀ᵐ x, ‖fderiv ℝ f x‖ ≤ L) (hDgb : ∀ᵐ x, ‖fderiv ℝ g x‖ ≤ L)
    (hJf : (∫ x : Space, ‖f x‖ ^ 4) ≤ j ^ 2)
    (hJg : (∫ x : Space, ‖g x‖ ^ 4) ≤ j ^ 2)
    (hEg : (∫ x : Space, ‖fderiv ℝ g x‖ ^ 2) ≤ Q ^ 2)
    (hδ : ∀ᵐ x, ‖f x - g x‖ ≤ d)
    (hDδ : ∀ᵐ x, ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ d)
    (hδ2 : (∫ x : Space, ‖f x - g x‖ ^ 2) ≤ d ^ 2)
    (hDδ2 : (∫ x : Space, ‖fderiv ℝ f x - fderiv ℝ g x‖ ^ 2) ≤ d ^ 2) :
    let A := nearMass * M ^ 4 + j ^ 2
    let B := 4 * nearMass * M ^ 3 * L + 2 * (M ^ 2 * j ^ 2 + Q ^ 2)
    let CP := 4 * nearMass * M ^ 3 + 8 * M * j
    let CG := nearMass * (4 * M ^ 3 + 16 * M ^ 2 * L) + 8 * (M + 1) * j + 32 * j * Q
    let a := 3 * A * M ^ 2
    let b := 6 * A * M * L + 3 * B * M ^ 2
    let e := 3 * CP * M ^ 2
    let U := fun x => hartreeNonlinearity κ f x - hartreeNonlinearity κ g x
    let V := fun x => fderiv ℝ (hartreeNonlinearity κ f) x - fderiv ℝ (hartreeNonlinearity κ g) x
    MemLp U 2 ∧ MemLp V 2 ∧
    (∫ x : Space, ‖U x‖ ^ 2) ≤ 2 * κ ^ 2 * (a ^ 2 + CP ^ 2 * M ^ 2 * j ^ 2) * d ^ 2 ∧
    (∫ x : Space, ‖V x‖ ^ 2) ≤
      4 * κ ^ 2 * (a ^ 2 + b ^ 2 + e ^ 2 * Q ^ 2 + CG ^ 2 * M ^ 2 * j ^ 2) * d ^ 2 ∧
    ∀ φ : Space → ℂ, HasCompactSupport φ → ContDiff ℝ 1 φ → ∀ v : Space,
      Integrable (fun x : Space => U x * fderiv ℝ φ x v) ∧
      Integrable (fun x : Space => V x v * φ x) ∧
      (∫ x : Space, U x * fderiv ℝ φ x v) = -(∫ x : Space, V x v * φ x) := by
  dsimp only
  let A := nearMass * M ^ 4 + j ^ 2
  let B := 4 * nearMass * M ^ 3 * L + 2 * (M ^ 2 * j ^ 2 + Q ^ 2)
  let CP := 4 * nearMass * M ^ 3 + 8 * M * j
  let CG := nearMass * (4 * M ^ 3 + 16 * M ^ 2 * L) + 8 * (M + 1) * j + 32 * j * Q
  let a := 3 * A * M ^ 2
  let b := 6 * A * M * L + 3 * B * M ^ 2
  let e := 3 * CP * M ^ 2
  let U := fun x => hartreeNonlinearity κ f x - hartreeNonlinearity κ g x
  let V := fun x => fderiv ℝ (hartreeNonlinearity κ f) x - fderiv ℝ (hartreeNonlinearity κ g) x
  have hn := regularRadiationKernel_checks.2.1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCP : 0 ≤ CP := by dsimp [CP]; positivity
  have hCG : 0 ≤ CG := by dsimp [CG]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hpot := quartic_potential_first_order_difference f g hf hg hf4 hg4 hDf hDg hfg
    hM hL hj hQ hd hfb hgb hDfb hDgb hJf hJg hEg hδ hDδ hδ2 hDδ2
  have hF := hartree_differential_noncompact κ f hf hf4 hDf M L hM hL hfb hDfb
  have hG := hartree_differential_noncompact κ g hg hg4 hDg M L hM hL hgb hDgb
  have hsF := hartree_first_order_source_noncompact κ f hf hf4 hDf M L hM hL hfb hDfb
  have hsG := hartree_first_order_source_noncompact κ g hg hg4 hDg M L hM hL hgb hDgb
  have hU : MemLp U 2 := hsF.1.sub hsG.1
  have hV : MemLp V 2 := hsF.2.1.sub hsG.2.1
  have hPf (x : Space) : ‖potential (quarticDensity f) x‖ ≤ A := by
    have hbr : ∀ᵐ y, ‖quarticDensity f y‖ ≤ M ^ 4 := by
      filter_upwards [hfb] with y hy
      simpa only [quarticDensity, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] using
        pow_le_pow_left₀ (norm_nonneg _) hy 4
    have ht := (potential_bound (quarticDensity f) hf4.ofReal (M ^ 4) (by positivity) hbr x).2
    simp only [quarticDensity, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)] at ht
    exact ht.trans (add_le_add le_rfl hJf)
  have hGg (x : Space) : ‖gradientPotential (fderiv ℝ (quarticDensity g)) x‖ ≤ B := by
    apply (quarticDensity_gradient_potential_bound g hg hg4 hDg M L hM hL hgb hDgb x).2.trans
    dsimp [B]
    nlinarith only [mul_le_mul_of_nonneg_left hJg (sq_nonneg M), hEg]
  have hGdiff (x : Space) :
      ‖gradientPotential (fderiv ℝ (quarticDensity f)) x -
        gradientPotential (fderiv ℝ (quarticDensity g)) x‖ ≤ CG * d := by
    have ht := (hpot x).2
    rw [(quarticPotential_hasFDerivAt_noncompact f hf hf4 hDf M L hM hL hfb hDfb x).fderiv,
      (quarticPotential_hasFDerivAt_noncompact g hg hg4 hDg M L hM hL hgb hDgb x).fderiv] at ht
    exact ht
  have huv : ∀ᵐ x, ‖U x‖ ≤ |κ| * (a * ‖f x - g x‖ + CP * d * ‖g x‖ ^ 3) := by
    filter_upwards [hfb, hgb] with x hfx hgx
    have heq : U x = (κ : ℂ) *
        (potential (quarticDensity f) x * (c (f x) - c (g x)) +
          (potential (quarticDensity f) x - potential (quarticDensity g) x) * c (g x)) := by
      dsimp [U, hartreeNonlinearity, c]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg κ)
    calc
      _ ≤ ‖potential (quarticDensity f) x * (c (f x) - c (g x))‖ +
          ‖(potential (quarticDensity f) x - potential (quarticDensity g) x) * c (g x)‖ := norm_add_le _ _
      _ = ‖potential (quarticDensity f) x‖ * ‖c (f x) - c (g x)‖ +
          ‖potential (quarticDensity f) x - potential (quarticDensity g) x‖ * ‖g x‖ ^ 3 := by
        rw [norm_mul, norm_mul, c_norm]
      _ ≤ A * (3 * M ^ 2 * ‖f x - g x‖) + (CP * d) * ‖g x‖ ^ 3 :=
        add_le_add (mul_le_mul (hPf x) (c_difference (f x) (g x) hM hfx hgx) (norm_nonneg _) hA)
          (mul_le_mul_of_nonneg_right (hpot x).1 (by positivity))
      _ = _ := by dsimp [a]; ring
  have hvg : ∀ᵐ x, ‖V x‖ ≤ |κ| *
      (a * ‖fderiv ℝ f x - fderiv ℝ g x‖ + b * ‖f x - g x‖ +
        e * d * ‖fderiv ℝ g x‖ + CG * d * ‖f x‖ ^ 3) := by
    filter_upwards [hfb, hgb, hDgb] with x hfx hgx hdy
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hdf : ‖dc (f x) (fderiv ℝ f x v) - dc (g x) (fderiv ℝ g x v)‖ ≤
        (3 * M ^ 2 * ‖fderiv ℝ f x - fderiv ℝ g x‖ + 6 * M * L * ‖f x - g x‖) * ‖v‖ := by
      apply (dc_difference (f x) (g x) (fderiv ℝ f x v) (fderiv ℝ g x v) hM hfx hgx).trans
      have hdel := (fderiv ℝ f x - fderiv ℝ g x).le_opNorm v
      change ‖fderiv ℝ f x v - fderiv ℝ g x v‖ ≤ _ at hdel
      calc
        _ ≤ 3 * M ^ 2 * (‖fderiv ℝ f x - fderiv ℝ g x‖ * ‖v‖) +
            6 * M * ‖f x - g x‖ * (L * ‖v‖) :=
          add_le_add (mul_le_mul_of_nonneg_left hdel (by positivity))
            (mul_le_mul_of_nonneg_left
              (((fderiv ℝ g x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hdy (norm_nonneg _))) (by positivity))
        _ = _ := by ring
    have hdg : ‖dc (g x) (fderiv ℝ g x v)‖ ≤ 3 * M ^ 2 * ‖fderiv ℝ g x‖ * ‖v‖ := by
      apply (dc_norm (g x) (fderiv ℝ g x v)).trans
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hgx 2) (by norm_num))
        ((fderiv ℝ g x).le_opNorm v) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have heq : V x v = (κ : ℂ) *
        (((potential (quarticDensity f) x * (dc (f x) (fderiv ℝ f x v) - dc (g x) (fderiv ℝ g x v)) +
          (potential (quarticDensity f) x - potential (quarticDensity g) x) * dc (g x) (fderiv ℝ g x v)) +
          (gradientPotential (fderiv ℝ (quarticDensity f)) x v -
            gradientPotential (fderiv ℝ (quarticDensity g)) x v) * c (f x)) +
          gradientPotential (fderiv ℝ (quarticDensity g)) x v * (c (f x) - c (g x))) := by
      change fderiv ℝ (hartreeNonlinearity κ f) x v - fderiv ℝ (hartreeNonlinearity κ g) x v = _
      rw [hF.2 x v, hG.2 x v]
      dsimp [dc, c]
      ring
    have hgd : ‖gradientPotential (fderiv ℝ (quarticDensity f)) x v -
        gradientPotential (fderiv ℝ (quarticDensity g)) x v‖ ≤ CG * d * ‖v‖ :=
      ((gradientPotential (fderiv ℝ (quarticDensity f)) x -
        gradientPotential (fderiv ℝ (quarticDensity g)) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hGdiff x) (norm_nonneg _))
    have hgg : ‖gradientPotential (fderiv ℝ (quarticDensity g)) x v‖ ≤ B * ‖v‖ :=
      ((gradientPotential (fderiv ℝ (quarticDensity g)) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hGg x) (norm_nonneg _))
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |κ| *
          (((‖potential (quarticDensity f) x * (dc (f x) (fderiv ℝ f x v) - dc (g x) (fderiv ℝ g x v))‖ +
            ‖(potential (quarticDensity f) x - potential (quarticDensity g) x) * dc (g x) (fderiv ℝ g x v)‖) +
            ‖(gradientPotential (fderiv ℝ (quarticDensity f)) x v - gradientPotential (fderiv ℝ (quarticDensity g)) x v) * c (f x)‖) +
            ‖gradientPotential (fderiv ℝ (quarticDensity g)) x v * (c (f x) - c (g x))‖) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg κ)
        exact (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ |κ| * (((A * ((3 * M ^ 2 * ‖fderiv ℝ f x - fderiv ℝ g x‖ +
            6 * M * L * ‖f x - g x‖) * ‖v‖) +
            (CP * d) * (3 * M ^ 2 * ‖fderiv ℝ g x‖ * ‖v‖)) +
            (CG * d * ‖v‖) * ‖f x‖ ^ 3) +
            (B * ‖v‖) * (3 * M ^ 2 * ‖f x - g x‖)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg κ)
        simp only [norm_mul, c_norm]
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul (hPf x) hdf (norm_nonneg _) hA)
          (mul_le_mul (hpot x).1 hdg (norm_nonneg _) (by positivity)))
          (mul_le_mul_of_nonneg_right hgd (by positivity)))
          (mul_le_mul hgg (c_difference (f x) (g x) hM hfx hgx) (norm_nonneg _) (by positivity))
      _ = _ := by dsimp [a, b, e]; ring
  have h6 (u : Space → ℂ) (hu : Continuous u)
      (hu4 : Integrable (fun x : Space => ‖u x‖ ^ 4))
      (huM : ∀ᵐ x, ‖u x‖ ≤ M) (huJ : (∫ x : Space, ‖u x‖ ^ 4) ≤ j ^ 2) :
      Integrable (fun x : Space => ‖u x‖ ^ 6) ∧
      (∫ x : Space, ‖u x‖ ^ 6) ≤ M ^ 2 * j ^ 2 := by
    have hm : ∀ᵐ x, ‖u x‖ ^ 6 ≤ M ^ 2 * ‖u x‖ ^ 4 := by
      filter_upwards [huM] with x hx
      calc
        _ = ‖u x‖ ^ 2 * ‖u x‖ ^ 4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by positivity)
    have hi : Integrable (fun x : Space => ‖u x‖ ^ 6) :=
      (hu4.const_mul (M ^ 2)).mono' (hu.aestronglyMeasurable.norm.pow 6)
        (hm.mono fun x hx => by simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ ‖u x‖ ^ 6)] using hx)
    have ht := integral_mono_ae hi (hu4.const_mul (M ^ 2)) hm
    rw [integral_const_mul] at ht
    exact ⟨hi, ht.trans (mul_le_mul_of_nonneg_left huJ (sq_nonneg M))⟩
  obtain ⟨hf6, hIf6⟩ := h6 f hf.continuous hf4 hfb hJf
  obtain ⟨hg6, hIg6⟩ := h6 g hg.continuous hg4 hgb hJg
  have hU2 : ∀ᵐ x, ‖U x‖ ^ 2 ≤ 2 * κ ^ 2 *
      (a ^ 2 * ‖f x - g x‖ ^ 2 + CP ^ 2 * d ^ 2 * ‖g x‖ ^ 6) := by
    filter_upwards [huv] with x hx
    have ht := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow, sq_abs] at ht
    have hp : (a * ‖f x - g x‖ + CP * d * ‖g x‖ ^ 3) ^ 2 ≤
        2 * (a ^ 2 * ‖f x - g x‖ ^ 2 + CP ^ 2 * d ^ 2 * ‖g x‖ ^ 6) := by
      nlinarith only [sq_nonneg (a * ‖f x - g x‖ - CP * d * ‖g x‖ ^ 3)]
    exact (ht.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg κ))).trans_eq (by ring)
  have hV2 : ∀ᵐ x, ‖V x‖ ^ 2 ≤ 4 * κ ^ 2 *
      (a ^ 2 * ‖fderiv ℝ f x - fderiv ℝ g x‖ ^ 2 + b ^ 2 * ‖f x - g x‖ ^ 2 +
        e ^ 2 * d ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + CG ^ 2 * d ^ 2 * ‖f x‖ ^ 6) := by
    filter_upwards [hvg] with x hx
    have ht := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow, sq_abs] at ht
    have hp := four_square (a * ‖fderiv ℝ f x - fderiv ℝ g x‖) (b * ‖f x - g x‖)
      (e * d * ‖fderiv ℝ g x‖) (CG * d * ‖f x‖ ^ 3)
    have hp' : (a * ‖fderiv ℝ f x - fderiv ℝ g x‖ + b * ‖f x - g x‖ +
        e * d * ‖fderiv ℝ g x‖ + CG * d * ‖f x‖ ^ 3) ^ 2 ≤
        4 * (a ^ 2 * ‖fderiv ℝ f x - fderiv ℝ g x‖ ^ 2 + b ^ 2 * ‖f x - g x‖ ^ 2 +
          e ^ 2 * d ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + CG ^ 2 * d ^ 2 * ‖f x‖ ^ 6) := by
      convert hp using 1 <;> ring
    exact (ht.trans (mul_le_mul_of_nonneg_left hp' (sq_nonneg κ))).trans_eq (by ring)
  have hiδ := hfg.norm.integrable_sq
  have hiDδ := (hDf.sub hDg).norm.integrable_sq
  have hig := hDg.norm.integrable_sq
  refine ⟨hU, hV, ?_, ?_, ?_⟩
  · have hmaj := ((hiδ.const_mul (a ^ 2)).add (hg6.const_mul (CP ^ 2 * d ^ 2))).const_mul (2 * κ ^ 2)
    have ht := integral_mono_ae hU.norm.integrable_sq hmaj hU2
    simp only [Pi.add_apply] at ht
    rw [integral_const_mul, integral_add (hiδ.const_mul (a ^ 2)) (hg6.const_mul (CP ^ 2 * d ^ 2)),
      integral_const_mul, integral_const_mul] at ht
    calc
      _ ≤ 2 * κ ^ 2 * (a ^ 2 * (∫ x : Space, ‖f x - g x‖ ^ 2) +
          (CP ^ 2 * d ^ 2) * (∫ x : Space, ‖g x‖ ^ 6)) := ht
      _ ≤ 2 * κ ^ 2 * (a ^ 2 * d ^ 2 + (CP ^ 2 * d ^ 2) * (M ^ 2 * j ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hδ2 (sq_nonneg a))
            (mul_le_mul_of_nonneg_left hIg6 (by positivity))) (by positivity)
      _ = _ := by ring
  · have ht1 := hiDδ.const_mul (a ^ 2)
    have ht2 := hiδ.const_mul (b ^ 2)
    have ht3 := hig.const_mul (e ^ 2 * d ^ 2)
    have ht4 := hf6.const_mul (CG ^ 2 * d ^ 2)
    have hmaj := (((ht1.add ht2).add ht3).add ht4).const_mul (4 * κ ^ 2)
    have ht := integral_mono_ae hV.norm.integrable_sq hmaj hV2
    simp only [Pi.add_apply] at ht
    have hadd4 := integral_add ((ht1.add ht2).add ht3) ht4
    have hadd3 := integral_add (ht1.add ht2) ht3
    have hadd2 := integral_add ht1 ht2
    simp only [Pi.add_apply] at hadd4 hadd3 hadd2
    rw [integral_const_mul, hadd4, hadd3, hadd2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at ht
    calc
      _ ≤ 4 * κ ^ 2 * (((a ^ 2 * (∫ x : Space, ‖fderiv ℝ f x - fderiv ℝ g x‖ ^ 2) +
          b ^ 2 * (∫ x : Space, ‖f x - g x‖ ^ 2)) +
          (e ^ 2 * d ^ 2) * (∫ x : Space, ‖fderiv ℝ g x‖ ^ 2)) +
          (CG ^ 2 * d ^ 2) * (∫ x : Space, ‖f x‖ ^ 6)) := ht
      _ ≤ 4 * κ ^ 2 * (((a ^ 2 * d ^ 2 + b ^ 2 * d ^ 2) +
          (e ^ 2 * d ^ 2) * Q ^ 2) + (CG ^ 2 * d ^ 2) * (M ^ 2 * j ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hDδ2 (sq_nonneg a))
            (mul_le_mul_of_nonneg_left hδ2 (sq_nonneg b)))
          (mul_le_mul_of_nonneg_left hEg (by positivity)))
          (mul_le_mul_of_nonneg_left hIf6 (by positivity))
      _ = _ := by ring
  · intro φ hcφ hφ v
    have ht : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hcφ
    have hDt : MemLp (fderiv ℝ φ) 2 :=
      (hφ.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hcφ.fderiv ℝ)
    have hVv : MemLp (fun x => V x v) 2 :=
      hV.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ v)
    have htv : MemLp (fun x => fderiv ℝ φ x v) 2 :=
      hDt.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ v)
    have hright := hVv.integrable_mul ht
    have hleft := hU.integrable_mul htv
    have hbase := hU.integrable_mul ht
    refine ⟨hleft, hright, ?_⟩
    exact integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℂ) hright hleft hbase
      (fun x _ => (hF.1 x).hasFDerivAt.sub (hG.1 x).hasFDerivAt)
      (fun x _ => (hφ.differentiable (by norm_num) x).hasFDerivAt)

#print axioms hartree_first_order_difference_noncompact
end HBL.RegularRadiation.FullFirstOrderDifference
