import HBL.TypeIIDynamicSelection.ActualHartreeMatchedKummerInteriorSourceBound
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import Mathlib.Tactic

/-!
# Radial physical Hdot1 energy for the ACTUAL matched Green region

The complete Green--regular Kummer field is not merely controlled at its
upper endpoint. Compatibility eliminates its singular origin mode and the
original two-coordinate Fredholm jet controls the regular channel.

On the actual physical interval [A*a,A*b], the exact pullback derivative
has factor A^{-1}. Therefore the three-dimensional radial-gradient energy
has the geometric factor A (b-a) and does not hide an arbitrary envelope
for the Green branch. The original source F, left jet U,DU, and uniform
basis budget C are the only displayed quantitative inputs.

This is a genuine Green-region energy bound; it does not yet imply
global inner+Green+repair+remote Hdot1 or a full s^(-9/4) Hartree remainder.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The actual physical derivative of the normalized Green pullback is
bounded on the entire physical matching annulus, not just at its right end.
No independent Cauchy slope bound is assumed at that end. -/
theorem actual_Hartree_matched_physical_Green_region_derivative_bound
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (A a b C M : ℝ)
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < scale)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hFcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt F x)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0)
    (y : ℝ) (hy : y ∈ Icc (A * a) (A * b)) :
    let v := actualOriginMatchedKummerPullback K A a b F U DU
    let E := 2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)
    ‖deriv v y‖ ≤ E / A := by
  dsimp only
  let w := actualOriginMatchedKummerValue K a b F U DU
  let v := actualOriginMatchedKummerPullback K A a b F U DU
  let E := 2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)
  have hx : y / A ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hA).2
      simpa only [mul_comm] using hy.1
    · apply (div_le_iff₀ hA).2
      simpa only [mul_comm] using hy.2
  have hyScale : y ∈ Ioo 0 (A * scale) := by
    constructor
    · exact (mul_pos hA ha).trans_le hy.1
    · exact hy.2.trans_lt (mul_lt_mul_of_pos_left hb hA)
  have hClass :=
    (actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb F hFcont U DU (y / A)
      ⟨(div_pos hyScale.1 hA), hx.2.trans_lt hb⟩).1
  have hPull :=
    (actual_Hartree_matched_Kummer_pullback_classical
      K A hA ha hab hb F hFcont U DU y hyScale).1
  have hInt :=
    actual_Hartree_matched_Kummer_interior_from_source_and_left_jet
      K a b C M hC hM hK hab F hF U DU hzero (y / A) hx
  have hSlope :
      ‖actualOriginMatchedKummerSlope K a b F U DU (y / A)‖ ≤ E := by
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hInt
  have hInv : ‖(A : ℂ)⁻¹‖ = A⁻¹ := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hA]
  calc
    ‖deriv v y‖ =
        ‖(A : ℂ)⁻¹ * actualOriginMatchedKummerSlope
          K a b F U DU (y / A)‖ := by
      rw [hPull.deriv, hClass.deriv]
    _ = A⁻¹ * ‖actualOriginMatchedKummerSlope K a b F U DU (y / A)‖ := by
      rw [norm_mul, hInv]
    _ ≤ A⁻¹ * E :=
      mul_le_mul_of_nonneg_left hSlope (inv_nonneg.mpr hA.le)
    _ = E / A := by rw [div_eq_mul_inv]; ring

/-- The genuine physical radial gradient of the same source-controlled
Green field. The true physical 3D r² weight is integrated, not postulated
as an abstract regional Hdot1 bound. -/
theorem actual_Hartree_matched_physical_Green_region_radial_H1_energy
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (A a b C M : ℝ)
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < scale)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : OriginBasisOn K a b C)
    (F : ℝ → ℂ)
    (hFcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt F x)
    (hF : ∀ x ∈ Icc a b, ‖F x‖ ≤ M)
    (U DU : ℂ)
    (hzero : actualMomentLockedIntervalObstruction K a b F U DU = 0) :
    let v := actualOriginMatchedKummerPullback K A a b F U DU
    let E := 2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)
    (∫ y in Icc (A * a) (A * b),
      y ^ 2 * ‖deriv v y‖ ^ 2) ≤ A * (b - a) * (b * E) ^ 2 := by
  dsimp only
  let v := actualOriginMatchedKummerPullback K A a b F U DU
  let E := 2 * C ^ 3 * ((b - a) * M + ‖U‖ + ‖DU‖)
  let lo := A * a
  let hi := A * b
  let D := b * E
  let g : ℝ → ℝ := fun y => y ^ 2 * ‖deriv v y‖ ^ 2
  have hB : 0 ≤ b := ha.le.trans hab
  have hLo : 0 < lo := mul_pos hA ha
  have hLoHi : lo ≤ hi := mul_le_mul_of_nonneg_left hab hA.le
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hD : 0 ≤ D := mul_nonneg hB hE
  have hBound (y : ℝ) (hy : y ∈ Icc lo hi) :
      g y ≤ D ^ 2 := by
    have hDerivative : ‖deriv v y‖ ≤ E / A :=
      actual_Hartree_matched_physical_Green_region_derivative_bound
        K A a b C M hA ha hab hb hC hM hK F hFcont hF U DU hzero
        y (by simpa only [lo, hi] using hy)
    have hy0 : 0 ≤ y := hLo.le.trans hy.1
    have hP : y * ‖deriv v y‖ ≤ D := by
      calc
        _ ≤ (A * b) * (E / A) :=
          mul_le_mul (by simpa only [hi] using hy.2)
            hDerivative (norm_nonneg _) (by positivity)
        _ = D := by dsimp [D]; field_simp [hA.ne']
    have hNonneg : 0 ≤ y * ‖deriv v y‖ :=
      mul_nonneg hy0 (norm_nonneg _)
    calc
      g y = (y * ‖deriv v y‖) ^ 2 := by dsimp [g]; ring
      _ ≤ D ^ 2 := pow_le_pow_left₀ hNonneg hP 2
  have hFinite : (volume : Measure ℝ) (Icc lo hi) < ⊤ := by
    simp only [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hAE : ∀ᵐ y : ℝ ∂volume, y ∈ Icc lo hi →
      ‖g y‖ ≤ D ^ 2 := by
    filter_upwards with y
    intro hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; positivity)]
    exact hBound y hy
  have hNorm := norm_setIntegral_le_of_norm_le_const_ae'
      (μ := volume) (s := Icc lo hi) (f := g) (C := D ^ 2)
      hFinite hAE
  have hLen : hi - lo = A * (b - a) := by
    dsimp [lo,hi]; ring
  have hIntegral : ‖∫ y in Icc lo hi, g y‖ ≤ D ^ 2 * (A * (b - a)) := by
    simpa only [Real.volume_real_Icc_of_le hLoHi, hLen] using hNorm
  calc
    (∫ y in Icc (A * a) (A * b),
      y ^ 2 * ‖deriv v y‖ ^ 2) = ∫ y in Icc lo hi, g y := rfl
    _ ≤ ‖∫ y in Icc lo hi, g y‖ :=
      (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
    _ ≤ D ^ 2 * (A * (b - a)) := hIntegral
    _ = A * (b - a) * (b * E) ^ 2 := by dsimp [D]; ring

end HBL.TypeIIDynamicSelection
