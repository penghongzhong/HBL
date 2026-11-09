import HBL.TypeIIDynamicSelection.ActualHartreeBackwardSpectralNeumannFiniteGain
import HBL.TypeIIDynamicSelection.ActualHartreeBackwardZeroLeftSpectralVolterraSlope
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummerClassical
import Mathlib.Tactic

/-!
# All-finite actual backward spectral Cramer-Green value and derivative

Every generated spectral field is the original origin Kummer-Green
solution of delta times the preceding field, with zero Cauchy data
at the SAME left matching radius. Its C1 radial slope is identified
with the actual derivative via the classical original Green theorem.

This is a spatial estimate only. Genuine time derivatives and full
four-region nonlocal nonlinear Hartree re-matching are still required.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

theorem actual_Hartree_backward_spectral_Neumann_finite_true_C1_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hK : OriginBasisOn K a b C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (F : ℝ → ℂ) (U DU delta : ℂ)
    (hFcont : ∀ x ∈ Ioo (0 : ℝ) scale, ContinuousAt F x)
    (hInitial : ∀ r ∈ Icc (a / 2) a,
      ‖actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta 0 r‖ ≤ H)
    (hInt : ∀ (n : ℕ) (r : ℝ), r ∈ Icc (a / 2) a →
      IntervalIntegrable
        (originGreenSourceA K
          (fun x => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x))
        volume r a)
    (hIntR : ∀ (n : ℕ),
      IntervalIntegrable
        (originGreenSourceA K
          (fun x => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x))
        volume a b) :
    let c := 2 * G ^ 2 * a * ‖delta‖
    ∀ (n : ℕ) (r : ℝ), r ∈ Icc (a / 2) a →
      let u := actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta (n + 1)
      ‖(r : ℂ) * u r‖ + ‖(r : ℂ) ^ 2 * deriv u r‖ ≤
        (a + (a + 1) * (a - r)) * c ^ (n + 1) * H := by
  dsimp only
  let c : ℝ := 2 * G ^ 2 * a * ‖delta‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hPair : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G := by
    intro x hx
    exact ⟨(hModes x hx).1, (hModes x hx).2.2.1⟩
  have hAll :=
    actual_Hartree_backward_spectral_Neumann_all_finite_value_gain
      K a b C G H ha hab hb.le hG hH hK hPair
      F U DU delta hInitial hInt hIntR
  have hCont : ∀ (n : ℕ) (x : ℝ),
      x ∈ Ioo (0 : ℝ) scale →
      ContinuousAt (actualHartreeBackwardSpectralNeumannIterate
        K a b F U DU delta n) x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        exact (actual_origin_matched_Kummer_classical_on_positive_interval
          K ha hab hb F hFcont U DU x hx).1.continuousAt
    | succ n ih =>
        intro x hx
        have hqCont (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) scale) :
            ContinuousAt
              (fun t => delta *
                actualHartreeBackwardSpectralNeumannIterate
                  K a b F U DU delta n t) y :=
          continuousAt_const.mul (ih y hy)
        exact (actual_origin_matched_Kummer_classical_on_positive_interval
          K ha hab hb
          (fun t => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n t)
          hqCont 0 0 x hx).1.continuousAt
  intro n r hr
  let Hn : ℝ := c ^ n * H
  have hHn : 0 ≤ Hn := by
    dsimp [Hn]
    exact mul_nonneg (pow_nonneg hc _) hH
  let M : ℝ := a * ‖delta‖ * Hn
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrPos : 0 < r := (half_pos ha).trans_le hr.1
  have hrK : r ∈ Ioo (0 : ℝ) scale :=
    ⟨hrPos, (hr.2.trans hab).trans_lt hb⟩
  have hForce (x : ℝ) (hx : x ∈ Icc (a / 2) a) :
      ‖delta * actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta n x‖ ≤ M / x := by
    have hxPos : 0 < x := (half_pos ha).trans_le hx.1
    have hPrev :
        ‖actualHartreeBackwardSpectralNeumannIterate
            K a b F U DU delta n x‖ ≤ Hn := hAll n x hx
    have hConst : 0 ≤ ‖delta‖ * Hn :=
      mul_nonneg (norm_nonneg delta) hHn
    have hMul := mul_le_mul_of_nonneg_left hx.2 hConst
    apply (le_div_iff₀ hxPos).2
    calc
      ‖delta * actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta n x‖ * x =
          (‖delta‖ *
            ‖actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x‖) * x := by rw [norm_mul]
      _ ≤ (‖delta‖ * Hn) * x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPrev (norm_nonneg delta))
          hxPos.le
      _ ≤ (‖delta‖ * Hn) * a := hMul
      _ = M := by dsimp [M]; ring
  have hqCont (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) scale) :
      ContinuousAt
        (fun t => delta *
          actualHartreeBackwardSpectralNeumannIterate
            K a b F U DU delta n t) x :=
    continuousAt_const.mul (hCont n x hx)
  have hDerivative :=
    (actual_origin_matched_Kummer_classical_on_positive_interval
      K ha hab hb
      (fun t => delta *
        actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta n t)
      hqCont 0 0 r hrK).1.deriv
  have hSlope :=
    actual_Hartree_zero_left_backward_original_Green_slope_bound
      K a b C G M ha hab hb.le hG hM hK hModes
      (fun t => delta *
        actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta n t)
      hForce r hr (hInt n r hr) (hIntR n)
  have hSlopeReal :
      ‖(r : ℂ) ^ 2 *
        deriv (actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta (n + 1)) r‖ ≤
        (a + 1) * (a - r) * (c ^ (n + 1) * H) := by
    have hE :
        ‖(r : ℂ) ^ 2 *
          deriv (actualHartreeBackwardSpectralNeumannIterate
            K a b F U DU delta (n + 1)) r‖ ≤
          2 * (a + 1) * G ^ 2 * M * (a - r) := by
      change ‖(r : ℂ) ^ 2 * deriv
        (actualOriginMatchedKummerValue K a b
          (fun t => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n t)
          0 0) r‖ ≤ _
      rw [hDerivative]
      exact hSlope
    calc
      _ ≤ 2 * (a + 1) * G ^ 2 * M * (a - r) := hE
      _ = (a + 1) * (a - r) * (c ^ (n + 1) * H) := by
        dsimp [M, Hn, c]
        rw [pow_succ]
        ring
  have hValue :
      ‖(r : ℂ) *
        actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta (n + 1) r‖ ≤
        a * (c ^ (n + 1) * H) := by
    have hNormR : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
    calc
      _ = r * ‖actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta (n + 1) r‖ := by
        rw [norm_mul, hNormR]
      _ ≤ r * (c ^ (n + 1) * H) :=
        mul_le_mul_of_nonneg_left (hAll (n + 1) r hr) hrPos.le
      _ ≤ a * (c ^ (n + 1) * H) :=
        mul_le_mul_of_nonneg_right hr.2
          (mul_nonneg (pow_nonneg hc _) hH)
  change ‖(r : ℂ) *
      actualHartreeBackwardSpectralNeumannIterate
        K a b F U DU delta (n + 1) r‖ +
    ‖(r : ℂ) ^ 2 * deriv
      (actualHartreeBackwardSpectralNeumannIterate
        K a b F U DU delta (n + 1)) r‖ ≤
    (a + (a + 1) * (a - r)) * c ^ (n + 1) * H
  calc
    _ ≤ a * (c ^ (n + 1) * H) +
        (a + 1) * (a - r) * (c ^ (n + 1) * H) :=
      add_le_add hValue hSlopeReal
    _ = (a + (a + 1) * (a - r)) * c ^ (n + 1) * H := by ring

end HBL.TypeIIDynamicSelection
