import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Quantitative moving-frame estimates for the analytic implication in
manuscript Lemma 3.3. The connection is defined by actual inverse,
derivative, bounded commutator and remainder operations. In particular,
no bound on the connection or its difference is an input.

Scope: this independently proves the moving-frame implication, including
the inverse-difference terms missing from the manuscript's short proof.
Instantiation by the actual background/graph transform in Propositions
2.13 and 3.2 is NOT supplied here. Original dependency-closed acceptance
remains 8/21; this module alone must not be counted as a ninth environment.
-/

noncomputable section

namespace HBL.SlowFrame

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- The algebraic value of the exact moving connection at one time.
K is the frame derivative and C the time-scaled bounded commutator. -/
def connectionValue (S : Aˣ) (K C R : A) : A :=
  (↑(S⁻¹) : A) * (-K + C + R * (↑S : A))

/-- Near-identity frames and their actual inverses have uniform bounds.
The inverse bound is proved, not included as a separate assumption. -/
theorem frame_norm_and_inverse_le (S : Aˣ)
    (hS : ‖(↑S : A) - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(↑S : A)‖ ≤ (3 / 2 : ℝ) ∧ ‖(↑(S⁻¹) : A)‖ ≤ 2 := by
  constructor
  · have h := norm_add_le ((↑S : A) - 1) (1 : A)
    rw [sub_add_cancel, norm_one] at h
    linarith
  · have hid : (↑(S⁻¹) : A) =
        1 - (↑(S⁻¹) : A) * ((↑S : A) - 1) := by
      calc
        (↑(S⁻¹) : A) = (↑(S⁻¹) : A) * (↑S : A) -
            (↑(S⁻¹) : A) * ((↑S : A) - 1) := by noncomm_ring
        _ = 1 - (↑(S⁻¹) : A) * ((↑S : A) - 1) := by simp
    have hn : ‖(↑(S⁻¹) : A)‖ ≤
        1 + ‖(↑(S⁻¹) : A)‖ * ‖(↑S : A) - 1‖ := by
      calc
        ‖(↑(S⁻¹) : A)‖ =
            ‖1 - (↑(S⁻¹) : A) * ((↑S : A) - 1)‖ := congrArg norm hid
        _ ≤ ‖(1 : A)‖ + ‖(↑(S⁻¹) : A) * ((↑S : A) - 1)‖ := norm_sub_le _ _
        _ ≤ 1 + ‖(↑(S⁻¹) : A)‖ * ‖(↑S : A) - 1‖ := by
          rw [norm_one]
          exact add_le_add le_rfl (norm_mul_le (↑(S⁻¹) : A) ((↑S : A) - 1))
    have hmul := mul_le_mul_of_nonneg_left hS (norm_nonneg (↑(S⁻¹) : A))
    linarith

/-- Lipschitz estimate for the actual inverse of two near-identity frames. -/
theorem frame_inverse_difference_le (S T : Aˣ)
    (hS : ‖(↑S : A) - 1‖ ≤ (1 / 2 : ℝ))
    (hT : ‖(↑T : A) - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(↑(S⁻¹) : A) - (↑(T⁻¹) : A)‖ ≤ 4 * ‖(↑S : A) - (↑T : A)‖ := by
  have hSi := (frame_norm_and_inverse_le S hS).2
  have hTi := (frame_norm_and_inverse_le T hT).2
  have hleft : (↑(S⁻¹) : A) * (↑T : A) * (↑(T⁻¹) : A) = (↑(S⁻¹) : A) := by
    rw [mul_assoc]
    simp
  have hright : (↑(S⁻¹) : A) * (↑S : A) * (↑(T⁻¹) : A) = (↑(T⁻¹) : A) := by simp
  have hid : (↑(S⁻¹) : A) - (↑(T⁻¹) : A) =
      (↑(S⁻¹) : A) * ((↑T : A) - (↑S : A)) * (↑(T⁻¹) : A) := by
    calc
      (↑(S⁻¹) : A) - (↑(T⁻¹) : A) =
          (↑(S⁻¹) : A) * (↑T : A) * (↑(T⁻¹) : A) -
          (↑(S⁻¹) : A) * (↑S : A) * (↑(T⁻¹) : A) := by rw [hleft, hright]
      _ = _ := by noncomm_ring
  rw [hid]
  calc
    ‖(↑(S⁻¹) : A) * ((↑T : A) - (↑S : A)) * (↑(T⁻¹) : A)‖ ≤
        (‖(↑(S⁻¹) : A)‖ * ‖(↑T : A) - (↑S : A)‖) * ‖(↑(T⁻¹) : A)‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (2 * ‖(↑T : A) - (↑S : A)‖) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hSi (norm_nonneg _)) hTi
        (norm_nonneg _) (by positivity)
    _ = 4 * ‖(↑S : A) - (↑T : A)‖ := by rw [norm_sub_rev]; ring

omit [NormOneClass A] in
private theorem residual_norm_le (S : Aˣ) (K C R : A) :
    ‖-K + C + R * (↑S : A)‖ ≤ ‖K‖ + ‖C‖ + ‖R‖ * ‖(↑S : A)‖ := by
  have h1 := norm_add_le (-K + C) (R * (↑S : A))
  have h2 := norm_add_le (-K) C
  rw [norm_neg] at h2
  have h3 := norm_mul_le R (↑S : A)
  linarith

omit [NormOneClass A] in
private theorem residual_difference_norm_le (S T : Aˣ) (K L C D R U : A) :
    ‖(-K + C + R * (↑S : A)) - (-L + D + U * (↑T : A))‖ ≤
      ‖K - L‖ + ‖C - D‖ + ‖R - U‖ * ‖(↑S : A)‖ +
        ‖U‖ * ‖(↑S : A) - (↑T : A)‖ := by
  have hid : (-K + C + R * (↑S : A)) - (-L + D + U * (↑T : A)) =
      (-(K - L) + (C - D)) + (R - U) * (↑S : A) +
        U * ((↑S : A) - (↑T : A)) := by noncomm_ring
  rw [hid]
  have h1 := norm_add_le (-(K - L) + (C - D)) ((R - U) * (↑S : A))
  have h2 := norm_add_le (-(K - L)) (C - D)
  rw [norm_neg] at h2
  have h3 := norm_add_le ((-(K - L) + (C - D)) + (R - U) * (↑S : A))
    (U * ((↑S : A) - (↑T : A)))
  have h4 := norm_mul_le (R - U) (↑S : A)
  have h5 := norm_mul_le U ((↑S : A) - (↑T : A))
  linarith

/-- Complete single-frame estimate from the primitive three source terms. -/
theorem connectionValue_norm_le (S : Aˣ) (K C R : A) (b : ℝ)
    (hb : 0 ≤ b) (hS : ‖(↑S : A) - 1‖ ≤ (1 / 2 : ℝ))
    (hK : ‖K‖ ≤ b) (hC : ‖C‖ ≤ b) (hR : ‖R‖ ≤ b) :
    ‖connectionValue S K C R‖ ≤ 7 * b := by
  obtain ⟨hSn, hSi⟩ := frame_norm_and_inverse_le S hS
  have hRS := mul_le_mul hR hSn (norm_nonneg (↑S : A)) hb
  have hres : ‖-K + C + R * (↑S : A)‖ ≤ (7 / 2 : ℝ) * b := by
    have h := residual_norm_le S K C R
    linarith
  unfold connectionValue
  calc
    ‖(↑(S⁻¹) : A) * (-K + C + R * (↑S : A))‖ ≤
        ‖(↑(S⁻¹) : A)‖ * ‖-K + C + R * (↑S : A)‖ := norm_mul_le _ _
    _ ≤ 2 * ((7 / 2 : ℝ) * b) :=
      mul_le_mul hSi hres (norm_nonneg _) (by norm_num)
    _ = 7 * b := by ring

/-- Full two-frame estimate, retaining the inverse-difference and
remainder-times-frame-difference contributions. -/
theorem connectionValue_difference_le (S T : Aˣ) (K L C D R U : A)
    (b e d : ℝ) (hb : 0 ≤ b) (he : 0 ≤ e) (hd : 0 ≤ d)
    (hS : ‖(↑S : A) - 1‖ ≤ (1 / 2 : ℝ))
    (hT : ‖(↑T : A) - 1‖ ≤ (1 / 2 : ℝ))
    (hL : ‖L‖ ≤ b) (hD : ‖D‖ ≤ b) (hU : ‖U‖ ≤ b)
    (hKL : ‖K - L‖ ≤ e) (hCD : ‖C - D‖ ≤ e) (hRU : ‖R - U‖ ≤ e)
    (hST : ‖(↑S : A) - (↑T : A)‖ ≤ d) :
    ‖connectionValue S K C R - connectionValue T L D U‖ ≤ 7 * e + 16 * b * d := by
  obtain ⟨hSn, hSi⟩ := frame_norm_and_inverse_le S hS
  have hTn := (frame_norm_and_inverse_le T hT).1
  have hUT := mul_le_mul hU hTn (norm_nonneg (↑T : A)) hb
  have hresT : ‖-L + D + U * (↑T : A)‖ ≤ (7 / 2 : ℝ) * b := by
    have h := residual_norm_le T L D U
    linarith
  have hRUS := mul_le_mul hRU hSn (norm_nonneg (↑S : A)) he
  have hUST := mul_le_mul hU hST (norm_nonneg ((↑S : A) - (↑T : A))) hb
  have hresDiff : ‖(-K + C + R * (↑S : A)) - (-L + D + U * (↑T : A))‖ ≤
      (7 / 2 : ℝ) * e + b * d := by
    have h := residual_difference_norm_le S T K L C D R U
    linarith
  have hinv : ‖(↑(S⁻¹) : A) - (↑(T⁻¹) : A)‖ ≤ 4 * d :=
    (frame_inverse_difference_le S T hS hT).trans
      (mul_le_mul_of_nonneg_left hST (by norm_num))
  have hid : connectionValue S K C R - connectionValue T L D U =
      (↑(S⁻¹) : A) * ((-K + C + R * (↑S : A)) - (-L + D + U * (↑T : A))) +
      ((↑(S⁻¹) : A) - (↑(T⁻¹) : A)) * (-L + D + U * (↑T : A)) := by
    unfold connectionValue
    noncomm_ring
  rw [hid]
  have h1 := norm_add_le
    ((↑(S⁻¹) : A) * ((-K + C + R * (↑S : A)) - (-L + D + U * (↑T : A))))
    (((↑(S⁻¹) : A) - (↑(T⁻¹) : A)) * (-L + D + U * (↑T : A)))
  have h2 := (norm_mul_le (↑(S⁻¹) : A) _).trans
    (mul_le_mul hSi hresDiff (norm_nonneg _) (by norm_num))
  have h3 := (norm_mul_le ((↑(S⁻¹) : A) - (↑(T⁻¹) : A)) _).trans
    (mul_le_mul hinv hresT (norm_nonneg _) (by positivity))
  nlinarith

variable [NormedAlgebra ℝ A]

/-- Actual time-dependent connection, with the ordinary derivative of
the frame, the time-scaled bounded commutator and the transformed remainder. -/
def movingConnection (S : ℝ → Aˣ) (C R : ℝ → A) (s : ℝ) : A :=
  connectionValue (S s) (deriv (fun t => (↑(S t) : A)) s) ((s⁻¹ : ℝ) • C s) (R s)

/-- The full pointwise/two-path analytic implication of Lemma 3.3.
All hypotheses concern frames and their primitive source terms; none
assumes the asserted connection estimate. The inverse difference terms
produce the explicit additional 16 M L coefficient.

This does not construct the manuscript background or its graph frame. -/
theorem movingConnection_positive_margin
    (S T : ℝ → Aˣ) (C D R U : ℝ → A)
    (s κ δ M L ρ : ℝ) (hs : 0 < s) (hκ : 0 < κ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hS : ‖(↑(S s) : A) - 1‖ ≤ (1 / 2 : ℝ))
    (hT : ‖(↑(T s) : A) - 1‖ ≤ (1 / 2 : ℝ))
    (hKS : ‖deriv (fun t => (↑(S t) : A)) s‖ ≤ M * s ^ (-1 - κ))
    (hKT : ‖deriv (fun t => (↑(T t) : A)) s‖ ≤ M * s ^ (-1 - κ))
    (hC : ‖(s⁻¹ : ℝ) • C s‖ ≤ M * s ^ (-1 - κ))
    (hD : ‖(s⁻¹ : ℝ) • D s‖ ≤ M * s ^ (-1 - κ))
    (hR : ‖R s‖ ≤ M * s ^ (-1 - κ))
    (hU : ‖U s‖ ≤ M * s ^ (-1 - κ))
    (hdS : ‖(↑(S s) : A) - (↑(T s) : A)‖ ≤ L * ρ * s ^ (-δ))
    (hdK : ‖deriv (fun t => (↑(S t) : A)) s - deriv (fun t => (↑(T t) : A)) s‖ ≤
      L * ρ * s ^ (-1 - κ - δ))
    (hdC : ‖(s⁻¹ : ℝ) • C s - (s⁻¹ : ℝ) • D s‖ ≤ L * ρ * s ^ (-1 - κ - δ))
    (hdR : ‖R s - U s‖ ≤ L * ρ * s ^ (-1 - κ - δ)) :
    0 < κ ∧
      ‖movingConnection S C R s‖ ≤ (7 * M) * s ^ (-1 - κ) ∧
      ‖movingConnection S C R s - movingConnection T D U s‖ ≤
        ((7 + 16 * M) * L) * ρ * s ^ (-1 - κ - δ) := by
  have hw : 0 ≤ s ^ (-1 - κ) := (Real.rpow_pos_of_pos hs _).le
  have hz : 0 ≤ s ^ (-δ) := (Real.rpow_pos_of_pos hs _).le
  have hwz : 0 ≤ s ^ (-1 - κ - δ) := (Real.rpow_pos_of_pos hs _).le
  have hprod : s ^ (-1 - κ) * s ^ (-δ) = s ^ (-1 - κ - δ) := by
    simpa only [sub_eq_add_neg] using (Real.rpow_add hs (-1 - κ) (-δ)).symm
  refine ⟨hκ, ?_, ?_⟩
  · have h := connectionValue_norm_le (S s)
      (deriv (fun t => (↑(S t) : A)) s) ((s⁻¹ : ℝ) • C s) (R s)
      (M * s ^ (-1 - κ)) (mul_nonneg hM hw) hS hKS hC hR
    change ‖connectionValue (S s) _ _ _‖ ≤ _
    nlinarith only [h]
  · have h := connectionValue_difference_le (S s) (T s)
      (deriv (fun t => (↑(S t) : A)) s) (deriv (fun t => (↑(T t) : A)) s)
      ((s⁻¹ : ℝ) • C s) ((s⁻¹ : ℝ) • D s) (R s) (U s)
      (M * s ^ (-1 - κ)) (L * ρ * s ^ (-1 - κ - δ)) (L * ρ * s ^ (-δ))
      (mul_nonneg hM hw) (mul_nonneg (mul_nonneg hL hρ) hwz)
      (mul_nonneg (mul_nonneg hL hρ) hz) hS hT hKT hD hU hdK hdC hdR hdS
    have hid : 7 * (L * ρ * s ^ (-1 - κ - δ)) +
        16 * (M * s ^ (-1 - κ)) * (L * ρ * s ^ (-δ)) =
        ((7 + 16 * M) * L) * ρ * s ^ (-1 - κ - δ) := by
      calc
        _ = 7 * (L * ρ * s ^ (-1 - κ - δ)) +
            16 * M * L * ρ * (s ^ (-1 - κ) * s ^ (-δ)) := by ring
        _ = _ := by rw [hprod]; ring
    rw [hid] at h
    exact h

end HBL.SlowFrame
