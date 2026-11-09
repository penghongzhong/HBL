import HBL.TypeIIDynamicSelection.ActualHartreeBackwardZeroLeftSpectralVolterra
import Mathlib.Tactic

/-!
# Finite backward spectral Neumann corrections from the actual origin Green map

This is a genuine finite recursion of the original normalized Cramer Green
operator, not a recurrence of invented scalar envelopes.  The zeroth term
is the matched physical-source Green field and each subsequent correction
uses the preceding field as its actual spectral source, with zero anchor
Cauchy data.

The only size input is the initial matched field on the backward physical
shell.  Integrability of each explicitly constructed Green forcing is
stated separately; it is NOT an assumption of decay or positive time order.
The exact backward Wronskian/Volterra estimate is invoked at every step.

The conclusion is a quantitative spatial estimate for every finite n.
It neither proves the original four-domain nonlinear time residual nor
the finite physical profile theorem of manuscript section 2.13.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- The actual n-th backward spectral correction with the ORIGINAL
zero-jet origin Kummer Green map.  No abstract right inverse is introduced. -/
noncomputable def actualHartreeBackwardSpectralNeumannIterate
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU delta : ℂ) :
    ℕ → ℝ → ℂ
  | 0 => actualOriginMatchedKummerValue K a b F U DU
  | n + 1 =>
      actualOriginMatchedKummerValue K a b
        (fun x => delta *
          actualHartreeBackwardSpectralNeumannIterate K a b F U DU delta n x)
        0 0

/-- All finite actual Green iterates have a geometrically improved
backward-shell bound.  Their sources are literally delta times the
previous original Cramer-Green response.  There is no independently
assigned size envelope for any correction of positive index. -/
theorem actual_Hartree_backward_spectral_Neumann_all_finite_value_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hK : OriginBasisOn K a b C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (U DU delta : ℂ)
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
    ∀ (n : ℕ) (r : ℝ), r ∈ Icc (a / 2) a →
      ‖actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta n r‖ ≤
        (2 * G ^ 2 * a * ‖delta‖) ^ n * H := by
  let c : ℝ := 2 * G ^ 2 * a * ‖delta‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  intro n
  induction n with
  | zero =>
      intro r hr
      simpa only [pow_zero, one_mul] using hInitial r hr
  | succ n ih =>
      intro r hr
      let Hn : ℝ := c ^ n * H
      have hHn : 0 ≤ Hn := by
        dsimp [Hn]
        exact mul_nonneg (pow_nonneg hc _) hH
      have hM : 0 ≤ a * ‖delta‖ * Hn := by positivity
      have hForce (x : ℝ) (hx : x ∈ Icc (a / 2) a) :
          ‖delta * actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x‖ ≤ (a * ‖delta‖ * Hn) / x := by
        have hxpos : 0 < x := (half_pos ha).trans_le hx.1
        have hPrev :
            ‖actualHartreeBackwardSpectralNeumannIterate
                K a b F U DU delta n x‖ ≤ Hn := ih x hx
        have hConst : 0 ≤ ‖delta‖ * Hn :=
          mul_nonneg (norm_nonneg delta) hHn
        have hMul := mul_le_mul_of_nonneg_left hx.2 hConst
        apply (le_div_iff₀ hxpos).2
        calc
          ‖delta * actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x‖ * x =
              (‖delta‖ *
                ‖actualHartreeBackwardSpectralNeumannIterate
                  K a b F U DU delta n x‖) * x := by rw [norm_mul]
          _ ≤ (‖delta‖ * Hn) * x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hPrev (norm_nonneg delta))
              hxpos.le
          _ ≤ (‖delta‖ * Hn) * a := hMul
          _ = a * ‖delta‖ * Hn := by ring
      have hOne :=
        actual_Hartree_zero_left_original_Green_backward_inverse_linear_bound
          K a b C G (a * ‖delta‖ * Hn) ha hab hb hG hM hK
          hModes
          (fun x => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x)
          hForce r hr (hInt n r hr) (hIntR n)
      calc
        ‖actualHartreeBackwardSpectralNeumannIterate
            K a b F U DU delta (n + 1) r‖ ≤
              2 * G ^ 2 * (a * ‖delta‖ * Hn) := hOne
        _ = c ^ (n + 1) * H := by
          dsimp [c, Hn]
          rw [pow_succ]
          ring


end HBL.TypeIIDynamicSelection
