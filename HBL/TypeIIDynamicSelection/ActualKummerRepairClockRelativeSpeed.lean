import HBL.KinematicSliceDynamics
import HBL.TypeIIDynamicSelection.ActualHartreeLockedPhysicalGain
import Mathlib.Tactic

/-!
# The physical Kummer clock forces the actual relative scale speed

The exact self-similar physical Kummer scale is a(s)=sqrt(q(s)).
Its derivative and relative speed must come from the ACTUAL integrated
modulation clock, not an assumed Type-II exponent or independent velocity.

The already audited trapped clock gives
 q(s) >= (A/2)*s,   q'(s)=A+4*h(s),   |h(s)| <= H*s^(-delta).
We prove |a'(s)|/a(s)=O(s^(-1)) and hence the locked positive-order
scale-speed input required by the physical Kummer repair time derivative.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- A positive linearly growing clock with bounded derivative forces
the associated square-root scale to have relative speed O(s^(-1)). -/
theorem actual_Kummer_sqrt_clock_relative_speed_from_physical_derivative
    (q : ℝ → ℝ) (s qdot c C : ℝ)
    (hs : 1 ≤ s) (hc : 0 < c) (hC : 0 ≤ C)
    (hqlow : c * s ≤ q s)
    (hqdot : HasDerivAt q qdot s)
    (hqd : |qdot| ≤ C) :
    let a : ℝ → ℝ := fun t => Real.sqrt (q t)
    let adot := qdot / (2 * a s)
    HasDerivAt a adot s ∧ 0 < a s ∧
      |adot| / a s ≤ (C / c) * s ^ (-1 : ℝ) := by
  dsimp only
  let a : ℝ → ℝ := fun t => Real.sqrt (q t)
  let adot := qdot / (2 * a s)
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hqpos : 0 < q s :=
    (mul_pos hc hspos).trans_le hqlow
  have ha : 0 < a s := Real.sqrt_pos.2 hqpos
  have hsqrtEq : (a s) ^ 2 = q s := Real.sq_sqrt hqpos.le
  have hDer : HasDerivAt a adot s := by
    dsimp [a, adot]
    exact hqdot.sqrt hqpos.ne'
  have hden : 0 < 2 * a s := mul_pos (by norm_num) ha
  have hEq : |adot| / a s = |qdot| / (2 * q s) := by
    dsimp [adot]
    calc
      |qdot / (2 * a s)| / a s =
          (|qdot| / (2 * a s)) / a s := by
        rw [abs_div, abs_of_pos hden]
      _ = |qdot| / ((2 * a s) * a s) := by
        field_simp [ha.ne']
      _ = |qdot| / (2 * q s) := by
        congr 1
        calc
          (2 * a s) * a s = 2 * (a s) ^ 2 := by ring
          _ = 2 * q s := by rw [hsqrtEq]
  have hD : 0 < c * s := mul_pos hc hspos
  have hTwo : c * s ≤ 2 * q s := by linarith [hqlow, hqpos]
  have hCompare :
      |qdot| / (2 * q s) ≤ C / (c * s) := by
    calc
      _ ≤ C / (2 * q s) :=
        div_le_div_of_nonneg_right hqd (by positivity)
      _ ≤ C / (c * s) :=
        div_le_div_of_nonneg_left hC hD hTwo
  have hPower :
      C / (c * s) = (C / c) * s ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    field_simp [hc.ne', hspos.ne']
  exact ⟨hDer, ha, hEq.le.trans (hCompare.trans_eq hPower)⟩

/-- The physical slice-clock concentration coordinate supplies the
relative speed at order one directly from its own equation.
No independent derivative of the Kummer radius is assumed. -/
theorem actual_Kummer_slice_clock_relative_speed
    {A s0 kappa delta H s : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs0 : 0 < s0)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hH : 0 ≤ H)
    (hh : ContinuousOn h (Ici s0))
    (hbound : ∀ t : ℝ, s0 ≤ t → |h t| ≤ H * t ^ (-delta))
    (hsmall : (4 * H / (1 - delta)) * s0 ^ (-delta) ≤ A / 4)
    (hkappa : |kappa| ≤ A * s0 / 4)
    (hs : s0 < s) (hs1 : 1 ≤ s) :
    let q : ℝ → ℝ := HBL.Kinematic.sliceClock A s0 kappa h
    let a : ℝ → ℝ := fun t => Real.sqrt (q t)
    let adot := (A + 4 * h s) / (2 * a s)
    HasDerivAt a adot s ∧ 0 < a s ∧
      |adot| / a s ≤
        ((A + 4 * H * s0 ^ (-delta)) / (A / 2)) *
          s ^ (-1 : ℝ) := by
  dsimp only
  let q : ℝ → ℝ := HBL.Kinematic.sliceClock A s0 kappa h
  let a : ℝ → ℝ := fun t => Real.sqrt (q t)
  let C : ℝ := A + 4 * H * s0 ^ (-delta)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hqbound := HBL.Kinematic.sliceClock_linear_bounds
    h hA hs0 hdelta hdeltaOne hH hbound hsmall hkappa hs.le
  have hqdot : HasDerivAt q (A + 4 * h s) s :=
    HBL.Kinematic.sliceClock_hasDerivAt h hh hs
  have hsPow :
      s ^ (-delta) ≤ s0 ^ (-delta) :=
    Real.rpow_le_rpow_of_nonpos hs0 hs.le (by linarith)
  have hPoint :
      |h s| ≤ H * s0 ^ (-delta) := by
    calc
      _ ≤ H * s ^ (-delta) := hbound s hs.le
      _ ≤ H * s0 ^ (-delta) := mul_le_mul_of_nonneg_left hsPow hH
  have hqd :
      |A + 4 * h s| ≤ C := by
    calc
      _ ≤ |A| + |4 * h s| := abs_add_le _ _
      _ = A + 4 * |h s| := by
        rw [abs_of_pos hA, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      _ ≤ A + 4 * (H * s0 ^ (-delta)) :=
        by
          have hm := mul_le_mul_of_nonneg_left hPoint
            (show (0 : ℝ) ≤ 4 by norm_num)
          linarith only [hm]
      _ = C := by dsimp [C]; ring
  have hRaw :=
    actual_Kummer_sqrt_clock_relative_speed_from_physical_derivative
      q s (A + 4 * h s) (A / 2) C
      hs1 (by positivity) hC hqbound.1 hqdot hqd
  dsimp only at hRaw
  exact hRaw

/-- The same clock-derived relative speed satisfies the current locked
Kummer next-layer exponent, with a constant fixed by the actual path. -/
theorem actual_Kummer_slice_clock_locked_relative_speed
    {A s0 kappa delta H s beta rhoStar : ℝ} (h : ℝ → ℝ)
    (hA : 0 < A) (hs0 : 0 < s0)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hH : 0 ≤ H)
    (hh : ContinuousOn h (Ici s0))
    (hbound : ∀ t : ℝ, s0 ≤ t → |h t| ≤ H * t ^ (-delta))
    (hsmall : (4 * H / (1 - delta)) * s0 ^ (-delta) ≤ A / 4)
    (hkappa : |kappa| ≤ A * s0 / 4)
    (hs : s0 < s) (hs1 : 1 ≤ s)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4) :
    let q : ℝ → ℝ := HBL.Kinematic.sliceClock A s0 kappa h
    let a : ℝ → ℝ := fun t => Real.sqrt (q t)
    let adot := (A + 4 * h s) / (2 * a s)
    let kl := actualHartreeLockedKappa beta rhoStar
    0 < kl ∧ HasDerivAt a adot s ∧ 0 < a s ∧
      |adot| / a s ≤
        ((A + 4 * H * s0 ^ (-delta)) / (A / 2)) *
          s ^ (-kl) := by
  dsimp only
  let kl := actualHartreeLockedKappa beta rhoStar
  let C : ℝ := (A + 4 * H * s0 ^ (-delta)) / (A / 2)
  have hkpos : 0 < kl :=
    actual_Hartree_locked_kappa_positive
      beta rhoStar hbeta hrhoStar hflat
  have hkle : kl ≤ 1 := by
    have h0 := actual_Hartree_locked_kappa_le_repair beta rhoStar
    have h1 : actualKummerRepairCenterTimeGain beta ≤ 1 / 2 := by
      unfold actualKummerRepairCenterTimeGain
      exact min_le_right _ _
    dsimp [kl]
    linarith
  have hRaw :=
    actual_Kummer_slice_clock_relative_speed
      h hA hs0 hdelta hdeltaOne hH hh hbound hsmall hkappa hs hs1
  dsimp only at hRaw
  have hPow :
      s ^ (-1 : ℝ) ≤ s ^ (-kl) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hFinal := (mul_le_mul_of_nonneg_left hPow hC)
  refine ⟨hkpos, hRaw.1, hRaw.2.1, ?_⟩
  exact hRaw.2.2.trans (by simpa only [C, kl] using hFinal)

end HBL.TypeIIDynamicSelection
