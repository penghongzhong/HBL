import HBL.TypeIIDynamicSelection.ActualHartreeMatchedExteriorSelected
import Mathlib.Tactic

/-!
# The compatibility-selected speed is controlled by original source data

This exposes a quantitative estimate already used internally by the selected
source-envelope proof.  The same complete obstruction, the same fixed
Fredholm jet and the same full Green integral are retained.  No selected
speed size or obstruction smallness is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_selected_speed_original_bound_region
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 < B)
    (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ r ∈ Icc 0 scale,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ r ∈ Icc 0 scale,
      ‖K.y r‖ ≤ G ∧ ‖K.dy r‖ ≤ G ∧ ‖K.x r‖ ≤ G ∧ ‖K.dx r‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon C : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (F : ℝ → ℂ) (Q : ℝ), 0 ≤ Q →
        IntervalIntegrable F volume (L / a) B →
        (∀ r ∈ Icc (L / a) B, ‖F r‖ ≤ Q / r ^ 2) →
        let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm
        ∃ p : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F p.1 p.2 = 0 ∧
          (∀ q : ℝ × ℝ,
            actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
              Fp Fm hp hm F q.1 q.2 = 0 → q = p) ∧
          |p.1| + |p.2| ≤ (C / a) * (N0 + Q) := by
  obtain ⟨Ls, es, _Cs, hLs, hes, hesOne, _hCs, hSelected⟩ :=
    actual_Hartree_selected_corrected_source_bounds_region
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Li, ei, _hLi, hei, hInverse⟩ :=
    actual_Hartree_moment_locked_coupled_inverse_bound_region
      K D G hD hG hB hBR hcoeff hbound hsmallB
  let CT := actualMomentLockedObstructionTraceConstant D G B
  let CK := 1 + (D + 1) * G * B ^ 2
  let ZC := CT + CK * B
  let C := 1024 * ZC / B ^ 2
  have hCT : 0 ≤ CT := by
    dsimp [CT, actualMomentLockedObstructionTraceConstant,
      actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hCK : 0 ≤ CK := by dsimp [CK]; positivity
  have hZC : 0 ≤ ZC := by dsimp [ZC]; positivity
  have hC : 0 < C := by
    dsimp [C]
    have hz : 0 < ZC + 1 := by linarith
    have hb2 : 0 < B ^ 2 := pow_pos hB 2
    have hraw : 0 < 1024 * (ZC + 1) / B ^ 2 := by positivity
    have hzero : 0 ≤ 1024 / B ^ 2 := by positivity
    by_cases hzc : ZC = 0
    · subst ZC
      simp [C]
    · have hzcpos : 0 < ZC := lt_of_le_of_ne hZC (Ne.symm hzc)
      positivity
  let L0 := max Ls Li
  let epsilon := min es ei
  have hL0 : 6 ≤ L0 := hLs.trans (le_max_left _ _)
  have heps : 0 < epsilon := lt_min hes hei
  have hepsOne : epsilon ≤ 1 := (min_le_left _ _).trans hesOne
  refine ⟨L0, epsilon, C, hL0, heps, hepsOne, hC, ?_⟩
  intro L c a hLp hLarge ha3 hSmall Fp Fm hp hm hcp hcm
    F Q hQ hF hEnvelope
  dsimp only
  have hLargeS : Ls ≤ L := (le_max_left _ _).trans hLarge
  have hLargeI : Li ≤ L := (le_max_right _ _).trans hLarge
  have hSmallS : a * |c| ≤ es := hSmall.trans (min_le_left _ _)
  have hSmallI : a * |c| ≤ ei := hSmall.trans (min_le_right _ _)
  have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
  have hLtwo : 2 < L := by linarith [hL0.trans hLarge]
  have hLone : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  obtain ⟨p, _Qa, hCompat, hUnique, _hQa, hLB, _hEnv, _hSize⟩ :=
    hSelected L c a hLp hLargeS ha3 hSmallS
      Fp Fm hp hm hcp hcm F Q hQ hF hEnvelope
  let N0 := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let E := N0 + Q
  have hN0 : 0 ≤ N0 := add_nonneg
    (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hE : 0 ≤ E := add_nonneg hN0 hQ
  let J0 := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let Z0 := actualMomentLockedIntervalObstruction K (L / a) B F J0.1 J0.2
  have hTrace :=
    actual_Hartree_canonical_baseline_outgoing_trace_bound
      K D G B L a hD hG hBR hLtwo ha3 hLB hcoeff hbound
      Fp Fm hp hm hcp hcm
  have hGreen :=
    (actual_general_source_Green_coefficient_bound
      K D G B (L / a) Q hD hG hQ (div_pos hLp ha) hLB hBR
      hcoeff hbound F hF hEnvelope).2
  have hZ :
      ‖Z0‖ ≤ CT / a * N0 + CK * B * Q := by
    dsimp [Z0, J0]
    exact (norm_sub_le _ _).trans (add_le_add hTrace hGreen)
  have hTpart : CT / a * N0 ≤ CT * E :=
    (mul_le_mul_of_nonneg_right (div_le_self hCT haOne) hN0).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hQ) hCT)
  have hGpart : CK * B * Q ≤ CK * B * E :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN0)
      (mul_nonneg hCK hB.le)
  have hZtotal : ‖Z0‖ ≤ ZC * E :=
    (hZ.trans (add_le_add hTpart hGpart)).trans_eq
      (by dsimp [ZC]; ring)
  have hSpeed0 :=
    hInverse L c a hLp hLargeI ha3 hc hSmallI
      Fp Fm hp hm F hF p.1 p.2 hCompat
  have hSpeed :
      |p.1| + |p.2| ≤
        1024 / (a * B ^ 2) * (ZC * E) :=
    hSpeed0.trans
      (mul_le_mul_of_nonneg_left hZtotal (by positivity))
  refine ⟨p, hCompat, hUnique, ?_⟩
  calc
    |p.1| + |p.2| ≤ 1024 / (a * B ^ 2) * (ZC * E) := hSpeed
    _ = (C / a) * E := by
      dsimp [C]
      field_simp [ha.ne', hB.ne']
      ring
    _ = (C / a) * (N0 + Q) := rfl

end HBL.TypeIIDynamicSelection
