import HBL.PropagatedFeedbackTail
import Mathlib.Tactic

/-!
# Propagated nonlinear and profile-forcing tails

These are generic Duhamel estimates for the final HBL centre map.  The
manuscript-specific residual and Hartree nonlinear bounds enter only through
their explicit pointwise decay constants.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

/-- A nonlinear source difference with one extra time derivative and a
shrinking-ball gain s^{-delta} produces a weighted centre-map Lipschitz
constant of order s0^{-delta}. -/
theorem propagatedNonlinearTail_difference_weighted
    (U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace)
    (G : ℝ → CenterEnergySpace → CenterEnergySpace)
    (q r : ℝ → CenterEnergySpace)
    (s0 p delta CU CN R D s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hdelta : 0 < delta)
    (hCU : 0 ≤ CU) (hCN : 0 ≤ CN) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hs : s0 ≤ s)
    (hU : ∀ t, s ≤ t → ‖U s t‖ ≤ CU)
    (hG : ∀ t, s ≤ t →
      ‖G t (q t) - G t (r t)‖ ≤
        (CN * R * D) * t ^ (-p - 1 - delta))
    (hmeas : AEStronglyMeasurable
      (fun t => U s t (G t (q t) - G t (r t)))
      (volume.restrict (Ioi s))) :
    ‖∫ t in Ioi s, U s t (G t (q t) - G t (r t))‖ ≤
      ((CU * CN * R) / (p + delta) * s0 ^ (-delta)) *
        D * s ^ (-p) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hden : 0 < p + delta := by linarith
  have hexp : -p - 1 - delta < -1 := by linarith
  have hmajor : IntegrableOn
      (fun t : ℝ => (CU * CN * R * D) * t ^ (-p - 1 - delta))
      (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul (CU * CN * R * D)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖U s t (G t (q t) - G t (r t))‖ ≤
        (CU * CN * R * D) * t ^ (-p - 1 - delta) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hUt := (U s t).le_opNorm (G t (q t) - G t (r t))
    have hsrc := hG t ht.le
    calc
      ‖U s t (G t (q t) - G t (r t))‖
          ≤ ‖U s t‖ * ‖G t (q t) - G t (r t)‖ := hUt
      _ ≤ CU * ((CN * R * D) * t ^ (-p - 1 - delta)) := by
        exact mul_le_mul (hU t ht.le) hsrc (norm_nonneg _) hCU
      _ = (CU * CN * R * D) * t ^ (-p - 1 - delta) := by ring
  have hI : (∫ t in Ioi s, t ^ (-p - 1 - delta)) =
      s ^ (-p - delta) / (p + delta) := by
    have h1 : -1 - (p + delta) = -p - 1 - delta := by ring
    have h2 : -(p + delta) = -p - delta := by ring
    simpa only [h1,h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + delta) hsp hden)
  have hraw :
      ‖∫ t in Ioi s, U s t (G t (q t) - G t (r t))‖ ≤
        (CU * CN * R * D) * (s ^ (-p - delta) / (p + delta)) := by
    calc
      ‖∫ t in Ioi s, U s t (G t (q t) - G t (r t))‖
          ≤ ∫ t in Ioi s, (CU * CN * R * D) * t ^ (-p - 1 - delta) := by
            exact norm_integral_le_of_norm_le hmajor hpoint
      _ = (CU * CN * R * D) *
          (s ^ (-p - delta) / (p + delta)) := by
            rw [integral_const_mul, hI]
  have hpow : s ^ (-p - delta) = s ^ (-delta) * s ^ (-p) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  have hmono : s ^ (-delta) ≤ s0 ^ (-delta) :=
    Real.rpow_le_rpow_of_nonpos hs0 hs (by linarith)
  have hc : 0 ≤ (CU * CN * R * D) / (p + delta) := by positivity
  calc
    ‖∫ t in Ioi s, U s t (G t (q t) - G t (r t))‖
        ≤ (CU * CN * R * D) / (p + delta) * s ^ (-p - delta) := by
          calc
            ‖∫ t in Ioi s, U s t (G t (q t) - G t (r t))‖
                ≤ (CU * CN * R * D) *
                    (s ^ (-p - delta) / (p + delta)) := hraw
            _ = (CU * CN * R * D) / (p + delta) *
                  s ^ (-p - delta) := by ring
    _ = (CU * CN * R * D) / (p + delta) *
          (s ^ (-delta) * s ^ (-p)) := by rw [hpow]
    _ ≤ (CU * CN * R * D) / (p + delta) *
          (s0 ^ (-delta) * s ^ (-p)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hsp.le _)) hc
    _ = ((CU * CN * R) / (p + delta) * s0 ^ (-delta)) *
          D * s ^ (-p) := by ring

/-- A path-independent high-order profile forcing has a small weighted
centre tail whenever its decay order N is strictly larger than p+1. -/
theorem propagatedProfileForcing_weighted
    (U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace)
    (F : ℝ → CenterEnergySpace)
    (s0 p N CU CF s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hN : p + 1 < N)
    (hCU : 0 ≤ CU) (hCF : 0 ≤ CF)
    (hs : s0 ≤ s)
    (hU : ∀ t, s ≤ t → ‖U s t‖ ≤ CU)
    (hF : ∀ t, s ≤ t → ‖F t‖ ≤ CF * t ^ (-N))
    (hmeas : AEStronglyMeasurable
      (fun t => U s t (F t)) (volume.restrict (Ioi s))) :
    ‖∫ t in Ioi s, U s t (F t)‖ ≤
      (CU * CF) / (N - 1) * s0 ^ (p + 1 - N) * s ^ (-p) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hNm1 : 0 < N - 1 := by linarith
  have hexp : -N < -1 := by linarith
  have hmajor : IntegrableOn
      (fun t : ℝ => (CU * CF) * t ^ (-N)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul (CU * CF)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖U s t (F t)‖ ≤ (CU * CF) * t ^ (-N) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      ‖U s t (F t)‖ ≤ ‖U s t‖ * ‖F t‖ := (U s t).le_opNorm (F t)
      _ ≤ CU * (CF * t ^ (-N)) :=
        mul_le_mul (hU t ht.le) (hF t ht.le) (norm_nonneg _) hCU
      _ = (CU * CF) * t ^ (-N) := by ring
  have hI : (∫ t in Ioi s, t ^ (-N)) =
      s ^ (1-N) / (N-1) := by
    have h1 : -1 - (N-1) = -N := by ring
    have h2 : -(N-1) = 1-N := by ring
    simpa only [h1,h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀:=s) (δ:=N-1) hsp hNm1)
  have hraw :
      ‖∫ t in Ioi s, U s t (F t)‖ ≤
        (CU * CF) * (s ^ (1-N) / (N-1)) := by
    calc
      ‖∫ t in Ioi s, U s t (F t)‖
          ≤ ∫ t in Ioi s, (CU * CF) * t ^ (-N) :=
            norm_integral_le_of_norm_le hmajor hpoint
      _ = (CU * CF) * (s ^ (1-N)/(N-1)) := by
            rw [integral_const_mul,hI]
  have hpow : s ^ (1-N) = s ^ (p+1-N) * s ^ (-p) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  have hmono : s ^ (p+1-N) ≤ s0 ^ (p+1-N) :=
    Real.rpow_le_rpow_of_nonpos hs0 hs (by linarith)
  have hc : 0 ≤ (CU * CF)/(N-1) := by positivity
  calc
    ‖∫ t in Ioi s, U s t (F t)‖
        ≤ (CU * CF)/(N-1) * s^(1-N) := by
          calc
            ‖∫ t in Ioi s, U s t (F t)‖
                ≤ (CU * CF) * (s^(1-N)/(N-1)) := hraw
            _ = (CU * CF)/(N-1) * s^(1-N) := by ring
    _ = (CU * CF)/(N-1) * (s^(p+1-N) * s^(-p)) := by rw [hpow]
    _ ≤ (CU * CF)/(N-1) * (s0^(p+1-N) * s^(-p)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hsp.le _)) hc
    _ = (CU * CF)/(N-1) * s0^(p+1-N) * s^(-p) := by ring

#print axioms propagatedNonlinearTail_difference_weighted
#print axioms propagatedProfileForcing_weighted

end HBL.MainBackward
