import HBL.RetainedFeedbackTail
import Mathlib.Tactic

/-!
# Propagated retained-feedback tail

This is an unnumbered analytic bridge for the repaired HBL backward scheme.
The nonautonomous centre propagator is supplied as the standard Kato--Kisyński
linear-evolution boundary.  The manuscript-specific statement proved here is
the weighted Duhamel estimate: a uniformly bounded propagator preserves the
extra time decay of the retained threshold feedback.

No existence of the HBL orbit or of the centre-stable graph is assumed.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.MainBackward

open HBL.Modulation.TriangularRepair

abbrev CenterEnergySpace := FeedbackEnergySpace

def propagatedFeedbackTail
    (U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] CenterEnergySpace)
    (a b : ℝ → ℝ × ℝ) (s : ℝ) : CenterEnergySpace :=
  -(∫ t in Ioi s, U s t (E t (a t - b t)))

private theorem propagated_source_bound
    {U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace}
    {E : ℝ → (ℝ × ℝ) →L[ℝ] CenterEnergySpace}
    {a b : ℝ → ℝ × ℝ}
    {CU L D p nu s t : ℝ}
    (hCU : 0 ≤ CU) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hs : 0 < s) (hst : s ≤ t)
    (hU : ‖U s t‖ ≤ CU)
    (hE : ‖E t‖ ≤ L * t ^ (-nu))
    (hab : ‖a t - b t‖ ≤ D * t ^ (1 - p)) :
    ‖U s t (E t (a t - b t))‖ ≤
      (CU * L * D) * t ^ (1 - p - nu) := by
  have ht : 0 < t := hs.trans_le hst
  have h1 := (U s t).le_opNorm (E t (a t - b t))
  have h2 := (E t).le_opNorm (a t - b t)
  have h2' : ‖E t (a t - b t)‖ ≤
      (L * D) * (t ^ (-nu) * t ^ (1 - p)) := by
    calc
      ‖E t (a t - b t)‖ ≤ ‖E t‖ * ‖a t - b t‖ := h2
      _ ≤ (L * t ^ (-nu)) * (D * t ^ (1 - p)) :=
        mul_le_mul hE hab (norm_nonneg _) (mul_nonneg hL (Real.rpow_nonneg ht.le _))
      _ = (L * D) * (t ^ (-nu) * t ^ (1 - p)) := by ring
  have h3 : ‖U s t (E t (a t - b t))‖ ≤
      CU * ((L * D) * (t ^ (-nu) * t ^ (1 - p))) := by
    exact h1.trans (mul_le_mul hU h2' (norm_nonneg _) hCU)
  have hp :
      t ^ (-nu) * t ^ (1 - p) = t ^ (1 - p - nu) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [hp] at h3
  nlinarith only [h3]

/-- Exact propagated Duhamel difference bound. -/
theorem propagatedFeedbackTail_difference_bound
    (U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] CenterEnergySpace)
    (a b : ℝ → ℝ × ℝ)
    (s0 p nu CU L D s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hCU : 0 ≤ CU) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hs : s0 ≤ s)
    (hU : ∀ t, s ≤ t → ‖U s t‖ ≤ CU)
    (hE : ∀ t, s ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hab : ∀ t, s ≤ t → ‖a t - b t‖ ≤ D * t ^ (1 - p))
    (hmeas : AEStronglyMeasurable
      (fun t => U s t (E t (a t - b t))) (volume.restrict (Ioi s))) :
    ‖propagatedFeedbackTail U E a b s‖ ≤
      (CU * L * D) / (p + nu - 2) * s ^ (2 - p - nu) := by
  have hsp : 0 < s := hs0.trans_le hs
  have hexp : 1 - p - nu < -1 := by linarith
  have hscalar : IntegrableOn
      (fun t : ℝ => (CU * L * D) * t ^ (1 - p - nu)) (Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt hexp hsp).const_mul (CU * L * D)
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi s),
      ‖U s t (E t (a t - b t))‖ ≤
        (CU * L * D) * t ^ (1 - p - nu) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact propagated_source_bound hCU hL hD hsp ht.le
      (hU t ht.le) (hE t ht.le) (hab t ht.le)
  have hint : IntegrableOn (fun t => U s t (E t (a t - b t))) (Ioi s) :=
    hscalar.mono' hmeas hpoint
  have hI : (∫ t in Ioi s, t ^ (1 - p - nu)) =
      s ^ (2 - p - nu) / (p + nu - 2) := by
    have h1 : -1 - (p + nu - 2) = 1 - p - nu := by ring
    have h2 : -(p + nu - 2) = 2 - p - nu := by ring
    simpa only [h1, h2] using
      (HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
        (s₀ := s) (δ := p + nu - 2) hsp (by linarith))
  unfold propagatedFeedbackTail
  rw [norm_neg]
  calc
    ‖∫ t in Ioi s, U s t (E t (a t - b t))‖
        ≤ ∫ t in Ioi s, (CU * L * D) * t ^ (1 - p - nu) := by
          exact norm_integral_le_of_norm_le hscalar hpoint
    _ = (CU * L * D) *
        (s ^ (2 - p - nu) / (p + nu - 2)) := by
          rw [integral_const_mul, hI]
    _ = (CU * L * D) / (p + nu - 2) * s ^ (2 - p - nu) := by ring

/-- Weighted Lipschitz form used in the joint contraction. -/
theorem propagatedFeedbackTail_difference_weighted
    (U : ℝ → ℝ → CenterEnergySpace →L[ℝ] CenterEnergySpace)
    (E : ℝ → (ℝ × ℝ) →L[ℝ] CenterEnergySpace)
    (a b : ℝ → ℝ × ℝ)
    (s0 p nu CU L D s : ℝ)
    (hs0 : 0 < s0) (hp : 1 < p) (hnu : 2 < nu)
    (hCU : 0 ≤ CU) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hs : s0 ≤ s)
    (hU : ∀ t, s ≤ t → ‖U s t‖ ≤ CU)
    (hE : ∀ t, s ≤ t → ‖E t‖ ≤ L * t ^ (-nu))
    (hab : ∀ t, s ≤ t → ‖a t - b t‖ ≤ D * t ^ (1 - p))
    (hmeas : AEStronglyMeasurable
      (fun t => U s t (E t (a t - b t))) (volume.restrict (Ioi s))) :
    ‖propagatedFeedbackTail U E a b s‖ ≤
      ((CU * L) / (p + nu - 2) * s0 ^ (2 - nu)) * D * s ^ (-p) := by
  have hsp : 0 < s := hs0.trans_le hs
  have h := propagatedFeedbackTail_difference_bound U E a b s0 p nu CU L D s
    hs0 hp hnu hCU hL hD hs hU hE hab hmeas
  have hpow :
      s ^ (2 - p - nu) = s ^ (2 - nu) * s ^ (-p) := by
    rw [← Real.rpow_add hsp]
    congr 1
    ring
  have hmono : s ^ (2 - nu) ≤ s0 ^ (2 - nu) :=
    Real.rpow_le_rpow_of_nonpos hs0 hs (by linarith)
  have hc : 0 ≤ (CU * L * D) / (p + nu - 2) := by
    positivity
  rw [hpow] at h
  calc
    ‖propagatedFeedbackTail U E a b s‖
        ≤ (CU * L * D) / (p + nu - 2) *
            (s ^ (2 - nu) * s ^ (-p)) := h
    _ ≤ (CU * L * D) / (p + nu - 2) *
            (s0 ^ (2 - nu) * s ^ (-p)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hsp.le _)) hc
    _ = ((CU * L) / (p + nu - 2) * s0 ^ (2 - nu)) *
          D * s ^ (-p) := by ring

#print axioms propagatedFeedbackTail_difference_bound
#print axioms propagatedFeedbackTail_difference_weighted

end HBL.MainBackward
