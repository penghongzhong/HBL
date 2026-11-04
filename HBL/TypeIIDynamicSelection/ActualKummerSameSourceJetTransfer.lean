import HBL.TypeIIDynamicSelection.ActualKummerTwoInterfaceObstruction
import Mathlib.Tactic

/-!
Quantitative transfer for the SAME original physical Kummer source.
The source-dependent particular solution cancels exactly in a difference
of two Cauchy solutions. The amplification is an explicit expression in
the actual fundamental pair and physical Wronskian, not an assumed
uniform constant. This does not assert simultaneous remote compatibility.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualKummerJetSize
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (t : ℝ) : ℝ :=
  ‖K.phi t‖ + ‖K.dphi t‖ + ‖K.psi t‖ + ‖K.dpsi t‖

def actualKummerJetAmplification
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d : ℝ) : ℝ :=
  actualKummerJetSize K d *
    (actualKummerJetSize K (-d) / ‖localAnnulusWronskian K (-d)‖)

private theorem jetSize_nonneg
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (t : ℝ) :
    0 ≤ actualKummerJetSize K t := by
  unfold actualKummerJetSize
  positivity

private theorem coefficients_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (t : ℝ) (p q : ℂ) :
    ‖actualKummerMatchPhi K t p q‖ + ‖actualKummerMatchPsi K t p q‖ ≤
      (actualKummerJetSize K t / ‖localAnnulusWronskian K t‖) *
        (‖p‖ + ‖q‖) := by
  have hp : ‖p * K.dpsi t - q * K.psi t‖ ≤
      ‖p‖ * ‖K.dpsi t‖ + ‖q‖ * ‖K.psi t‖ := by
    calc
      _ ≤ ‖p * K.dpsi t‖ + ‖q * K.psi t‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have hq : ‖K.phi t * q - K.dphi t * p‖ ≤
      ‖K.phi t‖ * ‖q‖ + ‖K.dphi t‖ * ‖p‖ := by
    calc
      _ ≤ ‖K.phi t * q‖ + ‖K.dphi t * p‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have hsum :
      (‖p‖ * ‖K.dpsi t‖ + ‖q‖ * ‖K.psi t‖) +
        (‖K.phi t‖ * ‖q‖ + ‖K.dphi t‖ * ‖p‖) ≤
      actualKummerJetSize K t * (‖p‖ + ‖q‖) := by
    dsimp [actualKummerJetSize]
    nlinarith [mul_nonneg (norm_nonneg p) (norm_nonneg (K.phi t)),
      mul_nonneg (norm_nonneg p) (norm_nonneg (K.psi t)),
      mul_nonneg (norm_nonneg q) (norm_nonneg (K.dphi t)),
      mul_nonneg (norm_nonneg q) (norm_nonneg (K.dpsi t))]
  unfold actualKummerMatchPhi actualKummerMatchPsi
  rw [norm_div, norm_div]
  calc
    _ ≤ (‖p‖ * ‖K.dpsi t‖ + ‖q‖ * ‖K.psi t‖) /
          ‖localAnnulusWronskian K t‖ +
        (‖K.phi t‖ * ‖q‖ + ‖K.dphi t‖ * ‖p‖) /
          ‖localAnnulusWronskian K t‖ :=
      _root_.add_le_add
        (div_le_div_of_nonneg_right hp (norm_nonneg _))
        (div_le_div_of_nonneg_right hq (norm_nonneg _))
    _ = ((‖p‖ * ‖K.dpsi t‖ + ‖q‖ * ‖K.psi t‖) +
        (‖K.phi t‖ * ‖q‖ + ‖K.dphi t‖ * ‖p‖)) /
          ‖localAnnulusWronskian K t‖ := by ring
    _ ≤ (actualKummerJetSize K t * (‖p‖ + ‖q‖)) /
          ‖localAnnulusWronskian K t‖ :=
      div_le_div_of_nonneg_right hsum (norm_nonneg _)
    _ = _ := by ring

private theorem homogeneous_jet_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (t : ℝ) (a c : ℂ) :
    ‖a * K.phi t + c * K.psi t‖ +
      ‖a * K.dphi t + c * K.dpsi t‖ ≤
      actualKummerJetSize K t * (‖a‖ + ‖c‖) := by
  have hv := norm_add_le (a * K.phi t) (c * K.psi t)
  have hd := norm_add_le (a * K.dphi t) (c * K.dpsi t)
  simp only [norm_mul] at hv hd
  dsimp [actualKummerJetSize]
  nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg (K.psi t)),
    mul_nonneg (norm_nonneg a) (norm_nonneg (K.dpsi t)),
    mul_nonneg (norm_nonneg c) (norm_nonneg (K.phi t)),
    mul_nonneg (norm_nonneg c) (norm_nonneg (K.dphi t))]

/-- Source-independent homogeneous difference, but BOTH solutions retain
exactly the same inhomogeneous physical Kummer Green source F. -/
theorem actual_Kummer_same_source_right_transfer_difference
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (U DU A DA : ℂ) :
    (actualKummerPhysicalRightTransfer K d F U DU).1 -
        (actualKummerPhysicalRightTransfer K d F A DA).1 =
      actualKummerMatchPhi K (-d) (U-A) (DU-DA) * K.phi d +
        actualKummerMatchPsi K (-d) (U-A) (DU-DA) * K.psi d ∧
    (actualKummerPhysicalRightTransfer K d F U DU).2 -
        (actualKummerPhysicalRightTransfer K d F A DA).2 =
      actualKummerMatchPhi K (-d) (U-A) (DU-DA) * K.dphi d +
        actualKummerMatchPsi K (-d) (U-A) (DU-DA) * K.dpsi d := by
  have hshift : z + d - z = d := by ring
  constructor
  · dsimp [actualKummerPhysicalRightTransfer, actualKummerCauchyValue,
      actualKummerLeftMatchPhi, actualKummerLeftMatchPsi,
      actualKummerMatchPhi, actualKummerMatchPsi]
    rw [hshift]
    ring
  · dsimp [actualKummerPhysicalRightTransfer, actualKummerCauchyDeriv,
      actualKummerLeftMatchPhi, actualKummerLeftMatchPsi,
      actualKummerMatchPhi, actualKummerMatchPsi]
    rw [hshift]
    ring

/-- Explicit quantitative transmission of BOTH boundary coordinates.
The positive-annulus hypotheses verify the actual inverse Wronskian.
No constant uniform in a moving annulus is silently postulated. -/
theorem actual_Kummer_same_source_right_transfer_norm_bound
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (U DU A DA : ℂ) :
    localAnnulusWronskian K (-d) ≠ 0 ∧
    0 ≤ actualKummerJetAmplification K d ∧
    ‖(actualKummerPhysicalRightTransfer K d F U DU).1 -
        (actualKummerPhysicalRightTransfer K d F A DA).1‖ +
      ‖(actualKummerPhysicalRightTransfer K d F U DU).2 -
        (actualKummerPhysicalRightTransfer K d F A DA).2‖ ≤
      actualKummerJetAmplification K d * (‖U-A‖ + ‖DU-DA‖) := by
  have ht : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hnonneg : 0 ≤ actualKummerJetAmplification K d :=
    mul_nonneg (jetSize_nonneg K d)
      (div_nonneg (jetSize_nonneg K (-d)) (norm_nonneg _))
  refine ⟨K.wronskian_ne (-d) ht, hnonneg, ?_⟩
  obtain ⟨hv, hs⟩ :=
    actual_Kummer_same_source_right_transfer_difference K d F U DU A DA
  rw [hv, hs]
  calc
    _ ≤ actualKummerJetSize K d *
        (‖actualKummerMatchPhi K (-d) (U-A) (DU-DA)‖ +
          ‖actualKummerMatchPsi K (-d) (U-A) (DU-DA)‖) :=
      homogeneous_jet_norm_le K d _ _
    _ ≤ actualKummerJetSize K d *
        ((actualKummerJetSize K (-d) / ‖localAnnulusWronskian K (-d)‖) *
          (‖U-A‖ + ‖DU-DA‖)) :=
      mul_le_mul_of_nonneg_left (coefficients_norm_le K (-d) _ _)
        (jetSize_nonneg K d)
    _ = _ := by unfold actualKummerJetAmplification; ring

end HBL.TypeIIDynamicSelection
