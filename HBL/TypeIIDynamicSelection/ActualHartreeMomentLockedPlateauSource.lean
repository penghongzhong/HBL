import HBL.TypeIIDynamicSelection.ActualHartreeTwoChannelMatchedShell
import HBL.TypeIIDynamicSelection.ActualHartreeCanonicalTransmission
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCoupledCompatibility

/-!
Exact source identification on the plateau of the ORIGINAL inner cutoff.
The two inner channels are the real/imaginary parts of the same radially
conjugated full Hartree interaction, with the actual moment-locked scale
and phase inputs added.  On 0 < y <= L the cutoff equals one, so their
physical source is exactly the full outer forcing after the a^2 pullback.

All Riesz interactions are retained inside the original physical source.
These identities require no source norm, regularity, or free amplitude.
-/
noncomputable section
set_option autoImplicit false
open Set

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- On the full source plateau, the adjusted real and imaginary inner
channels reconstruct the ORIGINAL physical source and both actual speed
directions, with their prescribed real coefficients. -/
theorem actual_Hartree_moment_locked_plateau_physical_source
    (ell c : ℝ) (z : ℝ → ℂ) (y db dw : ℝ)
    (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    actualHartreeTwoChannelPhysicalSource
        (fun r => Fp r + dw * Gp r) (fun r => Fm r + db * Gm r) y =
      actualHartreePhysicalSliceInteraction ell c z y +
        (db : ℂ) * actualMomentLockedScaleSource c y +
        (dw : ℂ) * actualMomentLockedPhaseSource c y := by
  dsimp only
  have hCut := actual_Hartree_inner_source_cutoff_one
    (actualHartreeSlowInnerRadius ell) y hL hyL
  have hPair (v : ℂ) : (v.re : ℂ) + Complex.I * (v.im : ℂ) = v := by
    apply Complex.ext <;> simp
  have hBase : (actualHartreeTransmissionPlusSource ell c z y : ℂ) +
      Complex.I * (actualHartreeTransmissionMinusSource ell c z y : ℂ) =
      (y : ℂ) * actualHartreePhysicalSliceInteraction ell c z y := by
    unfold actualHartreeTransmissionPlusSource actualHartreeTransmissionMinusSource
    rw [hPair]
    unfold actualHartreeRadiallyConjugatedInnerSource
    rw [hCut, mul_one]
  have hSpeed := actual_Hartree_moment_locked_inner_sources_core
    (actualHartreeSlowInnerRadius ell) c y hL ⟨hy, hyL⟩
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  unfold actualHartreeTwoChannelPhysicalSource
  apply (div_eq_iff hyC).2
  push_cast
  linear_combination hBase + (db : ℂ) * hSpeed.1 + (dw : ℂ) * hSpeed.2

/-- The actual Laplacian rescaling of the complete outer source is the
negative of the same adjusted inner physical source throughout the plateau.
In particular the overlap [L/2,L] introduces no source-cutoff mismatch. -/
theorem actual_Hartree_moment_locked_plateau_scaled_source
    (a ell c : ℝ) (z : ℝ → ℂ) (y db dw : ℝ) (ha : 0 < a)
    (hL : 0 < actualHartreeSlowInnerRadius ell)
    (hy : 0 < y) (hyL : y ≤ actualHartreeSlowInnerRadius ell) :
    let L := actualHartreeSlowInnerRadius ell
    let Fp := actualHartreeTransmissionPlusSource ell c z
    let Fm := actualHartreeTransmissionMinusSource ell c z
    let Gp := actualMomentLockedInnerPhaseSource L c
    let Gm := actualMomentLockedInnerScaleSource L c
    let Fo : ℝ → ℂ := fun r =>
      -actualHartreeLaplacianScaledKummerSource a ell c z r -
        (db : ℂ) * actualMomentLockedScaledScaleSource a c r -
        (dw : ℂ) * actualMomentLockedScaledPhaseSource a c r
    ((a ^ 2)⁻¹ : ℝ) • Fo (y / a) +
      actualHartreeTwoChannelPhysicalSource
        (fun r => Fp r + dw * Gp r) (fun r => Fm r + db * Gm r) y = 0 := by
  dsimp only
  have hSource := actual_Hartree_moment_locked_plateau_physical_source
    ell c z y db dw hL hy hyL
  dsimp only at hSource
  rw [hSource]
  have hScale : a * (y / a) = y := by field_simp [ha.ne']
  have hUnit : (((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), Complex.ofReal_one]
  unfold actualHartreeLaplacianScaledKummerSource actualMomentLockedScaledScaleSource
    actualMomentLockedScaledPhaseSource
  rw [hScale]
  simp only [Complex.real_smul]
  linear_combination -(actualHartreePhysicalSliceInteraction ell c z y +
    (db : ℂ) * actualMomentLockedScaleSource c y +
    (dw : ℂ) * actualMomentLockedPhaseSource c y) * hUnit

end HBL.TypeIIDynamicSelection
