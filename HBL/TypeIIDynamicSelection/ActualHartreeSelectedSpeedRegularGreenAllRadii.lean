import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSpeedSelection
import HBL.TypeIIDynamicSelection.ActualHartreeTwoSpeedRegularGreenAllRadii
import Mathlib.Tactic

/-!
# Original 3D Hartree source and unique real Cramer speed -> regular Green moment

The UNIQUE real two-channel modulation speed is produced by the same
literal inverse-square quartic nonlocal Hartree source F0, with the
previously strict verified physical estimate
  |p1|+|p2| <= (Csel/a)*(N_Fredholm+Q_Hartree).
The original two real modulation forcing profiles have a genuine
O(a/r) envelope; their original regular Green coefficient is derived
with the sharp O(a B) source integral bound, uniformly at every radius.

This file composes the two source-faithful producers with the SAME
selected speed p; the moving scale a cancels algebraically. There is
no independently imposed bound on p, no guessed time decay and no
preassigned Type-II law. The original F0 regular Green term and
literal time-dependent four-region PDE matching are separate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- Same genuine original physical Hartree source, same uniquely compatible
real two-speed: its ENTIRE lower-origin regular Green moment is controlled
at all Kummer radii solely by the original physical Fredholm and Riesz
source norms, with no scale a or shrinking left radius. -/
theorem actual_Hartree_true_source_selected_regular_Green_moment_all_radii
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon Csel Csp : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < Csel ∧ 0 < Csp ∧
      ∀ (L c a : ℝ) (hLp : 0 < L),
        L0 ≤ L → L ^ 3 ≤ a → a * |c| ≤ epsilon →
        L / a ≤ B →
      ∀ (Fp Fm : ℝ → ℝ)
        (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
        (hm : InWeightedL2 (7 / 4 : ℝ) Fm),
        Continuous Fp → Continuous Fm →
      ∀ (Bz Az ell : ℝ), 0 ≤ Bz → 0 ≤ Az →
        0 < ell → ell ≤ 1 →
      ∀ (z : ℝ → ℂ), Measurable z →
        (∀ y : ℝ, 0 < y → ‖z y‖ ≤ Bz) →
        (∀ y : ℝ, 1 ≤ y → y * ‖z y‖ ≤ Az) →
      let F0 : ℝ → ℂ :=
        fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
      let Q : ℝ :=
        actualHartreePhysicalWeightedSourceConstant Bz Az *
          ell ^ (1 / 8 : ℝ)
      let N : ℝ :=
        innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm
      ∃ p : ℝ × ℝ,
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        ∀ r ∈ Icc (L / a) B,
          let Fsp : ℝ → ℂ :=
            fun x => (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originGreenCoeffB K (L / a) Fsp r‖ ≤
            (Csp * G * B * Csel) * (N + Q) := by
  obtain ⟨L0, epsilon, Csel,
    hL0, heps, hepsOne, hCsel, hSelected⟩ :=
    actual_Hartree_true_nonlocal_source_selects_unique_real_speed
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  obtain ⟨Csp, hCsp, hRegular⟩ :=
    actual_Hartree_two_real_speed_regular_Green_moment_all_radii
  refine ⟨L0, epsilon, Csel, Csp,
    hL0, heps, hepsOne, hCsel, hCsp, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F0 : ℝ → ℂ :=
    fun r => -actualHartreeLaplacianScaledKummerSource a ell c z r
  let Q : ℝ :=
    actualHartreePhysicalWeightedSourceConstant Bz Az * ell ^ (1 / 8 : ℝ)
  let N : ℝ :=
    innerWeightedNorm (7 / 4 : ℝ) Fp +
      innerWeightedNorm (7 / 4 : ℝ) Fm
  obtain ⟨p, hCompat, hUnique, hSpeed⟩ :=
    hSelected L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  refine ⟨p, hCompat, hUnique, ?_⟩
  have hLone : 1 ≤ L := by linarith
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
  have hCoefficientPos : 0 ≤ Csp * G * a * B := by positivity
  intro r hr
  let Fsp : ℝ → ℂ :=
    fun x => (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  have hRaw :
      ‖originGreenCoeffB K (L / a) Fsp r‖ ≤
        (Csp * G * a * B) * (|p.1| + |p.2|) := by
    simpa only [Fsp] using
      (hRegular K G L c a B hG hLone ha hBOne hBR
        hSmallOne hbound p r hr)
  calc
    ‖originGreenCoeffB K (L / a) Fsp r‖ ≤
        (Csp * G * a * B) * (|p.1| + |p.2|) := hRaw
    _ ≤ (Csp * G * a * B) * ((Csel / a) * (N + Q)) :=
      mul_le_mul_of_nonneg_left hSpeed hCoefficientPos
    _ = (Csp * G * B * Csel) * (N + Q) := by
      field_simp [ha.ne']

end HBL.TypeIIDynamicSelection
