import HBL.TypeIIDynamicSelection.ActualHartreeTrueSelectedFullMatchedRadialEnergy
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedRadialH1FromAlgebraicSlope
import Mathlib.Tactic

/-!
# Original quartic Hartree source to genuine 3D radial Hdot1 on matched Kummer annulus

One and the SAME original inverse-square quartic Hartree Riesz source,
the same two original weighted Fredholm channels and the genuine unique
two-real-speed Cramer selector produce the ACTUAL full Cramer-matched
Kummer field. The earlier source-specific theorem bounds its entire
r-weighted radial Green slope, including the Fredholm outgoing trace,
with no inverse moving-left-radius loss.

The preexisting origin Kummer certificate proves that for the genuine
interval-integrable selected source and its compatible left Fredholm jet,
the algebraic Green slope is the actual derivative almost everywhere.
The actual radial ḢH¹ gradient integral in r²dr is then bounded
by (B-r0)*Efull², not by a synthetic regional norm hypothesis.

No independent Fadj envelope, arbitrary speed, external left jet,
arbitrary blowup-time decay exponent, or Type-II law is assumed.
This finite normalized Kummer-region H1 theorem does not by itself
establish the physical rescaled/global four-region energy or the
nonlinear PDE positive-time residual and finite recurrence.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual selected Hartree field: full matched annular 3D Hdot1 energy
derived from one original PDE source, compatibility, its exact a.e.
Kummer derivative and source-produced Fredholm outgoing trace. -/
theorem actual_Hartree_true_selected_full_matched_radial_H1_no_left_radius
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hcoeff : ∀ x ∈ Icc 0 scale,
      ‖originFirstCoeff x‖ + ‖originZeroCoeff mu theta‖ ≤ D)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (hsmallB : ((D + 1) * G + 1 / 4) * B ^ 2 ≤ 1) :
    ∃ L0 epsilon Cn Csel Csp : ℝ,
      6 ≤ L0 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      0 < Cn ∧ 0 < Csel ∧ 0 < Csp ∧
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
        fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
      let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
        ell ^ (1 / 8 : ℝ)
      let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm
      let T : ℝ := ((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ)) +
        (Csp * G * B * Csel) * (N + Q)
      let E : ℝ := (B + 1) * G *
        (1 + (D + 1) * G * B ^ 2) * (Cn * (N + Q)) +
        2 * (D + 1) * G * B ^ 2 * T
      ∃ (p : ℝ × ℝ) (Qa : ℝ),
        actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
          Fp Fm hp hm F0 p.1 p.2 = 0 ∧
        (∀ q : ℝ × ℝ,
          actualMomentLockedCoupledCompatibility K L c hLp a (L / a) B
            Fp Fm hp hm F0 q.1 q.2 = 0 → q = p) ∧
        0 ≤ Qa ∧ Qa ≤ Cn * (N + Q) ∧
        let Gp := actualMomentLockedInnerPhaseSource L c
        let Gm := actualMomentLockedInnerScaleSource L c
        let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
        let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
        let Fpa := fun x => Fp x + p.2 * Gp x
        let Fma := fun x => Fm x + p.1 * Gm x
        let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
        let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
        let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
        let Fadj := fun x => F0 x + (-(p.1 : ℂ)) *
          actualMomentLockedScaledScaleSource a c x +
          (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
        let Cr := 1 + (D + 1) * G * (B ^ 2 + 2)
        let Cf := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
        let Nadj := innerWeightedNorm (7 / 4 : ℝ) Fpa +
          innerWeightedNorm (7 / 4 : ℝ) Fma
        let Efull := E + (B + 1) * G * (Cr * (Cf * Nadj)) +
          2 * (D + 1) * G ^ 2 * B ^ 2 *
            ((L / a) * ‖J.2‖ + (L / a + 1) * ‖J.1‖)
        let W := actualOriginMatchedKummerValue K (L / a) B Fadj J.1 J.2
        (∫ r in Icc (L / a) B, r ^ 2 * ‖deriv W r‖ ^ 2) ≤
          (B - L / a) * Efull ^ 2 := by
  obtain ⟨L0, epsilon, Cn, Csel, Csp,
    hL0, heps, hepsOne, hCn, hCsel, hCsp, hProducer⟩ :=
    actual_Hartree_true_selected_full_matched_radial_energy_no_left_radius
      K D G B hD hG hB hBOne hBR hcoeff hbound hsmallB
  refine ⟨L0, epsilon, Cn, Csel, Csp,
    hL0, heps, hepsOne, hCn, hCsel, hCsp, ?_⟩
  intro L c a hLp hLarge ha3 hSmall hOrder
    Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
    z hz hSup hStrauss
  dsimp only
  let F0 : ℝ → ℂ :=
    fun x => -actualHartreeLaplacianScaledKummerSource a ell c z x
  let Q : ℝ := actualHartreePhysicalWeightedSourceConstant Bz Az *
    ell ^ (1 / 8 : ℝ)
  let N : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fp +
    innerWeightedNorm (7 / 4 : ℝ) Fm
  let T : ℝ := ((8 / 3 : ℝ) * G * Q) * L ^ (-(3 / 8 : ℝ)) +
    (Csp * G * B * Csel) * (N + Q)
  let E : ℝ := (B + 1) * G * (1 + (D + 1) * G * B ^ 2) *
    (Cn * (N + Q)) + 2 * (D + 1) * G * B ^ 2 * T
  obtain ⟨p, Qa, hCompat, hUnique, hQa, hQaBudget, hSlope⟩ :=
    hProducer L c a hLp hLarge ha3 hSmall hOrder
      Fp Fm hp hm hcp hcm Bz Az ell hBz hAz hell hellOne
      z hz hSup hStrauss
  refine ⟨p, Qa, hCompat, hUnique, hQa, hQaBudget, ?_⟩
  let Gp := actualMomentLockedInnerPhaseSource L c
  let Gm := actualMomentLockedInnerScaleSource L c
  let hgp := actual_Hartree_moment_locked_inner_phase_source_weighted L c hLp
  let hgm := actual_Hartree_moment_locked_inner_scale_source_weighted L c hLp
  let Fpa := fun x => Fp x + p.2 * Gp x
  let Fma := fun x => Fm x + p.1 * Gm x
  let hpa := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fp Gp hp hgp p.2
  let hma := innerWeighted_add_smul_mem (7 / 4 : ℝ) Fm Gm hm hgm p.1
  let J := actualMomentLockedCanonicalInnerJet Fpa Fma hpa hma a (L / a)
  let Fadj : ℝ → ℂ := fun x =>
    F0 x + (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
      (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
  let Cr : ℝ := 1 + (D + 1) * G * (B ^ 2 + 2)
  let Cf : ℝ := actualInnerShellValueConstant + actualInnerShellDerivativeConstant
  let Nadj : ℝ := innerWeightedNorm (7 / 4 : ℝ) Fpa +
    innerWeightedNorm (7 / 4 : ℝ) Fma
  let Efull : ℝ := E + (B + 1) * G * (Cr * (Cf * Nadj)) +
    2 * (D + 1) * G ^ 2 * B ^ 2 *
      ((L / a) * ‖J.2‖ + (L / a + 1) * ‖J.1‖)
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hr0 : 0 < L / a := div_pos hLp ha
  have hLone : 1 ≤ L := by linarith
  have haOne : 1 ≤ a := (one_le_pow₀ hLone).trans ha3
  have hc : |c| ≤ 1 := by
    have hSmallOne : a * |c| ≤ 1 := hSmall.trans hepsOne
    have hca : |c| ≤ a * |c| := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right haOne (abs_nonneg c))
    exact hca.trans hSmallOne
  have hFI0 : IntervalIntegrable F0 volume (L / a) B :=
    (actual_Hartree_scaled_Kummer_source_intervalIntegrable
      Bz Az ell c a (L / a) B hBz hAz hell hellOne hc
      ha hr0 hOrder z hz hSup hStrauss).neg
  have hSpeedInt := actual_Hartree_moment_locked_scaled_speed_integrable_on
    a c (L / a) B ha hr0 hOrder
  have hFI : IntervalIntegrable Fadj volume (L / a) B := by
    have hSum : IntervalIntegrable
        (fun x => (-(p.1 : ℂ)) *
            actualMomentLockedScaledScaleSource a c x +
          (-(p.2 : ℂ)) *
            actualMomentLockedScaledPhaseSource a c x)
        volume (L / a) B :=
      (hSpeedInt.1.const_mul (-(p.1 : ℂ))).add
        (hSpeedInt.2.const_mul (-(p.2 : ℂ)))
    simpa only [Fadj, add_assoc] using hFI0.add hSum
  have hCompatOb :
      actualMomentLockedIntervalObstruction K (L / a) B
        Fadj J.1 J.2 = 0 := by
    change actualMomentLockedIntervalObstruction K (L / a) B
      (fun x => F0 x -
        (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
        (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x)
        J.1 J.2 = 0 at hCompat
    have hEq : (fun x => F0 x -
        (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
        (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x) =
        Fadj := by
      funext x
      dsimp [Fadj]
      ring
    simpa only [hEq] using hCompat
  have hK : OriginBasisOn K (L / a) B
      (G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1) :=
    origin_kummer_annulus_bound K (L / a) B G hr0 hBR hG hbound
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg
      (actualHartreePhysicalWeightedSourceConstant_nonneg Bz Az hBz hAz)
      (Real.rpow_nonneg hell.le _)
  have hN : 0 ≤ N :=
    add_nonneg (innerWeightedNorm_nonneg _ _)
      (innerWeightedNorm_nonneg _ _)
  have hNadj : 0 ≤ Nadj :=
    add_nonneg (innerWeightedNorm_nonneg _ _)
      (innerWeightedNorm_nonneg _ _)
  have hT : 0 ≤ T := by
    dsimp [T]
    have hLpow : 0 ≤ L ^ (-(3 / 8 : ℝ)) := Real.rpow_nonneg hLp.le _
    positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCf : 0 ≤ Cf := by
    dsimp [Cf, actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hEfull : 0 ≤ Efull := by dsimp [Efull]; positivity
  have hPoint : ∀ r ∈ Icc (L / a) B,
      ‖(r : ℂ) * actualOriginMatchedKummerSlope
        K (L / a) B Fadj J.1 J.2 r‖ ≤ Efull := by
    intro r hr
    simpa only [Efull, E, Fadj, F0, Q, N, T, J, Cr, Cf, Nadj,
      Gp, Gm, Fpa, Fma, hgp, hgm, hpa, hma] using hSlope r hr
  have hInt :=
    actual_Hartree_matched_radial_H1_of_algebraic_slope_bound
      K (L / a) B
      (G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1)
      Efull hOrder hEfull hK Fadj hFI J.1 J.2 hCompatOb hPoint
  simpa only [Fadj, F0, Q, N, T, E, Cr, Cf, Nadj, Efull, J,
    Gp, Gm, Fpa, Fma, hgp, hgm, hpa, hma] using hInt

end HBL.TypeIIDynamicSelection
