import HBL.TypeIIDynamicSelection.ActualHartreeTrueSourceSelectedZeroLeftEnergySlope
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedSlopeFromTraceEnergyBound
import HBL.TypeIIDynamicSelection.ActualHartreeFredholmOutgoingNoRadiusLoss
import Mathlib.Tactic

/-!
# TRUE same-selector full matched Hartree Kummer radial-energy slope

This is the physical source-specific counterpart of the exact Cramer
full-matched Green/Volterra radial-slope transport theorem. The genuine
original inverse-square quartic Hartree Riesz source F0 and its original
two Fredholm channels choose exactly ONE UNIQUE real Cramer speed p.
Both the zero-left adjusted Green energy budget and the Fredholm left
outgoing trace are then constructed from that SAME speed.

The full matched Kummer continuation has an outgoing original Green
trace J_-(r0), not a vanishing outgoing coefficient at every interior
point. This trace is derived from the corrected Fredholm source and
has the crucial factor r0. Its product with the O(r^-2) singular mode
derivative has a bounded r-weighted energy coordinate for all r>=r0.
The regular homogeneous coefficient also comes from the same left jet.

No independent regular Kummer energy norm, outgoing-jet norm, generated
source order, upper time decay, moving-basis differentiability or Type-II
blowup exponent is introduced. This is an honest fixed-time matched
algebraic radial-energy estimate; the C1/a.e. identification and full
time-dependent nonlinear four-region remainder are still outstanding.
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

/-- The full TRUE source-selected matched radial-energy slope, not merely
its zero-left surrogate, has no inverse moving left-radius loss. The
Fredholm outgoing trace is constructed from the same unique speed. -/
theorem actual_Hartree_true_selected_full_matched_radial_energy_no_left_radius
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
        ∀ r ∈ Icc (L / a) B,
          ‖(r : ℂ) * actualOriginMatchedKummerSlope
            K (L / a) B Fadj J.1 J.2 r‖ ≤
            E + (B + 1) * G * (Cr * (Cf * Nadj)) +
              2 * (D + 1) * G ^ 2 * B ^ 2 *
                ((L / a) * ‖J.2‖ + (L / a + 1) * ‖J.1‖) := by
  obtain ⟨L0, epsilon, Cn, Csel, Csp,
    hL0, heps, hepsOne, hCn, hCsel, hCsp, hPhysical⟩ :=
    actual_Hartree_true_source_unique_speed_zero_left_energy_slope
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
    hPhysical L c a hLp hLarge ha3 hSmall hOrder
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
  have ha : 0 < a := (pow_pos hLp 3).trans_le ha3
  have hLpTwo : 2 < L := by linarith
  have hr0 : 0 < L / a := div_pos hLp ha
  have hK : OriginBasisOn K (L / a) B
      (G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1) :=
    origin_kummer_annulus_bound K (L / a) B G hr0 hBR hG hbound
  have hSrcCont := actual_Hartree_moment_locked_inner_sources_continuous L c
  have hcpa : Continuous Fpa := by
    dsimp [Fpa, Gp]
    exact hcp.add (continuous_const.mul hSrcCont.2)
  have hcma : Continuous Fma := by
    dsimp [Fma, Gm]
    exact hcm.add (continuous_const.mul hSrcCont.1)
  have hTraceRaw :=
    actual_Hartree_original_Fredholm_outgoing_trace_source_radius_gain
      K D G B L a hD hG hB hBOne hBR.le hcoeff hbound
      hLpTwo ha hOrder Fpa Fma hpa hma hcpa hcma
  have hTrace :
      ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
        (Cr * (Cf * Nadj)) * (L / a) := by
    have hRaw :
        ‖actualOriginOutgoingTrace K (L / a) J.1 J.2‖ ≤
          Cr * (L / a) * (Cf * Nadj) := by
      simpa only [J, Cr, Cf, Nadj] using hTraceRaw
    calc
      _ ≤ Cr * (L / a) * (Cf * Nadj) := hRaw
      _ = (Cr * (Cf * Nadj)) * (L / a) := by ring
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCf : 0 ≤ Cf := by
    dsimp [Cf, actualInnerShellValueConstant, actualInnerShellDerivativeConstant]
    positivity
  have hNadj : 0 ≤ Nadj := by
    dsimp [Nadj]
    exact add_nonneg (innerWeightedNorm_nonneg _ _) (innerWeightedNorm_nonneg _ _)
  have hCt : 0 ≤ Cr * (Cf * Nadj) := by positivity
  intro r hr
  have hZero : ‖(r : ℂ) *
      actualOriginMatchedKummerSlope K (L / a) B Fadj 0 0 r‖ ≤ E := by
    simpa only [Fadj, E, F0, Q, N, T] using hSlope r hr
  have hFull :=
    actual_Hartree_full_matched_radial_energy_from_zero_left_and_jet
      K (L / a) B
      (G * (1 / (L / a) + 1 / (L / a) ^ 2) + B ^ 2 + 1)
      D G E (Cr * (Cf * Nadj)) hr0 hOrder hBR
      hD hG hCt hK hcoeff hbound Fadj J.1 J.2
      (by
        have hDef :
            (fun x => F0 x -
              (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
              (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x) =
            Fadj := by
          funext x
          dsimp [Fadj]
          ring
        change actualMomentLockedIntervalObstruction K (L / a) B
          (fun x => F0 x -
            (p.1 : ℂ) * actualMomentLockedScaledScaleSource a c x -
            (p.2 : ℂ) * actualMomentLockedScaledPhaseSource a c x)
          J.1 J.2 = 0 at hCompat
        simpa only [hDef] using hCompat)
      hTrace r hr hZero
  simpa only [Fadj, J, Gp, Gm, Fpa, Fma, hgp, hgm, hpa, hma,
    F0, Q, N, T, E, Cr, Cf, Nadj] using hFull

end HBL.TypeIIDynamicSelection
