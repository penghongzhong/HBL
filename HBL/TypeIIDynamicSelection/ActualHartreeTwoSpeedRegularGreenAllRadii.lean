import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreenAllRadii
import HBL.TypeIIDynamicSelection.ActualOriginGreenIntegrable
import Mathlib.Tactic

/-!
# Actual real two-speed source: WHOLE lower-origin regular Green moment at all radii

The authentic modulation source is the same linear combination of the
original scale/phase generators used by the unique two-channel Cramer
compatibility selector. Both source generators and their Green integrals
are original source distributions, not arbitrary annular forcing.

The previously verified two generator bounds have the sharp physical
O(a B) coefficient order uniformly at EVERY intermediate radius.
Here linearity of the literal original Wronskian Green integral is
proved using its true interval-integrability certificates; the combined
real-speed source moment is then controlled in one formula.

No independent speed bound, growth law, Type-II rate or residual order
is postulated. The next bridge must apply the unique real Hartree
source-produced speed estimate |p1|+|p2| <= C/a*(N+Q).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- For the two literal real-speed outer Hartree generators and any real
two-speed p, the *same* original lower-origin coefficient at every
radius has the sharp O(a B |p|_1) bound without a logarithm or inverse
left-radius loss. The bound is an output of the source integral. -/
theorem actual_Hartree_two_real_speed_regular_Green_moment_all_radii :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
        (G L c a B : ℝ),
        0 ≤ G → 1 ≤ L → 0 < a → B ≤ 1 → B < scale →
        a * |c| ≤ 1 →
        (∀ x ∈ Icc 0 scale,
          ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
          ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G) →
        ∀ (p : ℝ × ℝ) (r : ℝ) (hr : r ∈ Icc (L / a) B),
          let Fsp : ℝ → ℂ :=
            fun x => (-(p.1 : ℂ)) * actualMomentLockedScaledScaleSource a c x +
              (-(p.2 : ℂ)) * actualMomentLockedScaledPhaseSource a c x
          ‖originGreenCoeffB K (L / a) Fsp r‖ ≤
            (Csp * G * a * B) * (|p.1| + |p.2|) := by
  obtain ⟨Csp, hCsp, hAll⟩ :=
    actual_Hartree_speed_regular_Green_coefficients_all_radii
  refine ⟨Csp, hCsp, ?_⟩
  intro mu theta scale K G L c a B hG hL ha hBOne hBR hSmall hbound
  intro p r hr
  dsimp only
  let r0 : ℝ := L / a
  let Psc : ℝ → ℂ := actualMomentLockedScaledScaleSource a c
  let Pph : ℝ → ℂ := actualMomentLockedScaledPhaseSource a c
  let beta : ℂ := -(p.1 : ℂ)
  let gamma : ℂ := -(p.2 : ℂ)
  let Fsp : ℝ → ℂ := fun x => beta * Psc x + gamma * Pph x
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr0 : 0 < r0 := div_pos hLp ha
  have hBasis : OriginBasisOn K r0 r
      (G * (1 / r0 + 1 / r0 ^ 2) + r ^ 2 + 1) :=
    origin_kummer_annulus_bound K r0 r G hr0
      (hr.2.trans_lt hBR) hG hbound
  have hSpeedInt :=
    actual_Hartree_moment_locked_scaled_speed_integrable_on
      a c r0 r ha hr0 (by simpa only [r0] using hr.1)
  have hGreenInt :=
    actual_origin_Green_source_integrability K hBasis hr.1
  have hSourceIntPsc :
      IntervalIntegrable (originGreenSourceB K Psc) volume r0 r :=
    (hGreenInt Psc hSpeedInt.1).2
  have hSourceIntPph :
      IntervalIntegrable (originGreenSourceB K Pph) volume r0 r :=
    (hGreenInt Pph hSpeedInt.2).2
  have hSourceLinear :
      originGreenSourceB K Fsp =
        (fun x => beta * originGreenSourceB K Psc x +
          gamma * originGreenSourceB K Pph x) := by
    funext x
    dsimp [Fsp, originGreenSourceB]
    ring
  have hCoeffLinear :
      originGreenCoeffB K r0 Fsp r =
        beta * originGreenCoeffB K r0 Psc r +
          gamma * originGreenCoeffB K r0 Pph r := by
    unfold originGreenCoeffB
    rw [hSourceLinear,
      intervalIntegral.integral_add
        (hSourceIntPsc.const_mul beta)
        (hSourceIntPph.const_mul gamma)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hOriginal :=
    hAll K G L c a B hG hL ha hBOne hBR hSmall hbound r hr
  have hSpeedPoint :
      ‖originGreenCoeffB K r0 Psc r‖ ≤ Csp * G * a * B ∧
      ‖originGreenCoeffB K r0 Pph r‖ ≤ Csp * G * a * B := by
    simpa only [r0, Psc, Pph] using hOriginal
  have hBeta : ‖beta‖ = |p.1| := by
    dsimp [beta]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hGamma : ‖gamma‖ = |p.2| := by
    dsimp [gamma]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hBound :
      ‖originGreenCoeffB K r0 Fsp r‖ ≤
        (Csp * G * a * B) * (|p.1| + |p.2|) := by
    rw [hCoeffLinear]
    calc
      ‖beta * originGreenCoeffB K r0 Psc r +
          gamma * originGreenCoeffB K r0 Pph r‖ ≤
        ‖beta‖ * ‖originGreenCoeffB K r0 Psc r‖ +
          ‖gamma‖ * ‖originGreenCoeffB K r0 Pph r‖ := by
        simpa only [norm_mul] using
          (norm_add_le
            (beta * originGreenCoeffB K r0 Psc r)
            (gamma * originGreenCoeffB K r0 Pph r))
      _ ≤ ‖beta‖ * (Csp * G * a * B) +
          ‖gamma‖ * (Csp * G * a * B) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSpeedPoint.1 (norm_nonneg beta))
          (mul_le_mul_of_nonneg_left hSpeedPoint.2 (norm_nonneg gamma))
      _ = (Csp * G * a * B) * (|p.1| + |p.2|) := by
        rw [hBeta, hGamma]
        ring
  simpa only [Fsp, beta, gamma, Psc, Pph, r0] using hBound

end HBL.TypeIIDynamicSelection
