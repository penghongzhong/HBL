import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedCorrectionResidual
import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylorBubbleBound
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedCrossGain
import HBL.TypeIIDynamicSelection.ActualHartreeFullMixedRieszEnvelope
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import Mathlib.Tactic

/-!
# The actual moment-locked correction remainder is one physical layer higher

This is a direct consumer of the exact physical correction-residual identity.
After subtracting the genuinely linear correction equation, the only terms
left here are:
1. the selected speed increments acting on the correction itself;
2. the exact nonlocal Hartree Taylor remainder.

Both are bounded as actual PDE expressions. No GeneratedTerm tag or assigned
order is used to prove the gain.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

def actualHartreeMomentLockedCorrectionPrincipalPart
    (c : ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega s r : ℝ) : ℂ :=
  Complex.I * deriv (fun t => H t r) s +
    complexRadialLaplacian (H s) r +
    actualHartreeComplexLinearization
      (fun x => (actualMomentLockedCore c x : ℂ)) (H s) r +
    Complex.I * (b : ℂ) * complexRadialDilation (H s) r +
    (omega : ℂ) * H s r +
    (db : ℂ) * actualMomentLockedScaleSource c r +
    (domega : ℂ) * actualMomentLockedPhaseSource c r

def actualHartreeMomentLockedCorrectionGeneratedRemainder
    (c : ℝ) (H : ℝ → ℝ → ℂ)
    (db domega s r : ℝ) : ℂ :=
  Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
    (domega : ℂ) * H s r +
    actualHartreeComplexTaylorRemainder
      (fun x => (actualMomentLockedCore c x : ℂ)) (H s) r

theorem actual_Hartree_moment_locked_core_bubble_envelope
    (c r : ℝ) (hr : 0 < r) (hc : |c| ≤ 1) :
    |actualMomentLockedCore c r| ≤
      (2 + 9 * monopoleRadialBoundConstant) * bubble r := by
  let C : ℝ := 2 + 9 * monopoleRadialBoundConstant
  have hMono : 0 ≤ monopoleRadialBoundConstant :=
    monopoleRadialBoundConstant_pos.le
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  have hdecay :=
    actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hden : 0 < 1 + r := by linarith
  have hbase : 0 < 1 + r ^ 2 := by positivity
  have hsqrtpos : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 hbase
  have hsqrt :
      Real.sqrt (1 + r ^ 2) ≤ 1 + r := by
    have hsq : (Real.sqrt (1 + r ^ 2)) ^ 2 = 1 + r ^ 2 :=
      Real.sq_sqrt hbase.le
    have hs0 : 0 ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_nonneg _
    nlinarith
  have hinv :
      (1 + r)⁻¹ ≤ (Real.sqrt (1 + r ^ 2))⁻¹ :=
    inv_anti₀ hsqrtpos hsqrt
  have hdiv : |actualMomentLockedCore c r| ≤ C / (1 + r) := by
    apply (le_div_iff₀ hden).2
    simpa only [C, actualMomentLockedCore, mul_comm] using hdecay
  calc
    |actualMomentLockedCore c r| ≤ C / (1 + r) := hdiv
    _ = C * (1 + r)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ C * (Real.sqrt (1 + r ^ 2))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hC
    _ = C * bubble r := by rfl

theorem actual_Hartree_moment_locked_correction_generated_remainder_exact
    (c0 c1 : ℝ → ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega m s r : ℝ) (hr : 0 < r)
    (hsame : c1 s = c0 s)
    (hc0 : HasDerivAt c0 (-(b * c0 s) + m) s)
    (hc1 : HasDerivAt c1 (-((b + db) * c1 s) + m) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r) :
    complexRadialRenormalizedResidual
        (fun t x => (actualMomentLockedCore (c1 t) x : ℂ) + H t x)
        (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual
        (fun t x => (actualMomentLockedCore (c0 t) x : ℂ)) b omega s r -
      actualHartreeMomentLockedCorrectionPrincipalPart
        (c0 s) H b omega db domega s r =
      actualHartreeMomentLockedCorrectionGeneratedRemainder
        (c0 s) H db domega s r := by
  have h :=
    actual_Hartree_moment_locked_correction_residual_exact
      c0 c1 H b omega db domega m s r hr
      hsame hc0 hc1 hHtime hHspace hHsecond
  rw [h]
  unfold actualHartreeMomentLockedCorrectionLinearPart
    actualHartreeMomentLockedCorrectionPrincipalPart
    actualHartreeMomentLockedCorrectionGeneratedRemainder
  ring

theorem actual_Hartree_moment_locked_correction_next_physical_layer
    (c0 c1 : ℝ → ℝ) (H : ℝ → ℝ → ℂ)
    (b omega db domega m s r beta rhoStar rho Cspeed CHd CH : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hr : 0 < r)
    (hsame : c1 s = c0 s)
    (hc0 : HasDerivAt c0 (-(b * c0 s) + m) s)
    (hc1 : HasDerivAt c1 (-((b + db) * c1 s) + m) s)
    (hcCore : |c0 s| ≤ 1)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hH : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    let Mcore := 2 + 9 * monopoleRadialBoundConstant
    let kappa := actualHartreePhysicalKappa beta rhoStar
    ‖complexRadialRenormalizedResidual
        (fun t x => (actualMomentLockedCore (c1 t) x : ℂ) + H t x)
        (b + db) (omega + domega) s r -
      complexRadialRenormalizedResidual
        (fun t x => (actualMomentLockedCore (c0 t) x : ℂ)) b omega s r -
      actualHartreeMomentLockedCorrectionPrincipalPart
        (c0 s) H b omega db domega s r‖ ≤
      (Cspeed * (CHd + CH) +
        63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-(rho + kappa)) := by
  dsimp only
  let Mcore : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let kappa : ℝ := actualHartreePhysicalKappa beta rhoStar
  have hkpos : 0 < kappa := by
    dsimp [kappa]
    exact actual_Hartree_physical_kappa_positive
      beta rhoStar hbeta hrhoStar hflat
  have hrho0 : 0 ≤ rho := le_trans hkpos.le hrho
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hMcore : 0 ≤ Mcore := by
    dsimp [Mcore]
    positivity
  let e : ℝ := CH * s ^ (-rho)
  have hsPow0 : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg hCH hsPow0
  have hsPowOne : s ^ (-rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have heCH : e ≤ CH := by
    dsimp [e]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsPowOne hCH
  have hCoreMeas :
      Measurable (fun x : ℝ => (actualMomentLockedCore (c0 s) x : ℂ)) := by
    change Measurable
      (fun x : ℝ => (monopolePerturbedRadialProfile
        (monopoleQuadraticRadius (c0 s)) (c0 s) x : ℂ))
    exact Complex.continuous_ofReal.measurable.comp
      (actual_Hartree_moving_monopole_measurable (c0 s))
  have hCoreB : ∀ x : ℝ, 0 < x →
      ‖(actualMomentLockedCore (c0 s) x : ℂ)‖ ≤ Mcore * bubble x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa only [Mcore] using
      actual_Hartree_moment_locked_core_bubble_envelope
        (c0 s) x hx hcCore
  have hHB : ∀ x : ℝ, 0 < x → ‖H s x‖ ≤ e * bubble x := by
    intro x hx
    simpa only [e, mul_assoc] using hH x hx
  have hTaylor0 :=
    actual_Hartree_complex_Taylor_bubble_bound
      (fun x => (actualMomentLockedCore (c0 s) x : ℂ))
      (H s) hCoreMeas hHmeas Mcore e hMcore he
      hCoreB hHB r hr
  have hsum : Mcore + e ≤ Mcore + CH := by
    linarith only [heCH]
  have hsumPow : (Mcore + e) ^ 5 ≤ (Mcore + CH) ^ 5 :=
    pow_le_pow_left₀ (add_nonneg hMcore he) hsum 5
  have hbubble : 0 ≤ bubble r := bubble_nonneg r
  have hsumCH : 0 ≤ Mcore + CH := add_nonneg hMcore hCH
  have he2 : e ^ 2 = CH ^ 2 * s ^ (-2 * rho) := by
    dsimp [e]
    rw [mul_pow]
    have hp :
        (s ^ (-rho)) ^ 2 = s ^ (-2 * rho) := by
      rw [← Real.rpow_mul_natCast hs0 (-rho) 2]
      congr 1
      ring
    rw [hp]
  have hExp :
      s ^ (-2 * rho) ≤ s ^ (-(rho + kappa)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hTaylor :
      ‖actualHartreeComplexTaylorRemainder
        (fun x => (actualMomentLockedCore (c0 s) x : ℂ)) (H s) r‖ ≤
      (63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-(rho + kappa)) := by
    calc
      _ ≤ 63 * (Mcore + e) ^ 5 * e ^ 2 * bubble r ^ 5 := hTaylor0
      _ ≤ 63 * (Mcore + CH) ^ 5 * e ^ 2 * bubble r ^ 5 := by
        have hfactor : 0 ≤ 63 * e ^ 2 * bubble r ^ 5 := by
          exact mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg e))
            (pow_nonneg hbubble 5)
        calc
          63 * (Mcore + e) ^ 5 * e ^ 2 * bubble r ^ 5 =
              (Mcore + e) ^ 5 * (63 * e ^ 2 * bubble r ^ 5) := by ring
          _ ≤ (Mcore + CH) ^ 5 * (63 * e ^ 2 * bubble r ^ 5) :=
            mul_le_mul_of_nonneg_right hsumPow hfactor
          _ = _ := by ring
      _ = (63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-2 * rho) := by
        rw [he2]
        ring
      _ ≤ (63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-(rho + kappa)) := by
        have hcoef : 0 ≤
            63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (pow_nonneg hsumCH 5))
              (sq_nonneg CH))
            (pow_nonneg hbubble 5)
        exact mul_le_mul_of_nonneg_left hExp hcoef
  have hHpoint : ‖H s r‖ ≤ CH * s ^ (-rho) := by
    calc
      ‖H s r‖ ≤ CH * s ^ (-rho) * bubble r := hH r hr
      _ ≤ CH * s ^ (-rho) * 1 :=
        mul_le_mul_of_nonneg_left (bubble_le_one r)
          (mul_nonneg hCH (Real.rpow_nonneg hs0 _))
      _ = CH * s ^ (-rho) := by ring
  have hSpeedNext :=
    actual_Hartree_speed_cross_next_physical_layer
      H db domega s r beta rhoStar rho Cspeed CHd CH
      hbeta hrhoStar hflat hs hrho hCs hCHd hCH hSpeed hDilation hHpoint
  have hExact :=
    actual_Hartree_moment_locked_correction_generated_remainder_exact
      c0 c1 H b omega db domega m s r hr hsame hc0 hc1
      hHtime hHspace hHsecond
  rw [hExact]
  unfold actualHartreeMomentLockedCorrectionGeneratedRemainder
  calc
    _ ≤ ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
          (domega : ℂ) * H s r‖ +
        ‖actualHartreeComplexTaylorRemainder
          (fun x => (actualMomentLockedCore (c0 s) x : ℂ)) (H s) r‖ :=
      norm_add_le _ _
    _ ≤ (Cspeed * (CHd + CH)) * s ^ (-(rho + kappa)) +
        (63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-(rho + kappa)) :=
      add_le_add hSpeedNext hTaylor
    _ = (Cspeed * (CHd + CH) +
        63 * (Mcore + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-(rho + kappa)) := by ring

end HBL.TypeIIDynamicSelection
