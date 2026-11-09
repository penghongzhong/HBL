import HBL.TypeIIDynamicSelection.ActualHartreeComplexCorrectionResidual
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedCrossGain
import HBL.TypeIIDynamicSelection.ActualHartreePhysicalOneLayerGain
import Mathlib.Tactic

/-!
# One GLOBAL evolving Hartree background: genuine next-layer nonlinear correction

The older moment-locked correction atom simultaneously required globally
identical core-parameter paths and distinct speed ODEs, forcing db*c=0
at interior times. This replacement works on one actual global complex
background U and one genuine correction H, with the original quartic
nonlocal Hartree residual evaluated on U+H and U themselves.

The principal equation includes the scale and phase speed increments
acting on the background U. It deliberately excludes only their cross
terms on H, whose true size is quadratic in the current correction
order. The other remainder is the exact nonlocal Hartree Taylor term.

No equality of two distinct global core paths, prescribed rate, abstract
generated-order tag or assumed bound on the new nonlinear remainder
is used. To close the manuscript's real four-region finite recursion,
U and H must still be produced from the same physical matched profile
and the principal equation must actually be solved in every region.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual linear PDE correction to be solved. Unlike the complete
variation, this excludes only the quadratic speed cross terms on H. -/
def actualHartreeOneGlobalCoreCorrectionPrincipal
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ) : ℂ :=
  actualHartreeComplexCorrectionLinearPart U H b omega db domega s r -
    (Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
      (domega : ℂ) * H s r)

/-- Literal original nonlocal Hartree PDE difference after solving the
principal linearized correction, on ONE globally defined background. -/
def actualHartreeOneGlobalCoreCorrectionRemainder
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ) : ℂ :=
  complexRadialRenormalizedResidual
      (fun t x => U t x + H t x) (b + db) (omega + domega) s r -
    complexRadialRenormalizedResidual U b omega s r -
    actualHartreeOneGlobalCoreCorrectionPrincipal
      U H b omega db domega s r

/-- All actual nonlocal quartic contributions are retained. The only
quadratic terms are the two speed/correction cross terms and the
complete original Hartree Taylor remainder, with no second core path. -/
theorem actual_Hartree_one_global_core_correction_remainder_exact
    (U H : ℝ → ℝ → ℂ) (b omega db domega s r : ℝ)
    (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r) :
    actualHartreeOneGlobalCoreCorrectionRemainder
      U H b omega db domega s r =
    (Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
      (domega : ℂ) * H s r) +
      actualHartreeComplexTaylorRemainder (U s) (H s) r := by
  have hExact :=
    actual_Hartree_complex_correction_residual_exact
      U H b omega db domega s r hr hUtime hHtime
      hUspace hHspace hUsecond hHsecond
  unfold actualHartreeOneGlobalCoreCorrectionRemainder
    actualHartreeOneGlobalCoreCorrectionPrincipal
  rw [hExact]
  ring

/-- Genuine full quartic-Hartree next-order estimate for ANY ONE real
evolving physical background; unlike the old atom it does not force
db*c=0 by globally identifying two incompatible core-parameter paths.
Every premise is a true field/velocity/regularity bound and the
nonlinear remainder itself is NOT an input. -/
theorem actual_Hartree_one_global_core_correction_next_physical_layer
    (U H : ℝ → ℝ → ℂ)
    (b omega db domega s r beta rhoStar rho Cspeed CHd CH M : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4)
    (hs : 1 ≤ s)
    (hrho : actualHartreePhysicalKappa beta rhoStar ≤ rho)
    (hCs : 0 ≤ Cspeed) (hCHd : 0 ≤ CHd) (hCH : 0 ≤ CH)
    (hM : 0 ≤ M) (hr : 0 < r)
    (hUtime : DifferentiableAt ℝ (fun t => U t r) s)
    (hHtime : DifferentiableAt ℝ (fun t => H t r) s)
    (hUspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (U s) x)
    (hHspace : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (H s) x)
    (hUsecond : DifferentiableAt ℝ (deriv (U s)) r)
    (hHsecond : DifferentiableAt ℝ (deriv (H s)) r)
    (hUmeas : Measurable (U s)) (hHmeas : Measurable (H s))
    (hSpeed : |db| + |domega| ≤ Cspeed * s ^ (-rho))
    (hDilation :
      ‖complexRadialDilation (H s) r‖ ≤ CHd * s ^ (-rho))
    (hUB : ∀ x : ℝ, 0 < x → ‖U s x‖ ≤ M * bubble x)
    (hHB : ∀ x : ℝ, 0 < x →
      ‖H s x‖ ≤ CH * s ^ (-rho) * bubble x) :
    ‖actualHartreeOneGlobalCoreCorrectionRemainder
        U H b omega db domega s r‖ ≤
      (Cspeed * (CHd + CH) +
        63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
        s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
  let kappa : ℝ := actualHartreePhysicalKappa beta rhoStar
  have hk : 0 < kappa :=
    actual_Hartree_physical_kappa_positive beta rhoStar hbeta hrhoStar hflat
  have hrho0 : 0 ≤ rho := hk.le.trans hrho
  have hs0 : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
  have hsPow0 : 0 ≤ s ^ (-rho) := Real.rpow_nonneg hs0 _
  have hsPowOne : s ^ (-rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  let e : ℝ := CH * s ^ (-rho)
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg hCH hsPow0
  have heCH : e ≤ CH := by
    dsimp [e]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsPowOne hCH
  have hHBscaled : ∀ x : ℝ, 0 < x → ‖H s x‖ ≤ e * bubble x := by
    intro x hx
    simpa only [e, mul_assoc] using hHB x hx
  have hTaylorRaw :=
    actual_Hartree_complex_Taylor_bubble_bound
      (U s) (H s) hUmeas hHmeas M e hM he hUB hHBscaled r hr
  have hSum : M + e ≤ M + CH := by linarith only [heCH]
  have hSumPow : (M + e) ^ 5 ≤ (M + CH) ^ 5 :=
    pow_le_pow_left₀ (add_nonneg hM he) hSum 5
  have hBubble : 0 ≤ bubble r := bubble_nonneg r
  have hSumCH : 0 ≤ M + CH := add_nonneg hM hCH
  have he2 : e ^ 2 = CH ^ 2 * s ^ (-2 * rho) := by
    dsimp [e]
    rw [mul_pow]
    have hp : (s ^ (-rho)) ^ 2 = s ^ (-2 * rho) := by
      rw [← Real.rpow_mul_natCast hs0 (-rho) 2]
      congr 1
      ring
    rw [hp]
  have hExp :
      s ^ (-2 * rho) ≤ s ^ (-(rho + kappa)) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith [hrho])
  have hTaylor :
      ‖actualHartreeComplexTaylorRemainder (U s) (H s) r‖ ≤
        (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-(rho + kappa)) := by
    calc
      _ ≤ 63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 := hTaylorRaw
      _ ≤ 63 * (M + CH) ^ 5 * e ^ 2 * bubble r ^ 5 := by
        have hfactor : 0 ≤ 63 * e ^ 2 * bubble r ^ 5 := by
          positivity
        calc
          63 * (M + e) ^ 5 * e ^ 2 * bubble r ^ 5 =
              (M + e) ^ 5 * (63 * e ^ 2 * bubble r ^ 5) := by ring
          _ ≤ (M + CH) ^ 5 * (63 * e ^ 2 * bubble r ^ 5) :=
            mul_le_mul_of_nonneg_right hSumPow hfactor
          _ = _ := by ring
      _ = (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-2 * rho) := by
        rw [he2]
        ring
      _ ≤ (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
          s ^ (-(rho + kappa)) := by
        have hCoef : 0 ≤
            63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5 := by positivity
        exact mul_le_mul_of_nonneg_left hExp hCoef
  have hHpoint : ‖H s r‖ ≤ CH * s ^ (-rho) := by
    calc
      ‖H s r‖ ≤ CH * s ^ (-rho) * bubble r := hHB r hr
      _ ≤ CH * s ^ (-rho) * 1 :=
        mul_le_mul_of_nonneg_left (bubble_le_one r)
          (mul_nonneg hCH hsPow0)
      _ = CH * s ^ (-rho) := by ring
  have hCross :=
    actual_Hartree_speed_cross_next_physical_layer
      H db domega s r beta rhoStar rho Cspeed CHd CH
      hbeta hrhoStar hflat hs hrho hCs hCHd hCH
      hSpeed hDilation hHpoint
  have hExact :=
    actual_Hartree_one_global_core_correction_remainder_exact
      U H b omega db domega s r hr
      hUtime hHtime hUspace hHspace hUsecond hHsecond
  rw [hExact]
  calc
    _ ≤ ‖Complex.I * (db : ℂ) * complexRadialDilation (H s) r +
           (domega : ℂ) * H s r‖ +
         ‖actualHartreeComplexTaylorRemainder (U s) (H s) r‖ :=
      norm_add_le _ _
    _ ≤ (Cspeed * (CHd + CH)) * s ^ (-(rho + kappa)) +
         (63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
           s ^ (-(rho + kappa)) :=
      add_le_add hCross hTaylor
    _ = (Cspeed * (CHd + CH) +
         63 * (M + CH) ^ 5 * CH ^ 2 * bubble r ^ 5) *
           s ^ (-(rho + actualHartreePhysicalKappa beta rhoStar)) := by
      dsimp [kappa]
      ring

end HBL.TypeIIDynamicSelection
