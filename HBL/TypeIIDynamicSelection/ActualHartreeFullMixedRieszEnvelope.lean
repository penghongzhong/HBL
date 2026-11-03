import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleRadialDecay
import HBL.TypeIIDynamicSelection.ActualHartreeMovingMonopoleMeasurable
import HBL.TypeIIDynamicSelection.ActualMixedQuarticGain
import HBL.TypeIIDynamicSelection.ActualRadiationScaling
import HBL.TypeIIDynamicSelection.ActualHartreeStraussRieszEnvelope
import HBL.RadialHartreeDomination
import HBL.MonopoleCoreIntegrability
import Mathlib.Tactic

/-!
# HBL revised 2.13: full physical mixed quartic Riesz source via one radial envelope

Unlike the compact-terminal source, this argument is valid for every
high-regularity radial Hartree radiation z(t) in a single physical
local time interval. High-regularity L-infinity and the cited Strauss
radial H1 bound give (1+u)|z(t,u)| <= 2(B+A).
The genuinely constructed moving monopole has
(1+r)|V_c(r)| <= 2+9*Cmon, whenever |c|<=1.

For Z_ell(r)=sqrt(ell)*z(t,ell*r), 0<ell<=1, the exact quartic
interaction F_mix=|V_c+Z_ell|^4-|V_c|^4-|Z_ell|^4 satisfies
  |F_mix(r)| <= C(B,A,Cmon)*sqrt(ell)/(1+r^2).
Thus the TRUE radial inverse-square Hartree Riesz potential of the
full mixed quartic density has a globally uniform O(sqrt(ell)) bound
by the already verified physical row-domination theorem.

No source decay order is assumed, no terminal support persistence,
no substitute local cubic and no selected blowup exponent is used.
This is a genuine nonlocal source component, NOT yet the entire
weighted nonlinear residual, C1 interfacial compatibility or the
revised original 2.13 acceptance.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Both the bounded core and the actual compactly cut-off monopole
are controlled by ONE uniform Japanese 1/(1+r) envelope. -/
theorem actual_Hartree_moving_monopole_one_plus_radius_decay
    (c r : ℝ) (hr : 0 < r) (hc : |c| ≤ 1) :
    (1 + r) * |monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c r| ≤
        2 + 9 * monopoleRadialBoundConstant := by
  have hs := monopolePerturbedRadialProfile_abs_le
    (R := monopoleQuadraticRadius c) hr hc
  have hd := actual_Hartree_moving_monopole_global_radial_decay c r hr
  calc
    (1 + r) * |monopolePerturbedRadialProfile
      (monopoleQuadraticRadius c) c r| =
      |monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c r| +
      r * |monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c r| := by ring
    _ ≤ (1 + monopoleRadialBoundConstant) +
          (1 + 8 * monopoleRadialBoundConstant) :=
      add_le_add hs hd
    _ = 2 + 9 * monopoleRadialBoundConstant := by ring

/-- Strauss radial H1 and L-infinity give a GLOBAL decay envelope for
the SAME physical regular Hartree trajectory, not terminal support. -/
theorem actual_Hartree_Strauss_global_one_plus_radius_decay
    (z : ℝ → ℂ) (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ∀ u : ℝ, 0 < u →
      (1 + u) * ‖z u‖ ≤ 2 * (B + A) := by
  intro u hu
  by_cases hsmall : u ≤ 1
  · have hfirst : 1 + u ≤ (2 : ℝ) := by linarith
    have hbound : (1 + u) * ‖z u‖ ≤ 2 * B :=
      mul_le_mul hfirst (hSup u hu) (norm_nonneg _) (by norm_num)
    nlinarith [hbound, hA]
  · have hlarge : 1 ≤ u := le_of_not_ge hsmall
    calc
      (1 + u) * ‖z u‖ = ‖z u‖ + u * ‖z u‖ := by ring
      _ ≤ B + A := add_le_add (hSup u hu) (hStrauss u hlarge)
      _ ≤ 2 * (B + A) := by linarith

/-- The true energy-critical radiation scaling converts that global
physical estimate into a uniform (1+ell*r) spatial envelope. -/
theorem actual_Hartree_scaled_Strauss_global_radial_decay
    (ell r B A : ℝ) (hell : 0 < ell) (hr : 0 < r)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    (1 + ell * r) * ‖rescalePhysicalRadiation ell z r‖ ≤
      2 * (B + A) * Real.sqrt ell := by
  have hsource := actual_Hartree_Strauss_global_one_plus_radius_decay
    z B A hB hA hSup hStrauss (ell * r) (mul_pos hell hr)
  unfold rescalePhysicalRadiation
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg ell)]
  calc
    (1 + ell * r) * (Real.sqrt ell * ‖z (ell * r)‖) =
      Real.sqrt ell * ((1 + ell * r) * ‖z (ell * r)‖) := by ring
    _ ≤ Real.sqrt ell * (2 * (B + A)) :=
      mul_le_mul_of_nonneg_left hsource (Real.sqrt_nonneg ell)
    _ = 2 * (B + A) * Real.sqrt ell := by ring

/-- Algebraic heart of the new proof: two natural radial envelopes,
the actual Hartree quartic expansion, and ell<=1 yield one bubble-squared
majorant with a genuine positive physical power 1/2. -/
theorem actual_Hartree_mixed_quartic_bubble_squared_from_radial_envelopes
    (ell r D E : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (V : ℝ → ℝ) (Z : ℝ → ℂ)
    (hV : (1 + r) * |V r| ≤ D)
    (hZ : (1 + ell * r) * ‖Z r‖ ≤ E * Real.sqrt ell) :
    |actualWholeRadiationMixedQuartic V Z r| ≤
      (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 +
        4 * D * E ^ 3) * Real.sqrt ell * bubble r ^ 2 := by
  let a : ℝ := 1 + r
  let b : ℝ := 1 + ell * r
  let x : ℝ := |V r|
  let y : ℝ := ‖Z r‖
  let s : ℝ := Real.sqrt ell
  have hx : 0 ≤ x := abs_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hb : 1 ≤ b := by dsimp [b]; nlinarith [mul_pos hell hr]
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = ell := Real.sq_sqrt hell.le
  have hsone : s ≤ 1 := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hellOne
  have hells : ell ≤ s := by
    have h := mul_nonneg hs (sub_nonneg.mpr hsone)
    nlinarith [h, hssq]
  have hax : a * x ≤ D := by simpa only [a, x] using hV
  have hby : b * y ≤ E * s := by simpa only [b, y, s] using hZ
  have hx0 : x ≤ D := by
    have hfirst : x ≤ a * x := by
      calc
        x = 1 * x := by ring
        _ ≤ a * x := mul_le_mul_of_nonneg_right ha hx
    exact hfirst.trans hax
  have hy0 : y ≤ E * s := by
    have hfirst : y ≤ b * y := by
      calc
        y = 1 * y := by ring
        _ ≤ b * y := mul_le_mul_of_nonneg_right hb hy
    exact hfirst.trans hby
  have hgeo : 1 + r ^ 2 ≤ a ^ 2 := by
    dsimp [a]
    nlinarith [hr.le]
  have hElla : ell * a ≤ b := by
    dsimp [a, b]
    nlinarith [hellOne]
  have hax2 : a ^ 2 * x ^ 2 ≤ D ^ 2 := by
    calc
      a ^ 2 * x ^ 2 = (a * x) ^ 2 := by ring
      _ ≤ D ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ a) hx) hax 2
  have hxy : x * y ≤ D * (E * s) :=
    mul_le_mul hx0 hy0 hy hD
  have hy2 : y ^ 2 ≤ E ^ 2 * ell := by
    calc
      y ^ 2 ≤ (E * s) ^ 2 := pow_le_pow_left₀ hy hy0 2
      _ = E ^ 2 * ell := by rw [mul_pow, hssq]
  have h1 : (1 + r ^ 2) * x ^ 3 * y ≤ D ^ 3 * E * s := by
    calc
      _ ≤ a ^ 2 * x ^ 3 * y := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgeo (by positivity : 0 ≤ x ^ 3))
          hy
      _ = (a ^ 2 * x ^ 2) * (x * y) := by ring
      _ ≤ D ^ 2 * (D * (E * s)) :=
        mul_le_mul hax2 hxy (by positivity) (by positivity)
      _ = D ^ 3 * E * s := by ring
  have h2 : (1 + r ^ 2) * x ^ 2 * y ^ 2 ≤
      D ^ 2 * E ^ 2 * s := by
    calc
      _ ≤ a ^ 2 * x ^ 2 * y ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgeo (by positivity : 0 ≤ x ^ 2))
          (by positivity : 0 ≤ y ^ 2)
      _ = (a ^ 2 * x ^ 2) * y ^ 2 := by ring
      _ ≤ D ^ 2 * (E ^ 2 * ell) :=
        mul_le_mul hax2 hy2 (by positivity) (by positivity)
      _ ≤ D ^ 2 * (E ^ 2 * s) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hells (sq_nonneg E))
          (sq_nonneg D)
      _ = D ^ 2 * E ^ 2 * s := by ring
  have hby3 : b * y ^ 3 ≤ (E * s) * (E ^ 2 * ell) := by
    calc
      _ = (b * y) * y ^ 2 := by ring
      _ ≤ (E * s) * (E ^ 2 * ell) :=
        mul_le_mul hby hy2 (by positivity) (by positivity)
  have hay3 : a * y ^ 3 ≤ E ^ 3 * s := by
    have hMul : ell * (a * y ^ 3) ≤ ell * (E ^ 3 * s) := by
      calc
        ell * (a * y ^ 3) = (ell * a) * y ^ 3 := by ring
        _ ≤ b * y ^ 3 := mul_le_mul_of_nonneg_right hElla (by positivity)
        _ ≤ (E * s) * (E ^ 2 * ell) := hby3
        _ = ell * (E ^ 3 * s) := by ring
    by_contra hn
    have hgt : E ^ 3 * s < a * y ^ 3 := lt_of_not_ge hn
    have hPos : 0 < ell * (a * y ^ 3 - E ^ 3 * s) :=
      mul_pos hell (sub_pos.mpr hgt)
    nlinarith only [hMul, hPos]
  have h3 : (1 + r ^ 2) * x * y ^ 3 ≤ D * E ^ 3 * s := by
    calc
      _ ≤ a ^ 2 * x * y ^ 3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgeo hx)
          (by positivity : 0 ≤ y ^ 3)
      _ = (a * x) * (a * y ^ 3) := by ring
      _ ≤ D * (E ^ 3 * s) :=
        mul_le_mul hax hay3 (by positivity) hD
      _ = D * E ^ 3 * s := by ring
  have hlinear :
      |4 * V r ^ 3 * (Z r).re| ≤ 4 * x ^ 3 * y := by
    have hre := Complex.abs_re_le_norm (Z r)
    calc
      |4 * V r ^ 3 * (Z r).re| =
          (4 * |V r| ^ 3) * |(Z r).re| := by
        rw [abs_mul, abs_mul, abs_pow]
        norm_num
      _ ≤ (4 * |V r| ^ 3) * ‖Z r‖ :=
        mul_le_mul_of_nonneg_left hre (by positivity)
      _ = 4 * x ^ 3 * y := rfl
  have hpoly :
      |actualWholeRadiationMixedQuartic V Z r| ≤
        4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 := by
    calc
      _ = |4 * V r ^ 3 * (Z r).re +
          actualWholeRadiationMixedHigher V Z r| := by
          rw [actual_whole_radiation_mixed_linear_higher_exact]
      _ ≤ |4 * V r ^ 3 * (Z r).re| +
          |actualWholeRadiationMixedHigher V Z r| := abs_add_le _ _
      _ ≤ 4 * x ^ 3 * y +
          (6 * x ^ 2 + 4 * x * y) * y ^ 2 :=
        add_le_add hlinear (actual_whole_radiation_mixed_higher_abs_le V Z r)
      _ = 4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 +
          4 * x * y ^ 3 := by ring
  have hbound :
      (1 + r ^ 2) * |actualWholeRadiationMixedQuartic V Z r| ≤
        (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 +
          4 * D * E ^ 3) * s := by
    calc
      _ ≤ (1 + r ^ 2) *
        (4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 +
          4 * x * y ^ 3) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 4 * ((1 + r ^ 2) * x ^ 3 * y) +
        6 * ((1 + r ^ 2) * x ^ 2 * y ^ 2) +
        4 * ((1 + r ^ 2) * x * y ^ 3) := by ring
      _ ≤ 4 * (D ^ 3 * E * s) +
        6 * (D ^ 2 * E ^ 2 * s) +
        4 * (D * E ^ 3 * s) :=
        add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num)))
          (mul_le_mul_of_nonneg_left h3 (by norm_num))
      _ = (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 +
          4 * D * E ^ 3) * s := by ring
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hdiv :
      |actualWholeRadiationMixedQuartic V Z r| ≤
        ((4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 +
          4 * D * E ^ 3) * s) / (1 + r ^ 2) :=
    (le_div_iff₀ hden).2 (by
      calc
        |actualWholeRadiationMixedQuartic V Z r| * (1 + r ^ 2) =
            (1 + r ^ 2) * |actualWholeRadiationMixedQuartic V Z r| := by ring
        _ ≤ _ := hbound)
  have hbubble : bubble r ^ 2 = (1 + r ^ 2)⁻¹ := by
    unfold bubble
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  simpa only [s, hbubble, div_eq_mul_inv] using hdiv

/-- Apply the algebraic envelope to the actual physical Hartree
monopole c and genuine critical radiation, not abstract source atoms. -/
theorem actual_Hartree_physical_full_mixed_density_bubble_squared_gain
    (ell c r B A : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    |actualWholeRadiationMixedQuartic
      (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
      (rescalePhysicalRadiation ell z) r| ≤
      (4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
        (2 * (B + A)) +
       6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
        (2 * (B + A)) ^ 2 +
       4 * (2 + 9 * monopoleRadialBoundConstant) *
        (2 * (B + A)) ^ 3) *
        Real.sqrt ell * bubble r ^ 2 := by
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  have hD : 0 ≤ D := by
    dsimp [D]
    have := monopoleRadialBoundConstant_pos
    positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  exact actual_Hartree_mixed_quartic_bubble_squared_from_radial_envelopes
    ell r D E hell hellOne hr hD hE
    (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
    (rescalePhysicalRadiation ell z)
    (actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc)
    (actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss)

/-- The FULL inverse-square nonlocal Hartree Riesz potential of the
complete mixed quartic density has genuine positive O(sqrt(ell))
strength, uniformly over observation radius and high-regularity time,
under standard physical H1 radial and Linfinity inputs. -/
theorem actual_Hartree_full_mixed_nonlinear_Riesz_from_Strauss
    (ell c r B A : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : 0 < r) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho *
        actualWholeRadiationMixedQuartic
          (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
          (rescalePhysicalRadiation ell z) rho)
      (Ioi (0 : ℝ)) ∧
    |radialHartreePotential
      (actualWholeRadiationMixedQuartic
        (monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c)
        (rescalePhysicalRadiation ell z)) r| ≤
      radialHartreeRowBoundConstant *
      (4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
        (2 * (B + A)) +
       6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
        (2 * (B + A)) ^ 2 +
       4 * (2 + 9 * monopoleRadialBoundConstant) *
        (2 * (B + A)) ^ 3) * Real.sqrt ell := by
  let V : ℝ → ℝ :=
    monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let F : ℝ → ℝ := actualWholeRadiationMixedQuartic V Z
  let D : ℝ := 4 * (2 + 9 * monopoleRadialBoundConstant) ^ 3 *
        (2 * (B + A)) +
       6 * (2 + 9 * monopoleRadialBoundConstant) ^ 2 *
        (2 * (B + A)) ^ 2 +
       4 * (2 + 9 * monopoleRadialBoundConstant) *
        (2 * (B + A)) ^ 3
  have hD : 0 ≤ D := by
    dsimp [D]
    have := monopoleRadialBoundConstant_pos
    positivity
  have hV : Measurable V := by
    dsimp [V]
    exact actual_Hartree_moving_monopole_measurable c
  have hZ : Measurable Z := by
    dsimp [Z]
    unfold rescalePhysicalRadiation
    exact measurable_const.mul
      (hz.comp (measurable_const.mul measurable_id))
  have hF : Measurable F := by
    dsimp [F, actualWholeRadiationMixedQuartic]
    have hVc : Measurable (fun u => (V u : ℂ)) :=
      Complex.measurable_ofReal.comp hV
    exact (((hVc.add hZ).norm.pow_const 4).sub
      (hVc.norm.pow_const 4)).sub (hZ.norm.pow_const 4)
  have hEnvelope : ∀ rho : ℝ, 0 < rho →
      |F rho| ≤ (D * Real.sqrt ell) * bubble rho ^ 2 := by
    intro rho hrho
    simpa only [F, V, Z, D, mul_assoc] using
      actual_Hartree_physical_full_mixed_density_bubble_squared_gain
        ell c rho B A hell hellOne hrho hc hB hA
        z hSup hStrauss
  have h := radialHartreePotential_bubble_sq_domination
    F hF (mul_nonneg hD (Real.sqrt_nonneg ell)) hEnvelope hr
  simpa only [F, V, Z, D, mul_assoc] using h

end HBL.TypeIIDynamicSelection
