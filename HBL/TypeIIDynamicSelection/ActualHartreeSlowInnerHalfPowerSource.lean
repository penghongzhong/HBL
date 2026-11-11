import HBL.TypeIIDynamicSelection.ActualHartreeConjugatedLocalizedInner
import HBL.TypeIIDynamicSelection.ActualHartreeComplexTaylorBubbleBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
The SAME original quartic Hartree interaction on its actual slow inner
partition has length order 1/2, not merely 1/16. The sharper estimate
retains I[W^4]=3W^2 before combining the full ten interaction monomials.
No Riesz/source envelope, time rate, selected orbit or residual gain is
assumed. Only the old physical radiation amplitude and Strauss inputs
remain. Transport, selected speed corrections, moving derivatives and
all other regions are outside this source-component certificate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
open Set MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail
open HBL.Profile.ActualInner HBL.L2Kernel

/-- The actual core potential has inverse-square, rather than only
inverse-radius, decay. This is produced by the exact quartic bubble row. -/
theorem actual_Hartree_moving_core_Riesz_inverse_square
    (c r : ℝ) (hc : |c| ≤ 1) (hr : 0 < r) :
    |radialHartreePotential
      (fun rho => monopolePerturbedRadialProfile
        (monopoleQuadraticRadius c) c rho ^ 4) r| ≤
      6 * (2 + 9 * monopoleRadialBoundConstant) ^ 4 / (1 + r) ^ 2 := by
  let V : ℝ → ℝ := monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    have h := monopoleRadialBoundConstant_pos
    positivity
  have hVmeas : Measurable V := actual_Hartree_moving_monopole_measurable c
  have hDom (rho : ℝ) (hrho : 0 < rho) : |V rho ^ 4| ≤ D ^ 4 * bubble rho ^ 4 := by
    have hV := actual_Hartree_moving_monopole_one_plus_radius_decay c rho hrho hc
    have hs : Real.sqrt (1 + rho ^ 2) ≤ 1 + rho := by
      rw [Real.sqrt_le_iff]
      constructor <;> nlinarith
    have hv : |V rho| ≤ D * bubble rho := by
      unfold bubble
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < Real.sqrt (1 + rho ^ 2))]
      calc
        |V rho| * Real.sqrt (1 + rho ^ 2) ≤ |V rho| * (1 + rho) :=
          mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        _ ≤ D := by simpa only [V, D, mul_comm] using hV
    rw [abs_pow]
    calc
      |V rho| ^ 4 ≤ (D * bubble rho) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hv 4
      _ = D ^ 4 * bubble rho ^ 4 := mul_pow _ _ _
  have hRaw := (actual_Hartree_bubble_four_potential_domination
    (fun rho => V rho ^ 4) (hVmeas.pow_const 4) (pow_nonneg hD 4) hDom hr).2
  have hBubble : bubble r ^ 2 ≤ 2 / (1 + r) ^ 2 := by
    rw [bubble_sq, inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)
      (by positivity : 0 < (1 + r) ^ 2)).2
    nlinarith [sq_nonneg (r - 1)]
  calc
    _ ≤ 3 * D ^ 4 * bubble r ^ 2 := hRaw
    _ ≤ 3 * D ^ 4 * (2 / (1 + r) ^ 2) :=
      mul_le_mul_of_nonneg_left hBubble (by positivity)
    _ = _ := by dsimp [D]; ring

/-- Fixed physical constants, independent of ell, c, observation radius
and the actual radiation field. -/
def actualHartreeSlowInnerHalfPowerConstant (B A : ℝ) : ℝ :=
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let CW : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  let Cm := (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 + 4 * D * E ^ 3) * CW
  let Cz := 2 * (B ^ 4 + A ^ 4) * CW
  let C4 := 6 * D ^ 4
  Cm * (D ^ 3 + 3 * E * (2 * D + 3 * E) ^ 2) +
    3 * Cz * D * (D + 6 * E) ^ 2 + C4 * E * (2 * D + 3 * E) ^ 2

private theorem halfPowerConstant_nonneg (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    0 ≤ actualHartreeSlowInnerHalfPowerConstant B A := by
  have hM := monopoleRadialBoundConstant_pos
  have hW := actualHartreeBubbleSquaredRieszDecayConstant_pos
  dsimp [actualHartreeSlowInnerHalfPowerConstant]
  positivity

private theorem ten_term_core_bound
    (d s D E Cm Cz C4 pm pz pc v z : ℝ)
    (hd : 0 < d) (hs : 0 ≤ s) (ht : s * d ≤ 3)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hCm : 0 ≤ Cm) (hCz : 0 ≤ Cz) (hC4 : 0 ≤ C4)
    (hpm0 : 0 ≤ pm) (hpz0 : 0 ≤ pz) (hpc0 : 0 ≤ pc)
    (hv0 : 0 ≤ v) (hz0 : 0 ≤ z)
    (hpm : pm ≤ Cm * s / d) (hpz : pz ≤ Cz * s ^ 2)
    (hpc : pc ≤ C4 / d ^ 2) (hv : v ≤ D / d) (hz : z ≤ E * s) :
    d ^ 4 * (pm * (v ^ 3 + (2 * v + z) ^ 2 * z) +
      pz * ((v + 2 * z) ^ 2 * v) + pc * ((2 * v + z) ^ 2 * z)) ≤
    (Cm * (D ^ 3 + 3 * E * (2 * D + 3 * E) ^ 2) +
      3 * Cz * D * (D + 6 * E) ^ 2 + C4 * E * (2 * D + 3 * E) ^ 2) * s := by
  have hMono := actual_Hartree_complete_ten_term_polynomial_mono
    pm pz pc v z (Cm * s / d) (Cz * s ^ 2) (C4 / d ^ 2) (D / d) (E * s)
    hpm0 hpz0 hpc0 hv0 hz0 hpm hpz hpc hv hz
  have ht0 : 0 ≤ s * d := mul_nonneg hs hd.le
  have hPoly :
      Cm * (D ^ 3 + (2 * D + E * (s * d)) ^ 2 * (E * (s * d))) +
        Cz * (s * d) * (D + 2 * E * (s * d)) ^ 2 * D +
        C4 * (2 * D + E * (s * d)) ^ 2 * E ≤
      Cm * (D ^ 3 + (2 * D + E * 3) ^ 2 * (E * 3)) +
        Cz * 3 * (D + 2 * E * 3) ^ 2 * D +
        C4 * (2 * D + E * 3) ^ 2 * E := by
    gcongr
  calc
    _ ≤ d ^ 4 * ((Cm * s / d) * ((D / d) ^ 3 + (2 * (D / d) + E * s) ^ 2 * (E * s)) +
        (Cz * s ^ 2) * (((D / d) + 2 * (E * s)) ^ 2 * (D / d)) +
        (C4 / d ^ 2) * ((2 * (D / d) + E * s) ^ 2 * (E * s))) :=
      mul_le_mul_of_nonneg_left hMono (pow_nonneg hd.le 4)
    _ = (Cm * (D ^ 3 + (2 * D + E * (s * d)) ^ 2 * (E * (s * d))) +
        Cz * (s * d) * (D + 2 * E * (s * d)) ^ 2 * D +
        C4 * (2 * D + E * (s * d)) ^ 2 * E) * s := by
      field_simp [hd.ne']
      all_goals ring
    _ ≤ (Cm * (D ^ 3 + (2 * D + E * 3) ^ 2 * (E * 3)) +
        Cz * 3 * (D + 2 * E * 3) ^ 2 * D +
        C4 * (2 * D + E * 3) ^ 2 * E) * s :=
      mul_le_mul_of_nonneg_right hPoly hs
    _ = _ := by ring

private theorem sqrt_scale_times_slow_radius (ell r : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1)
    (hr : r ≤ 2 * actualHartreeSlowInnerRadius ell) :
    Real.sqrt ell * (1 + r) ≤ 3 := by
  have hs1 : Real.sqrt ell ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hellOne
  have hp : Real.sqrt ell * actualHartreeSlowInnerRadius ell = ell ^ (7 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, actualHartreeSlowInnerRadius, ← Real.rpow_add hell]
    norm_num
  have hpow : ell ^ (7 / 16 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow hell.le hellOne (show (0 : ℝ) ≤ 7 / 16 by norm_num)
  have hx := mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg ell)
  nlinarith

/-- On the actual slow source support, all ten terms of the same original
nonlocal interaction have a square-root physical length gain and r^-4
spatial decay. The three Riesz estimates are derived, not assumed. -/
theorem actual_Hartree_slow_inner_physical_half_power
    (ell c r B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hr : 0 < r) (hNear : r ≤ 2 * actualHartreeSlowInnerRadius ell)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    (1 + r) ^ 4 * ‖actualHartreePhysicalSliceInteraction ell c z r‖ ≤
      actualHartreeSlowInnerHalfPowerConstant B A * Real.sqrt ell := by
  let V : ℝ → ℝ := monopolePerturbedRadialProfile (monopoleQuadraticRadius c) c
  let Z : ℝ → ℂ := rescalePhysicalRadiation ell z
  let D : ℝ := 2 + 9 * monopoleRadialBoundConstant
  let E : ℝ := 2 * (B + A)
  let CW : ℝ := actualHartreeBubbleSquaredRieszDecayConstant
  let Cm : ℝ := (4 * D ^ 3 * E + 6 * D ^ 2 * E ^ 2 + 4 * D * E ^ 3) * CW
  let Cz : ℝ := 2 * (B ^ 4 + A ^ 4) * CW
  let C4 : ℝ := 6 * D ^ 4
  let pm := radialHartreePotential (actualWholeRadiationMixedQuartic V Z) r
  let pz := radialHartreePotential (fun rho => ‖Z rho‖ ^ 4) r
  let pc := radialHartreePotential (fun rho => ‖(V rho : ℂ)‖ ^ 4) r
  have hD : 0 ≤ D := by dsimp [D]; have h := monopoleRadialBoundConstant_pos; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hCW : 0 ≤ CW := actualHartreeBubbleSquaredRieszDecayConstant_pos.le
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have hCz : 0 ≤ Cz := by dsimp [Cz]; positivity
  have hC4 : 0 ≤ C4 := by dsimp [C4]; positivity
  have hd : 0 < 1 + r := by linarith
  have hPm : |pm| ≤ Cm * Real.sqrt ell / (1 + r) :=
    actual_Hartree_full_mixed_Riesz_spatial_decay
      ell c r B A hell hellOne hr hc hB hA z hz hSup hStrauss
  have hPz0 : |pz| ≤ Cz * ell / (1 + ell * r) :=
    actual_Hartree_pure_radiation_Riesz_global_scaled_decay
      ell r B A hell hr hB hA z hz hSup hStrauss
  have hPz : |pz| ≤ Cz * (Real.sqrt ell) ^ 2 := by
    rw [Real.sq_sqrt hell.le]
    apply hPz0.trans
    exact div_le_self (mul_nonneg hCz hell.le) (by nlinarith [mul_pos hell hr])
  have hRealQuartic : (fun rho : ℝ => ‖(V rho : ℂ)‖ ^ 4) = (fun rho => V rho ^ 4) := by
    funext rho
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |V rho| ^ 4 = (|V rho| ^ 2) ^ 2 := by ring
      _ = (V rho ^ 2) ^ 2 := by rw [sq_abs]
      _ = V rho ^ 4 := by ring
  have hPc : |pc| ≤ C4 / (1 + r) ^ 2 := by
    dsimp only [pc]
    rw [hRealQuartic]
    exact actual_Hartree_moving_core_Riesz_inverse_square c r hc hr
  have hV : ‖(V r : ℂ)‖ ≤ D / (1 + r) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (le_div_iff₀ hd).2
    simpa only [V, D, mul_comm] using
      actual_Hartree_moving_monopole_one_plus_radius_decay c r hr hc
  have hZ : ‖Z r‖ ≤ E * Real.sqrt ell := by
    have hs := actual_Hartree_scaled_Strauss_global_radial_decay
      ell r B A hell hr hB hA z hSup hStrauss
    have hh : ‖Z r‖ ≤ (1 + ell * r) * ‖Z r‖ := by
      nlinarith [mul_nonneg (mul_pos hell hr).le (norm_nonneg (Z r))]
    exact hh.trans hs
  have hScalar := ten_term_core_bound (1 + r) (Real.sqrt ell) D E Cm Cz C4
    |pm| |pz| |pc| ‖(V r : ℂ)‖ ‖Z r‖ hd (Real.sqrt_nonneg ell)
    (sqrt_scale_times_slow_radius ell r hell hellOne hNear)
    hD hE hCm hCz hC4 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hPm hPz hPc hV hZ
  have hNorm := actual_Hartree_physical_interaction_complete_ten_term_norm_le
    (fun _ : ℝ => V) (fun _ : ℝ => Z) 0 r
  exact (mul_le_mul_of_nonneg_left hNorm (pow_nonneg hd.le 4)).trans hScalar

/-- The ORIGINAL radially conjugated, smoothly partitioned source retains
order 1/2 in its full Japanese weighted pointwise envelope. The cutoff is
applied after the whole nonlocal interaction; no Hartree density is cut. -/
theorem actual_Hartree_conjugated_slow_inner_half_power_pointwise
    (ell c B A : ℝ)
    (hell : 0 < ell) (hellOne : ell ≤ 1) (hc : |c| ≤ 1)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (z : ℝ → ℂ) (hz : Measurable z)
    (hSup : ∀ u : ℝ, 0 < u → ‖z u‖ ≤ B)
    (hStrauss : ∀ u : ℝ, 1 ≤ u → u * ‖z u‖ ≤ A) :
    ∀ r : ℝ, 0 < r →
      affineJapaneseWeight (7 / 4 : ℝ) r *
        ‖actualHartreeRadiallyConjugatedInnerSource
          (actualHartreeSlowInnerRadius ell) ell c z r‖ ≤
      actualHartreeSlowInnerHalfPowerConstant B A * Real.sqrt ell *
        (1 + r) ^ (-(5 / 4 : ℝ)) := by
  intro r hr
  let L := actualHartreeSlowInnerRadius ell
  let K := actualHartreeSlowInnerHalfPowerConstant B A
  let F := actualHartreePhysicalSliceInteraction ell c z
  have hL : 0 < L := Real.rpow_pos_of_pos hell _
  have hK : 0 ≤ K := halfPowerConstant_nonneg B A hB hA
  have hd : 0 < 1 + r := by linarith
  by_cases hNear : r ≤ 2 * L
  · have hF : ‖F r‖ ≤ K * Real.sqrt ell / (1 + r) ^ 4 := by
      apply (le_div_iff₀ (pow_pos hd 4)).2
      simpa only [F, K, mul_comm] using actual_Hartree_slow_inner_physical_half_power
        ell c r B A hell hellOne hc hr hNear hB hA z hz hSup hStrauss
    have hC := actual_Hartree_inner_source_cutoff_range L r
    have hG : ‖actualHartreeRadiallyConjugatedInnerSource L ell c z r‖ ≤
        (1 + r) * ‖F r‖ := by
      unfold actualHartreeRadiallyConjugatedInnerSource
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hr.le hC.1)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      nlinarith
    have hWeight : affineJapaneseWeight (7 / 4 : ℝ) r ≤ (1 + r) ^ (7 / 4 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + r ^ 2)
        (show 1 + r ^ 2 ≤ (1 + r) ^ 2 by nlinarith) (show (0 : ℝ) ≤ 7 / 8 by norm_num)
      have hp : ((1 + r) ^ 2) ^ (7 / 8 : ℝ) = (1 + r) ^ (7 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (1 + r) 2, ← Real.rpow_mul hd.le]
        norm_num
      change (1 + r ^ 2) ^ ((7 / 4 : ℝ) / 2) ≤ _
      norm_num at h ⊢
      exact h.trans_eq hp
    have hPower : (1 + r) ^ (7 / 4 : ℝ) * (1 + r) / (1 + r) ^ 4 =
        (1 + r) ^ (-(5 / 4 : ℝ)) := by
      calc
        _ = (1 + r) ^ ((7 / 4 : ℝ) + 1 - 4) := by
          rw [Real.rpow_sub hd, Real.rpow_add hd, Real.rpow_one]
          norm_num [Real.rpow_natCast]
        _ = _ := by norm_num
    calc
      _ ≤ (1 + r) ^ (7 / 4 : ℝ) * ((1 + r) * ‖F r‖) :=
        mul_le_mul hWeight hG (norm_nonneg _) (Real.rpow_nonneg hd.le _)
      _ ≤ (1 + r) ^ (7 / 4 : ℝ) *
          ((1 + r) * (K * Real.sqrt ell / (1 + r) ^ 4)) := by gcongr
      _ = (K * Real.sqrt ell) *
          ((1 + r) ^ (7 / 4 : ℝ) * (1 + r) / (1 + r) ^ 4) := by ring
      _ = _ := by rw [hPower]
  · have hFar : 2 ≤ r / L := (le_div_iff₀ hL).2 (le_of_lt (lt_of_not_ge hNear))
    have hZero : actualHartreeInnerSourceCutoff L r = 0 := by
      unfold actualHartreeInnerSourceCutoff
      rw [cutoff_one_of_two_le (r / L) hFar]
      ring
    change affineJapaneseWeight (7 / 4 : ℝ) r *
      ‖actualHartreeRadiallyConjugatedInnerSource L ell c z r‖ ≤ _
    simp only [actualHartreeRadiallyConjugatedInnerSource, hZero, mul_zero,
      Complex.ofReal_zero, zero_mul, norm_zero]
    positivity

end HBL.TypeIIDynamicSelection
