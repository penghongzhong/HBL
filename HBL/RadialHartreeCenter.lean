import HBL.RadialHartreeMultipole
import HBL.RadialHartreeDomination
import HBL.RadialHartreeBubbleExact
import HBL.AffineTailSecondRationalIntegral

/-! A full center expansion of the actual radial Hartree potential.
The hypotheses are measurability, radial `dr` integrability and quadratic
flatness of the density. The density need not vanish near the origin.
The proof derives absolute convergence before splitting the actual integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- The genuine center value, separate from the original total quotient at zero. -/
def radialHartreeCenter (F : ℝ → ℝ) : ℝ :=
  4 * Real.pi * hartreeKappa * ∫ rho in Ioi (0 : ℝ), F rho

/-- Subtract the actual integrable bubble density with the same center value. -/
def radialHartreeCenteredDensity (F : ℝ → ℝ) (rho : ℝ) : ℝ :=
  F rho - F 0 * bubble rho ^ 4

private theorem bubble_four_dr_integrable :
    IntegrableOn (fun rho : ℝ => bubble rho ^ 4) (Ioi 0) := by
  convert second_rational_integrableOn using 1
  funext rho
  rw [show bubble rho ^ 4 = (bubble rho ^ 2) ^ 2 by ring, bubble_sq, inv_pow]

private theorem bubble_four_dr_mass :
    (∫ rho in Ioi (0 : ℝ), bubble rho ^ 4) = Real.pi / 4 := by
  convert second_rational_integral using 2
  funext rho
  rw [show bubble rho ^ 4 = (bubble rho ^ 2) ^ 2 by ring, bubble_sq, inv_pow]

private theorem bubble_four_flat (rho : ℝ) :
    |1 - bubble rho ^ 4| ≤ 2 * rho ^ 2 := by
  have hb := bubble_abs_le_one rho
  have hbn : 0 ≤ bubble rho := by unfold bubble; positivity
  have hb1 : bubble rho ≤ 1 := (le_abs_self _).trans hb
  have hp : 0 ≤ bubble rho ^ 2 := sq_nonneg _
  have hp1 : bubble rho ^ 2 ≤ 1 := by nlinarith
  have heq : (1 - bubble rho ^ 2) * (1 + rho ^ 2) = rho ^ 2 := by
    rw [bubble_sq]
    field_simp [(by positivity : (1 + rho ^ 2 : ℝ) ≠ 0)]
    ring
  have he : 1 - bubble rho ^ 2 ≤ rho ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg rho)]
  have hf : bubble rho ^ 4 ≤ 1 := by nlinarith [sq_nonneg (1 - bubble rho ^ 2)]
  rw [abs_of_nonneg (sub_nonneg.mpr hf)]
  nlinarith [sq_nonneg (1 - bubble rho ^ 2)]

/-- Subtraction of the actual bubble derives a quadratically vanishing density
from raw flatness, without assuming a potential estimate. -/
theorem radialHartreeCenteredDensity_flat
    (F : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |F rho - F 0| ≤ B * rho ^ 2)
    {rho : ℝ} (hrho : 0 < rho) (htop : rho ≤ 2) :
    |radialHartreeCenteredDensity F rho| ≤ (B + 2 * |F 0|) * rho ^ 2 := by
  have _ := hB
  have heq : radialHartreeCenteredDensity F rho =
      (F rho - F 0) + F 0 * (1 - bubble rho ^ 4) := by
    unfold radialHartreeCenteredDensity
    ring
  rw [heq]
  calc
    |(F rho - F 0) + F 0 * (1 - bubble rho ^ 4)| ≤
        |F rho - F 0| + |F 0 * (1 - bubble rho ^ 4)| := abs_add_le _ _
    _ = |F rho - F 0| + |F 0| * |1 - bubble rho ^ 4| := by rw [abs_mul]
    _ ≤ B * rho ^ 2 + |F 0| * (2 * rho ^ 2) :=
      add_le_add (hflat rho hrho htop)
        (mul_le_mul_of_nonneg_left (bubble_four_flat rho) (abs_nonneg _))
    _ = _ := by ring

private theorem centered_measurable (F : ℝ → ℝ) (hf : Measurable F) :
    Measurable (radialHartreeCenteredDensity F) :=
  hf.sub (measurable_const.mul (bubble_contDiff_infty.continuous.measurable.pow_const 4))

private theorem centered_integrable (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi 0)) :
    IntegrableOn (radialHartreeCenteredDensity F) (Ioi 0) :=
  hF.sub (bubble_four_dr_integrable.const_mul (F 0))

private theorem flat_weighted_integrable
    (G : ℝ → ℝ) (hg : Measurable G) (hG : IntegrableOn G (Ioi 0))
    {A : ℝ} (_hA : 0 ≤ A)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |G rho| ≤ A * rho ^ 2) :
    IntegrableOn (fun rho => |G rho| / rho ^ 2) (Ioi 0) := by
  have hconst : IntegrableOn (fun _ : ℝ => A) (Ioc (0 : ℝ) 2) :=
    integrableOn_const (by simp)
  have hind : IntegrableOn ((Ioc (0 : ℝ) 2).indicator (fun _ : ℝ => A)) (Ioi 0) :=
    (hconst.integrable_indicator measurableSet_Ioc).integrableOn
  have habs : Measurable (fun rho => |G rho|) := by
    simpa only [Real.norm_eq_abs] using hg.norm
  have hm : Measurable (fun rho => |G rho| / rho ^ 2) :=
    habs.div (measurable_id.pow_const 2)
  apply (hind.add hG.abs).mono' hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (sq_nonneg _))]
  simp only [Pi.add_apply]
  by_cases ht : rho ≤ 2
  · rw [indicator_of_mem (show rho ∈ Ioc (0 : ℝ) 2 from ⟨hrho, ht⟩)]
    have hdiv : |G rho| / rho ^ 2 ≤ A :=
      (div_le_iff₀ (sq_pos_of_pos hrho)).2 (hflat rho hrho ht)
    linarith [abs_nonneg (G rho)]
  · rw [indicator_of_notMem (show rho ∉ Ioc (0 : ℝ) 2 from fun h => ht h.2), zero_add]
    have hsq : 1 ≤ rho ^ 2 := by nlinarith
    exact div_le_self (abs_nonneg _) hsq

/-- The inverse-square radial moment is a consequence of raw density flatness
and `dr` integrability; it is not an additional assumption. -/
theorem radialHartreeCenteredDensity_weighted_integrable
    (F : ℝ → ℝ) (hf : Measurable F) (hF : IntegrableOn F (Ioi 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |F rho - F 0| ≤ B * rho ^ 2) :
    IntegrableOn (fun rho => |radialHartreeCenteredDensity F rho| / rho ^ 2) (Ioi 0) := by
  apply flat_weighted_integrable (radialHartreeCenteredDensity F)
    (centered_measurable F hf) (centered_integrable F hF)
    (show 0 ≤ B + 2 * |F 0| by positivity)
  intro rho hrho htop
  exact radialHartreeCenteredDensity_flat F hB hflat hrho htop

private theorem near_bubble_domination
    (G : ℝ → ℝ) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hrtop : r ≤ 1)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |G rho| ≤ A * rho ^ 2) :
    ∀ rho, 0 < rho → |(Iic (2 * r)).indicator G rho| ≤
      (20 * A * r ^ 2) * bubble rho ^ 2 := by
  intro rho hrho
  by_cases ht : rho ≤ 2 * r
  · rw [indicator_of_mem (show rho ∈ Iic (2 * r) from ht), bubble_sq]
    have htop : rho ≤ 2 := by linarith
    have hsq : rho ^ 2 ≤ 4 * r ^ 2 := by nlinarith
    have hsq4 : rho ^ 2 ≤ 4 := by nlinarith
    have hsmall : |G rho| ≤ 4 * A * r ^ 2 := by
      calc
        |G rho| ≤ A * rho ^ 2 := hflat rho hrho htop
        _ ≤ A * (4 * r ^ 2) := mul_le_mul_of_nonneg_left hsq hA
        _ = _ := by ring
    apply hsmall.trans
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + rho ^ 2)]
    nlinarith [mul_nonneg (show 0 ≤ A * r ^ 2 by positivity)
      (show 0 ≤ 4 - rho ^ 2 by linarith)]
  · rw [indicator_of_notMem (show rho ∉ Iic (2 * r) from ht), abs_zero]
    positivity

private theorem near_mass_bound
    (G : ℝ → ℝ) (hG : IntegrableOn G (Ioi 0))
    {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hrtop : r ≤ 1)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |G rho| ≤ A * rho ^ 2) :
    |∫ rho in Ioi (0 : ℝ), (Iic (2 * r)).indicator G rho| ≤
      (20 * A * r ^ 2) * (Real.pi / 2) := by
  have hw : IntegrableOn (fun rho : ℝ => bubble rho ^ 2) (Ioi 0) := by
    simpa only [bubble_sq] using
      (integrable_inv_one_add_sq.integrableOn :
        IntegrableOn (fun rho : ℝ => (1 + rho ^ 2)⁻¹) (Ioi 0))
  calc
    |∫ rho in Ioi (0 : ℝ), (Iic (2 * r)).indicator G rho| ≤
        ∫ rho in Ioi (0 : ℝ), |(Iic (2 * r)).indicator G rho| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ rho in Ioi (0 : ℝ), (20 * A * r ^ 2) * bubble rho ^ 2 := by
      apply integral_mono_ae (hG.indicator measurableSet_Iic).abs (hw.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
      exact near_bubble_domination G hA hr hrtop hflat rho hrho
    _ = (20 * A * r ^ 2) * (Real.pi / 2) := by
      rw [integral_const_mul]
      simp_rw [bubble_sq]
      rw [first_rational_integral]

private theorem potential_add
    (F G : ℝ → ℝ) {r : ℝ}
    (hF : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0))
    (hG : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * G rho) (Ioi 0)) :
    radialHartreePotential (fun rho => F rho + G rho) r =
      radialHartreePotential F r + radialHartreePotential G r := by
  unfold radialHartreePotential
  simp_rw [mul_add]
  rw [integral_add hF hG]
  ring

private theorem potential_const_mul (F : ℝ → ℝ) (a r : ℝ) :
    radialHartreePotential (fun rho => a * F rho) r = a * radialHartreePotential F r := by
  unfold radialHartreePotential
  simp_rw [show ∀ rho : ℝ, rho * hartreeRadialLog r rho * (a * F rho) =
    a * (rho * hartreeRadialLog r rho * F rho) from fun rho => by ring]
  rw [integral_const_mul]
  ring

private theorem flat_potential_quadratic
    (G : ℝ → ℝ) (hg : Measurable G) (hG : IntegrableOn G (Ioi 0))
    {A : ℝ} (hA : 0 ≤ A)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |G rho| ≤ A * rho ^ 2)
    {r : ℝ} (hr : 0 < r) (hrtop : r ≤ 1) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * G rho) (Ioi 0) ∧
    |radialHartreePotential G r - radialHartreeCenter G| ≤
      (20 * A * (radialHartreeRowBoundConstant +
          4 * Real.pi * hartreeKappa * (Real.pi / 2)) +
        4 * Real.pi * hartreeKappa *
          ∫ rho in Ioi (0 : ℝ), |G rho| / rho ^ 2) * r ^ 2 := by
  let N : ℝ → ℝ := (Iic (2 * r)).indicator G
  let T : ℝ → ℝ := (Ioi (2 * r)).indicator G
  have hN := radialHartreePotential_bubble_sq_domination N
    (hg.indicator measurableSet_Iic) (show 0 ≤ 20 * A * r ^ 2 by positivity)
    (near_bubble_domination G hA hr hrtop hflat) hr
  have hfar := radialHartreeExteriorPotential_quadratic_center G hg
    (hG.mono_set (show Ioi (2 * r) ⊆ Ioi (0 : ℝ) from
      fun rho hrho => (show (0 : ℝ) < 2 * r by positivity).trans hrho))
    (show 0 < 2 * r by positivity) hr (le_refl (2 * r))
  have hTrow : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * T rho) (Ioi 0) := by
    convert (hfar.2.1.integrable_indicator measurableSet_Ioi).integrableOn using 1
    funext rho
    by_cases ht : rho ∈ Ioi (2 * r) <;> simp [T, ht]
  have hsplit : G = fun rho => N rho + T rho := by
    funext rho
    by_cases ht : rho ≤ 2 * r
    · simp [N, T, ht, not_lt.mpr ht]
    · simp [N, T, ht, lt_of_not_ge ht]
  have hrow : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * G rho) (Ioi 0) := by
    convert hN.1.add hTrow using 1
    funext rho
    change rho * hartreeRadialLog r rho * G rho =
      rho * hartreeRadialLog r rho * N rho + rho * hartreeRadialLog r rho * T rho
    rw [← mul_add, ← congrFun hsplit rho]
  have hNI : IntegrableOn N (Ioi 0) := hG.indicator measurableSet_Iic
  have hTI : IntegrableOn T (Ioi 0) := hG.indicator measurableSet_Ioi
  have hpotsplit : radialHartreePotential G r =
      radialHartreePotential N r + radialHartreePotential T r := by
    calc
      radialHartreePotential G r = radialHartreePotential (fun rho => N rho + T rho) r :=
        congrArg (fun f => radialHartreePotential f r) hsplit
      _ = _ := potential_add N T hN.1 hTrow
  have hcentersplit : radialHartreeCenter G = radialHartreeCenter N + radialHartreeCenter T := by
    unfold radialHartreeCenter
    rw [show (∫ rho in Ioi (0 : ℝ), G rho) =
      ∫ rho in Ioi (0 : ℝ), N rho + T rho from congrArg (fun f => ∫ rho in Ioi (0 : ℝ), f rho) hsplit,
      integral_add hNI hTI]
    ring
  have hTpot : radialHartreePotential T r = radialHartreeExteriorPotential G (2 * r) r :=
    (radialHartreeExteriorPotential_eq_indicator G (by positivity) r).symm
  have hTcenter : radialHartreeCenter T = radialHartreeExteriorCenter G (2 * r) := by
    unfold radialHartreeCenter radialHartreeExteriorCenter
    dsimp [T]
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (show Ioi (2 * r) ⊆ Ioi (0 : ℝ) from
        fun rho hrho => (show (0 : ℝ) < 2 * r by positivity).trans hrho)]
  have hJ := flat_weighted_integrable G hg hG hA hflat
  have hJle : (∫ rho in Ioi (2 * r), |G rho| / rho ^ 2) ≤
      ∫ rho in Ioi (0 : ℝ), |G rho| / rho ^ 2 := by
    apply setIntegral_mono_set hJ
    · exact Eventually.of_forall (fun rho => div_nonneg (abs_nonneg _) (sq_nonneg _))
    · exact Eventually.of_forall (fun rho hrho => (show (0 : ℝ) < 2 * r by positivity).trans hrho)
  have hK : 0 ≤ 4 * Real.pi * hartreeKappa := by unfold hartreeKappa; positivity
  have hnearMass : |radialHartreeCenter N| ≤
      (4 * Real.pi * hartreeKappa) * ((20 * A * r ^ 2) * (Real.pi / 2)) := by
    unfold radialHartreeCenter
    rw [abs_mul, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left (near_mass_bound G hG hA hr hrtop hflat) hK
  have hterr : |radialHartreePotential T r - radialHartreeCenter T| ≤
      (4 * Real.pi * hartreeKappa) * r ^ 2 *
        ∫ rho in Ioi (0 : ℝ), |G rho| / rho ^ 2 := by
    rw [hTpot, hTcenter]
    exact hfar.2.2.trans (mul_le_mul_of_nonneg_left hJle (mul_nonneg hK (sq_nonneg _)))
  refine ⟨hrow, ?_⟩
  rw [hpotsplit, hcentersplit]
  calc
    |radialHartreePotential N r + radialHartreePotential T r -
        (radialHartreeCenter N + radialHartreeCenter T)| =
        |(radialHartreePotential N r - radialHartreeCenter N) +
          (radialHartreePotential T r - radialHartreeCenter T)| := by congr 1; ring
    _ ≤ |radialHartreePotential N r - radialHartreeCenter N| +
        |radialHartreePotential T r - radialHartreeCenter T| := abs_add_le _ _
    _ ≤ (|radialHartreePotential N r| + |radialHartreeCenter N|) +
        |radialHartreePotential T r - radialHartreeCenter T| :=
      add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ (radialHartreeRowBoundConstant * (20 * A * r ^ 2) +
        (4 * Real.pi * hartreeKappa) * ((20 * A * r ^ 2) * (Real.pi / 2))) +
        (4 * Real.pi * hartreeKappa) * r ^ 2 *
          ∫ rho in Ioi (0 : ℝ), |G rho| / rho ^ 2 :=
      add_le_add (add_le_add hN.2 hnearMass) hterr
    _ = _ := by ring

/-- Explicit finite constant for the full center estimate. Its density moment
has been derived to be absolutely integrable from the raw hypotheses. -/
def radialHartreeCenterBoundConstant (F : ℝ → ℝ) (B : ℝ) : ℝ :=
  1 + 3 * |F 0| +
    20 * (B + 2 * |F 0|) * (radialHartreeRowBoundConstant +
      4 * Real.pi * hartreeKappa * (Real.pi / 2)) +
    4 * Real.pi * hartreeKappa *
      ∫ rho in Ioi (0 : ℝ), |radialHartreeCenteredDensity F rho| / rho ^ 2

theorem radialHartreeCenterBoundConstant_pos (F : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    0 < radialHartreeCenterBoundConstant F B := by
  have hrow := radialHartreeRowBoundConstant_pos
  have hmass : 0 ≤ ∫ rho in Ioi (0 : ℝ), |radialHartreeCenteredDensity F rho| / rho ^ 2 :=
    integral_nonneg (fun rho => div_nonneg (abs_nonneg _) (sq_nonneg _))
  unfold radialHartreeCenterBoundConstant hartreeKappa
  positivity

/-- The complete actual radial Hartree row converges absolutely, and its genuine
center error is quadratic, including the density's entire inner contribution. -/
theorem radialHartreePotential_quadratic_center
    (F : ℝ → ℝ) (hf : Measurable F) (hF : IntegrableOn F (Ioi 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |F rho - F 0| ≤ B * rho ^ 2)
    {r : ℝ} (hr : 0 < r) (hrtop : r ≤ 1) :
    IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) ∧
      |radialHartreePotential F r - radialHartreeCenter F| ≤
        radialHartreeCenterBoundConstant F B * r ^ 2 := by
  let G := radialHartreeCenteredDensity F
  have hG := centered_integrable F hF
  have hg := centered_measurable F hf
  have hquad := flat_potential_quadratic G hg hG
    (show 0 ≤ B + 2 * |F 0| by positivity)
    (fun rho hrho htop => radialHartreeCenteredDensity_flat F hB hflat hrho htop)
    hr hrtop
  have hBrow := (radialHartreeBubble_four_integrable hr).const_mul (F 0)
  have hBrow' : IntegrableOn
      (fun rho => rho * hartreeRadialLog r rho * (F 0 * bubble rho ^ 4)) (Ioi 0) := by
    exact hBrow.congr (Eventually.of_forall (fun rho => by ring))
  have hsplit : F = fun rho => (F 0 * bubble rho ^ 4) + G rho := by
    funext rho
    dsimp [G, radialHartreeCenteredDensity]
    ring
  have hrow : IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) := by
    convert hBrow'.add hquad.1 using 1
    funext rho
    change rho * hartreeRadialLog r rho * F rho =
      rho * hartreeRadialLog r rho * (F 0 * bubble rho ^ 4) +
        rho * hartreeRadialLog r rho * G rho
    rw [← mul_add, ← congrFun hsplit rho]
  have hpot : radialHartreePotential F r = F 0 * (3 * bubble r ^ 2) +
      radialHartreePotential G r := by
    calc
      radialHartreePotential F r =
          radialHartreePotential (fun rho => F 0 * bubble rho ^ 4 + G rho) r :=
        congrArg (fun f => radialHartreePotential f r) hsplit
      _ = radialHartreePotential (fun rho => F 0 * bubble rho ^ 4) r +
          radialHartreePotential G r := potential_add _ G hBrow' hquad.1
      _ = _ := by rw [potential_const_mul, radialHartreePotential_bubble_four hr]
  have hcenter : radialHartreeCenter F = F 0 * 3 + radialHartreeCenter G := by
    unfold radialHartreeCenter
    rw [show (∫ rho in Ioi (0 : ℝ), F rho) =
      ∫ rho in Ioi (0 : ℝ), F 0 * bubble rho ^ 4 + G rho from
        congrArg (fun f => ∫ rho in Ioi (0 : ℝ), f rho) hsplit,
      integral_add (bubble_four_dr_integrable.const_mul (F 0)) hG,
      integral_const_mul, bubble_four_dr_mass]
    unfold hartreeKappa
    field_simp [Real.pi_ne_zero]
    ring
  have hbubble : |F 0 * (3 * bubble r ^ 2 - 3)| ≤ 3 * |F 0| * r ^ 2 := by
    have heq : 3 * bubble r ^ 2 - 3 = -3 * r ^ 2 / (1 + r ^ 2) := by
      rw [bubble_sq]
      field_simp [(by positivity : (1 + r ^ 2 : ℝ) ≠ 0)]
      ring
    rw [abs_mul, heq, abs_div, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ 1 + r ^ 2)]
    norm_num
    calc
      |F 0| * (3 * r ^ 2 / (1 + r ^ 2)) ≤ |F 0| * (3 * r ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact div_le_self (by positivity) (by nlinarith [sq_nonneg r])
      _ = _ := by ring
  refine ⟨hrow, ?_⟩
  rw [hpot, hcenter]
  calc
    |F 0 * (3 * bubble r ^ 2) + radialHartreePotential G r -
        (F 0 * 3 + radialHartreeCenter G)| =
        |F 0 * (3 * bubble r ^ 2 - 3) +
          (radialHartreePotential G r - radialHartreeCenter G)| := by congr 1; ring
    _ ≤ |F 0 * (3 * bubble r ^ 2 - 3)| +
        |radialHartreePotential G r - radialHartreeCenter G| := abs_add_le _ _
    _ ≤ 3 * |F 0| * r ^ 2 +
      (20 * (B + 2 * |F 0|) * (radialHartreeRowBoundConstant +
          4 * Real.pi * hartreeKappa * (Real.pi / 2)) +
        4 * Real.pi * hartreeKappa *
          ∫ rho in Ioi (0 : ℝ), |G rho| / rho ^ 2) * r ^ 2 :=
      add_le_add hbubble hquad.2
    _ ≤ radialHartreeCenterBoundConstant F B * r ^ 2 := by
      dsimp [radialHartreeCenterBoundConstant, G]
      nlinarith [sq_nonneg r]

/-- The actual unsplit positive-radius potential tends to its derived center mass. -/
theorem radialHartreePotential_tendsto_center
    (F : ℝ → ℝ) (hf : Measurable F) (hF : IntegrableOn F (Ioi 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |F rho - F 0| ≤ B * rho ^ 2) :
    Tendsto (radialHartreePotential F) (nhdsWithin 0 (Ioi 0))
      (nhds (radialHartreeCenter F)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlim : Tendsto (fun r : ℝ => radialHartreeCenterBoundConstant F B * r ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hid : Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      nhdsWithin_le_nhds
    simpa using (hid.pow 2).const_mul (radialHartreeCenterBoundConstant F B)
  refine squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_ hlim
  have hnear : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), r < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with r hr htop
  rw [Real.dist_eq]
  exact (radialHartreePotential_quadratic_center F hf hF hB hflat hr htop.le).2

/-- The full center theorem packages the finite derived moment, strictly positive
constant, all core row integrals, quadratic error and the genuine center limit. -/
theorem radialHartree_full_center_environment
    (F : ℝ → ℝ) (hf : Measurable F) (hF : IntegrableOn F (Ioi 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → |F rho - F 0| ≤ B * rho ^ 2) :
    IntegrableOn (fun rho => |radialHartreeCenteredDensity F rho| / rho ^ 2) (Ioi 0) ∧
    0 < radialHartreeCenterBoundConstant F B ∧
    (∀ r, 0 < r → r ≤ 1 →
      IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) ∧
      |radialHartreePotential F r - radialHartreeCenter F| ≤
        radialHartreeCenterBoundConstant F B * r ^ 2) ∧
    Tendsto (radialHartreePotential F) (nhdsWithin 0 (Ioi 0))
      (nhds (radialHartreeCenter F)) := by
  exact ⟨radialHartreeCenteredDensity_weighted_integrable F hf hF hB hflat,
    radialHartreeCenterBoundConstant_pos F hB,
    fun _ hr htop => radialHartreePotential_quadratic_center F hf hF hB hflat hr htop,
    radialHartreePotential_tendsto_center F hf hF hB hflat⟩

end HBL.Modulation.Monopole
