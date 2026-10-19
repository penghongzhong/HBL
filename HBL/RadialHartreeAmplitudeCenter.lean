import HBL.RadialHartreeCenter
import Mathlib.Analysis.Complex.Basic

/-!
The actual center expansion for the quartic density of a complex radial
amplitude.  The inputs concern the amplitude itself: measurability, a uniform
bound, radial weighted L2 mass, and quadratic flatness at the origin.
Density dr-integrability and density flatness are derived, not assumed.

The center is the genuine limiting value of the positive-radius potential.
No assertion identifies the totalized quotient at radius zero with this value.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Modulation.Monopole
open HBL.Modulation.AffineTail

/-- A bounded radial amplitude with finite radial L2 mass has a quartic
density integrable against dr.  The proof uses a bounded near part and the
actual weighted mass away from the origin. -/
theorem radialAmplitude_four_dr_integrable
    {Z : ℝ → ℂ} {M : ℝ} (hZ : Measurable Z)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z rho‖ ≤ M)
    (hmass : IntegrableOn (fun rho => rho ^ 2 * ‖Z rho‖ ^ 2) (Ioi 0)) :
    IntegrableOn (fun rho => ‖Z rho‖ ^ 4) (Ioi 0) := by
  have hconst : IntegrableOn (fun _ : ℝ => M ^ 4) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hind : IntegrableOn ((Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => M ^ 4))
      (Ioi 0) := (hconst.integrable_indicator measurableSet_Ioc).integrableOn
  apply (hind.add (hmass.const_mul (M ^ 2))).mono'
    (hZ.norm.pow_const 4).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with rho hrho
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
  simp only [Pi.add_apply]
  by_cases ht : rho ≤ 1
  · rw [indicator_of_mem (show rho ∈ Ioc (0 : ℝ) 1 from ⟨hrho, ht⟩)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hbound rho hrho.le) 4).trans
      (le_add_of_nonneg_right (by positivity))
  · rw [indicator_of_notMem (show rho ∉ Ioc (0 : ℝ) 1 from fun h => ht h.2),
      zero_add]
    have hz : ‖Z rho‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound rho hrho.le) 2
    have hrhosq : 1 ≤ rho ^ 2 := by nlinarith
    calc
      ‖Z rho‖ ^ 4 = ‖Z rho‖ ^ 2 * ‖Z rho‖ ^ 2 := by ring
      _ ≤ M ^ 2 * ‖Z rho‖ ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg _)
      _ ≤ M ^ 2 * (rho ^ 2 * ‖Z rho‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg ‖Z rho‖]) (sq_nonneg M)

/-- Quartic density flatness follows from the primitive complex-amplitude
flatness, with the explicit constant 4 M^3 D, including M = 0. -/
theorem radialAmplitude_four_quadratic_flat
    {Z : ℝ → ℂ} {M D : ℝ} (hM : 0 ≤ M) (_hD : 0 ≤ D)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z rho‖ ≤ M)
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → ‖Z rho - Z 0‖ ≤ D * rho ^ 2)
    {rho : ℝ} (hrho : 0 < rho) (htop : rho ≤ 2) :
    |‖Z rho‖ ^ 4 - ‖Z 0‖ ^ 4| ≤ (4 * M ^ 3 * D) * rho ^ 2 := by
  have hdiff : |‖Z rho‖ - ‖Z 0‖| ≤ D * rho ^ 2 :=
    (abs_norm_sub_norm_le (Z rho) (Z 0)).trans (hflat rho hrho htop)
  have hmax : max |‖Z rho‖| |‖Z 0‖| ≤ M := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      (max_le (hbound rho hrho.le) (hbound 0 le_rfl))
  have hp : max |‖Z rho‖| |‖Z 0‖| ^ 3 ≤ M ^ 3 :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax 3
  calc
    |‖Z rho‖ ^ 4 - ‖Z 0‖ ^ 4| ≤
        |‖Z rho‖ - ‖Z 0‖| * 4 * max |‖Z rho‖| |‖Z 0‖| ^ 3 := by
      simpa using (abs_pow_sub_pow_le (a := ‖Z rho‖) (b := ‖Z 0‖) (n := 4))
    _ ≤ |‖Z rho‖ - ‖Z 0‖| * 4 * M ^ 3 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (D * rho ^ 2) * 4 * M ^ 3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdiff (by norm_num)) (pow_nonneg hM 3)
    _ = (4 * M ^ 3 * D) * rho ^ 2 := by ring

/-- Complete actual center conclusion from primitive complex-amplitude data.
The mass is the radial weighted L2 integral, not an assumed quartic dr bound
or an assumed potential estimate.  The last conclusion is a right-hand
center limit, separate from evaluation of the totalized quotient at zero. -/
theorem radialHartreeAmplitude_full_center_environment
    {Z : ℝ → ℂ} {M D : ℝ} (hZ : Measurable Z) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ rho, 0 ≤ rho → ‖Z rho‖ ≤ M)
    (hmass : IntegrableOn (fun rho => rho ^ 2 * ‖Z rho‖ ^ 2) (Ioi 0))
    (hflat : ∀ rho, 0 < rho → rho ≤ 2 → ‖Z rho - Z 0‖ ≤ D * rho ^ 2) :
    let F : ℝ → ℝ := fun rho => ‖Z rho‖ ^ 4
    IntegrableOn F (Ioi 0) ∧
    (∀ rho, 0 < rho → rho ≤ 2 → |F rho - F 0| ≤ (4 * M ^ 3 * D) * rho ^ 2) ∧
    IntegrableOn (fun rho => |radialHartreeCenteredDensity F rho| / rho ^ 2) (Ioi 0) ∧
    0 < radialHartreeCenterBoundConstant F (4 * M ^ 3 * D) ∧
    (∀ r, 0 < r → r ≤ 1 →
      IntegrableOn (fun rho => rho * hartreeRadialLog r rho * F rho) (Ioi 0) ∧
      |radialHartreePotential F r -
          4 * Real.pi * hartreeKappa * (∫ rho in Ioi (0 : ℝ), F rho)| ≤
        radialHartreeCenterBoundConstant F (4 * M ^ 3 * D) * r ^ 2) ∧
    Tendsto (radialHartreePotential F) (nhdsWithin 0 (Ioi 0))
      (nhds (4 * Real.pi * hartreeKappa * (∫ rho in Ioi (0 : ℝ), F rho))) := by
  dsimp only
  have hi := radialAmplitude_four_dr_integrable hZ hbound hmass
  have hf : ∀ rho, 0 < rho → rho ≤ 2 →
      |‖Z rho‖ ^ 4 - ‖Z 0‖ ^ 4| ≤ (4 * M ^ 3 * D) * rho ^ 2 :=
    fun _ hrho htop => radialAmplitude_four_quadratic_flat hM hD hbound hflat hrho htop
  have hc := radialHartree_full_center_environment (fun rho => ‖Z rho‖ ^ 4)
    (hZ.norm.pow_const 4) hi (show 0 ≤ 4 * M ^ 3 * D by positivity) hf
  exact ⟨hi, hf, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

end HBL.Modulation.Monopole
